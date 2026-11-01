(** ConsensusSeparation: the small machine in the framework of Aman Pohjola
    and Parrow (ESOP 2016, "The Expressive Power of Monotonic Parallel
    Composition").

    Their framework, Definitions 1-5 of the paper:
    - a transition system is a set of processes with a step relation;
    - a composition is an associative, commutative operation on processes;
    - it is monotonic if P ==> Q implies P (x) R ==> Q (x) R;
    - a process predicate f is P-stable if, for every P' reachable from
      n copies of P, f(Q) implies f(P' (x) Q);
    - P is an f, g-consensus process if f and g are P-stable, and for
      every n > 1, n copies of P can reach f, can reach g, and once one of
      them holds the other is never reached.

    - Their Theorem 15: with a monotonic composition there is no consensus
      process ([cs_no_consensus_monotonic]). Two halves of 2n copies run
      apart, one to f and one to g, and stability puts both on the joined
      state.
    - The encoding: processes are a shared state of EarnedCore.v and a
      multiset of SmallConsensus.v's threads, each proposing a bit;
      composing two processes pools their threads on one shared state.
      The process with one thread proposing each bit is a consensus process
      for "some thread decided 0" and "some thread decided 1"
      ([cs_machine_consensus]), so by Theorem 15 that composition is not
      monotonic ([cs_machine_not_monotonic]): the machine sits on the
      non-monotonic side of their split.

    How two already-running shared states combine plays no part in
    Definition 5, which composes only fresh copies and finished runs through
    stable predicates; here they combine to a stuck state, which keeps the
    composition associative and commutative. *)

From Coq Require Import List Arith Lia Bool Relations FunctionalExtensionality.
Import ListNotations.
Require Minimal.EarnedCore.
Require Import Minimal.SmallConsensus.
Module E := Minimal.EarnedCore.

(** ** Their framework and Theorem 15 *)

Section Framework.

Variable P : Type.
Variable step : P -> P -> Prop.
Variable comp : P -> P -> P.
Hypothesis comp_assoc : forall p q r, comp p (comp q r) = comp (comp p q) r.
Hypothesis comp_comm : forall p q, comp p q = comp q p.

Definition cs_steps : P -> P -> Prop := clos_refl_trans P step.

Definition cs_monotonic : Prop := forall p q r, cs_steps p q -> cs_steps (comp p r) (comp q r).

(** k + 1 copies of p. *)
Fixpoint cs_copies (p : P) (k : nat) : P :=
  match k with O => p | S k => comp p (cs_copies p k) end.

Definition cs_extensible (f : P -> bool) (p : P) : Prop := forall q, f q = true -> f (comp p q) = true.

Definition cs_stable (f : P -> bool) (p : P) : Prop :=
  forall k p', cs_steps (cs_copies p k) p' -> cs_extensible f p'.

(** Definition 5: n > 1 copies are cs_copies p k with k >= 1. *)
Definition cs_consensus (f g : P -> bool) (p : P) : Prop :=
  cs_stable f p /\ cs_stable g p /\
  forall k, 1 <= k ->
    (exists p', cs_steps (cs_copies p k) p' /\ f p' = true) /\
    (exists p', cs_steps (cs_copies p k) p' /\ g p' = true) /\
    (forall p' p'', cs_steps (cs_copies p k) p' -> cs_steps p' p'' ->
       (f p' = true -> g p'' <> true) /\ (g p' = true -> f p'' <> true)).

Lemma cs_copies_add : forall p a b, comp (cs_copies p a) (cs_copies p b) = cs_copies p (a + b + 1).
Proof.
  intros p a. induction a as [| a IH]; intro b; simpl.
  - replace (b + 1) with (S b) by lia. reflexivity.
  - rewrite <- comp_assoc, IH. reflexivity.
Qed.

Lemma cs_mono_r : cs_monotonic -> forall p q r, cs_steps p q -> cs_steps (comp r p) (comp r q).
Proof. intros M p q r H. rewrite (comp_comm r p), (comp_comm r q). apply M. exact H. Qed.

Theorem cs_no_consensus_monotonic : cs_monotonic -> forall f g p, ~ cs_consensus f g p.
Proof.
  intros M f g p [Sf [Sg C]].
  destruct (C 1 (le_n 1)) as [[p1 [H1 F1]] [[p2 [H2 G2]] _]].
  destruct (C 3 ltac:(lia)) as [_ [_ NC]].
  assert (R : cs_steps (cs_copies p 3) (comp p1 p2)).
  { replace (cs_copies p 3) with (comp (cs_copies p 1) (cs_copies p 1)) by (rewrite cs_copies_add; reflexivity).
    apply rt_trans with (comp p1 (cs_copies p 1)); [apply M; exact H1 |].
    apply cs_mono_r; [exact M | exact H2]. }
  assert (Fj : f (comp p1 p2) = true).
  { rewrite comp_comm. exact (Sf 1 p2 H2 p1 F1). }
  assert (Gj : g (comp p1 p2) = true) by exact (Sg 1 p1 H1 p2 G2).
  destruct (NC (comp p1 p2) (comp p1 p2) R (rt_refl _ _ _)) as [N _].
  exact (N Fj Gj).
Qed.

End Framework.

(** ** The encoding of the small machine *)

(** A thread: the bit it proposes and where it is in the protocol. *)
Record cs_kind : Type := mkk { k_inp : bool; k_loc : sc_local }.

Definition cs_loc_eqb (a b : sc_local) : bool :=
  match a, b with
  | SStart, SStart => true
  | SChecked, SChecked => true
  | SDecided x, SDecided y => Bool.eqb x y
  | _, _ => false
  end.

Definition cs_kind_eqb (a b : cs_kind) : bool := Bool.eqb (k_inp a) (k_inp b) && cs_loc_eqb (k_loc a) (k_loc b).

Lemma cs_kind_eqb_eq : forall a b, cs_kind_eqb a b = true <-> a = b.
Proof.
  intros [ia la] [ib lb]. unfold cs_kind_eqb. simpl. split.
  - intro H. apply andb_true_iff in H as [H1 H2]. apply Bool.eqb_prop in H1. subst ib.
    destruct la, lb; simpl in H2; try discriminate; try reflexivity.
    apply Bool.eqb_prop in H2. subst. reflexivity.
  - intro H. injection H as <- <-. rewrite Bool.eqb_reflx. destruct la; simpl; try reflexivity.
    apply Bool.eqb_reflx.
Qed.

(** The shared state: untouched, a state of the machine, or stuck. *)
Inductive cs_store : Type := SInit | SAt (s : E.state) | SStuck.

Definition cs_merge (a b : cs_store) : cs_store :=
  match a, b with
  | SInit, x => x
  | x, SInit => x
  | _, _ => SStuck
  end.

Definition cs_state (a : cs_store) : option E.state :=
  match a with SInit => Some (E.start 0 0) | SAt s => Some s | SStuck => None end.

Record cs_cfg : Type := mkcfg { c_st : cs_store; c_th : cs_kind -> nat }.

(** Composition pools the threads on one shared state. *)
Definition cs_comp (c d : cs_cfg) : cs_cfg :=
  mkcfg (cs_merge (c_st c) (c_st d)) (fun k => c_th c k + c_th d k).

Lemma cs_comp_assoc : forall c d e, cs_comp c (cs_comp d e) = cs_comp (cs_comp c d) e.
Proof.
  intros [a f] [b g] [x h]. unfold cs_comp. simpl. f_equal.
  - destruct a, b, x; reflexivity.
  - apply functional_extensionality. intro k. lia.
Qed.

Lemma cs_comp_comm : forall c d, cs_comp c d = cs_comp d c.
Proof.
  intros [a f] [b g]. unfold cs_comp. simpl. f_equal.
  - destruct a, b; reflexivity.
  - apply functional_extensionality. intro k. lia.
Qed.

(** One thread of kind k moves to kind k'. *)
Definition cs_move (m : cs_kind -> nat) (k k' : cs_kind) (j : cs_kind) : nat :=
  (if cs_kind_eqb j k then m j - 1 else m j) + (if cs_kind_eqb j k' then 1 else 0).

(** A step: some thread runs its next instruction on the shared state. *)
Definition cs_step (c c' : cs_cfg) : Prop :=
  exists k s, 0 < c_th c k /\ cs_state (c_st c) = Some s /\
    match k_loc k with
    | SStart => c' = mkcfg (SAt (E.exec s (E.CHECK (sc_code (k_inp k)) E.CA)))
                          (cs_move (c_th c) k (mkk (k_inp k) SChecked))
    | SChecked => c' = mkcfg (SAt s)
                          (cs_move (c_th c) k (mkk (k_inp k)
                             (SDecided (sc_decode (E.f_prop (sc_oldest (E.facts (E.core_of s))))))))
    | SDecided _ => False
    end.

(** "Some thread decided b". *)
Definition cs_dec (b : bool) (c : cs_cfg) : bool :=
  Nat.ltb 0 (c_th c (mkk false (SDecided b)) + c_th c (mkk true (SDecided b))).

(** One thread proposing each bit, on a fresh state. *)
Definition cs_P : cs_cfg :=
  mkcfg SInit (fun k => match k_loc k with SStart => 1 | _ => 0 end).

Lemma cs_copies_P : forall n,
  cs_copies cs_cfg cs_comp cs_P n = mkcfg SInit (fun k => match k_loc k with SStart => S n | _ => 0 end).
Proof.
  induction n as [| n IH]; [reflexivity |]. simpl. rewrite IH. unfold cs_comp, cs_P. simpl. f_equal.
  apply functional_extensionality. intro k. destruct (k_loc k); lia.
Qed.

(** Decided threads never move. *)
Lemma cs_step_keeps_decided : forall c c' i b, cs_step c c' ->
  c_th c (mkk i (SDecided b)) <= c_th c' (mkk i (SDecided b)).
Proof.
  intros c c' i b [k [s [Hk [Hs Hstep]]]].
  destruct (k_loc k) eqn:Hl; try contradiction; subst c'; simpl; unfold cs_move;
    destruct (cs_kind_eqb (mkk i (SDecided b)) k) eqn:E1;
    try (apply cs_kind_eqb_eq in E1; subst k; simpl in Hl; discriminate);
    destruct (cs_kind_eqb _ _); lia.
Qed.

Lemma cs_steps_keep_decided : forall c c' i b, cs_steps cs_cfg cs_step c c' ->
  c_th c (mkk i (SDecided b)) <= c_th c' (mkk i (SDecided b)).
Proof.
  intros c c' i b H. induction H as [x y H | x | x y z _ IH1 _ IH2].
  - apply cs_step_keeps_decided. exact H.
  - lia.
  - lia.
Qed.

Lemma cs_dec_mono : forall c c' b, cs_steps cs_cfg cs_step c c' -> cs_dec b c = true -> cs_dec b c' = true.
Proof.
  intros c c' b H D. unfold cs_dec in *. apply Nat.ltb_lt in D. apply Nat.ltb_lt.
  pose proof (cs_steps_keep_decided c c' false b H). pose proof (cs_steps_keep_decided c c' true b H). lia.
Qed.

(** The invariant: SmallConsensus.v's, counted. *)
Definition cs_inv (c : cs_cfg) : Prop :=
  exists s, cs_state (c_st c) = Some s /\
    E.ca (E.core_of s) = 0 /\
    (E.err (E.core_of s) = true -> E.facts (E.core_of s) <> []) /\
    (forall k, 0 < c_th c k -> k_loc k <> SStart -> E.facts (E.core_of s) <> []) /\
    (forall k b, 0 < c_th c k -> k_loc k = SDecided b ->
       b = sc_decode (E.f_prop (sc_oldest (E.facts (E.core_of s))))).

Lemma cs_move_pos : forall m k k' j, 0 < cs_move m k k' j ->
  j = k' \/ (j <> k /\ 0 < m j) \/ (j = k /\ 1 < m j).
Proof.
  intros m k k' j H. unfold cs_move in H.
  destruct (cs_kind_eqb j k') eqn:E2; [left; apply cs_kind_eqb_eq; exact E2 |].
  destruct (cs_kind_eqb j k) eqn:E1.
  - right; right. split; [apply cs_kind_eqb_eq; exact E1 | lia].
  - right; left. split; [intro Z; subst; rewrite (proj2 (cs_kind_eqb_eq k k) eq_refl) in E1; discriminate | lia].
Qed.

Lemma cs_step_inv : forall c c', cs_inv c -> cs_step c c' -> cs_inv c'.
Proof.
  intros c c' [s0 [Hs0 [Hca [Herr [Hloc Hdec]]]]] [k [s [Hk [Hs Hstep]]]].
  rewrite Hs in Hs0. injection Hs0 as Es. subst s.
  destruct (k_loc k) as [| | b0] eqn:Hl; [| | contradiction]; subst c'.
  - (* the CHECK *)
    destruct (sc_check_effect (E.core_of s0) (k_inp k) Hca) as [Hca' Hcase].
    exists (E.exec s0 (E.CHECK (sc_code (k_inp k)) E.CA)). simpl. split; [reflexivity |].
    cbn [E.core_of E.exec]. split; [exact Hca' |].
    destruct Hcase as [[Hf Herr'] | [Hf Herr']]; rewrite Hf.
    + assert (Hne : E.facts (E.core_of s0) <> []).
      { destruct Herr' as [H | [_ H]]; [apply Herr; exact H | exact H]. }
      split; [intros _; exact Hne |]. split; [intros _ _ _; exact Hne |].
      intros j b Hj Hjl. destruct (cs_move_pos _ _ _ _ Hj) as [-> | [[_ Hj'] | [-> Hj']]].
      * simpl in Hjl. discriminate.
      * exact (Hdec j b Hj' Hjl).
      * rewrite Hl in Hjl. discriminate.
    + split; [intros _; discriminate |]. split; [intros _ _ _; discriminate |].
      intros j b Hj Hjl. destruct (cs_move_pos _ _ _ _ Hj) as [-> | [[_ Hj'] | [-> Hj']]].
      * simpl in Hjl. discriminate.
      * rewrite (Hdec j b Hj' Hjl).
        assert (Hne : E.facts (E.core_of s0) <> []) by (apply (Hloc j Hj'); rewrite Hjl; discriminate).
        rewrite sc_oldest_cons by exact Hne. reflexivity.
      * rewrite Hl in Hjl. discriminate.
  - (* the read *)
    assert (Hne : E.facts (E.core_of s0) <> []) by (apply (Hloc k Hk); rewrite Hl; discriminate).
    exists s0. simpl. split; [reflexivity |]. split; [exact Hca |]. split; [exact Herr |].
    split; [intros _ _ _; exact Hne |].
    intros j b Hj Hjl. destruct (cs_move_pos _ _ _ _ Hj) as [-> | [[_ Hj'] | [-> Hj']]].
    + simpl in Hjl. injection Hjl as <-. reflexivity.
    + exact (Hdec j b Hj' Hjl).
    + rewrite Hl in Hjl. discriminate.
Qed.

Lemma cs_steps_inv : forall c c', cs_steps cs_cfg cs_step c c' -> cs_inv c -> cs_inv c'.
Proof.
  intros c c' H. induction H as [x y H | x | x y z _ IH1 _ IH2]; intro Hc.
  - exact (cs_step_inv x y Hc H).
  - exact Hc.
  - apply IH2, IH1, Hc.
Qed.

Lemma cs_inv_copies : forall n, cs_inv (cs_copies cs_cfg cs_comp cs_P n).
Proof.
  intro n. rewrite cs_copies_P. exists (E.start 0 0). simpl.
  split; [reflexivity |]. split; [reflexivity |]. split; [discriminate |].
  split.
  - intros k Hk Hl. exfalso. destruct (k_loc k); [apply Hl; reflexivity | lia | lia].
  - intros k b Hk Hkl. rewrite Hkl in Hk. lia.
Qed.

(** No conflict: a run never has threads decided both ways. *)
Lemma cs_no_both : forall n c, cs_steps cs_cfg cs_step (cs_copies cs_cfg cs_comp cs_P n) c ->
  cs_dec false c = true -> cs_dec true c <> true.
Proof.
  intros n c H Df Dt.
  destruct (cs_steps_inv _ _ H (cs_inv_copies n)) as [s [_ [_ [_ [_ Hdec]]]]].
  unfold cs_dec in Df, Dt. apply Nat.ltb_lt in Df. apply Nat.ltb_lt in Dt.
  assert (Ef : false = sc_decode (E.f_prop (sc_oldest (E.facts (E.core_of s))))).
  { destruct (c_th c (mkk false (SDecided false))) eqn:Z.
    - apply (Hdec (mkk true (SDecided false))); [lia | reflexivity].
    - apply (Hdec (mkk false (SDecided false))); [lia | reflexivity]. }
  assert (Et : true = sc_decode (E.f_prop (sc_oldest (E.facts (E.core_of s))))).
  { destruct (c_th c (mkk false (SDecided true))) eqn:Z.
    - apply (Hdec (mkk true (SDecided true))); [lia | reflexivity].
    - apply (Hdec (mkk false (SDecided true))); [lia | reflexivity]. }
  rewrite <- Et in Ef. discriminate.
Qed.

Lemma cs_move_target_pos : forall m k k', 0 < cs_move m k k' k'.
Proof. intros. unfold cs_move. rewrite (proj2 (cs_kind_eqb_eq k' k') eq_refl). lia. Qed.

(** From n + 1 copies, a thread proposing b checks first and then reads:
    it decides b. *)
Lemma cs_can_choose : forall n b, exists c,
  cs_steps cs_cfg cs_step (cs_copies cs_cfg cs_comp cs_P n) c /\ cs_dec b c = true.
Proof.
  intros n b. rewrite cs_copies_P.
  set (m0 := fun k : cs_kind => match k_loc k with SStart => S n | _ => 0 end).
  set (s1 := E.exec (E.start 0 0) (E.CHECK (sc_code b) E.CA)).
  set (m1 := cs_move m0 (mkk b SStart) (mkk b SChecked)).
  set (d := sc_decode (E.f_prop (sc_oldest (E.facts (E.core_of s1))))).
  assert (Hd : d = b) by (unfold d, s1; destruct b; reflexivity).
  set (m2 := cs_move m1 (mkk b SChecked) (mkk b (SDecided d))).
  exists (mkcfg (SAt s1) m2). split.
  - apply rt_trans with (mkcfg (SAt s1) m1); apply rt_step.
    + exists (mkk b SStart), (E.start 0 0). split; [cbn [c_th]; unfold m0; simpl; lia |].
      split; reflexivity.
    + exists (mkk b SChecked), s1. split; [cbn [c_th]; apply cs_move_target_pos |].
      split; reflexivity.
  - assert (P2 : 0 < m2 (mkk b (SDecided d))) by apply cs_move_target_pos.
    rewrite Hd in P2. unfold cs_dec. apply Nat.ltb_lt. cbn [c_th]. destruct b; lia.
Qed.

(** The machine's protocol is a consensus process in their sense. *)
Theorem cs_machine_consensus : cs_consensus cs_cfg cs_step cs_comp (cs_dec false) (cs_dec true) cs_P.
Proof.
  split; [| split].
  - intros k p' _ q Hq. unfold cs_dec in *. apply Nat.ltb_lt in Hq. apply Nat.ltb_lt. simpl. lia.
  - intros k p' _ q Hq. unfold cs_dec in *. apply Nat.ltb_lt in Hq. apply Nat.ltb_lt. simpl. lia.
  - intros k _. split; [apply cs_can_choose |]. split; [apply cs_can_choose |].
    intros p' p'' H1 H2. split.
    + intros F G. apply (cs_no_both k p'' (rt_trans _ _ _ _ _ H1 H2)); [exact (cs_dec_mono _ _ false H2 F) | exact G].
    + intros G F. apply (cs_no_both k p'' (rt_trans _ _ _ _ _ H1 H2)); [exact F | exact (cs_dec_mono _ _ true H2 G)].
Qed.

(** So, by their Theorem 15, the composition is not monotonic. *)
Corollary cs_machine_not_monotonic : ~ cs_monotonic cs_cfg cs_step cs_comp.
Proof.
  intro M. exact (cs_no_consensus_monotonic cs_cfg cs_step cs_comp cs_comp_assoc cs_comp_comm M
                    (cs_dec false) (cs_dec true) cs_P cs_machine_consensus).
Qed.

Print Assumptions cs_no_consensus_monotonic.
Print Assumptions cs_machine_consensus.
Print Assumptions cs_machine_not_monotonic.
