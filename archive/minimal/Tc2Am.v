(** Tc2Am.v: abstract two-counter machines with a finite control that behave
    the same way on every large counter value (tame machines).

    A tame machine has a control type Q with decidable equality, a transition
    function from (control, counter A, counter B) to the next triple or to
    nothing (stopped), and a threshold B0. Four properties are assumed:

      - the control reachable from a listed finite set of controls stays in it;
      - one step changes at most one counter, by at most one;
      - if counter A is at least B0, adding an even number d to it changes
        nothing but the result, in which counter A is also raised by d (the
        same for counter B).

    The last property says that a counter above B0 is only read through its
    parity and through the fact that it is not zero. The EarnedCore machine,
    with its checks, commitments, certificates, facts and trap latch, is such
    a machine once the finite part of its state is taken as the control
    (Tc2Embed.v).

    This file has the runs, the translation lemmas, the swap of the two
    counters and the pigeonhole principle for sequences in a listed set.
    Dependencies: Coq standard library. No axioms and no unfinished proofs.           *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is about abstract two-counter machines with a finite control, the shape
   the two-counter machine of EarnedCore.v takes once its finite part is the
   control (Tc2Embed.v). The machine's link to the abstract record (a
   CertificationSystem with the trace cost floor, and a Thiele-complete
   machine) lives in EarnedCoreLinks.v and ThieleComplete.v. *)


From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Set Default Goal Selector "!".

Record tc2_am : Type := mk_tc2_am {
  am_Q : Type;
  am_eq : forall q q' : am_Q, {q = q'} + {q <> q'};
  am_nx : am_Q -> nat -> nat -> option (am_Q * nat * nat);
  am_B : nat;
  am_lq : list am_Q;
  am_B1 : 1 <= am_B;
  am_closed : forall q a b q' a' b',
    In q am_lq -> am_nx q a b = Some (q', a', b') -> In q' am_lq;
  am_step1 : forall q a b q' a' b', am_nx q a b = Some (q', a', b') ->
    (a' = a /\ (b' = b \/ b' = S b \/ S b' = b)) \/ (b' = b /\ (a' = S a \/ S a' = a));
  am_tameA : forall q a b d, am_B <= a ->
    am_nx q (a + 2 * d) b =
      match am_nx q a b with Some (q', a', b') => Some (q', a' + 2 * d, b') | None => None end;
  am_tameB : forall q a b d, am_B <= b ->
    am_nx q a (b + 2 * d) =
      match am_nx q a b with Some (q', a', b') => Some (q', a', b' + 2 * d) | None => None end
}.

Definition tc2_cfg (M : tc2_am) : Type := (am_Q M * nat * nat)%type.

Definition am_stp (M : tc2_am) (k : tc2_cfg M) : tc2_cfg M :=
  match k with (q, a, b) => match am_nx M q a b with Some k' => k' | None => k end end.

Fixpoint am_run (M : tc2_am) (n : nat) (k : tc2_cfg M) : tc2_cfg M :=
  match n with 0 => k | S m => am_run M m (am_stp M k) end.

Definition am_hlt (M : tc2_am) (k : tc2_cfg M) : Prop :=
  match k with (q, a, b) => am_nx M q a b = None end.

Definition am_q (M : tc2_am) (k : tc2_cfg M) : am_Q M := fst (fst k).
Definition am_a (M : tc2_am) (k : tc2_cfg M) : nat := snd (fst k).
Definition am_b (M : tc2_am) (k : tc2_cfg M) : nat := snd k.

Lemma am_run_add : forall M n m (k : tc2_cfg M), am_run M (n + m) k = am_run M m (am_run M n k).
Proof. intros M n. induction n as [| n IH]; intros m k; simpl; [reflexivity | apply IH]. Qed.

Lemma am_run_S_l : forall M n (k : tc2_cfg M), am_run M (S n) k = am_run M n (am_stp M k).
Proof. reflexivity. Qed.

Lemma am_run_S_r : forall M n (k : tc2_cfg M), am_run M (S n) k = am_stp M (am_run M n k).
Proof. intros M n k. replace (S n) with (n + 1) by lia. rewrite am_run_add. reflexivity. Qed.

Lemma am_hlt_stp : forall M (k : tc2_cfg M), am_hlt M k -> am_stp M k = k.
Proof. intros M [[q a] b] H. unfold am_hlt in H. simpl in H. unfold am_stp. rewrite H. reflexivity. Qed.

Lemma am_hlt_run : forall M n (k : tc2_cfg M), am_hlt M k -> am_run M n k = k.
Proof.
  intros M n. induction n as [| n IH]; intros k H; [reflexivity |].
  simpl. rewrite (am_hlt_stp M k H). apply IH, H.
Qed.

Lemma am_run_after : forall M n m (k : tc2_cfg M), n <= m ->
  am_hlt M (am_run M n k) -> am_run M m k = am_run M n k.
Proof.
  intros M n m k Hle H. replace m with (n + (m - n)) by lia.
  rewrite am_run_add. apply am_hlt_run, H.
Qed.

Lemma am_stp_q : forall M (k : tc2_cfg M), In (am_q M k) (am_lq M) -> In (am_q M (am_stp M k)) (am_lq M).
Proof.
  intros M [[q a] b] H. simpl in H. unfold am_stp. destruct (am_nx M q a b) as [[[q' a'] b'] |] eqn:E.
  - simpl. eapply am_closed; eauto.
  - exact H.
Qed.

Lemma am_run_q : forall M n (k : tc2_cfg M), In (am_q M k) (am_lq M) -> In (am_q M (am_run M n k)) (am_lq M).
Proof.
  intros M n. induction n as [| n IH]; intros k H; [exact H |].
  simpl. apply IH, am_stp_q, H.
Qed.

(* one step moves one counter by at most one *)
Lemma am_stp_step1 : forall M (k : tc2_cfg M),
  (am_a M (am_stp M k) = am_a M k /\
     (am_b M (am_stp M k) = am_b M k \/ am_b M (am_stp M k) = S (am_b M k) \/ S (am_b M (am_stp M k)) = am_b M k)) \/
  (am_b M (am_stp M k) = am_b M k /\
     (am_a M (am_stp M k) = S (am_a M k) \/ S (am_a M (am_stp M k)) = am_a M k)).
Proof.
  intros M [[q a] b]. unfold am_stp. destruct (am_nx M q a b) as [[[q' a'] b'] |] eqn:E.
  - destruct (am_step1 M _ _ _ _ _ _ E) as [[H1 H2] | [H1 H2]]; simpl; [left | right]; auto.
  - simpl. left. auto.
Qed.

(* ------------------------------------------------------------------ *)
(* translation                                                         *)
(* ------------------------------------------------------------------ *)

Definition am_shA (M : tc2_am) (d : nat) (k : tc2_cfg M) : tc2_cfg M :=
  match k with (q, a, b) => (q, a + d, b) end.
Definition am_shB (M : tc2_am) (d : nat) (k : tc2_cfg M) : tc2_cfg M :=
  match k with (q, a, b) => (q, a, b + d) end.

Lemma am_stp_shB : forall M d (k : tc2_cfg M), am_B M <= am_b M k ->
  am_stp M (am_shB M (2 * d) k) = am_shB M (2 * d) (am_stp M k).
Proof.
  intros M d [[q a] b] H. simpl in H.
  change (am_shB M (2 * d) (q, a, b)) with (q, a, b + 2 * d).
  unfold am_stp at 1. rewrite (am_tameB M q a b d H).
  unfold am_stp. destruct (am_nx M q a b) as [[[q' a'] b'] |]; reflexivity.
Qed.

Lemma am_stp_shA : forall M d (k : tc2_cfg M), am_B M <= am_a M k ->
  am_stp M (am_shA M (2 * d) k) = am_shA M (2 * d) (am_stp M k).
Proof.
  intros M d [[q a] b] H. simpl in H.
  change (am_shA M (2 * d) (q, a, b)) with (q, a + 2 * d, b).
  unfold am_stp at 1. rewrite (am_tameA M q a b d H).
  unfold am_stp. destruct (am_nx M q a b) as [[[q' a'] b'] |]; reflexivity.
Qed.

(* a run during which counter B stays at or above the threshold is translated by a shift of B *)
Lemma am_run_shB : forall M d n (k : tc2_cfg M),
  (forall t, t < n -> am_B M <= am_b M (am_run M t k)) ->
  am_run M n (am_shB M (2 * d) k) = am_shB M (2 * d) (am_run M n k).
Proof.
  intros M d n. induction n as [| n IH]; intros k H; [reflexivity |].
  rewrite (am_run_S_l M n (am_shB M (2 * d) k)), (am_run_S_l M n k). rewrite am_stp_shB.
  - apply IH. intros t Ht. specialize (H (S t) ltac:(lia)). simpl in H. exact H.
  - specialize (H 0 ltac:(lia)). exact H.
Qed.

Lemma am_run_shA : forall M d n (k : tc2_cfg M),
  (forall t, t < n -> am_B M <= am_a M (am_run M t k)) ->
  am_run M n (am_shA M (2 * d) k) = am_shA M (2 * d) (am_run M n k).
Proof.
  intros M d n. induction n as [| n IH]; intros k H; [reflexivity |].
  rewrite (am_run_S_l M n (am_shA M (2 * d) k)), (am_run_S_l M n k). rewrite am_stp_shA.
  - apply IH. intros t Ht. specialize (H (S t) ltac:(lia)). simpl in H. exact H.
  - specialize (H 0 ltac:(lia)). exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* the swap of the two counters                                        *)
(* ------------------------------------------------------------------ *)

Definition am_swp (M : tc2_am) : tc2_am.
Proof.
  refine (mk_tc2_am (am_Q M) (am_eq M)
            (fun q a b => match am_nx M q b a with Some (q', b', a') => Some (q', a', b') | None => None end)
            (am_B M) (am_lq M) (am_B1 M) _ _ _ _).
  - intros q a b q' a' b' Hq H. destruct (am_nx M q b a) as [[[q1 b1] a1] |] eqn:E; [| discriminate].
    injection H as <- <- <-. exact (am_closed M q b a q1 b1 a1 Hq E).
  - intros q a b q' a' b' H. destruct (am_nx M q b a) as [[[q1 b1] a1] |] eqn:E; [| discriminate].
    injection H as <- <- <-. destruct (am_step1 M _ _ _ _ _ _ E) as [[H1 [H2 | [H2 | H2]]] | [H1 [H2 | H2]]].
    + left. split; [exact H2 | left; exact H1].
    + right. split; [exact H1 | left; exact H2].
    + right. split; [exact H1 | right; exact H2].
    + left. split; [exact H1 | right; left; exact H2].
    + left. split; [exact H1 | right; right; exact H2].
  - intros q a b d H. cbv beta. rewrite (am_tameB M q b a d H).
    destruct (am_nx M q b a) as [[[q1 b1] a1] |]; reflexivity.
  - intros q a b d H. cbv beta. rewrite (am_tameA M q b a d H).
    destruct (am_nx M q b a) as [[[q1 b1] a1] |]; reflexivity.
Defined.

Definition am_sw (M : tc2_am) (k : tc2_cfg M) : tc2_cfg (am_swp M) :=
  match k with (q, a, b) => (q, b, a) end.
Definition am_usw (M : tc2_am) (k : tc2_cfg (am_swp M)) : tc2_cfg M :=
  match k with (q, a, b) => (q, b, a) end.

Lemma am_sw_stp : forall M (k : tc2_cfg M), am_stp (am_swp M) (am_sw M k) = am_sw M (am_stp M k).
Proof.
  intros M [[q a] b]. simpl. unfold am_stp. simpl.
  destruct (am_nx M q a b) as [[[q' a'] b'] |]; reflexivity.
Qed.

Lemma am_sw_run : forall M n (k : tc2_cfg M), am_run (am_swp M) n (am_sw M k) = am_sw M (am_run M n k).
Proof.
  intros M n. induction n as [| n IH]; intro k; [reflexivity |].
  simpl. rewrite am_sw_stp. apply IH.
Qed.

Lemma am_sw_hlt : forall M (k : tc2_cfg M), am_hlt (am_swp M) (am_sw M k) <-> am_hlt M k.
Proof.
  intros M [[q a] b]. simpl. unfold am_hlt. simpl. split; intro H.
  - destruct (am_nx M q a b) as [[[q' a'] b'] |]; [discriminate | reflexivity].
  - rewrite H. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* the pigeonhole principle                                            *)
(* ------------------------------------------------------------------ *)

Lemma tc2_dup_or_nodup : forall (X : Type) (eqX : forall x y : X, {x = y} + {x <> y}) (f : nat -> X) n i,
  (exists a b, i <= a /\ a < b /\ b < i + n /\ f a = f b) \/ NoDup (map f (seq i n)).
Proof.
  intros X eqX f n. induction n as [| n IH]; intro i.
  - right. constructor.
  - destruct (IH (S i)) as [(a & b & H1 & H2 & H3 & H4) | Hnd].
    + left. exists a, b. repeat split; auto; lia.
    + destruct (in_dec eqX (f i) (map f (seq (S i) n))) as [Hin | Hnin].
      * left. apply in_map_iff in Hin. destruct Hin as (b & Hb & Hin). apply in_seq in Hin.
        exists i, b. repeat split; try lia. symmetry. exact Hb.
      * right. simpl. constructor; [exact Hnin | exact Hnd].
Qed.

Lemma tc2_pigeon_b : forall (X : Type) (eqX : forall x y : X, {x = y} + {x <> y}) (l : list X) (f : nat -> X),
  (forall t, t <= length l -> In (f t) l) -> exists i j, i < j /\ j <= length l /\ f i = f j.
Proof.
  intros X eqX l f Hin.
  destruct (tc2_dup_or_nodup X eqX f (S (length l)) 0) as [(a & b & H1 & H2 & H3 & H4) | Hnd].
  - exists a, b. repeat split; auto; lia.
  - exfalso.
    assert (Hle : length (map f (seq 0 (S (length l)))) <= length l).
    { apply NoDup_incl_length; [exact Hnd |]. intros y Hy. apply in_map_iff in Hy.
      destruct Hy as (t & <- & Ht). apply in_seq in Ht. apply Hin. lia. }
    rewrite map_length, seq_length in Hle. lia.
Qed.

Lemma tc2_bex_dec : forall (P : nat -> Prop), (forall n, {P n} + {~ P n}) -> forall n,
  {exists t, t <= n /\ P t} + {forall t, t <= n -> ~ P t}.
Proof.
  intros P Pd n. induction n as [| n IH].
  - destruct (Pd 0) as [H | H].
    + left. exists 0. split; [lia | exact H].
    + right. intros t Ht. assert (t = 0) by lia. subst. exact H.
  - destruct IH as [IH | H].
    + left. destruct IH as (t & H1 & H2). exists t. split; [lia | exact H2].
    + destruct (Pd (S n)) as [H' | H'].
      * left. exists (S n). split; [lia | exact H'].
      * right. intros t Ht. destruct (Nat.eq_dec t (S n)) as [-> | Hne]; [exact H' | apply H; lia].
Qed.

Lemma tc2_ball_dec : forall (P : nat -> Prop), (forall n, {P n} + {~ P n}) -> forall n,
  {forall t, t <= n -> P t} + {exists t, t <= n /\ ~ P t}.
Proof.
  intros P Pd n. induction n as [| n IH].
  - destruct (Pd 0) as [H | H].
    + left. intros t Ht. assert (t = 0) by lia. subst. exact H.
    + right. exists 0. split; [lia | exact H].
  - destruct IH as [H | IH].
    + destruct (Pd (S n)) as [H' | H'].
      * left. intros t Ht. destruct (Nat.eq_dec t (S n)) as [-> | Hne]; [exact H' | apply H; lia].
      * right. exists (S n). split; [lia | exact H'].
    + right. destruct IH as (t & H1 & H2). exists t. split; [lia | exact H2].
Qed.

Lemma tc2_least : forall (P : nat -> Prop), (forall n, {P n} + {~ P n}) -> (exists t, P t) ->
  exists t, P t /\ forall u, u < t -> ~ P u.
Proof.
  intros P Pd [t Ht]. revert Ht. induction t as [t IH] using lt_wf_ind; intro Ht.
  destruct t as [| t'].
  - exists 0. split; [exact Ht | intros u Hu; lia].
  - destruct (tc2_bex_dec P Pd t') as [Hex | Hno].
    + destruct Hex as (u & Hu & Hpu). exact (IH u ltac:(lia) Hpu).
    + exists (S t'). split; [exact Ht |]. intros u Hu. apply Hno. lia.
Qed.

Definition tc2_pick (n : nat) (P : nat -> bool) : nat :=
  match find P (seq 0 (S n)) with Some k => k | None => 0 end.

Lemma tc2_pick_spec : forall n P, (exists k, k <= n /\ P k = true) ->
  tc2_pick n P <= n /\ P (tc2_pick n P) = true.
Proof.
  intros n P (k & Hk & HP). unfold tc2_pick.
  destruct (find P (seq 0 (S n))) as [k' |] eqn:E.
  - apply find_some in E. destruct E as [Hin Hp]. apply in_seq in Hin. split; [lia | exact Hp].
  - exfalso. apply find_none with (x := k) in E; [congruence | apply in_seq; lia].
Qed.

Print Assumptions am_run_shB.
Print Assumptions tc2_pigeon_b.
Print Assumptions tc2_least.
