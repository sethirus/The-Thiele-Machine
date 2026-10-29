(** Tc2Embed.v: the EarnedCore machine as a tame abstract machine.

    A program P of EarnedCore (INC, DEC, HALT, CHECK, COMMIT, CERTIFY, with
    its version stamps, fact table, commitment channel and trap latch) is
    turned into a tame abstract machine of Tc2Am.v. The control of the
    abstract machine keeps, besides the program counter,

      - the trap latch,
      - whether the channel holds a commitment,
      - for each recorded fact: its property, its counter, and whether it is
        still about the current version of that counter

    and at most 16 facts (the capacity of the fact table). The numbers kept
    by the machine are only the two counters. A CHECK reads a counter through
    the property it names (zero, even, at least n); once the counter is at
    least one more than every n named in the program, a CHECK reads only the
    parity of the counter, and everything else reads only whether a counter
    is zero. That is the tameness.

    Dependencies: EarnedCore.v, Tc2Am.v. No axioms and no unfinished proofs.           *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedCore.
Require Import Minimal.Tc2Am.
Module E := Minimal.EarnedCore.
Set Default Goal Selector "!".

Definition tc2_prop_eq (p q : E.prop) : {p = q} + {p <> q}.
Proof. decide equality. apply Nat.eq_dec. Defined.

Definition tc2_ctr_eq (c d : E.ctr) : {c = d} + {c <> d}.
Proof. decide equality. Defined.

Definition tc2_fa : Type := (E.prop * E.ctr * bool)%type.
Definition tc2_Q : Type := (nat * bool * bool * list tc2_fa)%type.

Definition tc2_fa_eq : forall x y : tc2_fa, {x = y} + {x <> y}.
Proof.
  intros [[p c] b] [[p' c'] b'].
  destruct (tc2_prop_eq p p') as [-> | Hp]; [| right; congruence].
  destruct (tc2_ctr_eq c c') as [-> | Hc]; [| right; congruence].
  destruct (Bool.bool_dec b b') as [-> | Hb]; [left; reflexivity | right; congruence].
Defined.

Definition tc2_Q_eq : forall x y : tc2_Q, {x = y} + {x <> y}.
Proof.
  intros [[[a b] c] l] [[[a' b'] c'] l'].
  destruct (Nat.eq_dec a a') as [-> | H1]; [| right; congruence].
  destruct (Bool.bool_dec b b') as [-> | H2]; [| right; congruence].
  destruct (Bool.bool_dec c c') as [-> | H3]; [| right; congruence].
  destruct (list_eq_dec tc2_fa_eq l l') as [-> | H4]; [left; reflexivity | right; congruence].
Defined.

Definition tc2_fa_eqb (x y : tc2_fa) : bool := if tc2_fa_eq x y then true else false.

Lemma tc2_fa_eqb_true : forall x y, tc2_fa_eqb x y = true <-> x = y.
Proof.
  intros x y. unfold tc2_fa_eqb. destruct (tc2_fa_eq x y) as [H | H]; split; intro H'; auto; discriminate.
Qed.

(* a jump target, with every address outside the program folded to one dead address *)
Definition tc2_cl (n j : nat) : nat := if (1 <=? j) && (j <=? n) then j else S n.

Lemma tc2_cl_in : forall n j, 1 <= j -> j <= n -> tc2_cl n j = j.
Proof.
  intros n j H1 H2. unfold tc2_cl. replace ((1 <=? j) && (j <=? n)) with true; [reflexivity |].
  symmetry. apply andb_true_iff. split; apply Nat.leb_le; lia.
Qed.

Lemma tc2_cl_range : forall n j, 1 <= tc2_cl n j /\ tc2_cl n j <= S n.
Proof.
  intros n j. unfold tc2_cl. destruct ((1 <=? j) && (j <=? n)) eqn:H; [| lia].
  apply andb_true_iff in H. destruct H as [H1 H2]. apply Nat.leb_le in H1. apply Nat.leb_le in H2. lia.
Qed.

Lemma tc2_cl_out : forall n j, ~ (1 <= j /\ j <= n) -> tc2_cl n j = S n.
Proof.
  intros n j H. unfold tc2_cl.
  destruct (1 <=? j) eqn:E1, (j <=? n) eqn:E2; simpl; try reflexivity.
  apply Nat.leb_le in E1. apply Nat.leb_le in E2. lia.
Qed.

(* the facts about a counter lose their currency when the counter is written *)
Definition tc2_bump (c : E.ctr) (fl : list tc2_fa) : list tc2_fa :=
  map (fun f => match f with (p, d, b) => (p, d, if E.ctr_eqb d c then false else b) end) fl.

Definition tc2_ctrval (c : E.ctr) (a b : nat) : nat := match c with E.CA => a | E.CB => b end.

(* the transition of the abstract machine, instruction by instruction *)
Definition tc2_nxi (n : nat) (i : E.instr) (pc : nat) (er ch : bool) (fl : list tc2_fa) (a b : nat) :
  option (tc2_Q * nat * nat) :=
  match i with
  | E.HALT => None
  | E.INC E.CA => Some ((tc2_cl n (S pc), er, ch, tc2_bump E.CA fl), S a, b)
  | E.INC E.CB => Some ((tc2_cl n (S pc), er, ch, tc2_bump E.CB fl), a, S b)
  | E.DEC E.CA j =>
      match a with
      | 0 => Some ((tc2_cl n (S pc), er, ch, fl), 0, b)
      | S m => Some ((tc2_cl n j, er, ch, tc2_bump E.CA fl), m, b)
      end
  | E.DEC E.CB j =>
      match b with
      | 0 => Some ((tc2_cl n (S pc), er, ch, fl), a, 0)
      | S m => Some ((tc2_cl n j, er, ch, tc2_bump E.CB fl), a, m)
      end
  | E.CHECK p c =>
      if E.eval p (tc2_ctrval c a b) && Nat.ltb (length fl) E.fact_cap
      then Some ((tc2_cl n (S pc), er, ch, (p, c, true) :: fl), a, b)
      else Some ((pc, true, ch, fl), a, b)
  | E.COMMIT p c =>
      if existsb (fun f => tc2_fa_eqb f (p, c, true)) fl
      then Some ((tc2_cl n (S pc), er, true, fl), a, b)
      else Some ((pc, true, ch, fl), a, b)
  | E.CERTIFY =>
      if ch then Some ((tc2_cl n (S pc), er, ch, fl), a, b)
      else Some ((pc, true, ch, fl), a, b)
  end.

Definition tc2_nx (P : list E.instr) (q : tc2_Q) (a b : nat) : option (tc2_Q * nat * nat) :=
  match q with (((pc, er), ch), fl) =>
    if er then None else
    match E.fetch P pc with
    | None => None
    | Some i => tc2_nxi (length P) i pc er ch fl a b
    end
  end.

(* the abstraction of a core *)
Definition tc2_absf (k : E.core) (f : E.fact) : tc2_fa :=
  (E.f_prop f, E.f_ctr f, Nat.eqb (E.f_ver f) (E.ver k (E.f_ctr f))).

Definition tc2_abs (P : list E.instr) (k : E.core) : tc2_Q :=
  (tc2_cl (length P) (E.pc k), E.err k, match E.chan k with Some _ => true | None => false end,
   map (tc2_absf k) (E.facts k)).

Definition tc2_inv (P : list E.instr) (k : E.core) : Prop :=
  (forall f, In f (E.facts k) -> E.f_ver f <= E.ver k (E.f_ctr f) /\ In (E.CHECK (E.f_prop f) (E.f_ctr f)) P) /\
  length (E.facts k) <= E.fact_cap.

Lemma tc2_inv_start : forall P a b, tc2_inv P (E.start_core a b).
Proof. intros P a b. split; [intros f Hf; simpl in Hf; contradiction | simpl; unfold E.fact_cap; lia]. Qed.

Lemma tc2_next_in : forall P k i, E.next_instr P k = Some i ->
  E.err k = false /\ E.fetch P (E.pc k) = Some i /\ In i P /\ 1 <= E.pc k /\ E.pc k <= length P /\ i <> E.HALT.
Proof.
  intros P k i H. unfold E.next_instr in H.
  destruct (E.err k) eqn:He; [discriminate |].
  destruct (E.fetch P (E.pc k)) as [j |] eqn:Hf; [| discriminate].
  assert (Hj : j <> E.HALT) by (intro Hh; subst j; discriminate).
  assert (Hij : i = j) by (destruct j; try (injection H as <-; reflexivity); contradiction).
  subst j.
  assert (Hrange : 1 <= E.pc k /\ E.pc k <= length P /\ In i P).
  { unfold E.fetch in Hf. destruct (E.pc k) as [| m] eqn:Hp; [discriminate |].
    assert (Hlt : m < length P) by (apply nth_error_Some; rewrite Hf; discriminate).
    split; [lia | split; [lia | eapply nth_error_In; exact Hf]]. }
  destruct Hrange as (R1 & R2 & R3).
  refine (conj eq_refl (conj eq_refl (conj R3 (conj R1 (conj R2 Hj))))).
Qed.

Lemma tc2_fetch_cl : forall (P : list E.instr) j, E.fetch P (tc2_cl (length P) j) = E.fetch P j.
Proof.
  intros P j. unfold tc2_cl. destruct ((1 <=? j) && (j <=? length P)) eqn:H.
  - reflexivity.
  - change (E.fetch P (S (length P))) with (nth_error P (length P)).
    rewrite (proj2 (nth_error_None P (length P)) (le_n _)).
    destruct j as [| m]; [reflexivity |]. change (E.fetch P (S m)) with (nth_error P m).
    symmetry. apply nth_error_None. apply andb_false_iff in H.
    destruct H as [H | H]; apply Nat.leb_gt in H; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* the abstraction of the basic moves                                  *)
(* ------------------------------------------------------------------ *)

Definition tc2_chb (k : E.core) : bool := match E.chan k with Some _ => true | None => false end.

Lemma tc2_abs_write : forall P k c n j, tc2_inv P k ->
  tc2_abs P (E.write k c n j) =
    (tc2_cl (length P) j, E.err k, tc2_chb k, tc2_bump c (map (tc2_absf k) (E.facts k))).
Proof.
  intros P k c n j [Hf _]. unfold tc2_abs, tc2_chb, tc2_bump.
  destruct c; cbn [E.write E.pc E.err E.chan E.facts]; f_equal; rewrite map_map; apply map_ext_in;
    intros [p d v] Hin; destruct (Hf _ Hin) as [Hv _]; cbn [E.f_ver E.f_ctr E.f_prop] in Hv;
    unfold tc2_absf; cbn [E.f_prop E.f_ctr E.f_ver]; destruct d; cbn [E.ver E.ctr_eqb E.va E.vb] in *; auto;
    f_equal; try (apply Nat.eqb_neq; lia).
Qed.

Lemma tc2_abs_goto : forall P k j,
  tc2_abs P (E.goto k j) = (tc2_cl (length P) j, E.err k, tc2_chb k, map (tc2_absf k) (E.facts k)).
Proof. intros P k j. unfold tc2_abs, tc2_chb. reflexivity. Qed.

Lemma tc2_abs_trap : forall P k,
  tc2_abs P (E.trap k) = (tc2_cl (length P) (E.pc k), true, tc2_chb k, map (tc2_absf k) (E.facts k)).
Proof. intros P k. unfold tc2_abs, tc2_chb. reflexivity. Qed.

Lemma tc2_abs_record : forall P k p c,
  tc2_abs P (E.record_fact k (E.claim k p c)) =
    (tc2_cl (length P) (S (E.pc k)), E.err k, tc2_chb k, (p, c, true) :: map (tc2_absf k) (E.facts k)).
Proof.
  intros P k p c. unfold tc2_abs, tc2_chb, E.record_fact, E.claim. cbn [E.pc E.err E.chan E.facts].
  f_equal. simpl. f_equal. unfold tc2_absf. cbn [E.f_prop E.f_ctr E.f_ver]. f_equal. apply Nat.eqb_refl.
Qed.

Lemma tc2_abs_commit : forall P k p c,
  tc2_abs P (E.commit_to k (E.claim k p c)) =
    (tc2_cl (length P) (S (E.pc k)), E.err k, true, map (tc2_absf k) (E.facts k)).
Proof. intros P k p c. unfold tc2_abs, E.commit_to. reflexivity. Qed.

Lemma tc2_existsb_commit : forall k p c fs,
  existsb (fun f => tc2_fa_eqb f (p, c, true)) (map (tc2_absf k) fs) =
  existsb (E.fact_eqb (E.claim k p c)) fs.
Proof.
  intros k p c fs. induction fs as [| [q d v] fs IH]; [reflexivity |].
  simpl. rewrite IH. f_equal.
  apply Bool.eq_iff_eq_true. rewrite tc2_fa_eqb_true, E.fact_eqb_eq. unfold tc2_absf, E.claim.
  cbn [E.f_prop E.f_ctr E.f_ver]. split.
  - intros H. injection H as H1 H2 H3. apply Nat.eqb_eq in H3. subst. reflexivity.
  - intros H. injection H as H1 H2 H3. subst. f_equal. f_equal. apply Nat.eqb_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* the invariant is kept                                               *)
(* ------------------------------------------------------------------ *)

Lemma tc2_facts_write : forall k c n j, E.facts (E.write k c n j) = E.facts k.
Proof. intros k c n j. destruct c; reflexivity. Qed.

Lemma tc2_inv_cexec : forall P k i, tc2_inv P k -> E.next_instr P k = Some i -> tc2_inv P (E.cexec k i).
Proof.
  intros P k i Hinv Hn. destruct (tc2_next_in P k i Hn) as (He & Hf & Hin & R1 & R2 & Hne).
  destruct Hinv as [Hf1 Hf2]. unfold E.cexec. rewrite He.
  assert (Hwr : forall c n j, tc2_inv P (E.write k c n j)).
  { intros c n j. split.
    - intros f Hf'. rewrite tc2_facts_write in Hf'. destruct (Hf1 f Hf') as [H1 H2]. split; [| exact H2].
      destruct c, (E.f_ctr f); cbn [E.write E.ver E.va E.vb E.facts] in *; lia.
    - rewrite tc2_facts_write. exact Hf2. }
  destruct i as [c | c j | | p c | p c |].
  - apply Hwr.
  - destruct c; cbn [E.val]; [destruct (E.ca k) | destruct (E.cb k)];
      first [apply Hwr | split; [intros f Hf'; exact (Hf1 f Hf') | exact Hf2]].
  - contradiction.
  - destruct (E.check_ok k p c) eqn:Hc.
    + split.
      * intros f [<- | Hf']; [| exact (Hf1 f Hf')].
        unfold E.claim. cbn [E.f_ver E.f_ctr E.f_prop]. split; [apply le_n |].
        unfold E.record_fact. cbn [E.facts]. exact Hin.
      * unfold E.check_ok in Hc. apply andb_true_iff in Hc. destruct Hc as [_ Hc]. apply Nat.ltb_lt in Hc.
        unfold E.record_fact. cbn [E.facts]. simpl. lia.
    + split; [intros f Hf'; exact (Hf1 f Hf') | exact Hf2].
  - destruct (E.commit_ok k p c).
    + split; [intros f Hf'; exact (Hf1 f Hf') | exact Hf2].
    + split; [intros f Hf'; exact (Hf1 f Hf') | exact Hf2].
  - destruct (E.certify_ok k); (split; [intros f Hf'; exact (Hf1 f Hf') | exact Hf2]).
Qed.

Definition tc2_stp (P : list E.instr) (x : tc2_Q * nat * nat) : tc2_Q * nat * nat :=
  match x with (q, a, b) => match tc2_nx P q a b with Some y => y | None => x end end.

Lemma tc2_inv_step : forall P k, tc2_inv P k -> tc2_inv P (E.core_step P k).
Proof.
  intros P k H. unfold E.core_step. destruct (E.next_instr P k) as [i |] eqn:Hn;
    [apply tc2_inv_cexec; assumption | exact H].
Qed.

Lemma tc2_nx_none : forall P k, E.next_instr P k = None ->
  tc2_nx P (tc2_abs P k) (E.ca k) (E.cb k) = None.
Proof.
  intros P k Hn. unfold E.next_instr in Hn. unfold tc2_abs, tc2_nx.
  destruct (E.err k) eqn:He; [reflexivity |].
  rewrite tc2_fetch_cl. destruct (E.fetch P (E.pc k)) as [i |] eqn:Hf; [| reflexivity].
  destruct i; try discriminate Hn. reflexivity.
Qed.

Lemma tc2_nx_some : forall P k i, E.next_instr P k = Some i ->
  tc2_nx P (tc2_abs P k) (E.ca k) (E.cb k) =
    tc2_nxi (length P) i (E.pc k) false (tc2_chb k) (map (tc2_absf k) (E.facts k)) (E.ca k) (E.cb k).
Proof.
  intros P k i Hn. destruct (tc2_next_in P k i Hn) as (He & Hf & Hin & R1 & R2 & Hne).
  unfold tc2_abs, tc2_nx. rewrite He, tc2_fetch_cl, Hf. rewrite tc2_cl_in by assumption. reflexivity.
Qed.

Lemma tc2_sim_step : forall P k, tc2_inv P k ->
  (tc2_abs P (E.core_step P k), E.ca (E.core_step P k), E.cb (E.core_step P k)) =
  tc2_stp P (tc2_abs P k, E.ca k, E.cb k).
Proof.
  intros P k Hinv. unfold tc2_stp.
  destruct (E.next_instr P k) as [i |] eqn:Hn.
  - rewrite (tc2_nx_some P k i Hn).
    destruct (tc2_next_in P k i Hn) as (He & Hf & Hin & R1 & R2 & Hne).
    unfold E.core_step. rewrite Hn. unfold E.cexec. rewrite He.
    destruct i as [c | c j | | p c | p c |]; unfold tc2_nxi.
    + destruct c; cbn [E.val]; rewrite tc2_abs_write by exact Hinv; rewrite He; reflexivity.
    + destruct c; cbn [E.val].
      * destruct (E.ca k) as [| m] eqn:Ha.
        -- rewrite tc2_abs_goto, He. unfold E.goto. cbn [E.ca E.cb]. rewrite Ha. reflexivity.
        -- rewrite tc2_abs_write by exact Hinv. rewrite He. reflexivity.
      * destruct (E.cb k) as [| m] eqn:Hb.
        -- rewrite tc2_abs_goto, He. unfold E.goto. cbn [E.ca E.cb]. rewrite Hb. reflexivity.
        -- rewrite tc2_abs_write by exact Hinv. rewrite He. reflexivity.
    + contradiction.
    + assert (Hck : E.check_ok k p c = E.eval p (tc2_ctrval c (E.ca k) (E.cb k)) && Nat.ltb (length (map (tc2_absf k) (E.facts k))) E.fact_cap).
      { unfold E.check_ok. rewrite He, map_length. destruct c; reflexivity. }
      rewrite Hck. destruct (E.eval p (tc2_ctrval c (E.ca k) (E.cb k)) && Nat.ltb (length (map (tc2_absf k) (E.facts k))) E.fact_cap).
      * rewrite tc2_abs_record, He. reflexivity.
      * rewrite tc2_abs_trap, tc2_cl_in by assumption. reflexivity.
    + assert (Hco : E.commit_ok k p c = existsb (fun f => tc2_fa_eqb f (p, c, true)) (map (tc2_absf k) (E.facts k))).
      { unfold E.commit_ok. rewrite He, tc2_existsb_commit. reflexivity. }
      rewrite Hco. destruct (existsb (fun f => tc2_fa_eqb f (p, c, true)) (map (tc2_absf k) (E.facts k))).
      * rewrite tc2_abs_commit, He. reflexivity.
      * rewrite tc2_abs_trap, tc2_cl_in by assumption. reflexivity.
    + assert (Hce : E.certify_ok k = tc2_chb k).
      { unfold E.certify_ok, tc2_chb. rewrite He. destruct (E.chan k); reflexivity. }
      rewrite Hce. destruct (tc2_chb k) eqn:Hch.
      * rewrite tc2_abs_goto, He, Hch. reflexivity.
      * rewrite tc2_abs_trap, tc2_cl_in by assumption. rewrite Hch. reflexivity.
  - unfold E.core_step. rewrite Hn. rewrite (tc2_nx_none P k Hn). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* the finite control, and its size                                    *)
(* ------------------------------------------------------------------ *)

Fixpoint tc2_lu {X : Type} (n : nat) (al : list X) : list (list X) :=
  match n with
  | 0 => [[]]
  | S m => [] :: flat_map (fun x => map (cons x) (tc2_lu m al)) al
  end.

Lemma tc2_lu_in : forall {X : Type} n (al : list X) l, length l <= n -> (forall x, In x l -> In x al) ->
  In l (tc2_lu n al).
Proof.
  intros X n al. induction n as [| n IH]; intros l Hl Hin.
  - destruct l; [left; reflexivity | simpl in Hl; lia].
  - destruct l as [| x l].
    + left. reflexivity.
    + right. apply in_flat_map. exists x. split; [apply Hin; left; reflexivity |].
      apply in_map. apply IH; [simpl in Hl; lia | intros y Hy; apply Hin; right; exact Hy].
Qed.

Fixpoint tc2_pw (b e : nat) : nat := match e with 0 => 1 | S e' => b * tc2_pw b e' end.

Lemma tc2_flat_len : forall {X : Type} (L : list (list X)) (al : list X),
  length (flat_map (fun x => map (cons x) L) al) = length al * length L.
Proof.
  intros X L al. induction al as [| x al IH]; [reflexivity |].
  simpl. rewrite app_length, map_length, IH. reflexivity.
Qed.

Lemma tc2_pw_pos : forall b e, 1 <= b -> 1 <= tc2_pw b e.
Proof. intros b e Hb. induction e as [| e IH]; simpl; [lia | nia]. Qed.

Lemma tc2_lu_len : forall {X : Type} n (al : list X), length (tc2_lu n al) <= tc2_pw (S (length al)) n.
Proof.
  intros X n al. induction n as [| n IH]; [simpl; lia |].
  simpl tc2_lu. simpl length. rewrite tc2_flat_len. simpl tc2_pw.
  pose proof (tc2_pw_pos (S (length al)) n ltac:(lia)). nia.
Qed.

Definition tc2_thr (P : list E.instr) : nat :=
  fold_right Nat.max 0 (map (fun i => match i with E.CHECK (E.PGe n) _ => n | _ => 0 end) P).

Lemma tc2_thr_ge : forall P n c, In (E.CHECK (E.PGe n) c) P -> n <= tc2_thr P.
Proof.
  intros P n c. induction P as [| i P IH]; intro H; [contradiction |].
  unfold tc2_thr. simpl. destruct H as [Hi | H].
  - subst i. apply Nat.le_max_l.
  - pose proof (IH H) as H1. unfold tc2_thr in H1. etransitivity; [exact H1 | apply Nat.le_max_r].
Qed.

Definition tc2_fal (P : list E.instr) : list tc2_fa :=
  flat_map (fun i => match i with E.CHECK p c => [(p, c, true); (p, c, false)] | _ => [] end) P.

Lemma tc2_fal_in : forall P p c b, In (p, c, b) (tc2_fal P) <-> In (E.CHECK p c) P.
Proof.
  intros P p c b. unfold tc2_fal. rewrite in_flat_map. split.
  - intros (i & Hi & H). destruct i as [x | x y | | q d | q d |]; simpl in H; try contradiction.
    destruct H as [H | [H | H]]; [| | contradiction]; injection H as <- <- _; exact Hi.
  - intro H. exists (E.CHECK p c). split; [exact H |]. simpl. destruct b; [left | right; left]; reflexivity.
Qed.

Lemma tc2_flat_len2 : forall {A B : Type} (f : A -> list B) (l : list A),
  (forall x, length (f x) <= 2) -> length (flat_map f l) <= 2 * length l.
Proof.
  intros A B f l H. induction l as [| x l IH]; [simpl; lia |].
  simpl. rewrite app_length. pose proof (H x). lia.
Qed.

Lemma tc2_fal_len : forall P, length (tc2_fal P) <= 2 * length P.
Proof.
  intro P. unfold tc2_fal. apply tc2_flat_len2. intro i. destruct i; simpl; lia.
Qed.

Definition tc2_lq (P : list E.instr) : list tc2_Q :=
  list_prod (list_prod (list_prod (seq 1 (S (length P))) [false; true]) [false; true])
    (tc2_lu E.fact_cap (tc2_fal P)).

Definition tc2_okq (P : list E.instr) (q : tc2_Q) : Prop :=
  match q with (((pc, er), ch), fl) =>
    1 <= pc /\ pc <= S (length P) /\ length fl <= E.fact_cap /\
    forall x, In x fl -> In (E.CHECK (fst (fst x)) (snd (fst x))) P
  end.

Lemma tc2_lu_ok : forall {X : Type} n (al : list X) l, In l (tc2_lu n al) ->
  length l <= n /\ forall x, In x l -> In x al.
Proof.
  intros X n al. induction n as [| n IH]; intros l H.
  - simpl in H. destruct H as [<- | []]. simpl. split; [lia | intros x []].
  - simpl in H. destruct H as [<- | H].
    + simpl. split; [lia | intros x []].
    + apply in_flat_map in H. destruct H as (x & Hx & H). apply in_map_iff in H. destruct H as (l' & <- & Hl').
      destruct (IH l' Hl') as [H1 H2]. simpl. split; [lia |].
      intros y [<- | Hy]; [exact Hx | apply H2; exact Hy].
Qed.

Lemma tc2_lq_in : forall P q, In q (tc2_lq P) <-> tc2_okq P q.
Proof.
  intros P [[[pc er] ch] fl]. unfold tc2_lq, tc2_okq. split.
  - intro H. apply in_prod_iff in H. destruct H as [H1 Hfl]. apply in_prod_iff in H1. destruct H1 as [H2 Hch].
    apply in_prod_iff in H2. destruct H2 as [Hpc Her]. apply in_seq in Hpc.
    destruct (tc2_lu_ok _ _ _ Hfl) as [F1 F2].
    repeat split; [lia | lia | exact F1 |]. intros [[p c] b] Hx. cbn [fst snd]. apply (proj1 (tc2_fal_in P p c b)). apply F2. exact Hx.
  - intros (H1 & H2 & H3 & H4). apply in_prod_iff. split.
    + apply in_prod_iff. split.
      * apply in_prod_iff. split; [apply in_seq; lia | destruct er; [right; left | left]; reflexivity].
      * destruct ch; [right; left | left]; reflexivity.
    + apply tc2_lu_in; [exact H3 |]. intros [[p c] b] Hx. apply (proj2 (tc2_fal_in P p c b)). exact (H4 _ Hx).
Qed.

Lemma tc2_bump_ok : forall P c fl,
  (forall x, In x fl -> In (E.CHECK (fst (fst x)) (snd (fst x))) P) ->
  length (tc2_bump c fl) = length fl /\
  forall x, In x (tc2_bump c fl) -> In (E.CHECK (fst (fst x)) (snd (fst x))) P.
Proof.
  intros P c fl H. unfold tc2_bump. split; [apply map_length |].
  intros x Hx. apply in_map_iff in Hx. destruct Hx as ([[p d] b] & <- & Hin).
  specialize (H _ Hin). cbn [fst snd] in *. exact H.
Qed.

Lemma tc2_fetch_in : forall (P : list E.instr) n i, E.fetch P n = Some i -> In i P /\ 1 <= n /\ n <= length P.
Proof.
  intros P n i H. unfold E.fetch in H. destruct n as [| m]; [discriminate |].
  assert (Hlt : m < length P) by (apply nth_error_Some; rewrite H; discriminate).
  split; [eapply nth_error_In; exact H | lia].
Qed.

Lemma tc2_nx_okq : forall P q a b q' a' b', tc2_okq P q -> tc2_nx P q a b = Some (q', a', b') -> tc2_okq P q'.
Proof.
  intros P [[[pc er] ch] fl] a b q' a' b' Hok H. unfold tc2_nx in H.
  destruct er; [discriminate |].
  destruct (E.fetch P pc) as [i |] eqn:Hf; [| discriminate].
  destruct (tc2_fetch_in P pc i Hf) as (Hin & R1 & R2).
  destruct Hok as (O1 & O2 & O3 & O4).
  destruct (tc2_bump_ok P E.CA fl O4) as [BA1 BA2]. destruct (tc2_bump_ok P E.CB fl O4) as [BB1 BB2].
  destruct (tc2_cl_range (length P) (S pc)) as [C1 C2].
  unfold tc2_nxi in H.
  destruct i as [c | c j | | p c | p c |].
  - destruct c; injection H as <- <- <-.
    + split; [exact C1 | split; [exact C2 | split; [rewrite BA1; exact O3 | exact BA2]]].
    + split; [exact C1 | split; [exact C2 | split; [rewrite BB1; exact O3 | exact BB2]]].
  - destruct (tc2_cl_range (length P) j) as [D1 D2].
    destruct c; [destruct a as [| m] | destruct b as [| m]]; injection H as <- <- <-;
      (split; [first [exact C1 | exact D1] | split; [first [exact C2 | exact D2] | split; [first [exact O3 | rewrite BA1; exact O3 | rewrite BB1; exact O3] | first [exact O4 | exact BA2 | exact BB2]]]]).
  - discriminate.
  - destruct (E.eval p (tc2_ctrval c a b) && Nat.ltb (length fl) E.fact_cap) eqn:Hg.
    + injection H as <- <- <-. apply andb_true_iff in Hg. destruct Hg as [_ Hg]. apply Nat.ltb_lt in Hg.
      split; [exact C1 | split; [exact C2 | split; [simpl; lia |]]].
      intros x [<- | Hx]; [cbn [fst snd]; exact Hin | exact (O4 _ Hx)].
    + injection H as <- <- <-. repeat split; [exact O1 | exact O2 | exact O3 | exact O4].
  - destruct (existsb (fun f => tc2_fa_eqb f (p, c, true)) fl).
    + injection H as <- <- <-. repeat split; [exact C1 | exact C2 | exact O3 | exact O4].
    + injection H as <- <- <-. repeat split; [exact O1 | exact O2 | exact O3 | exact O4].
  - destruct ch.
    + injection H as <- <- <-. repeat split; [exact C1 | exact C2 | exact O3 | exact O4].
    + injection H as <- <- <-. repeat split; [exact O1 | exact O2 | exact O3 | exact O4].
Qed.

Lemma tc2_nx_step1 : forall P q a b q' a' b', tc2_nx P q a b = Some (q', a', b') ->
  (a' = a /\ (b' = b \/ b' = S b \/ S b' = b)) \/ (b' = b /\ (a' = S a \/ S a' = a)).
Proof.
  intros P [[[pc er] ch] fl] a b q' a' b' H. unfold tc2_nx in H.
  destruct er; [discriminate |].
  destruct (E.fetch P pc) as [i |]; [| discriminate].
  unfold tc2_nxi in H.
  destruct i as [c | c j | | p c | p c |].
  - destruct c; injection H as <- <- <-; [right; split; auto | left; split; auto].
  - destruct c; [destruct a as [| m] | destruct b as [| m]]; injection H as <- <- <-;
      first [left; split; [reflexivity | left; reflexivity] | right; split; [reflexivity | right; reflexivity]
            | left; split; [reflexivity | right; right; reflexivity]].
  - discriminate.
  - destruct (E.eval p (tc2_ctrval c a b) && Nat.ltb (length fl) E.fact_cap); injection H as <- <- <-; left; split; first [reflexivity | left; reflexivity].
  - destruct (existsb (fun f => tc2_fa_eqb f (p, c, true)) fl); injection H as <- <- <-; left; split; first [reflexivity | left; reflexivity].
  - destruct ch; injection H as <- <- <-; left; split; first [reflexivity | left; reflexivity].
Qed.

Lemma tc2_even_shift : forall a d, Nat.even (a + 2 * d) = Nat.even a.
Proof.
  intros a d. rewrite Nat.even_add. replace (Nat.even (2 * d)) with true; [destruct (Nat.even a); reflexivity |].
  symmetry. rewrite Nat.even_mul. reflexivity.
Qed.

Lemma tc2_eval_shift : forall P p c a d, In (E.CHECK p c) P -> S (tc2_thr P) <= a ->
  E.eval p (a + 2 * d) = E.eval p a.
Proof.
  intros P p c a d Hin Ha. destruct p as [| | n]; simpl.
  - destruct a; [lia |]. reflexivity.
  - apply tc2_even_shift.
  - pose proof (tc2_thr_ge P n c Hin). apply Bool.eq_iff_eq_true. rewrite !Nat.leb_le. lia.
Qed.

Lemma tc2_nx_tameA : forall P q a b d, S (tc2_thr P) <= a ->
  tc2_nx P q (a + 2 * d) b =
    match tc2_nx P q a b with Some (q', a', b') => Some (q', a' + 2 * d, b') | None => None end.
Proof.
  intros P [[[pc er] ch] fl] a b d Ha. unfold tc2_nx.
  destruct er; [reflexivity |].
  destruct (E.fetch P pc) as [i |] eqn:Hf; [| reflexivity].
  destruct (tc2_fetch_in P pc i Hf) as (Hin & _ & _).
  unfold tc2_nxi.
  destruct i as [c | c j | | p c | p c |].
  - destruct c; reflexivity.
  - destruct c.
    + destruct a as [| m]; [lia | reflexivity].
    + destruct b as [| m]; reflexivity.
  - reflexivity.
  - destruct c; cbn [tc2_ctrval].
    + rewrite (tc2_eval_shift P p E.CA a d Hin Ha).
      destruct (E.eval p a && Nat.ltb (length fl) E.fact_cap); reflexivity.
    + destruct (E.eval p b && Nat.ltb (length fl) E.fact_cap); reflexivity.
  - destruct (existsb (fun f => tc2_fa_eqb f (p, c, true)) fl); reflexivity.
  - destruct ch; reflexivity.
Qed.

Lemma tc2_nx_tameB : forall P q a b d, S (tc2_thr P) <= b ->
  tc2_nx P q a (b + 2 * d) =
    match tc2_nx P q a b with Some (q', a', b') => Some (q', a', b' + 2 * d) | None => None end.
Proof.
  intros P [[[pc er] ch] fl] a b d Hb. unfold tc2_nx.
  destruct er; [reflexivity |].
  destruct (E.fetch P pc) as [i |] eqn:Hf; [| reflexivity].
  destruct (tc2_fetch_in P pc i Hf) as (Hin & _ & _).
  unfold tc2_nxi.
  destruct i as [c | c j | | p c | p c |].
  - destruct c; reflexivity.
  - destruct c.
    + destruct a as [| m]; reflexivity.
    + destruct b as [| m]; [lia | reflexivity].
  - reflexivity.
  - destruct c; cbn [tc2_ctrval].
    + destruct (E.eval p a && Nat.ltb (length fl) E.fact_cap); reflexivity.
    + rewrite (tc2_eval_shift P p E.CB b d Hin Hb).
      destruct (E.eval p b && Nat.ltb (length fl) E.fact_cap); reflexivity.
  - destruct (existsb (fun f => tc2_fa_eqb f (p, c, true)) fl); reflexivity.
  - destruct ch; reflexivity.
Qed.

(* the EarnedCore program as a tame abstract machine *)
Definition tc2_am_of (P : list E.instr) : tc2_am.
Proof.
  refine (mk_tc2_am tc2_Q tc2_Q_eq (tc2_nx P) (S (tc2_thr P)) (tc2_lq P) _ _ _ _ _).
  - lia.
  - intros q a b q' a' b' Hq H. apply tc2_lq_in. apply (tc2_nx_okq P q a b q' a' b'); [apply tc2_lq_in; exact Hq | exact H].
  - intros q a b q' a' b' H. exact (tc2_nx_step1 P q a b q' a' b' H).
  - intros q a b d H. exact (tc2_nx_tameA P q a b d H).
  - intros q a b d H. exact (tc2_nx_tameB P q a b d H).
Defined.

Lemma tc2_am_stp : forall P x, am_stp (tc2_am_of P) x = tc2_stp P x.
Proof. intros P [[q a] b]. reflexivity. Qed.

(* the run of the program and the run of the machine agree *)
Lemma tc2_sim_run : forall P n k, tc2_inv P k ->
  (tc2_abs P (E.core_run n P k), E.ca (E.core_run n P k), E.cb (E.core_run n P k)) =
  am_run (tc2_am_of P) n (tc2_abs P k, E.ca k, E.cb k).
Proof.
  intros P n. induction n as [| n IH]; intros k Hinv; [reflexivity |].
  simpl E.core_run. rewrite am_run_S_l. rewrite tc2_am_stp. rewrite <- (tc2_sim_step P k Hinv).
  apply IH. apply tc2_inv_step. exact Hinv.
Qed.

Lemma tc2_inv_run : forall P n k, tc2_inv P k -> tc2_inv P (E.core_run n P k).
Proof.
  intros P n. induction n as [| n IH]; intros k H; [exact H |].
  simpl. apply IH. apply tc2_inv_step. exact H.
Qed.

Lemma tc2_nxi_some : forall n i pc er ch fl a b, i <> E.HALT -> tc2_nxi n i pc er ch fl a b <> None.
Proof.
  intros n i pc er ch fl a b Hne. unfold tc2_nxi. destruct i as [c | c j | | p c | p c |]; try contradiction; try discriminate.
  - destruct c; discriminate.
  - destruct c; [destruct a | destruct b]; discriminate.
  - destruct (E.eval p (tc2_ctrval c a b) && Nat.ltb (length fl) E.fact_cap); discriminate.
  - destruct (existsb (fun f => tc2_fa_eqb f (p, c, true)) fl); discriminate.
  - destruct ch; discriminate.
Qed.

Lemma tc2_halted_iff : forall P k, tc2_nx P (tc2_abs P k) (E.ca k) (E.cb k) = None <-> E.next_instr P k = None.
Proof.
  intros P k. split.
  - intro H. destruct (E.next_instr P k) as [i |] eqn:Hn; [| reflexivity].
    exfalso. rewrite (tc2_nx_some P k i Hn) in H.
    destruct (tc2_next_in P k i Hn) as (_ & _ & _ & _ & _ & Hne). exact (tc2_nxi_some _ _ _ _ _ _ _ _ Hne H).
  - apply tc2_nx_none.
Qed.

(* the plain function of a program: counter A when it stops, started with the input in A and 0 in B *)
Definition tc2_pf (P : list E.instr) (x y : nat) : Prop :=
  exists N, E.halted P (E.core_of (E.run_prog N P (E.start x 0))) /\
            E.ca (E.core_of (E.run_prog N P (E.start x 0))) = y.

Definition tc2_q0 (P : list E.instr) : tc2_Q := tc2_abs P (E.start_core 0 0).

Lemma tc2_abs_start : forall P x, tc2_abs P (E.start_core x 0) = tc2_q0 P.
Proof. intros P x. reflexivity. Qed.

Theorem tc2_pf_iff : forall P x y, tc2_pf P x y <->
  exists n, am_hlt (tc2_am_of P) (am_run (tc2_am_of P) n (tc2_q0 P, x, 0)) /\
            am_a (tc2_am_of P) (am_run (tc2_am_of P) n (tc2_q0 P, x, 0)) = y.
Proof.
  intros P x y.
  assert (Hrun : forall n, (tc2_abs P (E.core_run n P (E.start_core x 0)), E.ca (E.core_run n P (E.start_core x 0)),
                            E.cb (E.core_run n P (E.start_core x 0))) = am_run (tc2_am_of P) n (tc2_q0 P, x, 0)).
  { intro n. rewrite (tc2_sim_run P n (E.start_core x 0) (tc2_inv_start P x 0)). reflexivity. }
  assert (Hcore : forall n, E.core_of (E.run_prog n P (E.start x 0)) = E.core_run n P (E.start_core x 0)).
  { intro n. rewrite E.core_run_prog. reflexivity. }
  split.
  - intros (N & Hh & Hy). exists N. rewrite Hcore in Hh, Hy. rewrite <- Hrun.
    split; [| exact Hy]. unfold am_hlt. cbn [am_nx tc2_am_of]. unfold E.halted in Hh.
    cbn [fst snd]. apply tc2_halted_iff. exact Hh.
  - intros (n & Hh & Hy). exists n. rewrite Hcore. rewrite <- Hrun in Hh, Hy.
    split; [| exact Hy]. unfold E.halted. apply tc2_halted_iff. exact Hh.
Qed.

Print Assumptions tc2_pf_iff.
