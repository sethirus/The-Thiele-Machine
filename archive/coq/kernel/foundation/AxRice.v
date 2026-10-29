(** AxRice: Rice's theorem and the diagonal at every point of the record axis.

    The host machine (EarnedMulti.v with the property PSlot, the machine the
    universal program runs on) keeps a record of what its program has
    established.  Read the record through any order: a reading is a function
    from final host states to a preordered set (A, <=), and a point of the
    axis is any a in A.  The threshold test of a is "a <= record", a Boolean
    given by the order itself.  A program REACHES a on an input when it
    stops and the record of its final state is at or above a.

    Two programs behave alike at a when on every input both run forever, or
    both stop and either both reach a or neither does.  They behave alike on
    the record when on every input both run forever or both stop with
    equivalent records.

    What a reading may depend on.  A reading is OBSERVABLE at one of two
    levels, and the level decides which theorem applies.
      Level 1  (ax_reads_hagree): the record is a function of everything a
               program can read of its final state: every register, the fact
               table, the channel, the trap latch, the ledger, the flag.
      Level 2  (ax_reads_obs):    the record is a function of the six
               numbers the recursion theorem with record preserves: register
               0, the trap latch, the ledger, the flag, the number of facts
               and whether the channel is empty.
    Every level 2 reading is a level 1 reading.

    Results (all closed):

      ax_rice_threshold   For a level 1 reading and any point a: a property
                          of programs that respects behaving alike at a, holds
                          of one program and fails of another, is undecidable
                          (the vendored sense: a decider would make the
                          complement of single-tape Turing machine halting
                          enumerable).
      ax_rice_record      The same for properties that respect behaving alike
                          on the whole record.
      ax_diagonal_threshold  For a level 2 reading and any point a: let Pi
                          respect behaving alike at a, hold of yes and fail
                          of no.  No Boolean function d on programs, whose
                          flip (no where d says yes, yes where d says no)
                          some host program computes on program numbers, is
                          correct for Pi.
      ax_diagonal_record  The same for the whole record.

    The host record.  ax_host_rec reads a final state as the quadruple
    (flag, number of facts, channel committed, trap latch) in the product of
    the two-point order, the chain of the natural numbers, and two more
    two-point orders.  It is a level 2 reading, so every theorem above
    applies to every one of its points.  The points that matter are
    reached: a program reaches the flag, a committed channel, the trap, and
    for every k up to the cap of 16 exactly k facts (ax_facts_reach).  No
    program reaches 17 facts (ax_facts_cap), so the point "17 facts" is
    unreachable and every property of "reaches it" is trivial: the host axis
    has 17 levels of fact count and no more.  For every reachable point not
    below the floor the property "reaches a on some input" is nontrivial,
    hence undecidable (ax_reach_undecidable).

    Where this stops.  A threshold on the CONTENT of the fact table (which
    claim is in it) is a level 1 reading but not a level 2 reading: Rice
    holds there, and the diagonal as proved here does not, because the
    recursion theorem with record preserves the number of facts and not
    their content (SmFixedPoint.v, SmNoExact.v).  The record axis whose
    points are the numbers of facts, the flag, the channel and the trap is the
    one the host's earned layer prices; the content is an object of the
    certified-claims axis of AxSmall.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Synthetic Require Import Undecidability.
From Kernel Require Import AxCore.
Require Minimal.EarnedMulti Minimal.UniversalCodes.
Require Import Minimal.SmHostBlocks Kernel.SmHostRice Kernel.SmKleene Kernel.SmFixedPoint.
Module M := Minimal.EarnedMulti.
Module UC := Minimal.UniversalCodes.

Local Notation hinstr := (@M.instr UC.hprop).
Local Notation hstate := (@M.state UC.hprop).
Local Notation hends := (sm_hends UC.hprop_eqb UC.heval).
Local Notation hequiv := (sm_hequiv UC.hprop_eqb UC.heval).
Local Notation hrun_prog := (M.run_prog UC.hprop_eqb UC.heval).
Local Notation hagree := (@sm_hagree UC.hprop).

(** * 1. Readings of the final state, equivalence of records, behaviour at a point *)

Section Readings.

Variable A : Type.
Variable P : BPre A.
Variable rd : hstate -> A.

Definition ax_req (x y : A) : Prop := bp_le P x y /\ bp_le P y x.

Lemma ax_req_sym : forall x y, ax_req x y -> ax_req y x.
Proof. intros x y [H1 H2]. split; assumption. Qed.

(** The Boolean threshold test of the point a on a final state. *)
Definition ax_reach (a : A) (s : hstate) : bool := bp_leb A P a (rd s).

Lemma ax_reach_req : forall a x y, ax_req x y -> bp_leb A P a x = bp_leb A P a y.
Proof.
  intros a x y [Hxy Hyx]. apply eq_true_iff_eq. split; intro H.
  - exact (bp_trans A P a x y H Hxy).
  - exact (bp_trans A P a y x H Hyx).
Qed.

(** Level 1: the reading is a function of what a program can read. *)
Definition ax_reads_hagree : Prop :=
  forall s t, hagree s t -> ax_req (rd s) (rd t).

(** Level 2: the reading is a function of what the recursion theorem with
    record preserves. *)
Definition ax_reads_obs : Prop :=
  forall s t, sm2_obs s t -> ax_req (rd s) (rd t).

(** Two programs behave alike at the point a. *)
Definition ax_reach_equiv (a : A) (p q : list hinstr) : Prop :=
  forall x,
    (forall s, hends p x s -> exists t, hends q x t /\ ax_reach a s = ax_reach a t) /\
    (forall t, hends q x t -> exists s, hends p x s /\ ax_reach a s = ax_reach a t).

(** Two programs behave alike on the whole record. *)
Definition ax_record_equiv (p q : list hinstr) : Prop :=
  forall x,
    (forall s, hends p x s -> exists t, hends q x t /\ ax_req (rd s) (rd t)) /\
    (forall t, hends q x t -> exists s, hends p x s /\ ax_req (rd s) (rd t)).

Lemma ax_reach_equiv_sym : forall a p q, ax_reach_equiv a p q -> ax_reach_equiv a q p.
Proof.
  intros a p q H x. destruct (H x) as [H1 H2]. split.
  - intros t Ht. destruct (H2 t Ht) as [s [Hs E]]. exists s. split; [exact Hs | symmetry; exact E].
  - intros s Hs. destruct (H1 s Hs) as [t [Ht E]]. exists t. split; [exact Ht | symmetry; exact E].
Qed.

Lemma ax_record_equiv_sym : forall p q, ax_record_equiv p q -> ax_record_equiv q p.
Proof.
  intros p q H x. destruct (H x) as [H1 H2]. split.
  - intros t Ht. destruct (H2 t Ht) as [s [Hs E]]. exists s. split; [exact Hs | apply ax_req_sym; exact E].
  - intros s Hs. destruct (H1 s Hs) as [t [Ht E]]. exists t. split; [exact Ht | apply ax_req_sym; exact E].
Qed.

(** Behaving alike on the record implies behaving alike at every point. *)
Lemma ax_record_equiv_reach : forall a p q, ax_record_equiv p q -> ax_reach_equiv a p q.
Proof.
  intros a p q H x. destruct (H x) as [H1 H2]. split.
  - intros s Hs. destruct (H1 s Hs) as [t [Ht E]]. exists t. split; [exact Ht |].
    unfold ax_reach. apply ax_reach_req. exact E.
  - intros t Ht. destruct (H2 t Ht) as [s [Hs E]]. exists s. split; [exact Hs |].
    unfold ax_reach. apply ax_reach_req. exact E.
Qed.

(** The host's own notion of behaving the same implies behaving alike on the
    record, for a level 1 reading. *)
Lemma ax_hequiv_record : ax_reads_hagree -> forall p q, hequiv p q -> ax_record_equiv p q.
Proof.
  intros Hr p q H x. destruct (H x) as [H1 H2]. split.
  - intros s Hs. destruct (H1 s Hs) as [t [Ht Ha]]. exists t. split; [exact Ht | apply Hr; exact Ha].
  - intros t Ht. destruct (H2 t Ht) as [s [Hs Ha]]. exists s. split; [exact Hs | apply Hr; exact Ha].
Qed.

(** For a level 2 reading, the equivalence of the recursion theorem with
    record implies behaving alike on the record. *)
Lemma ax_obs_equiv_record : ax_reads_obs -> forall p q, sm2_obs_equiv p q -> ax_record_equiv p q.
Proof.
  intros Hr p q H x. destruct (H x) as [H1 H2]. split.
  - intros s Hs. destruct (H1 s Hs) as [t [Ht Ha]]. exists t. split; [exact Ht | apply Hr; exact Ha].
  - intros t Ht. destruct (H2 t Ht) as [s [Hs Ha]]. exists s. split; [exact Hs | apply Hr; exact Ha].
Qed.

(** A level 2 reading is a level 1 reading. *)
Lemma ax_obs_hagree : ax_reads_obs -> ax_reads_hagree.
Proof.
  intros Ho s t Ha. apply Ho.
  destruct Ha as (Hv & Hf & Hc & He & Hm & Hk).
  unfold sm2_obs. repeat split.
  - apply Hv.
  - exact He.
  - exact Hm.
  - exact Hk.
  - rewrite Hf. reflexivity.
  - rewrite Hc. tauto.
  - rewrite Hc. tauto.
Qed.

(** * 2. Rice's theorem at every point and on the whole record *)

Theorem ax_rice_threshold : ax_reads_hagree -> forall a (Pi : list hinstr -> Prop) y n,
  (forall p q, ax_reach_equiv a p q -> Pi p -> Pi q) ->
  Pi y -> ~ Pi n -> undecidable Pi.
Proof.
  intros Hr a Pi y n Hext Hy Hn.
  apply (sm_host_rice UC.hprop_eqb UC.heval Pi y n); [| exact Hy | exact Hn].
  intros p q Hpq HP. apply (Hext p q); [| exact HP].
  apply ax_record_equiv_reach. apply ax_hequiv_record; assumption.
Qed.

Theorem ax_rice_record : ax_reads_hagree -> forall (Pi : list hinstr -> Prop) y n,
  (forall p q, ax_record_equiv p q -> Pi p -> Pi q) ->
  Pi y -> ~ Pi n -> undecidable Pi.
Proof.
  intros Hr Pi y n Hext Hy Hn.
  apply (sm_host_rice UC.hprop_eqb UC.heval Pi y n); [| exact Hy | exact Hn].
  intros p q Hpq HP. apply (Hext p q); [| exact HP].
  apply ax_hequiv_record; assumption.
Qed.

(** * 3. The diagonal at every point and on the whole record *)

Theorem ax_diagonal_record : ax_reads_obs -> forall (Pi : list hinstr -> Prop) yes no,
  (forall p q, ax_record_equiv p q -> Pi p -> Pi q) ->
  Pi yes -> ~ Pi no ->
  forall d : list hinstr -> bool,
  (exists T, sm_computes_map T (fun p => if d p then no else yes)) ->
  ~ (forall p, d p = true <-> Pi p).
Proof.
  intros Hr Pi yes no Hext Hy Hn d [T HT] Hd.
  destruct (sm2_kleene_obs _ T HT) as [e He].
  pose proof (ax_obs_equiv_record Hr He) as Hre.
  destruct (d e) eqn:Hde.
  - apply Hn. apply (Hext e no); [exact Hre | apply Hd, Hde].
  - assert (HPe : Pi e).
    { apply (Hext yes e); [| exact Hy]. apply ax_record_equiv_sym. exact Hre. }
    apply Hd in HPe. congruence.
Qed.

Theorem ax_diagonal_threshold : ax_reads_obs -> forall a (Pi : list hinstr -> Prop) yes no,
  (forall p q, ax_reach_equiv a p q -> Pi p -> Pi q) ->
  Pi yes -> ~ Pi no ->
  forall d : list hinstr -> bool,
  (exists T, sm_computes_map T (fun p => if d p then no else yes)) ->
  ~ (forall p, d p = true <-> Pi p).
Proof.
  intros Hr a Pi yes no Hext Hy Hn d [T HT] Hd.
  destruct (sm2_kleene_obs _ T HT) as [e He].
  pose proof (ax_record_equiv_reach a (ax_obs_equiv_record Hr He)) as Hre.
  destruct (d e) eqn:Hde.
  - apply Hn. apply (Hext e no); [exact Hre | apply Hd, Hde].
  - assert (HPe : Pi e).
    { apply (Hext yes e); [| exact Hy]. apply ax_reach_equiv_sym. exact Hre. }
    apply Hd in HPe. congruence.
Qed.

(** The property "reaches a on some input" respects behaving alike at a. *)
Definition ax_reaches (a : A) (p : list hinstr) : Prop :=
  exists x s, hends p x s /\ ax_reach a s = true.

Lemma ax_reaches_ext : forall a p q, ax_reach_equiv a p q -> ax_reaches a p -> ax_reaches a q.
Proof.
  intros a p q H [x [s [Hs Hr]]]. destruct (H x) as [H1 _].
  destruct (H1 s Hs) as [t [Ht E]]. exists x, t. split; [exact Ht | rewrite <- E; exact Hr].
Qed.

(** For a level 1 reading, a point reached by some program and not by the
    program that stops at once is a nontrivial point: the property of
    reaching it is undecidable. *)
Theorem ax_reach_undecidable : ax_reads_hagree -> forall a y,
  ax_reaches a y ->
  (forall x, ax_reach a (@sm_hstart UC.hprop x) = false) ->
  undecidable (ax_reaches a).
Proof.
  intros Hr a y Hy Hfloor.
  apply (ax_rice_threshold Hr (a := a) (Pi := ax_reaches a) (y := y) (n := [M.HALT])).
  - intros p q Hpq Hp. exact (ax_reaches_ext Hpq Hp).
  - exact Hy.
  - intros [x [s [Hs Hrs]]]. destruct Hs as [n [-> Hh]].
    assert (Hn : forall m, hrun_prog m [M.HALT] (@sm_hstart UC.hprop x) = @sm_hstart UC.hprop x).
    { induction m as [| m IH]; [reflexivity |]. simpl. rewrite <- IH at 2. reflexivity. }
    rewrite Hn in Hrs. rewrite Hfloor in Hrs. discriminate.
Qed.

End Readings.

Print Assumptions ax_rice_threshold.
Print Assumptions ax_rice_record.
Print Assumptions ax_diagonal_threshold.
Print Assumptions ax_diagonal_record.
Print Assumptions ax_reach_undecidable.

(** * 4. The host record: flag, number of facts, committed channel, trap *)

Definition ax_pair_pre {A B : Type} (P : BPre A) (Q : BPre B) : BPre (A * B).
Proof.
  refine {| bp_leb := fun x y => bp_leb A P (fst x) (fst y) && bp_leb B Q (snd x) (snd y) |}.
  - intro x. rewrite !bp_refl. reflexivity.
  - intros x y z H1 H2. apply andb_true_iff in H1 as [H1a H1b]. apply andb_true_iff in H2 as [H2a H2b].
    apply andb_true_iff. split; [exact (bp_trans A P _ _ _ H1a H2a) | exact (bp_trans B Q _ _ _ H1b H2b)].
Defined.

Lemma ax_pair_le : forall {A B : Type} (P : BPre A) (Q : BPre B) x y,
  bp_le (ax_pair_pre P Q) x y <-> bp_le P (fst x) (fst y) /\ bp_le Q (snd x) (snd y).
Proof.
  intros A B P Q x y. unfold bp_le. simpl. rewrite andb_true_iff. tauto.
Qed.

(** The order of the host record: flag, fact count, channel committed, trap. *)
Definition ax_host_pre : BPre (bool * (nat * (bool * bool))) :=
  ax_pair_pre two_pre (ax_pair_pre nat_pre (ax_pair_pre two_pre two_pre)).

Definition ax_chan_set (s : hstate) : bool :=
  match M.chan (M.core_of s) with Some _ => true | None => false end.

Definition ax_host_rec (s : hstate) : bool * (nat * (bool * bool)) :=
  (M.cert s, (length (M.facts (M.core_of s)), (ax_chan_set s, M.err (M.core_of s)))).

Definition ax_host_floor : bool * (nat * (bool * bool)) := (false, (0, (false, false))).

(** The reading is a function of what the recursion theorem with record
    preserves, so it is a level 2 reading, hence also level 1. *)
Lemma ax_host_rec_obs : ax_reads_obs ax_host_pre ax_host_rec.
Proof.
  intros s t Ho. unfold sm2_obs in Ho.
  destruct Ho as (_ & He & _ & Hk & Hl & Hc).
  assert (Hcs : ax_chan_set s = ax_chan_set t).
  { unfold ax_chan_set. destruct (M.chan (M.core_of s)) as [a |] eqn:E1;
      destruct (M.chan (M.core_of t)) as [b |] eqn:E2; try reflexivity.
    - exfalso. pose proof (proj2 Hc eq_refl) as H. discriminate.
    - exfalso. pose proof (proj1 Hc eq_refl) as H. discriminate. }
  assert (Heq : ax_host_rec s = ax_host_rec t).
  { unfold ax_host_rec. rewrite Hk, Hl, Hcs, He. reflexivity. }
  rewrite Heq. split; apply bp_le_refl.
Qed.

Lemma ax_host_rec_hagree : ax_reads_hagree ax_host_pre ax_host_rec.
Proof. apply ax_obs_hagree. exact ax_host_rec_obs. Qed.

(** Every start has the floor record. *)
Lemma ax_host_floor_start : forall x, ax_host_rec (@sm_hstart UC.hprop x) = ax_host_floor.
Proof. intro x. reflexivity. Qed.

(** The four kinds of point. *)
Definition ax_pt_flag : bool * (nat * (bool * bool)) := (true, (0, (false, false))).
Definition ax_pt_facts (k : nat) : bool * (nat * (bool * bool)) := (false, (k, (false, false))).
Definition ax_pt_chan : bool * (nat * (bool * bool)) := (false, (0, (true, false))).
Definition ax_pt_trap : bool * (nat * (bool * bool)) := (false, (0, (false, true))).

Lemma ax_pt_facts_leb : forall k c m b1 b2,
  bp_leb _ ax_host_pre (ax_pt_facts k) (c, (m, (b1, b2))) = Nat.leb k m.
Proof. intros k c m b1 b2. destruct c, b1, b2; cbn; rewrite ?andb_true_r; reflexivity. Qed.

(** * 5. What the host reaches: the cap of 16 facts, and every level below it *)

Lemma ax_facts_cap_run : forall n p (s : hstate),
  length (M.facts (M.core_of s)) <= M.fact_cap ->
  length (M.facts (M.core_of (hrun_prog n p s))) <= M.fact_cap.
Proof.
  induction n as [| n IH]; intros p s H; [exact H |].
  simpl. apply IH. unfold M.step. destruct (M.next_instr p (M.core_of s)) as [i |]; [| exact H].
  unfold M.exec. simpl. apply M.multi_facts_bounded_step. exact H.
Qed.

(** No run of any program holds more than 16 facts. *)
Theorem ax_facts_cap : forall p x n,
  length (M.facts (M.core_of (hrun_prog n p (@sm_hstart UC.hprop x)))) <= 16.
Proof.
  intros p x n. change 16 with M.fact_cap. apply ax_facts_cap_run. simpl. lia.
Qed.

(** So the point "17 facts" is reached by no program on any input. *)
Corollary ax_facts_17_unreached : forall k p x s,
  17 <= k -> hends p x s -> ax_reach ax_host_pre ax_host_rec (ax_pt_facts k) s = false.
Proof.
  intros k p x s Hk [n [-> _]].
  pose proof (ax_facts_cap p x n) as H.
  unfold ax_reach, ax_host_rec. rewrite ax_pt_facts_leb.
  apply Nat.leb_gt. lia.
Qed.

(** Programs that reach each point. *)
Definition ax_chk : hinstr := M.CHECK UC.PSlot 5.

Definition ax_prog_facts (k : nat) : list hinstr :=
  M.INC 5 :: (repeat ax_chk k ++ [M.HALT]).

Definition ax_prog_flag : list hinstr :=
  [M.INC 5; M.CHECK UC.PSlot 5; M.COMMIT UC.PSlot 5; M.CERTIFY; M.HALT].

Definition ax_prog_chan : list hinstr :=
  [M.INC 5; M.CHECK UC.PSlot 5; M.COMMIT UC.PSlot 5; M.HALT].

Definition ax_prog_trap : list hinstr := [M.CHECK UC.PSlot 5; M.HALT].

Lemma ax_nth_repeat : forall (x : hinstr) k j, j < k -> nth_error (repeat x k) j = Some x.
Proof.
  intros x k. induction k as [| k IH]; intros j Hj; [lia |].
  destruct j as [| j]; [reflexivity |]. simpl. apply IH. lia.
Qed.

Lemma ax_fetch_chk : forall k j, j < k -> M.fetch (ax_prog_facts k) (S (S j)) = Some ax_chk.
Proof.
  intros k j Hj. unfold ax_prog_facts, M.fetch. simpl.
  rewrite nth_error_app1 by (rewrite repeat_length; exact Hj).
  apply ax_nth_repeat. exact Hj.
Qed.

Lemma ax_fetch_halt : forall k, M.fetch (ax_prog_facts k) (S (S k)) = Some M.HALT.
Proof.
  intro k. unfold ax_prog_facts, M.fetch. simpl.
  rewrite nth_error_app2 by (rewrite repeat_length; lia).
  rewrite repeat_length, Nat.sub_diag. reflexivity.
Qed.

(** The state after j checks. *)
Definition ax_inv (j : nat) (s : hstate) : Prop :=
  M.err (M.core_of s) = false /\ M.pc (M.core_of s) = S (S j) /\
  M.vals (M.core_of s) 5 = 1 /\ M.vers (M.core_of s) 5 = 1 /\
  length (M.facts (M.core_of s)) = j /\ M.chan (M.core_of s) = None /\ M.cert s = false.

Lemma ax_inv_zero : forall k, ax_inv 0 (hrun_prog 1 (ax_prog_facts k) (@sm_hstart UC.hprop 0)).
Proof.
  intro k. unfold ax_inv. repeat split; reflexivity.
Qed.

Lemma ax_inv_step : forall k j s,
  j < k -> k <= 16 -> ax_inv j s ->
  ax_inv (S j) (M.step UC.hprop_eqb UC.heval (ax_prog_facts k) s).
Proof.
  intros k j s Hjk Hk (He & Hpc & Hv & Hver & Hlen & Hch & Hc).
  assert (Hnext : M.next_instr (ax_prog_facts k) (M.core_of s) = Some ax_chk).
  { unfold M.next_instr. rewrite He, Hpc, (ax_fetch_chk Hjk). reflexivity. }
  assert (Hok : M.check_ok UC.heval (M.core_of s) UC.PSlot 5 = true).
  { unfold M.check_ok. rewrite He, Hv, Hlen. simpl.
    replace (UC.heval UC.PSlot 1) with true by reflexivity. simpl.
    apply Nat.ltb_lt. unfold M.fact_cap. lia. }
  unfold M.step. rewrite Hnext. unfold ax_chk.
  rewrite (M.multi_exec_check_pass UC.hprop_eqb UC.heval s UC.PSlot 5 Hok).
  unfold ax_inv. simpl. repeat split; try assumption.
  - rewrite Hpc. reflexivity.
  - rewrite Hlen. reflexivity.
Qed.

Lemma ax_inv_run : forall k j, j <= k -> k <= 16 ->
  ax_inv j (hrun_prog (S j) (ax_prog_facts k) (@sm_hstart UC.hprop 0)).
Proof.
  intros k j. induction j as [| j IH]; intros Hjk Hk.
  - apply ax_inv_zero.
  - rewrite M.multi_run_prog_succ. apply ax_inv_step; [lia | exact Hk | apply IH; lia].
Qed.

Theorem ax_facts_reach : forall k, k <= 16 ->
  exists s, hends (ax_prog_facts k) 0 s /\ ax_host_rec s = (false, (k, (false, false))).
Proof.
  intros k Hk.
  exists (hrun_prog (S k) (ax_prog_facts k) (@sm_hstart UC.hprop 0)).
  pose proof (ax_inv_run (le_n k) Hk) as (He & Hpc & _ & _ & Hlen & Hch & Hc).
  split.
  - exists (S k). split; [reflexivity |].
    unfold M.halted, M.next_instr. rewrite He, Hpc, ax_fetch_halt. reflexivity.
  - unfold ax_host_rec, ax_chan_set. rewrite Hlen, Hch, He, Hc. reflexivity.
Qed.

(** The record points of the host axis, and the programs that reach them. *)
Lemma ax_prog_flag_ends : exists s, hends ax_prog_flag 0 s /\
  ax_host_rec s = (true, (1, (true, false))).
Proof.
  exists (hrun_prog 4 ax_prog_flag (@sm_hstart UC.hprop 0)). split.
  - exists 4. split; [reflexivity |]. vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

Lemma ax_prog_chan_ends : exists s, hends ax_prog_chan 0 s /\
  ax_host_rec s = (false, (1, (true, false))).
Proof.
  exists (hrun_prog 3 ax_prog_chan (@sm_hstart UC.hprop 0)). split.
  - exists 3. split; [reflexivity |]. vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

Lemma ax_prog_trap_ends : exists s, hends ax_prog_trap 0 s /\
  ax_host_rec s = (false, (0, (false, true))).
Proof.
  exists (hrun_prog 1 ax_prog_trap (@sm_hstart UC.hprop 0)). split.
  - exists 1. split; [reflexivity |]. vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

(** * 6. Rice and the diagonal on the host axis *)

Definition ax_host_reaches (a : bool * (nat * (bool * bool))) : list hinstr -> Prop :=
  ax_reaches ax_host_pre ax_host_rec a.

(** Every reachable point not below the floor: the property of reaching it is
    undecidable, and no decider whose flip a host program computes is correct. *)
Theorem ax_host_point_undecidable : forall a y,
  ax_host_reaches a y ->
  bp_leb _ ax_host_pre a ax_host_floor = false ->
  undecidable (ax_host_reaches a).
Proof.
  intros a y Hy Hf.
  apply (ax_reach_undecidable ax_host_rec_hagree Hy).
  intro x. unfold ax_reach. rewrite ax_host_floor_start. exact Hf.
Qed.

Theorem ax_host_point_diagonal : forall a y,
  ax_host_reaches a y ->
  bp_leb _ ax_host_pre a ax_host_floor = false ->
  forall d : list hinstr -> bool,
    (exists T, sm_computes_map T (fun p => if d p then [M.HALT] else y)) ->
    ~ (forall p, d p = true <-> ax_host_reaches a p).
Proof.
  intros a y Hy Hf d HT.
  apply (ax_diagonal_threshold ax_host_rec_obs (a := a) (Pi := ax_host_reaches a) (yes := y) (no := [M.HALT])).
  - intros p q Hpq Hp. exact (ax_reaches_ext Hpq Hp).
  - exact Hy.
  - intros [x [s [Hs Hr]]]. destruct Hs as [n [-> Hh]].
    assert (Hn : forall m, hrun_prog m [M.HALT] (@sm_hstart UC.hprop x) = @sm_hstart UC.hprop x).
    { induction m as [| m IH]; [reflexivity |]. simpl. rewrite <- IH at 2. reflexivity. }
    rewrite Hn in Hr. unfold ax_reach in Hr. rewrite ax_host_floor_start in Hr.
    rewrite Hf in Hr. discriminate.
  - exact HT.
Qed.

(** The four kinds of point are reached and are not the floor. *)
Corollary ax_flag_undecidable : undecidable (ax_host_reaches ax_pt_flag).
Proof.
  apply (ax_host_point_undecidable (a := ax_pt_flag) (y := ax_prog_flag)).
  - destruct ax_prog_flag_ends as [s [Hs Hr]]. exists 0, s. split; [exact Hs |].
    unfold ax_reach. rewrite Hr. vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

Corollary ax_chan_undecidable : undecidable (ax_host_reaches ax_pt_chan).
Proof.
  apply (ax_host_point_undecidable (a := ax_pt_chan) (y := ax_prog_chan)).
  - destruct ax_prog_chan_ends as [s [Hs Hr]]. exists 0, s. split; [exact Hs |].
    unfold ax_reach. rewrite Hr. vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

Corollary ax_trap_undecidable : undecidable (ax_host_reaches ax_pt_trap).
Proof.
  apply (ax_host_point_undecidable (a := ax_pt_trap) (y := ax_prog_trap)).
  - destruct ax_prog_trap_ends as [s [Hs Hr]]. exists 0, s. split; [exact Hs |].
    unfold ax_reach. rewrite Hr. vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

Corollary ax_facts_undecidable : forall k, 1 <= k -> k <= 16 ->
  undecidable (ax_host_reaches (ax_pt_facts k)).
Proof.
  intros k H1 H16.
  apply (ax_host_point_undecidable (a := ax_pt_facts k) (y := ax_prog_facts k)).
  - destruct (ax_facts_reach H16) as [s [Hs Hr]]. exists 0, s. split; [exact Hs |].
    unfold ax_reach. rewrite Hr. rewrite ax_pt_facts_leb. apply Nat.leb_refl.
  - unfold ax_host_floor. rewrite ax_pt_facts_leb. apply Nat.leb_gt. lia.
Qed.

Corollary ax_flag_diagonal : forall d : list hinstr -> bool,
  (exists T, sm_computes_map T (fun p => if d p then [M.HALT] else ax_prog_flag)) ->
  ~ (forall p, d p = true <-> ax_host_reaches ax_pt_flag p).
Proof.
  apply (ax_host_point_diagonal (a := ax_pt_flag) (y := ax_prog_flag)).
  - destruct ax_prog_flag_ends as [s [Hs Hr]]. exists 0, s. split; [exact Hs |].
    unfold ax_reach. rewrite Hr. vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

(** The point "17 facts" is not reached, so reaching it is the trivial
    property: the fact count has 17 levels. *)
Corollary ax_facts_17_trivial : forall p, ~ ax_host_reaches (ax_pt_facts 17) p.
Proof.
  intros p [x [s [Hs Hr]]].
  rewrite (ax_facts_17_unreached (le_n 17) Hs) in Hr. discriminate.
Qed.

Print Assumptions ax_facts_cap.
Print Assumptions ax_facts_17_unreached.
Print Assumptions ax_facts_reach.
Print Assumptions ax_host_point_undecidable.
Print Assumptions ax_host_point_diagonal.
Print Assumptions ax_flag_undecidable.
Print Assumptions ax_chan_undecidable.
Print Assumptions ax_trap_undecidable.
Print Assumptions ax_facts_undecidable.
Print Assumptions ax_flag_diagonal.
Print Assumptions ax_facts_17_trivial.
Print Assumptions ax_host_rec_obs.
