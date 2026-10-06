(** RealizeCompact.v: running U and U_P for hundreds of millions of steps.

    In EarnedMulti.v and EarnedMultiPriced.v the registers are functions,
    vals : nat -> nat and vers : nat -> nat, and a write builds the function
    "agrees with the old one except at r". Run as extracted code, every write
    adds one more layer to a chain of closures. After n steps a lookup of a
    register that was not written lately walks up to n layers, and the layers
    are never freed. A run of U on a guest whose program code is 2^24 takes
    about 4 * 10^8 steps and does not fit in memory that way.

    This file adds the one repair that leaves the machine alone. The state
    reached after any number of steps can be replaced by a state with the same
    program counter, facts, channel, trap latch, ledger and flag, in which the
    registers below a bound N are held in a table and every other register
    reads as a given function g (its value) and 0 (its version). Replacing a
    state this way changes nothing a later step can see, provided

      * the program names only registers below N (prog_below), and
      * the registers N and above hold g and have version 0, which is true of
        every loaded start state, because only a write moves a register, and
        a write names a register of the program.

    rlz_sched_sound states this for every schedule of steps and replacements:
    the run with replacements equals, register by register and field by field,
    the run without them, after the same number of steps. So the extracted
    driver may compact as often as it likes without changing any result. The
    last section instantiates it for U and U_P, which name registers up to 80;
    N is 96.

    Two states are equal "up to storage" when their registers and versions
    agree at every register and every other field is equal. That relation is
    all the extracted code is compared on: the state views of
    RealizeExtract.v read only registers, versions, facts, channel, latch,
    ledger and flag.

    Dependencies: Realize.v, RealizePriced.v, the machines they name. No
    axioms, no Admitted.                                                   *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   adds a storage change to the machines of EarnedMulti.v and
   EarnedMultiPriced.v and proves it invisible; the claims about those
   machines are in the files named above. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.RealizeNames.
Require Kernel.Realize Kernel.RealizePriced.

(* ================================================================= *)
(* The host (EarnedMulti.v).                                        *)
(* ================================================================= *)

Section Compact.
Context {prop : Type}.
Variable prop_eqb : prop -> prop -> bool.
Variable eval : prop -> nat -> bool.

(* Every register an instruction names is below N. *)
Definition rlz_instr_ok (N : nat) (i : (@Minimal.EarnedMulti.instr prop)) : bool :=
  match i with
  | Minimal.EarnedMulti.INC r => Nat.ltb r N
  | Minimal.EarnedMulti.DEC r _ => Nat.ltb r N
  | Minimal.EarnedMulti.CHECK _ r => Nat.ltb r N
  | Minimal.EarnedMulti.COMMIT _ r => Nat.ltb r N
  | _ => true
  end.

Definition rlz_prog_below (N : nat) (P : list (@Minimal.EarnedMulti.instr prop)) : bool :=
  forallb (rlz_instr_ok N) P.

Definition rlz_tab (N : nat) (f : nat -> nat) : list nat := map f (seq 0 N).

(* The same machine state with the registers below N held in a table.
   Registers N and above read as g (their values) and 0 (their versions). *)
Definition rlz_compact_core (N : nat) (g : nat -> nat) (k : (@Minimal.EarnedMulti.core prop)) : (@Minimal.EarnedMulti.core prop) :=
  let tv := rlz_tab N (Minimal.EarnedMulti.vals k) in
  let tr := rlz_tab N (Minimal.EarnedMulti.vers k) in
  Minimal.EarnedMulti.mkcore (fun r => if Nat.ltb r N then nth r tv 0 else g r)
             (fun r => if Nat.ltb r N then nth r tr 0 else 0)
             (Minimal.EarnedMulti.pc k) (Minimal.EarnedMulti.facts k) (Minimal.EarnedMulti.chan k) (Minimal.EarnedMulti.err k).

Definition rlz_compact (N : nat) (g : nat -> nat) (s : (@Minimal.EarnedMulti.state prop)) : (@Minimal.EarnedMulti.state prop) :=
  Minimal.EarnedMulti.mkst (rlz_compact_core N g (Minimal.EarnedMulti.core_of s)) (Minimal.EarnedMulti.mu s) (Minimal.EarnedMulti.cert s).

(* Two states that differ only in how the registers are stored. *)
Definition rlz_core_eqv (k l : (@Minimal.EarnedMulti.core prop)) : Prop :=
  (forall r, Minimal.EarnedMulti.vals k r = Minimal.EarnedMulti.vals l r) /\ (forall r, Minimal.EarnedMulti.vers k r = Minimal.EarnedMulti.vers l r) /\
  Minimal.EarnedMulti.pc k = Minimal.EarnedMulti.pc l /\ Minimal.EarnedMulti.facts k = Minimal.EarnedMulti.facts l /\ Minimal.EarnedMulti.chan k = Minimal.EarnedMulti.chan l /\
  Minimal.EarnedMulti.err k = Minimal.EarnedMulti.err l.

Definition rlz_eqv (s t : (@Minimal.EarnedMulti.state prop)) : Prop :=
  rlz_core_eqv (Minimal.EarnedMulti.core_of s) (Minimal.EarnedMulti.core_of t) /\ Minimal.EarnedMulti.mu s = Minimal.EarnedMulti.mu t /\ Minimal.EarnedMulti.cert s = Minimal.EarnedMulti.cert t.

Lemma rlz_core_eqv_refl : forall k, rlz_core_eqv k k.
Proof. intro k. repeat split; auto. Qed.

Lemma rlz_core_eqv_trans : forall k l m, rlz_core_eqv k l -> rlz_core_eqv l m -> rlz_core_eqv k m.
Proof.
  intros k l m (Hv & Hr & Hp & Hf & Hc & He) (Hv' & Hr' & Hp' & Hf' & Hc' & He').
  repeat split; [intro r; rewrite Hv; apply Hv' | intro r; rewrite Hr; apply Hr' | congruence | congruence | congruence | congruence].
Qed.

Lemma rlz_eqv_refl : forall s, rlz_eqv s s.
Proof. intro s. refine (conj _ (conj _ _)); [apply rlz_core_eqv_refl | reflexivity | reflexivity]. Qed.

Lemma rlz_eqv_trans : forall s t u, rlz_eqv s t -> rlz_eqv t u -> rlz_eqv s u.
Proof.
  intros s t u (H1 & H2 & H3) (H1' & H2' & H3').
  refine (conj _ (conj _ _)); [eapply rlz_core_eqv_trans; eauto | congruence | congruence].
Qed.

(* ---- a step does not tell the two storages apart ---- *)

Lemma rlz_claim_eqv : forall k l p r, rlz_core_eqv k l -> Minimal.EarnedMulti.claim k p r = Minimal.EarnedMulti.claim l p r.
Proof. intros k l p r (Hv & Hr & _). unfold Minimal.EarnedMulti.claim. rewrite Hr. reflexivity. Qed.

Lemma rlz_check_ok_eqv : forall k l p r, rlz_core_eqv k l ->
  Minimal.EarnedMulti.check_ok eval k p r = Minimal.EarnedMulti.check_ok eval l p r.
Proof.
  intros k l p r (Hv & Hr & Hp & Hf & Hc & He). unfold Minimal.EarnedMulti.check_ok.
  rewrite Hv, Hf, He. reflexivity.
Qed.

Lemma rlz_commit_ok_eqv : forall k l p r, rlz_core_eqv k l ->
  Minimal.EarnedMulti.commit_ok prop_eqb k p r = Minimal.EarnedMulti.commit_ok prop_eqb l p r.
Proof.
  intros k l p r H. pose proof H as (Hv & Hr & Hp & Hf & Hc & He). unfold Minimal.EarnedMulti.commit_ok.
  rewrite He, Hf, (rlz_claim_eqv k l p r H). reflexivity.
Qed.

Lemma rlz_certify_ok_eqv : forall k l, rlz_core_eqv k l ->
  Minimal.EarnedMulti.certify_ok k = Minimal.EarnedMulti.certify_ok l.
Proof.
  intros k l (Hv & Hr & Hp & Hf & Hc & He). unfold Minimal.EarnedMulti.certify_ok.
  rewrite He, Hc. reflexivity.
Qed.

Lemma rlz_write_eqv : forall k l r n j, rlz_core_eqv k l ->
  rlz_core_eqv (Minimal.EarnedMulti.write k r n j) (Minimal.EarnedMulti.write l r n j).
Proof.
  intros k l r n j (Hv & Hr & Hp & Hf & Hc & He). unfold Minimal.EarnedMulti.write, rlz_core_eqv; simpl.
  repeat split; try assumption.
  - intro x. unfold Minimal.EarnedMulti.upd. destruct (Nat.eqb x r); [reflexivity | apply Hv].
  - intro x. unfold Minimal.EarnedMulti.upd. destruct (Nat.eqb x r); [rewrite Hr; reflexivity | apply Hr].
Qed.

Lemma rlz_goto_eqv : forall k l j, rlz_core_eqv k l ->
  rlz_core_eqv (Minimal.EarnedMulti.goto k j) (Minimal.EarnedMulti.goto l j).
Proof.
  intros k l j (Hv & Hr & Hp & Hf & Hc & He). unfold Minimal.EarnedMulti.goto, rlz_core_eqv; simpl.
  repeat split; try assumption.
Qed.

Lemma rlz_trap_eqv : forall k l, rlz_core_eqv k l ->
  rlz_core_eqv (Minimal.EarnedMulti.trap k) (Minimal.EarnedMulti.trap l).
Proof.
  intros k l (Hv & Hr & Hp & Hf & Hc & He). unfold Minimal.EarnedMulti.trap, rlz_core_eqv; simpl.
  repeat split; try assumption.
Qed.

Lemma rlz_record_fact_eqv : forall k l f, rlz_core_eqv k l ->
  rlz_core_eqv (Minimal.EarnedMulti.record_fact k f) (Minimal.EarnedMulti.record_fact l f).
Proof.
  intros k l f (Hv & Hr & Hp & Hf & Hc & He). unfold Minimal.EarnedMulti.record_fact, rlz_core_eqv; simpl.
  repeat split; try assumption; congruence.
Qed.

Lemma rlz_commit_to_eqv : forall k l f, rlz_core_eqv k l ->
  rlz_core_eqv (Minimal.EarnedMulti.commit_to k f) (Minimal.EarnedMulti.commit_to l f).
Proof.
  intros k l f (Hv & Hr & Hp & Hf & Hc & He). unfold Minimal.EarnedMulti.commit_to, rlz_core_eqv; simpl.
  repeat split; try assumption; congruence.
Qed.

Lemma rlz_cexec_eqv : forall k l (i : (@Minimal.EarnedMulti.instr prop)), rlz_core_eqv k l ->
  rlz_core_eqv (Minimal.EarnedMulti.cexec prop_eqb eval k i) (Minimal.EarnedMulti.cexec prop_eqb eval l i).
Proof.
  intros k l i H. pose proof H as (Hv & Hr & Hp & Hf & Hc & He).
  unfold Minimal.EarnedMulti.cexec. rewrite <- He.
  destruct (Minimal.EarnedMulti.err k) eqn:E; [exact H |].
  destruct i as [r | r j | | p r | p r | ].
  - rewrite <- (Hv r), <- Hp. apply rlz_write_eqv. exact H.
  - rewrite <- (Hv r), <- Hp. destruct (Minimal.EarnedMulti.vals k r) as [| n].
    + apply rlz_goto_eqv. exact H.
    + apply rlz_write_eqv. exact H.
  - exact H.
  - rewrite <- (rlz_check_ok_eqv k l p r H), <- (rlz_claim_eqv k l p r H).
    destruct (Minimal.EarnedMulti.check_ok eval k p r).
    + apply rlz_record_fact_eqv. exact H.
    + apply rlz_trap_eqv. exact H.
  - rewrite <- (rlz_commit_ok_eqv k l p r H), <- (rlz_claim_eqv k l p r H).
    destruct (Minimal.EarnedMulti.commit_ok prop_eqb k p r).
    + apply rlz_commit_to_eqv. exact H.
    + apply rlz_trap_eqv. exact H.
  - rewrite <- (rlz_certify_ok_eqv k l H), <- Hp.
    destruct (Minimal.EarnedMulti.certify_ok k).
    + apply rlz_goto_eqv. exact H.
    + apply rlz_trap_eqv. exact H.
Qed.

Lemma rlz_fires_eqv : forall k l (i : (@Minimal.EarnedMulti.instr prop)), rlz_core_eqv k l -> Minimal.EarnedMulti.fires k i = Minimal.EarnedMulti.fires l i.
Proof.
  intros k l i H. unfold Minimal.EarnedMulti.fires. destruct i; try reflexivity.
  apply rlz_certify_ok_eqv. exact H.
Qed.

Lemma rlz_exec_eqv : forall s t (i : (@Minimal.EarnedMulti.instr prop)), rlz_eqv s t ->
  rlz_eqv (Minimal.EarnedMulti.exec prop_eqb eval s i) (Minimal.EarnedMulti.exec prop_eqb eval t i).
Proof.
  intros s t i (Hk & Hm & Hc). unfold Minimal.EarnedMulti.exec, rlz_eqv; simpl.
  refine (conj _ (conj _ _)).
  - apply rlz_cexec_eqv. exact Hk.
  - rewrite Hm. reflexivity.
  - rewrite Hc, (rlz_fires_eqv _ _ i Hk). reflexivity.
Qed.

Lemma rlz_next_instr_eqv : forall (P : list (@Minimal.EarnedMulti.instr prop)) k l, rlz_core_eqv k l ->
  Minimal.EarnedMulti.next_instr P k = Minimal.EarnedMulti.next_instr P l.
Proof.
  intros P k l (Hv & Hr & Hp & Hf & Hc & He). unfold Minimal.EarnedMulti.next_instr. rewrite He, Hp. reflexivity.
Qed.

Lemma rlz_step_eqv : forall (P : list (@Minimal.EarnedMulti.instr prop)) s t, rlz_eqv s t ->
  rlz_eqv (Minimal.EarnedMulti.step prop_eqb eval P s) (Minimal.EarnedMulti.step prop_eqb eval P t).
Proof.
  intros P s t H. pose proof H as (Hk & _). unfold Minimal.EarnedMulti.step.
  rewrite <- (rlz_next_instr_eqv P _ _ Hk).
  destruct (Minimal.EarnedMulti.next_instr P (Minimal.EarnedMulti.core_of s)) as [i |];
    [apply rlz_exec_eqv; exact H | exact H].
Qed.

Lemma rlz_run_prog_eqv : forall n (P : list (@Minimal.EarnedMulti.instr prop)) s t, rlz_eqv s t ->
  rlz_eqv (Minimal.EarnedMulti.run_prog prop_eqb eval n P s) (Minimal.EarnedMulti.run_prog prop_eqb eval n P t).
Proof.
  induction n as [| n IH]; intros P s t H; simpl; [exact H |].
  apply IH. apply rlz_step_eqv. exact H.
Qed.

(* ---- the registers at and above N are never touched ---- *)

Definition rlz_cinv (N : nat) (g : nat -> nat) (k : (@Minimal.EarnedMulti.core prop)) : Prop :=
  forall r, N <= r -> Minimal.EarnedMulti.vals k r = g r /\ Minimal.EarnedMulti.vers k r = 0.

Definition rlz_inv (N : nat) (g : nat -> nat) (s : (@Minimal.EarnedMulti.state prop)) : Prop :=
  rlz_cinv N g (Minimal.EarnedMulti.core_of s).

Lemma rlz_next_in : forall (P : list (@Minimal.EarnedMulti.instr prop)) (k : (@Minimal.EarnedMulti.core prop)) i, Minimal.EarnedMulti.next_instr P k = Some i -> In i P.
Proof.
  intros P k i H. unfold Minimal.EarnedMulti.next_instr in H.
  destruct (Minimal.EarnedMulti.err k); [discriminate |].
  unfold Minimal.EarnedMulti.fetch in H. destruct (Minimal.EarnedMulti.pc k) as [| m]; [discriminate |].
  destruct (nth_error P m) as [j |] eqn:E; [| discriminate].
  apply nth_error_In in E.
  destruct j; first [discriminate | (injection H as <-; exact E)].
Qed.

Lemma rlz_cexec_inv : forall N g k (i : (@Minimal.EarnedMulti.instr prop)), rlz_instr_ok N i = true -> rlz_cinv N g k ->
  rlz_cinv N g (Minimal.EarnedMulti.cexec prop_eqb eval k i).
Proof.
  intros N g k i Hi Hk. unfold Minimal.EarnedMulti.cexec. destruct (Minimal.EarnedMulti.err k); [exact Hk |].
  destruct i as [r | r j | | p r | p r | ]; simpl in Hi.
  - apply Nat.ltb_lt in Hi. unfold Minimal.EarnedMulti.write, rlz_cinv; simpl. intros x Hx.
    unfold Minimal.EarnedMulti.upd. assert (Hne : Nat.eqb x r = false) by (apply Nat.eqb_neq; lia).
    rewrite Hne. apply Hk. exact Hx.
  - apply Nat.ltb_lt in Hi. destruct (Minimal.EarnedMulti.vals k r) as [| n].
    + exact Hk.
    + unfold Minimal.EarnedMulti.write, rlz_cinv; simpl. intros x Hx.
      unfold Minimal.EarnedMulti.upd. assert (Hne : Nat.eqb x r = false) by (apply Nat.eqb_neq; lia).
      rewrite Hne. apply Hk. exact Hx.
  - exact Hk.
  - destruct (Minimal.EarnedMulti.check_ok eval k p r); exact Hk.
  - destruct (Minimal.EarnedMulti.commit_ok prop_eqb k p r); exact Hk.
  - destruct (Minimal.EarnedMulti.certify_ok k); exact Hk.
Qed.

Lemma rlz_step_inv : forall N g (P : list (@Minimal.EarnedMulti.instr prop)) s, rlz_prog_below N P = true -> rlz_inv N g s ->
  rlz_inv N g (Minimal.EarnedMulti.step prop_eqb eval P s).
Proof.
  intros N g P s HP Hs. unfold Minimal.EarnedMulti.step.
  destruct (Minimal.EarnedMulti.next_instr P (Minimal.EarnedMulti.core_of s)) as [i |] eqn:E; [| exact Hs].
  apply rlz_next_in in E. unfold rlz_prog_below in HP. rewrite forallb_forall in HP.
  unfold Minimal.EarnedMulti.exec, rlz_inv. simpl. apply rlz_cexec_inv; [apply HP; exact E | exact Hs].
Qed.

Lemma rlz_nth_tab : forall N f r, r < N -> nth r (rlz_tab N f) 0 = f r.
Proof.
  intros N f r H. unfold rlz_tab.
  rewrite (nth_indep _ 0 (f 0)) by (rewrite map_length, seq_length; exact H).
  rewrite map_nth, seq_nth by exact H. reflexivity.
Qed.

Lemma rlz_compact_eqv : forall N g s, rlz_inv N g s -> rlz_eqv (rlz_compact N g s) s.
Proof.
  intros N g s Hs. unfold rlz_eqv, rlz_core_eqv, rlz_compact, rlz_compact_core; simpl.
  repeat split; try reflexivity.
  - intro r. destruct (Nat.ltb r N) eqn:E.
    + apply Nat.ltb_lt in E. apply rlz_nth_tab. exact E.
    + apply Nat.ltb_ge in E. symmetry. apply (proj1 (Hs r E)).
  - intro r. destruct (Nat.ltb r N) eqn:E.
    + apply Nat.ltb_lt in E. apply rlz_nth_tab. exact E.
    + apply Nat.ltb_ge in E. symmetry. apply (proj2 (Hs r E)).
Qed.

Lemma rlz_compact_inv : forall N g s, rlz_inv N g (rlz_compact N g s).
Proof.
  intros N g s. unfold rlz_inv, rlz_cinv, rlz_compact, rlz_compact_core; simpl.
  intros r Hr. apply Nat.ltb_ge in Hr. rewrite Hr. split; reflexivity.
Qed.

(* A run that steps and, after the steps the schedule marks, compacts. *)
Fixpoint rlz_sched (N : nat) (g : nat -> nat) (P : list (@Minimal.EarnedMulti.instr prop)) (sched : list bool)
  (s : (@Minimal.EarnedMulti.state prop)) : (@Minimal.EarnedMulti.state prop) :=
  match sched with
  | [] => s
  | b :: t =>
      rlz_sched N g P t
        (if b then rlz_compact N g (Minimal.EarnedMulti.step prop_eqb eval P s) else Minimal.EarnedMulti.step prop_eqb eval P s)
  end.

(* Whatever the schedule, the run with compaction is the run without it, up
   to the storage of the registers: same program counter, facts, channel,
   trap latch, ledger and flag, and every register and version equal. *)
Theorem rlz_sched_sound : forall N g (P : list (@Minimal.EarnedMulti.instr prop)) sched s,
  rlz_prog_below N P = true -> rlz_inv N g s ->
  rlz_eqv (rlz_sched N g P sched s) (Minimal.EarnedMulti.run_prog prop_eqb eval (length sched) P s).
Proof.
  intros N g P sched. induction sched as [| b t IH]; intros s HP Hs; simpl.
  - apply rlz_eqv_refl.
  - assert (Hs' : rlz_inv N g (Minimal.EarnedMulti.step prop_eqb eval P s)) by (apply rlz_step_inv; assumption).
    assert (Hu : rlz_inv N g (if b then rlz_compact N g (Minimal.EarnedMulti.step prop_eqb eval P s) else Minimal.EarnedMulti.step prop_eqb eval P s)).
    { destruct b; [apply rlz_compact_inv | exact Hs']. }
    assert (Heq : rlz_eqv (if b then rlz_compact N g (Minimal.EarnedMulti.step prop_eqb eval P s) else Minimal.EarnedMulti.step prop_eqb eval P s)
                             (Minimal.EarnedMulti.step prop_eqb eval P s)).
    { destruct b; [apply rlz_compact_eqv; exact Hs' | apply rlz_eqv_refl]. }
    eapply rlz_eqv_trans; [apply IH; assumption |].
    apply rlz_run_prog_eqv. exact Heq.
Qed.

End Compact.

(* ================================================================= *)
(* The priced host (EarnedMultiPriced.v).                           *)
(* ================================================================= *)

Section Compactp.
Context {prop : Type}.
Variable prop_eqb : prop -> prop -> bool.
Variable eval : prop -> nat -> bool.

(* Every register an instruction names is below N. *)
Definition rlzp_instr_ok (N : nat) (i : (@Minimal.EarnedMultiPriced.pu_instr prop)) : bool :=
  match i with
  | Minimal.EarnedMultiPriced.INC r => Nat.ltb r N
  | Minimal.EarnedMultiPriced.DEC r _ => Nat.ltb r N
  | Minimal.EarnedMultiPriced.CHECK _ r => Nat.ltb r N
  | Minimal.EarnedMultiPriced.COMMIT _ r => Nat.ltb r N
  | _ => true
  end.

Definition rlzp_prog_below (N : nat) (P : list (@Minimal.EarnedMultiPriced.pu_instr prop)) : bool :=
  forallb (rlzp_instr_ok N) P.

Definition rlzp_tab (N : nat) (f : nat -> nat) : list nat := map f (seq 0 N).

(* The same machine state with the registers below N held in a table.
   Registers N and above read as g (their values) and 0 (their versions). *)
Definition rlzp_compact_core (N : nat) (g : nat -> nat) (k : (@Minimal.EarnedMultiPriced.pu_core prop)) : (@Minimal.EarnedMultiPriced.pu_core prop) :=
  let tv := rlzp_tab N (Minimal.EarnedMultiPriced.vals k) in
  let tr := rlzp_tab N (Minimal.EarnedMultiPriced.vers k) in
  Minimal.EarnedMultiPriced.mkcore (fun r => if Nat.ltb r N then nth r tv 0 else g r)
             (fun r => if Nat.ltb r N then nth r tr 0 else 0)
             (Minimal.EarnedMultiPriced.pc k) (Minimal.EarnedMultiPriced.facts k) (Minimal.EarnedMultiPriced.chan k) (Minimal.EarnedMultiPriced.err k).

Definition rlzp_compact (N : nat) (g : nat -> nat) (s : (@Minimal.EarnedMultiPriced.pu_state prop)) : (@Minimal.EarnedMultiPriced.pu_state prop) :=
  Minimal.EarnedMultiPriced.mkst (rlzp_compact_core N g (Minimal.EarnedMultiPriced.core_of s)) (Minimal.EarnedMultiPriced.mu s) (Minimal.EarnedMultiPriced.cert s).

(* Two states that differ only in how the registers are stored. *)
Definition rlzp_core_eqv (k l : (@Minimal.EarnedMultiPriced.pu_core prop)) : Prop :=
  (forall r, Minimal.EarnedMultiPriced.vals k r = Minimal.EarnedMultiPriced.vals l r) /\ (forall r, Minimal.EarnedMultiPriced.vers k r = Minimal.EarnedMultiPriced.vers l r) /\
  Minimal.EarnedMultiPriced.pc k = Minimal.EarnedMultiPriced.pc l /\ Minimal.EarnedMultiPriced.facts k = Minimal.EarnedMultiPriced.facts l /\ Minimal.EarnedMultiPriced.chan k = Minimal.EarnedMultiPriced.chan l /\
  Minimal.EarnedMultiPriced.err k = Minimal.EarnedMultiPriced.err l.

Definition rlzp_eqv (s t : (@Minimal.EarnedMultiPriced.pu_state prop)) : Prop :=
  rlzp_core_eqv (Minimal.EarnedMultiPriced.core_of s) (Minimal.EarnedMultiPriced.core_of t) /\ Minimal.EarnedMultiPriced.mu s = Minimal.EarnedMultiPriced.mu t /\ Minimal.EarnedMultiPriced.cert s = Minimal.EarnedMultiPriced.cert t.

Lemma rlzp_core_eqv_refl : forall k, rlzp_core_eqv k k.
Proof. intro k. repeat split; auto. Qed.

Lemma rlzp_core_eqv_trans : forall k l m, rlzp_core_eqv k l -> rlzp_core_eqv l m -> rlzp_core_eqv k m.
Proof.
  intros k l m (Hv & Hr & Hp & Hf & Hc & He) (Hv' & Hr' & Hp' & Hf' & Hc' & He').
  repeat split; [intro r; rewrite Hv; apply Hv' | intro r; rewrite Hr; apply Hr' | congruence | congruence | congruence | congruence].
Qed.

Lemma rlzp_eqv_refl : forall s, rlzp_eqv s s.
Proof. intro s. refine (conj _ (conj _ _)); [apply rlzp_core_eqv_refl | reflexivity | reflexivity]. Qed.

Lemma rlzp_eqv_trans : forall s t u, rlzp_eqv s t -> rlzp_eqv t u -> rlzp_eqv s u.
Proof.
  intros s t u (H1 & H2 & H3) (H1' & H2' & H3').
  refine (conj _ (conj _ _)); [eapply rlzp_core_eqv_trans; eauto | congruence | congruence].
Qed.

(* ---- a step does not tell the two storages apart ---- *)

Lemma rlzp_claim_eqv : forall k l p r, rlzp_core_eqv k l -> Minimal.EarnedMultiPriced.pu_claim k p r = Minimal.EarnedMultiPriced.pu_claim l p r.
Proof. intros k l p r (Hv & Hr & _). unfold Minimal.EarnedMultiPriced.pu_claim. rewrite Hr. reflexivity. Qed.

Lemma rlzp_check_ok_eqv : forall k l p r, rlzp_core_eqv k l ->
  Minimal.EarnedMultiPriced.pu_check_ok eval k p r = Minimal.EarnedMultiPriced.pu_check_ok eval l p r.
Proof.
  intros k l p r (Hv & Hr & Hp & Hf & Hc & He). unfold Minimal.EarnedMultiPriced.pu_check_ok.
  rewrite Hv, Hf, He. reflexivity.
Qed.

Lemma rlzp_commit_ok_eqv : forall k l p r, rlzp_core_eqv k l ->
  Minimal.EarnedMultiPriced.pu_commit_ok prop_eqb k p r = Minimal.EarnedMultiPriced.pu_commit_ok prop_eqb l p r.
Proof.
  intros k l p r H. pose proof H as (Hv & Hr & Hp & Hf & Hc & He). unfold Minimal.EarnedMultiPriced.pu_commit_ok.
  rewrite He, Hf, (rlzp_claim_eqv k l p r H). reflexivity.
Qed.

Lemma rlzp_certify_ok_eqv : forall k l, rlzp_core_eqv k l ->
  Minimal.EarnedMultiPriced.pu_certify_ok k = Minimal.EarnedMultiPriced.pu_certify_ok l.
Proof.
  intros k l (Hv & Hr & Hp & Hf & Hc & He). unfold Minimal.EarnedMultiPriced.pu_certify_ok.
  rewrite He, Hc. reflexivity.
Qed.

Lemma rlzp_write_eqv : forall k l r n j, rlzp_core_eqv k l ->
  rlzp_core_eqv (Minimal.EarnedMultiPriced.pu_write k r n j) (Minimal.EarnedMultiPriced.pu_write l r n j).
Proof.
  intros k l r n j (Hv & Hr & Hp & Hf & Hc & He). unfold Minimal.EarnedMultiPriced.pu_write, rlzp_core_eqv; simpl.
  repeat split; try assumption.
  - intro x. unfold Minimal.EarnedMultiPriced.pu_upd. destruct (Nat.eqb x r); [reflexivity | apply Hv].
  - intro x. unfold Minimal.EarnedMultiPriced.pu_upd. destruct (Nat.eqb x r); [rewrite Hr; reflexivity | apply Hr].
Qed.

Lemma rlzp_goto_eqv : forall k l j, rlzp_core_eqv k l ->
  rlzp_core_eqv (Minimal.EarnedMultiPriced.pu_goto k j) (Minimal.EarnedMultiPriced.pu_goto l j).
Proof.
  intros k l j (Hv & Hr & Hp & Hf & Hc & He). unfold Minimal.EarnedMultiPriced.pu_goto, rlzp_core_eqv; simpl.
  repeat split; try assumption.
Qed.

Lemma rlzp_trap_eqv : forall k l, rlzp_core_eqv k l ->
  rlzp_core_eqv (Minimal.EarnedMultiPriced.pu_trap k) (Minimal.EarnedMultiPriced.pu_trap l).
Proof.
  intros k l (Hv & Hr & Hp & Hf & Hc & He). unfold Minimal.EarnedMultiPriced.pu_trap, rlzp_core_eqv; simpl.
  repeat split; try assumption.
Qed.

Lemma rlzp_record_fact_eqv : forall k l f, rlzp_core_eqv k l ->
  rlzp_core_eqv (Minimal.EarnedMultiPriced.pu_record_fact k f) (Minimal.EarnedMultiPriced.pu_record_fact l f).
Proof.
  intros k l f (Hv & Hr & Hp & Hf & Hc & He). unfold Minimal.EarnedMultiPriced.pu_record_fact, rlzp_core_eqv; simpl.
  repeat split; try assumption; congruence.
Qed.

Lemma rlzp_commit_to_eqv : forall k l f, rlzp_core_eqv k l ->
  rlzp_core_eqv (Minimal.EarnedMultiPriced.pu_commit_to k f) (Minimal.EarnedMultiPriced.pu_commit_to l f).
Proof.
  intros k l f (Hv & Hr & Hp & Hf & Hc & He). unfold Minimal.EarnedMultiPriced.pu_commit_to, rlzp_core_eqv; simpl.
  repeat split; try assumption; congruence.
Qed.

Lemma rlzp_cexec_eqv : forall k l (i : (@Minimal.EarnedMultiPriced.pu_instr prop)), rlzp_core_eqv k l ->
  rlzp_core_eqv (Minimal.EarnedMultiPriced.pu_cexec prop_eqb eval k i) (Minimal.EarnedMultiPriced.pu_cexec prop_eqb eval l i).
Proof.
  intros k l i H. pose proof H as (Hv & Hr & Hp & Hf & Hc & He).
  unfold Minimal.EarnedMultiPriced.pu_cexec. rewrite <- He.
  destruct (Minimal.EarnedMultiPriced.err k) eqn:E; [exact H |].
  destruct i as [r | r j | | p r | p r | | ].
  - rewrite <- (Hv r), <- Hp. apply rlzp_write_eqv. exact H.
  - rewrite <- (Hv r), <- Hp. destruct (Minimal.EarnedMultiPriced.vals k r) as [| n].
    + apply rlzp_goto_eqv. exact H.
    + apply rlzp_write_eqv. exact H.
  - exact H.
  - rewrite <- (rlzp_check_ok_eqv k l p r H), <- (rlzp_claim_eqv k l p r H).
    destruct (Minimal.EarnedMultiPriced.pu_check_ok eval k p r).
    + apply rlzp_record_fact_eqv. exact H.
    + apply rlzp_trap_eqv. exact H.
  - rewrite <- (rlzp_commit_ok_eqv k l p r H), <- (rlzp_claim_eqv k l p r H).
    destruct (Minimal.EarnedMultiPriced.pu_commit_ok prop_eqb k p r).
    + apply rlzp_commit_to_eqv. exact H.
    + apply rlzp_trap_eqv. exact H.
  - rewrite <- (rlzp_certify_ok_eqv k l H), <- Hp.
    destruct (Minimal.EarnedMultiPriced.pu_certify_ok k).
    + apply rlzp_goto_eqv. exact H.
    + apply rlzp_trap_eqv. exact H.
  - rewrite <- Hp. apply rlzp_goto_eqv. exact H.
Qed.

Lemma rlzp_fires_eqv : forall k l (i : (@Minimal.EarnedMultiPriced.pu_instr prop)), rlzp_core_eqv k l -> Minimal.EarnedMultiPriced.pu_fires k i = Minimal.EarnedMultiPriced.pu_fires l i.
Proof.
  intros k l i H. unfold Minimal.EarnedMultiPriced.pu_fires. destruct i; try reflexivity.
  apply rlzp_certify_ok_eqv. exact H.
Qed.

Lemma rlzp_exec_eqv : forall s t (i : (@Minimal.EarnedMultiPriced.pu_instr prop)), rlzp_eqv s t ->
  rlzp_eqv (Minimal.EarnedMultiPriced.pu_exec prop_eqb eval s i) (Minimal.EarnedMultiPriced.pu_exec prop_eqb eval t i).
Proof.
  intros s t i (Hk & Hm & Hc). unfold Minimal.EarnedMultiPriced.pu_exec, rlzp_eqv; simpl.
  refine (conj _ (conj _ _)).
  - apply rlzp_cexec_eqv. exact Hk.
  - rewrite Hm. reflexivity.
  - rewrite Hc, (rlzp_fires_eqv _ _ i Hk). reflexivity.
Qed.

Lemma rlzp_next_instr_eqv : forall (P : list (@Minimal.EarnedMultiPriced.pu_instr prop)) k l, rlzp_core_eqv k l ->
  Minimal.EarnedMultiPriced.pu_next_instr P k = Minimal.EarnedMultiPriced.pu_next_instr P l.
Proof.
  intros P k l (Hv & Hr & Hp & Hf & Hc & He). unfold Minimal.EarnedMultiPriced.pu_next_instr. rewrite He, Hp. reflexivity.
Qed.

Lemma rlzp_step_eqv : forall (P : list (@Minimal.EarnedMultiPriced.pu_instr prop)) s t, rlzp_eqv s t ->
  rlzp_eqv (Minimal.EarnedMultiPriced.pu_step prop_eqb eval P s) (Minimal.EarnedMultiPriced.pu_step prop_eqb eval P t).
Proof.
  intros P s t H. pose proof H as (Hk & _). unfold Minimal.EarnedMultiPriced.pu_step.
  rewrite <- (rlzp_next_instr_eqv P _ _ Hk).
  destruct (Minimal.EarnedMultiPriced.pu_next_instr P (Minimal.EarnedMultiPriced.core_of s)) as [i |];
    [apply rlzp_exec_eqv; exact H | exact H].
Qed.

Lemma rlzp_run_prog_eqv : forall n (P : list (@Minimal.EarnedMultiPriced.pu_instr prop)) s t, rlzp_eqv s t ->
  rlzp_eqv (Minimal.EarnedMultiPriced.pu_run_prog prop_eqb eval n P s) (Minimal.EarnedMultiPriced.pu_run_prog prop_eqb eval n P t).
Proof.
  induction n as [| n IH]; intros P s t H; simpl; [exact H |].
  apply IH. apply rlzp_step_eqv. exact H.
Qed.

(* ---- the registers at and above N are never touched ---- *)

Definition rlzp_cinv (N : nat) (g : nat -> nat) (k : (@Minimal.EarnedMultiPriced.pu_core prop)) : Prop :=
  forall r, N <= r -> Minimal.EarnedMultiPriced.vals k r = g r /\ Minimal.EarnedMultiPriced.vers k r = 0.

Definition rlzp_inv (N : nat) (g : nat -> nat) (s : (@Minimal.EarnedMultiPriced.pu_state prop)) : Prop :=
  rlzp_cinv N g (Minimal.EarnedMultiPriced.core_of s).

Lemma rlzp_next_in : forall (P : list (@Minimal.EarnedMultiPriced.pu_instr prop)) (k : (@Minimal.EarnedMultiPriced.pu_core prop)) i, Minimal.EarnedMultiPriced.pu_next_instr P k = Some i -> In i P.
Proof.
  intros P k i H. unfold Minimal.EarnedMultiPriced.pu_next_instr in H.
  destruct (Minimal.EarnedMultiPriced.err k); [discriminate |].
  unfold Minimal.EarnedMultiPriced.pu_fetch in H. destruct (Minimal.EarnedMultiPriced.pc k) as [| m]; [discriminate |].
  destruct (nth_error P m) as [j |] eqn:E; [| discriminate].
  apply nth_error_In in E.
  destruct j; first [discriminate | (injection H as <-; exact E)].
Qed.

Lemma rlzp_cexec_inv : forall N g k (i : (@Minimal.EarnedMultiPriced.pu_instr prop)), rlzp_instr_ok N i = true -> rlzp_cinv N g k ->
  rlzp_cinv N g (Minimal.EarnedMultiPriced.pu_cexec prop_eqb eval k i).
Proof.
  intros N g k i Hi Hk. unfold Minimal.EarnedMultiPriced.pu_cexec. destruct (Minimal.EarnedMultiPriced.err k); [exact Hk |].
  destruct i as [r | r j | | p r | p r | | ]; simpl in Hi.
  - apply Nat.ltb_lt in Hi. unfold Minimal.EarnedMultiPriced.pu_write, rlzp_cinv; simpl. intros x Hx.
    unfold Minimal.EarnedMultiPriced.pu_upd. assert (Hne : Nat.eqb x r = false) by (apply Nat.eqb_neq; lia).
    rewrite Hne. apply Hk. exact Hx.
  - apply Nat.ltb_lt in Hi. destruct (Minimal.EarnedMultiPriced.vals k r) as [| n].
    + exact Hk.
    + unfold Minimal.EarnedMultiPriced.pu_write, rlzp_cinv; simpl. intros x Hx.
      unfold Minimal.EarnedMultiPriced.pu_upd. assert (Hne : Nat.eqb x r = false) by (apply Nat.eqb_neq; lia).
      rewrite Hne. apply Hk. exact Hx.
  - exact Hk.
  - destruct (Minimal.EarnedMultiPriced.pu_check_ok eval k p r); exact Hk.
  - destruct (Minimal.EarnedMultiPriced.pu_commit_ok prop_eqb k p r); exact Hk.
  - destruct (Minimal.EarnedMultiPriced.pu_certify_ok k); exact Hk.
  - unfold Minimal.EarnedMultiPriced.pu_goto, rlzp_cinv; simpl. exact Hk.
Qed.

Lemma rlzp_step_inv : forall N g (P : list (@Minimal.EarnedMultiPriced.pu_instr prop)) s, rlzp_prog_below N P = true -> rlzp_inv N g s ->
  rlzp_inv N g (Minimal.EarnedMultiPriced.pu_step prop_eqb eval P s).
Proof.
  intros N g P s HP Hs. unfold Minimal.EarnedMultiPriced.pu_step.
  destruct (Minimal.EarnedMultiPriced.pu_next_instr P (Minimal.EarnedMultiPriced.core_of s)) as [i |] eqn:E; [| exact Hs].
  apply rlzp_next_in in E. unfold rlzp_prog_below in HP. rewrite forallb_forall in HP.
  unfold Minimal.EarnedMultiPriced.pu_exec, rlzp_inv. simpl. apply rlzp_cexec_inv; [apply HP; exact E | exact Hs].
Qed.

Lemma rlzp_nth_tab : forall N f r, r < N -> nth r (rlzp_tab N f) 0 = f r.
Proof.
  intros N f r H. unfold rlzp_tab.
  rewrite (nth_indep _ 0 (f 0)) by (rewrite map_length, seq_length; exact H).
  rewrite map_nth, seq_nth by exact H. reflexivity.
Qed.

Lemma rlzp_compact_eqv : forall N g s, rlzp_inv N g s -> rlzp_eqv (rlzp_compact N g s) s.
Proof.
  intros N g s Hs. unfold rlzp_eqv, rlzp_core_eqv, rlzp_compact, rlzp_compact_core; simpl.
  repeat split; try reflexivity.
  - intro r. destruct (Nat.ltb r N) eqn:E.
    + apply Nat.ltb_lt in E. apply rlzp_nth_tab. exact E.
    + apply Nat.ltb_ge in E. symmetry. apply (proj1 (Hs r E)).
  - intro r. destruct (Nat.ltb r N) eqn:E.
    + apply Nat.ltb_lt in E. apply rlzp_nth_tab. exact E.
    + apply Nat.ltb_ge in E. symmetry. apply (proj2 (Hs r E)).
Qed.

Lemma rlzp_compact_inv : forall N g s, rlzp_inv N g (rlzp_compact N g s).
Proof.
  intros N g s. unfold rlzp_inv, rlzp_cinv, rlzp_compact, rlzp_compact_core; simpl.
  intros r Hr. apply Nat.ltb_ge in Hr. rewrite Hr. split; reflexivity.
Qed.

(* A run that steps and, after the steps the schedule marks, compacts. *)
Fixpoint rlzp_sched (N : nat) (g : nat -> nat) (P : list (@Minimal.EarnedMultiPriced.pu_instr prop)) (sched : list bool)
  (s : (@Minimal.EarnedMultiPriced.pu_state prop)) : (@Minimal.EarnedMultiPriced.pu_state prop) :=
  match sched with
  | [] => s
  | b :: t =>
      rlzp_sched N g P t
        (if b then rlzp_compact N g (Minimal.EarnedMultiPriced.pu_step prop_eqb eval P s) else Minimal.EarnedMultiPriced.pu_step prop_eqb eval P s)
  end.

(* Whatever the schedule, the run with compaction is the run without it, up
   to the storage of the registers: same program counter, facts, channel,
   trap latch, ledger and flag, and every register and version equal. *)
Theorem rlzp_sched_sound : forall N g (P : list (@Minimal.EarnedMultiPriced.pu_instr prop)) sched s,
  rlzp_prog_below N P = true -> rlzp_inv N g s ->
  rlzp_eqv (rlzp_sched N g P sched s) (Minimal.EarnedMultiPriced.pu_run_prog prop_eqb eval (length sched) P s).
Proof.
  intros N g P sched. induction sched as [| b t IH]; intros s HP Hs; simpl.
  - apply rlzp_eqv_refl.
  - assert (Hs' : rlzp_inv N g (Minimal.EarnedMultiPriced.pu_step prop_eqb eval P s)) by (apply rlzp_step_inv; assumption).
    assert (Hu : rlzp_inv N g (if b then rlzp_compact N g (Minimal.EarnedMultiPriced.pu_step prop_eqb eval P s) else Minimal.EarnedMultiPriced.pu_step prop_eqb eval P s)).
    { destruct b; [apply rlzp_compact_inv | exact Hs']. }
    assert (Heq : rlzp_eqv (if b then rlzp_compact N g (Minimal.EarnedMultiPriced.pu_step prop_eqb eval P s) else Minimal.EarnedMultiPriced.pu_step prop_eqb eval P s)
                             (Minimal.EarnedMultiPriced.pu_step prop_eqb eval P s)).
    { destruct b; [apply rlzp_compact_eqv; exact Hs' | apply rlzp_eqv_refl]. }
    eapply rlzp_eqv_trans; [apply IH; assumption |].
    apply rlzp_run_prog_eqv. exact Heq.
Qed.

End Compactp.

(* ================================================================= *)
(* U and U_P.                                                         *)
(* ================================================================= *)

(* The registers 0 to 95 are held in the table. U and U_P name registers up
   to 80 (the layout constants of UniversalLayout.v and UniversalPLayout.v). *)
Definition rlz_table_size : nat := 96.

Lemma rlz_host_program_below :
  rlz_prog_below rlz_table_size Kernel.Realize.rlz_host_program = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rlz_phost_program_below :
  rlzp_prog_below rlz_table_size Kernel.RealizePriced.rlz_phost_program = true.
Proof. vm_compute. reflexivity. Qed.

(* A run of U from a state, one block of steps for each entry of the
   schedule: a step, then, when the entry is true, a replacement. g is the
   function the registers at and above rlz_table_size read as. *)
Definition rlz_host_sched (g : nat -> nat) (sched : list bool)
  (s : @Minimal.EarnedMulti.state Minimal.UniversalCodes.hprop)
  : @Minimal.EarnedMulti.state Minimal.UniversalCodes.hprop :=
  rlz_sched Kernel.Realize.rlz_host_prop_eqb Kernel.Realize.rlz_host_eval
    rlz_table_size g Kernel.Realize.rlz_host_program sched s.

Definition rlz_phost_sched (g : nat -> nat) (sched : list bool)
  (s : @Minimal.EarnedMultiPriced.pu_state Kernel.UniversalPCodes.pu_hprop)
  : @Minimal.EarnedMultiPriced.pu_state Kernel.UniversalPCodes.pu_hprop :=
  rlzp_sched Kernel.RealizePriced.rlz_phost_prop_eqb Kernel.RealizePriced.rlz_pu_heval
    rlz_table_size g Kernel.RealizePriced.rlz_phost_program sched s.

(* A run is the same whether its schedule is given at once or in pieces. *)
Lemma rlz_host_sched_app : forall g l1 l2 s,
  rlz_host_sched g (l1 ++ l2) s = rlz_host_sched g l2 (rlz_host_sched g l1 s).
Proof.
  intros g l1. induction l1 as [| b t IH]; intros l2 s; simpl; [reflexivity |].
  apply IH.
Qed.

Lemma rlz_phost_sched_app : forall g l1 l2 s,
  rlz_phost_sched g (l1 ++ l2) s = rlz_phost_sched g l2 (rlz_phost_sched g l1 s).
Proof.
  intros g l1. induction l1 as [| b t IH]; intros l2 s; simpl; [reflexivity |].
  apply IH.
Qed.

(* The host of U after any schedule of steps and replacements from a loaded
   guest equals, up to storage, the host after as many steps as the schedule
   has entries: the term rlz_host_at, which rlz_host_at_is shows is
   UniversalRun.v's hrun. *)
Theorem rlz_host_sched_sound : forall P x y sched,
  rlz_eqv (rlz_host_sched (Kernel.Realize.rlz_host_regs P x y) sched
             (Kernel.Realize.rlz_host_load P x y))
          (Kernel.Realize.rlz_host_at P x y (length sched)).
Proof.
  intros P x y sched. unfold rlz_host_sched, Kernel.Realize.rlz_host_at.
  apply rlz_sched_sound; [exact rlz_host_program_below |].
  unfold rlz_inv, rlz_cinv, Kernel.Realize.rlz_host_load, Kernel.Realize.rlz_host_start.
  simpl. intros r _. split; reflexivity.
Qed.

Theorem rlz_phost_sched_sound : forall P x y sched,
  rlzp_eqv (rlz_phost_sched (Kernel.RealizePriced.rlz_phost_regs P x y) sched
              (Kernel.RealizePriced.rlz_phost_load P x y))
           (Kernel.RealizePriced.rlz_phost_at P x y (length sched)).
Proof.
  intros P x y sched. unfold rlz_phost_sched, Kernel.RealizePriced.rlz_phost_at.
  apply rlzp_sched_sound; [exact rlz_phost_program_below |].
  unfold rlzp_inv, rlzp_cinv, Kernel.RealizePriced.rlz_phost_load, Kernel.RealizePriced.rlz_phost_start.
  simpl. intros r _. split; reflexivity.
Qed.

(* The same, with the names of the theorems about U and U_P. *)
Corollary rlz_host_sched_sound_original : forall P x y sched,
  rlz_eqv (rlz_host_sched (Kernel.Realize.rlz_host_regs P x y) sched
             (Kernel.Realize.rlz_host_load P x y))
          (Minimal.EarnedMulti.run_prog Minimal.UniversalCodes.hprop_eqb Minimal.UniversalCodes.heval
             (length sched) Kernel.UniversalLayout.U (Kernel.UniversalSim.hload P x y)).
Proof.
  intros P x y sched. rewrite <- Kernel.Realize.rlz_host_at_is. apply rlz_host_sched_sound.
Qed.

Corollary rlz_phost_sched_sound_original : forall P x y sched,
  rlzp_eqv (rlz_phost_sched (Kernel.RealizePriced.rlz_phost_regs P x y) sched
              (Kernel.RealizePriced.rlz_phost_load P x y))
           (Minimal.EarnedMultiPriced.pu_run_prog Kernel.UniversalPCodes.pu_hprop_eqb
              Kernel.UniversalPCodes.pu_heval (length sched) Kernel.UniversalPLayout.U_P
              (Kernel.UniversalPSim.pu_hload (map Kernel.RealizePriced.rlz_to_pr P) x y)).
Proof.
  intros P x y sched. rewrite <- Kernel.RealizePriced.rlz_phost_at_eq. apply rlz_phost_sched_sound.
Qed.

(* ================================================================= *)
(* Assumption audit. Every line must print                            *)
(* "Closed under the global context".                                 *)
(* ================================================================= *)

Print Assumptions rlz_sched_sound.
Print Assumptions rlzp_sched_sound.
Print Assumptions rlz_host_program_below.
Print Assumptions rlz_phost_program_below.
Print Assumptions rlz_host_sched_app.
Print Assumptions rlz_phost_sched_app.
Print Assumptions rlz_host_sched_sound.
Print Assumptions rlz_phost_sched_sound.
Print Assumptions rlz_host_sched_sound_original.
Print Assumptions rlz_phost_sched_sound_original.
