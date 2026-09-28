(** FiniteCertMachine: a finite, merge-priced machine that the VM runs.

    [PermanentCertification] and [PermanentRecordPricing] are about finite
    machines whose certificate no step revokes. The 51-opcode VM is not such
    a machine as a whole, by design: its ledger is an unbounded natural, and
    its schedule prices the merge that certifies while leaving other merges
    free. The last section proves both halves of that. This file builds a
    finite machine that is an instance and shows the VM runs it.

    The finite machine has four program slots and a certification flag:
    eight states. Three instructions.

    - [FCertify] stamps the flag and moves to the next slot. It merges each
      slot's stamped and unstamped states, so it costs one.
    - [FJump a] moves to slot [a]. It merges four slots into one, a
      four-fold squeeze, so under one unit per halving it costs two.
    - [FNext] moves to the next slot, wrapping around. It is a bijection, so
      it costs nothing.

    The machine is finite, its certificate is permanent, and its prices meet
    both premises: every merging instruction costs at least one, and every
    instruction's cost pays for its squeeze. So A2 and the logarithmic bound
    of [PermanentRecordPricing] hold for it as theorems, not as a chosen rule.

    The VM runs it. Read a VM state through the window
    (program counter modulo four, certification flag). Then [CERTIFY 0],
    [JUMP a 2], and [CHECKPOINT "" 0] step exactly as [FCertify], [FJump a],
    and [FNext] step, and the VM ledger rises by exactly the finite
    machine's price. The [JUMP] charge of two is a program's choice of
    [mu_delta]; the VM's schedule allows it and does not force it. The
    window is a projection: the VM's full state, ledger included, keeps more
    than the eight finite states do. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
From Coq Require String.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.
From Kernel Require Import MuLedgerConservation PrimeAxiom MuInitiality.
From Kernel Require Import PermanentCertification.
From Kernel Require Import PermanentRecordPricing.

(** * A generic counting lemma *)

(** If every fiber of [f] on a duplicate-free list has at most [K] members,
    the list has at most [K] times as many members as it has images. *)
Section FiberBound.

Variables (X Y : Type).
Variable eq_dec_T : forall a b : Y, {a = b} + {a <> b}.
Variable f : X -> Y.

Definition hits (y : Y) (x : X) : bool :=
  if eq_dec_T (f x) y then true else false.

Lemma filter_split_length :
  forall (p : X -> bool) (l : list X),
    length (filter p l) + length (filter (fun x => negb (p x)) l) = length l.
Proof.
  intros p l. induction l as [| x xs IH]; simpl; [reflexivity |].
  destruct (p x); simpl; lia.
Qed.

Lemma fiber_bound_compression :
  forall K (D : list X),
    NoDup D ->
    (forall y, length (filter (hits y) D) <= K) ->
    length D <= K * length (nodup eq_dec_T (map f D)).
Proof.
  intros K D.
  remember (length D) as n eqn:Hn.
  revert D Hn.
  induction n as [n IH] using (well_founded_induction Nat.lt_wf_0).
  intros D Hn HndD Hfib.
  destruct D as [| x xs].
  - simpl in Hn. subst n. simpl. lia.
  - set (y := f x).
    set (B := filter (fun z => negb (hits y z)) (x :: xs)).
    assert (Hsplit := filter_split_length (hits y) (x :: xs)).
    assert (HA : length (filter (hits y) (x :: xs)) <= K) by apply Hfib.
    assert (HxA : In x (filter (hits y) (x :: xs))).
    { apply filter_In. split; [left; reflexivity |].
      unfold hits. destruct (eq_dec_T (f x) y); [reflexivity | contradiction]. }
    assert (HAlen : 1 <= length (filter (hits y) (x :: xs))).
    { destruct (filter (hits y) (x :: xs)); [contradiction | simpl; lia]. }
    assert (HBlt : length B < n) by (unfold B; lia).
    assert (HndB : NoDup B) by (apply NoDup_filter; exact HndD).
    assert (HfibB : forall z, length (filter (hits z) B) <= K).
    { intro z. apply Nat.le_trans with (m := length (filter (hits z) (x :: xs))).
      - apply NoDup_incl_length.
        + apply NoDup_filter. exact HndB.
        + intros w Hw. apply filter_In in Hw as [HwB Hwz].
          apply filter_In. split; [| exact Hwz].
          unfold B in HwB. apply filter_In in HwB as [Hw _]. exact Hw.
      - apply Hfib. }
    pose proof (IH (length B) HBlt B eq_refl HndB HfibB) as HIH.
    assert (Himg : length (y :: nodup eq_dec_T (map f B))
                   <= length (nodup eq_dec_T (map f (x :: xs)))).
    { apply NoDup_incl_length.
      - constructor; [| apply NoDup_nodup].
        intro Hin. apply nodup_In in Hin.
        apply in_map_iff in Hin as [w [Hwy HwB]].
        unfold B in HwB. apply filter_In in HwB as [_ Hneg].
        unfold hits in Hneg. rewrite Hwy in Hneg.
        destruct (eq_dec_T y y); [discriminate | contradiction].
      - intros z [<- | Hz].
        + apply nodup_In. apply in_map. left. reflexivity.
        + apply nodup_In. apply nodup_In in Hz.
          apply in_map_iff in Hz as [w [<- HwB]].
          apply in_map. unfold B in HwB. apply filter_In in HwB as [Hw _]. exact Hw. }
    simpl length in Himg.
    rewrite <- Hsplit in Hn. fold B in Hn.
    assert (Hmul : K * S (length (nodup eq_dec_T (map f B)))
                   <= K * length (nodup eq_dec_T (map f (x :: xs))))
      by (apply Nat.mul_le_mono_l; exact Himg).
    rewrite Nat.mul_succ_r in Hmul.
    lia.
Qed.

End FiberBound.

(** * The finite machine *)

Inductive Slot := L0 | L1 | L2 | L3.

Definition slot_eq_dec : forall a b : Slot, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition next_slot (p : Slot) : Slot :=
  match p with L0 => L1 | L1 => L2 | L2 => L3 | L3 => L0 end.

Definition FState : Type := (Slot * bool)%type.

Definition fstate_eq_dec : forall a b : FState, {a = b} + {a <> b}.
Proof. decide equality; auto using bool_dec, slot_eq_dec. Defined.

Inductive FInstr := FCertify | FJump (a : Slot) | FNext.

Definition fstep (x : FState) (i : FInstr) : FState :=
  match i with
  | FCertify => (next_slot (fst x), true)
  | FJump a => (a, snd x)
  | FNext => (next_slot (fst x), snd x)
  end.

Definition fcert (x : FState) : bool := snd x.

Definition fcost (i : FInstr) : nat :=
  match i with FCertify => 1 | FJump _ => 2 | FNext => 0 end.

Definition all_fstates : list FState :=
  [(L0, false); (L1, false); (L2, false); (L3, false);
   (L0, true); (L1, true); (L2, true); (L3, true)].

Theorem fin_finite : finite_states all_fstates.
Proof.
  split.
  - repeat constructor; simpl; intuition discriminate.
  - intros [p c]. destruct p, c; simpl; tauto.
Qed.

Theorem fin_permanent : permanent fstep fcert.
Proof. intros [p c] i Hc. destruct i; simpl in *; auto. Qed.

(** [FNext] forgets nothing. [FCertify] and [FJump] merge. *)
Lemma next_slot_injective : forall p q, next_slot p = next_slot q -> p = q.
Proof. intros p q H. destruct p, q; simpl in H; congruence. Qed.

Theorem fnext_injective : step_injective fstep FNext.
Proof.
  intros [p c] [q d] H. simpl in H. inversion H as [[Hpq Hcd]].
  apply next_slot_injective in Hpq. subst. reflexivity.
Qed.

Theorem fcertify_merges : ~ step_injective fstep FCertify.
Proof.
  intro Hinj. specialize (Hinj (L0, false) (L0, true) eq_refl). discriminate.
Qed.

Theorem fjump_merges : forall a, ~ step_injective fstep (FJump a).
Proof.
  intros a Hinj. specialize (Hinj (L0, false) (L1, false) eq_refl). discriminate.
Qed.

(** The price is the merge indicator, with the jump's squeeze paid in full. *)
Theorem fin_merging_priced : merging_steps_priced fstep fcost.
Proof.
  intros i Hmerge. destruct i; simpl; [lia | lia |].
  exfalso. exact (Hmerge fnext_injective).
Qed.

(** Every instruction's cost pays for its squeeze. *)
Lemma fin_fiber_bound :
  forall i (D : list FState),
    NoDup D ->
    forall y, length (filter (hits FState FState fstate_eq_dec (fun x => fstep x i) y) D)
              <= 2 ^ fcost i.
Proof.
  intros i D HD y.
  apply Nat.le_trans
    with (m := length (filter (hits FState FState fstate_eq_dec (fun x => fstep x i) y)
                              all_fstates)).
  - apply NoDup_incl_length; [apply NoDup_filter; exact HD |].
    intros x Hx. apply filter_In in Hx as [_ Hhit].
    apply filter_In. split; [apply (proj2 fin_finite) | exact Hhit].
  - destruct i as [| a |]; destruct y as [q d]; destruct q, d;
      try destruct a; vm_compute; lia.
Qed.

Theorem fin_compression_priced :
  compression_priced fstep fcost fstate_eq_dec.
Proof.
  intros i D HD. unfold image_size.
  apply fiber_bound_compression; [exact HD |].
  intro y. apply fin_fiber_bound. exact HD.
Qed.

(** A2 holds for the finite machine, twice over. *)
Theorem fin_a2_from_merging_price : a2_holds fstep fcert fcost.
Proof.
  exact (a2_from_merging_price_and_permanence FState FInstr fstep fcert fcost
           all_fstates fin_finite fin_permanent fin_merging_priced).
Qed.

Theorem fin_a2_from_compression_price : a2_holds fstep fcert fcost.
Proof.
  exact (a2_from_compression_price_and_permanence FState FInstr fstep fcert fcost
           fstate_eq_dec all_fstates fin_finite fin_permanent fin_compression_priced).
Qed.

(** * The VM runs the finite machine *)

Fixpoint slot_of_nat (n : nat) : Slot :=
  match n with 0 => L0 | S k => next_slot (slot_of_nat k) end.

Definition nat_of_slot (p : Slot) : nat :=
  match p with L0 => 0 | L1 => 1 | L2 => 2 | L3 => 3 end.

Lemma slot_of_nat_of_slot : forall p, slot_of_nat (nat_of_slot p) = p.
Proof. intros []; reflexivity. Qed.

(** The window: program counter modulo four, and the certification flag. *)
Definition fin_window (s : VMState) : FState :=
  (slot_of_nat s.(vm_pc), s.(vm_certified)).

Definition vm_instr_of (i : FInstr) : vm_instruction :=
  match i with
  | FCertify => instr_certify 0
  | FJump a => instr_jump (nat_of_slot a) 2
  | FNext => instr_checkpoint String.EmptyString 0
  end.

(** One VM step, read through the window, is one finite step. *)
Theorem vm_runs_finite_machine :
  forall (s : VMState) (i : FInstr),
    fin_window (vm_apply s (vm_instr_of i)) = fstep (fin_window s) i.
Proof.
  intros s i. destruct i as [| a |]; unfold fin_window; simpl.
  - reflexivity.
  - rewrite slot_of_nat_of_slot. reflexivity.
  - reflexivity.
Qed.

(** And the VM ledger rises by exactly the finite machine's price. *)
Theorem vm_pays_finite_price :
  forall (s : VMState) (i : FInstr),
    (vm_apply s (vm_instr_of i)).(vm_mu) = s.(vm_mu) + fcost i.
Proof.
  intros s i. rewrite vm_apply_mu. destruct i; reflexivity.
Qed.

Fixpoint frun (trace : list FInstr) (x : FState) : FState :=
  match trace with [] => x | i :: rest => frun rest (fstep x i) end.

Fixpoint fcost_total (trace : list FInstr) : nat :=
  match trace with [] => 0 | i :: rest => fcost i + fcost_total rest end.

Fixpoint vm_run_list (trace : list FInstr) (s : VMState) : VMState :=
  match trace with
  | [] => s
  | i :: rest => vm_run_list rest (vm_apply s (vm_instr_of i))
  end.

(** Whole runs agree too: the window follows the finite run, and the ledger
    rises by the finite total. *)
Theorem vm_runs_finite_trace :
  forall trace (s : VMState),
    fin_window (vm_run_list trace s) = frun trace (fin_window s) /\
    (vm_run_list trace s).(vm_mu) = s.(vm_mu) + fcost_total trace.
Proof.
  induction trace as [| i rest IH]; intro s; simpl.
  - split; [reflexivity | lia].
  - destruct (IH (vm_apply s (vm_instr_of i))) as [Hw Hmu].
    rewrite vm_runs_finite_machine in Hw.
    split; [exact Hw |].
    rewrite Hmu, vm_pays_finite_price. lia.
Qed.

(** Any VM run of this fragment that starts uncertified and ends certified
    has paid at least one, and the payment is the finite machine's derived
    price, not a rule supplied for the purpose. *)
Theorem vm_fragment_certification_paid :
  forall trace (s : VMState),
    s.(vm_certified) = false ->
    (vm_run_list trace s).(vm_certified) = true ->
    (vm_run_list trace s).(vm_mu) >= s.(vm_mu) + 1.
Proof.
  intros trace s H0 H1.
  destruct (vm_runs_finite_trace trace s) as [Hw Hmu].
  rewrite Hmu.
  assert (Hfloor : fcost_total trace >= 1).
  { assert (Hstart : fcert (fin_window s) = false) by exact H0.
    assert (Hend : fcert (frun trace (fin_window s)) = true).
    { rewrite <- Hw. exact H1. }
    clear Hw Hmu H0 H1.
    revert Hstart Hend. generalize (fin_window s) as x.
    induction trace as [| i rest IH]; intros x Hstart Hend; simpl in *.
    - rewrite Hstart in Hend. discriminate.
    - destruct (fcert (fstep x i)) eqn:Hmid.
      + pose proof (fin_a2_from_merging_price x i Hstart Hmid). lia.
      + pose proof (IH (fstep x i) Hmid Hend). lia. }
  lia.
Qed.

(** * What the full VM prices

    The full VM is not an instance of the permanent-certificate theorem, and
    that is a design choice. Its schedule prices the step that certifies and
    leaves other merges free. Both halves are theorems. The certifying step
    merges states: a certified and an uncertified state that agree on
    everything else land on the same result, and the VM charges that step at
    least one. And a [JUMP] at zero cost merges program counters for free.
    Pricing every merge is what Landauer's principle would ask of a physical
    machine; the VM leaves that question to physics and prices the
    certification merge alone. *)

Definition with_certified (s : VMState) (b : bool) : VMState :=
  {| vm_graph := s.(vm_graph);
     vm_csrs := s.(vm_csrs);
     vm_regs := s.(vm_regs);
     vm_mem := s.(vm_mem);
     vm_pc := s.(vm_pc);
     vm_mu := s.(vm_mu);
     vm_mu_tensor := s.(vm_mu_tensor);
     vm_err := s.(vm_err);
     vm_logic_acc := s.(vm_logic_acc);
     vm_mstatus := s.(vm_mstatus);
     vm_witness := s.(vm_witness);
     vm_certified := b |}.

Definition with_pc (s : VMState) (p : nat) : VMState :=
  {| vm_graph := s.(vm_graph);
     vm_csrs := s.(vm_csrs);
     vm_regs := s.(vm_regs);
     vm_mem := s.(vm_mem);
     vm_pc := p;
     vm_mu := s.(vm_mu);
     vm_mu_tensor := s.(vm_mu_tensor);
     vm_err := s.(vm_err);
     vm_logic_acc := s.(vm_logic_acc);
     vm_mstatus := s.(vm_mstatus);
     vm_witness := s.(vm_witness);
     vm_certified := s.(vm_certified) |}.

(** [CERTIFY] forgets whether the state was already certified. *)
Lemma certify_forgets_flag :
  forall s d,
    vm_apply (with_certified s false) (instr_certify d) =
    vm_apply (with_certified s true) (instr_certify d).
Proof. intros s d. reflexivity. Qed.

Theorem vm_certify_merges : forall d, ~ step_injective vm_apply (instr_certify d).
Proof.
  intros d Hinj.
  specialize (Hinj (with_certified init_state false) (with_certified init_state true)
                   (certify_forgets_flag init_state d)).
  apply (f_equal vm_certified) in Hinj. discriminate.
Qed.

(** Every VM step that switches the certification flag on is a merge, and
    the VM prices it. *)
Theorem vm_certifying_step_is_priced_merge :
  forall (s : VMState) (i : vm_instruction),
    s.(vm_certified) = false ->
    (vm_apply s i).(vm_certified) = true ->
    ~ step_injective vm_apply i /\ instruction_cost i >= 1.
Proof.
  intros s i Hoff Hon.
  rewrite vm_apply_certified in Hon.
  destruct i; try (rewrite Hoff in Hon; discriminate).
  split; [apply vm_certify_merges | simpl; lia].
Qed.

(** A zero-cost [JUMP] merges program counters, and the VM charges nothing. *)
Theorem vm_jump_is_free_merge :
  ~ step_injective vm_apply (instr_jump 0 0) /\ instruction_cost (instr_jump 0 0) = 0.
Proof.
  split; [| reflexivity].
  intro Hinj.
  specialize (Hinj (with_pc init_state 0) (with_pc init_state 1) eq_refl).
  apply (f_equal vm_pc) in Hinj. discriminate.
Qed.

(** Together: the VM prices the merge that certifies and leaves at least one
    other merge free. So the merging-price premise of
    [a2_from_merging_price_and_permanence] fails for the full VM on purpose,
    while A2 itself holds there as a theorem. *)
Theorem vm_prices_certifying_merge_leaves_others_free :
  (forall (s : VMState) (i : vm_instruction),
      s.(vm_certified) = false ->
      (vm_apply s i).(vm_certified) = true ->
      ~ step_injective vm_apply i /\ instruction_cost i >= 1) /\
  (exists i : vm_instruction, ~ step_injective vm_apply i /\ instruction_cost i = 0) /\
  ~ merging_steps_priced vm_apply instruction_cost.
Proof.
  split; [exact vm_certifying_step_is_priced_merge |].
  split; [exists (instr_jump 0 0); exact vm_jump_is_free_merge |].
  intro Hpriced.
  destruct vm_jump_is_free_merge as [Hmerge Hzero].
  pose proof (Hpriced (instr_jump 0 0) Hmerge) as Hc.
  rewrite Hzero in Hc. inversion Hc.
Qed.
