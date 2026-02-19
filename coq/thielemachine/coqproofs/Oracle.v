From Coq Require Import List Lia ZArith.
Import ListNotations.
Local Open Scope nat_scope.

From ThieleMachine Require Import ThieleMachine PartitionLogic ThieleProc.
From Kernel Require Import MuLedgerConservation.

Local Notation sum_mu_exec := ThieleMachine.sum_mu.

(** * Sighted oracle state scaffolding *)

(**  The second-level Thiele machine [T_1] reasons about full [Prog]
     scripts before emitting them to the blind core [T_0].  Its state
     therefore tracks the candidate program, the active partition of the
     search space, and the µ-ledger entries accrued while discovering the
     witness.  This file records that data as a reusable Coq record and
     supplies the minimal lemmas needed to fold µ-cost deltas back into
     the ledger total. *)

Record T1_State := {
  t1_prog : Prog;
  t1_partition : Partition;
  t1_mu_ledger : list nat;
}.

(**  Materialising the oracle's verdict for [T_0] requires a compact
     receipt that exposes only the witness program, the partition that
     scoped the search, and the µ-total accumulated along the way. *)
Record T1_Receipt := {
  t1_receipt_prog : Prog;
  t1_receipt_partition : Partition;
  t1_receipt_mu_total : nat;
}.

(**  Once [T_1] emits a receipt, the classical [T_0] executor must be
     able to replay the witness program.  A [T1_ReceiptWitness] packages
     the concrete [State] and execution trace that justify that replay,
     together with a µ-bound that shows the ledger total recorded in the
     receipt dominates the certificate sizes recovered from the receipts
     catalogue. *)
Record T1_ReceiptWitness (receipt : T1_Receipt) := {
  t1_receipt_witness_state0 : State;
  t1_receipt_witness_trace : list (State * StepObs);
  t1_receipt_witness_exec :
    Exec receipt.(t1_receipt_prog)
         t1_receipt_witness_state0
         t1_receipt_witness_trace;
  t1_receipt_witness_replay :
    replay_ok receipt.(t1_receipt_prog)
              t1_receipt_witness_state0
              (receipts_of t1_receipt_witness_state0 t1_receipt_witness_trace)
    = true;
  t1_receipt_witness_mu_bound :
    Z.le (sum_bits (receipts_of t1_receipt_witness_state0
                                    t1_receipt_witness_trace))
         (Z.of_nat receipt.(t1_receipt_mu_total));
}.

(**  Bootstrapping a search starts with an empty µ-ledger. *)
Definition t1_bootstrap_state (prog : Prog) (partition : Partition) : T1_State :=
  {| t1_prog := prog;
     t1_partition := partition;
     t1_mu_ledger := [] |}.

(**  Logging a discovery step appends its µ-cost to the ledger. *)
Definition t1_charge_mu (st : T1_State) (delta : nat) : T1_State :=
  {| t1_prog := st.(t1_prog);
     t1_partition := st.(t1_partition);
     t1_mu_ledger := st.(t1_mu_ledger) ++ [delta] |}.

Definition t1_with_partition (st : T1_State) (partition : Partition) : T1_State :=
  {| t1_prog := st.(t1_prog);
     t1_partition := partition;
     t1_mu_ledger := st.(t1_mu_ledger) |}.

Definition t1_repartition (st : T1_State) (new_partition : Partition) : T1_State :=
  let delta := partition_change_cost st.(t1_partition) new_partition in
  t1_charge_mu (t1_with_partition st new_partition) delta.

Definition t1_mu_total (st : T1_State) : nat :=
  ledger_sum st.(t1_mu_ledger).

(** HELPER: Base case property *)
(** HELPER: Base case property *)
Lemma t1_bootstrap_total_zero :
  forall prog partition,
    t1_mu_total (t1_bootstrap_state prog partition) = 0%nat.
Proof.
  intros prog partition. unfold t1_mu_total, t1_bootstrap_state. simpl.
  reflexivity.
Qed.

(** [ledger_sum_app_singleton]: formal specification. *)
Lemma ledger_sum_app_singleton :
  forall l delta,
    ledger_sum (l ++ [delta]) = (ledger_sum l + delta)%nat.
Proof.
  induction l as [|hd tl IH]; intros delta; simpl.
  - lia.
  - rewrite IH. lia.
Qed.
(** HELPER: Accessor/projection *)

(** HELPER: Accessor/projection *)
Lemma t1_charge_mu_total :
  forall st delta,
    t1_mu_total (t1_charge_mu st delta) = (t1_mu_total st + delta)%nat.
Proof.
  intros st delta. unfold t1_mu_total, t1_charge_mu. simpl.
  apply ledger_sum_app_singleton.
Qed.

(** [t1_charge_mu_prog_preserved]: formal specification. *)
Lemma t1_charge_mu_prog_preserved :
  forall st delta,
    t1_prog (t1_charge_mu st delta) = t1_prog st.
Proof.
  reflexivity.
Qed.

(** [t1_charge_mu_partition_preserved]: formal specification. *)
Lemma t1_charge_mu_partition_preserved :
  forall st delta,
    t1_partition (t1_charge_mu st delta) = t1_partition st.
Proof.
  reflexivity.
(** HELPER: Accessor/projection *)
Qed.

(** HELPER: Accessor/projection *)
Lemma t1_with_partition_total :
  forall st partition,
    t1_mu_total (t1_with_partition st partition) = t1_mu_total st.
Proof.
  intros st partition. reflexivity.
Qed.

(** [t1_with_partition_prog_preserved]: formal specification. *)
Lemma t1_with_partition_prog_preserved :
  forall st partition,
    t1_prog (t1_with_partition st partition) = t1_prog st.
Proof.
  reflexivity.
Qed.

(** [t1_with_partition_partition_replaced]: formal specification. *)
Lemma t1_with_partition_partition_replaced :
  forall st partition,
    t1_partition (t1_with_partition st partition) = partition.
Proof.
  intros st partition. reflexivity.
Qed.

(** [t1_repartition_prog_preserved]: formal specification. *)
Lemma t1_repartition_prog_preserved :
  forall st new_partition,
    t1_prog (t1_repartition st new_partition) = t1_prog st.
Proof.
  reflexivity.
Qed.

(* DEFINITIONAL — record field accessor after repartition *)
(** [t1_repartition_partition_replaced]: formal specification. *)
Lemma t1_repartition_partition_replaced :
  forall st new_partition,
    t1_partition (t1_repartition st new_partition) = new_partition.
Proof.
  intros st new_partition. unfold t1_repartition, t1_with_partition, t1_charge_mu.
(** HELPER: Accessor/projection *)
  reflexivity.
Qed.

(** HELPER: Accessor/projection *)
Lemma t1_repartition_total :
  forall st new_partition,
    t1_mu_total (t1_repartition st new_partition)
    = (t1_mu_total st + partition_change_cost st.(t1_partition) new_partition)%nat.
Proof.
  intros st new_partition. unfold t1_repartition.
  rewrite t1_charge_mu_total, t1_with_partition_total. reflexivity.
Qed.

Definition t1_emit_receipt (st : T1_State) : T1_Receipt :=
  {| t1_receipt_prog := st.(t1_prog);
     t1_receipt_partition := st.(t1_partition);
     t1_receipt_mu_total := t1_mu_total st |}.

(** [t1_emit_receipt_prog]: formal specification. *)
Lemma t1_emit_receipt_prog :
  forall st,
    t1_receipt_prog (t1_emit_receipt st) = t1_prog st.
Proof. reflexivity. Qed.

(** [t1_emit_receipt_partition]: formal specification. *)
Lemma t1_emit_receipt_partition :
(** HELPER: Accessor/projection *)
  forall st,
    t1_receipt_partition (t1_emit_receipt st) = t1_partition st.
Proof. reflexivity. Qed.

(** HELPER: Accessor/projection *)
Lemma t1_emit_receipt_mu_total :
  forall st,
    t1_receipt_mu_total (t1_emit_receipt st) = t1_mu_total st.
Proof. reflexivity. Qed.

(** HELPER: Base case property *)
Lemma t1_bootstrap_receipt_zero :
  forall prog partition,
    t1_receipt_mu_total (t1_emit_receipt (t1_bootstrap_state prog partition)) = 0%nat.
Proof.
  intros prog partition.
  rewrite t1_emit_receipt_mu_total, t1_bootstrap_total_zero.
  reflexivity.
Qed.

(**  The oracle evolves via partition updates and µ-ledger charges.  Both
     transitions expose their parameters explicitly as actions so downstream
     proofs can sequence them without duplicating the underlying arithmetic. *)
Inductive T1_Action :=
| T1Charge (delta : nat)
| T1Repartition (new_partition : Partition).

Definition t1_step (st : T1_State) (act : T1_Action) : T1_State :=
  match act with
  | T1Charge delta => t1_charge_mu st delta
  | T1Repartition new_partition => t1_repartition st new_partition
  end.

Fixpoint t1_run (st : T1_State) (actions : list T1_Action) : T1_State :=
  match actions with
  | [] => st
  | act :: rest => t1_run (t1_step st act) rest
  end.

Definition t1_action_mu_delta (st : T1_State) (act : T1_Action) : nat :=
  match act with
  | T1Charge delta => delta
  | T1Repartition new_partition =>
      partition_change_cost st.(t1_partition) new_partition
  end.

Fixpoint t1_run_mu_delta (st : T1_State) (actions : list T1_Action) : nat :=
  match actions with
  | [] => 0%nat
  | act :: rest =>
      (t1_action_mu_delta st act +
      t1_run_mu_delta (t1_step st act) rest
      )%nat
  end.

Definition t1_trace_receipt (st : T1_State) (actions : list T1_Action) : T1_Receipt :=
  t1_emit_receipt (t1_run st actions).

(** [t1_step_prog_preserved]: formal specification. *)
Lemma t1_step_prog_preserved :
  forall st act,
    t1_prog (t1_step st act) = t1_prog st.
Proof.
  intros st act.
  destruct act; simpl;
    auto using t1_charge_mu_prog_preserved,
                t1_repartition_prog_preserved.
Qed.

(** [t1_step_partition]: formal specification. *)
Lemma t1_step_partition :
  forall st act,
    t1_partition (t1_step st act) =
    match act with
    | T1Charge _ => t1_partition st
    | T1Repartition new_partition => new_partition
    end.
Proof.
(** HELPER: Accessor/projection *)
  intros st act.
  destruct act; simpl;
    auto using t1_charge_mu_partition_preserved,
                t1_repartition_partition_replaced.
Qed.

(** HELPER: Accessor/projection *)
Lemma t1_step_mu_total :
  forall st act,
    t1_mu_total (t1_step st act) =
    (t1_mu_total st + t1_action_mu_delta st act)%nat.
Proof.
  intros st act.
  destruct act; simpl;
    auto using t1_charge_mu_total,
                t1_repartition_total.
Qed.

(** [t1_run_prog_preserved]: formal specification. *)
Lemma t1_run_prog_preserved :
  forall st actions,
    t1_prog (t1_run st actions) = t1_prog st.
Proof.
  intros st actions. revert st.
  induction actions as [|act rest IH]; intros st; simpl.
  - reflexivity.
  - specialize (IH (t1_step st act)). simpl in IH.
    rewrite IH, t1_step_prog_preserved. reflexivity.
Qed.

(** [t1_run_partition_after]: formal specification. *)
Lemma t1_run_partition_after :
  forall st actions,
    t1_partition (t1_run st actions) =
    fold_left (fun current act =>
                 match act with
                 | T1Charge _ => current
                 | T1Repartition new_partition => new_partition
                 end)
              actions (t1_partition st).
Proof.
  intros st actions. revert st.
(** HELPER: Accessor/projection *)
  induction actions as [|act rest IH]; intros st; simpl.
  - reflexivity.
  - specialize (IH (t1_step st act)). simpl in IH.
    rewrite IH, t1_step_partition.
    destruct act; simpl; reflexivity.
Qed.

(** HELPER: Accessor/projection *)
Lemma t1_run_mu_total :
  forall st actions,
    t1_mu_total (t1_run st actions) =
    (t1_mu_total st + t1_run_mu_delta st actions)%nat.
(** HELPER: Accessor/projection *)
Proof.
  intros st actions. revert st.
  induction actions as [|act rest IH]; intros st; simpl.
  - lia.
  - specialize (IH (t1_step st act)). simpl in IH.
    rewrite IH, t1_step_mu_total. lia.
Qed.

(** HELPER: Accessor/projection *)
Lemma t1_emit_receipt_mu_total_run :
  forall st actions,
    t1_receipt_mu_total (t1_emit_receipt (t1_run st actions)) =
    (t1_mu_total st + t1_run_mu_delta st actions)%nat.
Proof.
  intros st actions.
  rewrite t1_emit_receipt_mu_total, t1_run_mu_total.
  reflexivity.
Qed.

(** [t1_trace_receipt_prog]: formal specification. *)
Lemma t1_trace_receipt_prog :
  forall st actions,
    t1_receipt_prog (t1_trace_receipt st actions) = t1_prog st.
Proof.
  intros st actions. unfold t1_trace_receipt.
  rewrite t1_emit_receipt_prog, t1_run_prog_preserved.
  reflexivity.
Qed.

(** [t1_trace_receipt_partition]: formal specification. *)
Lemma t1_trace_receipt_partition :
  forall st actions,
    t1_receipt_partition (t1_trace_receipt st actions) =
    fold_left (fun current act =>
                 match act with
                 | T1Charge _ => current
(** HELPER: Accessor/projection *)
                 | T1Repartition new_partition => new_partition
                 end)
              actions (t1_partition st).
Proof.
  intros st actions. unfold t1_trace_receipt.
  rewrite t1_emit_receipt_partition, t1_run_partition_after.
  reflexivity.
Qed.

(** HELPER: Accessor/projection *)
Lemma t1_trace_receipt_mu_total :
  forall st actions,
    t1_receipt_mu_total (t1_trace_receipt st actions) =
    (t1_mu_total st + t1_run_mu_delta st actions)%nat.
Proof.
  intros st actions. unfold t1_trace_receipt.
  apply t1_emit_receipt_mu_total_run.
Qed.

(**  Any concrete execution trace that runs the emitted witness program
     and proves the µ-bound immediately instantiates a
     [T1_ReceiptWitness].  This lemma packages the replay and µ-accounting
     facts required by [T_0] so oracle callers can reuse them without
     rebuilding the bookkeeping arguments. *)
Lemma t1_receipt_witness_of_exec :
  forall receipt s0 tr,
    Exec receipt.(t1_receipt_prog) s0 tr ->
    Z.le (sum_bits (receipts_of s0 tr)) (Z.of_nat receipt.(t1_receipt_mu_total)) ->
    T1_ReceiptWitness receipt.
Proof.
  intros receipt s0 tr Hexec Hmu.
  refine ({| t1_receipt_witness_state0 := s0;
            t1_receipt_witness_trace := tr;
            t1_receipt_witness_exec := Hexec;
            t1_receipt_witness_replay := _;
            t1_receipt_witness_mu_bound := Hmu |}).
  apply replay_of_exec. exact Hexec.
Qed.

(**  Oracle action traces often come with a separate execution witness.
     The following corollary packages that witness together with the µ-bound
     accumulated along the trace, yielding a ready-to-use
     [T1_ReceiptWitness] for the receipt returned by [t1_trace_receipt]. *)
Lemma t1_trace_receipt_witness :
  forall st actions s0 tr,
    Exec (t1_prog st) s0 tr ->
    Z.le (sum_bits (receipts_of s0 tr))
         (Z.of_nat (t1_mu_total st + t1_run_mu_delta st actions)) ->
    T1_ReceiptWitness (t1_trace_receipt st actions).
Proof.
  intros st actions s0 tr Hexec Hmu.
  apply (t1_receipt_witness_of_exec (t1_trace_receipt st actions) s0 tr).
  - rewrite t1_trace_receipt_prog. exact Hexec.
  - rewrite t1_trace_receipt_mu_total. exact Hmu.
Qed.

(**  The canonical closed-state execution from [ThieleProc] supplies a
     concrete [Exec] witness for every compiled program, so oracle traces can
     immediately reuse it when instantiating [T1_ReceiptWitness]. *)
Lemma t1_prog_closed_trace_exec :
  forall st,
    Exec (t1_prog st) closed_state (trace_of_prog (t1_prog st)).
Proof.
  intro st. apply closed_trace_exec.
Qed.

(** [t1_closed_trace_sum_bits_le_sum_mu]: formal specification. *)
Lemma t1_closed_trace_sum_bits_le_sum_mu :
  forall st,
    Z.le (sum_bits (receipts_of closed_state (trace_of_prog (t1_prog st))))
         (sum_mu_exec (trace_of_prog (t1_prog st))).
Proof.
  intro st.
  pose proof (t1_prog_closed_trace_exec st) as Hexec.
  exact (mu_pays_bits_exec (t1_prog st)
                           closed_state
                           (trace_of_prog (t1_prog st))
                           Hexec).
Qed.

(** [t1_trace_receipt_closed_witness_from_bits]: formal specification. *)
Lemma t1_trace_receipt_closed_witness_from_bits :
  forall st actions,
    Z.le (sum_bits (receipts_of closed_state (trace_of_prog (t1_prog st))))
         (Z.of_nat (t1_mu_total st + t1_run_mu_delta st actions)) ->
    T1_ReceiptWitness (t1_trace_receipt st actions).
Proof.
  intros st actions Hbound.
  apply t1_trace_receipt_witness with
      (s0 := closed_state)
      (tr := trace_of_prog (t1_prog st)).
  - apply t1_prog_closed_trace_exec.
  - exact Hbound.
Qed.

(** [t1_trace_receipt_closed_witness_from_mu]: formal specification. *)
Lemma t1_trace_receipt_closed_witness_from_mu :
  forall st actions,
    Z.le (sum_mu_exec (trace_of_prog (t1_prog st)))
         (Z.of_nat (t1_mu_total st + t1_run_mu_delta st actions)) ->
    T1_ReceiptWitness (t1_trace_receipt st actions).
Proof.
  intros st actions Hmu.
  apply t1_trace_receipt_closed_witness_from_bits.
  eapply Z.le_trans.
  - apply t1_closed_trace_sum_bits_le_sum_mu.
  - exact Hmu.
Qed.

(**  Converting µ-bounds from [Z] to [nat]. *)

Fixpoint sum_instr_certificates (instrs : list Instr) : nat :=
  match instrs with
  | [] => 0%nat
  | instr :: tl => instr.(instr_cert) + sum_instr_certificates tl
  end.

Definition prog_closed_trace_mu_requirement (prog : Prog) : nat :=
  sum_instr_certificates prog.(code).

Definition t1_closed_trace_mu_requirement (st : T1_State) : nat :=
  prog_closed_trace_mu_requirement st.(t1_prog).

(** [sum_mu_exec_closed_trace_nat]: formal specification. *)
Lemma sum_mu_exec_closed_trace_nat :
  forall (instrs : list Instr),
    forall start_pc : nat,
      sum_mu_exec (closed_trace start_pc instrs)
      = Z.of_nat (sum_instr_certificates instrs).
Proof.
  induction instrs as [|instr tl IH]; intros start_pc; simpl.
  - reflexivity.
  - simpl. rewrite IH.
    simpl.
    rewrite Nat2Z.inj_add.
    reflexivity.
Qed.

(** [trace_of_prog_sum_mu_nat]: formal specification. *)
Lemma trace_of_prog_sum_mu_nat :
  forall prog,
    sum_mu_exec (trace_of_prog prog)
    = Z.of_nat (prog_closed_trace_mu_requirement prog).
Proof.
  intro prog. unfold trace_of_prog, prog_closed_trace_mu_requirement.
  apply sum_mu_exec_closed_trace_nat.
Qed.

(** [t1_closed_trace_sum_mu_nat]: formal specification. *)
Lemma t1_closed_trace_sum_mu_nat :
  forall st,
    sum_mu_exec (trace_of_prog (t1_prog st))
    = Z.of_nat (t1_closed_trace_mu_requirement st).
Proof.
  intro st. unfold t1_closed_trace_mu_requirement.
  apply trace_of_prog_sum_mu_nat.
Qed.

(** [t1_trace_receipt_closed_witness_from_ledger_nat]: formal specification. *)
Lemma t1_trace_receipt_closed_witness_from_ledger_nat :
  forall st actions,
    (t1_closed_trace_mu_requirement st
     <= t1_mu_total st + t1_run_mu_delta st actions)%nat ->
    T1_ReceiptWitness (t1_trace_receipt st actions).
Proof.
  intros st actions Hnat.
    apply t1_trace_receipt_closed_witness_from_mu.
    rewrite t1_closed_trace_sum_mu_nat.
    apply -> Nat2Z.inj_le.
    exact Hnat.
  Qed.

(**  Canonical µ-charging action sequences.  Charging the certificate of each
     instruction in program order guarantees that the oracle ledger dominates
     the closed-trace µ-requirement, which is precisely the bound needed to
     instantiate [T1_ReceiptWitness]es via
     [t1_trace_receipt_closed_witness_from_ledger_nat]. *)

Definition t1_closed_trace_mu_actions (st : T1_State) : list T1_Action :=
  map T1Charge (map instr_cert (t1_prog st).(code)).

(** [t1_run_mu_delta_all_charge]: formal specification. *)
Lemma t1_run_mu_delta_all_charge :
  forall st charges,
    t1_run_mu_delta st (map T1Charge charges) = ledger_sum charges.
Proof.
  intros st charges. revert st.
  induction charges as [|delta rest IH]; intros st; simpl.
  - reflexivity.
  - specialize (IH (t1_step st (T1Charge delta))).
    simpl in IH.
    rewrite IH. reflexivity.
Qed.

(** [ledger_sum_map_instr_cert]: formal specification. *)
Lemma ledger_sum_map_instr_cert :
  forall instrs,
    ledger_sum (map instr_cert instrs) = sum_instr_certificates instrs.
Proof.
  induction instrs as [|instr rest IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** [t1_run_mu_delta_closed_trace_mu_actions]: formal specification. *)
Lemma t1_run_mu_delta_closed_trace_mu_actions :
  forall st,
    t1_run_mu_delta st (t1_closed_trace_mu_actions st)
    = t1_closed_trace_mu_requirement st.
Proof.
  intro st.
  unfold t1_closed_trace_mu_actions, t1_closed_trace_mu_requirement.
  rewrite t1_run_mu_delta_all_charge.
  apply ledger_sum_map_instr_cert.
Qed.

(** [t1_closed_trace_mu_requirement_covered_by_canonical_actions]: formal specification. *)
Lemma t1_closed_trace_mu_requirement_covered_by_canonical_actions :
  forall st,
    (t1_closed_trace_mu_requirement st
     <= t1_mu_total st
        + t1_run_mu_delta st (t1_closed_trace_mu_actions st))%nat.
Proof.
  intro st.
  rewrite t1_run_mu_delta_closed_trace_mu_actions.
  lia.
Qed.

(** [t1_trace_receipt_closed_witness_canonical]: formal specification. *)
Lemma t1_trace_receipt_closed_witness_canonical :
  forall st,
    T1_ReceiptWitness (t1_trace_receipt st (t1_closed_trace_mu_actions st)).
Proof.
  intro st.
  apply t1_trace_receipt_closed_witness_from_ledger_nat.
  apply t1_closed_trace_mu_requirement_covered_by_canonical_actions.
Qed.
