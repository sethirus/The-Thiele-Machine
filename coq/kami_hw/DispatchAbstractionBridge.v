(** First checked actual-dispatch / [kami_step] bridge. The observation is
    explicitly limited to PC, charge, error and all sixteen data registers.
    This concrete ADD instance is not a full-snapshot or all-opcode refinement. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ActionEvaluator DispatchExecution DispatchObservation
  DispatchContracts CoreTyping ThieleTypes Abstraction.
From Kernel Require Import VMStep.
From Coq Require Import List String Arith.PeanoNat.
Import ListNotations VMStep.VMStep.
Open Scope string_scope.

Record DispatchCoreObservation := {
  core_pc : nat;
  core_mu : nat;
  core_err : bool;
  core_regs : list nat
}.

Definition snapshot_core_observation (s : KamiSnapshot) : DispatchCoreObservation :=
  {| core_pc := snap_pc s; core_mu := snap_mu s; core_err := snap_err s;
     core_regs := map (snap_regs s) (seq 0 16) |}.

Definition regs_core_observation (s : RegsT) : option DispatchCoreObservation :=
  match action_read_syntax s "pc" (Bit 32),
        action_read_syntax s "mu" (Bit 32),
        action_read_syntax s "err" Bool,
        action_read_syntax s "regs" (Vector (Bit 32) 4) with
  | Some pc, Some mu, Some err, Some regs =>
      Some {| core_pc := wordToNat pc; core_mu := wordToNat mu; core_err := err;
              core_regs := map (fun i => wordToNat (regs (natToWord 4 i))) (seq 0 16) |}
  | _, _, _, _ => None
  end.

Definition dispatch_add_snapshot : KamiSnapshot :=
  {| snap_pc := 0;
     snap_mu := 0;
     snap_err := false;
     snap_halted := false;
     snap_regs := fun i => if Nat.eqb i 1 then 7 else if Nat.eqb i 2 then 9 else 0;
     snap_mem := fun _ => 0;
     snap_partition_ops := 0;
     snap_mdl_ops := 0;
     snap_info_gain := 0;
     snap_error_code := 0;
     snap_mu_tensor := fun _ => 0;
     snap_pt_sizes := fun _ => 0;
     snap_pt_next_id := 1;
     snap_certified := false;
     snap_wc_same_00 := 0;
     snap_wc_diff_00 := 0;
     snap_wc_same_01 := 0;
     snap_wc_diff_01 := 0;
     snap_wc_same_10 := 0;
     snap_wc_diff_10 := 0;
     snap_wc_same_11 := 0;
     snap_wc_diff_11 := 0;
     snap_module_tensors := fun _ _ => 0;
     snap_rich_state := empty_rich_snapshot_state;
     snap_csr_cert_addr := 0;
     snap_csr_status := 0;
     snap_csr_err := 0;
     snap_csr_heap_base := 0;
     snap_logic_acc := 0;
     snap_mstatus := 0 |}.

Example dispatch_add_initial_observation :
  regs_core_observation dispatch_add_state =
    Some (snapshot_core_observation dispatch_add_snapshot).
Proof. vm_compute. reflexivity. Qed.

Lemma dispatch_add_post_observation : forall final,
  dispatch_add_post final ->
  regs_core_observation final = Some (snapshot_core_observation
    (kami_step dispatch_add_snapshot (instr_add 3 1 2 5))).
Proof.
  intros final [Hp [Hm [He Hr]]].
  unfold regs_core_observation, action_read_syntax.
  rewrite Hp, Hm, He, Hr. repeat rewrite kind_eq.
  vm_compute. reflexivity.
Qed.

Theorem dispatch_matches_kami_step_supported : exists u,
  regs_core_observation dispatch_add_state =
    Some (snapshot_core_observation dispatch_add_snapshot) /\
  SemAction dispatch_add_state (attrType dispatch_rule type) u (M.empty _) WO /\
  Multistep ThieleCPUCore.thieleCore dispatch_add_state
    (M.union u dispatch_add_state) [NormalizationExecution.normalization_label "step"] /\
  regs_core_observation (M.union u dispatch_add_state) =
    Some (snapshot_core_observation
      (kami_step dispatch_add_snapshot (instr_add 3 1 2 5))).
Proof.
  destruct dispatch_add_actual_execution as [u [Hs [Hx Hp]]].
  exists u. split; [exact dispatch_add_initial_observation|].
  split; [exact Hs|]. split; [exact Hx|].
  apply dispatch_add_post_observation. exact Hp.
Qed.

Lemma dispatch_add_state_typed :
  registers_match cpu_register_kind dispatch_add_state.
Proof.
  intro key. unfold register_kind, cpu_register_kind, dispatch_add_state,
    dispatch_loaded_reset.
  destruct (string_dec key "regs") as [Hr|Hr].
  - subst. rewrite M.find_add_1. vm_compute. reflexivity.
  - rewrite M.find_add_2 by exact Hr.
    destruct (string_dec key "imem") as [Hi|Hi].
    + subst. rewrite M.find_add_1. vm_compute. reflexivity.
    + rewrite M.find_add_2 by exact Hi. reflexivity.
Qed.

Theorem dispatch_preserves_register_schema : forall old u,
  registers_match cpu_register_kind old ->
  eval_dispatch old = Some u ->
  registers_match cpu_register_kind (M.union u old).
Proof.
  intros old u Htyped He. apply update_preserves_registers; [exact Htyped|].
  pose proof cpu_writes_declared as Hd.
  rewrite Forall_forall in Hd. specialize (Hd dispatch_rule dispatch_rule_in).
  pose proof (proj1 (dispatch_actual_action_iff old u) He) as Hs.
  destruct (eval_linear_action_complete _ _ _ _ _ _ dispatch_rule_linear Hs)
    as [Hr _].
  eapply evaluated_updates_match; [exact Hd|exact Hr].
Qed.

Theorem dispatch_add_typed_refinement : exists u,
  registers_match cpu_register_kind dispatch_add_state /\
  registers_match cpu_register_kind (M.union u dispatch_add_state) /\
  regs_core_observation dispatch_add_state =
    Some (snapshot_core_observation dispatch_add_snapshot) /\
  SemAction dispatch_add_state (attrType dispatch_rule type) u (M.empty _) WO /\
  Multistep ThieleCPUCore.thieleCore dispatch_add_state
    (M.union u dispatch_add_state) [NormalizationExecution.normalization_label "step"] /\
  regs_core_observation (M.union u dispatch_add_state) =
    Some (snapshot_core_observation
      (kami_step dispatch_add_snapshot (instr_add 3 1 2 5))).
Proof.
  destruct dispatch_matches_kami_step_supported as [u [Hi [Hs [Hx Ho]]]].
  exists u. split; [exact dispatch_add_state_typed|].
  split.
  - apply dispatch_preserves_register_schema; [exact dispatch_add_state_typed|].
    apply dispatch_actual_action_iff. exact Hs.
  - exact (conj Hi (conj Hs (conj Hx Ho))).
Qed.
