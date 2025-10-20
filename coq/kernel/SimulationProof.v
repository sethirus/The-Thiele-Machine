From Coq Require Import List Bool Arith.PeanoNat.
From Coq Require Import Strings.String.
Import ListNotations.

Require Import Kernel.Kernel.
Require Import Kernel.KernelTM.
Require Import Kernel.KernelThiele.
Require Import Kernel.VMState.
Require Import Kernel.VMStep.

(** * Simulation between the Python VM semantics and the kernel machine *)

Definition states_related (s_vm : VMState) (s_kernel : state) : Prop :=
  s_vm.(vm_pc) = s_kernel.(tm_state) /\
  s_vm.(vm_mu) = s_kernel.(mu_cost).

Definition compile_instruction (instr : vm_instruction) : instruction :=
  H_ClaimTapeIsZero (instruction_cost instr).

Definition compile_trace (trace : list vm_instruction) : program :=
  map compile_instruction trace.

Lemma compile_trace_nth :
  forall trace pc instr,
    nth_error trace pc = Some instr ->
    nth_error (compile_trace trace) pc = Some (compile_instruction instr).
Proof.
  intros trace pc instr Hnth.
  unfold compile_trace, compile_instruction.
  rewrite List.nth_error_map, Hnth.
  reflexivity.
Qed.

Definition vm_apply (s : VMState) (instr : vm_instruction) : VMState :=
  match instr with
  | instr_pnew region cost =>
      let '(graph', _) := graph_pnew s.(vm_graph) region in
      advance_state s (instr_pnew region cost) graph' s.(vm_csrs) s.(vm_err)
  | instr_psplit module left_region right_region cost =>
      match graph_psplit s.(vm_graph) module left_region right_region with
      | Some (graph', _, _) =>
          advance_state s (instr_psplit module left_region right_region cost)
            graph' s.(vm_csrs) s.(vm_err)
      | None =>
          advance_state s (instr_psplit module left_region right_region cost)
            s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)
      end
  | instr_pmerge m1 m2 cost =>
      match graph_pmerge s.(vm_graph) m1 m2 with
      | Some (graph', _) =>
          advance_state s (instr_pmerge m1 m2 cost) graph' s.(vm_csrs) s.(vm_err)
      | None =>
          advance_state s (instr_pmerge m1 m2 cost)
            s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)
      end
  | instr_lassert module formula cost =>
      if z3_oracle formula then
        let graph' := graph_add_axiom s.(vm_graph) module formula in
        let csrs' := csr_set_err (csr_set_status s.(vm_csrs) 1) 0 in
        advance_state s (instr_lassert module formula cost)
          graph' (csr_set_cert_addr csrs' (ascii_checksum formula)) s.(vm_err)
      else
        advance_state s (instr_lassert module formula cost)
          s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)
  | instr_ljoin cert1 cert2 cost =>
      if String.eqb cert1 cert2 then
        let csrs' := csr_set_err s.(vm_csrs) 0 in
        advance_state s (instr_ljoin cert1 cert2 cost)
          s.(vm_graph)
          (csr_set_cert_addr csrs' (ascii_checksum (String.append cert1 cert2)))
          s.(vm_err)
      else
        let csrs' := csr_set_err s.(vm_csrs) 1 in
        advance_state s (instr_ljoin cert1 cert2 cost)
          s.(vm_graph)
          (csr_set_cert_addr csrs' (ascii_checksum (String.append cert1 cert2)))
          (latch_err s true)
  | instr_mdlacc module cost =>
      advance_state s (instr_mdlacc module cost) s.(vm_graph) s.(vm_csrs) s.(vm_err)
  | instr_emit module payload cost =>
      let csrs' := csr_set_cert_addr s.(vm_csrs) (ascii_checksum payload) in
      advance_state s (instr_emit module payload cost) s.(vm_graph) csrs' s.(vm_err)
  | instr_pdiscover module evidence cost =>
      let graph' := graph_record_discovery s.(vm_graph) module evidence in
      advance_state s (instr_pdiscover module evidence cost) graph' s.(vm_csrs) s.(vm_err)
  | instr_pyexec payload cost =>
      advance_state s (instr_pyexec payload cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)
  end.

Fixpoint run_vm (fuel : nat) (trace : list vm_instruction) (s : VMState)
  : VMState :=
  match fuel with
  | 0 => s
  | S fuel' =>
      match nth_error trace s.(vm_pc) with
      | Some instr => run_vm fuel' trace (vm_apply s instr)
      | None => s
      end
  end.

Inductive vm_exec : nat -> list vm_instruction -> VMState -> VMState -> Prop :=
| vm_exec_zero : forall trace s,
    vm_exec 0 trace s s
| vm_exec_step : forall fuel trace s instr s' s'',
    nth_error trace s.(vm_pc) = Some instr ->
    vm_step s instr s' ->
    vm_exec fuel trace s' s'' ->
    vm_exec (S fuel) trace s s''.

Lemma vm_step_vm_apply :
  forall s instr s',
    vm_step s instr s' ->
    vm_apply s instr = s'.
Proof.
  intros s instr s' Hstep.
  inversion Hstep; subst; simpl;
    repeat match goal with
           | H : _ = _ |- _ => rewrite H
           end; reflexivity.
Qed.

Lemma vm_step_deterministic :
  forall s instr s1 s2,
    vm_step s instr s1 ->
    vm_step s instr s2 ->
    s1 = s2.
Proof.
  intros s instr s1 s2 Hstep1 Hstep2.
  rewrite <- (vm_step_vm_apply _ _ _ Hstep1).
  rewrite <- (vm_step_vm_apply _ _ _ Hstep2).
  reflexivity.
Qed.

Lemma vm_step_pc :
  forall s instr s',
    vm_step s instr s' ->
    s'.(vm_pc) = S s.(vm_pc).
Proof.
  intros s instr s' Hstep.
  inversion Hstep; subst; reflexivity.
Qed.

Lemma vm_step_mu :
  forall s instr s',
    vm_step s instr s' ->
    s'.(vm_mu) = s.(vm_mu) + instruction_cost instr.
Proof.
  intros s instr s' Hstep.
  inversion Hstep; subst; reflexivity.
Qed.

Lemma vm_exec_run_vm :
  forall fuel trace s s',
    vm_exec fuel trace s s' ->
    run_vm fuel trace s = s'.
Proof.
  intros fuel trace s s' Hexec.
  induction Hexec as [| fuel trace s instr s'' s''' Hnth Hstep Hexec IH].
  - reflexivity.
  - simpl.
    rewrite Hnth.
    rewrite (vm_step_vm_apply _ _ _ Hstep).
    exact IH.
Qed.

Lemma vm_exec_deterministic :
  forall fuel trace s s1 s2,
    vm_exec fuel trace s s1 ->
    vm_exec fuel trace s s2 ->
    s1 = s2.
Proof.
  intros fuel trace s s1 s2 Hexec1 Hexec2.
  rewrite <- (vm_exec_run_vm _ _ _ _ Hexec1).
  rewrite <- (vm_exec_run_vm _ _ _ _ Hexec2).
  reflexivity.
Qed.

Lemma step_thiele_hclaim_tm_state :
  forall prog st delta,
    fetch prog st = H_ClaimTapeIsZero delta ->
    (step_thiele prog st).(tm_state) = S st.(tm_state).
Proof.
  intros prog st delta Hfetch.
  unfold step_thiele.
  rewrite Hfetch.
  reflexivity.
Qed.

Lemma step_thiele_hclaim_mu :
  forall prog st delta,
    fetch prog st = H_ClaimTapeIsZero delta ->
    (step_thiele prog st).(mu_cost) = st.(mu_cost) + delta.
Proof.
  intros prog st delta Hfetch.
  unfold step_thiele.
  rewrite Hfetch.
  reflexivity.
Qed.

Lemma fetch_compile_trace :
  forall trace s_vm s_kernel instr,
    states_related s_vm s_kernel ->
    nth_error trace s_vm.(vm_pc) = Some instr ->
    fetch (compile_trace trace) s_kernel
    = compile_instruction instr.
Proof.
  intros trace s_vm s_kernel instr [Hpc Hmu] Hnth.
  unfold fetch.
  rewrite <- Hpc.
  rewrite (compile_trace_nth trace s_vm.(vm_pc) instr Hnth).
  reflexivity.
Qed.

Lemma vm_step_kernel_simulation :
  forall trace s_vm s_kernel instr s_vm',
    states_related s_vm s_kernel ->
    nth_error trace s_vm.(vm_pc) = Some instr ->
    vm_step s_vm instr s_vm' ->
    states_related s_vm' (step_thiele (compile_trace trace) s_kernel).
Proof.
  intros trace s_vm s_kernel instr s_vm' Hrel Hnth Hstep.
  destruct Hrel as [Hpc Hmu].
  pose proof (fetch_compile_trace trace s_vm s_kernel instr (conj Hpc Hmu) Hnth) as Hfetch.
  split.
  - rewrite (vm_step_pc _ _ _ Hstep).
    rewrite Hpc.
    symmetry.
    eapply step_thiele_hclaim_tm_state with (delta := instruction_cost instr).
    rewrite Hfetch.
    reflexivity.
  - rewrite (vm_step_mu _ _ _ Hstep).
    rewrite Hmu.
    symmetry.
    eapply step_thiele_hclaim_mu with (delta := instruction_cost instr).
    rewrite Hfetch.
    reflexivity.
Qed.

Lemma run_thiele_unfold :
  forall fuel prog st,
    run_thiele (S fuel) prog st =
    match fetch prog st with
    | T_Halt => st
    | _ => run_thiele fuel prog (step_thiele prog st)
    end.
Proof.
  intros fuel prog st.
  reflexivity.
Qed.

Lemma vm_exec_simulation :
  forall fuel trace s_vm s_kernel s_vm',
    states_related s_vm s_kernel ->
    vm_exec fuel trace s_vm s_vm' ->
    exists s_kernel',
      run_thiele fuel (compile_trace trace) s_kernel = s_kernel' /\
      states_related s_vm' s_kernel'.
Proof.
  intros fuel trace s_vm s_kernel s_vm' Hrel Hexec.
  revert s_kernel Hrel.
  induction Hexec as [| fuel trace s instr s' s'' Hnth Hstep Hexec IH];
    intros s_kernel Hrel.
  - exists s_kernel. split; [reflexivity|assumption].
  - set (prog := compile_trace trace).
    pose proof (vm_step_kernel_simulation trace s s_kernel instr s' Hrel Hnth Hstep)
      as Hrel_step.
    pose proof (fetch_compile_trace trace s s_kernel instr Hrel Hnth)
      as Hfetch.
    specialize (IH (step_thiele prog s_kernel) Hrel_step).
    destruct IH as [s_kernel' [Hrun Hrel_final]].
    exists s_kernel'.
    split.
    + subst prog.
      rewrite run_thiele_unfold.
      rewrite Hfetch.
      exact Hrun.
    + exact Hrel_final.
Qed.

Theorem vm_is_a_correct_refinement_of_kernel :
  forall fuel trace s_vm s_kernel s_vm',
    states_related s_vm s_kernel ->
    vm_exec fuel trace s_vm s_vm' ->
    exists final_kernel,
      run_vm fuel trace s_vm = s_vm' /\
      run_thiele fuel (compile_trace trace) s_kernel = final_kernel /\
      states_related s_vm' final_kernel.
Proof.
  intros fuel trace s_vm s_kernel s_vm' Hrel Hexec.
  pose proof (vm_exec_run_vm fuel trace s_vm s_vm' Hexec) as Hrun_vm.
  pose proof (vm_exec_simulation fuel trace s_vm s_kernel s_vm' Hrel Hexec)
    as [final_kernel [Hrun_kernel Hrel_final]].
  exists final_kernel.
  split; [assumption|].
  split; assumption.
Qed.
