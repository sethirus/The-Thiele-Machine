(** Internal counter-dependent control under the unchanged PC-indexed runner.
    No scratch register or memory is used. The trap trampoline is executable
    VM code, and the error latch is retained rather than cleared or ignored in
    the state relation. Programs in this abstract contract contain address 3840;
    this is not a claim about the finite RTL instruction memory. *)
From Coq Require Import List Bool Arith Lia Strings.String.
From Kernel Require Import VMState VMStep SimulationProof VMUnboundedCounterAccess.
Import ListNotations.

Definition counter_branch_result (s : VMState) (target : nat) (equal : bool) : VMState :=
 {| vm_graph := s.(vm_graph);
    vm_csrs := if equal then s.(vm_csrs) else csr_set_err s.(vm_csrs) 1;
    vm_regs := s.(vm_regs); vm_mem := s.(vm_mem); vm_pc := target;
    vm_mu := s.(vm_mu) + 1; vm_mu_tensor := s.(vm_mu_tensor);
    vm_err := if equal then s.(vm_err) else true;
    vm_logic_acc := s.(vm_logic_acc); vm_mstatus := s.(vm_mstatus);
    vm_witness := s.(vm_witness); vm_certified := s.(vm_certified) |}.

Theorem counter_branch_correct : forall p s u v yes no,
 vm_witness s = counter_witness u v ->
 nth_error p (vm_pc s) = Some (instr_chsh_lassert 0) ->
 nth_error p (S (vm_pc s)) = Some (instr_jump yes 0) ->
 nth_error p LASSERT_TRAP_PC = Some (instr_jump no 0) ->
 run_vm 2 p s = counter_branch_result s (if Nat.eqb u v then yes else no) (Nat.eqb u v).
Proof.
 intros p s u v yes no Hw Hguard Hyes Hno.
 cbn [run_vm]. rewrite Hguard. cbn [vm_apply]. rewrite Hw.
 destruct (column_contractive_check_witness (counter_witness u v)) eqn:Hcheck.
 - apply witness_counter_equality_test in Hcheck. subst v. rewrite Nat.eqb_refl.
   cbn [vm_pc]. rewrite Hyes. cbn [vm_apply run_vm].
   unfold counter_branch_result, jump_state, apply_cost; cbn.
   rewrite Nat.add_0_r, Hw. reflexivity.
 - assert (Hne : u <> v).
   { intro H; apply witness_counter_equality_test in H. congruence. }
   apply Nat.eqb_neq in Hne. rewrite Hne.
   cbn [vm_pc]. rewrite Hno. cbn [vm_apply run_vm].
   unfold counter_branch_result, jump_state, apply_cost; cbn.
   rewrite Nat.add_0_r, Hw. reflexivity.
Qed.

Definition counter_drain_program : list vm_instruction :=
 [instr_chsh_lassert 0; instr_jump 3841 0;
  instr_chsh_trial 0 0 0 1 0; instr_jump 0 0] ++
 repeat (instr_checkpoint "" 0) (LASSERT_TRAP_PC - 4) ++ [instr_jump 2 0].

Lemma counter_drain_fetch :
 nth_error counter_drain_program 0 = Some (instr_chsh_lassert 0) /\
 nth_error counter_drain_program 1 = Some (instr_jump 3841 0) /\
 nth_error counter_drain_program 2 = Some (instr_chsh_trial 0 0 0 1 0) /\
 nth_error counter_drain_program 3 = Some (instr_jump 0 0) /\
 nth_error counter_drain_program LASSERT_TRAP_PC = Some (instr_jump 2 0).
Proof. vm_compute; repeat split; reflexivity. Qed.

Lemma run_vm_split_fuel : forall a b p s,
 run_vm (a+b) p s = run_vm b p (run_vm a p s).
Proof.
 induction a as [|a IH]; intros b p s; [reflexivity|].
 cbn [Nat.add run_vm]. destruct (nth_error p (vm_pc s)) eqn:E.
 - apply IH.
 - destruct b; [reflexivity|]. cbn [run_vm]. rewrite E. reflexivity.
Qed.

Definition counter_iteration_result (s : VMState) (u v : nat) : VMState :=
 {| vm_graph := s.(vm_graph); vm_csrs := csr_set_err s.(vm_csrs) 1;
    vm_regs := s.(vm_regs); vm_mem := s.(vm_mem); vm_pc := 0;
    vm_mu := s.(vm_mu) + 1; vm_mu_tensor := s.(vm_mu_tensor); vm_err := true;
    vm_logic_acc := s.(vm_logic_acc); vm_mstatus := s.(vm_mstatus);
    vm_witness := counter_witness u (S v); vm_certified := s.(vm_certified) |}.

Theorem counter_drain_iteration : forall s u v,
 vm_pc s = 0 -> vm_witness s = counter_witness u v -> u <> v ->
 run_vm 4 counter_drain_program s = counter_iteration_result s u v.
Proof.
 intros s u v Hpc Hw Hne.
 destruct counter_drain_fetch as [H0 [H1 [H2 [H3 Htrap]]]].
 replace 4 with (2+2) by reflexivity. rewrite run_vm_split_fuel.
 rewrite (counter_branch_correct _ s u v 3841 2 Hw).
 2: rewrite Hpc; exact H0.
 2: rewrite Hpc; exact H1.
 2: exact Htrap.
 apply Nat.eqb_neq in Hne. rewrite Hne.
 cbn [run_vm counter_branch_result vm_pc]. rewrite H2.
 cbn [vm_apply].
 assert (Hbits : chsh_bits_ok 0 0 0 1 = true) by reflexivity.
 rewrite Hbits. cbn [vm_pc counter_branch_result]. rewrite H3. cbn [vm_apply].
 unfold counter_branch_result, counter_iteration_result, jump_state, apply_cost.
 cbn. rewrite Hw. rewrite !Nat.add_0_r. reflexivity.
Qed.

Theorem counter_drain_exit : forall s u,
 vm_pc s = 0 -> vm_witness s = counter_witness u u ->
 run_vm 2 counter_drain_program s = counter_branch_result s 3841 true.
Proof.
 intros s u Hpc Hw.
 destruct counter_drain_fetch as [H0 [H1 [H2 [H3 Htrap]]]].
 rewrite (counter_branch_correct _ s u u 3841 2 Hw).
 - rewrite Nat.eqb_refl. reflexivity.
 - rewrite Hpc; exact H0.
 - rewrite Hpc; exact H1.
 - exact Htrap.
Qed.

(** Ghost result of n internally executed unequal rounds; not an evaluator
    used to choose instructions. The running program is always the same list. *)
Fixpoint counter_rounds (s : VMState) (u v n : nat) : VMState :=
 match n with
 | 0 => s
 | S k => counter_rounds (counter_iteration_result s u v) u (S v) k
 end.

Lemma counter_drain_by_difference : forall d s u v,
 vm_pc s = 0 -> vm_witness s = counter_witness u v -> u = v+d ->
 run_vm (4*d+2) counter_drain_program s =
 counter_branch_result (counter_rounds s u v d) 3841 true.
Proof.
 induction d as [|d IH]; intros s u v Hpc Hw Hdiff.
 - cbn [Nat.mul Nat.add counter_rounds].
   replace v with u in Hw by lia. apply (counter_drain_exit s u); assumption.
 - replace (4*S d+2) with (4+(4*d+2)) by lia.
   rewrite run_vm_split_fuel.
   rewrite (counter_drain_iteration s u v Hpc Hw) by lia.
   cbn [counter_rounds]. apply IH; cbn [counter_iteration_result vm_pc vm_witness]; try reflexivity; lia.
Qed.

Theorem counter_drain_correct : forall s u v,
 vm_pc s = 0 -> vm_witness s = counter_witness u v -> v <= u ->
 run_vm (4*(u-v)+2) counter_drain_program s =
 counter_branch_result (counter_rounds s u v (u-v)) 3841 true.
Proof.
 intros s u v Hpc Hw Hle. apply counter_drain_by_difference; try assumption; lia.
Qed.

Lemma counter_rounds_fields : forall n s u v,
 vm_witness s = counter_witness u v ->
 vm_witness (counter_rounds s u v n) = counter_witness u (v+n) /\
 vm_mu (counter_rounds s u v n) = vm_mu s + n /\
 vm_err (counter_rounds s u v n) = (if Nat.eqb n 0 then vm_err s else true) /\
 vm_csrs (counter_rounds s u v n) = (if Nat.eqb n 0 then vm_csrs s else csr_set_err (vm_csrs s) 1).
Proof.
 induction n as [|n IH]; intros s u v Hw.
 - cbn [counter_rounds Nat.eqb]. rewrite !Nat.add_0_r. auto.
 - cbn [counter_rounds].
   specialize (IH (counter_iteration_result s u v) u (S v) eq_refl).
   cbn [counter_iteration_result vm_witness vm_mu vm_err vm_csrs] in IH.
   destruct IH as [Hw' [Hm [He Hc]]].
   rewrite Hw', Hm, He, Hc.
   replace (S v+n) with (v+S n) by lia.
   replace (vm_mu s+1+n) with (vm_mu s+S n) by lia.
   destruct n; cbn [Nat.eqb]; repeat split; reflexivity.
Qed.

From Kernel Require Import VMUnboundedExec MuInitiality.
Lemma counter_drain_length : List.length counter_drain_program = 3841.
Proof. vm_compute. reflexivity. Qed.

Theorem counter_drain_halts : forall s u v,
 vm_pc s = 0 -> vm_witness s = counter_witness u v -> v <= u ->
 vm_halts_at counter_drain_program s
   (counter_branch_result (counter_rounds s u v (u-v)) 3841 true).
Proof.
 intros s u v Hpc Hw Hle. exists (4*(u-v)+2). split.
 - apply counter_drain_correct; assumption.
 - unfold halted. cbn [counter_branch_result vm_pc].
   rewrite counter_drain_length. reflexivity.
Qed.

Definition counter_example_state (u v : nat) (err : bool) : VMState :=
 {| vm_graph := init_state.(vm_graph); vm_csrs := init_state.(vm_csrs);
    vm_regs := [42]; vm_mem := [13]; vm_pc := 0; vm_mu := 7;
    vm_mu_tensor := init_state.(vm_mu_tensor); vm_err := err;
    vm_logic_acc := 99; vm_mstatus := init_state.(vm_mstatus);
    vm_witness := counter_witness u v; vm_certified := true |}.

Example counter_branch_repeats_after_error :
 let s := counter_example_state 2 0 false in
 map (fun fuel => let r := run_vm fuel counter_drain_program s in
                    (vm_pc r, vm_mu r, vm_err r)) [2;4;6;8;10] =
 [(2,8,true); (0,8,true); (2,9,true); (0,9,true); (3841,10,true)].
Proof. vm_compute. reflexivity. Qed.

Example counter_equal_preserves_existing_error_and_data :
 let r := run_vm 2 counter_drain_program (counter_example_state 3 3 true) in
 (vm_pc r, vm_mu r, vm_err r, vm_regs r, vm_mem r, vm_certified r) =
 (3841,8,true,[42],[13],true).
Proof. vm_compute. reflexivity. Qed.

Example counter_unequal_reaches_equal_witness :
 vm_witness (run_vm 10 counter_drain_program (counter_example_state 2 0 false)) =
 counter_witness 2 2.
Proof. vm_compute. reflexivity. Qed.

Lemma counter_rounds_frame : forall n s u v,
 let r := counter_rounds s u v n in
 (vm_graph r, vm_regs r, vm_mem r, vm_mu_tensor r,
  vm_logic_acc r, vm_mstatus r, vm_certified r) =
 (vm_graph s, vm_regs s, vm_mem s, vm_mu_tensor s,
  vm_logic_acc s, vm_mstatus s, vm_certified s).
Proof.
 induction n as [|n IH]; intros s u v; [reflexivity|].
 cbn [counter_rounds]. rewrite IH. reflexivity.
Qed.

(** One-instruction update macros. They use no scratch and preserve the error
    and CSR states, including an already latched error. *)
Definition counter_update_result (s : VMState) (u v : nat) : VMState :=
 {| vm_graph := s.(vm_graph); vm_csrs := s.(vm_csrs);
    vm_regs := s.(vm_regs); vm_mem := s.(vm_mem); vm_pc := S s.(vm_pc);
    vm_mu := s.(vm_mu); vm_mu_tensor := s.(vm_mu_tensor); vm_err := s.(vm_err);
    vm_logic_acc := s.(vm_logic_acc); vm_mstatus := s.(vm_mstatus);
    vm_witness := counter_witness u v; vm_certified := s.(vm_certified) |}.

Theorem counter_increment_correct : forall p s u v,
 vm_witness s = counter_witness u v ->
 nth_error p (vm_pc s) = Some (instr_chsh_trial 0 0 0 0 0) ->
 run_vm 1 p s = counter_update_result s (S u) v.
Proof.
 intros p s u v Hw Hfetch. cbn [run_vm]. rewrite Hfetch.
 unfold vm_apply. cbn.
 unfold counter_update_result, apply_cost. cbn. rewrite Hw, Nat.add_0_r.
 reflexivity.
Qed.
Theorem counter_decrement_correct : forall p s u v,
 vm_witness s = counter_witness u v ->
 nth_error p (vm_pc s) = Some (instr_chsh_trial 0 0 0 1 0) ->
 run_vm 1 p s = counter_update_result s u (S v).
Proof.
 intros p s u v Hw Hfetch. cbn [run_vm]. rewrite Hfetch.
 unfold vm_apply. cbn.
 unfold counter_update_result, apply_cost. cbn. rewrite Hw, Nat.add_0_r.
 reflexivity.
Qed.
