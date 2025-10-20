From Coq Require Import List Bool Arith.PeanoNat.
Import ListNotations.

Require Import Kernel.Kernel.
Require Import Kernel.KernelTM.
Require Import Kernel.KernelThiele.

(** * Formal bridge between the Python VM and the kernel interpreter *)

(** The Python implementation executes a richer instruction set than the
    minimalist kernel.  For the purposes of the simulation proof we abstract
    each opcode to the amount of non-classical reasoning it performs and
    whether it raises an error flag.  The classical bookkeeping (module tables,
    certificates, etc.) is left implicit—only the program counter, μ-ledger,
    and error bit participate in the Coq model. *)

Inductive vm_opcode : Type :=
| VM_PNEW
| VM_PSPLIT
| VM_PMERGE
| VM_LASSERT
| VM_LJOIN
| VM_MDLACC
| VM_EMIT
| VM_PDISCOVER
| VM_PYEXEC.

Record vm_instruction : Type := {
  vm_op : vm_opcode;
  vm_mu_delta : nat;
  vm_sets_err : bool
}.

Record vm_state : Type := {
  vm_pc : nat;
  vm_mu : nat;
  vm_err : bool
}.

Definition vm_fetch (prog : list vm_instruction) (st : vm_state)
  : option vm_instruction :=
  nth_error prog st.(vm_pc).

Definition vm_step (instr : vm_instruction) (st : vm_state) : vm_state :=
  {| vm_pc := S st.(vm_pc);
     vm_mu := st.(vm_mu) + instr.(vm_mu_delta);
     vm_err := orb st.(vm_err) instr.(vm_sets_err) |}.

Fixpoint run_vm (fuel : nat) (prog : list vm_instruction) (st : vm_state)
  : vm_state :=
  match fuel with
  | 0 => st
  | S fuel' =>
      if st.(vm_err)
      then st
      else match vm_fetch prog st with
           | None => st
           | Some instr => run_vm fuel' prog (vm_step instr st)
           end
  end.

(** The kernel interpreter already exposes a tape/head state.  We embed the
    VM state into it by reusing the program counter as [tm_state] and the μ
    ledger as [mu_cost].  The tape contains a single distinguished cell that is
    always zero, ensuring that the [H_ClaimTapeIsZero] action is idempotent. *)

Definition encode_state (st : vm_state) : state :=
  {| tape := repeat false 1;
     head := 0;
     tm_state := st.(vm_pc);
     mu_cost := st.(vm_mu) |}.

Definition decode_state (st : state) : vm_state :=
  {| vm_pc := st.(tm_state);
     vm_mu := st.(mu_cost);
     vm_err := false |}.

Definition compile_instruction (instr : vm_instruction) : instruction :=
  H_ClaimTapeIsZero instr.(vm_mu_delta).

Definition compile_program (prog : list vm_instruction) : program :=
  map compile_instruction prog.

Definition err_free (prog : list vm_instruction) : Prop :=
  Forall (fun instr => instr.(vm_sets_err) = false) prog.

Lemma decode_encode_state_id :
  forall st,
    st.(vm_err) = false ->
    decode_state (encode_state st) = st.
Proof.
  intros [pc mu err] Herr.
  simpl in Herr.
  subst err.
  reflexivity.
Qed.

Lemma Forall_nth_error_vm
  {A : Type} {P : A -> Prop} {l : list A} :
  Forall P l ->
  forall n x,
    nth_error l n = Some x ->
    P x.
Proof.
  intros H.
  induction H as [|y ys Hy Hys IH]; intros n x Hnth; simpl in *.
  - destruct n; inversion Hnth.
  - destruct n as [|n']; simpl in Hnth.
    + inversion Hnth; subst; assumption.
    + apply (IH n' x); assumption.
Qed.

Lemma claim_tape_zero_repeat_false :
  forall n, claim_tape_zero (repeat false n) = repeat false n.
Proof.
  intros n.
  unfold claim_tape_zero.
  rewrite repeat_length.
  reflexivity.
Qed.

Lemma nth_error_compile :
  forall prog idx instr,
    nth_error prog idx = Some instr ->
    nth_error (compile_program prog) idx = Some (compile_instruction instr).
Proof.
  intros prog idx instr Hnth.
  unfold compile_program, compile_instruction.
  rewrite List.nth_error_map, Hnth.
  reflexivity.
Qed.

Lemma vm_step_simulated :
  forall prog st instr,
    nth_error prog st.(vm_pc) = Some instr ->
    step_thiele (compile_program prog) (encode_state st) =
    encode_state (vm_step instr st).
  Proof.
    intros prog st instr Hnth.
    unfold step_thiele.
    assert (Hfetch_comp :
              fetch (compile_program prog) (encode_state st)
              = compile_instruction instr).
    { unfold fetch, compile_program, compile_instruction, encode_state; simpl.
      rewrite List.nth_error_map, Hnth.
      reflexivity. }
    rewrite Hfetch_comp.
    unfold encode_state, vm_step, compile_instruction.
    simpl.
    unfold claim_tape_zero; simpl.
  reflexivity.
  Qed.

Lemma err_free_nth :
  forall prog idx instr,
    err_free prog ->
    nth_error prog idx = Some instr ->
    instr.(vm_sets_err) = false.
Proof.
  unfold err_free.
  intros prog idx instr Herr Hnth.
  eapply Forall_nth_error_vm in Herr; eauto.
Qed.

Lemma vm_step_err_false :
  forall instr st,
    vm_err st = false ->
    instr.(vm_sets_err) = false ->
    vm_err (vm_step instr st) = false.
Proof.
  intros instr st HerrSt HerrInstr.
  unfold vm_step.
  simpl.
  rewrite HerrSt, HerrInstr.
  reflexivity.
Qed.

Lemma run_vm_err_false :
  forall fuel prog st,
    err_free prog ->
    vm_err st = false ->
    vm_err (run_vm fuel prog st) = false.
Proof.
  induction fuel as [|fuel IH]; intros prog st Herr Hst; simpl.
  - exact Hst.
  - destruct (vm_err st) eqn:HerrSt.
    + congruence.
    + destruct (vm_fetch prog st) as [instr|] eqn:Hfetch.
      * unfold vm_fetch in Hfetch.
        pose proof Hfetch as Hnth.
        assert (Herr_instr : instr.(vm_sets_err) = false)
          by (apply (err_free_nth prog st.(vm_pc) instr); assumption).
        apply IH; [assumption|].
        apply vm_step_err_false; assumption.
      * exact HerrSt.
Qed.

Lemma run_vm_thiele_agree :
  forall fuel prog st,
    err_free prog ->
    st.(vm_err) = false ->
    run_thiele fuel (compile_program prog) (encode_state st)
    = encode_state (run_vm fuel prog st).
Proof.
  induction fuel as [|fuel IH]; intros prog st Herr Hst; simpl.
  - reflexivity.
  - simpl in Hst.
    rewrite Hst.
    destruct (vm_fetch prog st) as [instr|] eqn:Hfetch.
    + unfold vm_fetch in Hfetch.
      pose proof Hfetch as Hnth.
      assert (Hfetch_comp :
              fetch (compile_program prog) (encode_state st)
              = compile_instruction instr).
      { unfold fetch, compile_program, compile_instruction, encode_state; simpl.
        rewrite List.nth_error_map, Hfetch.
        reflexivity. }
      rewrite Hfetch_comp.
      simpl.
      apply vm_step_simulated in Hfetch.
      rewrite Hfetch.
      apply IH.
      * assumption.
      * simpl.
        rewrite Hst, Bool.orb_false_l.
        apply (err_free_nth prog st.(vm_pc) instr); [assumption|exact Hnth].
    + unfold vm_fetch in Hfetch.
      assert (Hfetch_comp :
                fetch (compile_program prog) (encode_state st) = T_Halt).
      { unfold fetch, compile_program, encode_state in *; simpl in *.
        rewrite List.nth_error_map, Hfetch.
        reflexivity. }
      rewrite Hfetch_comp.
      simpl.
      reflexivity.
Qed.

Theorem vm_is_instance_of_kernel :
  forall fuel prog st,
    err_free prog ->
    st.(vm_err) = false ->
    decode_state (run_thiele fuel (compile_program prog) (encode_state st))
    = run_vm fuel prog st.
Proof.
  intros fuel prog st Herr Hst.
  pose proof (run_vm_thiele_agree fuel prog st Herr Hst) as Hsim.
  remember (run_vm fuel prog st) as rv eqn:Hrv.
  assert (HerrRv : rv.(vm_err) = false).
  { subst rv. apply run_vm_err_false; assumption. }
  apply eq_trans with (y := decode_state (encode_state rv)).
  - apply (f_equal decode_state) in Hsim.
    exact Hsim.
  - apply decode_encode_state_id.
    exact HerrRv.
Qed.

(** The theorem states that the μ-ledger and program counter behaviour of the
    Python VM is precisely the one computed by the kernel interpreter when the
    high-level instructions are compiled down to the primitive
    [H_ClaimTapeIsZero] actions carrying the same μ-deltas. *)
