(** Concrete applicability and fault observations of the actual dispatch
    semantics. These checks evaluate the real rule, not [kami_step]. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore NormalizationStart
  NormalizationSteps ActionEvaluator DispatchExecution.
From Coq Require Import List String NArith.
Import ListNotations.
Open Scope string_scope.

Definition dispatch_instruction (version opcode operand_a : N) : word 128 :=
  NToWord 128 (N.lor (N.shiftl version 120)
    (N.lor (N.shiftl opcode 24) (N.shiftl operand_a 16))).

Definition dispatch_loaded_reset (instruction : word 128) : RegsT :=
  M.add "imem"
    (existT (fullType type) (SyntaxKind (Vector (Bit 128) 7))
      (fun _ => instruction)) dispatch_reset_state.

Definition dispatch_observes_bit {n} (old : RegsT) (key : string) (expected : word n) : bool :=
  match eval_dispatch old with
  | Some updates =>
      match action_read_syntax (M.union updates old) key (Bit n) with
      | Some v => word_eqb v expected
      | None => false
      end
  | None => false
  end.

Example dispatch_invalid_chsh_stays_idle :
  dispatch_observes_bit (dispatch_loaded_reset (dispatch_instruction 3 46 0))
    "chsh_phase" (natToWord 5 0) = true.
Proof. vm_compute. reflexivity. Qed.

Example dispatch_valid_chsh_starts :
  dispatch_observes_bit (dispatch_loaded_reset (dispatch_instruction 2 46 0))
    "chsh_phase" (natToWord 5 1) = true.
Proof. vm_compute. reflexivity. Qed.

Example dispatch_invalid_sat_stays_idle :
  dispatch_observes_bit (dispatch_loaded_reset (dispatch_instruction 3 3 32))
    "lassert_phase" (natToWord 3 0) = true.
Proof. vm_compute. reflexivity. Qed.

Example dispatch_valid_sat_starts :
  dispatch_observes_bit (dispatch_loaded_reset (dispatch_instruction 2 3 32))
    "lassert_phase" (natToWord 3 1) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dispatch_observation_actual : forall n old key (expected : word n),
  dispatch_observes_bit old key expected = true ->
  exists updates,
    SemAction old (attrType dispatch_rule type) updates (M.empty _) WO /\
    M.find key (M.union updates old) =
      Some (existT (fullType type) (SyntaxKind (Bit n)) expected).
Proof.
  intros n old key expected H. unfold dispatch_observes_bit in H.
  destruct (eval_dispatch old) as [updates|] eqn:He; [|discriminate].
  destruct (action_read_syntax (M.union updates old) key (Bit n)) as [value|] eqn:Hr;
    [|discriminate]. unfold word_eqb in H.
  destruct (weq value expected) as [Hv|Hne]; [subst value|discriminate].
  exists updates. split.
  - apply dispatch_actual_action_iff. exact He.
  - eapply action_read_sound. exact Hr.
Qed.

Definition dispatch_bianchi_state (old : RegsT) : RegsT :=
  M.add "mu_tensor"
    (existT (fullType type) (SyntaxKind (Vector (Bit 32) 4))
      (fun idx => if weq idx (natToWord 4 0) then natToWord 32 1 else natToWord 32 0)) old.

Example dispatch_bianchi_chsh_stays_idle :
  dispatch_observes_bit
    (dispatch_bianchi_state (dispatch_loaded_reset (dispatch_instruction 2 46 0)))
    "chsh_phase" (natToWord 5 0) = true.
Proof. vm_compute. reflexivity. Qed.

Example dispatch_bianchi_sat_stays_idle :
  dispatch_observes_bit
    (dispatch_bianchi_state (dispatch_loaded_reset (dispatch_instruction 2 3 32)))
    "lassert_phase" (natToWord 3 0) = true.
Proof. vm_compute. reflexivity. Qed.
