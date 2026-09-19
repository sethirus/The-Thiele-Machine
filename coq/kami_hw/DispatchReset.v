(** Reset facts are about Kami's actual register initialization map. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore NormalizationStart
  NormalizationSteps DispatchExecution.
From Coq Require Import List String FunctionalExtensionality.
Import ListNotations.
Open Scope string_scope.

Definition actual_reset_contract (old : RegsT) : Prop :=
  M.find "halted" old = Some (regbool false) /\
  M.find "err" old = Some (regbool false) /\
  M.find "lassert_phase" old = Some
    (existT (fullType type) (SyntaxKind (Bit 3)) (natToWord 3 0)) /\
  M.find "chsh_phase" old = Some (reg5 (natToWord 5 0)) /\
  M.find "mc_phase" old = Some (reg4 (natToWord 4 0)) /\
  M.find "morph_next_id" old = Some (reg5 (natToWord 5 1)) /\
  M.find "coupling_desc_next_id" old = Some (reg5 (natToWord 5 1)) /\
  M.find "coupling_pair_next_id" old = Some (reg5 (natToWord 5 0)) /\
  M.find "morph_valid_table" old = Some (regvalid (fun _ => false)) /\
  M.find "coupling_desc_valid_table" old = Some (regvalid (fun _ => false)) /\
  M.find "coupling_desc_base_table" old = Some (regbases (fun _ => natToWord 4 0)) /\
  M.find "coupling_desc_count_table" old = Some (regcounts (fun _ => natToWord 5 0)) /\
  M.find "coupling_pair_valid_table" old = Some (regvalid (fun _ => false)).

Theorem actual_cpu_reset_contract : actual_reset_contract dispatch_reset_state.
Proof.
  vm_compute. repeat split; try reflexivity.
  all: do 2 f_equal; apply functional_extensionality; intro idx;
    shatter_word idx;
    repeat match goal with b : bool |- _ => destruct b end; reflexivity.
Qed.
