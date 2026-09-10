(* Active regression proof: compiled by _CoqProject and CI; included in the
   full assumption receipt. Historical review copies remain under artifacts/. *)
(* Independent checks of claims discussed in the accompanying assessment.
   Compile with the repository's _CoqProject load paths. *)
From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import VMState VMStep SimulationProof MuInitiality
  UniversalCertificationCost F1_LogicalErasure F1_StrongForm.

(* A2 requires a predicate and a cost function, not two dedicated fields. *)
Definition counter_certification_system : CertificationSystem.
Proof.
  refine {| cs_state := nat; cs_instr := unit;
            cs_step := fun n _ => S n;
            cs_cost := fun _ => 1;
            cs_cert := Nat.odd |}.
  intros. lia.
Defined.

Definition pack_receipt (mu : nat) (cert : bool) (memory : list nat) :=
  mu :: (if cert then 1 else 0) :: memory.
Definition unpack_receipt (encoded : list nat) : nat * bool * list nat :=
  match encoded with
  | mu :: cert :: memory => (mu, Nat.eqb cert 1, memory)
  | _ => (0, false, [])
  end.
Theorem receipt_encoding_roundtrip :
  forall mu cert memory,
    unpack_receipt (pack_receipt mu cert memory) = (mu, cert, memory).
Proof. intros mu [] memory; reflexivity. Qed.

(* Trace-fold initiality does not establish existence of a certification-
   preserving VM-state morphism into every CertCostMachine. *)
Definition never_certifies : CertCostMachine.
Proof.
  refine {| ccm_state := unit; ccm_step := fun _ _ => tt;
            ccm_cost := fun _ => 0; ccm_cert := fun _ => false |}.
  intros s i Hbefore Hafter. discriminate Hafter.
Defined.

Theorem no_vm_state_morphism_to_never_certifies :
  CertCostMorphism thiele_cert_cost_machine never_certifies -> False.
Proof.
  intro morphism.
  pose proof (ccm_map_cert _ _ morphism
    (vm_apply init_state (instr_certify 0))) as H.
  discriminate H.
Qed.

(* The current F1 premises cannot hold together on the full VM ISA:
   JUMP 1 at cost zero collapses the macro-property PC = 1. *)
Definition pc_is_one (s : VMState) : bool := Nat.eqb (vm_pc s) 1.

Lemma zero_cost_jump_collapses_pc_class :
  step_collapses_bool_classes pc_is_one (instr_jump 1 0).
Proof.
  split.
  - exists init_state. split; reflexivity.
  - intros s _. reflexivity.
Qed.

Theorem full_vm_f1_premises_incompatible :
  ~ exists dissipation : vm_instruction -> nat,
      (forall P i, step_collapses_bool_classes P i -> dissipation i >= 1) /\
      cost_dissipation_calibrated dissipation.
Proof.
  intros [dissipation [Hlandauer Hcalibration]].
  pose proof (Hlandauer pc_is_one (instr_jump 1 0)
    zero_cost_jump_collapses_pc_class) as Hpositive.
  pose proof (Hcalibration (instr_jump 1 0)) as Hzero.
  cbn [instruction_cost] in Hzero. lia.
Qed.

Print Assumptions receipt_encoding_roundtrip.
Print Assumptions no_vm_state_morphism_to_never_certifies.
Print Assumptions full_vm_f1_premises_incompatible.

(* Structural state can change for zero ledger cost. A2 must not be read as
   a positive price for every observable change. *)
Theorem zero_cost_partition_changes_structure :
  vm_graph (vm_apply init_state (instr_pnew [1] 0)) <> vm_graph init_state /\
  vm_mu (vm_apply init_state (instr_pnew [1] 0)) = 0.
Proof.
  split.
  - vm_compute. discriminate.
  - reflexivity.
Qed.
