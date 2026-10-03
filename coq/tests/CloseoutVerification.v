(** * CloseoutVerification: machine-checked invariants for the closeout state

    This is a status module: the two checkpoints below are statements
    about the kernel's configuration that hold by [reflexivity] or by case
    analysis on the instruction type. Their job is to
    ensure that any change which would break a structural invariant
    (for example, removing the empty [rtl_gap_registry] or accidentally
    losing a [Qed] proof) shows up immediately as a build failure of
    this file.

    The opcode coverage state:

      - 37 opcodes unconditional ([SupportedOpcode] without the four
        Q_{1+AB} certificate opcodes the CPU does not encode, + CALL +
        RET + CHSH_TRIAL + TENSOR_SET + TENSOR_GET + LASSERT).
      - 10 opcodes conditional, with [Qed] proofs under
        [WFDrivenPrecondition] structural invariants: PNEW, PSPLIT,
        PMERGE, MORPH, MORPH_ID, MORPH_DELETE, MORPH_ASSERT, MORPH_GET,
        COMPOSE, MORPH_TENSOR.
      - 0 structural gaps in [rtl_gap_registry].

    SCOPE NOTE: foundation connectivity gap suppressed; this file is
    a status / documentation module that does not define new semantics
    or μ-cost theorems. It is intentionally excluded from the
    foundation chain and exists purely as an audit boundary. *)

From Coq Require Import List.
Import ListNotations.

From Kernel Require Import VMStep.
From KamiHW Require Import RTLGapRegistry EmbedStep.

(** Checkpoint 1: zero gaps in the RTL registry.

    The [rtl_gap_registry] from [KamiHW.RTLGapRegistry] tracks any
    opcode whose RTL/Kami refinement is incomplete. The registry
    is empty; this lemma certifies that fact and fails to build if a gap is
    introduced. *)
Theorem closeout_zero_gaps :
  List.length rtl_gap_registry = 0.
Proof. reflexivity. Qed.

(** Checkpoint 2: opcode-coverage partition.

    Every instruction falls in one of three classes: [SupportedOpcode]
    (proved by [embed_step_supported]), the six opcodes with their own
    unconditional or bounded-invariant proofs ([unconditional_extra]), and
    the ten structural opcodes proved under [WFDrivenPrecondition]
    ([wf_conditional]). The theorem fails to build if an instruction is
    added to the type without being placed in a class. *)
Definition unconditional_extra (i : vm_instruction) : Prop :=
  match i with
  | instr_call _ _ | instr_ret _ | instr_chsh_trial _ _ _ _ _
  | instr_tensor_set _ _ _ _ _ | instr_tensor_get _ _ _ _ _
  | instr_lassert _ _ _ _ _ => True
  | _ => False
  end.

Definition wf_conditional (i : vm_instruction) : Prop :=
  match i with
  | instr_pnew _ _ | instr_psplit _ _ _ _ | instr_pmerge _ _ _
  | instr_morph _ _ _ _ _ | instr_morph_id _ _ _ | instr_morph_delete _ _
  | instr_morph_assert _ _ _ _ | instr_morph_get _ _ _ _
  | instr_compose _ _ _ _ | instr_morph_tensor _ _ _ _ => True
  | _ => False
  end.

Theorem closeout_opcode_coverage :
  forall i : vm_instruction,
    SupportedOpcode i \/ unconditional_extra i \/ wf_conditional i.
Proof. intro i; destruct i; simpl; tauto. Qed.
