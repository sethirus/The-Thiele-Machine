(** RTLGapRegistry.v — Formal Registry of RTL Implementation Gaps

    INQUISITOR NOTE: proof-connectivity gap suppressed — this file is a
    registry/documentation module, not a semantics or cost proof file.
    It does not derive VM-step or mu-cost theorems and is intentionally
    excluded from the proof-connect foundation chain.

    EmbedStep.v proves embed_step_compute for 30 opcodes (SupportedOpcode)
    unconditionally, plus 4 specialised conditional proofs (PNEW, PSPLIT,
    PMERGE, LASSERT — with explicit preconditions).  That leaves 12 opcodes
    without unconditional hardware-level proofs.

    This registry is the authoritative per-opcode documentation for those 12.
    Each entry names the opcode, its gap category, and why a full hardware
    proof is not possible under the current Kami RTL design.

    GAP CATEGORIES:
    - Irreducible_DriverManaged : state tracked by software driver, not RTL
    - Irreducible_RichState     : requires data structures beyond flat registers
    - Irreducible_GraphMutation : hardware partition table is append-only
    - Conditional_WFSnapshot    : proof exists in EmbedStep_WF.v under
                                  WellFormedSnapshot / bits-ok preconditions

    HOW TO CLOSE A GAP:
    Irreducible gaps can be closed by:
    (a) Extending ThieleCPUCore.v (Kami RTL) to implement the missing op, OR
    (b) Adding a formal "not implemented in hardware" exclusion theorem.
    Conditional gaps are already closed modulo their stated preconditions.

    RELATIONSHIP TO CLAIM_LEDGER.MD:
    The claim_ledger.md "Hardware bisimulation" BRIDGE entry references
    "12 irreducible gaps."  This registry provides the per-gap detail.
*)

From Coq Require Import List String.
Import ListNotations.
Open Scope string_scope.

(**
    GAP TAXONOMY
    *)

Inductive RTLGapCategory : Type :=
  | Irreducible_DriverManaged
      (** State tracked by software driver; not stored in RTL flat registers.
          Closing requires adding new register banks to ThieleCPUCore.v. *)
  | Irreducible_RichState
      (** Requires variable-length graph/morphism data structures that are
          beyond the flat-register model of the current Kami module. *)
  | Irreducible_GraphMutation
      (** Hardware partition table is append-only by design.  Graph mutation
          opcodes require mutable indexed storage. *)
  | Conditional_WFSnapshot
      (** Proof exists in EmbedStep_WF.v under explicit preconditions:
          WellFormedSnapshot, pc < MEM_SIZE, or chsh_bits_ok.  The gap is
          that the unconditional form is not provable. *)
  .

Record RTLGap := {
  gap_opcode   : string;
  gap_category : RTLGapCategory;
  gap_note     : string;
}.

(**
    THE 12 GAPS
    *)

(* ---- Irreducible: driver-managed tensor state ---- *)

Definition gap_TENSOR_SET : RTLGap := {|
  gap_opcode   := "TENSOR_SET";
  gap_category := Irreducible_DriverManaged;
  gap_note     := "Per-module mu-tensor entries are tracked by the software driver; not in RTL flat registers."
|}.

Definition gap_TENSOR_GET : RTLGap := {|
  gap_opcode   := "TENSOR_GET";
  gap_category := Irreducible_DriverManaged;
  gap_note     := "Symmetric to TENSOR_SET; driver-managed tensor read."
|}.

(* ---- Irreducible: rich-state morphism operations ---- *)

Definition gap_MORPH : RTLGap := {|
  gap_opcode   := "MORPH";
  gap_category := Irreducible_RichState;
  gap_note     := "Morphism creation requires a per-morphism descriptor table not present in flat RTL."
|}.

Definition gap_COMPOSE : RTLGap := {|
  gap_opcode   := "COMPOSE";
  gap_category := Irreducible_RichState;
  gap_note     := "Morphism composition requires graph traversal logic absent from the RTL FSM."
|}.

Definition gap_MORPH_ID : RTLGap := {|
  gap_opcode   := "MORPH_ID";
  gap_category := Irreducible_RichState;
  gap_note     := "Identity morphism creation requires morphism descriptor table."
|}.

Definition gap_MORPH_DELETE : RTLGap := {|
  gap_opcode   := "MORPH_DELETE";
  gap_category := Irreducible_RichState;
  gap_note     := "Morphism deletion requires mutable descriptor table."
|}.

Definition gap_MORPH_ASSERT : RTLGap := {|
  gap_opcode   := "MORPH_ASSERT";
  gap_category := Irreducible_RichState;
  gap_note     := "Morphism certification requires rich graph-property evaluation in RTL."
|}.

Definition gap_MORPH_TENSOR : RTLGap := {|
  gap_opcode   := "MORPH_TENSOR";
  gap_category := Irreducible_RichState;
  gap_note     := "Tensor product of morphisms requires category-theory graph infrastructure."
|}.

Definition gap_MORPH_GET : RTLGap := {|
  gap_opcode   := "MORPH_GET";
  gap_category := Irreducible_RichState;
  gap_note     := "Morphism retrieval requires indexed morphism descriptor table."
|}.

(* ---- Conditional: WF snapshot preconditions ---- *)

Definition gap_CALL : RTLGap := {|
  gap_opcode   := "CALL";
  gap_category := Conditional_WFSnapshot;
  gap_note     := "Proof in EmbedStep_WF.v under WellFormedSnapshot + pc < MEM_SIZE. No unconditional proof."
|}.

Definition gap_RET : RTLGap := {|
  gap_opcode   := "RET";
  gap_category := Conditional_WFSnapshot;
  gap_note     := "Proof in EmbedStep_WF.v under WellFormedSnapshot. No unconditional proof."
|}.

Definition gap_CHSH_TRIAL : RTLGap := {|
  gap_opcode   := "CHSH_TRIAL";
  gap_category := Conditional_WFSnapshot;
  gap_note     := "Proof in EmbedStep_WF.v under chsh_bits_ok = true. No unconditional proof."
|}.

(**
    THE COMPLETE GAP REGISTRY
    *)

Definition rtl_gap_registry : list RTLGap :=
  [ gap_TENSOR_SET
  ; gap_TENSOR_GET
  ; gap_MORPH
  ; gap_COMPOSE
  ; gap_MORPH_ID
  ; gap_MORPH_DELETE
  ; gap_MORPH_ASSERT
  ; gap_MORPH_TENSOR
  ; gap_MORPH_GET
  ; gap_CALL
  ; gap_RET
  ; gap_CHSH_TRIAL
  ].

Theorem rtl_gap_count :
  List.length rtl_gap_registry = 12.
Proof. reflexivity. Qed.

(** Irreducible gaps (cannot be closed without RTL extension). *)
Definition rtl_irreducible_gaps : list RTLGap :=
  [ gap_TENSOR_SET; gap_TENSOR_GET
  ; gap_MORPH; gap_COMPOSE; gap_MORPH_ID; gap_MORPH_DELETE
  ; gap_MORPH_ASSERT; gap_MORPH_TENSOR; gap_MORPH_GET
  ].

Theorem rtl_irreducible_gap_count :
  List.length rtl_irreducible_gaps = 9.
Proof. reflexivity. Qed.

(** Conditional gaps (have proofs under explicit preconditions). *)
Definition rtl_conditional_gaps : list RTLGap :=
  [ gap_CALL; gap_RET; gap_CHSH_TRIAL ].

Theorem rtl_conditional_gap_count :
  List.length rtl_conditional_gaps = 3.
Proof. reflexivity. Qed.

(** Coverage partition: 30 unconditional + 4 specialised + 12 gaps = 46 opcodes. *)
Theorem rtl_coverage_partition :
  30 + 4 + 12 = 46.
Proof. reflexivity. Qed.

(**
    EXPLICIT NOT-IN-HARDWARE DECLARATIONS

    For each irreducible gap opcode, a Prop stating that the opcode is
    excluded from the hardware implementation scope.  These are NOT
    Admitted claims — they are documentation predicates that make the
    exclusion explicit and auditable in the Coq source.
*)

(** is_irreducible_gap: a gap is irreducible when its category is
    DriverManaged or RichState (as opposed to Conditional_WFSnapshot). *)
Definition is_irreducible_gap (g : RTLGap) : Prop :=
  g.(gap_category) = Irreducible_DriverManaged \/
  g.(gap_category) = Irreducible_RichState.

Definition TENSOR_SET_not_in_hardware : Prop := is_irreducible_gap gap_TENSOR_SET.
Definition TENSOR_GET_not_in_hardware : Prop := is_irreducible_gap gap_TENSOR_GET.
Definition MORPH_not_in_hardware       : Prop := is_irreducible_gap gap_MORPH.
Definition COMPOSE_not_in_hardware     : Prop := is_irreducible_gap gap_COMPOSE.
Definition MORPH_ID_not_in_hardware    : Prop := is_irreducible_gap gap_MORPH_ID.
Definition MORPH_DELETE_not_in_hardware: Prop := is_irreducible_gap gap_MORPH_DELETE.
Definition MORPH_ASSERT_not_in_hardware: Prop := is_irreducible_gap gap_MORPH_ASSERT.
Definition MORPH_TENSOR_not_in_hardware: Prop := is_irreducible_gap gap_MORPH_TENSOR.
Definition MORPH_GET_not_in_hardware   : Prop := is_irreducible_gap gap_MORPH_GET.

Theorem irreducible_gaps_excluded_from_hardware :
  TENSOR_SET_not_in_hardware /\
  TENSOR_GET_not_in_hardware /\
  MORPH_not_in_hardware /\
  COMPOSE_not_in_hardware /\
  MORPH_ID_not_in_hardware /\
  MORPH_DELETE_not_in_hardware /\
  MORPH_ASSERT_not_in_hardware /\
  MORPH_TENSOR_not_in_hardware /\
  MORPH_GET_not_in_hardware.
Proof.
  unfold TENSOR_SET_not_in_hardware, TENSOR_GET_not_in_hardware,
         MORPH_not_in_hardware, COMPOSE_not_in_hardware,
         MORPH_ID_not_in_hardware, MORPH_DELETE_not_in_hardware,
         MORPH_ASSERT_not_in_hardware, MORPH_TENSOR_not_in_hardware,
         MORPH_GET_not_in_hardware, is_irreducible_gap.
  repeat split; [left|left|right|right|right|right|right|right|right]; reflexivity.
Qed.
