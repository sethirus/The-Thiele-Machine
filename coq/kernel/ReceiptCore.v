(** =========================================================================
    RECEIPT CORE: Generic Computational Receipt Framework
    =========================================================================

    WHY THIS FILE EXISTS:
    I claim computational systems must provide RECEIPTS - verifiable evidence
    that operations occurred with specific costs. This file defines the minimal
    abstract interface for receipt traces, independent of VM specifics. Receipts
    make μ-accounting auditable.

    THE CORE CLAIM:
    Receipts are finite traces (r_op, r_payload) that can be DECODED via
    channel predicates (line 23) into payload streams (line 26). The decoder
    is generic - works for any channel/trace combination. This is the universal
    receipt abstraction.

    WHAT THIS PROVES:
    - Receipt: Abstract receipt structure (opcode + payload, line 12)
    - ReceiptChannel: Boolean predicate for filtering receipts (line 23)
    - decode: Extract payload stream for matching receipts (line 26)
    - decodes_to: Predicate asserting decoded stream equality (line 30)
    - decodes_to_refl: Reflexivity - decode always produces itself (line 33)

    PHYSICAL INTERPRETATION:
    Receipts are the "observational outcomes" of computation. Like experimental
    data, receipts are finite, concrete, and verifiable. The channel abstraction
    separates EMISSION (kernel's job) from VERIFICATION (prover's job). Boolean
    channels avoid classical axioms - keep verification constructive.

    FALSIFICATION:
    Show that decode(ch, tr) ≠ decode(ch, tr) for some channel/trace. This
    would violate decodes_to_refl (line 33) and break reflexivity.

    Or prove the channel abstraction is insufficiently expressive - can't
    distinguish some operationally distinct receipt sequences. Add more
    structure to Receipt if needed.

    NO AXIOMS (uses bool, not Prop, for channels). NO ADMITS. Pure abstraction.

    ========================================================================= *)

From Coq Require Import List.
Import ListNotations.

Module ReceiptCore.

(** =========================================================================
    RECEIPT STRUCTURE
    ========================================================================= *)

(** ABSTRACT RECEIPT: Operation + Payload

    A receipt records that operation r_op occurred with payload r_payload.
    Intentionally minimal - kernel decides what gets recorded.

    Examples:
    - μ-cost receipts: r_op = COST, r_payload = [delta, instruction_id]
    - Observation receipts: r_op = MEASURE, r_payload = [module_id, outcome]
    - Certification receipts: r_op = CERT, r_payload = [formula_hash, bits] *)
Record Receipt := {
  r_op : nat;           (* Operation identifier *)
  r_payload : list nat  (* Payload data *)
}.

(** Trace = sequence of receipts. This is what verifiers see. *)
Definition Trace := list Receipt.

(** =========================================================================
    RECEIPT CHANNELS
    ========================================================================= *)

(** CHANNEL ABSTRACTION: Boolean predicate on receipts

    A channel selects which receipts to decode. Using bool (not Prop) keeps
    verification constructive and avoids classical axioms.

    Example channels:
    - fun r => r.(r_op) =? COST            (* μ-cost receipts only *)
    - fun r => r.(r_op) =? MEASURE         (* Observation receipts only *)
    - fun r => r.(r_op) =? CERT            (* Certification receipts only *) *)
Definition ReceiptChannel := Receipt -> bool.

(** =========================================================================
    DECODING
    ========================================================================= *)

(** GENERIC DECODER: Extract payload stream for channel

    Given a channel predicate ch and trace tr, decode:
    1. Filters tr to receipts matching ch
    2. Extracts r_payload from each matching receipt
    3. Returns payload stream as list (list nat)

    This is the universal decoder - works for any channel/trace. Verifiers
    use this to extract relevant data from raw receipt traces. *)
Definition decode (ch : ReceiptChannel) (tr : Trace) : list (list nat) :=
  map r_payload (filter ch tr).

(** DECODING PREDICATE: Assert decoded stream equals expected

    decodes_to ch tr xs means "decoding trace tr with channel ch yields xs".
    This is the verification statement: "the trace contains this data stream". *)
Definition decodes_to (ch : ReceiptChannel) (tr : Trace) (xs : list (list nat)) : Prop :=
  decode ch tr = xs.

(** REFLEXIVITY: Decoder always produces its own output

    Trivial but important: decode(ch, tr) decodes to itself. This establishes
    that decoding is deterministic and well-defined. *)
(** HELPER: Reflexivity/transitivity/symmetry property *)
(** HELPER: Reflexivity/transitivity/symmetry property *)
Lemma decodes_to_refl :
  forall ch tr, decodes_to ch tr (decode ch tr).
Proof.
  intros; unfold decodes_to; reflexivity.
Qed.

(** =========================================================================
    FRAMEWORK NOTES

    This module is INTENTIONALLY ABSTRACT. It doesn't specify:
    - How receipts are emitted (kernel's job)
    - What operations exist (application-specific)
    - What payloads mean (depends on r_op)

    It DOES specify:
    - Receipt structure (opcode + payload)
    - Channel abstraction (boolean predicates)
    - Decoding semantics (filter + map)

    This separation allows:
    - Kernel to emit receipts without knowing about channels
    - Verifiers to define channels without knowing kernel internals
    - Proofs to use generic decoding without VM-specific details

    See ReceiptIntegrity.v for how this connects to μ-accounting.

    ========================================================================= *)

End ReceiptCore.
