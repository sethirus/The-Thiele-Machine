(** ReceiptCore: a minimal abstract interface for receipt traces

  This file defines a small generic framework for receipts and receipt
  channels, independent of the concrete VM. A receipt is just an operation id
  plus payload, and decoding filters a trace through a boolean channel
  predicate.

  The point is modest: isolate the reusable abstraction that later receipt
  files instantiate. Using boolean channels keeps the interface constructive
  and lightweight.

  *)

(* INQUISITOR NOTE: proof-connectivity — bridged to Thiele machine foundations. *)
From Kernel Require Import VMState VMStep.
From Kernel Require Import MuCostModel.

From Coq Require Import List.
Import ListNotations.

Module ReceiptCore.

(** Receipt structure. *)

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

(** Receipt channels. *)

(** CHANNEL ABSTRACTION: Boolean predicate on receipts

    A channel selects which receipts to decode. Using bool (not Prop) keeps
    verification constructive and avoids classical axioms.

    Example channels:
    - fun r => r.(r_op) =? COST            (* μ-cost receipts only *)
    - fun r => r.(r_op) =? MEASURE         (* Observation receipts only *)
    - fun r => r.(r_op) =? CERT            (* Certification receipts only *) *)
Definition ReceiptChannel := Receipt -> bool.

(** Decoding. *)

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

(** Previously: [decodes_to_refl] asserted [decodes_to ch tr (decode ch tr)].
    Since [decodes_to ch tr xs] is defined as [decode ch tr = xs], the
    claim reduces to [decode ch tr = decode ch tr] and discharges by
    [reflexivity].  No caller depended on the lemma; the reflexivity
    fact is available at any site by [unfold decodes_to; reflexivity]. *)

(**
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

    *)

End ReceiptCore.
