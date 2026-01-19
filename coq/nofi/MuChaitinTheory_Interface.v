From Coq Require Import Arith.PeanoNat Strings.String.

Require Import Kernel.VMState.
Require Import Kernel.VMStep.
Require Import Kernel.MuInformation.
Require Import Kernel.MuNoFreeInsightQuantitative.
Require Import Kernel.MuChaitin.
Require Import Kernel.RevelationRequirement.

Import RevelationProof.

(** * μ–Chaitin Theory Interface (axiom-free)

    This interface is the “theory layer” counterpart of [Kernel.MuChaitin].

    It intentionally does **not** attempt to model a full proof calculus.
    Instead it provides the minimal contracts needed for a Chaitin-style bound:

    - A theory is realized as a kernel trace generator.
    - If the theory can certify/prove at least [k] bits (in a traceable sense),
      then there is a *concrete* kernel run whose μ-ledger budget is bounded by
      the theory description size (plus a fixed overhead), and whose
      certification step has payload-size ≥ k.

    The functor theorem in [MuChaitinTheory_Theorem.v] turns these contracts
    into a quantitative impossibility statement:

      proves_bits k -> k ≤ |desc| + overhead.
*)

Module Type MU_CHAITIN_THEORY_SYSTEM.
  Variable theory_desc : string.
  Variable overhead : nat.

  (** A claim “the theory can certify/prove ≥ k bits of halting information”.
      This is intentionally abstract: a client may instantiate it with a
      provability predicate, an enumerator, or a compiler-to-trace pipeline.
  *)
  Variable proves_bits : nat -> Prop.

  (** Realize proofs/certifications as a kernel trace. *)
  Variable trace_for : nat -> Trace.
  Variable fuel_for : nat -> nat.
  Variable s_init : VMState.

  Variable clean_start : s_init.(vm_csrs).(csr_cert_addr) = 0%nat.

  (** Pricing policy used by the kernel-level μ–Chaitin corollary.
      Typically this is discharged by construction: declared μ-cost >= payload.
  *)
  Variable priced : forall instr, MuChaitin.cert_priced instr.

  (** The theory description size is the only “free” information source.
      Any additional certified payload must be paid via μ-injection.

      Concretely: for any k the trace-based run that witnesses [proves_bits k]
      must have μ-ledger increase bounded by |desc| + overhead.
  *)
  Variable proves_bits_witness :
    forall k,
      proves_bits k ->
      exists s_final instr,
        trace_run (fuel_for k) (trace_for k) s_init = Some s_final /\
        has_supra_cert s_final /\
        MuNoFreeInsightQuantitative.is_cert_setter instr /\
        (* The run pays enough μ-information for the payload of [instr]. *)
        mu_info_nat s_init s_final >= MuChaitin.cert_payload_size instr /\
        (* The certified payload is at least k bits. *)
        MuChaitin.cert_payload_size instr >= k /\
        (* Budget upper bound: theory description size + overhead. *)
        s_final.(vm_mu) <= s_init.(vm_mu) + String.length theory_desc + overhead.
End MU_CHAITIN_THEORY_SYSTEM.
