(** CommitmentVsErasure: equal-trust separation between commitment cost
    and erasure cost.

    The verification-cost gap is a trust-boundary theorem: trusted producers
    beat untrusted trace audits for any local invariant.  This file targets a
    different comparison, with trust held fixed on both sides.

    Both systems below are "trusted" in the same formal sense: their record
    includes the law they claim to enforce.

    - A trusted erasure-accounting system enforces: erased steps cost at least 1.
    - A trusted A2 certification system enforces: cert-flip steps cost at least 1.

    The separation is semantic, not about trace validation.  A trusted erasure
    law can certify without erasing, at total cost 0.  A trusted A2 law cannot
    certify at total cost 0.  This is the first substitution-test target:
    the theorem talks about commitment specifically, and the erasure law is not
    a substitute for it under equal trust.
*)

From Coq Require Import List Arith.PeanoNat Lia Bool.
Import ListNotations.

From Kernel Require Import UniversalCertificationCost.

(** A trusted erasure-accounting system.

    The record has the same shape as [CertificationSystem], but the trusted law
    is Landauer-style erasure accounting rather than A2 commitment accounting.
    The [tea_erases] predicate is intentionally step-local: it says whether the
    current step performs an erasure. *)
Record TrustedErasureAccountingSystem := mk_trusted_erasure_system {
  tea_state  : Type;
  tea_instr  : Type;
  tea_step   : tea_state -> tea_instr -> tea_state;
  tea_cost   : tea_instr -> nat;
  tea_cert   : tea_state -> bool;
  tea_erases : tea_state -> tea_instr -> bool;

  tea_erasure_costs :
    forall (s : tea_state) (i : tea_instr),
      tea_erases s i = true ->
      tea_cost i >= 1;
}.

Fixpoint tea_run (TE : TrustedErasureAccountingSystem)
                 (trace : list (tea_instr TE))
                 (s : tea_state TE) : tea_state TE :=
  match trace with
  | [] => s
  | i :: rest => tea_run TE rest (tea_step TE s i)
  end.

Fixpoint tea_total_cost (TE : TrustedErasureAccountingSystem)
                        (trace : list (tea_instr TE)) : nat :=
  match trace with
  | [] => 0
  | i :: rest => tea_cost TE i + tea_total_cost TE rest
  end.

Fixpoint tea_any_erasure (TE : TrustedErasureAccountingSystem)
                         (trace : list (tea_instr TE))
                         (s : tea_state TE) : bool :=
  match trace with
  | [] => false
  | i :: rest =>
      orb (tea_erases TE s i)
          (tea_any_erasure TE rest (tea_step TE s i))
  end.

(** Discharge the impossible erasure branch through the trusted [discriminate]
    idiom. This witness system never erases, so [tea_erasure_costs] is only ever
    asked about a [false = true] hypothesis; keeping a raw [False] eliminator out
    of term position. *)
Lemma erasure_branch_unreachable {P : Prop} (H : false = true) : P.
Proof. discriminate H. Qed.

(** A concrete trusted erasure system that commits certification without
    erasing anything.

    State is the certification bit.  The single instruction sets it to true.
    The step is trusted with respect to the erasure law because it never erases.
    Its cost is therefore allowed to be 0 under erasure accounting. *)
Definition commit_without_erasure_system : TrustedErasureAccountingSystem :=
  {| tea_state := bool;
     tea_instr := unit;
     tea_step := fun _ _ => true;
     tea_cost := fun _ => 0;
     tea_cert := fun b => b;
     tea_erases := fun _ _ => false;
     tea_erasure_costs := fun _ _ Herase =>
       erasure_branch_unreachable Herase |}.

Definition commit_without_erasure_trace :
  list (tea_instr commit_without_erasure_system) := [tt].

Lemma trusted_erasure_system_certifies_without_erasure :
  tea_cert commit_without_erasure_system false = false /\
  tea_cert commit_without_erasure_system
    (tea_run commit_without_erasure_system
             commit_without_erasure_trace false) = true /\
  tea_total_cost commit_without_erasure_system
    commit_without_erasure_trace = 0 /\
  tea_any_erasure commit_without_erasure_system
    commit_without_erasure_trace false = false.
Proof.
  repeat split.
Qed.

(** Same trust posture, different trusted law: every trusted A2 system pays
    positive cost when it reaches certification. *)
(* Re-exports the universal certification-cost floor under the name this file's
   erasure-vs-A2 narrative refers to. No new content; deliberate.
   INQUISITOR NOTE: alias for universal_nfi_any_substrate. *)
Theorem trusted_a2_system_certification_cost_floor :
  forall (CS : CertificationSystem)
         (trace : list (cs_instr CS))
         (s0 : cs_state CS),
    cs_cert CS s0 = false ->
    cs_cert CS (cs_run CS trace s0) = true ->
    cs_total_cost CS trace >= 1.
Proof.
  exact universal_nfi_any_substrate.
Qed.

(** Equal-trust separation.

    A trusted erasure law and a trusted A2 law make different predictions for
    the same semantic event: reaching a certified state.  Erasure accounting
    permits zero-cost certification when no erasure occurs; A2 accounting
    forbids zero-cost certification by construction. *)
Theorem commitment_cost_not_reducible_to_erasure_cost :
  (exists (TE : TrustedErasureAccountingSystem)
          (trace : list (tea_instr TE))
          (s0 : tea_state TE),
      tea_cert TE s0 = false /\
      tea_cert TE (tea_run TE trace s0) = true /\
      tea_total_cost TE trace = 0 /\
      tea_any_erasure TE trace s0 = false)
  /\
  (forall (CS : CertificationSystem)
          (trace : list (cs_instr CS))
          (s0 : cs_state CS),
      cs_cert CS s0 = false ->
      cs_cert CS (cs_run CS trace s0) = true ->
      cs_total_cost CS trace >= 1).
Proof.
  split.
  - exists commit_without_erasure_system,
      commit_without_erasure_trace,
      false.
    exact trusted_erasure_system_certifies_without_erasure.
  - exact trusted_a2_system_certification_cost_floor.
Qed.

Print Assumptions trusted_erasure_system_certifies_without_erasure.
Print Assumptions trusted_a2_system_certification_cost_floor.
Print Assumptions commitment_cost_not_reducible_to_erasure_cost.
