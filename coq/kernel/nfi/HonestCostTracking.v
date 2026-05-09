(** HonestCostTracking: well-formedness separation between
    honest cost-tracking systems and unconstrained cost-bearing systems.

    AIM
    ---
    The Receipt Theorem and `universal_nfi_any_substrate` together establish that
    *any* CertificationSystem (which by construction satisfies A2) cannot certify
    at total trace cost zero.  A natural rebuttal is: "fine, build a TM that
    increments MU_ADDR on every cert-flip; it satisfies A2 by construction; the
    Receipt Theorem then says nothing about computers in general."  That rebuttal
    is correct as stated — and concedes the entire point.  *Once you accept the
    A2 constraint, you are inside the honest world the Receipt Theorem describes.*

    What this file proves
    ---------------------
    The A2 constraint is a *non-trivial* well-formedness restriction, not a
    tautology.  We exhibit a `CostBearingSystem` (a record without A2) where
    a single non-empty trace certifies at total cost zero.  By
    `universal_nfi_any_substrate`, no `CertificationSystem` (i.e. no honest
    cost-tracking system) can match this trace.

    Therefore the class of (state, trace) pairs reachable in the unconstrained
    world is *strictly larger* than the class reachable in the honest world.
    The well-formedness gap is real.  This is the same shape of separation that
    linear types make over untyped lambda calculus: same compute power, strictly
    smaller well-formedness class.

    What this file does NOT prove
    -----------------------------
    - It does not claim Thiele computes more functions than a Turing machine.
      Church-Turing is preserved.  `thiele_morphism_exists` already shows any
      honest cost-tracking machine is initial-imaged by Thiele.
    - It does not prove a separation between *language classes* (sets of
      accepted inputs).  The separation is between (input, certified-trace)
      pairs.  A dishonest TM can produce a trace certifying that 2+2=5 at cost
      0; an honest one cannot.  That is the gap.

    Falsification
    -------------
    To falsify [honest_cost_tracking_strict_restriction], either (a) exhibit a
    `CertificationSystem` (one that constructs without `cs_cert_costs` in scope)
    with a non-empty cert-flip trace at total cost 0, or (b) prove that every
    `CostBearingSystem` either satisfies A2 or has no cert-flip trace.  Both
    contradict the kernel.
*)

From Kernel Require Import UniversalCertificationCost.
From Kernel Require Import VMState.
From Kernel Require Import VMStep.
From Kernel Require Import MuCostModel.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.

(** A cost-bearing system without A2.  Same fields as
    [CertificationSystem], minus the [cs_cert_costs] honesty constraint.
    This models a Turing machine where the programmer might or might not
    honor cost-tracking — the ISA imposes no discipline. *)
Record CostBearingSystem := mk_cb_system {
  cb_state : Type;
  cb_instr : Type;
  cb_step  : cb_state -> cb_instr -> cb_state;
  cb_cost  : cb_instr -> nat;
  cb_cert  : cb_state -> bool;
}.

Fixpoint cb_run (CB : CostBearingSystem)
                (trace : list (cb_instr CB))
                (s : cb_state CB) : cb_state CB :=
  match trace with
  | []        => s
  | i :: rest => cb_run CB rest (cb_step CB s i)
  end.

Fixpoint cb_total_cost (CB : CostBearingSystem)
                       (trace : list (cb_instr CB)) : nat :=
  match trace with
  | []        => 0
  | i :: rest => cb_cost CB i + cb_total_cost CB rest
  end.

(** A concrete dishonest system.

    State: a single bit, the certification flag.
    Instr: unit (one instruction, "forge").
    Step:  (fun _ _ => true) — flips the flag to true regardless of prior value.
    Cost:  0 — the forge instruction costs nothing.
    Cert:  the identity on bool.

    This is the smallest possible witness of free certification. *)
Definition dishonest_forge_system : CostBearingSystem :=
  {| cb_state := bool;
     cb_instr := unit;
     cb_step  := fun _ _ => true;
     cb_cost  := fun _   => 0;
     cb_cert  := fun b   => b |}.

(** A non-empty trace on the dishonest system that flips cert false→true
    at total cost zero.  This is the "free forgery" witness. *)
Definition dishonest_forge_trace : list (cb_instr dishonest_forge_system) := [tt].

(** Free certification is reachable in the unconstrained cost-bearing world. *)
Lemma dishonest_free_certification :
    cb_cert dishonest_forge_system false = false
  /\ cb_cert dishonest_forge_system
        (cb_run dishonest_forge_system dishonest_forge_trace false) = true
  /\ cb_total_cost dishonest_forge_system dishonest_forge_trace = 0.
Proof.
  repeat split.
Qed.

(** [honest_cost_tracking_strict_restriction]: the well-formedness gap.

    LEFT CONJUNCT (existence of free forgery): there is a CostBearingSystem
    with a non-empty trace that flips cert false→true at total cost zero.

    RIGHT CONJUNCT (no honest system can do this): every CertificationSystem,
    on every uncert→cert trace, has total cost ≥ 1.

    Together: the A2 constraint cuts free-forgery traces out of the
    reachable trace-set.  That is a non-trivial restriction.

    Note: the right conjunct is exactly [universal_nfi_any_substrate]. *)
Theorem honest_cost_tracking_strict_restriction :
  (** There exists a free-forgery trace in the unconstrained world. *)
  (exists (CB : CostBearingSystem)
          (s0 : cb_state CB)
          (trace : list (cb_instr CB)),
      cb_cert CB s0 = false
      /\ cb_cert CB (cb_run CB trace s0) = true
      /\ cb_total_cost CB trace = 0)
  /\
  (** No honest cost-tracking system admits a free-forgery trace. *)
  (forall (CS : CertificationSystem)
          (trace : list (cs_instr CS))
          (s0 : cs_state CS),
      cs_cert CS s0 = false ->
      cs_cert CS (cs_run CS trace s0) = true ->
      cs_total_cost CS trace >= 1).
Proof.
  split.
  - exists dishonest_forge_system, false, dishonest_forge_trace.
    exact dishonest_free_certification.
  - exact universal_nfi_any_substrate.
Qed.

(** Corollary: any system that *can* free-forge fails to satisfy A2.

    This is the contrapositive of A2: if there is a state s and instruction i
    where cert flips false→true at cost 0, then no CertificationSystem record
    can be built with this (cb_step, cb_cost, cb_cert) — because A2 would fail
    on (s, i).

    Operationally: "honest cost-tracking" is exactly "A2 holds."  A system
    that exhibits free certification is, by definition, not honest. *)
Theorem free_forgery_violates_A2 :
  forall (CB : CostBearingSystem) (s : cb_state CB) (i : cb_instr CB),
      cb_cert CB s = false
   -> cb_cert CB (cb_step CB s i) = true
   -> cb_cost CB i = 0
   -> ~ (forall (s' : cb_state CB) (i' : cb_instr CB),
            cb_cert CB s' = false ->
            cb_cert CB (cb_step CB s' i') = true ->
            cb_cost CB i' >= 1).
Proof.
  intros CB s i Hf Ht Hc Hhonest.
  specialize (Hhonest s i Hf Ht).
  rewrite Hc in Hhonest.
  inversion Hhonest.
Qed.

(** Corollary: the dishonest forge system explicitly fails A2.

    Direct demonstration that [dishonest_forge_system] is in the relative
    complement of the honest class. *)
Corollary dishonest_forge_system_violates_A2 :
  ~ (forall (s : cb_state dishonest_forge_system)
            (i : cb_instr dishonest_forge_system),
        cb_cert dishonest_forge_system s = false ->
        cb_cert dishonest_forge_system
                (cb_step dishonest_forge_system s i) = true ->
        cb_cost dishonest_forge_system i >= 1).
Proof.
  apply (free_forgery_violates_A2 dishonest_forge_system false tt);
    reflexivity.
Qed.

(** ** Connection to the Thiele cost foundation.

    The Thiele VM's [vm_apply] cost-discipline ([instruction_cost] in
    [VMStep.v]) is precisely the A2-respecting cost rule, so the Thiele
    VM is a [CertificationSystem] (witnessed by [thiele_cert_addr_system]
    in [UniversalCertificationCost.v]).  The well-formedness gap proven
    above therefore says: any Thiele VM trace lives inside the honest
    class; the only way to escape into the dishonest class is to build a
    different cost model that violates A2.  The [free_forgery_violates_A2]
    theorem is exactly the formal sense in which Thiele's ISA enforces
    what TM ISAs leave to programmer discipline. *)
Remark thiele_vm_is_in_honest_class :
  exists (CS : CertificationSystem),
    cs_state CS = VMState /\
    forall s i, cs_cert CS s = false ->
                cs_cert CS (cs_step CS s i) = true ->
                cs_cost CS i >= 1.
Proof.
  exists thiele_cert_addr_system. split.
  - reflexivity.
  - apply cs_cert_costs.
Qed.
