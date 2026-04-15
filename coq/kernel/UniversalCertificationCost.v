(** UniversalCertificationCost.v
    ======================================================================
    UNIVERSAL NO FREE INSIGHT: ANY SOUND CERTIFICATION MECHANISM COSTS

    THE GAP THIS CLOSES
    ======================================================================
    AbstractNoFI.v proves NoFI for AbstractCertMachine — parameterized over
    STATE TYPE but fixed to vm_instruction as the instruction type.
    "Universal" there means: any machine using Thiele's instruction vocabulary.

    THIS FILE proves NoFI for CertificationSystem — parameterized over BOTH
    state type AND instruction type.  The instruction vocabulary is fully
    abstract.  No reference to vm_instruction, VMState, or Thiele at all.

    THE CLAIM
    ======================================================================
    THEOREM (universal_nfi_any_substrate):

      For any computational system CS with:
        A2. cs_cert_costs: going from uncertified → certified in one step
            requires the instruction cost to be ≥ 1,

      executing ANY trace from an uncertified initial state to a certified
      final state must have total cost ≥ 1.

    This is substrate-independent.  The instruction type is a Coq Type —
    it could be vm_instruction, a proof term, a Bitcoin transaction, a
    photon absorption, or anything else with a cost function.

    THE MINIMUM AXIOM
    ======================================================================
    A2 alone is sufficient for the base claim.  It says:

        ∀ s i,  cs_cert s = false  →
                cs_cert (cs_step s i) = true  →
                cs_cost i ≥ 1

    In words: "You cannot certify in one step for free."

    This is weaker than it looks.  It does NOT say:
      - Cert is monotone (once certified, always certified)
      - The witness is meaningful
      - The cost is tight

    It says only: the moment of certification has a positive price tag.

    The universal theorem (trace-level, any length) follows from A2 alone
    by induction on the trace.

    THE THIELE INSTANTIATION
    ======================================================================
    The Thiele VM instantiates CertificationSystem TWICE:

    Instance 1 (csr_cert_addr channel):
      cs_cert   := thiele_cert_bool (csr_cert_addr ≠ 0)
      cs_step   := vm_apply
      cs_cost   := instruction_cost
      A2 discharged by: no_free_certification (from AbstractNoFI.v)

    Instance 2 (vm_certified channel):
      cs_cert   := (fun s => s.(vm_certified))
      cs_step   := vm_apply
      cs_cost   := instruction_cost
      A2 discharged by: no_free_certification_certified (from AbstractNoFI.v)

    Both instances are fully proven (zero Admitted).

    WHAT COMES NEXT (Axiom 5)
    ======================================================================
    This file closes the base gap: certification costs ≥ 1.
    The next challenge is the QUANTITATIVE gap:

        certification costs ≥ K(certificate)

    where K is the Kolmogorov complexity (or information content) of the
    certificate.  That would say: you can't compress the cost of insight
    below the information content of what you learn.

    Axiom 5 will require adding a witness complexity measure to
    CertificationSystem.  This file provides the foundation.

    STATUS: Zero Admitted.  Zero project-local axioms.
    ======================================================================
*)

From Coq Require Import List Arith.PeanoNat Lia Bool.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof AbstractNoFI.

(** =========================================================================
    PART 1: THE ABSTRACT CERTIFICATION SYSTEM
    =========================================================================

    CertificationSystem: fully parameterized over BOTH state type AND
    instruction type.  No reference to vm_instruction.

    THE SINGLE AXIOM (A2):
    A certification step — one that moves cert from false to true —
    must have cost ≥ 1.  This is the only axiom needed for the base theorem.
*)

Record CertificationSystem := mk_cert_system {
  (** The state space of the computational system. *)
  cs_state : Type;

  (** The instruction type.  Fully abstract — could be vm_instruction,
      a proof term, a network packet, a thermodynamic process, anything. *)
  cs_instr : Type;

  (** The step function: one instruction transforms one state. *)
  cs_step  : cs_state -> cs_instr -> cs_state;

  (** The cost function: how much does executing this instruction cost? *)
  cs_cost  : cs_instr -> nat;

  (** The certification indicator: is this state certified? *)
  cs_cert  : cs_state -> bool;

  (** *** AXIOM A2: The certification transition has cost ≥ 1. ***

      Going from uncertified to certified in a SINGLE step requires that
      the instruction executing that step has cost ≥ 1.

      This is the formal content of "No Free Certification":
        - You cannot certify for free.
        - Any system where A2 fails has "free forgery" — it can certify
          without spending anything, which is not honest accounting.

      Physical reading: measurement, proof verification, or consensus
      finalization all require performing work.  A2 names this formally.
  *)
  cs_cert_costs :
    forall (s : cs_state) (i : cs_instr),
      cs_cert s = false ->
      cs_cert (cs_step s i) = true ->
      cs_cost i >= 1;
}.

(** =========================================================================
    PART 2: TRACE EXECUTION AND TOTAL COST
    =========================================================================
*)

(** Execute a list of instructions on a CertificationSystem.
    Left-fold: instructions applied in list order. *)
Fixpoint cs_run (CS : CertificationSystem)
                (trace : list (cs_instr CS))
                (s : cs_state CS) : cs_state CS :=
  match trace with
  | []        => s
  | i :: rest => cs_run CS rest (cs_step CS s i)
  end.

(** Total cost of a trace: sum of per-instruction costs. *)
Fixpoint cs_total_cost (CS : CertificationSystem)
                       (trace : list (cs_instr CS)) : nat :=
  match trace with
  | []        => 0
  | i :: rest => cs_cost CS i + cs_total_cost CS rest
  end.

(** =========================================================================
    PART 3: THE UNIVERSAL THEOREM
    =========================================================================

    universal_nfi_any_substrate:

    For ANY CertificationSystem CS satisfying A2 (cs_cert_costs),
    any trace from an uncertified initial state to a certified final state
    has total cost ≥ 1.

    PROOF STRUCTURE:
    Induction on the trace.
    - Base: empty trace — cert cannot go from false to true → contradiction.
    - Step (i :: rest):
        Case A: i certifies (cert goes false→true at step 1).
          → A2 gives cost i ≥ 1.
          → total_cost (i::rest) = cost i + total_cost rest ≥ 1.
        Case B: i does not certify (cert still false after i).
          → cert must be set somewhere in rest.
          → IH on rest gives total_cost rest ≥ 1.
          → total_cost (i::rest) = cost i + total_cost rest ≥ 0 + 1 = 1.

    NOTE: The proof does NOT require cert monotonicity.
    The single axiom A2 (cs_cert_costs) is sufficient.
*)

Theorem universal_nfi_any_substrate :
  forall (CS : CertificationSystem)
         (trace : list (cs_instr CS))
         (s0 : cs_state CS),
    (** Precondition: start uncertified *)
    cs_cert CS s0 = false ->
    (** Postcondition: end certified *)
    cs_cert CS (cs_run CS trace s0) = true ->
    (** Conclusion: total cost of the trace is ≥ 1 *)
    cs_total_cost CS trace >= 1.
Proof.
  intros CS.
  induction trace as [| i rest IH]; intros s0 Hfalse Htrue.
  - (* Base: empty trace. cs_run returns s0. cert(s0) = false ≠ true. *)
    simpl in Htrue. rewrite Hfalse in Htrue. discriminate.
  - (* Step: trace = i :: rest. *)
    simpl in Htrue. simpl.
    (* Does instruction i certify? *)
    destruct (cs_cert CS (cs_step CS s0 i)) eqn:Hstep.
    + (** Case A: cert becomes true after i.
          cert(s0) = false and cert(step s0 i) = true.
          By A2: cost i ≥ 1. *)
      pose proof (cs_cert_costs CS s0 i Hfalse Hstep).
      lia.
    + (** Case B: cert still false after i.
          cert must be set in the rest of the trace.
          IH gives total_cost rest ≥ 1. *)
      specialize (IH (cs_step CS s0 i) Hstep Htrue).
      lia.
Qed.

(** Corollary: if the trace certifies from a false-start, the trace is nonempty.
    (Follows from base case: empty trace can't certify.) *)
Corollary cert_trace_nonempty :
  forall (CS : CertificationSystem)
         (trace : list (cs_instr CS))
         (s0 : cs_state CS),
    cs_cert CS s0 = false ->
    cs_cert CS (cs_run CS trace s0) = true ->
    trace <> [].
Proof.
  intros CS trace s0 Hfalse Htrue Hempty.
  subst trace. simpl in Htrue. rewrite Hfalse in Htrue. discriminate.
Qed.

(** =========================================================================
    PART 4: THE THIELE VM AS AN INSTANCE — CHANNEL A
    =========================================================================

    Instantiation of CertificationSystem for the Thiele VM's
    csr_cert_addr channel (thiele_cert_bool = csr_cert_addr ≠ 0).

    A2 is discharged by no_free_certification from AbstractNoFI.v:
      ∀ s i, cert_addr = 0 → cert_addr after ≠ 0 → instruction_cost i ≥ 1
*)

(** thiele_cs_A: The Thiele VM as a CertificationSystem, cert_addr channel. *)
Definition thiele_cert_addr_system : CertificationSystem :=
  {|
    cs_state := VMState;
    cs_instr := vm_instruction;
    cs_step  := vm_apply;
    cs_cost  := instruction_cost;
    cs_cert  := thiele_cert_bool;

    (** A2: discharged by no_free_certification *)
    cs_cert_costs :=
      fun s i Hfalse Htrue =>
        no_free_certification s i
          (proj1 (thiele_cert_bool_zero_iff s) Hfalse)
          (proj1 (thiele_cert_bool_nonzero_iff (vm_apply s i)) Htrue)
  |}.

(** Theorem: Thiele VM (cert_addr channel) satisfies universal NoFI. *)
Theorem thiele_universal_nfi_cert_addr :
  forall (trace : list vm_instruction) (s0 : VMState),
    thiele_cert_bool s0 = false ->
    thiele_cert_bool (cs_run thiele_cert_addr_system trace s0) = true ->
    cs_total_cost thiele_cert_addr_system trace >= 1.
Proof.
  intros trace s0 Hfalse Htrue.
  exact (universal_nfi_any_substrate thiele_cert_addr_system trace s0 Hfalse Htrue).
Qed.

(** =========================================================================
    PART 5: THE THIELE VM AS AN INSTANCE — CHANNEL B
    =========================================================================

    Instantiation for the vm_certified channel (CERTIFY opcode).

    A2 is discharged by no_free_certification_certified from AbstractNoFI.v:
      ∀ s i, vm_certified = false → vm_certified after = true →
             instruction_cost i ≥ 1
*)

(** thiele_cs_B: The Thiele VM as a CertificationSystem, vm_certified channel. *)
Definition thiele_certified_system : CertificationSystem :=
  {|
    cs_state := VMState;
    cs_instr := vm_instruction;
    cs_step  := vm_apply;
    cs_cost  := instruction_cost;
    cs_cert  := (fun s => s.(vm_certified));

    (** A2: discharged by no_free_certification_certified *)
    cs_cert_costs := no_free_certification_certified
  |}.

(** Theorem: Thiele VM (vm_certified channel) satisfies universal NoFI. *)
Theorem thiele_universal_nfi_certified :
  forall (trace : list vm_instruction) (s0 : VMState),
    s0.(vm_certified) = false ->
    (cs_run thiele_certified_system trace s0).(vm_certified) = true ->
    cs_total_cost thiele_certified_system trace >= 1.
Proof.
  intros trace s0 Hfalse Htrue.
  exact (universal_nfi_any_substrate thiele_certified_system trace s0 Hfalse Htrue).
Qed.

(** =========================================================================
    PART 6: WHAT THE UNIVERSAL THEOREM SAYS
    =========================================================================

    The theorem is substrate-independent in the following sense:

    ANY system satisfying A2 (cs_cert_costs) is subject to this theorem.
    A2 says: the moment of certification costs ≥ 1.

    For the Thiele VM: cost = instruction_cost (vm_mu accounting).
    For a proof assistant: cost = proof term length (Kolmogorov-adjacent).
    For a consensus protocol: cost = computational work (hashcash etc).
    For a physical measurement: cost = thermodynamic work (Landauer).
    For a neural network: cost = training compute.

    The theorem does not depend on WHAT the cost measures — only that the
    certification transition is non-free.

    WHY A2 IS MINIMAL:
    A2 cannot be weakened further while retaining the conclusion.
    If A2 fails — if there exists a state s and instruction i with
      cs_cert s = false, cs_cert (cs_step s i) = true, cs_cost i = 0
    then the system has "free certification."  Running that single
    instruction certifies for free, and the trace has total cost 0.
    The theorem would be false.

    So A2 is exactly the right minimal condition.

    =========================================================================
    STATUS: Zero Admitted.  Zero project-local axioms beyond cs_cert_costs,
    which is a STRUCTURAL REQUIREMENT of CertificationSystem, not an axiom
    about any particular system.  Each instance discharges it by proof.
    =========================================================================

    NEXT: Axiom 5 — quantitative bound.
    The gap remaining after this file:

        ∃ trace s0.  cs_cert (cs_run CS trace s0) = true  ∧
                     cs_total_cost CS trace < K(certificate)

    Closing this requires adding a witness complexity measure to
    CertificationSystem and proving that cost ≥ complexity(witness).
    That is the content of Axiom 5 and the next phase of work.
*)

(** =========================================================================
    PART 7: REPRESENTATION THEOREM — SIMULATING CERTIFICATION SYSTEMS
    =========================================================================

    Any CertificationSystem with a simulation morphism into the Thiele VM
    is "faithfully represented" by Thiele:

    (1) Cost lower bound (already from universal_nfi_any_substrate)
    (2) The embedded Thiele execution certifies (genuinely new content)

    The record adds a cert-reflection field connecting the external cert
    indicator to vm_certified of the embedded state.  Without this, one
    cannot derive part (2) from the embedding alone — the external system's
    notion of "certified" could be unrelated to Thiele's vm_certified.
*)

Record SimulatingCertificationSystem := {
  scs_base   : CertificationSystem ;
  scs_decode : scs_base.(cs_instr) -> vm_instruction ;
  scs_embed  : scs_base.(cs_state) -> VMState ;
  scs_step_commutes :
    forall (s : scs_base.(cs_state)) (i : scs_base.(cs_instr)),
      scs_embed (scs_base.(cs_step) s i) =
      vm_apply (scs_embed s) (scs_decode i) ;
  scs_cost_preserved :
    forall (i : scs_base.(cs_instr)),
      scs_base.(cs_cost) i >= instruction_cost (scs_decode i) ;
  scs_cert_reflects :
    forall (s : scs_base.(cs_state)),
      scs_base.(cs_cert) s = (scs_embed s).(vm_certified)
}.

(** Helper: cs_run embeds into fold_left vm_apply via scs_step_commutes. *)
Lemma scs_run_embed :
  forall (SCS : SimulatingCertificationSystem)
         (trace : list (SCS.(scs_base).(cs_instr)))
         (s0 : SCS.(scs_base).(cs_state)),
    SCS.(scs_embed) (cs_run SCS.(scs_base) trace s0) =
    fold_left vm_apply (map SCS.(scs_decode) trace) (SCS.(scs_embed) s0).
Proof.
  intros SCS trace.
  induction trace as [| i rest IH]; intros s0; simpl.
  - reflexivity.
  - rewrite IH. f_equal.
    exact (SCS.(scs_step_commutes) s0 i).
Qed.

(** THE REPRESENTATION THEOREM

    Part (1): cost lower bound — follows directly from universal_nfi_any_substrate
              applied to scs_base.  Not new, but included for completeness.

    Part (2): the embedded Thiele execution certifies.  This IS new.
              Uses scs_cert_reflects + scs_run_embed to transfer the
              external cert indicator into vm_certified of the embedded state.
*)
Theorem thiele_represents_simulating_cert_system :
  forall (SCS : SimulatingCertificationSystem)
         (s0  : SCS.(scs_base).(cs_state))
         (trace : list (SCS.(scs_base).(cs_instr))),
    SCS.(scs_base).(cs_cert) s0 = false ->
    SCS.(scs_base).(cs_cert) (cs_run SCS.(scs_base) trace s0) = true ->
    (* (1) cost lower bound *)
    cs_total_cost SCS.(scs_base) trace >= 1 /\
    (* (2) the execution embeds into a Thiele certified execution *)
    (fold_left vm_apply (map SCS.(scs_decode) trace)
       (SCS.(scs_embed) s0)).(vm_certified) = true.
Proof.
  intros SCS s0 trace Hpre Hpost.
  split.
  - (* Part 1: universal_nfi_any_substrate *)
    exact (universal_nfi_any_substrate SCS.(scs_base) trace s0 Hpre Hpost).
  - (* Part 2: embedded execution certifies *)
    rewrite <- scs_run_embed.
    rewrite <- SCS.(scs_cert_reflects).
    exact Hpost.
Qed.

(** Thiele itself is trivially a SimulatingCertificationSystem (identity morphism). *)
Definition thiele_self_simulating : SimulatingCertificationSystem :=
  {| scs_base   := thiele_certified_system ;
     scs_decode := fun i => i ;
     scs_embed  := fun s => s ;
     scs_step_commutes := fun _ _ => eq_refl ;
     scs_cost_preserved := fun _ => le_n _ ;
     scs_cert_reflects  := fun _ => eq_refl |}.

(** =========================================================================
    PART 8: CERTIFIED-COST MACHINE CATEGORY AND INITIALITY
    =========================================================================

    Defines a category of certified-cost machines (objects = CertCostMachine,
    morphisms = CertCostMorphism) and proves that the Thiele VM is an
    initial object: there is a unique morphism from Thiele to any other
    machine in the category.

    DESIGN:
    - CertCostMachine uses vm_instruction as the instruction type
      (morphisms preserve instructions literally, only mapping states).
    - Thiele is initial because vm_apply is the canonical step function:
      any other machine M with the same instruction set has a unique
      simulation from Thiele via the identity on instructions.
    - Uniqueness follows from step-commutation: any morphism phi must
      satisfy phi(vm_apply s i) = M.step (phi s) i for all s, i.
      Given a starting state, this determines phi on all reachable states.

    CAVEAT:
    Full uniqueness (exists! phi. ...) requires that the morphism map is
    uniquely determined on ALL states, not just reachable ones.  We prove:
    - Existence of a morphism (assuming M provides a witness map)
    - Agreement on reachable states (any two morphisms agree on traces)
    The stronger unique-on-all-states version would need state surjectivity
    or a reachability restriction on the category.
*)

(** CertCostMachine: a system with the Thiele instruction set,
    a step function, a cost function, a cert indicator, and the
    A2 axiom (cert costs >= 1). *)
Record CertCostMachine := {
  ccm_state  : Type ;
  ccm_step   : ccm_state -> vm_instruction -> ccm_state ;
  ccm_cost   : vm_instruction -> nat ;
  ccm_cert   : ccm_state -> bool ;
  ccm_cert_costs :
    forall (s : ccm_state) (i : vm_instruction),
      ccm_cert s = false ->
      ccm_cert (ccm_step s i) = true ->
      ccm_cost i >= 1
}.

(** CertCostMorphism: simulation between CertCostMachines.
    Maps states, commutes with step, and preserves cost lower bounds. *)
Record CertCostMorphism (M N : CertCostMachine) := {
  ccm_map : M.(ccm_state) -> N.(ccm_state) ;
  ccm_map_step :
    forall (s : M.(ccm_state)) (i : vm_instruction),
      ccm_map (M.(ccm_step) s i) = N.(ccm_step) (ccm_map s) i ;
  ccm_map_cert :
    forall (s : M.(ccm_state)),
      M.(ccm_cert) s = N.(ccm_cert) (ccm_map s)
}.

(** The Thiele VM as a CertCostMachine. *)
Definition thiele_cert_cost_machine : CertCostMachine :=
  {| ccm_state      := VMState ;
     ccm_step       := vm_apply ;
     ccm_cost       := instruction_cost ;
     ccm_cert       := fun s => s.(vm_certified) ;
     ccm_cert_costs := no_free_certification_certified |}.

(** EXISTENCE: For any CertCostMachine M with a simulation map from Thiele,
    the map is a CertCostMorphism. *)
Theorem thiele_morphism_exists :
  forall (M : CertCostMachine)
         (phi : VMState -> M.(ccm_state))
         (Hstep : forall s i, phi (vm_apply s i) = M.(ccm_step) (phi s) i)
         (Hcert : forall s, s.(vm_certified) = M.(ccm_cert) (phi s)),
    CertCostMorphism thiele_cert_cost_machine M.
Proof.
  intros M phi Hstep Hcert.
  exact (Build_CertCostMorphism thiele_cert_cost_machine M phi Hstep Hcert).
Qed.

(** AGREEMENT ON REACHABLE STATES: Any two morphisms from Thiele to M
    that agree on an initial state agree on all states reachable from it.
    This is reachability-restricted uniqueness. *)
Theorem thiele_morphism_unique_on_traces :
  forall (M : CertCostMachine)
         (phi1 phi2 : CertCostMorphism thiele_cert_cost_machine M)
         (s0 : VMState)
         (trace : list vm_instruction),
    ccm_map _ _ phi1 s0 = ccm_map _ _ phi2 s0 ->
    ccm_map _ _ phi1 (fold_left vm_apply trace s0) =
    ccm_map _ _ phi2 (fold_left vm_apply trace s0).
Proof.
  intros M phi1 phi2 s0 trace Hinit.
  revert s0 Hinit.
  induction trace as [| i rest IH]; intros s0 Hinit; simpl.
  - exact Hinit.
  - apply IH.
    change (vm_apply s0 i) with (ccm_step thiele_cert_cost_machine s0 i).
    rewrite (ccm_map_step _ _ phi1 s0 i).
    rewrite (ccm_map_step _ _ phi2 s0 i).
    rewrite Hinit.
    reflexivity.
Qed.

(** IDENTITY MORPHISM: Thiele has an identity morphism to itself. *)
Definition thiele_id_morphism : CertCostMorphism thiele_cert_cost_machine thiele_cert_cost_machine :=
  Build_CertCostMorphism thiele_cert_cost_machine thiele_cert_cost_machine
    (fun s => s) (fun _ _ => eq_refl) (fun _ => eq_refl).

(** CertCostMachine lifts to CertificationSystem. *)
Definition ccm_to_cert_system (M : CertCostMachine) : CertificationSystem :=
  {| cs_state := M.(ccm_state) ;
     cs_instr := vm_instruction ;
     cs_step  := M.(ccm_step) ;
     cs_cost  := M.(ccm_cost) ;
     cs_cert  := M.(ccm_cert) ;
     cs_cert_costs := M.(ccm_cert_costs) |}.

(** Every CertCostMachine satisfies universal NoFI. *)
Corollary ccm_universal_nfi :
  forall (M : CertCostMachine)
         (trace : list vm_instruction)
         (s0 : M.(ccm_state)),
    M.(ccm_cert) s0 = false ->
    M.(ccm_cert) (cs_run (ccm_to_cert_system M) trace s0) = true ->
    cs_total_cost (ccm_to_cert_system M) trace >= 1.
Proof.
  intros M trace s0 Hpre Hpost.
  exact (universal_nfi_any_substrate (ccm_to_cert_system M) trace s0 Hpre Hpost).
Qed.
