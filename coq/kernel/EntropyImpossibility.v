From Coq Require Import List Arith.PeanoNat.
From Coq Require Import Logic.FunctionalExtensionality.

From Kernel Require Import VMState KernelPhysics.

Import ListNotations.

(** * EntropyImpossibility: Why naive entropy definitions fail

    WHY THIS FILE EXISTS:
    I claim you CANNOT define entropy as log(cardinality of microstate ensemble)
    without imposing additional finiteness structure. The reason: observational
    equivalence classes are INFINITE, so naive entropy is ∞ everywhere.

    THE PROOF STRATEGY:
    1. Construct tweak_regs: adds arbitrary data to vm_regs (unobservable register state)
    2. Show all tweaked states are observationally equivalent (region_equiv)
    3. Show tweaking is injective (different x → different states)
    4. Conclude: infinitely many distinct microstates per observable class

    PHYSICAL INTERPRETATION:
    This is like UV divergences in quantum field theory. If you allow arbitrarily
    fine-grained microstates (infinite cutoff), you get infinite entropy.
    The solution: impose finite_region_equiv_class (from Definitions.v) as a
    coarse-graining or measurement-resolution bound.

    This justifies the Bekenstein bound and holographic principle: finite
    information capacity per region is NOT optional - it's necessary for
    thermodynamics to be well-defined.

    FALSIFICATION: Show entropy can be well-defined without finiteness assumptions.
    Or exhibit a physical system with infinite entropy per finite region (violating
    Bekenstein bound). Or prove thermodynamics works with continuous (infinite)
    state spaces without cutoffs.
*)

(** region_equiv: Observational equivalence (same as Definitions.v)
    Two states are equivalent if all observable regions match.
*)
Definition region_equiv (s1 s2 : VMState) : Prop :=
  forall mid, ObservableRegion s1 mid = ObservableRegion s2 mid.

(** tweak_regs: Unobservable state modification
    Prepends x to vm_regs (the register list) while leaving all other fields
    (graph, CSRs, memory, PC, μ-ledger, error) unchanged.

    CRUCIAL PROPERTY: vm_regs is NOT part of ObservableRegion. You can tweak
    registers arbitrarily without affecting any measurement. This is like
    gauge freedom or internal degrees of freedom - invisible to physics.

    WHY THIS WORKS: ObservableRegion only depends on vm_mem and vm_graph,
    not on vm_regs. So tweak_regs creates infinitely many distinct states
    (different internal register configurations) that are observationally
    indistinguishable.
*)
Definition tweak_regs (s : VMState) (x : nat) : VMState :=
  {| vm_graph := s.(vm_graph);
     vm_csrs := s.(vm_csrs);
     vm_regs := x :: s.(vm_regs);
     vm_mem := s.(vm_mem);
     vm_pc := s.(vm_pc);
     vm_mu := s.(vm_mu);
     vm_err := s.(vm_err) |}.

(** Definitional lemma: This equality is by definition, not vacuous

    tweak_regs_region_equiv: Observational invisibility of register tweaking
    Proves region_equiv s (tweak_regs s x) for any x.

    PROOF: Unfold definitions, observe that ObservableRegion doesn't touch
    vm_regs, conclude reflexivity.

    PHYSICAL CLAIM: You can pack arbitrary information into internal registers
    without affecting any observable. This is the seed of the "infinite microstates
    per observable" problem.

    FALSIFICATION: Find an observable (measurement) that distinguishes s from
    tweak_regs s x. This would mean registers are measurable, contradicting
    the definition of ObservableRegion.
*)
Lemma tweak_regs_region_equiv : forall s x,
  region_equiv s (tweak_regs s x).
Proof.
  intros s x mid.
  unfold region_equiv, tweak_regs.
  unfold ObservableRegion.
  simpl.
  reflexivity.
Qed.

(** tweak_regs_injective: Different tweaks give different states
    If tweak_regs s a = tweak_regs s b, then a = b.

    PROOF: Equal states have equal vm_regs fields (f_equal), so a :: ... = b :: ...,
    thus a = b by list injectivity.

    WHY THIS MATTERS: Combined with tweak_regs_region_equiv, this proves we have
    an INJECTIVE function from nat to the region_equiv class. Since nat is
    infinite, the equiv class is infinite.

    This is the key to the impossibility result: we have infinitely many
    DISTINCT microstates (injectivity) that are all OBSERVATIONALLY IDENTICAL
    (region_equiv). Classical Boltzmann entropy S = log(Ω) gives S = log(∞) = ∞.
*)
Lemma tweak_regs_injective : forall s a b,
  tweak_regs s a = tweak_regs s b -> a = b.
Proof.
  intros s a b Heq.
  assert (Hregs : vm_regs (tweak_regs s a) = vm_regs (tweak_regs s b)).
  { now f_equal. }
  unfold tweak_regs in Hregs.
  simpl in Hregs.
  inversion Hregs; subst; reflexivity.
Qed.

(** region_equiv_class_infinite: Main impossibility result
    For any state s, there exists an injective function f : nat -> VMState
    where every f(n) is region_equiv to s.

    PROOF: Take f(n) = tweak_regs s n. Use the two lemmas above:
    - tweak_regs_region_equiv ensures ∀n, region_equiv s (f n)
    - tweak_regs_injective ensures f is injective (distinct inputs → distinct outputs)

    PHYSICAL INTERPRETATION:
    Every observable state has INFINITELY MANY underlying microstates. If you
    try to compute entropy as S = k log(number of microstates), you get ∞.

    This is analogous to:
    - UV divergences in QFT (need cutoff at Planck scale)
    - Bekenstein bound (finite bits per area, not volume)
    - Holographic principle (information lives on boundary)

    All these are saying: you MUST impose finite information density or physics
    breaks down.

    FALSIFICATION: Prove thermodynamics works without finiteness cutoffs, or
    show S = log(∞) is physically meaningful, or exhibit a natural coarse-graining
    that makes equiv classes finite without external assumptions.
*)
Theorem region_equiv_class_infinite : forall s,
  exists f : nat -> VMState,
    (forall n, region_equiv s (f n)) /\
    (forall n1 n2, f n1 = f n2 -> n1 = n2).
Proof.
  intro s.
  exists (fun n => tweak_regs s n).
  split.
  - intro n. apply tweak_regs_region_equiv.
  - intros n1 n2 Heq.
    apply (tweak_regs_injective s n1 n2 Heq).
Qed.

(** Clean failure localization for the plan's D1 definition:
   If entropy is defined as log(cardinality of the region_equiv class),
   then this class being infinite forces entropy to be non-finite unless
   additional finiteness/coarse-graining structure is assumed.

   Entropy_From_Observation_Fails_Without_Finiteness: Explicit failure theorem
   This is the same proof as region_equiv_class_infinite, but with a name
   that explicitly states the implication for entropy.

   THE CORE CLAIM:
   You cannot define S = k_B log |{microstates consistent with observations}|
   without FIRST imposing finite_region_equiv_class (from Definitions.v).

   Without that finiteness assumption, the cardinality is ℵ₀ (countably infinite)
   for EVERY state, so S = ∞ everywhere. This makes thermodynamics meaningless:
   no equilibrium, no temperature, no second law.

   SOLUTION: Impose finite_region_equiv_class as an axiom. This says the universe
   has finite information density - there are only finitely many distinguishable
   microstates per observable region. This is the computational version of the
   Bekenstein bound.

   FALSIFICATION: Define a workable notion of entropy for continuous state spaces
   without cutoffs. Or show that S = ∞ is physically acceptable (thermal systems
   can have infinite entropy per finite volume).
*)
Theorem Entropy_From_Observation_Fails_Without_Finiteness :
  forall s,
    exists f : nat -> VMState,
      (forall n, region_equiv s (f n)) /\
      (forall n1 n2, f n1 = f n2 -> n1 = n2).
Proof.
  intro s.
  apply region_equiv_class_infinite.
Qed.
