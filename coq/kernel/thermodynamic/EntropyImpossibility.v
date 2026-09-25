From Coq Require Import List Arith.PeanoNat.
From Coq Require Import Logic.FunctionalExtensionality.

From Kernel Require Import VMState KernelPhysics.

Import ListNotations.

(** EntropyImpossibility studies one selected observation map. Because
    [ObservableRegion] omits [vm_regs], prepending an arbitrary natural to that
    field gives infinitely many distinct [VMState] preimages of the same
    region-level observation. Therefore a cardinality-based entropy over these
    raw fibers is not finite without an explicit quotient, cutoff, or other
    finiteness premise. This is an observation-model result, not a theorem
    about all entropy definitions or physical systems. *)

(** region_equiv: two states are observationally equivalent when every
    ObservableRegion agrees. *)
Definition region_equiv (s1 s2 : VMState) : Prop :=
  forall mid, ObservableRegion s1 mid = ObservableRegion s2 mid.

(** [tweak_regs] prepends a natural to [vm_regs] and leaves the other VM fields
    unchanged. Since [ObservableRegion] reads [vm_mem] and [vm_graph] rather
    than [vm_regs], this construction supplies the observation-equivalent
    family used by the impossibility theorem. *)
Definition tweak_regs (s : VMState) (x : nat) : VMState :=
  {| vm_graph := s.(vm_graph);
     vm_csrs := s.(vm_csrs);
     vm_regs := x :: s.(vm_regs);
     vm_mem := s.(vm_mem);
     vm_pc := s.(vm_pc);
     vm_mu := s.(vm_mu);
     vm_mu_tensor := s.(vm_mu_tensor);
     vm_err := s.(vm_err);
     vm_logic_acc := s.(vm_logic_acc);
     vm_mstatus := s.(vm_mstatus);
     vm_witness := s.(vm_witness);
     vm_certified := s.(vm_certified) |}.

(** Note: the previous helper [tweak_regs_region_equiv] (which stated
    that [region_equiv s (tweak_regs s x)] holds for every [s], [x])
    was inlined at its single use site in
    [region_equiv_class_infinite] below. Conceptually the equivalence
    reflects that [ObservableRegion] ignores [vm_regs] entirely, so
    register tweaking is invisible to any region-level observer — this
    is the seed of the infinite-microstates-per-observable problem
    closed by [region_equiv_class_infinite]. *)

(** [tweak_regs_injective] shows that distinct natural inputs produce distinct
    full states. Together with region equivalence, it supplies an injective
    infinite family in one fiber of the selected observation. *)
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

(** [region_equiv_class_infinite] gives the injective observation-equivalent
    family for every state. Any entropy definition based on the cardinality of
    this raw fiber therefore needs an additional finiteness or coarse-graining
    convention. *)
Theorem region_equiv_class_infinite : forall s,
  exists f : nat -> VMState,
    (forall n, region_equiv s (f n)) /\
    (forall n1 n2, f n1 = f n2 -> n1 = n2).
Proof.
  intro s.
  exists (fun n => tweak_regs s n).
  split.
  - intros n mid.
    unfold region_equiv, tweak_regs.
    unfold ObservableRegion.
    simpl.
    reflexivity.
  - intros n1 n2 Heq.
    apply (tweak_regs_injective s n1 n2 Heq).
Qed.

(** The named entropy corollary repeats the same fiber result with the
   interpretation made explicit: the raw [region_equiv] class is infinite, so a
   finite cardinality-based entropy requires an extra finiteness convention. It
   does not rule out other entropy constructions. *)
Theorem Entropy_From_Observation_Fails_Without_Finiteness :
  forall s,
    exists f : nat -> VMState,
      (forall n, region_equiv s (f n)) /\
      (forall n1 n2, f n1 = f n2 -> n1 = n2).
Proof.
  intro s.
  apply region_equiv_class_infinite.
Qed.
