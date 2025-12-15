From Coq Require Import List Arith.PeanoNat.
From Coq Require Import Logic.FunctionalExtensionality.

From Kernel Require Import VMState KernelPhysics.

Import ListNotations.

Definition region_equiv (s1 s2 : VMState) : Prop :=
  forall mid, ObservableRegion s1 mid = ObservableRegion s2 mid.

Definition tweak_regs (s : VMState) (x : nat) : VMState :=
  {| vm_graph := s.(vm_graph);
     vm_csrs := s.(vm_csrs);
     vm_regs := x :: s.(vm_regs);
     vm_mem := s.(vm_mem);
     vm_pc := s.(vm_pc);
     vm_mu := s.(vm_mu);
     vm_err := s.(vm_err) |}.

Lemma tweak_regs_region_equiv : forall s x,
  region_equiv s (tweak_regs s x).
Proof.
  intros s x mid.
  unfold region_equiv, tweak_regs.
  unfold ObservableRegion.
  simpl.
  reflexivity.
Qed.

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

(* Clean failure localization for the plan's D1 definition:
   If entropy is defined as log(cardinality of the region_equiv class),
   then this class being infinite forces entropy to be non-finite unless
   additional finiteness/coarse-graining structure is assumed.
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
