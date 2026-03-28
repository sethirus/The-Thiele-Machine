(** * BlindnessRepresentation: The forgetful map as formal "Turing-style blindness"

    WHY THIS FILE EXISTS:
    A Turing machine is "blind" to Thiele structure not merely as rhetoric
    but as a provable consequence of what a forgetful map loses. This file
    formalizes that blindness precisely:

    - Define forget : VMState → TMSnapshot, dropping all Thiele-specific fields.
    - Show forget is non-injective (there exist states it cannot distinguish).
    - Characterize the kernel of forget exactly: two states have the same
      image iff they agree on pc, mu, registers, and memory.
    - Show forget is surjective: every classical state has a Thiele preimage.

    These four facts together constitute the REPRESENTATION THEOREM FOR
    BLINDNESS: the classical observer sees a quotient of Thiele state-space
    by the equivalence relation eq_on_classical, and the quotient map is
    exactly forget.

    COMPARISON WITH PartitionSeparation.v:
    PartitionSeparation.v shows an instruction-set separation (partition ops
    are semantic in Thiele but syntactic in TM). This file shows something
    orthogonal: the STATE SPACE is richer, and the richness is not recoverable
    from the classical view.

    NO AXIOMS. NO ADMITS. All proofs are constructive.
*)

From Coq Require Import List Bool Arith.PeanoNat.
Import ListNotations.

From Kernel Require Import VMState.
From Kernel Require Import ThieleTraceProjection.

(* ================================================================= *)
(** ** I.  The forgetful map                                         *)
(* ================================================================= *)

(** TMSnapshot: the classical Turing-machine-visible state.
    This is isomorphic to ClassicalSnapshot from ThieleTraceProjection.v,
    but named to emphasize the Turing-machine perspective. *)
Record TMSnapshot := mkTMSnapshot {
  tms_pc   : nat;
  tms_mu   : nat;
  tms_regs : list nat;
  tms_mem  : list nat
}.

(** forget: the forgetful map from Thiele state to Turing-machine state.

    Drops: vm_graph, vm_csrs, vm_mu_tensor, vm_err, vm_logic_acc,
           vm_mstatus, vm_witness, vm_certified.

    Retains: vm_pc, vm_mu, vm_regs, vm_mem. *)
Definition forget (s : VMState) : TMSnapshot :=
  {| tms_pc   := s.(vm_pc);
     tms_mu   := s.(vm_mu);
     tms_regs := s.(vm_regs);
     tms_mem  := s.(vm_mem) |}.

(* ================================================================= *)
(** ** II.  The equivalence relation induced by forget               *)
(* ================================================================= *)

(** Two Thiele states are classically equivalent if they agree on all
    fields that survive the forgetful map. *)
Definition eq_on_classical (s1 s2 : VMState) : Prop :=
  s1.(vm_pc)   = s2.(vm_pc)   /\
  s1.(vm_mu)   = s2.(vm_mu)   /\
  s1.(vm_regs) = s2.(vm_regs) /\
  s1.(vm_mem)  = s2.(vm_mem).

(** eq_on_classical is an equivalence relation. *)

Lemma eq_on_classical_refl : forall s, eq_on_classical s s.
Proof. intro s. unfold eq_on_classical. tauto. Qed.

Lemma eq_on_classical_sym :
  forall s1 s2, eq_on_classical s1 s2 -> eq_on_classical s2 s1.
Proof.
  intros s1 s2 [H1 [H2 [H3 H4]]].
  unfold eq_on_classical. repeat split; symmetry; assumption.
Qed.

Lemma eq_on_classical_trans :
  forall s1 s2 s3,
    eq_on_classical s1 s2 ->
    eq_on_classical s2 s3 ->
    eq_on_classical s1 s3.
Proof.
  intros s1 s2 s3 [H1 [H2 [H3 H4]]] [H5 [H6 [H7 H8]]].
  unfold eq_on_classical. repeat split; congruence.
Qed.

(* ================================================================= *)
(** ** III.  Theorem 3A: Kernel characterization                     *)
(* ================================================================= *)

(** [forget_sound]: formal specification.
    forget is sound: eq_on_classical implies same forget image. *)
Theorem forget_sound :
  forall s1 s2 : VMState,
    eq_on_classical s1 s2 ->
    forget s1 = forget s2.
Proof.
  intros s1 s2 [Hpc [Hmu [Hregs Hmem]]].
  unfold forget.
  f_equal; assumption.
Qed.

(** [forget_complete]: formal specification.
    forget is complete: same forget image implies eq_on_classical.

    The kernel of forget is EXACTLY eq_on_classical — no more, no less.
    This pins down precisely which information is lost by the forgetful map. *)
Theorem forget_complete :
  forall s1 s2 : VMState,
    forget s1 = forget s2 ->
    eq_on_classical s1 s2.
Proof.
  intros s1 s2 Heq.
  unfold eq_on_classical.
  unfold forget in Heq.
  injection Heq as Hpc Hmu Hregs Hmem.
  exact (conj Hpc (conj Hmu (conj Hregs Hmem))).
Qed.

(** REPRESENTATION THEOREM: forget s1 = forget s2 ↔ eq_on_classical s1 s2.
    The classical observer's inability to distinguish two states is exactly
    characterized by eq_on_classical. *)
Theorem forget_kernel_is_eq_on_classical :
  forall s1 s2 : VMState,
    forget s1 = forget s2 <-> eq_on_classical s1 s2.
Proof.
  intros s1 s2.
  split.
  - exact (forget_complete s1 s2).
  - exact (forget_sound s1 s2).
Qed.

(* ================================================================= *)
(** ** IV.  Theorem 3B: Non-injectivity (constructive blindness)     *)
(* ================================================================= *)

(** The two witnesses from ThieleTraceProjection have the same forget image. *)
Lemma forget_A_eq_B :
  forget trace_witness_A = forget trace_witness_B.
Proof. reflexivity. Qed.

(** forget_witness_uncert: same classical fields as trace_witness_A,
    but vm_certified = false. Used to show certification is in the kernel. *)
Definition forget_witness_uncert : VMState :=
  {| vm_graph     := empty_graph;
     vm_csrs      := example_csr;
     vm_regs      := [42; 0; 0; 0];
     vm_mem       := [0; 0; 0; 0];
     vm_pc        := 10;
     vm_mu        := 5;
     vm_mu_tensor := vm_mu_tensor_default;
     vm_err       := false;
     vm_logic_acc := 0;
     vm_mstatus   := 0;
     vm_witness   := {| wc_same_00 := 3; wc_diff_00 := 1;
                        wc_same_01 := 0; wc_diff_01 := 0;
                        wc_same_10 := 0; wc_diff_10 := 0;
                        wc_same_11 := 0; wc_diff_11 := 0 |};
     vm_certified := false |}.

(** [blindness_non_injective]: formal specification.

    The forgetful map is NOT injective: different Thiele states can be
    indistinguishable to a classical observer. The information lost is
    precisely the Thiele-specific structure (witness counters, partition
    graph, certification flag, etc.). *)
Theorem blindness_non_injective :
  exists s1 s2 : VMState,
    s1 <> s2 /\
    forget s1 = forget s2.
Proof.
  exists trace_witness_A, trace_witness_B.
  exact (conj witnesses_A_B_distinct forget_A_eq_B).
Qed.

(** [what_is_lost]: formal specification.
    The fields lost by forget are exactly the complement of eq_on_classical.
    In particular, two states with the same forget image can differ in:
      - vm_witness (CHSH trial counters)
      - vm_certified (certification bit)
      - vm_graph (partition graph)
      - vm_csrs, vm_mu_tensor, vm_logic_acc, vm_mstatus, vm_err *)
Theorem what_is_lost :
  exists s1 s2 : VMState,
    forget s1 = forget s2 /\
    s1.(vm_witness) <> s2.(vm_witness).
Proof.
  exists trace_witness_A, trace_witness_B.
  split.
  - exact forget_A_eq_B.
  - intro Heq.
    assert (H : read_wc_same_00 trace_witness_A = read_wc_same_00 trace_witness_B)
      by (unfold read_wc_same_00; congruence).
    rewrite read_wc_A, read_wc_B in H.
    discriminate.
Qed.

(** Certification is also in the kernel of forget. *)
Theorem certification_is_lost :
  exists s1 s2 : VMState,
    forget s1 = forget s2 /\
    s1.(vm_certified) <> s2.(vm_certified).
Proof.
  exists trace_witness_A, forget_witness_uncert.
  split.
  - reflexivity.
  - discriminate.
Qed.

(* ================================================================= *)
(** ** V.  Theorem 3C: Surjectivity (every classical state has preimage) *)
(* ================================================================= *)

(** [forget_surjective]: formal specification.

    The forgetful map is SURJECTIVE: every classical TMSnapshot is the
    image of some Thiele VMState. The preimage is constructed by
    supplying zero-initialized Thiele-specific fields. *)
Theorem forget_surjective :
  forall snap : TMSnapshot,
    exists s : VMState, forget s = snap.
Proof.
  intro snap.
  (* Construct a minimal Thiele state with the given classical fields *)
  exists {| vm_graph     := empty_graph;
            vm_csrs      := example_csr;
            vm_regs      := snap.(tms_regs);
            vm_mem       := snap.(tms_mem);
            vm_pc        := snap.(tms_pc);
            vm_mu        := snap.(tms_mu);
            vm_mu_tensor := [];
            vm_err       := false;
            vm_logic_acc := 0;
            vm_mstatus   := 0;
            vm_witness   := witness_counts_zero;
            vm_certified := false |}.
  unfold forget.
  simpl.
  destruct snap as [pc mu regs mem].
  reflexivity.
Qed.

(* ================================================================= *)
(** ** VI.  Corollaries: the quotient picture                        *)
(* ================================================================= *)

(** The fiber over any TMSnapshot is non-trivial: it contains at least
    two elements (one certified, one not). *)
Theorem fiber_is_non_trivial :
  forall snap : TMSnapshot,
    exists s1 s2 : VMState,
      forget s1 = snap /\
      forget s2 = snap /\
      s1 <> s2.
Proof.
  intro snap.
  (* Certified preimage *)
  pose (sc := {| vm_graph     := empty_graph;
                 vm_csrs      := example_csr;
                 vm_regs      := snap.(tms_regs);
                 vm_mem       := snap.(tms_mem);
                 vm_pc        := snap.(tms_pc);
                 vm_mu        := snap.(tms_mu);
                 vm_mu_tensor := [];
                 vm_err       := false;
                 vm_logic_acc := 0;
                 vm_mstatus   := 0;
                 vm_witness   := witness_counts_zero;
                 vm_certified := true |}).
  (* Uncertified preimage *)
  pose (su := {| vm_graph     := empty_graph;
                 vm_csrs      := example_csr;
                 vm_regs      := snap.(tms_regs);
                 vm_mem       := snap.(tms_mem);
                 vm_pc        := snap.(tms_pc);
                 vm_mu        := snap.(tms_mu);
                 vm_mu_tensor := [];
                 vm_err       := false;
                 vm_logic_acc := 0;
                 vm_mstatus   := 0;
                 vm_witness   := witness_counts_zero;
                 vm_certified := false |}).
  exists sc, su.
  repeat split.
  - unfold forget, sc. simpl. destruct snap; reflexivity.
  - unfold forget, su. simpl. destruct snap; reflexivity.
  - intro Heq.
    (* sc and su differ only in vm_certified *)
    assert (Hcert : sc.(vm_certified) = su.(vm_certified)) by congruence.
    unfold sc, su in Hcert.
    simpl in Hcert.
    discriminate.
Qed.

(** Summary: forget is many-to-one and onto.
    The classical observer sees a proper quotient of Thiele state-space. *)
Theorem forget_is_many_to_one_surjection :
  (exists s1 s2 : VMState, s1 <> s2 /\ forget s1 = forget s2)  (* many-to-one *)
  /\
  (forall snap : TMSnapshot, exists s : VMState, forget s = snap). (* surjective *)
Proof.
  split.
  - exact blindness_non_injective.
  - exact forget_surjective.
Qed.
