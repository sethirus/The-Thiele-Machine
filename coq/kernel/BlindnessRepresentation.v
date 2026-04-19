(** BlindnessRepresentation: the forgetful map as Turing-style blindness

    A Turing machine is "blind" to Thiele structure not merely as rhetoric
    but as a provable consequence of what a forgetful map loses. This file
    formalizes that blindness precisely:

    - Define forget : VMState → TMSnapshot, dropping all Thiele-specific fields.
    - Show forget is non-injective (there exist states it cannot distinguish).
    - Characterize the kernel of forget exactly: two states have the same
      image iff they agree on pc, mu, registers, and memory.
    - Show forget is surjective: every classical state has a Thiele preimage.

    These four facts are the representation theorem for blindness in this
    file: the classical observer sees the quotient of Thiele state-space by
    [eq_on_classical], and the quotient map is [forget].

    COMPARISON WITH PartitionSeparation.v:
    PartitionSeparation.v shows an instruction-set separation (partition ops
    are semantic in Thiele but syntactic in TM). This file shows something
    orthogonal: the STATE SPACE is richer, and the richness is not recoverable
    from the classical view.

    NO COQ AXIOMS. NO ADMITS. All proofs are constructive.
*)

From Coq Require Import List Bool Arith.PeanoNat.
Import ListNotations.

From Kernel Require Import VMState.
From Kernel Require Import ThieleTraceProjection.
From Kernel Require Import ShadowProjection.

(** The forgetful map. *)

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

(** The equivalence relation induced by [forget]. *)

(** Two Thiele states are classically equivalent if they agree on all
    fields that survive the forgetful map. *)
Definition eq_on_classical (s1 s2 : VMState) : Prop :=
  s1.(vm_pc)   = s2.(vm_pc)   /\
  s1.(vm_mu)   = s2.(vm_mu)   /\
  s1.(vm_regs) = s2.(vm_regs) /\
  s1.(vm_mem)  = s2.(vm_mem).

(** Reflexivity: a state agrees with itself on the classical fields. *)

Lemma eq_on_classical_refl : forall s, eq_on_classical s s.
Proof. intro s. unfold eq_on_classical. tauto. Qed.

(** Symmetry: if the classical fields match one way, they match the other way. *)
Lemma eq_on_classical_sym :
  forall s1 s2, eq_on_classical s1 s2 -> eq_on_classical s2 s1.
Proof.
  intros s1 s2 [H1 [H2 [H3 H4]]].
  unfold eq_on_classical. repeat split; symmetry; assumption.
Qed.

(** Transitivity: matching classical fields can be chained through a middle state. *)
Lemma eq_on_classical_trans :
  forall s1 s2 s3,
    eq_on_classical s1 s2 ->
    eq_on_classical s2 s3 ->
    eq_on_classical s1 s3.
Proof.
  intros s1 s2 s3 [H1 [H2 [H3 H4]]] [H5 [H6 [H7 H8]]].
  unfold eq_on_classical. repeat split; congruence.
Qed.

(** Kernel characterization. *)

(** [forget_sound]: states equivalent on classical fields have the same
    forgetful image. *)
Theorem forget_sound :
  forall s1 s2 : VMState,
    eq_on_classical s1 s2 ->
    forget s1 = forget s2.
Proof.
  intros s1 s2 [Hpc [Hmu [Hregs Hmem]]].
  unfold forget.
  f_equal; assumption.
Qed.

(** [forget_complete]: equal forgetful images agree on the classical fields.

    The kernel of forget is exactly [eq_on_classical], no more and no less.
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

(** Representation theorem: [forget s1 = forget s2] iff [eq_on_classical s1 s2].
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

(** Non-injectivity: constructive blindness. *)

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

(** [blindness_non_injective]: the forgetful map is not injective.
    Different Thiele states can be
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

(** [what_is_lost]: witness counters are invisible to [forget].
    This theorem only proves the witness-counter case. Certification gets its
    own witness below; other dropped fields follow from the definition but are
    not separately witnessed here. *)
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

(** Surjectivity: every classical snapshot has a preimage. *)

(** [forget_surjective]: every classical [TMSnapshot] is the
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

(** Corollaries: the quotient picture. *)

(** The fiber over any TMSnapshot is not a singleton: it contains at least
    two elements (one certified, one not). *)
Theorem fiber_has_two_preimages :
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

(** Bridge: [forget] and [shadow_proj] agree on shared fields. *)

(** [shadow_proj_and_forget_agree]: the two forgetful maps, [forget] in this
    file and [shadow_proj] in [ShadowProjection.v], agree on
    all shared fields (pc, mu, regs, mem).  shadow_proj additionally retains
    vm_err and vm_certified, which TMSnapshot does not track.

    This lemma is bookkeeping: it confirms that forget is the restriction of
    shadow_proj to the four tape-equivalent fields, so the two maps are
    mutually consistent.  A reviewer asking "are these the same map?" gets
    a machine-checked answer here.

    Proof: both sides reduce to the same record via reflexivity. *)
(* Definitional check: unfolding both maps produces reflexivity. *)
Lemma shadow_proj_and_forget_agree :
  forall s : VMState,
    forget s = {| tms_pc   := (shadow_proj s).(cs_pc);
                  tms_mu   := (shadow_proj s).(cs_mu);
                  tms_regs := (shadow_proj s).(cs_regs);
                  tms_mem  := (shadow_proj s).(cs_mem) |}.
Proof.
  intro s. unfold forget, shadow_proj. reflexivity.
Qed.
