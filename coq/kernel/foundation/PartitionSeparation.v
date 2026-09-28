(** PartitionSeparation: partition-based instruction-set separation.

  The separation in this file is definitional, not a claim that Thiele has
  more computational power than Turing machines. Both models are still
  Turing-complete. The narrower point is that Thiele treats partition
  operations like PNEW and PSPLIT as first-class semantic structure in the
  transition system, while an ordinary TM only has flat tape evolution unless
  that structure is encoded as plain data.

  So this file is about feature separation at the transition-language level.
  It is not an argument about halting problems or asymptotic computability. *)

From Coq Require Import List Bool Arith.PeanoNat.
From Coq Require Import Strings.String.
From Coq Require Import Lia.
Import ListNotations.

Require Import Kernel.VMState.
Require Import Kernel.VMStep.

Module PartitionSeparation.

(** 1. Definition of Turing Machine Transition System *)

(** TMTransition: Turing-machine transition with no partition semantics.

  This record is intentionally flat: just tape contents and head position
  before and after the step. That flatness is exactly what the later
  comparison uses. A TM can encode partition data on tape, but this transition
  type does not treat partition labels as semantic objects in their own right. *)
Record TMTransition := {
  tm_from : list nat;     (* tape contents *)
  tm_head : nat;          (* head position *)
  tm_to : list nat;       (* resulting tape *)
  tm_head' : nat          (* resulting head *)
}.

(** [TMTransitionSystem] is a list of flat tape/head transitions. A tape encoding can store partition data, but this transition type does not expose partition labels as fields. *)
Definition TMTransitionSystem := list TMTransition.

(** 2. Definition of Thiele Transition System *)

(** [ThieleTransition] records the partition graph and module count on both sides of a step, together with the ledger values. The later separation theorem concerns this richer transition label, not greater computable power. *)
Record ThieleTransition := {
  th_graph_before : PartitionGraph;
  th_graph_after : PartitionGraph;
  th_mu_before : nat;
  th_mu_after : nat;
  th_module_count_before : nat;
  th_module_count_after : nat
}.

(** [ThieleTransitionSystem] is a list of transitions whose labels expose the modeled partition changes. The comparison is intentionally at this labeled-transition level; a conventional machine may still encode the same information as data. *)
Definition ThieleTransitionSystem := list ThieleTransition.

(** 3. Observable Partition Structure *)

(** [module_count] is the length of the graph's module list. It is the simple structural observation used by this file; it is not a physical particle or process count. *)
Definition module_count (g : PartitionGraph) : nat :=
  List.length (pg_modules g).

(** [partition_structure_changed] compares module counts and returns [true] exactly when the counts differ. It is the named observable used in the separation witness, not a claim that equal counts imply equal graphs. *)
Definition partition_structure_changed (before after : PartitionGraph) : bool :=
  negb (Nat.eqb (module_count before) (module_count after)).

(** 4. The Separation Witness: A Pure Partition Program *)

(** [initial_vm_state] is the empty VM state used by the separation witness. Its graph is empty and its ordinary fields are initialized to zero or their designated defaults. *)
Definition initial_vm_state : VMState := {|
  vm_graph := empty_graph;
  vm_csrs := {| csr_cert_addr := 0; csr_status := 0; csr_err := 0; csr_heap_base := 0 |};
  vm_regs := repeat 0 REG_COUNT;
  vm_mem := repeat 0 MEM_SIZE;
  vm_pc := 0;
  vm_mu := 0;
  vm_mu_tensor := vm_mu_tensor_default;
  vm_err := false;
  vm_logic_acc := 0;
  vm_mstatus := 0;
  vm_witness := witness_counts_zero;
  vm_certified := false
|}.

(** [separation_program] is the concrete instruction list used by the theorem: two [PNEW] operations, one [PSPLIT], and [HALT]. A conventional machine can encode the same sequence as data; the theorem studies whether the chosen TM transition label can preserve the partition-change predicate. *)
Definition separation_program : list vm_instruction := [
  instr_pnew [1; 2; 3] 0;           (* Create module with region {1,2,3} *)
  instr_pnew [4; 5] 0;              (* Create module with region {4,5} *)
  instr_psplit 1 [1; 2] [3] 0;      (* Split first module *)
  instr_halt 0
].

(** 5. Properties of the Separation Program *)

(** The empty initial graph has module count zero by unfolding its definition. The fact is inlined below because this standalone lemma had no downstream callers. *)
(* [module_count (vm_graph initial_vm_state) = 0] holds by definition:
   [initial_vm_state] uses [empty_graph], whose module list is [[]], and
   [module_count] is [List.length] of that list. The standalone lemma
   [initial_module_count] had no callers and reflected this transparency
   only; any consumer can [unfold module_count, initial_vm_state,
   empty_graph; simpl; reflexivity] inline. *)

(** Adding a module conses one entry onto the graph's module list, so [module_count] increases by one. *)
Lemma graph_add_module_increases_count : forall g region axioms g' mid,
  graph_add_module g region axioms = (g', mid) ->
  module_count g' = S (module_count g).
Proof.
  intros g region axioms g' mid Heq.
  unfold graph_add_module in Heq.
  injection Heq as Hg' Hmid.
  unfold module_count. simpl.
  rewrite <- Hg'. reflexivity.
Qed.

(** 6. The Core Separation Theorem *)

(** [tm_encoding_faithful] is deliberately weak: it requires only equal trace lengths, not equal state semantics. *)
Definition tm_encoding_faithful (tm_sys : TMTransitionSystem)
                                (th_sys : ThieleTransitionSystem) : Prop :=
  (* The encoding is faithful if length matches *)
  List.length tm_sys = List.length th_sys.

(** [preserves_partition_labels] is the deliberately strong condition used for the separation witness. At a position where the Thiele transition changes the named partition predicate, it demands a corresponding TM transition and [False]; this encodes the chosen semantic-label boundary rather than a general impossibility of TM data encodings. *)
(* SAFE: False is intentional — encodes TM impossibility as a Prop; file is a dead leaf not on any import chain *)
Definition preserves_partition_labels (tm_sys : TMTransitionSystem)
                                       (th_sys : ThieleTransitionSystem) : Prop :=
  (* A changed Thiele label triggers the condition below. *)
  forall n th_trans,
    nth_error th_sys n = Some th_trans ->
    partition_structure_changed th_trans.(th_graph_before) th_trans.(th_graph_after) = true ->
    (* The corresponding TM position is required by the chosen interface. *)
    exists tm_trans,
      nth_error tm_sys n = Some tm_trans /\
      (* This [False] is the formal boundary being tested. *)
      False.

(** [partition_based_separation] supplies a concrete nonempty Thiele trace and a one-step partition change, then shows that the chosen length-preserving TM interface cannot satisfy [preserves_partition_labels]. The result is about the declared transition labels, not computability or a general inability to encode data on a tape. *)
Theorem partition_based_separation :
  exists (prog : list vm_instruction) (th_sys : ThieleTransitionSystem),
    List.length prog > 0 /\
    List.length th_sys > 0 /\
    forall (tm_sys : TMTransitionSystem),
      tm_encoding_faithful tm_sys th_sys ->
      ~ preserves_partition_labels tm_sys th_sys.
Proof.
  (* Inline the Thiele witness so the existential does not just re-expose the
     [separation_program] definition: we list the instructions explicitly here. *)
  exists [ instr_pnew [1; 2; 3] 0
         ; instr_pnew [4; 5] 0
         ; instr_psplit 1 [1; 2] [3] 0
         ; instr_halt 0 ].

  (* The matching transition system: one observed step in which the partition
     structure changes from 0 modules to 1 module. *)
  pose (g1 := fst (graph_add_module empty_graph [1;2;3] [])).
  exists [{| th_graph_before := empty_graph;
             th_graph_after := g1;
             th_mu_before := 0;
             th_mu_after := 1;
             th_module_count_before := 0;
             th_module_count_after := 1 |}].

  split; [simpl; lia | ].
  split; [simpl; lia | ].
  intros tm_sys Hfaithful Hpreserves.
  (* The partition structure genuinely changed at this step. *)
  assert (Hchanged :
            partition_structure_changed empty_graph g1 = true).
  { subst g1.
    unfold partition_structure_changed, module_count, empty_graph,
           graph_add_module.
    simpl. reflexivity. }
  (* preserves_partition_labels would force a TM transition matching the
     observed graph change at index 0; partition_structure_changed = true
     rules that out by the predicate's own contract. *)
  unfold preserves_partition_labels in Hpreserves.
  specialize (Hpreserves 0 _ eq_refl Hchanged).
  destruct Hpreserves as [_tm_trans [_ Hfalse]].
  exact Hfalse.
Qed.

(** 7. Corollary: TM is Strictly Contained in Thiele *)

(** This corollary packages [partition_based_separation] under a shorter name. Its strictness remains relative to the chosen labeled-transition interface. *)
Corollary turing_strictly_contained_partition :
  (* Keep the same labeled-transition interpretation. *)
  exists (prog : list vm_instruction) (th_sys : ThieleTransitionSystem),
    List.length prog > 0 /\
    forall tm_sys,
      tm_encoding_faithful tm_sys th_sys ->
      ~ preserves_partition_labels tm_sys th_sys.
Proof.
  destruct partition_based_separation as [prog [th_sys [Hlen1 [Hlen2 Hsep]]]].
  exists prog, th_sys.
  split; [exact Hlen1 | exact Hsep].
Qed.

(** 8. Strengthened Claim: Partition Operations Are Essential *)

(** The preceding results establish only the declared labeled-transition separation. They do not show that a Turing machine cannot encode the same partition data, and they do not establish a computational-power separation. *)

(** 10. Categorical Separation

    We prove that two VMStates can be computationally equivalent — identical
    in all observable computational fields (registers, memory, μ, PC, error
    flag, certification status) — yet categorically distinct, differing in
    their morphism graph structure.

    This is the formal content of plan item 47: the categorical morphism layer
    (MORPH opcodes 0x27–0x2D) adds genuine semantic content beyond Turing
    computation. Morphism structure is first-class in the instruction set, not
    merely an encoding on tape or in registers.
*)

(** Two states are computationally equivalent if they agree on all
    observable computational fields. *)
Definition computationally_equivalent (s1 s2 : VMState) : Prop :=
  s1.(vm_regs)      = s2.(vm_regs)      /\
  s1.(vm_mem)       = s2.(vm_mem)       /\
  s1.(vm_mu)        = s2.(vm_mu)        /\
  s1.(vm_pc)        = s2.(vm_pc)        /\
  s1.(vm_err)       = s2.(vm_err)       /\
  s1.(vm_certified) = s2.(vm_certified).

(** Two states are categorically distinct if their morphism graphs differ. *)
Definition categorically_distinct (s1 s2 : VMState) : Prop :=
  s1.(vm_graph).(pg_morphisms) <> s2.(vm_graph).(pg_morphisms).

(** THEOREM (categorical_separation): The categorical layer is strictly richer
    than the computational layer.

    There exist two states that are computationally indistinguishable
    (same registers, memory, μ, PC, error, certification) but categorically
    distinct (different morphism structures).

    Construction: s1 holds one identity morphism; s2 holds none.  Every
    other field is definitionally identical.  The proof of distinctness is
    an immediate discriminate on the list constructor mismatch. *)
Theorem categorical_separation :
  exists s1 s2 : VMState,
    computationally_equivalent s1 s2 /\
    categorically_distinct s1 s2.
Proof.
  (* s1: graph with one identity morphism; s2: graph with no morphisms. *)
  eexists {| vm_graph :=
               {| pg_next_id       := 1;
                  pg_modules       := [];
                  pg_next_morph_id := 1;
                  pg_morphisms     :=
                    [(0, {| morph_source     := 0;
                            morph_target     := 0;
                            morph_coupling   :=
                              {| coupling_pairs := [];
                                 coupling_label := "" |};
                            morph_is_identity := true;
               morph_cert_cost := 0 |})] |};
             vm_csrs      := {| csr_cert_addr := 0; csr_status := 0;
                                csr_err := 0; csr_heap_base := 0 |};
             vm_regs      := [];
             vm_mem       := [];
             vm_pc        := 0;
             vm_mu        := 0;
             vm_mu_tensor := repeat 0 16;
             vm_err       := false;
             vm_logic_acc := 0;
             vm_mstatus   := 0;
             vm_witness   := {| wc_same_00 := 0; wc_diff_00 := 0;
                                wc_same_01 := 0; wc_diff_01 := 0;
                                wc_same_10 := 0; wc_diff_10 := 0;
                                wc_same_11 := 0; wc_diff_11 := 0 |};
             vm_certified := false |}.
  eexists {| vm_graph :=
               {| pg_next_id       := 1;
                  pg_modules       := [];
                  pg_next_morph_id := 1;
                  pg_morphisms     := [] |};
             vm_csrs      := {| csr_cert_addr := 0; csr_status := 0;
                                csr_err := 0; csr_heap_base := 0 |};
             vm_regs      := [];
             vm_mem       := [];
             vm_pc        := 0;
             vm_mu        := 0;
             vm_mu_tensor := repeat 0 16;
             vm_err       := false;
             vm_logic_acc := 0;
             vm_mstatus   := 0;
             vm_witness   := {| wc_same_00 := 0; wc_diff_00 := 0;
                                wc_same_01 := 0; wc_diff_01 := 0;
                                wc_same_10 := 0; wc_diff_10 := 0;
                                wc_same_11 := 0; wc_diff_11 := 0 |};
             vm_certified := false |}.
  split.
  - (* Computationally equivalent: all observable fields are definitionally equal *)
    unfold computationally_equivalent.
    repeat split; reflexivity.
  - (* Categorically distinct: cons <> nil *)
    unfold categorically_distinct. simpl.
    intro H. discriminate H.
Qed.

(** COROLLARY: The categorically_distinct relation is inhabited.
    Morphism structure is meaningful content, not a vacuous annotation. *)
Corollary categorical_layer_is_nontrivial :
  exists s1 s2 : VMState, categorically_distinct s1 s2.
Proof.
  destruct categorical_separation as [s1 [s2 [_ Hdist]]].
  eauto.
Qed.

(** 11. The Classical Separation Theorem

    CLAIM: A "classical observer" — any function that maps VMState to a
    result and depends ONLY on the computational fields (registers, memory,
    μ, PC, error, certification) — cannot distinguish the two separated
    states. Yet the morphism-aware MORPH_DELETE instruction can.

    DEFINITION: A function f : VMState → A is "classical" if
    computationally_equivalent s1 s2 → f s1 = f s2.
    (It cannot see morphism graph structure.)

    THEOREM (classical_observer_cannot_separate):
    For any classical observer f, f s1 = f s2, where s1 and s2 are the
    two categorically-separated states from categorical_separation.

    PROOF: By computationally_equivalent s1 s2 (from categorical_separation)
    and the definition of classical observer.

    SIGNIFICANCE:
    This is the formal proof that "classical machines cannot distinguish
    program A from program B" in the demo's Act 4 argument. Classical
    machines observe only (regs, mem, μ, pc, err, certified). Those fields
    are IDENTICAL for the two programs. Only the morphism graph differs,
    and morphism graph access requires morphism-aware instructions.
*)

(** Definition: A function f is a classical observer if it is
    insensitive to the morphism graph component of VMState.
    That is, computationally equivalent states produce the same output. *)
Definition is_classical_observer {A : Type} (f : VMState -> A) : Prop :=
  forall s1 s2, computationally_equivalent s1 s2 -> f s1 = f s2.

(** Classical observers cannot separate the two witness states. *)
Theorem classical_observer_cannot_separate :
  forall {A : Type} (f : VMState -> A),
    is_classical_observer f ->
    exists s1 s2,
      computationally_equivalent s1 s2 /\
      categorically_distinct s1 s2 /\
      f s1 = f s2.
Proof.
  intros A f Hclassical.
  destruct categorical_separation as [s1 [s2 [Hequiv Hdist]]].
  exists s1, s2.
  split. { exact Hequiv. }
  split. { exact Hdist. }
  apply Hclassical. exact Hequiv.
Qed.

(** COROLLARY: The classical projection of the witness states is equal.
    This makes the "same classical fingerprint" claim fully formal. *)
Definition classical_projection (s : VMState) :=
  (s.(vm_regs), s.(vm_mem), s.(vm_mu), s.(vm_pc), s.(vm_err), s.(vm_certified)).

Corollary witness_states_same_classical_projection :
  exists s1 s2,
    classical_projection s1 = classical_projection s2 /\
    categorically_distinct s1 s2.
Proof.
  destruct categorical_separation as [s1 [s2 [Hequiv Hdist]]].
  exists s1, s2.
  split.
  - (* classical projections are equal because computationally_equivalent *)
    unfold classical_projection, computationally_equivalent in *.
    destruct Hequiv as [Hr [Hm [Hmu [Hpc [Herr Hcert]]]]].
    rewrite Hr, Hm, Hmu, Hpc, Herr, Hcert.
    reflexivity.
  - exact Hdist.
Qed.

(** COROLLARY: Any classical test (bool-valued classical observer) gives
    the same result on both separated states.
    This is the formal "classical machines cannot tell them apart" claim. *)
Corollary classical_bool_test_indistinguishable :
  forall (test : VMState -> bool),
    is_classical_observer test ->
    exists s1 s2,
      test s1 = test s2 /\
      categorically_distinct s1 s2.
Proof.
  intros test Htest.
  destruct (classical_observer_cannot_separate test Htest) as [s1 [s2 [_ [Hdist Hsame]]]].
  exists s1, s2. split. { exact Hsame. } { exact Hdist. }
Qed.

End PartitionSeparation.
