(** ShadowProjection.v — Formal Classical Shadow Projection

    ==========================================================================
    THE CLASSICAL SHADOW
    ==========================================================================

    The Thiele VM state is richer than any "classical" state that only tracks
    the computational fields. The classical shadow is the lossy projection that
    forgets the morphism graph structure.

    FORMAL DEFINITIONS:
      shadow_proj : VMState → ClassicalState
        projects to (regs, mem, pc, mu, err, certified)
        FORGETS: vm_graph (morphisms, modules), vm_csrs (csr_cert_addr),
                 vm_witness, vm_mstatus, vm_mu_tensor

    THEOREMS:
      C1: shadow_proj is well-defined (it's a total function)
      C2: shadow_proj is lossy — different states can have the same shadow
          (specifically: different morphism graphs map to the same shadow)
      C3: shadow_proj s1 = shadow_proj s2 but probe distinguishes them
          (upgraded from demo to formal theorem)
      C4: the distinguishing probe (MORPH_DELETE) is semantically legitimate
          — it depends on real retained structure, not metadata
      C5: shadow_proj is strictly lossy — the image does not capture morphism state

    ==========================================================================
    STATUS: Fully proven. Zero Admitted.
    ==========================================================================
*)

From Coq Require Import List Arith.PeanoNat Bool Lia String.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.

(** =========================================================================
    PART 1: THE SHADOW PROJECTION FUNCTION
    =========================================================================

    ClassicalState: the 6-field classical observable state.
    shadow_proj: projects VMState to ClassicalState, discarding graph structure.
*)

(** ClassicalState: what a classical observer can see.
    Explicitly excludes: vm_graph, vm_csrs (csr_cert_addr), vm_witness,
    vm_mstatus, vm_mu_tensor. *)
Record ClassicalState := {
  cs_regs      : list nat;
  cs_mem       : list nat;
  cs_pc        : nat;
  cs_mu        : nat;
  cs_err       : bool;
  cs_certified : bool
}.

(** shadow_proj: the formal classical shadow projection.
    Total, well-defined, always computable. *)
Definition shadow_proj (s : VMState) : ClassicalState := {|
  cs_regs      := s.(vm_regs);
  cs_mem       := s.(vm_mem);
  cs_pc        := s.(vm_pc);
  cs_mu        := s.(vm_mu);
  cs_err       := s.(vm_err);
  cs_certified := s.(vm_certified)
|}.

(** =========================================================================
    PART 2: SHADOW EQUALITY (CLASSICAL INDISTINGUISHABILITY)
    =========================================================================

    Two states are shadow-equal if their classical projections are identical.
    This is the formal notion of "indistinguishable to a classical observer."
*)

Definition shadow_equal (s1 s2 : VMState) : Prop :=
  shadow_proj s1 = shadow_proj s2.

Lemma shadow_equal_unfold :
  forall s1 s2,
    shadow_equal s1 s2 <->
    s1.(vm_regs) = s2.(vm_regs) /\
    s1.(vm_mem)  = s2.(vm_mem)  /\
    s1.(vm_pc)   = s2.(vm_pc)   /\
    s1.(vm_mu)   = s2.(vm_mu)   /\
    s1.(vm_err)  = s2.(vm_err)  /\
    s1.(vm_certified) = s2.(vm_certified).
Proof.
  intros s1 s2. split.
  - intro H. unfold shadow_equal, shadow_proj in H.
    injection H. intros. repeat split; assumption.
  - intros [Hr [Hm [Hpc [Hmu [Herr Hcert]]]]].
    unfold shadow_equal, shadow_proj.
    f_equal; assumption.
Qed.

(** =========================================================================
    PART 3: WITNESS STATES — THE SEPARATION PAIR
    =========================================================================

    We define explicit witness states for the separation theorem.
    These correspond exactly to the states in categorical_separation
    (PartitionSeparation.v) but are named here for direct use.

    separation_A: has one identity morphism (morphism id=0)
    separation_B: has no morphisms
    All other fields are identical.
*)

Definition separation_morph : MorphismState := {|
  morph_source     := 0;
  morph_target     := 0;
  morph_coupling   := {| coupling_pairs := []; coupling_label := "" |};
  morph_is_identity := true
|}.

Definition separation_csrs : CSRState :=
  {| csr_cert_addr := 0; csr_status := 0; csr_err := 0; csr_heap_base := 0 |}.

Definition separation_witness : WitnessCounts :=
  {| wc_same_00 := 0; wc_diff_00 := 0;
     wc_same_01 := 0; wc_diff_01 := 0;
     wc_same_10 := 0; wc_diff_10 := 0;
     wc_same_11 := 0; wc_diff_11 := 0 |}.

(** separation_A: state with morphism id=0 present *)
Definition separation_A : VMState := {|
  vm_graph     := {| pg_next_id       := 1;
                     pg_modules       := [];
                     pg_next_morph_id := 1;
                     pg_morphisms     := [(0, separation_morph)] |};
  vm_csrs      := separation_csrs;
  vm_regs      := [];
  vm_mem       := [];
  vm_pc        := 0;
  vm_mu        := 0;
  vm_mu_tensor := repeat 0 16;
  vm_err       := false;
  vm_logic_acc := 0;
  vm_mstatus   := 0;
  vm_witness   := separation_witness;
  vm_certified := false
|}.

(** separation_B: state with no morphisms — otherwise identical to A *)
Definition separation_B : VMState := {|
  vm_graph     := {| pg_next_id       := 1;
                     pg_modules       := [];
                     pg_next_morph_id := 1;
                     pg_morphisms     := [] |};
  vm_csrs      := separation_csrs;
  vm_regs      := [];
  vm_mem       := [];
  vm_pc        := 0;
  vm_mu        := 0;
  vm_mu_tensor := repeat 0 16;
  vm_err       := false;
  vm_logic_acc := 0;
  vm_mstatus   := 0;
  vm_witness   := separation_witness;
  vm_certified := false
|}.

(** =========================================================================
    PART 4: C2 — SHADOW PROJECTION IS LOSSY
    =========================================================================

    Different morphism graphs produce the same shadow projection.
    Therefore shadow_proj forgets graph structure.
*)

(** shadow_proj_forgets_graph: shadow_equal does not imply graph equality.
    separation_A and separation_B have identical shadows but different graphs. *)
Theorem shadow_proj_forgets_graph :
  shadow_equal separation_A separation_B /\
  separation_A.(vm_graph).(pg_morphisms) <> separation_B.(vm_graph).(pg_morphisms).
Proof.
  refine (conj _ _).
  - (* shadow equal: all classical fields are identical *)
    unfold shadow_equal, shadow_proj, separation_A, separation_B.
    simpl. reflexivity.
  - (* graph differs: cons ≠ nil *)
    simpl. intro H. discriminate H.
Qed.

(** =========================================================================
    PART 5: C4 — THE PROBE IS SEMANTICALLY LEGITIMATE
    =========================================================================

    The MORPH_DELETE 0 probe is a legitimate Thiele instruction.
    It succeeds on separation_A (morphism 0 exists) and fails on separation_B
    (morphism 0 does not exist).

    This is NOT metadata magic:
    - MORPH_DELETE is a standard opcode in the ISA
    - Its behavior is determined by the graph content via graph_delete_morphism
    - The error flag (vm_err) is the separation observable — it changes real program behavior
*)

(** The probe instruction: MORPH_DELETE with id=0, cost=0. *)
Definition morph_delete_probe : vm_instruction := instr_morph_delete 0 0.

(** probe_succeeds_on_A: MORPH_DELETE 0 does NOT set vm_err on separation_A.
    Proof: graph_delete_morphism finds morphism 0, returns Some — success branch. *)
Lemma probe_succeeds_on_A :
  (vm_apply separation_A morph_delete_probe).(vm_err) = false.
Proof.
  unfold vm_apply, morph_delete_probe, separation_A.
  simpl. reflexivity.
Qed.

(** probe_fails_on_B: MORPH_DELETE 0 SETS vm_err on separation_B.
    Proof: graph_delete_morphism returns None (no morphism 0) — failure branch. *)
Lemma probe_fails_on_B :
  (vm_apply separation_B morph_delete_probe).(vm_err) = true.
Proof.
  unfold vm_apply, morph_delete_probe, separation_B.
  simpl. reflexivity.
Qed.

(** =========================================================================
    PART 6: C3 — THE FORMAL SEPARATION THEOREM
    =========================================================================

    Upgrades the demo (Act 4 in demo_knowledge_receipt.py) to a formal theorem:
    There exist two states with the same classical shadow that are separated
    by a semantically legitimate probe.

    This is the theorem-grade version of "classical machines cannot tell them apart,
    but Thiele can."
*)

(** shadow_separation_theorem: THE CORE SEPARATION THEOREM.
    Existence of states that are:
    1. Shadow-equal (classically indistinguishable)
    2. Graph-distinct (different morphism structure)
    3. Separable by a single vm_apply probe
*)
Theorem shadow_separation_theorem :
  exists (s1 s2 : VMState) (probe : vm_instruction),
    (* C2: same classical shadow *)
    shadow_equal s1 s2 /\
    (* Thiele-distinct: different graph structure *)
    s1.(vm_graph).(pg_morphisms) <> s2.(vm_graph).(pg_morphisms) /\
    (* C3/C4: probe is a valid ISA instruction that separates them *)
    (vm_apply s1 probe).(vm_err) = false /\
    (vm_apply s2 probe).(vm_err) = true.
Proof.
  exists separation_A, separation_B, morph_delete_probe.
  refine (conj _ (conj _ (conj _ _))).
  - (* shadow equal *)
    unfold shadow_equal, shadow_proj, separation_A, separation_B.
    simpl. reflexivity.
  - (* graph distinct *)
    simpl. intro H. discriminate H.
  - (* probe succeeds on A *)
    exact probe_succeeds_on_A.
  - (* probe fails on B *)
    exact probe_fails_on_B.
Qed.

(** =========================================================================
    PART 7: C5 — SHADOW IS STRICTLY LOSSY
    =========================================================================

    The shadow projection is strictly lossy: there exist distinct (not
    shadow-related) structural facts that shadow_proj cannot express.
    The image of shadow_proj does not capture morphism-graph information.
*)

(** shadow_does_not_capture_morphisms: no function of ClassicalState alone
    can distinguish separation_A from separation_B.
    Any function f : ClassicalState → A gives the same result on both states. *)
Theorem shadow_does_not_capture_morphisms :
  forall {A : Type} (f : ClassicalState -> A),
    f (shadow_proj separation_A) = f (shadow_proj separation_B).
Proof.
  intros A f.
  (* The projections are definitionally equal *)
  assert (Heq : shadow_proj separation_A = shadow_proj separation_B).
  { unfold shadow_proj, separation_A, separation_B. simpl. reflexivity. }
  rewrite Heq. reflexivity.
Qed.

(** COROLLARY: No classical observer (function of classical state) can separate
    the witness states. *)
Corollary no_classical_separation :
  forall {A : Type} (f : VMState -> A),
    (** f is a classical observer: it depends only on shadow_proj *)
    (forall s1 s2, shadow_proj s1 = shadow_proj s2 -> f s1 = f s2) ->
    f separation_A = f separation_B.
Proof.
  intros A f Hclassical.
  apply Hclassical.
  unfold shadow_proj, separation_A, separation_B.
  simpl. reflexivity.
Qed.

(** shadow_strictly_lossy: The shadow projection is strictly lossy.
    The two witnesses have the same shadow but different graphs,
    and the probe separates them.
    This combines C2, C3, C4 into the single public-safe claim. *)
Theorem shadow_strictly_lossy :
  exists (s1 s2 : VMState),
    (** Same shadow — classical machines cannot tell them apart *)
    shadow_proj s1 = shadow_proj s2 /\
    (** Different graph — Thiele retains structure classical machines lose *)
    s1.(vm_graph).(pg_morphisms) <> s2.(vm_graph).(pg_morphisms) /\
    (** A legitimate probe separates them — the retained structure is actionable *)
    exists probe,
      (vm_apply s1 probe).(vm_err) <> (vm_apply s2 probe).(vm_err).
Proof.
  exists separation_A, separation_B.
  refine (conj _ (conj _ _)).
  - unfold shadow_proj, separation_A, separation_B. simpl. reflexivity.
  - simpl. intro H. discriminate H.
  - exists morph_delete_probe.
    rewrite probe_succeeds_on_A, probe_fails_on_B.
    discriminate.
Qed.
