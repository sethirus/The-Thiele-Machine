(** TuringClassicalEmbedding.v — D1+D2: Classical Machine Notion and Embedding

    D1: THE TURING / CLASSICAL COMPUTATION NOTION

    The "Turing notion" used throughout D2-D5 is:

      A CLASSICAL PROGRAM is a list of vm_instructions all satisfying
      is_classical_opcode (defined in ClassicalConservativity.v).

      This is the fragment of the Thiele ISA that:
        (a) Does NOT modify vm_graph (morphism structure)
        (b) Does NOT modify csr_cert_addr (structural cert channel)
        (c) Does NOT modify vm_certified
        (d) Does NOT modify vm_witness (CHSH counters)

      Classical opcodes include: load_imm, load, store, add, mul, xor,
      jnez, halt, read_port, write_port, mdlacc, morph_get, tensor_get,
      and all compute instructions.  They explicitly EXCLUDE: pnew, morph,
      compose, lassert, ljoin, emit, reveal, chsh_trial, certify, etc.

      Relation to KernelTM.v:
      The traditional Turing Machine model (KernelTM.v) uses T_Write,
      T_Move, T_Branch, T_Halt operating on a tape.  These have direct
      classical Thiele analogs (store/load for T_Write/read, jnez for
      T_Branch, halt for T_Halt).  The Thiele classical fragment is a
      strict superset of the traditional TM model, adding register
      arithmetic and direct memory operations.

      We do not formally simulate KernelTM.v inside the classical fragment
      here (that would require a large simulation proof).  Instead, we
      establish the classical fragment as the authoritative Turing notion
      for D2-D5, noting that the KernelTM.v model is a special case.

    D2: THE CLASSICAL → THIELE EMBEDDING

    The embedding classical_to_thiele is the identity function:
    classical programs ARE Thiele programs — the ISA is shared, and
    classical programs simply do not use structural opcodes.

    FAITHFULNESS (D2): The embedding preserves all shadow-observable
    behavior.  By D3 (ClassicalConservativity.v), classical traces do not
    touch the structural layer.  Therefore:
      (a) The shadow_proj of the Thiele result is the complete observable
          summary of the classical computation.
      (b) The structural state is frozen: vm_graph, csr_cert_addr, and
          vm_certified are unchanged by classical programs.

*)

From Coq Require Import List Arith.PeanoNat Bool.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof AbstractNoFI
                           ClassicalConservativity ShadowProjection
                           ProperSubsumption.

(**

    Pin down the "Turing notion" used in D2-D5.
*)

(** is_classical_program: A program is classical iff every instruction
    satisfies is_classical_opcode — i.e., it does not access structural
    (categorical) state: no graph mutations, no cert-channel ops, no
    witness ops, no certified flag changes. *)
Definition is_classical_program (prog : list vm_instruction) : Prop :=
  Forall (fun i => is_classical_opcode i = true) prog.

(** ClassicalMachine: the classical computation model used in D1-D5.
    A pair of a classical program with its classicality certificate. *)
Record ClassicalMachine := {
  cm_program   : list vm_instruction;
  cm_classical : is_classical_program cm_program
}.

(** cm_run: Execute a ClassicalMachine using the Thiele VM semantics.
    Since classical programs only use classical opcodes, the Thiele VM
    restricted to those opcodes IS the classical machine. *)
Definition cm_run (M : ClassicalMachine) (s0 : VMState) : VMState :=
  acm_run thiele_cert_machine (cm_program M) s0.


(** classical_to_thiele: The formal embedding is the identity on program
    lists.  Classical programs are already Thiele programs — no
    translation is needed, as they use a common ISA. *)
Definition classical_to_thiele (prog : list vm_instruction) : list vm_instruction :=
  prog.

(** D2_embedding_is_identity: The embedding is definitionally the identity.
    Running classical_to_thiele(prog) is the same as running prog. *)
(* DEFINITIONAL HELPER: classical_to_thiele is the identity — unfolding produces reflexivity. *)
Lemma D2_embedding_is_identity :
  forall (prog : list vm_instruction) (s0 : VMState),
    acm_run thiele_cert_machine (classical_to_thiele prog) s0 =
    acm_run thiele_cert_machine prog s0.
Proof.
  intros. unfold classical_to_thiele. reflexivity.
Qed.

(** D2_faithfulness: The embedding is faithful under shadow_proj.
    Running a classical program on the Thiele VM:
      (a) produces a shadow that captures all classical observables;
      (b) leaves the structural layer (graph, cert_addr, certified) unchanged.

    Proof uses D3_conservativity from ClassicalConservativity.v. *)
Theorem D2_faithfulness :
  forall (prog : list vm_instruction) (s0 : VMState),
    is_classical_program prog ->
    (** (a) The shadow projection is the classical-observable summary. *)
    shadow_proj (acm_run thiele_cert_machine prog s0) =
    {| cs_regs      := (acm_run thiele_cert_machine prog s0).(vm_regs);
       cs_mem       := (acm_run thiele_cert_machine prog s0).(vm_mem);
       cs_pc        := (acm_run thiele_cert_machine prog s0).(vm_pc);
       cs_mu        := (acm_run thiele_cert_machine prog s0).(vm_mu);
       cs_err       := (acm_run thiele_cert_machine prog s0).(vm_err);
       cs_certified := (acm_run thiele_cert_machine prog s0).(vm_certified) |} /\
    (** (b) The structural layer is frozen by classical traces (D3). *)
    (acm_run thiele_cert_machine prog s0).(vm_graph) = s0.(vm_graph) /\
    (acm_run thiele_cert_machine prog s0).(vm_csrs).(csr_cert_addr) =
      s0.(vm_csrs).(csr_cert_addr) /\
    (acm_run thiele_cert_machine prog s0).(vm_certified) = s0.(vm_certified).
Proof.
  intros prog s0 Hclassical.
  refine (conj _ _).
  - (* (a) shadow_proj is definitionally the projection onto classical fields *)
    unfold shadow_proj. reflexivity.
  - (* (b) structural preservation — apply D3_conservativity *)
    exact (D3_conservativity prog s0 Hclassical).
Qed.

(** D2_classical_machines_are_thiele: Any ClassicalMachine is a valid
    Thiele program.  The embedding gives a semantic inclusion:
    classical ⊆ Thiele. *)
(* DEFINITIONAL HELPER: cm_run unfolds to acm_run by construction — identity by reflexivity. *)
Theorem D2_classical_machines_are_thiele :
  forall (M : ClassicalMachine) (s0 : VMState),
    cm_run M s0 =
    acm_run thiele_cert_machine (classical_to_thiele (cm_program M)) s0.
Proof.
  intros M s0. unfold cm_run, classical_to_thiele. reflexivity.
Qed.

(**

    Two states that agree on the classical-observable fields plus vm_graph
    and vm_csrs produce equal shadow projections after any classical trace.

    Why vm_graph and vm_csrs are needed beyond shadow_proj:
      • instr_heap_load / instr_heap_store use csr_heap_base from vm_csrs to
        compute memory addresses, so shadow output depends on vm_csrs.
      • vm_graph equality is needed for structural preservation by
        classical_opcode_preserves_graph (used in classical_step_compat).
    Hence shadow equality alone cannot guarantee shadow-preservation through
    a classical trace containing these instructions. *)

(** vm_classical_compat: the compatibility relation for shadow preservation.
    Covers all fields that classical instructions can read to affect shadow
    output, excluding vm_witness (which classical instructions never read). *)
Definition vm_classical_compat (s1 s2 : VMState) : Prop :=
  shadow_proj s1 = shadow_proj s2 /\
  s1.(vm_graph) = s2.(vm_graph) /\
  s1.(vm_csrs) = s2.(vm_csrs).

(** Unpack shadow_proj equality into individual field equalities. *)
Lemma unpack_shadow_proj :
  forall s1 s2,
    shadow_proj s1 = shadow_proj s2 ->
    s1.(vm_regs) = s2.(vm_regs) /\
    s1.(vm_mem)  = s2.(vm_mem)  /\
    s1.(vm_pc)   = s2.(vm_pc)   /\
    s1.(vm_mu)   = s2.(vm_mu)   /\
    s1.(vm_err)  = s2.(vm_err)  /\
    s1.(vm_certified) = s2.(vm_certified).
Proof.
  intros s1 s2 H.
  unfold shadow_proj in H.
  injection H as Hr Hm Hpc Hmu Herr Hcert.
  tauto.
Qed.

(** *** Shadow-projection of the four state constructors ***

    Each helper states: if the relevant input fields are equal between two
    applications of the constructor, the shadow projections are equal.
    Proofs are by unfolding + congruence. *)

Lemma shadow_advance_state :
  forall s1 s2 instr g1 g2 c1 c2 e1 e2,
    s1.(vm_regs) = s2.(vm_regs) ->
    s1.(vm_mem)  = s2.(vm_mem)  ->
    s1.(vm_pc)   = s2.(vm_pc)   ->
    s1.(vm_mu)   = s2.(vm_mu)   ->
    s1.(vm_certified) = s2.(vm_certified) ->
    e1 = e2 ->
    shadow_proj (advance_state s1 instr g1 c1 e1) =
    shadow_proj (advance_state s2 instr g2 c2 e2).
Proof.
  intros s1 s2 instr g1 g2 c1 c2 e1 e2 Hregs Hmem Hpc Hmu Hcert Herr.
  unfold shadow_proj, advance_state, apply_cost.
  rewrite Hregs, Hmem, Hpc, Hmu, Hcert, Herr.
  reflexivity.
Qed.

Lemma shadow_advance_state_rm :
  forall s1 s2 instr g1 g2 c1 c2 regs1 regs2 mem1 mem2 e1 e2,
    s1.(vm_pc)   = s2.(vm_pc)   ->
    s1.(vm_mu)   = s2.(vm_mu)   ->
    s1.(vm_certified) = s2.(vm_certified) ->
    regs1 = regs2 ->
    mem1  = mem2  ->
    e1    = e2    ->
    shadow_proj (advance_state_rm s1 instr g1 c1 regs1 mem1 e1) =
    shadow_proj (advance_state_rm s2 instr g2 c2 regs2 mem2 e2).
Proof.
  intros s1 s2 instr g1 g2 c1 c2 regs1 regs2 mem1 mem2 e1 e2
         Hpc Hmu Hcert Hregs Hmem Herr.
  unfold shadow_proj, advance_state_rm, apply_cost.
  rewrite Hpc, Hmu, Hcert, Hregs, Hmem, Herr.
  reflexivity.
Qed.

Lemma shadow_jump_state :
  forall s1 s2 instr target,
    s1.(vm_mu)   = s2.(vm_mu)   ->
    s1.(vm_regs) = s2.(vm_regs) ->
    s1.(vm_mem)  = s2.(vm_mem)  ->
    s1.(vm_err)  = s2.(vm_err)  ->
    s1.(vm_certified) = s2.(vm_certified) ->
    shadow_proj (jump_state s1 instr target) =
    shadow_proj (jump_state s2 instr target).
Proof.
  intros s1 s2 instr target Hmu Hregs Hmem Herr Hcert.
  unfold shadow_proj, jump_state, apply_cost.
  rewrite Hmu, Hregs, Hmem, Herr, Hcert.
  reflexivity.
Qed.

Lemma shadow_jump_state_rm :
  forall s1 s2 instr target regs1 regs2 mem1 mem2,
    s1.(vm_mu)   = s2.(vm_mu)   ->
    s1.(vm_err)  = s2.(vm_err)  ->
    s1.(vm_certified) = s2.(vm_certified) ->
    regs1 = regs2 ->
    mem1  = mem2  ->
    shadow_proj (jump_state_rm s1 instr target regs1 mem1) =
    shadow_proj (jump_state_rm s2 instr target regs2 mem2).
Proof.
  intros s1 s2 instr target regs1 regs2 mem1 mem2 Hmu Herr Hcert Hregs Hmem.
  unfold shadow_proj, jump_state_rm, apply_cost.
  rewrite Hmu, Herr, Hcert, Hregs, Hmem.
  reflexivity.
Qed.

(** *** Single-step shadow compatibility ***

    For each classical instruction, equal-compat states produce equal shadow.
    The proof is a case analysis over all 30+ classical instructions.
    The branching case (jnez) is handled by replacing the s2 branch
    condition with the s1 condition, then splitting. *)

Lemma classical_step_shadow_compat :
  forall (i : vm_instruction) (s1 s2 : VMState),
    is_classical_opcode i = true ->
    vm_classical_compat s1 s2 ->
    shadow_proj (vm_apply s1 i) = shadow_proj (vm_apply s2 i).
Proof.
  intros i s1 s2 Hi [Hproj [Hgraph Hcsrs]].
  destruct (unpack_shadow_proj s1 s2 Hproj)
    as [Hr [Hm [Hpc [Hmu [Herr Hcert]]]]].
  assert (Hhb : s1.(vm_csrs).(csr_heap_base) = s2.(vm_csrs).(csr_heap_base))
    by (rewrite Hcsrs; reflexivity).
  destruct i; simpl in Hi; try discriminate; unfold vm_apply.
  (* 1. mdlacc *)
  - apply shadow_advance_state; congruence.
  (* 2. xfer *)
  - apply shadow_advance_state_rm; try congruence.
    unfold write_reg, read_reg. congruence.
  (* 3. load_imm *)
  - apply shadow_advance_state_rm; try congruence.
    unfold write_reg. congruence.
  (* 4. load *)
  - apply shadow_advance_state_rm; try congruence.
    unfold write_reg, read_reg, read_mem. congruence.
  (* 5. store *)
  - apply shadow_advance_state_rm; try congruence.
    unfold write_mem, read_reg. congruence.
  (* 6. add *)
  - apply shadow_advance_state_rm; try congruence.
    unfold write_reg, read_reg. congruence.
  (* 7. sub *)
  - apply shadow_advance_state_rm; try congruence.
    unfold write_reg, read_reg. congruence.
  (* 8. jump *)
  - apply shadow_jump_state; congruence.
  (* 9. jnez: branches on read_reg s rs — use match goal to avoid naming *)
  - match goal with
    | |- context [Nat.eqb (read_reg s2 ?reg) 0] =>
        replace (Nat.eqb (read_reg s2 reg) 0) with (Nat.eqb (read_reg s1 reg) 0)
          by (unfold read_reg; congruence);
        destruct (Nat.eqb (read_reg s1 reg) 0)
    end.
    + apply shadow_advance_state; congruence.
    + apply shadow_jump_state; congruence.
  (* 10. call *)
  - apply shadow_jump_state_rm; try congruence.
    + unfold write_reg, read_reg. congruence.
    + unfold write_mem, read_reg. congruence.
  (* 11. ret: return PC from memory; vm_pc not in output *)
  - unfold shadow_proj, jump_state_rm, apply_cost, read_reg, write_reg, read_mem.
    rewrite Hr, Hm, Hmu, Herr, Hcert. reflexivity.
  (* 12. xor_load *)
  - apply shadow_advance_state_rm; try congruence.
    unfold write_reg, read_mem. congruence.
  (* 13. xor_add *)
  - apply shadow_advance_state_rm; try congruence.
    unfold write_reg, read_reg. congruence.
  (* 14. xor_swap *)
  - apply shadow_advance_state_rm; try congruence.
  (* 15. xor_rank *)
  - apply shadow_advance_state_rm; try congruence.
    unfold write_reg, read_reg. congruence.
  (* 16. halt *)
  - apply shadow_advance_state; congruence.
  (* 17. checkpoint *)
  - apply shadow_advance_state; congruence.
  (* 19. read_port: value from instruction literal *)
  - apply shadow_advance_state_rm; try congruence.
    unfold write_reg. congruence.
  (* 20. write_port *)
  - apply shadow_advance_state; congruence.
  (* 21. heap_load: uses csr_heap_base — equal by Hhb *)
  - apply shadow_advance_state_rm; try congruence.
    unfold write_reg, read_mem, read_reg. congruence.
  (* 22. heap_store: uses csr_heap_base — equal by Hhb *)
  - apply shadow_advance_state_rm; try congruence.
    unfold write_mem, read_reg. congruence.
  (* 23. and *)
  - apply shadow_advance_state_rm; try congruence.
    unfold write_reg, read_reg. congruence.
  (* 24. or *)
  - apply shadow_advance_state_rm; try congruence.
    unfold write_reg, read_reg. congruence.
  (* 25. shl *)
  - apply shadow_advance_state_rm; try congruence.
    unfold write_reg, read_reg. congruence.
  (* 26. shr *)
  - apply shadow_advance_state_rm; try congruence.
    unfold write_reg, read_reg. congruence.
  (* 27. mul *)
  - apply shadow_advance_state_rm; try congruence.
    unfold write_reg, read_reg. congruence.
  (* 28. lui *)
  - apply shadow_advance_state_rm; try congruence.
    unfold write_reg. congruence.
  (* 29. tensor_get: branches on tensor_indices_ok (state-independent) *)
  - destruct (tensor_indices_ok i j).
    + apply shadow_advance_state_rm; try congruence.
      unfold write_reg, module_tensor_entry. rewrite Hgraph. congruence.
    + apply shadow_advance_state; try congruence.
      unfold latch_err; reflexivity.
  (* 30. morph_get: branches on graph_lookup_morphism *)
  - replace (graph_lookup_morphism (vm_graph s2) morph_id)
      with (graph_lookup_morphism (vm_graph s1) morph_id)
      by (rewrite Hgraph; reflexivity).
    destruct (graph_lookup_morphism (vm_graph s1) morph_id) as [ms|].
    + apply shadow_advance_state_rm; try congruence.
      unfold write_reg. congruence.
    + apply shadow_advance_state; try congruence.
      unfold latch_err; reflexivity.
Qed.

(** *** Single-step vm_csrs compatibility ***

    Classical instructions map equal vm_csrs to equal vm_csrs.
    The csrs in vm_apply results depend only on s.vm_csrs (and sometimes
    s.vm_graph for branch conditions), so Hcsrs + Hgraph suffice. *)

Lemma classical_step_csrs_compat :
  forall (i : vm_instruction) (s1 s2 : VMState),
    is_classical_opcode i = true ->
    s1.(vm_csrs) = s2.(vm_csrs) ->
    s1.(vm_graph) = s2.(vm_graph) ->
    s1.(vm_regs)  = s2.(vm_regs) ->
    (vm_apply s1 i).(vm_csrs) = (vm_apply s2 i).(vm_csrs).
Proof.
  intros i s1 s2 Hi Hcsrs Hgraph Hr.
  destruct i; simpl in Hi; try discriminate; unfold vm_apply.
  (* For most instructions: result.vm_csrs = f(s.vm_csrs) same for both *)
  all: try (unfold advance_state, advance_state_rm, jump_state, jump_state_rm;
            simpl; congruence).
  (* jnez: branch condition depends on vm_regs *)
  - match goal with
    | |- context [Nat.eqb (read_reg s2 ?reg) 0] =>
        replace (Nat.eqb (read_reg s2 reg) 0) with (Nat.eqb (read_reg s1 reg) 0)
          by (unfold read_reg; congruence);
        destruct (Nat.eqb (read_reg s1 reg) 0)
    end;
    unfold advance_state, jump_state; simpl; congruence.
  (* tensor_get: if tensor_indices_ok *)
  - destruct (tensor_indices_ok i j);
    unfold advance_state, advance_state_rm; simpl; congruence.
  (* morph_get: match on graph_lookup_morphism *)
  - replace (graph_lookup_morphism (vm_graph s2) morph_id)
      with (graph_lookup_morphism (vm_graph s1) morph_id)
      by (rewrite Hgraph; reflexivity).
    destruct (graph_lookup_morphism (vm_graph s1) morph_id);
    unfold advance_state, advance_state_rm; simpl; congruence.
Qed.

(** *** Single-step full compatibility ***

    Combines shadow, graph, and csrs compatibility into one lemma.
    Graph compatibility uses the already-proven classical_opcode_preserves_graph. *)

Lemma classical_step_compat :
  forall (i : vm_instruction) (s1 s2 : VMState),
    is_classical_opcode i = true ->
    vm_classical_compat s1 s2 ->
    vm_classical_compat (vm_apply s1 i) (vm_apply s2 i).
Proof.
  intros i s1 s2 Hi [Hproj [Hgraph Hcsrs]].
  destruct (unpack_shadow_proj s1 s2 Hproj)
    as [Hr [Hm [Hpc [Hmu [Herr Hcert]]]]].
  unfold vm_classical_compat.
  split; [| split].
  - exact (classical_step_shadow_compat i s1 s2 Hi
             (conj Hproj (conj Hgraph Hcsrs))).
  - rewrite (classical_opcode_preserves_graph s1 i Hi).
    rewrite (classical_opcode_preserves_graph s2 i Hi).
    exact Hgraph.
  - exact (classical_step_csrs_compat i s1 s2 Hi Hcsrs Hgraph Hr).
Qed.

(** *** Trace-level compatibility by induction *** *)

Lemma classical_trace_compat :
  forall (prog : list vm_instruction) (s1 s2 : VMState),
    is_classical_program prog ->
    vm_classical_compat s1 s2 ->
    vm_classical_compat (acm_run thiele_cert_machine prog s1)
                        (acm_run thiele_cert_machine prog s2).
Proof.
  induction prog as [| i rest IH]; intros s1 s2 Hclassical Hcompat.
  - simpl. exact Hcompat.
  - inversion Hclassical as [| ? ? Hi Hrest]; subst.
    simpl.
    apply IH.
    + exact Hrest.
    + exact (classical_step_compat i s1 s2 Hi Hcompat).
Qed.

(** D2_classical_shadow_preserved:
    Classical programs preserve shadow equality for classically-compatible
    initial states.

    Note: vm_classical_compat requires shadow equality PLUS vm_graph and
    vm_csrs equality.  The extra conditions are genuinely necessary because
    instr_morph_get / instr_tensor_get read vm_graph, and instr_heap_load /
    instr_heap_store read csr_heap_base from vm_csrs. *)
Theorem D2_classical_shadow_preserved :
  forall (prog : list vm_instruction) (s1 s2 : VMState),
    is_classical_program prog ->
    vm_classical_compat s1 s2 ->
    shadow_proj (acm_run thiele_cert_machine prog s1) =
    shadow_proj (acm_run thiele_cert_machine prog s2).
Proof.
  intros prog s1 s2 Hclassical Hcompat.
  destruct (classical_trace_compat prog s1 s2 Hclassical Hcompat)
    as [Hproj' _].
  exact Hproj'.
Qed.

(**

    This is the capstone theorem for the "Turing ⊂ Thiele" relationship.
    It assembles four orthogonal results into a single named formal claim.

    SAFE WORDING: "A classical Turing machine is a degenerate projection
    fragment of the Thiele machine: every TM computation embeds faithfully
    via lift_config, and shadow_proj is the quotient map back to the
    classical fragment.  The quotient is proper (shadow_proj is lossy)."
*)

(** eq_on_classical_shadow: the equivalence relation defined by shadow_proj.
    Two states are classically-shadow-equivalent iff they agree on all six
    shadow fields (regs, mem, pc, mu, err, certified). *)
Definition eq_on_classical_shadow (s1 s2 : VMState) : Prop :=
  s1.(vm_regs) = s2.(vm_regs) /\
  s1.(vm_mem)  = s2.(vm_mem)  /\
  s1.(vm_pc)   = s2.(vm_pc)   /\
  s1.(vm_mu)   = s2.(vm_mu)   /\
  s1.(vm_err)  = s2.(vm_err)  /\
  s1.(vm_certified) = s2.(vm_certified).

(** shadow_proj's kernel is exactly eq_on_classical_shadow.
    Adapts forget_kernel_is_eq_on_classical to the 6-field shadow. *)
Theorem shadow_proj_kernel_is_eq_on_classical_shadow :
  forall s1 s2 : VMState,
    shadow_proj s1 = shadow_proj s2 <-> eq_on_classical_shadow s1 s2.
Proof.
  intros s1 s2. split.
  - intro H. exact (unpack_shadow_proj s1 s2 H).
  - intros [Hr [Hm [Hpc [Hmu [Herr Hcert]]]]].
    unfold shadow_proj. f_equal; assumption.
Qed.

(** THE DEGENERATE PROJECTION THEOREM

    Part (1): Every TM run is faithfully simulated by the Thiele machine via
              lift_config.  The TM config is preserved component-wise.
              Source: ProperSubsumption.thiele_simulates_turing.

    Part (2): shadow_proj is the quotient map.  Its kernel is exactly
              eq_on_classical_shadow — the relation that identifies states
              a classical observer cannot distinguish.

    Part (3): Classically-compatible states (equal on shadow, graph, csrs) stay
              classically-compatible under classical programs.  I.e., the
              quotient is respected by classical traces.

    Part (4): The projection is strictly lossy — there exist distinct Thiele
              states that are shadow-equal.  The classical fragment is a
              proper quotient, not an isomorphism. *)
Theorem degenerate_projection_theorem :
  (* (1) Faithful embedding: every TM run embeds in Thiele *)
  (forall fuel delta c,
    (ProperSubsumption.thiele_run fuel delta
       (ProperSubsumption.lift_config c)).(ProperSubsumption.th_tm_config)
    = ProperSubsumption.tm_run fuel delta c) /\
  (* (2) shadow_proj is the quotient map — its kernel is eq_on_classical_shadow *)
  (forall s1 s2 : VMState,
    shadow_proj s1 = shadow_proj s2 <-> eq_on_classical_shadow s1 s2) /\
  (* (3) Classical traces respect the classical-compatible quotient *)
  (forall (prog : list vm_instruction) (s1 s2 : VMState),
    is_classical_program prog ->
    vm_classical_compat s1 s2 ->
    shadow_proj (acm_run thiele_cert_machine prog s1) =
    shadow_proj (acm_run thiele_cert_machine prog s2)) /\
  (* (4) The projection is strictly lossy — structural info is irreversibly erased *)
  (exists s1 s2 : VMState,
    shadow_proj s1 = shadow_proj s2 /\ s1 <> s2).
Proof.
  refine (conj _ (conj _ (conj _ _))).
  - (* Part 1: thiele_simulates_turing from ProperSubsumption *)
    exact ProperSubsumption.thiele_simulates_turing.
  - (* Part 2: shadow_proj kernel = eq_on_classical_shadow *)
    exact shadow_proj_kernel_is_eq_on_classical_shadow.
  - (* Part 3: D2_classical_shadow_preserved *)
    exact D2_classical_shadow_preserved.
  - (* Part 4: shadow_strictly_lossy provides the witness pair *)
    destruct shadow_strictly_lossy as [s1 [s2 [Heq [Hdiff _]]]].
    exists s1, s2.
    split.
    + exact Heq.
    + intro H.
      apply Hdiff.
      rewrite H.
      reflexivity.
Qed.

(**

    Converse of Part 3: if two states have different shadow projections,
    some classical program can distinguish them.

    The witness is trivial — the empty program [].  Since
    [acm_run thiele_cert_machine [] s = s], the initial shadow difference
    is preserved verbatim.  This confirms that shadow_proj is exactly the
    distinguishability quotient: shadow-equivalent states are indistinguishable
    by classical programs (Part 3), and shadow-inequivalent states are
    immediately distinguishable (Part 5). *)

Theorem shadow_inequivalent_states_distinguishable :
  forall (s1 s2 : VMState),
    shadow_proj s1 <> shadow_proj s2 ->
    exists (prog : list vm_instruction),
      is_classical_program prog /\
      shadow_proj (acm_run thiele_cert_machine prog s1) <>
      shadow_proj (acm_run thiele_cert_machine prog s2).
Proof.
  intros s1 s2 Hneq.
  exists nil.
  split.
  - (* Empty program is classical *)
    unfold is_classical_program. constructor.
  - (* acm_run _ [] s = s, so shadow difference is preserved *)
    simpl. exact Hneq.
Qed.