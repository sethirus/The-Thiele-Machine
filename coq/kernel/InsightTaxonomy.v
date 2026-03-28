(** InsightTaxonomy.v — Formal Taxonomy of Insight Events

    ==========================================================================
    THE CORE INSIGHT DESIGN PRINCIPLE
    ==========================================================================

    The Thiele Machine's ISA makes a deliberate distinction between two tiers
    of structural operations:

    TIER 1 — STRUCTURAL CREATION (can be zero-cost):
      PNEW, MORPH, COMPOSE, MORPH_ID, MORPH_DELETE, MORPH_TENSOR, MORPH_GET,
      PSPLIT, PMERGE, etc.
      These create or manipulate structural objects (modules, morphisms,
      partition refinements) but DO NOT certify them. instruction_cost uses
      the raw mu_delta parameter — a user can call these with cost=0.

    TIER 2 — CERTIFIED INSIGHT (always cost ≥ 1, enforced by S(cost)):
      MORPH_ASSERT, LASSERT, LJOIN, EMIT, REVEAL, READ_PORT, CERTIFY
      These CERTIFY structural claims — they mark a claim as formally valid
      and recorded. instruction_cost uses S(mu_delta), guaranteeing ≥ 1.

    THE NO FREE INSIGHT PRINCIPLE (formally precise):
      Uncertified structural creation is free.
      Certified structural insight cannot be free.

    This is NOT a gap — it is a deliberate and correct design:
    - Building structure cheaply allows exploration
    - Certifying a claim requires paying at least 1 unit of cost
    - The cost is the irreversible record that a claim was formally asserted

    ==========================================================================
    THEOREMS
    ==========================================================================

    1. structural_creation_can_be_free:
       PNEW and MORPH have cost 0 when called with mu_delta=0.
       This is intentional — not a gap.

    2. certified_insight_nonfree:
       Any transition that changes csr_cert_addr (0→nonzero) or vm_certified
       (false→true) must have instruction_cost ≥ 1.
       [from AbstractNoFI.v: certification_requires_positive_mu]

    3. morph_assert_is_certified_insight:
       MORPH_ASSERT sets csr_cert_addr (cert-addr-setter), hence is a
       certified insight event and its cost is provably ≥ 1.

    4. non_cert_ops_are_structurally_neutral_on_cert_channel:
       PNEW, MORPH, MORPH_DELETE, MORPH_GET, MORPH_TENSOR, COMPOSE, MORPH_ID
       preserve csr_cert_addr exactly (they are not cert_addr_setters).

    5. certified_insight_trace_nonfree:
       Along any trace, if cert evidence appears (cert_addr 0→nonzero),
       then total mu growth is ≥ 1. Composition of zero-cost structural
       creation ops cannot produce certification.
       [from AbstractNoFI.v: no_free_certification_trace_mu]

    ==========================================================================
    STATUS: Fully proven. Zero Admitted.
    ==========================================================================
*)

From Coq Require Import List Arith.PeanoNat Bool Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof AbstractNoFI
                           MuLedgerConservation.

(** =========================================================================
    PART 1: STRUCTURAL CREATION IS FREE (intentional design)
    =========================================================================

    PNEW and MORPH use instruction_cost = mu_delta (not S mu_delta).
    When called with mu_delta=0, they cost nothing.
    This is not a bug — it is the designed behavior:
      - Structure creation is exploration, not commitment
      - Certification (MORPH_ASSERT etc.) is the commitment that costs

    IMPORTANT: These theorems prove that a cost of 0 IS POSSIBLE.
    They do not say PNEW/MORPH always cost 0 — users may supply any mu_delta.
*)

(** PNEW with mu_delta=0 costs 0 — structural creation is free. *)
Lemma pnew_can_be_free :
  exists region,
    instruction_cost (instr_pnew region 0) = 0.
Proof.
  exists []. simpl. reflexivity.
Qed.

(** MORPH with mu_delta=0 costs 0 — morphism creation is free. *)
Lemma morph_can_be_free :
  exists dst src dst_mod cidx,
    instruction_cost (instr_morph dst src dst_mod cidx 0) = 0.
Proof.
  exists 0, 0, 0, 0. simpl. reflexivity.
Qed.

(** MORPH_DELETE costs 0 when mu_delta=0 — deletion is free. *)
Lemma morph_delete_can_be_free :
  exists mid,
    instruction_cost (instr_morph_delete mid 0) = 0.
Proof.
  exists 0. simpl. reflexivity.
Qed.

(** =========================================================================
    PART 2: CERTIFIED INSIGHT IS ALWAYS NON-FREE
    =========================================================================

    This is the core No Free Insight claim, stated in the formal vocabulary
    of "certified insight events."

    A transition is a CERTIFIED INSIGHT EVENT if it changes a cert channel
    from absent to present:
      - csr_cert_addr: 0 → nonzero (has_supra_cert becomes true)
      - vm_certified: false → true

    THEOREM: Any certified insight event has instruction_cost ≥ 1 and
    causes mu to increase by at least 1.

    This is exactly certification_requires_positive_mu from AbstractNoFI.v,
    restated in the "insight event" vocabulary.
*)

(** InsightEvent_Cert: a state transition is a certified insight event if
    either cert channel goes from absent to present. *)
Definition is_cert_insight_event (s : VMState) (i : vm_instruction) : Prop :=
  (s.(vm_csrs).(csr_cert_addr) = 0 /\
   (vm_apply s i).(vm_csrs).(csr_cert_addr) <> 0)
  \/
  (s.(vm_certified) = false /\
   (vm_apply s i).(vm_certified) = true).

(** certified_insight_nonfree: THE CORE NoFI THEOREM FOR INSIGHT EVENTS.
    Any certified insight event costs ≥ 1 and causes mu to increase. *)
Theorem certified_insight_nonfree :
  forall (s : VMState) (i : vm_instruction),
    is_cert_insight_event s i ->
    instruction_cost i >= 1 /\
    (vm_apply s i).(vm_mu) >= s.(vm_mu) + 1.
Proof.
  intros s i Hevent.
  unfold is_cert_insight_event in Hevent.
  split.
  - (* instruction_cost ≥ 1 *)
    destruct Hevent as [[Ha0 Ha1] | [Hb0 Hb1]].
    + exact (no_free_certification s i Ha0 Ha1).
    + exact (no_free_certification_certified s i Hb0 Hb1).
  - (* mu increased by ≥ 1 *)
    destruct Hevent as [[Ha0 Ha1] | [Hb0 Hb1]].
    + exact (no_free_certification_mu s i Ha0 Ha1).
    + exact (no_free_certification_certified_mu s i Hb0 Hb1).
Qed.

(** =========================================================================
    PART 3: MORPH_ASSERT IS A CERTIFIED INSIGHT EVENT
    =========================================================================

    MORPH_ASSERT is the primary structural certification opcode.
    When it succeeds (no error), it sets csr_cert_addr to a nonzero value.
    Therefore it is always a certified insight event from an uncertified state.

    This connects structural morphism certification to the cert channel.
*)

(** morph_assert_is_cert_setter: MORPH_ASSERT is in cert_addr_setterb.
    This means it CAN change csr_cert_addr — it is a cert-addr-setter. *)
Lemma morph_assert_is_cert_setter :
  forall mid p c cost,
    cert_addr_setterb (instr_morph_assert mid p c cost) = true.
Proof.
  intros. simpl. reflexivity.
Qed.

(** morph_assert_cost_pos: MORPH_ASSERT always costs ≥ 1.
    (Definitional: instruction_cost (instr_morph_assert ...) = S cost ≥ 1) *)
Lemma morph_assert_cost_pos :
  forall mid p c cost,
    instruction_cost (instr_morph_assert mid p c cost) >= 1.
Proof.
  intros. simpl. lia.
Qed.

(** morph_assert_mu_pos: MORPH_ASSERT always increases mu by ≥ 1. *)
Lemma morph_assert_mu_pos :
  forall (s : VMState) mid p c cost,
    (vm_apply s (instr_morph_assert mid p c cost)).(vm_mu) >= s.(vm_mu) + 1.
Proof.
  intros. rewrite vm_apply_mu. simpl. lia.
Qed.

(** =========================================================================
    PART 4: STRUCTURAL OPS PRESERVE THE CERT CHANNEL
    =========================================================================

    The structural creation/manipulation ops (PNEW, MORPH, COMPOSE, etc.)
    do NOT set csr_cert_addr. They are NOT cert_addr_setters.
    Therefore they cannot create certified insight events (alone).

    This proves the "negative cases" requirement: pure structural operations
    without a cert-setter in the trace cannot produce cert evidence.

    The key theorem: for all these ops, cert_addr_setterb = false.
    This is exactly what thiele_non_cert_addr_setter_preserves covers:
    cert_addr_setterb = false → csr_cert_addr preserved.
*)

(** pnew_not_cert_setter: PNEW does not set csr_cert_addr. *)
Lemma pnew_not_cert_setter :
  forall region cost,
    cert_addr_setterb (instr_pnew region cost) = false.
Proof.
  intros. simpl. reflexivity.
Qed.

(** morph_not_cert_setter: MORPH does not set csr_cert_addr. *)
Lemma morph_not_cert_setter :
  forall dst src dst_mod cidx cost,
    cert_addr_setterb (instr_morph dst src dst_mod cidx cost) = false.
Proof.
  intros. simpl. reflexivity.
Qed.

(** morph_delete_not_cert_setter: MORPH_DELETE does not set csr_cert_addr. *)
Lemma morph_delete_not_cert_setter :
  forall mid cost,
    cert_addr_setterb (instr_morph_delete mid cost) = false.
Proof.
  intros. simpl. reflexivity.
Qed.

(** morph_tensor_not_cert_setter: MORPH_TENSOR does not set csr_cert_addr. *)
Lemma morph_tensor_not_cert_setter :
  forall m1 m2 dst cost,
    cert_addr_setterb (instr_morph_tensor m1 m2 dst cost) = false.
Proof.
  intros. simpl. reflexivity.
Qed.

(** morph_get_not_cert_setter: MORPH_GET does not set csr_cert_addr. *)
Lemma morph_get_not_cert_setter :
  forall mid dst typ cost,
    cert_addr_setterb (instr_morph_get mid dst typ cost) = false.
Proof.
  intros. simpl. reflexivity.
Qed.

(** compose_not_cert_setter: COMPOSE does not set csr_cert_addr. *)
Lemma compose_not_cert_setter :
  forall r1 r2 dst cost,
    cert_addr_setterb (instr_compose r1 r2 dst cost) = false.
Proof.
  intros. simpl. reflexivity.
Qed.

(** morph_id_not_cert_setter: MORPH_ID does not set csr_cert_addr. *)
Lemma morph_id_not_cert_setter :
  forall mid dst cost,
    cert_addr_setterb (instr_morph_id mid dst cost) = false.
Proof.
  intros. simpl. reflexivity.
Qed.

(** structural_ops_preserve_cert_addr: PNEW/MORPH/COMPOSE/DELETE/TENSOR/GET/ID
    all preserve csr_cert_addr exactly (they are not cert_addr_setters).
    Therefore no combination of these operations alone can produce cert evidence. *)
Lemma pnew_preserves_cert_addr :
  forall (s : VMState) region cost,
    (vm_apply s (instr_pnew region cost)).(vm_csrs).(csr_cert_addr) =
    s.(vm_csrs).(csr_cert_addr).
Proof.
  intros. apply thiele_non_cert_addr_setter_preserves. simpl. reflexivity.
Qed.

Lemma morph_preserves_cert_addr :
  forall (s : VMState) dst src dst_mod cidx cost,
    (vm_apply s (instr_morph dst src dst_mod cidx cost)).(vm_csrs).(csr_cert_addr) =
    s.(vm_csrs).(csr_cert_addr).
Proof.
  intros. apply thiele_non_cert_addr_setter_preserves. simpl. reflexivity.
Qed.

(** =========================================================================
    PART 5: TRACE-LEVEL — STRUCTURAL-ONLY TRACES CANNOT CERTIFY
    =========================================================================

    A trace consisting ONLY of structural ops (no cert-setters) cannot
    produce cert evidence, no matter how many structural ops are composed.

    This is the formal "no smuggling through composition" theorem for
    structural ops specifically.
*)

(** structural_trace_nonfree: if a trace consists only of structural ops
    (all cert_addr_setterb = false), then cert_addr is preserved.
    This is a direct consequence of abstract_nfi. *)
Theorem structural_trace_preserves_cert_addr :
  forall (trace : list vm_instruction) (s0 : VMState),
    Forall (fun i => cert_addr_setterb i = false) trace ->
    (acm_run thiele_cert_machine trace s0).(vm_csrs).(csr_cert_addr) =
    s0.(vm_csrs).(csr_cert_addr).
Proof.
  induction trace as [| i rest IH]; intros s0 Hforall.
  - simpl. reflexivity.
  - inversion Hforall as [| ? ? Hi_false Hrest]; subst.
    simpl.
    rewrite (IH (vm_apply s0 i) Hrest).
    exact (thiele_non_cert_addr_setter_preserves s0 i Hi_false).
Qed.

(** COROLLARY: If cert_addr was 0 and the trace had no cert-setters,
    cert_addr is still 0 afterward — structural ops cannot certify. *)
Corollary structural_only_trace_cannot_certify :
  forall (trace : list vm_instruction) (s0 : VMState),
    s0.(vm_csrs).(csr_cert_addr) = 0 ->
    Forall (fun i => cert_addr_setterb i = false) trace ->
    (acm_run thiele_cert_machine trace s0).(vm_csrs).(csr_cert_addr) = 0.
Proof.
  intros trace s0 Hzero Hforall.
  rewrite (structural_trace_preserves_cert_addr trace s0 Hforall).
  exact Hzero.
Qed.

(** =========================================================================
    PART 6: THE INSIGHT DESIGN PRINCIPLE — SUMMARY
    =========================================================================

    The following theorem packages the full NoFI design:

    no_free_certified_insight:
      - Structural creation (PNEW, MORPH, COMPOSE, etc.): CAN be zero-cost.
        These ops preserve csr_cert_addr — they do not produce cert evidence.
      - Certified insight (MORPH_ASSERT, LASSERT, EMIT, REVEAL, LJOIN, CERTIFY):
        ALWAYS cost ≥ 1 by instruction_cost definition.
        These ops CAN change csr_cert_addr (cert_addr_setterb = true).
      - Therefore: cert evidence cannot appear via structural ops alone.
        Cert evidence requires at least one certified-insight-class instruction.
        That instruction has cost ≥ 1, so mu grows by ≥ 1.

    This is the precise formal content of "No Free Insight."
*)

(** no_free_certified_insight: the complete, precise NoFI statement.
    Cert evidence requires a cert-setter, which costs ≥ 1, so mu grew ≥ 1.
    Structural ops (PNEW, MORPH, etc.) cannot produce cert evidence.
    This is the formal design boundary. *)
Theorem no_free_certified_insight :
  forall (trace : list vm_instruction) (s0 : VMState),
    s0.(vm_csrs).(csr_cert_addr) = 0 ->
    (acm_run thiele_cert_machine trace s0).(vm_csrs).(csr_cert_addr) <> 0 ->
    (* Then: the trace contained a certified-insight-class instruction... *)
    (exists i, In i trace /\
               cert_addr_setterb i = true /\
               instruction_cost i >= 1) /\
    (* ...and mu grew by at least 1 *)
    (acm_run thiele_cert_machine trace s0).(vm_mu) >= s0.(vm_mu) + 1.
Proof.
  intros trace s0 Hzero Hnonzero.
  split.
  - exact (thiele_abstract_nfi_cost trace s0 Hzero Hnonzero).
  - exact (no_free_certification_trace_mu trace s0 Hzero Hnonzero).
Qed.
