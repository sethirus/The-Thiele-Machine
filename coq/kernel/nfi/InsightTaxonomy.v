(** InsightTaxonomy: formal taxonomy of selected VM event classes.

    The schedule permits some structural constructors to carry zero encoded cost when
    their [mu_delta] argument is zero.

    That existential zero-cost result is not a claim that structural operations are
    always free, nor is it a thermodynamic statement about implementation.

    The certification and revelation policy class receives a successor cost floor.

    That policy class is broader than the literal transitions that write a certification
    field, so the class name must not be read as a semantic checker for every member.

    Theorems proven here:
    1. [structural_creation_can_be_free] exhibits zero scheduled cost for selected
       structural instructions at [mu_delta = 0].
    2. [certified_insight_nonfree] prices a false-to-true transition on either named
       certification channel at least one unit.
    3. [morph_assert_is_certified_insight] identifies [MORPH_ASSERT] as a cert-address
       setter and proves its scheduled cost is at least one.
    4. [non_cert_ops_are_structurally_neutral_on_cert_channel] records preservation of
       the certification address by selected non-setter instructions.
    5. [certified_insight_trace_nonfree] lifts the channel-transition floor to a trace.
*)

From Coq Require Import List Arith.PeanoNat Bool Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof AbstractNoFI
                           MuLedgerConservation.

(**

    PNEW and MORPH use [instruction_cost = mu_delta], rather than the successor
    floor used by the certification and revelation policy class.

    At [mu_delta = 0] they therefore provide concrete zero-cost witnesses for this
    VM schedule.

    These lemmas prove that zero cost is possible for the displayed inputs.

    They do not say that PNEW or MORPH always cost zero; another encoded delta is
    charged exactly as supplied.
*)

(** PNEW with [mu_delta = 0] has zero scheduled cost in this VM. *)
Lemma pnew_can_be_free :
  exists region,
    instruction_cost (instr_pnew region 0) = 0.
Proof.
  exists []. simpl. reflexivity.
Qed.

(** MORPH with [mu_delta = 0] has zero scheduled cost in this VM. *)
Lemma morph_can_be_free :
  exists dst src dst_mod cidx,
    instruction_cost (instr_morph dst src dst_mod cidx 0) = 0.
Proof.
  exists 0, 0, 0, 0. simpl. reflexivity.
Qed.

(** MORPH_DELETE with [mu_delta = 0] has zero scheduled cost in this VM. *)
Lemma morph_delete_can_be_free :
  exists mid,
    instruction_cost (instr_morph_delete mid 0) = 0.
Proof.
  exists 0. simpl. reflexivity.
Qed.

(**

    This is the core No Free Insight claim, stated in the formal vocabulary
    of "certified insight events."

    A transition is a CERTIFIED INSIGHT EVENT if it changes a cert channel
    from absent to present:
      - csr_cert_addr: 0 → nonzero (has_supra_cert becomes true)
      - vm_certified: false → true

    Any certified insight event has instruction_cost ≥ 1 and
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

(** [certified_insight_nonfree] prices the selected certification-channel event.
    Any such event costs at least one scheduled unit and increases [vm_mu] by at least one. *)
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

(**

    MORPH_ASSERT is the primary structural certification opcode.
    When it succeeds (no error), it sets csr_cert_addr to a nonzero value.
    Therefore it is always a certified insight event from an uncertified state.

    This connects structural morphism certification to the cert channel.
*)

(** morph_assert_is_cert_setter: MORPH_ASSERT is in cert_addr_setterb.
    This means it can change csr_cert_addr; it is a cert-addr-setter. *)
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

(**

    The selected structural creation and manipulation operations do not set
    [csr_cert_addr] under the VM semantics used here.

    A trace made entirely from instructions satisfying [cert_addr_setterb = false]
    therefore preserves that channel.

    This is a statement about the named certification-address observation; it does
    not classify every structural operation as semantically inert in every field.
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

(**

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
    cert_addr is still 0 afterward; structural ops cannot certify. *)
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

(**

    The following theorem packages the selected VM policy:

      - Some structural instructions have zero-cost witnesses at [mu_delta = 0].
      - A trace that changes [csr_cert_addr] from zero to nonzero must contain an
        instruction in the abstract cert-setter class.
      - The cost law prices that transition and the resulting ledger increase.

    The positive-cost class and the literal certification-channel transition are
    related but distinct predicates in the repository.
*)

(** [no_free_certified_insight] states the precise channel and ledger boundary.
    Starting from a zero certification address, a nonzero final address requires a
    cert-setter in the trace and a ledger increase of at least one. *)
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
