(** PartitionRefinementNoFI: partition refinement is not free.

    Structural partition ops (PNEW, PSPLIT, PMERGE) change the partition graph
    but do NOT change any cert channel (csr_cert_addr, vm_certified). They are
    exploration — building structure without committing to it — and can have
    cost = 0. Certified partition insight ops (LASSERT, MORPH_ASSERT, LJOIN,
    EMIT, REVEAL) certify structural claims and always cost ≥ 1.

    Partition structure can be built for free. Certified partition knowledge
    cannot be acquired for free.

    partition_structural_ops_not_cert_setters: PNEW, PSPLIT, PMERGE have
    cert_addr_setterb = false — definitionally excluded from the cert-setter
    predicate.
    partition_structural_ops_can_be_free: each can be called with cost=0.
    partition_structural_trace_cannot_certify: a trace of only PNEW/PSPLIT/PMERGE
    cannot change csr_cert_addr.
    partition_refinement_nonfree: if cert channels go from absent to present over
    any trace, the trace contains a cert-setter with cost ≥ 1, and μ grew by
    at least 1.
    partition_free_but_certification_nonfree: packages the complete boundary.
*)

From Coq Require Import List Arith.PeanoNat Bool Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof AbstractNoFI
                           MuLedgerConservation InsightTaxonomy.

(**

    cert_addr_setterb identifies the five opcodes that CAN set csr_cert_addr:
    REVEAL, EMIT, LJOIN, LASSERT, MORPH_ASSERT.

    PNEW, PSPLIT, PMERGE are absent from that list. These lemmas make that
    explicit for each partition structural opcode.
*)

Lemma psplit_not_cert_addr_setter :
  forall (module : ModuleID) (left right : list nat) (cost : nat),
    cert_addr_setterb (instr_psplit module left right cost) = false.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma pmerge_not_cert_addr_setter :
  forall (m1 m2 : ModuleID) (cost : nat),
    cert_addr_setterb (instr_pmerge m1 m2 cost) = false.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma psplit_preserves_cert_addr :
  forall (s : VMState) (module : ModuleID) (left right : list nat) (cost : nat),
    (vm_apply s (instr_psplit module left right cost)).(vm_csrs).(csr_cert_addr) =
    s.(vm_csrs).(csr_cert_addr).
Proof.
  intros. apply thiele_non_cert_addr_setter_preserves. simpl. reflexivity.
Qed.

Lemma pmerge_preserves_cert_addr :
  forall (s : VMState) (m1 m2 : ModuleID) (cost : nat),
    (vm_apply s (instr_pmerge m1 m2 cost)).(vm_csrs).(csr_cert_addr) =
    s.(vm_csrs).(csr_cert_addr).
Proof.
  intros. apply thiele_non_cert_addr_setter_preserves. simpl. reflexivity.
Qed.

(** Unified statement: none of the three partition structural opcodes are
    cert-setters. This is the formal basis for the "exploration is free" claim. *)
Theorem partition_structural_ops_not_cert_setters :
  (forall (region : list nat) (cost : nat),
     cert_addr_setterb (instr_pnew region cost) = false) /\
  (forall (m : ModuleID) (left right : list nat) (cost : nat),
     cert_addr_setterb (instr_psplit m left right cost) = false) /\
  (forall (m1 m2 : ModuleID) (cost : nat),
     cert_addr_setterb (instr_pmerge m1 m2 cost) = false).
Proof.
  repeat split; intros; reflexivity.
Qed.

(**

    With mu_delta=0, each partition op costs exactly 0. This is the design
    intent: exploration does not require paying cost. The cost parameter
    mu_delta is fully under the caller's control, and 0 is always valid.
*)

Lemma psplit_can_be_free :
  exists (m : ModuleID) (left right : list nat),
    instruction_cost (instr_psplit m left right 0) = 0.
Proof.
  exists 0, [], []. simpl. reflexivity.
Qed.

Lemma pmerge_can_be_free :
  exists (m1 m2 : ModuleID),
    instruction_cost (instr_pmerge m1 m2 0) = 0.
Proof.
  exists 0, 0. simpl. reflexivity.
Qed.

Theorem partition_structural_ops_can_be_free :
  (exists (region : list nat), instruction_cost (instr_pnew region 0) = 0) /\
  (exists (m : ModuleID) (left right : list nat),
     instruction_cost (instr_psplit m left right 0) = 0) /\
  (exists (m1 m2 : ModuleID), instruction_cost (instr_pmerge m1 m2 0) = 0).
Proof.
  refine (conj _ (conj _ _)).
  - exact pnew_can_be_free.
  - exact psplit_can_be_free.
  - exact pmerge_can_be_free.
Qed.

(**

    A trace in which every instruction is one of PNEW, PSPLIT, PMERGE
    (all cert_addr_setterb = false) cannot change csr_cert_addr.

    This is the formal statement of: "no amount of structural partition
    manipulation can produce cert evidence."
*)

Inductive partition_structural_instr : vm_instruction -> Prop :=
  | psi_pnew   : forall r c,   partition_structural_instr (instr_pnew r c)
  | psi_psplit : forall m l r c, partition_structural_instr (instr_psplit m l r c)
  | psi_pmerge : forall m1 m2 c, partition_structural_instr (instr_pmerge m1 m2 c).

Lemma partition_structural_not_cert_setter :
  forall i, partition_structural_instr i -> cert_addr_setterb i = false.
Proof.
  intros i Hi. inversion Hi; simpl; reflexivity.
Qed.

Theorem partition_structural_trace_cannot_certify :
  forall (trace : list vm_instruction) (s0 : VMState),
    Forall partition_structural_instr trace ->
    (acm_run thiele_cert_machine trace s0).(vm_csrs).(csr_cert_addr) =
    s0.(vm_csrs).(csr_cert_addr).
Proof.
  intros trace s0 Hpsi.
  apply structural_trace_preserves_cert_addr.
  eapply Forall_impl; [| exact Hpsi].
  intros i Hi. exact (partition_structural_not_cert_setter i Hi).
Qed.

Corollary partition_structural_only_trace_stays_uncertified :
  forall (trace : list vm_instruction) (s0 : VMState),
    s0.(vm_csrs).(csr_cert_addr) = 0 ->
    Forall partition_structural_instr trace ->
    (acm_run thiele_cert_machine trace s0).(vm_csrs).(csr_cert_addr) = 0.
Proof.
  intros trace s0 Hzero Hpsi.
  rewrite (partition_structural_trace_cannot_certify trace s0 Hpsi).
  exact Hzero.
Qed.

(**

    If cert channels go from absent to present over any trace, then:
    (a) the trace contains at least one cert-setter instruction with cost ≥ 1
    (b) mu grew by at least 1

    This is the partition domain instantiation of no_free_certified_insight
    from InsightTaxonomy.v — stated explicitly as the "partition refinement
    boundary" theorem so it is findable under its conceptual name.

    WHAT "PARTITION REFINEMENT" MEANS HERE:
    Going from csr_cert_addr = 0 (no certified structural knowledge) to
    csr_cert_addr ≠ 0 (a certified claim has been registered) constitutes
    a strict refinement of what the machine formally asserts about its
    partition structure. This refinement cannot happen for free.
*)

Theorem partition_refinement_nonfree :
  forall (trace : list vm_instruction) (s0 : VMState),
    s0.(vm_csrs).(csr_cert_addr) = 0 ->
    (acm_run thiele_cert_machine trace s0).(vm_csrs).(csr_cert_addr) <> 0 ->
    (exists i, In i trace /\
               cert_addr_setterb i = true /\
               instruction_cost i >= 1) /\
    (acm_run thiele_cert_machine trace s0).(vm_mu) >= s0.(vm_mu) + 1.
Proof.
  intros trace s0 Hzero Hnonzero.
  exact (no_free_certified_insight trace s0 Hzero Hnonzero).
Qed.

(**

    A single theorem that packages the full boundary:
    - Partition structure creation/manipulation: CAN be zero-cost
    - Partition structure manipulation: CANNOT change cert channels
    - Certified partition knowledge: CANNOT be acquired for free

    This is the formal content of "partition refinement is non-free."
*)

Theorem partition_free_but_certification_nonfree :
  (* Structural ops have controllable cost (can be 0) *)
  (exists r,   instruction_cost (instr_pnew r 0) = 0) /\
  (exists m l r, instruction_cost (instr_psplit m l r 0) = 0) /\
  (exists m1 m2, instruction_cost (instr_pmerge m1 m2 0) = 0) /\
  (* Structural ops are not cert-setters *)
  (forall r c,   cert_addr_setterb (instr_pnew r c) = false) /\
  (forall m l r c, cert_addr_setterb (instr_psplit m l r c) = false) /\
  (forall m1 m2 c, cert_addr_setterb (instr_pmerge m1 m2 c) = false) /\
  (* Certified partition knowledge cannot be acquired for free *)
  (forall (trace : list vm_instruction) (s0 : VMState),
     s0.(vm_csrs).(csr_cert_addr) = 0 ->
     (acm_run thiele_cert_machine trace s0).(vm_csrs).(csr_cert_addr) <> 0 ->
     (acm_run thiele_cert_machine trace s0).(vm_mu) >= s0.(vm_mu) + 1).
Proof.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - exact pnew_can_be_free.
  - exact psplit_can_be_free.
  - exact pmerge_can_be_free.
  - intros. reflexivity.
  - intros. reflexivity.
  - intros. reflexivity.
  - intros trace s0 Hzero Hnonzero.
    exact (no_free_certification_trace_mu trace s0 Hzero Hnonzero).
Qed.
