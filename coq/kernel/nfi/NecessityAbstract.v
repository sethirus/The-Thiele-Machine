(** NecessityAbstract.v — Universal Projection Necessity Framework

    This file generalizes the necessity result of NecessityOfMuLedger.v to an
    arbitrary classical computation model represented as a projection

        P : VMState → C

    where C is any configuration type (tape+head, registers+memory, cost state,
    certified state, etc.).

    GENERIC NECESSITY THEOREM:
      For any P, if two concrete witness states are indistinguishable under P
      but differ in vm_mu or vm_certified, then no oracle Omega : C → _ can
      correctly predict vm_mu or vm_certified for all VMStates.

    Proof method: the same contradiction used in NecessityOfMuLedger.v —
    equal inputs to a function must produce equal outputs.

    FOUR NAMED SEPARATION RESULTS (four independent instantiations):

      A. Strict shadow   P = (mem, regs, pc)
         Witnesses: CERTIFY 0 vs PNEW [] 0 from the zero state.
         Neither vm_mu nor vm_certified is computable from P.

      B. Cost-annotated  P = (mem, regs, pc, mu)
         Witnesses: CERTIFY 2 vs PNEW [] 3 from the zero state.
         Both reach mu = 3; only CERTIFY sets vm_certified = true.
         vm_certified is not computable from P even knowing vm_mu.

      C. Cert-annotated  P = (mem, regs, pc, certified)
         Witnesses: CERTIFY 0 vs CERTIFY 1 from the zero state.
         Both set vm_certified = true; their vm_mu values are 1 and 2.
         vm_mu is not computable from P even knowing vm_certified.

      D. Full μ-ledger shadow  P = (mem, regs, pc, mu, certified)
         Witnesses: categorical_separation (PartitionSeparation.v §10).
         Two states with identical P_full but different pg_morphisms.
         vm_graph is not computable from P even knowing the full μ-ledger.

    COMPLETE INDEPENDENCE CLASSIFICATION:
      vm_mu ⊥ (mem, regs, pc)                         [from A, §3]
      vm_certified ⊥ (mem, regs, pc)                  [from A, §3]
      vm_certified ⊥ (mem, regs, pc, vm_mu)           [from B, §4]
      vm_mu ⊥ (mem, regs, pc, vm_certified)           [from C, §5]
      vm_graph ⊥ (mem, regs, pc, vm_mu, vm_certified) [from D, §9]

    The three independent non-classical components of VMState are:
      1. vm_mu        — the μ-ledger balance (§3–§5)
      2. vm_certified — the certification flag (§3–§5)
      3. vm_graph     — the categorical (partition/morphism) structure (§9)

    NAMED MACHINE INSTANCES:
      Turing machine  → P_strict  = strict shadow  (tape+head+state ≅ mem+regs+pc)
      RAM machine     → P_strict  = strict shadow  (registers+memory+pc)
      Cost semantics  → P_cost    = cost-annotated shadow
      Effect system   → P_cert    = cert-annotated shadow
      Full shadow     → P_full    = (mem, regs, pc, mu, certified)
*)

From Coq Require Import List Arith.PeanoNat Bool Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof PartitionSeparation.


(** ═══════════════════════════════════════════════════════════════════════════
    §1.  GENERIC PROJECTION NECESSITY THEOREMS

    The three theorems below are proved by a uniform argument:
    equal inputs to Omega force equal outputs, but the witnesses have
    unequal (vm_mu, vm_certified), yielding a contradiction.
    ═══════════════════════════════════════════════════════════════════════════ *)

(** No oracle can recover vm_mu from a projection that conflates two states
    with different vm_mu values. *)
Theorem generic_mu_necessity :
  forall {C : Type} (P : VMState -> C) (sA sB : VMState),
    P sA = P sB ->
    sA.(vm_mu) <> sB.(vm_mu) ->
    ~ exists (Omega : C -> nat), forall s, Omega (P s) = s.(vm_mu).
Proof.
  intros C P sA sB Heq Hdiff [Omega HOmega].
  assert (HA : Omega (P sA) = sA.(vm_mu)) by apply HOmega.
  assert (HB : Omega (P sB) = sB.(vm_mu)) by apply HOmega.
  rewrite Heq in HA.
  rewrite HA in HB.
  exact (Hdiff HB).
Qed.

(** No oracle can recover vm_certified from a projection that conflates two
    states with different vm_certified values. *)
Theorem generic_cert_necessity :
  forall {C : Type} (P : VMState -> C) (sA sB : VMState),
    P sA = P sB ->
    sA.(vm_certified) <> sB.(vm_certified) ->
    ~ exists (Omega : C -> bool), forall s, Omega (P s) = s.(vm_certified).
Proof.
  intros C P sA sB Heq Hdiff [Omega HOmega].
  assert (HA : Omega (P sA) = sA.(vm_certified)) by apply HOmega.
  assert (HB : Omega (P sB) = sB.(vm_certified)) by apply HOmega.
  rewrite Heq in HA.
  rewrite HA in HB.
  exact (Hdiff HB).
Qed.

(** No oracle can recover the pair (vm_mu, vm_certified) from a projection
    that conflates two states with different pairs. *)
Theorem generic_pair_necessity :
  forall {C : Type} (P : VMState -> C) (sA sB : VMState),
    P sA = P sB ->
    (sA.(vm_mu), sA.(vm_certified)) <> (sB.(vm_mu), sB.(vm_certified)) ->
    ~ exists (Omega : C -> nat * bool),
        forall s, Omega (P s) = (s.(vm_mu), s.(vm_certified)).
Proof.
  intros C P sA sB Heq Hdiff [Omega HOmega].
  assert (HA : Omega (P sA) = (sA.(vm_mu), sA.(vm_certified))) by apply HOmega.
  assert (HB : Omega (P sB) = (sB.(vm_mu), sB.(vm_certified))) by apply HOmega.
  rewrite Heq in HA.
  rewrite HA in HB.
  exact (Hdiff HB).
Qed.


(** ═══════════════════════════════════════════════════════════════════════════
    §2.  SHARED WITNESS INFRASTRUCTURE

    abs_zero is the common initial state for all three separation arguments.
    All witness programs start from abs_zero and execute one instruction.

    CERTIFY d:  advances pc by 1, sets vm_certified := true,
                charges vm_mu += S d.  vm_mem and vm_regs unchanged.

    PNEW [] c:  advances pc by 1, preserves vm_certified (stays false),
                charges vm_mu += c.    vm_mem and vm_regs unchanged.
    ═══════════════════════════════════════════════════════════════════════════ *)

Definition abs_empty_graph : PartitionGraph := {|
  pg_next_id       := 0;
  pg_modules       := [];
  pg_next_morph_id := 0;
  pg_morphisms     := []
|}.

Definition abs_empty_csrs : CSRState :=
  {| csr_cert_addr := 0; csr_status := 0; csr_err := 0; csr_heap_base := 0 |}.

Definition abs_empty_witness : WitnessCounts :=
  {| wc_same_00 := 0; wc_diff_00 := 0;
     wc_same_01 := 0; wc_diff_01 := 0;
     wc_same_10 := 0; wc_diff_10 := 0;
     wc_same_11 := 0; wc_diff_11 := 0 |}.

(** abs_zero: the canonical zero VMState. vm_mu = 0, vm_certified = false,
    all other fields empty or false.  All three separation arguments start here. *)
Definition abs_zero : VMState := {|
  vm_graph     := abs_empty_graph;
  vm_csrs      := abs_empty_csrs;
  vm_regs      := [];
  vm_mem       := [];
  vm_pc        := 0;
  vm_mu        := 0;
  vm_mu_tensor := repeat 0 16;
  vm_err       := false;
  vm_logic_acc := 0;
  vm_mstatus   := 0;
  vm_witness   := abs_empty_witness;
  vm_certified := false
|}.

(** ── CERTIFY helper lemmas ─────────────────────────────────────────────── *)

Lemma abs_certify_mem :
  forall s d, (vm_apply s (instr_certify d)).(vm_mem) = s.(vm_mem).
Proof. intros. unfold vm_apply. simpl. reflexivity. Qed.

Lemma abs_certify_regs :
  forall s d, (vm_apply s (instr_certify d)).(vm_regs) = s.(vm_regs).
Proof. intros. unfold vm_apply. simpl. reflexivity. Qed.

Lemma abs_certify_pc :
  forall s d, (vm_apply s (instr_certify d)).(vm_pc) = S s.(vm_pc).
Proof. intros. unfold vm_apply. simpl. reflexivity. Qed.

Lemma abs_certify_certified :
  forall s d, (vm_apply s (instr_certify d)).(vm_certified) = true.
Proof. intros. unfold vm_apply. simpl. reflexivity. Qed.

Lemma abs_certify_mu :
  forall s d, (vm_apply s (instr_certify d)).(vm_mu) = s.(vm_mu) + S d.
Proof. intros. unfold vm_apply. simpl. reflexivity. Qed.

(** ── PNEW helper lemmas ────────────────────────────────────────────────── *)

Lemma abs_pnew_mem :
  forall s r c, (vm_apply s (instr_pnew r c)).(vm_mem) = s.(vm_mem).
Proof.
  intros s r c. unfold vm_apply.
  destruct (graph_add_module s.(vm_graph) (List.seq 0 _) []) as [g' _].
  unfold advance_state. simpl. reflexivity.
Qed.

Lemma abs_pnew_regs :
  forall s r c, (vm_apply s (instr_pnew r c)).(vm_regs) = s.(vm_regs).
Proof.
  intros s r c. unfold vm_apply.
  destruct (graph_add_module s.(vm_graph) (List.seq 0 _) []) as [g' _].
  unfold advance_state. simpl. reflexivity.
Qed.

Lemma abs_pnew_pc :
  forall s r c, (vm_apply s (instr_pnew r c)).(vm_pc) = S s.(vm_pc).
Proof.
  intros s r c. unfold vm_apply.
  destruct (graph_add_module s.(vm_graph) (List.seq 0 _) []) as [g' _].
  unfold advance_state. simpl. reflexivity.
Qed.

Lemma abs_pnew_certified :
  forall s r c, (vm_apply s (instr_pnew r c)).(vm_certified) = s.(vm_certified).
Proof.
  intros s r c. unfold vm_apply.
  destruct (graph_add_module s.(vm_graph) (List.seq 0 _) []) as [g' _].
  unfold advance_state. simpl. reflexivity.
Qed.

Lemma abs_pnew_mu :
  forall s r c, (vm_apply s (instr_pnew r c)).(vm_mu) = s.(vm_mu) + c.
Proof.
  intros s r c. unfold vm_apply.
  destruct (graph_add_module s.(vm_graph) (List.seq 0 _) []) as [g' _].
  unfold advance_state, apply_cost, instruction_cost. simpl. reflexivity.
Qed.


(** ═══════════════════════════════════════════════════════════════════════════
    §3.  SEPARATION A — STRICT SHADOW  (TURING / RAM MODEL)

    P_strict = (mem, regs, pc): the strictly Turing-classical projection.
    This is the analog of the tape+head+control-state of a Turing machine,
    or the registers+memory+pc of a RAM machine.

    WITNESSES:
      abs_A_strict = vm_apply abs_zero (instr_certify 0)
        → vm_mu = 1, vm_certified = true, mem=[], regs=[], pc=1.
      abs_B_strict = vm_apply abs_zero (instr_pnew [] 0)
        → vm_mu = 0, vm_certified = false, mem=[], regs=[], pc=1.

    P_strict abs_A_strict = P_strict abs_B_strict = ([], [], 1).
    vm_mu and vm_certified differ: neither is recoverable from P_strict.
    ═══════════════════════════════════════════════════════════════════════════ *)

Record StrictShadow := mk_strict {
  ss_mem  : list nat;
  ss_regs : list nat;
  ss_pc   : nat
}.

Definition P_strict (s : VMState) : StrictShadow := {|
  ss_mem  := s.(vm_mem);
  ss_regs := s.(vm_regs);
  ss_pc   := s.(vm_pc)
|}.

Definition abs_A_strict : VMState := vm_apply abs_zero (instr_certify 0).
Definition abs_B_strict : VMState := vm_apply abs_zero (instr_pnew [] 0).

Lemma abs_strict_shadow_equal :
  P_strict abs_A_strict = P_strict abs_B_strict.
Proof.
  unfold P_strict, abs_A_strict, abs_B_strict.
  rewrite abs_certify_mem, abs_certify_regs, abs_certify_pc.
  rewrite abs_pnew_mem, abs_pnew_regs, abs_pnew_pc.
  unfold abs_zero. simpl. reflexivity.
Qed.

Lemma abs_strict_mu_A : abs_A_strict.(vm_mu) = 1.
Proof.
  unfold abs_A_strict.
  rewrite abs_certify_mu. unfold abs_zero. simpl. reflexivity.
Qed.

Lemma abs_strict_mu_B : abs_B_strict.(vm_mu) = 0.
Proof.
  unfold abs_B_strict.
  rewrite abs_pnew_mu. unfold abs_zero. simpl. reflexivity.
Qed.

Lemma abs_strict_cert_A : abs_A_strict.(vm_certified) = true.
Proof. unfold abs_A_strict. apply abs_certify_certified. Qed.

Lemma abs_strict_cert_B : abs_B_strict.(vm_certified) = false.
Proof.
  unfold abs_B_strict.
  rewrite abs_pnew_certified. unfold abs_zero. simpl. reflexivity.
Qed.

(** THEOREM A1: No strict-shadow oracle can recover vm_mu.
    Turing machines and RAM machines cannot determine μ-ledger balance
    from (tape, head, state) or (registers, memory, pc). *)
Theorem turing_ram_mu_necessity :
  ~ exists (Omega : StrictShadow -> nat),
      forall s, Omega (P_strict s) = s.(vm_mu).
Proof.
  apply (generic_mu_necessity P_strict abs_A_strict abs_B_strict).
  - exact abs_strict_shadow_equal.
  - rewrite abs_strict_mu_A, abs_strict_mu_B. discriminate.
Qed.

(** THEOREM A2: No strict-shadow oracle can recover vm_certified.
    Turing machines and RAM machines cannot determine certification status
    from (tape, head, state) or (registers, memory, pc). *)
Theorem turing_ram_cert_necessity :
  ~ exists (Omega : StrictShadow -> bool),
      forall s, Omega (P_strict s) = s.(vm_certified).
Proof.
  apply (generic_cert_necessity P_strict abs_A_strict abs_B_strict).
  - exact abs_strict_shadow_equal.
  - rewrite abs_strict_cert_A, abs_strict_cert_B. discriminate.
Qed.

(** THEOREM A3: No strict-shadow oracle can recover the pair (mu, certified).
    This is the joint impossibility — the μ-ledger as a whole is invisible
    to any classical Turing or RAM machine observer. *)
Theorem turing_ram_pair_necessity :
  ~ exists (Omega : StrictShadow -> nat * bool),
      forall s, Omega (P_strict s) = (s.(vm_mu), s.(vm_certified)).
Proof.
  apply (generic_pair_necessity P_strict abs_A_strict abs_B_strict).
  - exact abs_strict_shadow_equal.
  - rewrite abs_strict_mu_A, abs_strict_mu_B, abs_strict_cert_A, abs_strict_cert_B.
    discriminate.
Qed.


(** ═══════════════════════════════════════════════════════════════════════════
    §4.  SEPARATION B — COST-ANNOTATED SHADOW  (COST SEMANTICS MODEL)

    P_cost = (mem, regs, pc, mu): adds the runtime μ-cost to the projection.
    This models cost semantics and any machine that tracks exact resource use.

    WITNESSES:
      abs_A_cost = vm_apply abs_zero (instr_certify 2)
        → instruction_cost = S 2 = 3, so vm_mu = 3, vm_certified = true.
      abs_B_cost = vm_apply abs_zero (instr_pnew [] 3)
        → instruction_cost = 3,       so vm_mu = 3, vm_certified = false.

    Both states have (mem=[], regs=[], pc=1, mu=3).  Only vm_certified differs.
    Therefore: knowing vm_mu is not sufficient to determine vm_certified.

    INTERPRETATION: Certification is not merely resource expenditure.
    A machine can spend the same μ-cost through a non-certification path
    (e.g., a graph structural step) and remain uncertified.  The act of
    invoking CERTIFY is semantically distinct from paying its cost.
    ═══════════════════════════════════════════════════════════════════════════ *)

Record CostShadow := mk_cost {
  cs_mem  : list nat;
  cs_regs : list nat;
  cs_pc   : nat;
  cs_mu   : nat
}.

Definition P_cost (s : VMState) : CostShadow := {|
  cs_mem  := s.(vm_mem);
  cs_regs := s.(vm_regs);
  cs_pc   := s.(vm_pc);
  cs_mu   := s.(vm_mu)
|}.

Definition abs_A_cost : VMState := vm_apply abs_zero (instr_certify 2).
Definition abs_B_cost : VMState := vm_apply abs_zero (instr_pnew [] 3).

Lemma abs_cost_shadow_equal :
  P_cost abs_A_cost = P_cost abs_B_cost.
Proof.
  unfold P_cost, abs_A_cost, abs_B_cost.
  rewrite abs_certify_mem, abs_certify_regs, abs_certify_pc.
  rewrite abs_pnew_mem, abs_pnew_regs, abs_pnew_pc.
  rewrite abs_certify_mu, abs_pnew_mu.
  unfold abs_zero. simpl. reflexivity.
Qed.

Lemma abs_cost_cert_A : abs_A_cost.(vm_certified) = true.
Proof. unfold abs_A_cost. apply abs_certify_certified. Qed.

Lemma abs_cost_cert_B : abs_B_cost.(vm_certified) = false.
Proof.
  unfold abs_B_cost.
  rewrite abs_pnew_certified. unfold abs_zero. simpl. reflexivity.
Qed.

(** THEOREM B: No cost-annotated oracle can recover vm_certified.
    Even a machine that records exact μ-cost at every step cannot determine
    whether CERTIFY was invoked — equal cost can result from a non-certifying
    structural instruction, leaving vm_certified = false. *)
Theorem cost_model_cert_necessity :
  ~ exists (Omega : CostShadow -> bool),
      forall s, Omega (P_cost s) = s.(vm_certified).
Proof.
  apply (generic_cert_necessity P_cost abs_A_cost abs_B_cost).
  - exact abs_cost_shadow_equal.
  - rewrite abs_cost_cert_A, abs_cost_cert_B. discriminate.
Qed.


(** ═══════════════════════════════════════════════════════════════════════════
    §5.  SEPARATION C — CERT-ANNOTATED SHADOW  (EFFECT SYSTEM MODEL)

    P_cert = (mem, regs, pc, certified): adds the certification flag.
    This models effect systems, proof-carrying code, and any machine that
    tracks whether a certification effect has been invoked.

    WITNESSES:
      abs_A_cert = vm_apply abs_zero (instr_certify 0)
        → instruction_cost = S 0 = 1, so vm_mu = 1, vm_certified = true.
      abs_B_cert = vm_apply abs_zero (instr_certify 1)
        → instruction_cost = S 1 = 2, so vm_mu = 2, vm_certified = true.

    Both states have (mem=[], regs=[], pc=1, certified=true).
    Their vm_mu values are 1 and 2 — different.
    Therefore: knowing vm_certified is not sufficient to determine vm_mu.

    INTERPRETATION: The μ-ledger records a quantity distinct from certification
    presence.  Two certified executions can have different μ-balances depending
    on the cost argument supplied to CERTIFY.  The balance is not derivable
    from the fact of certification alone.
    ═══════════════════════════════════════════════════════════════════════════ *)

Record CertAnnotatedShadow := mk_cert_ann {
  cas_mem       : list nat;
  cas_regs      : list nat;
  cas_pc        : nat;
  cas_certified : bool
}.

Definition P_cert (s : VMState) : CertAnnotatedShadow := {|
  cas_mem       := s.(vm_mem);
  cas_regs      := s.(vm_regs);
  cas_pc        := s.(vm_pc);
  cas_certified := s.(vm_certified)
|}.

Definition abs_A_cert : VMState := vm_apply abs_zero (instr_certify 0).
Definition abs_B_cert : VMState := vm_apply abs_zero (instr_certify 1).

Lemma abs_cert_shadow_equal :
  P_cert abs_A_cert = P_cert abs_B_cert.
Proof.
  unfold P_cert, abs_A_cert, abs_B_cert.
  rewrite abs_certify_mem, abs_certify_regs, abs_certify_pc, abs_certify_certified.
  rewrite abs_certify_mem, abs_certify_regs, abs_certify_pc, abs_certify_certified.
  unfold abs_zero. simpl. reflexivity.
Qed.

Lemma abs_cert_mu_A : abs_A_cert.(vm_mu) = 1.
Proof.
  unfold abs_A_cert.
  rewrite abs_certify_mu. unfold abs_zero. simpl. reflexivity.
Qed.

Lemma abs_cert_mu_B : abs_B_cert.(vm_mu) = 2.
Proof.
  unfold abs_B_cert.
  rewrite abs_certify_mu. unfold abs_zero. simpl. reflexivity.
Qed.

(** THEOREM C: No cert-annotated oracle can recover vm_mu.
    Even a machine that records the certification flag at every step cannot
    determine the μ-ledger balance — two certified computations may carry
    different μ-values depending on the cost argument to CERTIFY. *)
Theorem cert_model_mu_necessity :
  ~ exists (Omega : CertAnnotatedShadow -> nat),
      forall s, Omega (P_cert s) = s.(vm_mu).
Proof.
  apply (generic_mu_necessity P_cert abs_A_cert abs_B_cert).
  - exact abs_cert_shadow_equal.
  - rewrite abs_cert_mu_A, abs_cert_mu_B. discriminate.
Qed.


(** ═══════════════════════════════════════════════════════════════════════════
    §6.  INDEPENDENCE CLASSIFICATION

    Collecting the three separation results into a single mutual-independence
    theorem.  This is the formal version of the claim:

      "vm_mu and vm_certified are each independent of (mem, regs, pc), and
       each independent of the other, relative to classical computation."

    Combined, A + B + C establish that the μ-ledger (vm_mu, vm_certified)
    is the minimal additional state needed to make certification determinate.
    ═══════════════════════════════════════════════════════════════════════════ *)

(** The four classical independence facts collected into one theorem. *)
Theorem mu_ledger_mutual_independence :

  (** I.   vm_mu ⊥ (mem, regs, pc) — from §3 *)
  (~ exists (Omega : StrictShadow -> nat),
       forall s, Omega (P_strict s) = s.(vm_mu)) /\

  (** II.  vm_certified ⊥ (mem, regs, pc) — from §3 *)
  (~ exists (Omega : StrictShadow -> bool),
       forall s, Omega (P_strict s) = s.(vm_certified)) /\

  (** III. vm_certified ⊥ (mem, regs, pc, vm_mu) — from §4 *)
  (~ exists (Omega : CostShadow -> bool),
       forall s, Omega (P_cost s) = s.(vm_certified)) /\

  (** IV.  vm_mu ⊥ (mem, regs, pc, vm_certified) — from §5 *)
  (~ exists (Omega : CertAnnotatedShadow -> nat),
       forall s, Omega (P_cert s) = s.(vm_mu)).

Proof.
  exact (conj turing_ram_mu_necessity
        (conj turing_ram_cert_necessity
        (conj cost_model_cert_necessity
              cert_model_mu_necessity))).
Qed.


(** ═══════════════════════════════════════════════════════════════════════════
    §7.  NAMED MACHINE INSTANCES

    Formal aliases connecting the above results to standard names in the
    theory of computation.  Each alias is definitionally equal to the
    projection it represents.
    ═══════════════════════════════════════════════════════════════════════════ *)

(** A Turing machine configuration (tape contents, head position, control state)
    is classically isomorphic to (vm_mem, vm_regs, vm_pc) in the Thiele VM.
    The T_Write/T_Move/T_Branch/T_Halt fragment of the ISA simulates standard
    tape operations via load/store/jnez/halt (see TuringClassicalEmbedding.v).
    Therefore, Theorem turing_ram_mu_necessity and turing_ram_cert_necessity
    hold for the standard Turing machine model. *)
Definition P_turing_machine : VMState -> StrictShadow := P_strict.

Theorem turing_machine_mu_necessity :
  ~ exists (Omega : StrictShadow -> nat),
      forall s, Omega (P_turing_machine s) = s.(vm_mu).
Proof. exact turing_ram_mu_necessity. Qed.

Theorem turing_machine_cert_necessity :
  ~ exists (Omega : StrictShadow -> bool),
      forall s, Omega (P_turing_machine s) = s.(vm_certified).
Proof. exact turing_ram_cert_necessity. Qed.

(** A RAM machine with explicit cost counters models P_cost.
    Even knowing the exact runtime cost at every step, a RAM machine
    cannot determine vm_certified. *)
Definition P_cost_ram : VMState -> CostShadow := P_cost.

Theorem cost_ram_cert_necessity :
  ~ exists (Omega : CostShadow -> bool),
      forall s, Omega (P_cost_ram s) = s.(vm_certified).
Proof. exact cost_model_cert_necessity. Qed.

(** An effect-tracking system that observes the vm_certified flag models P_cert.
    Even knowing whether certification occurred, an effect system cannot
    determine the μ-ledger balance. *)
Definition P_effect_system : VMState -> CertAnnotatedShadow := P_cert.

Theorem effect_system_mu_necessity :
  ~ exists (Omega : CertAnnotatedShadow -> nat),
      forall s, Omega (P_effect_system s) = s.(vm_mu).
Proof. exact cert_model_mu_necessity. Qed.


(** ═══════════════════════════════════════════════════════════════════════════
    §8.  MINIMALITY OF THE μ-LEDGER EXTENSION

    The three separations in §3–§5 show that individual projections fail to
    determine one or both of (vm_mu, vm_certified).  This section makes the
    minimality claim precise and machine-checkable:

    DEFINITIONS:
      mu_complete P    — P carries enough information to recover vm_mu
      cert_complete P  — P carries enough information to recover vm_certified
      proj_forgets_mu  — P is invariant under changes to vm_mu
      proj_forgets_cert — P is invariant under changes to vm_certified

    GENERAL THEOREMS:
      forgets_mu_not_mu_complete:   any P that forgets vm_mu is not mu-complete
      forgets_cert_not_cert_complete: any P that forgets vm_certified is not cert-complete

    CLASSIFICATION OF NAMED PROJECTIONS:
      P_strict: forgets both mu and cert → neither complete
      P_cost:   forgets cert, retains mu → cert-incomplete, mu-complete
      P_cert:   forgets mu, retains cert → mu-incomplete, cert-complete
      P_full:   retains both             → both complete

    MINIMALITY COROLLARY:
      P_full is the minimal projection (in the named lattice) that is both
      mu-complete and cert-complete.  Any projection that drops either field
      loses the corresponding completeness.  Therefore the μ-ledger
      (vm_mu, vm_certified) is the exact independent extension required.
    ═══════════════════════════════════════════════════════════════════════════ *)

(** Completeness predicates. *)
Definition mu_complete {C : Type} (P : VMState -> C) : Prop :=
  exists (Omega : C -> nat), forall s, Omega (P s) = s.(vm_mu).

Definition cert_complete {C : Type} (P : VMState -> C) : Prop :=
  exists (Omega : C -> bool), forall s, Omega (P s) = s.(vm_certified).

(** set_mu and set_cert: single-field state updates for the general arguments. *)
Definition set_mu (s : VMState) (new_mu : nat) : VMState := {|
  vm_graph     := s.(vm_graph);
  vm_csrs      := s.(vm_csrs);
  vm_regs      := s.(vm_regs);
  vm_mem       := s.(vm_mem);
  vm_pc        := s.(vm_pc);
  vm_mu        := new_mu;
  vm_mu_tensor := s.(vm_mu_tensor);
  vm_err       := s.(vm_err);
  vm_logic_acc := s.(vm_logic_acc);
  vm_mstatus   := s.(vm_mstatus);
  vm_witness   := s.(vm_witness);
  vm_certified := s.(vm_certified)
|}.

Definition set_cert (s : VMState) (new_cert : bool) : VMState := {|
  vm_graph     := s.(vm_graph);
  vm_csrs      := s.(vm_csrs);
  vm_regs      := s.(vm_regs);
  vm_mem       := s.(vm_mem);
  vm_pc        := s.(vm_pc);
  vm_mu        := s.(vm_mu);
  vm_mu_tensor := s.(vm_mu_tensor);
  vm_err       := s.(vm_err);
  vm_logic_acc := s.(vm_logic_acc);
  vm_mstatus   := s.(vm_mstatus);
  vm_witness   := s.(vm_witness);
  vm_certified := new_cert
|}.

(** Forgetting predicates: P is invariant under single-field mutations. *)
Definition proj_forgets_mu {C : Type} (P : VMState -> C) : Prop :=
  forall (s : VMState) (m : nat), P (set_mu s m) = P s.

Definition proj_forgets_cert {C : Type} (P : VMState -> C) : Prop :=
  forall (s : VMState) (b : bool), P (set_cert s b) = P s.

(** ── General impossibility theorems ─────────────────────────────────────── *)

(** Any projection that forgets vm_mu cannot be mu-complete.
    Proof: if P (set_mu s 1) = P s and P (set_mu s 2) = P s for any s,
    then P conflates two states with vm_mu = 1 and vm_mu = 2.
    Apply generic_mu_necessity for the contradiction. *)
Theorem forgets_mu_not_mu_complete :
  forall {C : Type} (P : VMState -> C),
    proj_forgets_mu P -> ~ mu_complete P.
Proof.
  intros C P Hforg.
  apply (generic_mu_necessity P (set_mu abs_zero 1) (set_mu abs_zero 2)).
  - rewrite (Hforg abs_zero 1), (Hforg abs_zero 2). reflexivity.
  - unfold set_mu, abs_zero. simpl. discriminate.
Qed.

(** Any projection that forgets vm_certified cannot be cert-complete. *)
Theorem forgets_cert_not_cert_complete :
  forall {C : Type} (P : VMState -> C),
    proj_forgets_cert P -> ~ cert_complete P.
Proof.
  intros C P Hforg.
  apply (generic_cert_necessity P (set_cert abs_zero true) (set_cert abs_zero false)).
  - rewrite (Hforg abs_zero true), (Hforg abs_zero false). reflexivity.
  - unfold set_cert, abs_zero. simpl. discriminate.
Qed.

(** Previously: four named [proj_forgets_*] witnesses [P_strict_forgets_mu],
    [P_strict_forgets_cert], [P_cost_forgets_cert], [P_cert_forgets_mu]
    sat here.  Each was a one-line reduction of the corresponding projection
    against [set_mu] / [set_cert], and each was used exactly once — in the
    matching bullet of [mu_ledger_minimality] below.  The four field-erasure
    facts are now supplied inline at those bullets. *)

(** ── P_full: the minimal complete extension ─────────────────────────────── *)

Record FullMuLedgerShadow := mk_full_mu_ledger {
  fml_mem       : list nat;
  fml_regs      : list nat;
  fml_pc        : nat;
  fml_mu        : nat;
  fml_certified : bool
}.

Definition P_full (s : VMState) : FullMuLedgerShadow := {|
  fml_mem       := s.(vm_mem);
  fml_regs      := s.(vm_regs);
  fml_pc        := s.(vm_pc);
  fml_mu        := s.(vm_mu);
  fml_certified := s.(vm_certified)
|}.

Lemma P_full_mu_complete : mu_complete P_full.
Proof.
  exists fml_mu. intro s. unfold P_full. simpl. reflexivity.
Qed.

Lemma P_full_cert_complete : cert_complete P_full.
Proof.
  exists fml_certified. intro s. unfold P_full. simpl. reflexivity.
Qed.

(** ── Named projection completeness classification ───────────────────────── *)

Lemma P_cost_mu_complete : mu_complete P_cost.
Proof. exists cs_mu. intro s. unfold P_cost. simpl. reflexivity. Qed.

Lemma P_cert_cert_complete : cert_complete P_cert.
Proof. exists cas_certified. intro s. unfold P_cert. simpl. reflexivity. Qed.

(** ── Classification table (all four named projections) ─────────────────── *)

Theorem mu_ledger_minimality :
  (** P_full achieves both completions *)
  mu_complete P_full /\ cert_complete P_full /\
  (** P_strict forgets both: neither complete *)
  ~ mu_complete P_strict /\ ~ cert_complete P_strict /\
  (** P_cost retains mu, forgets cert: mu-complete, cert-incomplete *)
  mu_complete P_cost /\ ~ cert_complete P_cost /\
  (** P_cert forgets mu, retains cert: cert-complete, mu-incomplete *)
  cert_complete P_cert /\ ~ mu_complete P_cert.
Proof.
  refine (conj P_full_mu_complete
         (conj P_full_cert_complete
         (conj _ (conj _ (conj P_cost_mu_complete
                         (conj _ (conj P_cert_cert_complete _))))))).
  - apply (forgets_mu_not_mu_complete P_strict).
    intros s m. unfold P_strict, set_mu. simpl. reflexivity.
  - apply (forgets_cert_not_cert_complete P_strict).
    intros s b. unfold P_strict, set_cert. simpl. reflexivity.
  - apply (forgets_cert_not_cert_complete P_cost).
    intros s b. unfold P_cost, set_cert. simpl. reflexivity.
  - apply (forgets_mu_not_mu_complete P_cert).
    intros s m. unfold P_cert, set_mu. simpl. reflexivity.
Qed.

(** THE MINIMALITY COROLLARY.

    P_full is the minimal classical extension that is both mu-complete and
    cert-complete.  Dropping either field loses the corresponding completeness
    for ANY projection, not just the named ones.

    Formally: the μ-ledger (vm_mu, vm_certified) is necessary and sufficient
    as the independent extension of (mem, regs, pc) that makes certification
    semantics determinate. *)
Corollary P_full_is_minimal_complete_extension :
  (** P_full achieves both completions *)
  mu_complete P_full /\ cert_complete P_full /\
  (** Dropping vm_mu from any projection destroys mu-completeness *)
  (forall {C : Type} (P : VMState -> C),
     proj_forgets_mu P -> ~ mu_complete P) /\
  (** Dropping vm_certified from any projection destroys cert-completeness *)
  (forall {C : Type} (P : VMState -> C),
     proj_forgets_cert P -> ~ cert_complete P).
Proof.
  exact (conj P_full_mu_complete
        (conj P_full_cert_complete
        (conj (@forgets_mu_not_mu_complete)
              (@forgets_cert_not_cert_complete)))).
Qed.


(** ═══════════════════════════════════════════════════════════════════════════
    §9.  GRAPH INDEPENDENCE

    The categorical layer (vm_graph) is independent from P_full.  Even knowing
    (mem, regs, pc, mu, certified) — the complete μ-ledger shadow — no
    classical observer can recover vm_graph.

    PROOF: categorical_separation (PartitionSeparation.v §10) gives two VMStates
    s1 and s2 that are computationally_equivalent (same mem, regs, mu, pc,
    err, certified) but categorically_distinct (different pg_morphisms).
    Since P_full ignores vm_graph, P_full s1 = P_full s2.  But vm_graph s1 ≠
    vm_graph s2 (their pg_morphisms differ, so the records differ).  Any
    oracle Ω : FullMuLedgerShadow → PartitionGraph must return the same value
    on equal inputs — contradiction.

    CONSEQUENCE (completing the independence classification):
      vm_graph ⊥ (mem, regs, pc, vm_mu, vm_certified)   [from §9]

    Together with §3–§5, the three independent non-classical components are:
      1. vm_mu        — μ-ledger balance
      2. vm_certified — certification flag
      3. vm_graph     — categorical (partition/morphism) structure

    Each is provably not recoverable from any combination of the others
    together with the strict classical shadow (mem, regs, pc).
    ═══════════════════════════════════════════════════════════════════════════ *)

(** No function of P_full can recover vm_graph.
    Uses categorical_separation to supply the separation witnesses. *)
Theorem graph_not_recoverable_from_P_full :
  ~ exists (Omega : FullMuLedgerShadow -> PartitionGraph),
      forall s, Omega (P_full s) = s.(vm_graph).
Proof.
  intros [Omega HOmega].
  destruct PartitionSeparation.categorical_separation as [s1 [s2 [Hequiv Hdist]]].
  assert (Heq_full : P_full s1 = P_full s2).
  { unfold P_full.
    unfold PartitionSeparation.computationally_equivalent in Hequiv.
    destruct Hequiv as [Hreg [Hmem [Hmu [Hpc [_ Hcert]]]]].
    congruence. }
  assert (HA : Omega (P_full s1) = s1.(vm_graph)) by apply HOmega.
  assert (HB : Omega (P_full s2) = s2.(vm_graph)) by apply HOmega.
  rewrite Heq_full in HA.
  rewrite HA in HB.
  (* HB : s1.(vm_graph) = s2.(vm_graph); Hdist says pg_morphisms differ *)
  apply Hdist.
  rewrite HB.
  reflexivity.
Qed.

(** Constructive form: for any claimed graph oracle, explicit falsifying witnesses exist. *)
Corollary graph_oracle_fails :
  forall (Omega : FullMuLedgerShadow -> PartitionGraph),
    ~ (forall s, Omega (P_full s) = s.(vm_graph)).
Proof.
  intros Omega HOmega.
  exact (graph_not_recoverable_from_P_full (ex_intro _ Omega HOmega)).
Qed.

(** ── Complete three-component independence ──────────────────────────────── *)

(** The five independence facts collected: classical shadow, μ-ledger pair,
    and graph are all mutually independent.  This is the full classification
    of VMState information components. *)
Theorem thiele_state_three_component_independence :
  (** I.   vm_mu ⊥ (mem, regs, pc)                          — §3 *)
  (~ exists (Omega : StrictShadow -> nat),
       forall s, Omega (P_strict s) = s.(vm_mu)) /\
  (** II.  vm_certified ⊥ (mem, regs, pc)                   — §3 *)
  (~ exists (Omega : StrictShadow -> bool),
       forall s, Omega (P_strict s) = s.(vm_certified)) /\
  (** III. vm_certified ⊥ (mem, regs, pc, vm_mu)            — §4 *)
  (~ exists (Omega : CostShadow -> bool),
       forall s, Omega (P_cost s) = s.(vm_certified)) /\
  (** IV.  vm_mu ⊥ (mem, regs, pc, vm_certified)            — §5 *)
  (~ exists (Omega : CertAnnotatedShadow -> nat),
       forall s, Omega (P_cert s) = s.(vm_mu)) /\
  (** V.   vm_graph ⊥ (mem, regs, pc, vm_mu, vm_certified)  — §9 *)
  (~ exists (Omega : FullMuLedgerShadow -> PartitionGraph),
       forall s, Omega (P_full s) = s.(vm_graph)).
Proof.
  exact (conj turing_ram_mu_necessity
        (conj turing_ram_cert_necessity
        (conj cost_model_cert_necessity
        (conj cert_model_mu_necessity
              graph_not_recoverable_from_P_full)))).
Qed.
