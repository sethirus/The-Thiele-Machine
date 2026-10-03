From Coq Require Import List Bool Arith.PeanoNat Lia.
From Coq Require Import Strings.String Strings.Ascii.
From Coq Require Import BinInt.   (* Z type and arithmetic *)
Import ListNotations.

From Kernel Require Import CertCheck VMState.

(* Force nat default scope locally: BinInt opens Z_scope which would reinterpret
   literals like [8] in [ascii_payload_bits_length] as Z. Marked [Local] so the
   scope choice does NOT propagate to importers; downstream files (like
   LassertTsirelsonCrossLink.v) keep their own scope discipline. *)
Local Open Scope nat_scope.

(** VMStep: how the machine runs.

    This file defines the 51-opcode instruction type and the [vm_step] relation for state transitions.
    Each instruction has an explicit μ-cost, and failure paths latch the error flag instead of leaving a state undefined.
    The checked transition properties are determinism, nondecreasing μ, and the locality claims used by the observation proofs.
    Their proof names are [SimulationProof.vm_step_deterministic], [MuLedgerConservation.vm_mu_monotonic_single_step], and [KernelPhysics.observational_no_signaling].
    [LASSERT] checks a SAT certificate together with a falsifying assignment; the [kind=false] UNSAT path is not implemented and fails.
    The comments below describe the executable contract; the theorems and tests are the evidence for it. *)

Module VMStep.

Definition check_lrat : string -> string -> bool := CertCheck.check_lrat.
Definition check_model : string -> string -> bool := CertCheck.check_model.

(** Payload bits.

    Coq strings are lists of 8-bit [ascii] values.  Cost accounting does
    not charge "string length" or "character length"; it exposes the actual
    Boolean bits carried by each payload byte and count those bits directly. *)
Definition ascii_payload_bits (a : ascii) : list bool :=
  match a with
  | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
      [b0; b1; b2; b3; b4; b5; b6; b7]
  end.

Fixpoint payload_bits (s : string) : list bool :=
  match s with
  | EmptyString => []
  | String a rest => ascii_payload_bits a ++ payload_bits rest
  end.

Definition payload_bit_length (s : string) : nat :=
  List.length (payload_bits s).

Lemma ascii_payload_bits_length :
  forall a, List.length (ascii_payload_bits a) = 8.
Proof.
  intro a. destruct a as [b0 b1 b2 b3 b4 b5 b6 b7]. reflexivity.
Qed.

Lemma payload_bit_length_ascii :
  forall s, payload_bit_length s = 8 * String.length s.
Proof.
  induction s as [| a rest IH].
  - reflexivity.
  - unfold payload_bit_length in *.
    simpl.
    rewrite app_length.
    rewrite ascii_payload_bits_length.
    fold (payload_bits rest).
    rewrite IH.
    lia.
Qed.

(** vm_instruction: The 51-opcode ISA. Every instruction carries an explicit
    μ-cost (mu_delta). The step relation applies (vm_mu + instruction_cost instr),
    making μ-monotonicity structural. You can't step without paying.

    The encoded cost is part of the instruction so the kernel can apply the same schedule in the executable and hardware-facing models.

    The quick reference:

    Partition ops (modify graph):
    - PNEW: Claim a range of data memory as a fresh module at pg_next_id.
      Traps if the range overlaps another module's range, runs past data
      memory, or the 64 module numbers are used up.
    - PSPLIT: Split a module's range at its middle (the left part gets size/2
      addresses). Traps if fewer than two module numbers are left.
    - PMERGE: Join two modules whose ranges touch. Traps otherwise, and when
      the module numbers are used up.
    - PDISCOVER: Carry evidence payload; the transition is a pure advance.

    Logical ops:
    - LASSERT: Check a formula with a SAT certificate and a falsifying witness.
      Cost: flen * 8 + S mu_delta. Success requires both a model and a
      countermodel, so a tautology fails the check. A successful step advances
      the pc and changes no certification field; a failed step traps.
      The UNSAT path always fails.
    - LJOIN: Reserve certificate join cost. The transition is a pure advance.
    - REVEAL: Reveal bits, record to μ-tensor. Cost: bits + S mu_delta.
    - EMIT: Emit payload bits outside the Coq state. Cost:
      payload_bit_length payload + S mu_delta.

    Register/memory ops:
    - XFER: dst = src (register copy).
    - LOAD_IMM: dst = imm (immediate load).
    - LOAD: dst = mem[regs[rs_addr]] (register-indirect).
    - STORE: mem[regs[rs_addr]] = src.
    - ADD/SUB: 64-bit modular arithmetic.
    - JUMP/JNEZ/CALL/RET: control flow. r15 = SP; CALL stores the return
      address at mem[SP] and increments SP, RET decrements SP and loads the pc.

    GF(2) ops (XOR_ADD and XOR_SWAP are reversible; XOR_LOAD and XOR_RANK overwrite dst):
    - XOR_LOAD: load from absolute addr (despite name, no XOR involved).
    - XOR_ADD: dst ^= src.
    - XOR_SWAP: swap two registers.
    - XOR_RANK: popcount (Hamming weight).

    Special:
    - MDLACC: Charges μ for module-structure access.
    - CHSH_TRIAL: Record CHSH trial if all bits ∈ {0,1}. Error otherwise.
    - HALT: Stop execution.
    - CHECKPOINT: Record label.
    - READ_PORT/WRITE_PORT: External I/O. READ_PORT costs ≥ 1 by runtime policy.
    - HEAP_LOAD/HEAP_STORE: Heap-relative memory (base + addr).
    - CERTIFY: Set vm_certified = true. Cost: S mu_delta.
    - AND/OR/SHL/SHR/MUL/LUI: Extended 64-bit ALU.
    - TENSOR_SET/GET: Per-module 4×4 metric tensor.
    - MORPH/COMPOSE/MORPH_ID/MORPH_DELETE/MORPH_ASSERT/MORPH_TENSOR/MORPH_GET:
      Categorical morphism operations. MORPH_ASSERT is a cert-setter.

    Cert-setters (cost ≥ 1 enforced by S): REVEAL, EMIT, LJOIN, LASSERT,
    READ_PORT, CERTIFY, MORPH_ASSERT and the five CHSH_LASSERT forms, twelve in
    all (see [is_cert_setterb]).

    The natural-number cost schedule makes the ledger nondecreasing; the conservation theorem checks that transition property. *)
Inductive vm_instruction :=
| instr_pnew (region : list nat) (mu_delta : nat)
| instr_psplit (module : ModuleID) (left right : list nat) (mu_delta : nat)
| instr_pmerge (m1 m2 : ModuleID) (mu_delta : nat)
| instr_lassert (formula_addr_reg cert_addr_reg : nat)
    (cert_kind : bool) (formula_len : nat) (mu_delta : nat)
| instr_ljoin (cert1_addr_reg cert2_addr_reg : nat) (mu_delta : nat)
| instr_mdlacc (module : ModuleID) (mu_delta : nat)
| instr_pdiscover (module : ModuleID) (evidence : list VMAxiom) (mu_delta : nat)
| instr_xfer (dst src : nat) (mu_delta : nat)
| instr_load_imm (dst : nat) (imm : nat) (mu_delta : nat)
| instr_load (dst : nat) (rs_addr : nat) (mu_delta : nat)
| instr_store (rs_addr : nat) (src : nat) (mu_delta : nat)
| instr_add (dst : nat) (rs1 : nat) (rs2 : nat) (mu_delta : nat)
| instr_sub (dst : nat) (rs1 : nat) (rs2 : nat) (mu_delta : nat)
| instr_jump (target : nat) (mu_delta : nat)
| instr_jnez (rs : nat) (target : nat) (mu_delta : nat)
| instr_call (target : nat) (mu_delta : nat)
| instr_ret (mu_delta : nat)
| instr_chsh_trial (x y a b : nat) (mu_delta : nat)
| instr_xor_load (dst addr : nat) (mu_delta : nat)
| instr_xor_add (dst src : nat) (mu_delta : nat)
| instr_xor_swap (a b : nat) (mu_delta : nat)
| instr_xor_rank (dst src : nat) (mu_delta : nat)
| instr_emit (module : ModuleID) (payload : string) (mu_delta : nat)
| instr_reveal (module : ModuleID) (bits : nat) (cert : string) (mu_delta : nat)
| instr_halt (mu_delta : nat)
| instr_checkpoint (label : string) (mu_delta : nat)
| instr_read_port (dst : nat) (channel_idx : nat) (value : nat) (bits : nat) (mu_delta : nat)
| instr_write_port (channel_idx : nat) (src : nat) (mu_delta : nat)
| instr_heap_load (dst : nat) (rs_addr : nat) (mu_delta : nat)
| instr_heap_store (rs_addr : nat) (src : nat) (mu_delta : nat)
| instr_certify (mu_delta : nat)
| instr_and (dst : nat) (rs1 : nat) (rs2 : nat) (mu_delta : nat)
| instr_or  (dst : nat) (rs1 : nat) (rs2 : nat) (mu_delta : nat)
| instr_shl (dst : nat) (rs1 : nat) (rs2 : nat) (mu_delta : nat)
| instr_shr (dst : nat) (rs1 : nat) (rs2 : nat) (mu_delta : nat)
| instr_mul (dst : nat) (rs1 : nat) (rs2 : nat) (mu_delta : nat)
| instr_lui (dst : nat) (imm : nat) (mu_delta : nat)
| instr_tensor_set (module : ModuleID) (i j value : nat) (mu_delta : nat)
| instr_tensor_get (dst : nat) (module : ModuleID) (i j : nat) (mu_delta : nat)
| instr_morph (dst : nat) (src_mod dst_mod : ModuleID) (coupling_idx : nat) (mu_delta : nat)
| instr_compose (dst : nat) (m1_id m2_id : MorphismID) (mu_delta : nat)
| instr_morph_id (dst : nat) (module : ModuleID) (mu_delta : nat)
| instr_morph_delete (morph_id : MorphismID) (mu_delta : nat)
| instr_morph_assert (morph_id : MorphismID) (property cert : string) (mu_delta : nat)
| instr_morph_tensor (dst : nat) (f_id g_id : MorphismID) (mu_delta : nat)
| instr_morph_get (dst : nat) (morph_id : MorphismID) (selector : nat) (mu_delta : nat)
(** instr_chsh_lassert: CHSH-aware certification. Reads the WitnessCounts
    buckets directly, computes the four CHSH correlators, and checks the three
    integer-arithmetic column-contractivity conditions. When all three hold
    the step advances the pc and changes no certification field. On failure
    it traps to LASSERT_TRAP_PC and latches vm_err. μ-cost is S mu_delta (≥ 1)
    regardless of success, matching the cert-setter cost discipline of CERTIFY,
    LJOIN, and MORPH_ASSERT. A run that passes this instruction without a trap
    has verified column-contractivity of the CHSH correlators; the bridge
    theorem reads that trap signature. *)
| instr_chsh_lassert (mu_delta : nat)
(** instr_chsh_lassert_1ab: Q_{1+AB}-aware certification (NPA level 1+AB).
    Like instr_chsh_lassert but additionally enforces the integer-arithmetic
    sum-of-squares condition
       E_{00}^2 + E_{01}^2 + E_{10}^2 + E_{11}^2 <= 1
    on the witness correlators. Combined check is sound for the γ = 0
    specialization of the column-contractivity-at-1+AB predicate; a
    successful step implies PSD of the 9x9 NPA Q_{1+AB} moment matrix
    at γ = 0 (bridge theorem in QuantumPartitionPSD_1AB.v).
    Cost is S mu_delta, matching the cert-setter discipline. *)
| instr_chsh_lassert_1ab (mu_delta : nat)
(** instr_chsh_lassert_1ab_g5: Q_{1+AB}-aware certification with caller-
    supplied 4-body moment γ_5. Carries a γ_5 bucket pair (same_g5, diff_g5)
    where γ_5 = (same_g5 - diff_g5) / (same_g5 + diff_g5). Runs the
    Z-arithmetic γ_5 SOS witness [q1ab_g5_full_integer_check_kernel] which
    combines the existing Q_1 column-contractive check on the four CHSH
    correlators with the γ_5 cleared polynomial inequality (see Section 12
    + 13 of QuantumPartitionPSD_1AB.v). A successful step implies PSD9 of
    the 9x9 NPA Q_{1+AB} moment matrix at (E, 0, 0, 0, 0, γ_5) for the
    γ_5 derived from the bucket pair. Cost is S mu_delta. *)
| instr_chsh_lassert_1ab_g5 (mu_delta same_g5 diff_g5 : nat)
(** instr_chsh_lassert_1ab_g345: Q_{1+AB}-aware certification with caller-
    supplied 3-body moments γ_3, γ_4 AND 4-body moment γ_5. Carries three
    γ-bucket pairs (same_g3, diff_g3), (same_g4, diff_g4), (same_g5, diff_g5)
    where γ_k = (same_g_k - diff_g_k) / (same_g_k + diff_g_k). Runs the
    Z-arithmetic 4×4 Sylvester PD witness [q1ab_g345_full_integer_check_kernel]
    which combines the Q_1 column-contractive check on the four CHSH
    correlators with the four leading principal minors of the difference
    matrix H_{γ_345} = det_M·M_M − M_N being positive (see Section 15 of
    QuantumPartitionPSD_1AB.v). A successful step implies PSD9 of the 9×9
    NPA Q_{1+AB} moment matrix at (E, 0, 0, γ_3, γ_4, γ_5) for the
    γ_3, γ_4, γ_5 derived from the bucket pairs. Cost is S mu_delta. *)
| instr_chsh_lassert_1ab_g345 (mu_delta same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 : nat)
(** instr_chsh_lassert_1ab_g12345: Q_{1+AB}-aware certification with caller-
    supplied 3-body moments γ_1, γ_2 AND γ_3, γ_4, AND 4-body moment γ_5.
    Carries five γ-bucket pairs, one each for γ_1..γ_5, encoded as
    (same_g_k, diff_g_k) with γ_k = (same_g_k − diff_g_k)/(same_g_k + diff_g_k).
    Runs the Z-arithmetic 6×6 → 5×5 → 4×4 Schur cascade PD witness
    [q1ab_g12345_full_integer_check_kernel] which combines the Q_1
    column-contractive check on the four CHSH correlators with the six
    Schur-cascade PD checks (H11, S6_22, sym4_d1..sym4_d4 of the cleared
    S5 entries; see Section 16 of QuantumPartitionPSD_1AB.v). A successful
    step implies PSD9 of the full 9×9 NPA Q_{1+AB} moment matrix at
    (E, γ_1, γ_2, γ_3, γ_4, γ_5) for the rationals derived from the
    bucket pairs: substrate-level Q_{1+AB} closure across all five γ
    parameters simultaneously. Cost is S mu_delta. *)
| instr_chsh_lassert_1ab_g12345 (mu_delta same_g1 diff_g1 same_g2 diff_g2 same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 : nat).


(** [instruction_cost] is the complete scheduled cost function. The assertion
    and receipt-bearing instructions add their payload size to the successor
    floor; [LJOIN], [CERTIFY], [MORPH_ASSERT] and the five CHSH_LASSERT forms
    have the positive successor floor without a payload term; all remaining
    constructors use their encoded
    [mu_delta]. This definition is the schedule consumed by the ledger lemmas. *)
Definition instruction_cost (instr : vm_instruction) : nat :=
  match instr with
  | instr_pnew _ cost => cost
  | instr_psplit _ _ _ cost => cost
  | instr_pmerge _ _ cost => cost
  | instr_lassert _ _ _ flen cost => flen * 8 + S cost
  | instr_ljoin _ _ cost => S cost
  | instr_mdlacc _ cost => cost
  | instr_pdiscover _ _ cost => cost
  | instr_xfer _ _ cost => cost
  | instr_load_imm _ _ cost => cost
  | instr_load _ _ cost => cost
  | instr_store _ _ cost => cost
  | instr_add _ _ _ cost => cost
  | instr_sub _ _ _ cost => cost
  | instr_jump _ cost => cost
  | instr_jnez _ _ cost => cost
  | instr_call _ cost => cost
  | instr_ret cost => cost
  | instr_chsh_trial _ _ _ _ cost => cost
  | instr_xor_load _ _ cost => cost
  | instr_xor_add _ _ cost => cost
  | instr_xor_swap _ _ cost => cost
  | instr_xor_rank _ _ cost => cost
  | instr_emit _ payload cost => payload_bit_length payload + S cost
  | instr_reveal _ bits _ cost => bits + S cost
  | instr_halt cost => cost
  | instr_checkpoint _ cost => cost
  | instr_read_port _ _ _ bits cost => bits + S cost
  | instr_write_port _ _ cost => cost
  | instr_heap_load _ _ cost => cost
  | instr_heap_store _ _ cost => cost
  | instr_certify cost => S cost
  | instr_and _ _ _ cost => cost
  | instr_or _ _ _ cost => cost
  | instr_shl _ _ _ cost => cost
  | instr_shr _ _ _ cost => cost
  | instr_mul _ _ _ cost => cost
  | instr_lui _ _ cost => cost
  | instr_tensor_set _ _ _ _ cost => cost
  | instr_tensor_get _ _ _ _ cost => cost
  | instr_morph _ _ _ _ cost => cost
  | instr_compose _ _ _ cost => cost
  | instr_morph_id _ _ cost => cost
  | instr_morph_delete _ cost => cost
  | instr_morph_assert _ _ _ cost => S cost  (* cert-setter *)
  | instr_morph_tensor _ _ _ cost => cost
  | instr_morph_get _ _ _ cost => cost
  | instr_chsh_lassert cost => S cost  (* cert-setter: column-contractive check *)
  | instr_chsh_lassert_1ab cost => S cost  (* cert-setter: Q_{1+AB} column-contractive check *)
  | instr_chsh_lassert_1ab_g5 cost _ _ => S cost  (* cert-setter: Q_{1+AB} γ_5-aware check *)
  | instr_chsh_lassert_1ab_g345 cost _ _ _ _ _ _ => S cost  (* cert-setter: Q_{1+AB} γ_{3,4,5}-aware 4×4 Sylvester check *)
  | instr_chsh_lassert_1ab_g12345 cost _ _ _ _ _ _ _ _ _ _ => S cost  (* cert-setter: full Q_{1+AB} γ_{1..5}-aware 6×6 Schur cascade *)
  end.

(** is_cert_setterb: Positive-cost policy predicate.

    This is NOT the literal "sets csr_cert_addr" predicate. In the hardware-aligned
    step semantics below, EMIT/LJOIN/LASSERT/REVEAL mostly advance state and charge
    μ; MORPH_ASSERT writes csr_cert_addr, and CERTIFY sets vm_certified.

    What this predicate says is narrower and more mechanical: instructions in the
    certification/revelation class must have instruction_cost ≥ 1. That is exactly
    what cert_setter_cost_pos proves by case analysis.

    IMPORTANT DISTINCTION from cert_addr_setterb (in AbstractNoFI.v):
    READ_PORT and CERTIFY are included here because the runtime policy makes them
    positive-cost actions. cert_addr_setterb is the abstract cert_addr channel.
    Different question, different predicate. *)
Definition is_cert_setterb (instr : vm_instruction) : bool :=
  match instr with
  | instr_reveal _ _ _ _ => true
  | instr_emit _ _ _ => true
  | instr_ljoin _ _ _ => true
  | instr_lassert _ _ _ _ _ => true
  | instr_read_port _ _ _ _ _ => true
  | instr_certify _ => true
  | instr_morph_assert _ _ _ _ => true
  | instr_chsh_lassert _ => true
  | instr_chsh_lassert_1ab _ => true
  | instr_chsh_lassert_1ab_g5 _ _ _ => true
  | instr_chsh_lassert_1ab_g345 _ _ _ _ _ _ _ => true
  | instr_chsh_lassert_1ab_g12345 _ _ _ _ _ _ _ _ _ _ _ => true
  | _ => false
  end.

(** nofi_step_cost_okb: Check that a single instruction satisfies the NoFI
    cost policy. If it's a cert-setter, its cost must be ≥ 1. For non-cert-setters,
    this is always true (no restriction). Used as a runtime gate. *)
Definition nofi_step_cost_okb (instr : vm_instruction) : bool :=
  match is_cert_setterb instr with
  | true => Nat.leb 1 (instruction_cost instr)
  | false => true
  end.

(** nofi_trace_cost_okb: Check that every instruction in a trace satisfies
    the NoFI cost policy. True iff forall i in trace, nofi_step_cost_okb i. *)
Definition nofi_trace_cost_okb (trace : list vm_instruction) : bool :=
  forallb nofi_step_cost_okb trace.

(** cert_setter_cost_pos: cert-setters always cost ≥ 1.
    This is a structural fact of the ISA, not a policy that is checked.
    EMIT, REVEAL, LASSERT, LJOIN, READ_PORT, CERTIFY, MORPH_ASSERT and the five
    CHSH_LASSERT forms, twelve in all, include the S cost floor in
    instruction_cost. Some also add payload bits. No matter what mu_delta the
    programmer encodes, the cost is at least 1, so no zero-cost cert-setter
    can be written. *)
Lemma cert_setter_cost_pos :
  forall instr,
    is_cert_setterb instr = true ->
    instruction_cost instr >= 1.
Proof.
  intros instr H.
  destruct instr; simpl in H; try discriminate; simpl; lia.
Qed.

(** declared_mu_delta: the mu_delta operand the instruction carries, the
    cost the program declares. [instruction_cost] adds the successor floor
    and any payload term to it for the twelve [is_cert_setterb] instructions
    and uses it unchanged for every other instruction. *)
Definition declared_mu_delta (instr : vm_instruction) : nat :=
  match instr with
  | instr_pnew _ cost => cost
  | instr_psplit _ _ _ cost => cost
  | instr_pmerge _ _ cost => cost
  | instr_lassert _ _ _ _ cost => cost
  | instr_ljoin _ _ cost => cost
  | instr_mdlacc _ cost => cost
  | instr_pdiscover _ _ cost => cost
  | instr_xfer _ _ cost => cost
  | instr_load_imm _ _ cost => cost
  | instr_load _ _ cost => cost
  | instr_store _ _ cost => cost
  | instr_add _ _ _ cost => cost
  | instr_sub _ _ _ cost => cost
  | instr_jump _ cost => cost
  | instr_jnez _ _ cost => cost
  | instr_call _ cost => cost
  | instr_ret cost => cost
  | instr_chsh_trial _ _ _ _ cost => cost
  | instr_xor_load _ _ cost => cost
  | instr_xor_add _ _ cost => cost
  | instr_xor_swap _ _ cost => cost
  | instr_xor_rank _ _ cost => cost
  | instr_emit _ _ cost => cost
  | instr_reveal _ _ _ cost => cost
  | instr_halt cost => cost
  | instr_checkpoint _ cost => cost
  | instr_read_port _ _ _ _ cost => cost
  | instr_write_port _ _ cost => cost
  | instr_heap_load _ _ cost => cost
  | instr_heap_store _ _ cost => cost
  | instr_certify cost => cost
  | instr_and _ _ _ cost => cost
  | instr_or _ _ _ cost => cost
  | instr_shl _ _ _ cost => cost
  | instr_shr _ _ _ cost => cost
  | instr_mul _ _ _ cost => cost
  | instr_lui _ _ cost => cost
  | instr_tensor_set _ _ _ _ cost => cost
  | instr_tensor_get _ _ _ _ cost => cost
  | instr_morph _ _ _ _ cost => cost
  | instr_compose _ _ _ cost => cost
  | instr_morph_id _ _ cost => cost
  | instr_morph_delete _ cost => cost
  | instr_morph_assert _ _ _ cost => cost
  | instr_morph_tensor _ _ _ cost => cost
  | instr_morph_get _ _ _ cost => cost
  | instr_chsh_lassert cost => cost
  | instr_chsh_lassert_1ab cost => cost
  | instr_chsh_lassert_1ab_g5 cost _ _ => cost
  | instr_chsh_lassert_1ab_g345 cost _ _ _ _ _ _ => cost
  | instr_chsh_lassert_1ab_g12345 cost _ _ _ _ _ _ _ _ _ _ => cost
  end.

(** Outside the cert-setter class the scheduled cost is the declared cost. *)
Lemma non_cert_setter_cost_is_declared :
  forall instr,
    is_cert_setterb instr = false ->
    instruction_cost instr = declared_mu_delta instr.
Proof.
  intros instr H.
  destruct instr; simpl in H; try discriminate; reflexivity.
Qed.

(** Inside the class the scheduled cost is at least one more than the
    declared cost: the successor floor, plus any payload bits. *)
Lemma cert_setter_cost_above_declared :
  forall instr,
    is_cert_setterb instr = true ->
    instruction_cost instr >= S (declared_mu_delta instr).
Proof.
  intros instr H.
  destruct instr; simpl in H; try discriminate; simpl; lia.
Qed.

(** [nofi_step_always_ok] proves that the boolean cost-policy check accepts every instruction under this ISA's own cost function. *)
Lemma nofi_step_always_ok : forall instr, nofi_step_cost_okb instr = true.
Proof.
  intros instr.
  unfold nofi_step_cost_okb.
  destruct (is_cert_setterb instr) eqn:Hcert.
  - apply Nat.leb_le. apply cert_setter_cost_pos. exact Hcert.
  - reflexivity.
Qed.

(** [nofi_trace_always_ok] lifts the per-instruction policy result to a list of instructions. *)
Lemma nofi_trace_always_ok : forall trace, nofi_trace_cost_okb trace = true.
Proof.
  intros trace.
  unfold nofi_trace_cost_okb.
  apply forallb_forall.
  intros instr _.
  apply nofi_step_always_ok.
Qed.

(** is_bit: True iff n is 0 or 1. CHSH requires all inputs and outputs
    to be binary. Anything else is a protocol violation and latches an error. *)
Definition is_bit (n : nat) : bool :=
  orb (Nat.eqb n 0) (Nat.eqb n 1).

(** chsh_bits_ok: All four CHSH trial values (settings x,y and outcomes a,b)
    must be single bits. If this check fails, step_chsh_trial_badbits fires
    and the error flag latches. No partial CHSH results: all bits or nothing. *)
Definition chsh_bits_ok (x y a b : nat) : bool :=
  andb (andb (is_bit x) (is_bit y)) (andb (is_bit a) (is_bit b)).

(** [apply_cost] adds the instruction's declared cost to the current ledger. Since both values are natural numbers, the update is nondecreasing. *)
Definition apply_cost (s : VMState) (instr : vm_instruction) : nat :=
  s.(vm_mu) + instruction_cost instr.

(** latch_err: Error flag is sticky. Once true, it stays true.
    orb flag s.(vm_err) means: if the flag was already set OR this step sets it,
    result is true. Errors can never clear. This mirrors hardware error latches. *)
Definition latch_err (s : VMState) (flag : bool) : bool :=
  orb flag s.(vm_err).

(** vm_mu_tensor_add_at: Increment the flat entry at index k of the
    vm_mu_tensor by delta.  Used by REVEAL to charge to a specific
    spacetime metric component. *)
Definition vm_mu_tensor_add_at (s : VMState) (k delta : nat) : list nat :=
  let old := nth k s.(vm_mu_tensor) 0 in
  list_update_at s.(vm_mu_tensor) k (old + delta).

(** tensor_indices_ok: hardware/extracted tensor ops accept only 4x4 indices.
    Invalid indices latch the error flag instead of mutating graph/registers. *)
Definition tensor_indices_ok (i j : nat) : bool :=
  Nat.ltb i 4 && Nat.ltb j 4.

(** morphism_selector_value: MORPH_GET selector decoding.
    0=source, 1=target, 2=number of coupling pairs, 3=is_identity. *)
Definition morphism_selector_value (ms : MorphismState) (selector : nat) : nat :=
  match selector with
  | 0 => ms.(morph_source)
  | 1 => ms.(morph_target)
  | 2 => List.length ms.(morph_coupling).(coupling_pairs)
  | 3 => if ms.(morph_is_identity) then 1 else 0
  | _ => 0
  end.

(** record_trial: Increment the appropriate WitnessCounts bucket
    based on settings (x, y) and whether outputs (a, b) match.
    Called by CHSH_TRIAL on valid bits. *)
Definition record_trial (wc : WitnessCounts) (x y a b : nat) : WitnessCounts :=
  let same := Nat.eqb a b in
  match x, y with
  | 0, 0 => if same then {| wc_same_00 := S wc.(wc_same_00); wc_diff_00 := wc.(wc_diff_00);
                             wc_same_01 := wc.(wc_same_01); wc_diff_01 := wc.(wc_diff_01);
                             wc_same_10 := wc.(wc_same_10); wc_diff_10 := wc.(wc_diff_10);
                             wc_same_11 := wc.(wc_same_11); wc_diff_11 := wc.(wc_diff_11) |}
             else       {| wc_same_00 := wc.(wc_same_00); wc_diff_00 := S wc.(wc_diff_00);
                             wc_same_01 := wc.(wc_same_01); wc_diff_01 := wc.(wc_diff_01);
                             wc_same_10 := wc.(wc_same_10); wc_diff_10 := wc.(wc_diff_10);
                             wc_same_11 := wc.(wc_same_11); wc_diff_11 := wc.(wc_diff_11) |}
  | 0, _ => if same then {| wc_same_00 := wc.(wc_same_00); wc_diff_00 := wc.(wc_diff_00);
                             wc_same_01 := S wc.(wc_same_01); wc_diff_01 := wc.(wc_diff_01);
                             wc_same_10 := wc.(wc_same_10); wc_diff_10 := wc.(wc_diff_10);
                             wc_same_11 := wc.(wc_same_11); wc_diff_11 := wc.(wc_diff_11) |}
             else       {| wc_same_00 := wc.(wc_same_00); wc_diff_00 := wc.(wc_diff_00);
                             wc_same_01 := wc.(wc_same_01); wc_diff_01 := S wc.(wc_diff_01);
                             wc_same_10 := wc.(wc_same_10); wc_diff_10 := wc.(wc_diff_10);
                             wc_same_11 := wc.(wc_same_11); wc_diff_11 := wc.(wc_diff_11) |}
  | _, 0 => if same then {| wc_same_00 := wc.(wc_same_00); wc_diff_00 := wc.(wc_diff_00);
                             wc_same_01 := wc.(wc_same_01); wc_diff_01 := wc.(wc_diff_01);
                             wc_same_10 := S wc.(wc_same_10); wc_diff_10 := wc.(wc_diff_10);
                             wc_same_11 := wc.(wc_same_11); wc_diff_11 := wc.(wc_diff_11) |}
             else       {| wc_same_00 := wc.(wc_same_00); wc_diff_00 := wc.(wc_diff_00);
                             wc_same_01 := wc.(wc_same_01); wc_diff_01 := wc.(wc_diff_01);
                             wc_same_10 := wc.(wc_same_10); wc_diff_10 := S wc.(wc_diff_10);
                             wc_same_11 := wc.(wc_same_11); wc_diff_11 := wc.(wc_diff_11) |}
  | _, _ => if same then {| wc_same_00 := wc.(wc_same_00); wc_diff_00 := wc.(wc_diff_00);
                             wc_same_01 := wc.(wc_same_01); wc_diff_01 := wc.(wc_diff_01);
                             wc_same_10 := wc.(wc_same_10); wc_diff_10 := wc.(wc_diff_10);
                             wc_same_11 := S wc.(wc_same_11); wc_diff_11 := wc.(wc_diff_11) |}
             else       {| wc_same_00 := wc.(wc_same_00); wc_diff_00 := wc.(wc_diff_00);
                             wc_same_01 := wc.(wc_same_01); wc_diff_01 := wc.(wc_diff_01);
                             wc_same_10 := wc.(wc_same_10); wc_diff_10 := wc.(wc_diff_10);
                             wc_same_11 := wc.(wc_same_11); wc_diff_11 := S wc.(wc_diff_11) |}
  end.

(** advance_state: Standard state builder for instructions that modify graph
    and/or CSRs but NOT registers or memory. Advances PC by 1, applies cost,
    preserves regs/mem/logic_acc/mstatus/witness/certified. Used by most
    structural instructions (PNEW, PSPLIT, PMERGE, EMIT, REVEAL, etc.). *)
Definition advance_state (s : VMState) (instr : vm_instruction)
  (graph : PartitionGraph) (csrs : CSRState) (err_flag : bool)
  : VMState :=
  {| vm_graph := graph;
     vm_csrs := csrs;
  vm_regs := s.(vm_regs);
  vm_mem := s.(vm_mem);
     vm_pc := S s.(vm_pc);
     vm_mu := apply_cost s instr;
     vm_mu_tensor := s.(vm_mu_tensor);
     vm_err := err_flag;
     vm_logic_acc := s.(vm_logic_acc);
     vm_mstatus := s.(vm_mstatus);
     vm_witness := s.(vm_witness);
     vm_certified := s.(vm_certified) |}.

(** advance_state_reveal: Like advance_state but additionally increments
    vm_mu_tensor[flat_idx] by delta, recording where in metric-space the
    revelation cost was charged.  The REVEAL instruction encodes the
    tensor direction as a flat index (= ti*4+tj, range 0..15) in its
    module field. *)
Definition advance_state_reveal (s : VMState) (instr : vm_instruction)
  (flat_idx delta : nat)
  (graph : PartitionGraph) (csrs : CSRState) (err_flag : bool)
  : VMState :=
  {| vm_graph := graph;
     vm_csrs := csrs;
     vm_regs := s.(vm_regs);
     vm_mem := s.(vm_mem);
     vm_pc := S s.(vm_pc);
     vm_mu := apply_cost s instr;
     vm_mu_tensor := vm_mu_tensor_add_at s flat_idx delta;
     vm_err := err_flag;
     vm_logic_acc := s.(vm_logic_acc);
     vm_mstatus := s.(vm_mstatus);
     vm_witness := s.(vm_witness);
     vm_certified := s.(vm_certified) |}.

(** advance_state_rm: State builder for instructions that also update registers
    or memory (rm = register/memory). Caller passes in the new regs and mem
    explicitly; advance_state_rm slots them in. Used by LOAD, STORE, ADD, XFER,
    XOR_*, CALL, RET, HEAP_LOAD, HEAP_STORE, and all the ALU ops. *)
Definition advance_state_rm (s : VMState) (instr : vm_instruction)
  (graph : PartitionGraph) (csrs : CSRState)
  (regs : list nat) (mem : list nat) (err_flag : bool)
  : VMState :=
  {| vm_graph := graph;
  vm_csrs := csrs;
  vm_regs := regs;
  vm_mem := mem;
  vm_pc := S s.(vm_pc);
  vm_mu := apply_cost s instr;
  vm_mu_tensor := s.(vm_mu_tensor);
  vm_err := err_flag;
  vm_logic_acc := s.(vm_logic_acc);
  vm_mstatus := s.(vm_mstatus);
  vm_witness := s.(vm_witness);
  vm_certified := s.(vm_certified) |}.

(** jump_state: Set PC to an arbitrary target instead of PC+1.
    Used by JUMP and the taken branch of JNEZ. *)
Definition jump_state (s : VMState) (instr : vm_instruction) (target : nat) : VMState :=
  {| vm_graph := s.(vm_graph);
     vm_csrs := s.(vm_csrs);
     vm_regs := s.(vm_regs);
     vm_mem := s.(vm_mem);
     vm_pc := target;
     vm_mu := apply_cost s instr;
     vm_mu_tensor := s.(vm_mu_tensor);
     vm_err := s.(vm_err);
     vm_logic_acc := s.(vm_logic_acc);
     vm_mstatus := s.(vm_mstatus);
     vm_witness := s.(vm_witness);
     vm_certified := s.(vm_certified) |}.

(** jump_state_rm: Like jump_state but also updates registers and memory.
    Used by CALL (saves the return address to memory, increments the SP register)
    and RET (decrements it). *)
Definition jump_state_rm (s : VMState) (instr : vm_instruction)
  (target : nat) (regs : list nat) (mem : list nat) : VMState :=
  {| vm_graph := s.(vm_graph);
     vm_csrs := s.(vm_csrs);
     vm_regs := regs;
     vm_mem := mem;
     vm_pc := target;
     vm_mu := apply_cost s instr;
     vm_mu_tensor := s.(vm_mu_tensor);
     vm_err := s.(vm_err);
     vm_logic_acc := s.(vm_logic_acc);
     vm_mstatus := s.(vm_mstatus);
     vm_witness := s.(vm_witness);
     vm_certified := s.(vm_certified) |}.

(** Hardware-aligned constants and helpers *)

(** Trap PC: hardware branches here on LASSERT failure.
    Must match KamiHW.Abstraction.LASSERT_TRAP_PC and ThieleCPUCore.v. *)
Definition LASSERT_TRAP_PC : nat := 3840.

(** Get module region size from graph, defaulting to 0 if not found. *)
Definition graph_module_size (g : PartitionGraph) (mid : ModuleID) : nat :=
  match graph_lookup g mid with
  | Some m => List.length m.(module_region)
  | None => 0
  end.

(** ** Partition operations on real memory ranges

    A module owns a range of data-memory addresses, [List.seq base len].
    PNEW claims a range, PSPLIT cuts a module's range in two at its middle,
    PMERGE joins two ranges that touch. No address ever belongs to two
    modules: PNEW and PMERGE trap instead of building an overlap or a
    region with a hole, and the theorems at the end of this file prove that
    every step keeps the regions disjoint and contiguous. *)

(** Region of module [mid], or the empty region when [mid] is not in the graph. *)
Definition graph_module_region (g : PartitionGraph) (mid : ModuleID) : list nat :=
  match graph_lookup g mid with
  | Some m => m.(module_region)
  | None => []
  end.

(** pnew_region: the range PNEW claims. The hardware PNEW word carries a base
    address (operand A) and a length (operand B). The kernel instruction
    carries a region list and reads it the same way: base is the first
    address of the normalized list, len is the number of distinct addresses. *)
Definition pnew_region (region : list nat) : list nat :=
  let r := normalize_region region in
  List.seq (hd 0 r) (List.length r).

Lemma pnew_region_contiguous : forall region, region_contiguous (pnew_region region).
Proof. intro region. unfold pnew_region. apply region_contiguous_seq. Qed.

Lemma pnew_region_normalized : forall region,
  normalize_region (pnew_region region) = pnew_region region.
Proof. intro region. unfold pnew_region. apply normalize_region_seq_range. Qed.

(** region_conflict g r: some module's region shares an address with [r]
    without being the same set of addresses. PNEW traps on a conflict. A
    region equal to an existing module's region is not a conflict: PNEW then
    returns that module, as [graph_pnew] does. *)
Definition region_conflict (g : PartitionGraph) (r : list nat) : bool :=
  existsb (fun p => negb (nat_list_eq (snd p).(module_region) r) &&
                    negb (nat_list_disjoint (snd p).(module_region) r))
          g.(pg_modules).

(** PNEW of the empty region claims nothing, so it never conflicts. *)
Lemma pnew_region_nil : pnew_region [] = [].
Proof. reflexivity. Qed.

Lemma region_conflict_nil : forall g, region_conflict g [] = false.
Proof.
  intro g. unfold region_conflict.
  induction (pg_modules g) as [|p rest IH]; [reflexivity|].
  cbn [existsb]. rewrite IH.
  assert (Hd : nat_list_disjoint (module_region (snd p)) [] = true).
  { apply nat_list_disjoint_spec. intros x _ []. }
  rewrite Hd. rewrite andb_false_r. reflexivity.
Qed.

(** module_room g k: issuing [k] more module numbers keeps every number
    below [NUM_MODULES], the 64 slots of the hardware partition table.
    PNEW, PSPLIT and PMERGE take their module numbers from [pg_next_id] and
    never reuse one, so [pg_next_id] counts every number ever issued. *)
Definition module_room (g : PartitionGraph) (k : nat) : bool :=
  Nat.leb (g.(pg_next_id) + k) NUM_MODULES.

(** region_in_memory r: every address of [r] is a data-memory address. *)
Definition region_in_memory (r : list nat) : bool :=
  forallb (fun a => Nat.ltb a MEM_SIZE) r.

(** pnew_ok g r: PNEW of the range [r] succeeds. A module number is free,
    the range lies inside data memory, and the range overlaps no module
    except one whose range it is. PNEW traps otherwise. *)
Definition pnew_ok (g : PartitionGraph) (r : list nat) : bool :=
  module_room g 1 && region_in_memory r && negb (region_conflict g r).

Lemma pnew_ok_spec : forall g r, pnew_ok g r = true ->
  module_room g 1 = true /\ region_in_memory r = true /\ region_conflict g r = false.
Proof.
  intros g r H. unfold pnew_ok in H.
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply negb_true_iff in H3. auto.
Qed.

Lemma module_room_spec : forall g k,
  module_room g k = true <-> g.(pg_next_id) + k <= NUM_MODULES.
Proof. intros g k. unfold module_room. apply Nat.leb_le. Qed.

Lemma region_in_memory_spec : forall r,
  region_in_memory r = true <-> (forall a, In a r -> a < MEM_SIZE).
Proof.
  intro r. unfold region_in_memory. rewrite forallb_forall.
  split; intros H a Ha; [apply Nat.ltb_lt; exact (H a Ha) | apply Nat.ltb_lt; exact (H a Ha)].
Qed.

(** On a range the memory check is the hardware's base + length test. *)
Lemma region_in_memory_seq : forall b n,
  region_in_memory (List.seq b n) = true <-> n = 0 \/ b + n <= MEM_SIZE.
Proof.
  intros b n. rewrite region_in_memory_spec. split.
  - intros H. destruct n as [|n]; [left; reflexivity|right].
    assert (Hl : In (b + n) (List.seq b (S n))) by (apply in_seq; lia).
    specialize (H _ Hl). lia.
  - intros [->|Hle] a Ha; [destruct Ha|]. apply in_seq in Ha. lia.
Qed.

Arguments module_room : simpl never.
Arguments pnew_ok : simpl never.

(** PNEW of the empty region claims no address, so it succeeds exactly when
    a module number is free. *)
Lemma pnew_ok_nil : forall g, pnew_ok g [] = module_room g 1.
Proof.
  intro g. unfold pnew_ok. rewrite region_conflict_nil.
  cbn [region_in_memory forallb negb]. rewrite andb_true_r, andb_true_r. reflexivity.
Qed.

(** pnew_adds_module g region: PNEW of [region] adds a fresh module to [g].
    PNEW succeeds, and no module owns exactly that range. *)
Definition pnew_adds_module (g : PartitionGraph) (region : list nat) : Prop :=
  pnew_ok g (pnew_region region) = true /\
  graph_find_region g (pnew_region region) = None.

(** region_contiguousb: decision procedure for [region_contiguous]. *)
Definition region_contiguousb (r : list nat) : bool :=
  if list_eq_dec Nat.eq_dec r (List.seq (hd 0 r) (List.length r)) then true else false.

Lemma region_contiguousb_spec : forall r,
  region_contiguousb r = true -> region_contiguous r.
Proof.
  intros r H. unfold region_contiguousb in H.
  destruct (list_eq_dec Nat.eq_dec r (List.seq (hd 0 r) (List.length r))) as [E|E].
  - exact E.
  - discriminate.
Qed.

(** pmerge_adjacent g m1 m2: the two regions laid end to end, in one order or
    the other, form one range. A range has no repeated address, so two
    adjacent regions are disjoint. PMERGE traps when this fails. *)
Definition pmerge_adjacent (g : PartitionGraph) (m1 m2 : ModuleID) : bool :=
  let r1 := graph_module_region g m1 in
  let r2 := graph_module_region g m2 in
  region_contiguousb (r1 ++ r2) || region_contiguousb (r2 ++ r1).

(** pmerge_ok g m1 m2: PMERGE succeeds. A module number is free and the two
    ranges touch. PMERGE traps otherwise. *)
Definition pmerge_ok (g : PartitionGraph) (m1 m2 : ModuleID) : bool :=
  module_room g 1 && pmerge_adjacent g m1 m2.

Arguments pmerge_ok : simpl never.

Lemma pmerge_ok_spec : forall g m1 m2, pmerge_ok g m1 m2 = true ->
  module_room g 1 = true /\ pmerge_adjacent g m1 m2 = true.
Proof. intros g m1 m2 H. unfold pmerge_ok in H. apply andb_true_iff in H. exact H. Qed.

(** pmerge_region r1 r2: the joined range, starting at the lower base. *)
Definition pmerge_region (r1 r2 : list nat) : list nat :=
  if region_contiguousb (r1 ++ r2) then r1 ++ r2 else r2 ++ r1.

(** psplit_left / psplit_right: the first half (rounded down) of a region
    and the rest. On a range [List.seq b n] they are [List.seq b (n/2)] and
    [List.seq (b + n/2) (n - n/2)]. *)
Definition psplit_left (r : list nat) : list nat :=
  firstn (Nat.div (List.length r) 2) r.

Definition psplit_right (r : list nat) : list nat :=
  skipn (Nat.div (List.length r) 2) r.

(** csr_err value of a partition fault. Every kernel fault writes 1 to
    csr_err; the hardware error_code register carries the word that tells
    the faults apart. *)
Definition ERR_PARTITION_OVERLAP : nat := 1.

(** partition_step_state s instr ok graph: the state after PNEW, PSPLIT or
    PMERGE.
    When [ok] holds the step installs [graph] and advances the pc, exactly
    as [advance_state] does. When [ok] fails the step traps the way a
    failed LASSERT does: the graph stays as it was, csr_err is set, the
    error flag latches, and the pc jumps to the trap vector. The cost is
    charged either way ([vm_mu] is [apply_cost s instr], written out). *)
Definition partition_step_state (s : VMState) (instr : vm_instruction)
  (ok : bool) (graph : PartitionGraph) : VMState :=
  {| vm_graph := if ok then graph else s.(vm_graph);
     vm_csrs := if ok then s.(vm_csrs) else csr_set_err s.(vm_csrs) ERR_PARTITION_OVERLAP;
     vm_regs := s.(vm_regs);
     vm_mem := s.(vm_mem);
     vm_pc := if ok then S s.(vm_pc) else LASSERT_TRAP_PC;
     vm_mu := s.(vm_mu) + instruction_cost instr;
     vm_mu_tensor := s.(vm_mu_tensor);
     vm_err := if ok then s.(vm_err) else true;
     vm_logic_acc := s.(vm_logic_acc);
     vm_mstatus := s.(vm_mstatus);
     vm_witness := s.(vm_witness);
     vm_certified := s.(vm_certified) |}.

Lemma partition_step_state_graph : forall s instr ok graph,
  vm_graph (partition_step_state s instr ok graph) = if ok then graph else vm_graph s.
Proof. reflexivity. Qed.

Lemma partition_step_state_ok : forall s instr graph,
  partition_step_state s instr true graph =
  advance_state s instr graph s.(vm_csrs) s.(vm_err).
Proof. reflexivity. Qed.

(** graph_hw_psplit: Hardware-aligned PSPLIT. Every morphism with the module
    as source or target is deleted, as [graph_psplit] does, the module is
    removed, and two fresh modules take the two halves of its range: the left
    one gets the first size/2 addresses, the right one the rest. A module ID
    that is not in the graph has the empty region, so both halves are empty.
    The step rule reads the module ID modulo 64, the width of the hardware
    operand. Every module ID of a reachable state is below 64
    ([vm_reachable_partition_in_bounds]), so the reading names every live
    module and no two live modules alias. *)
Definition graph_hw_psplit (g : PartitionGraph) (mid : nat) : PartitionGraph :=
  let orig := normalize_region (graph_module_region g mid) in
  let g0 := graph_cascade_delete_morphisms g mid in
  let g1 := match graph_remove g0 mid with
             | Some (g', _) => g'
             | None => g0
             end in
  let '(g2, _) := graph_add_module g1 (psplit_left orig) [] in
  let '(g3, _) := graph_add_module g2 (psplit_right orig) [] in
  g3.

(** graph_hw_pmerge: Hardware-aligned PMERGE. Every morphism with either
    module as source or target is deleted, as [graph_pmerge] does, both
    modules are removed, and one fresh module takes the joined range. The
    step rule runs it only when [pmerge_adjacent] holds. *)
Definition graph_hw_pmerge (g : PartitionGraph) (m1 m2 : nat) : PartitionGraph :=
  let merged := pmerge_region (graph_module_region g m1) (graph_module_region g m2) in
  let g0 := graph_cascade_delete_morphisms (graph_cascade_delete_morphisms g m1) m2 in
  let g1 := match graph_remove g0 m1 with
             | Some (g', _) => g'
             | None => g0
             end in
  let g2 := match graph_remove g1 m2 with
             | Some (g', _) => g'
             | None => g1
             end in
  let '(g3, _) := graph_add_module g2 merged [] in
  g3.

(** Helper for LASSERT: compute whether the binary SAT check passes. *)
(** ** Column-contractivity check on the CHSH WitnessCounts buckets

    For each setting pair (x,y) ∈ {0,1}² the WitnessCounts hold a [same] and a
    [diff] bucket. The signed difference [d_xy = same_xy - diff_xy] and the
    sum [n_xy = same_xy + diff_xy] (both interpreted in Z) determine the
    correlator [E_xy = d_xy / n_xy] (in R). The three column-contractivity
    conditions on the correlators
       1 - E_00^2 - E_10^2 >= 0
       1 - E_01^2 - E_11^2 >= 0
       (1 - E_00^2 - E_10^2)(1 - E_01^2 - E_11^2) >= (E_00*E_01 + E_10*E_11)^2
    are equivalent (after clearing denominators by the positive
    [n_00^2*n_01^2*n_10^2*n_11^2]) to three Z-arithmetic inequalities
       A := n_00^2 * n_10^2 - d_00^2 * n_10^2 - d_10^2 * n_00^2 >= 0
       B := n_01^2 * n_11^2 - d_01^2 * n_11^2 - d_11^2 * n_01^2 >= 0
       A * B >= C^2,  where C := d_00*d_01*n_10*n_11 + d_10*d_11*n_00*n_01
    Each n_xy must also be strictly positive (a correlator needs at least
    one trial per setting pair). The check function below is decidable and
    runs at kernel-step time using only integer arithmetic.

    The bridge theorem is
    [MuLedgerQuantumBridge.column_contractive_check_witness_sound]:
        column_contractive_check_witness wc = true
          -> zero_marginal_column_contractive (E_00 wc) (E_01 wc) (E_10 wc) (E_11 wc)
    which combined with [column_contractive_iff_npa_psd]
    (QuantumPartitionPSD.v) gives NPA-PSD on the witness-derived correlators
    whenever the check passes.
*)

Definition chsh_d_z (same diff : nat) : Z :=
  (Z.of_nat same - Z.of_nat diff)%Z.

Definition chsh_n_z (same diff : nat) : Z :=
  (Z.of_nat same + Z.of_nat diff)%Z.

Definition column_contractive_check_witness (wc : WitnessCounts) : bool :=
  let d00 := chsh_d_z wc.(wc_same_00) wc.(wc_diff_00) in
  let n00 := chsh_n_z wc.(wc_same_00) wc.(wc_diff_00) in
  let d01 := chsh_d_z wc.(wc_same_01) wc.(wc_diff_01) in
  let n01 := chsh_n_z wc.(wc_same_01) wc.(wc_diff_01) in
  let d10 := chsh_d_z wc.(wc_same_10) wc.(wc_diff_10) in
  let n10 := chsh_n_z wc.(wc_same_10) wc.(wc_diff_10) in
  let d11 := chsh_d_z wc.(wc_same_11) wc.(wc_diff_11) in
  let n11 := chsh_n_z wc.(wc_same_11) wc.(wc_diff_11) in
  let n00sq := (n00 * n00)%Z in
  let n01sq := (n01 * n01)%Z in
  let n10sq := (n10 * n10)%Z in
  let n11sq := (n11 * n11)%Z in
  let d00sq := (d00 * d00)%Z in
  let d01sq := (d01 * d01)%Z in
  let d10sq := (d10 * d10)%Z in
  let d11sq := (d11 * d11)%Z in
  let A := (n00sq * n10sq - d00sq * n10sq - d10sq * n00sq)%Z in
  let B := (n01sq * n11sq - d01sq * n11sq - d11sq * n01sq)%Z in
  let C := (d00 * d01 * n10 * n11 + d10 * d11 * n00 * n01)%Z in
  andb (Z.ltb 0 n00)
  (andb (Z.ltb 0 n01)
  (andb (Z.ltb 0 n10)
  (andb (Z.ltb 0 n11)
  (andb (Z.leb 0 A)
  (andb (Z.leb 0 B)
        (Z.leb (C * C) (A * B))))))).

(** ** Q_{1+AB} integer check: sum-of-squares bound on the four correlators

    Verifies, in pure Z arithmetic, the additional condition
       E_{00}^2 + E_{01}^2 + E_{10}^2 + E_{11}^2 <= 1
    by clearing denominators. With N_xy = same+diff and D_xy = same-diff,
    the cleared inequality is
       D_00^2 * N_01^2 * N_10^2 * N_11^2
       + N_00^2 * D_01^2 * N_10^2 * N_11^2
       + N_00^2 * N_01^2 * D_10^2 * N_11^2
       + N_00^2 * N_01^2 * N_10^2 * D_11^2
       <=  N_00^2 * N_01^2 * N_10^2 * N_11^2.

    The combined Q_{1+AB} check (used by [instr_chsh_lassert_1ab]) is
    the conjunction of [column_contractive_check_witness] and
    [sum_E_sq_check_witness]. Soundness for the column-contractive
    predicate at γ = 0 is proved in QuantumPartitionPSD_1AB.v. *)

Definition sum_E_sq_check_witness (wc : WitnessCounts) : bool :=
  let d00 := chsh_d_z wc.(wc_same_00) wc.(wc_diff_00) in
  let n00 := chsh_n_z wc.(wc_same_00) wc.(wc_diff_00) in
  let d01 := chsh_d_z wc.(wc_same_01) wc.(wc_diff_01) in
  let n01 := chsh_n_z wc.(wc_same_01) wc.(wc_diff_01) in
  let d10 := chsh_d_z wc.(wc_same_10) wc.(wc_diff_10) in
  let n10 := chsh_n_z wc.(wc_same_10) wc.(wc_diff_10) in
  let d11 := chsh_d_z wc.(wc_same_11) wc.(wc_diff_11) in
  let n11 := chsh_n_z wc.(wc_same_11) wc.(wc_diff_11) in
  let den := (n00 * n01 * n10 * n11)%Z in
  let den_sq := (den * den)%Z in
  let term00 := (d00 * d00 * n01 * n01 * n10 * n10 * n11 * n11)%Z in
  let term01 := (n00 * n00 * d01 * d01 * n10 * n10 * n11 * n11)%Z in
  let term10 := (n00 * n00 * n01 * n01 * d10 * d10 * n11 * n11)%Z in
  let term11 := (n00 * n00 * n01 * n01 * n10 * n10 * d11 * d11)%Z in
  Z.leb (term00 + term01 + term10 + term11) den_sq.

Definition column_contractive_check_q1ab_kernel (wc : WitnessCounts) : bool :=
  andb (column_contractive_check_witness wc)
       (sum_E_sq_check_witness wc).

(** ** Q_{1+AB} γ_5-aware integer check (abstract on signed correlators).

    Pure Z-arithmetic decider on (D_xy, N_xy, Ng5, Dg5) where:
      D_xy = (same - diff) in Z, N_xy = (same + diff) in Z (Q_1 buckets)
      g_5 = IZR Ng5 / IZR Dg5  with strict |Ng5| < Dg5

    Verifies:
      (a) every N_xy > 0,
      (b) Dg5 > 0 and -Dg5 < Ng5 < Dg5 (so |g_5| < 1 strictly),
      (c) the cleared SOS-witness polynomial inequality
            Dg5*(Dg5 - Ng5)*X_int + Dg5*(Dg5 + Ng5)*Y_int
            <= 2*(Dg5² - Ng5²)*Den2
          where X_int, Y_int, Den2 are integer-built squared sums and
          the denominator product.

    Soundness (in QuantumPartitionPSD_1AB.v): passing this check implies
    PSD9 of the 9x9 NPA Q_{1+AB} matrix at (E, 0, 0, 0, 0, g_5) when
    combined with column_contractive_check_witness for the (E_ij) part. *)
Definition q1ab_g5_check_z_kernel
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng5 Dg5 : Z) : bool :=
  ((0 <? N00)%Z)
  && ((0 <? N01)%Z)
  && ((0 <? N10)%Z)
  && ((0 <? N11)%Z)
  && ((0 <? Dg5)%Z)
  && ((-Dg5 <? Ng5)%Z)
  && ((Ng5 <? Dg5)%Z)
  && (let Apos := (D00 * N11 + D11 * N00)%Z in
      let Aneg := (D00 * N11 - D11 * N00)%Z in
      let Cpos := (D01 * N10 + D10 * N01)%Z in
      let Cneg := (D01 * N10 - D10 * N01)%Z in
      let n01n10sq := (N01 * N01 * (N10 * N10))%Z in
      let n00n11sq := (N00 * N00 * (N11 * N11))%Z in
      let Xint := (Apos * Apos * n01n10sq + Cneg * Cneg * n00n11sq)%Z in
      let Yint := (Aneg * Aneg * n01n10sq + Cpos * Cpos * n00n11sq)%Z in
      let Den2 := (n00n11sq * n01n10sq)%Z in
      (Dg5 * (Dg5 - Ng5) * Xint + Dg5 * (Dg5 + Ng5) * Yint
       <=? 2 * (Dg5 * Dg5 - Ng5 * Ng5) * Den2)%Z).

(** Composite Q_{1+AB} γ_5 integer check on a [WitnessCounts] and a γ_5
    nat bucket pair (same_g5, diff_g5). Reads the four CHSH correlator
    buckets from wc, the γ_5 numerator/denominator from the bucket pair,
    and conjoins the existing column_contractive_check_witness with the
    γ_5 SOS check. Used by [instr_chsh_lassert_1ab_g5]. *)
Definition q1ab_g5_full_integer_check_kernel
  (wc : WitnessCounts) (same_g5 diff_g5 : nat) : bool :=
  let Ng5 := chsh_d_z same_g5 diff_g5 in
  let Dg5 := chsh_n_z same_g5 diff_g5 in
  andb (column_contractive_check_witness wc)
       (q1ab_g5_check_z_kernel
          (chsh_d_z wc.(wc_same_00) wc.(wc_diff_00))
          (chsh_n_z wc.(wc_same_00) wc.(wc_diff_00))
          (chsh_d_z wc.(wc_same_01) wc.(wc_diff_01))
          (chsh_n_z wc.(wc_same_01) wc.(wc_diff_01))
          (chsh_d_z wc.(wc_same_10) wc.(wc_diff_10))
          (chsh_n_z wc.(wc_same_10) wc.(wc_diff_10))
          (chsh_d_z wc.(wc_same_11) wc.(wc_diff_11))
          (chsh_n_z wc.(wc_same_11) wc.(wc_diff_11))
          Ng5 Dg5).

(** ** Q_{1+AB} γ_{3,4,5} integer check via 4×4 Sylvester PD.

    Z-arithmetic decider on (D_xy, N_xy, Ng3, Dg3, Ng4, Dg4, Ng5, Dg5). The
    extension over the γ_5-only check encodes the inner ∀v∈R^4 inequality
    of the Section-14 caller witness as positive-definiteness of a 4×4
    symmetric matrix H_{γ_345} = det_M·M_M − M_N. PD is verified by
    Sylvester's criterion (4 leading principal minors > 0 in cleared-Z
    form). Soundness in QuantumPartitionPSD_1AB.v Section 15. *)

(** Cleared (integer-numerator) versions of A, B, C_M, det_M. *)

Definition cleared_A_num (D00 N00 D10 N10 : Z) : Z :=
  (N00*N00*N10*N10 - D00*D00*N10*N10 - D10*D10*N00*N00)%Z.

Definition cleared_C_M_num (D01 N01 D11 N11 : Z) : Z :=
  (N01*N01*N11*N11 - D01*D01*N11*N11 - D11*D11*N01*N01)%Z.

Definition cleared_B_num (D00 N00 D01 N01 D10 N10 D11 N11 : Z) : Z :=
  (- (D00*D01*N10*N11 + D10*D11*N00*N01))%Z.

Definition cleared_det_M_num (D00 N00 D01 N01 D10 N10 D11 N11 : Z) : Z :=
  (cleared_A_num D00 N00 D10 N10 * cleared_C_M_num D01 N01 D11 N11
   - cleared_B_num D00 N00 D01 N01 D10 N10 D11 N11
     * cleared_B_num D00 N00 D01 N01 D10 N10 D11 N11)%Z.

(** Uniform common scaling factor: N_e^4 · D_g^2. *)
Definition COMMON_Z
  (N00 N01 N10 N11 Dg3 Dg4 Dg5 : Z) : Z :=
  (N00*N00*N00*N00 * (N01*N01*N01*N01) * (N10*N10*N10*N10) * (N11*N11*N11*N11)
   * (Dg3*Dg3) * (Dg4*Dg4) * (Dg5*Dg5))%Z.

(** Per-entry cleared numerators (small Z polynomials, one per H_ij). *)

Definition cH11_per_entry (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 : Z) : Z :=
  let detM := cleared_det_M_num D00 N00 D01 N01 D10 N10 D11 N11 in
  let A_n := cleared_A_num D00 N00 D10 N10 in
  (Dg3*Dg3 * detM * (N00*N00 - D00*D00)
   - N00*N00 * N01*N01 * N11*N11 * A_n * (Ng3*Ng3))%Z.

Definition cH22_per_entry (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 : Z) : Z :=
  let detM := cleared_det_M_num D00 N00 D01 N01 D10 N10 D11 N11 in
  let CM_n := cleared_C_M_num D01 N01 D11 N11 in
  (Dg3*Dg3 * detM * (N01*N01 - D01*D01)
   - N00*N00 * N01*N01 * N10*N10 * CM_n * (Ng3*Ng3))%Z.

Definition cH33_per_entry (D00 N00 D01 N01 D10 N10 D11 N11 Ng4 Dg4 : Z) : Z :=
  let detM := cleared_det_M_num D00 N00 D01 N01 D10 N10 D11 N11 in
  let A_n := cleared_A_num D00 N00 D10 N10 in
  (Dg4*Dg4 * detM * (N10*N10 - D10*D10)
   - N01*N01 * N10*N10 * N11*N11 * A_n * (Ng4*Ng4))%Z.

Definition cH44_per_entry (D00 N00 D01 N01 D10 N10 D11 N11 Ng4 Dg4 : Z) : Z :=
  let detM := cleared_det_M_num D00 N00 D01 N01 D10 N10 D11 N11 in
  let CM_n := cleared_C_M_num D01 N01 D11 N11 in
  (Dg4*Dg4 * detM * (N11*N11 - D11*D11)
   - N00*N00 * N10*N10 * N11*N11 * CM_n * (Ng4*Ng4))%Z.

Definition cH12_per_entry (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 : Z) : Z :=
  let detM := cleared_det_M_num D00 N00 D01 N01 D10 N10 D11 N11 in
  let B_n := cleared_B_num D00 N00 D01 N01 D10 N10 D11 N11 in
  (- (Dg3*Dg3 * detM * D00 * D01)
   + N00*N00 * N01*N01 * N10 * N11 * B_n * (Ng3*Ng3))%Z.

Definition cH13_per_entry (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 : Z) : Z :=
  let detM := cleared_det_M_num D00 N00 D01 N01 D10 N10 D11 N11 in
  let A_n := cleared_A_num D00 N00 D10 N10 in
  (- (Dg3 * Dg4 * detM * D00 * D10)
   - N00 * N01*N01 * N10 * N11*N11 * A_n * Ng3 * Ng4)%Z.

Definition cH14_per_entry (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  let detM := cleared_det_M_num D00 N00 D01 N01 D10 N10 D11 N11 in
  let B_n := cleared_B_num D00 N00 D01 N01 D10 N10 D11 N11 in
  (N00 * N11 * Dg3 * Dg4 * detM * Ng5
   - Dg3 * Dg4 * Dg5 * detM * D00 * D11
   + N00*N00 * N01 * N10 * N11*N11 * Dg5 * B_n * Ng3 * Ng4)%Z.

Definition cH23_per_entry (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  let detM := cleared_det_M_num D00 N00 D01 N01 D10 N10 D11 N11 in
  let B_n := cleared_B_num D00 N00 D01 N01 D10 N10 D11 N11 in
  (- (N01 * N10 * Dg3 * Dg4 * detM * Ng5)
   - Dg3 * Dg4 * Dg5 * detM * D01 * D10
   + N00 * N01*N01 * N10*N10 * N11 * Dg5 * B_n * Ng3 * Ng4)%Z.

Definition cH24_per_entry (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 : Z) : Z :=
  let detM := cleared_det_M_num D00 N00 D01 N01 D10 N10 D11 N11 in
  let CM_n := cleared_C_M_num D01 N01 D11 N11 in
  (- (Dg3 * Dg4 * detM * D01 * D11)
   - N00*N00 * N01 * N10*N10 * N11 * CM_n * Ng3 * Ng4)%Z.

Definition cH34_per_entry (D00 N00 D01 N01 D10 N10 D11 N11 Ng4 Dg4 : Z) : Z :=
  let detM := cleared_det_M_num D00 N00 D01 N01 D10 N10 D11 N11 in
  let B_n := cleared_B_num D00 N00 D01 N01 D10 N10 D11 N11 in
  (- (Dg4*Dg4 * detM * D10 * D11)
   + N00 * N01 * N10*N10 * N11*N11 * B_n * (Ng4*Ng4))%Z.

(** Multipliers (COMMON/scale_ij) lifting per-entry cH to uniform COMMON. *)
Definition mult_for_H11 (N01 N10 N11 Dg4 Dg5 : Z) : Z :=
  (N01*N01 * (N10*N10) * (N11*N11) * (Dg4*Dg4) * (Dg5*Dg5))%Z.
Definition mult_for_H22 (N00 N10 N11 Dg4 Dg5 : Z) : Z :=
  (N00*N00 * (N10*N10) * (N11*N11) * (Dg4*Dg4) * (Dg5*Dg5))%Z.
Definition mult_for_H33 (N00 N01 N11 Dg3 Dg5 : Z) : Z :=
  (N00*N00 * (N01*N01) * (N11*N11) * (Dg3*Dg3) * (Dg5*Dg5))%Z.
Definition mult_for_H44 (N00 N01 N10 Dg3 Dg5 : Z) : Z :=
  (N00*N00 * (N01*N01) * (N10*N10) * (Dg3*Dg3) * (Dg5*Dg5))%Z.
Definition mult_for_H12 (N00 N01 N10 N11 Dg4 Dg5 : Z) : Z :=
  (N00 * N01 * (N10*N10) * (N11*N11) * (Dg4*Dg4) * (Dg5*Dg5))%Z.
Definition mult_for_H13 (N00 N01 N10 N11 Dg3 Dg4 Dg5 : Z) : Z :=
  (N00 * (N01*N01) * N10 * (N11*N11) * Dg3 * Dg4 * (Dg5*Dg5))%Z.
Definition mult_for_H14 (N00 N01 N10 N11 Dg3 Dg4 Dg5 : Z) : Z :=
  (N00 * (N01*N01) * (N10*N10) * N11 * Dg3 * Dg4 * Dg5)%Z.
Definition mult_for_H23 (N00 N01 N10 N11 Dg3 Dg4 Dg5 : Z) : Z :=
  (N00*N00 * N01 * N10 * (N11*N11) * Dg3 * Dg4 * Dg5)%Z.
Definition mult_for_H24 (N00 N01 N10 N11 Dg3 Dg4 Dg5 : Z) : Z :=
  (N00*N00 * N01 * (N10*N10) * N11 * Dg3 * Dg4 * (Dg5*Dg5))%Z.
Definition mult_for_H34 (N00 N01 N10 N11 Dg3 Dg5 : Z) : Z :=
  (N00*N00 * (N01*N01) * N10 * N11 * (Dg3*Dg3) * (Dg5*Dg5))%Z.

(** Cleared H entries (uniform COMMON scaling). *)
Definition cleared_H11_Z
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (mult_for_H11 N01 N10 N11 Dg4 Dg5
   * cH11_per_entry D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3)%Z.
Definition cleared_H22_Z
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (mult_for_H22 N00 N10 N11 Dg4 Dg5
   * cH22_per_entry D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3)%Z.
Definition cleared_H33_Z
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (mult_for_H33 N00 N01 N11 Dg3 Dg5
   * cH33_per_entry D00 N00 D01 N01 D10 N10 D11 N11 Ng4 Dg4)%Z.
Definition cleared_H44_Z
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (mult_for_H44 N00 N01 N10 Dg3 Dg5
   * cH44_per_entry D00 N00 D01 N01 D10 N10 D11 N11 Ng4 Dg4)%Z.
Definition cleared_H12_Z
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (mult_for_H12 N00 N01 N10 N11 Dg4 Dg5
   * cH12_per_entry D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3)%Z.
Definition cleared_H13_Z
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (mult_for_H13 N00 N01 N10 N11 Dg3 Dg4 Dg5
   * cH13_per_entry D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4)%Z.
Definition cleared_H14_Z
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (mult_for_H14 N00 N01 N10 N11 Dg3 Dg4 Dg5
   * cH14_per_entry D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)%Z.
Definition cleared_H23_Z
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (mult_for_H23 N00 N01 N10 N11 Dg3 Dg4 Dg5
   * cH23_per_entry D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)%Z.
Definition cleared_H24_Z
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (mult_for_H24 N00 N01 N10 N11 Dg3 Dg4 Dg5
   * cH24_per_entry D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4)%Z.
Definition cleared_H34_Z
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (mult_for_H34 N00 N01 N10 N11 Dg3 Dg5
   * cH34_per_entry D00 N00 D01 N01 D10 N10 D11 N11 Ng4 Dg4)%Z.

(** Z-arithmetic 4×4 leading principal minors. *)
Definition sym4_d1_Z (h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 : Z) : Z := h11.
Definition sym4_d2_Z (h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 : Z) : Z :=
  (h11*h22 - h12*h12)%Z.
Definition sym4_d3_Z (h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 : Z) : Z :=
  (h11*(h22*h33 - h23*h23)
   - h12*(h12*h33 - h13*h23)
   + h13*(h12*h23 - h13*h22))%Z.
Definition sym4_d4_Z (h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 : Z) : Z :=
  (h11*(h22*(h33*h44 - h34*h34) - h23*(h23*h44 - h24*h34) + h24*(h23*h34 - h24*h33))
   - h12*(h12*(h33*h44 - h34*h34) - h23*(h13*h44 - h14*h34) + h24*(h13*h34 - h14*h33))
   + h13*(h12*(h23*h44 - h24*h34) - h22*(h13*h44 - h14*h34) + h24*(h13*h24 - h14*h23))
   - h14*(h12*(h23*h34 - h24*h33) - h22*(h13*h34 - h14*h33) + h23*(h13*h24 - h14*h23)))%Z.

(** Composite cleared leading principal minors cd_k. *)
Definition cleared_d1
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  sym4_d1_Z
    (cleared_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H12_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H13_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H14_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H33_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H34_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H44_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).
Definition cleared_d2
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  sym4_d2_Z
    (cleared_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H12_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H13_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H14_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H33_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H34_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H44_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).
Definition cleared_d3
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  sym4_d3_Z
    (cleared_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H12_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H13_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H14_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H33_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H34_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H44_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).
Definition cleared_d4
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  sym4_d4_Z
    (cleared_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H12_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H13_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H14_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H33_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H34_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H44_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

(** Abstract Z-bool decider on 14 integer parameters. *)
Definition q1ab_g345_check_z_kernel
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : bool :=
  ((0 <? N00)%Z)
  && ((0 <? N01)%Z)
  && ((0 <? N10)%Z)
  && ((0 <? N11)%Z)
  && ((0 <? Dg3)%Z)
  && ((0 <? Dg4)%Z)
  && ((0 <? Dg5)%Z)
  && ((-Dg3 <? Ng3)%Z) && ((Ng3 <? Dg3)%Z)
  && ((-Dg4 <? Ng4)%Z) && ((Ng4 <? Dg4)%Z)
  && ((-Dg5 <? Ng5)%Z) && ((Ng5 <? Dg5)%Z)
  && ((0 <? cleared_A_num D00 N00 D10 N10)%Z)
  && ((0 <? cleared_C_M_num D01 N01 D11 N11)%Z)
  && ((0 <? cleared_det_M_num D00 N00 D01 N01 D10 N10 D11 N11)%Z)
  && ((0 <? cleared_d1 D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)%Z)
  && ((0 <? cleared_d2 D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)%Z)
  && ((0 <? cleared_d3 D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)%Z)
  && ((0 <? cleared_d4 D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)%Z).

(** Composite Q_{1+AB} γ_{3,4,5} integer check on [WitnessCounts] plus three
    γ-bucket pairs. Reads (D,N) for the 4 CHSH correlators from the witness
    counters and (Ng,Dg) for γ_3, γ_4, γ_5 from the supplied bucket pairs. *)
Definition q1ab_g345_full_integer_check_kernel
  (wc : WitnessCounts)
  (same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 : nat) : bool :=
  let Ng3 := chsh_d_z same_g3 diff_g3 in
  let Dg3 := chsh_n_z same_g3 diff_g3 in
  let Ng4 := chsh_d_z same_g4 diff_g4 in
  let Dg4 := chsh_n_z same_g4 diff_g4 in
  let Ng5 := chsh_d_z same_g5 diff_g5 in
  let Dg5 := chsh_n_z same_g5 diff_g5 in
  andb (column_contractive_check_witness wc)
       (q1ab_g345_check_z_kernel
          (chsh_d_z wc.(wc_same_00) wc.(wc_diff_00))
          (chsh_n_z wc.(wc_same_00) wc.(wc_diff_00))
          (chsh_d_z wc.(wc_same_01) wc.(wc_diff_01))
          (chsh_n_z wc.(wc_same_01) wc.(wc_diff_01))
          (chsh_d_z wc.(wc_same_10) wc.(wc_diff_10))
          (chsh_n_z wc.(wc_same_10) wc.(wc_diff_10))
          (chsh_d_z wc.(wc_same_11) wc.(wc_diff_11))
          (chsh_n_z wc.(wc_same_11) wc.(wc_diff_11))
          Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

(** ============================================================================
    Section 15.6. γ_{1,2,3,4,5} cleared-Z integer kernel (sym6 + Schur cascade).

    Lifts the real-valued [q1ab_g12345_minors_witness] (sym6_pd_interior at
    H_{γ_12345}) to a pure Z-arithmetic decision procedure. The cascade
    computes:

      - 21 cleared H_{ij}-numerators at uniform scaling
        [g12345_COMMON_Z] := (N00·N01·N10·N11·Dg1·Dg2·Dg3·Dg4·Dg5)²;
      - 15 cleared scaled_S_6 entries (4×4 Schur complement of row 1 of
        the sym6 H) at scaling g12345_COMMON_Z²;
      - 10 cleared scaled_S_5 entries (Schur of Schur: 4×4 Schur of row 1
        of the sym5 scaled_S_6) at scaling g12345_COMMON_Z⁴;
      - 4 sym4 Sylvester leading minors of the scaled_S_5 cleared values,
        at scaling g12345_COMMON_Z^(4·k) for k = 1..4.

    The kernel decider [q1ab_g12345_check_z_kernel] tests six positivities:
    cleared_H11 > 0, cleared_scaled_S_6_22 > 0, sym4_d_k of cleared
    scaled_S_5 > 0 for k = 1..4. Soundness in QuantumPartitionPSD_1AB.v
    Section 16.5. *)

(** Uniform common scaling factor for the 21-entry H_{γ_12345} matrix.
    All cleared H entries are at this scaling; cascade levels square it. *)
Definition g12345_COMMON_Z
  (N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5 : Z) : Z :=
  (let P := (N00*N01*N10*N11*Dg1*Dg2*Dg3*Dg4*Dg5)%Z in P*P)%Z.

(** Cleared H_{ij}-numerators at scaling g12345_COMMON_Z. Each is
    [g12345_COMMON_Z · q12345_HXX(D00/N00, ..., Ng5/Dg5)] expressed as a
    pure Z polynomial. *)

Definition cleared_g12345_H11_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* g12345_COMMON_Z · (1 - (D00/N00)² - (D10/N10)²)
     = (N01·N11·Dg1·Dg2·Dg3·Dg4·Dg5)² · (N00²·N10² - D00²·N10² - D10²·N00²) *)
  ((N01*N11*Dg1*Dg2*Dg3*Dg4*Dg5)
   * (N01*N11*Dg1*Dg2*Dg3*Dg4*Dg5)
   * (N00*N00*N10*N10 - D00*D00*N10*N10 - D10*D10*N00*N00))%Z.

Definition cleared_g12345_H22_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  ((N00*N10*Dg1*Dg2*Dg3*Dg4*Dg5)
   * (N00*N10*Dg1*Dg2*Dg3*Dg4*Dg5)
   * (N01*N01*N11*N11 - D01*D01*N11*N11 - D11*D11*N01*N01))%Z.

Definition cleared_g12345_H33_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_33 = 1 - e00² - g1² = (Dg1²·N00² - Dg1²·D00² - Ng1²·N00²)/(N00²·Dg1²)
     COMMON·H_33 = (N01·N10·N11·Dg2·Dg3·Dg4·Dg5)² · (Dg1²·(N00² - D00²) - Ng1²·N00²) *)
  ((N01*N10*N11*Dg2*Dg3*Dg4*Dg5)
   * (N01*N10*N11*Dg2*Dg3*Dg4*Dg5)
   * (Dg1*Dg1*(N00*N00 - D00*D00) - Ng1*Ng1*N00*N00))%Z.

Definition cleared_g12345_H44_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  ((N00*N10*N11*Dg1*Dg3*Dg4*Dg5)
   * (N00*N10*N11*Dg1*Dg3*Dg4*Dg5)
   * (Dg2*Dg2*(N01*N01 - D01*D01) - Ng2*Ng2*N01*N01))%Z.

Definition cleared_g12345_H55_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  ((N00*N01*N11*Dg2*Dg3*Dg4*Dg5)
   * (N00*N01*N11*Dg2*Dg3*Dg4*Dg5)
   * (Dg1*Dg1*(N10*N10 - D10*D10) - Ng1*Ng1*N10*N10))%Z.

Definition cleared_g12345_H66_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  ((N00*N01*N10*Dg1*Dg3*Dg4*Dg5)
   * (N00*N01*N10*Dg1*Dg3*Dg4*Dg5)
   * (Dg2*Dg2*(N11*N11 - D11*D11) - Ng2*Ng2*N11*N11))%Z.

Definition cleared_g12345_H12_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_12 = -(e00·e01 + e10·e11) = -(D00·D01·N10·N11 + D10·D11·N00·N01)/(N00·N01·N10·N11)
     COMMON·H_12 = -(N00·N01·N10·N11)·(Dg1·Dg2·Dg3·Dg4·Dg5)² · (numerator) *)
  ((N00*N01*N10*N11) * (Dg1*Dg2*Dg3*Dg4*Dg5) * (Dg1*Dg2*Dg3*Dg4*Dg5)
   * (-(D00*D01*N10*N11 + D10*D11*N00*N01)))%Z.

Definition cleared_g12345_H13_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_13 = -e10·g1 = -(D10·Ng1)/(N10·Dg1)
     COMMON·H_13 = -(N10·Dg1)·(N00·N01·N11·Dg1·Dg2·Dg3·Dg4·Dg5)·(N00·N01·N10·N11·Dg2·Dg3·Dg4·Dg5)·(D10·Ng1)
     Group: COMMON / (N10·Dg1) = N10·N00²·N01²·N11²·Dg1·Dg2²·Dg3²·Dg4²·Dg5² *)
  ((N00*N00*N01*N01*N10*N11*N11*Dg1*Dg2*Dg2*Dg3*Dg3*Dg4*Dg4*Dg5*Dg5)
   * (-(D10*Ng1)))%Z.

Definition cleared_g12345_H14_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_14 = g3 - e10·g2 = (Ng3·N10·Dg2 - D10·Ng2·Dg3)/(N10·Dg2·Dg3)
     COMMON / (N10·Dg2·Dg3) = N10·N00²·N01²·N11²·Dg1²·Dg2·Dg3·Dg4²·Dg5² *)
  ((N00*N00*N01*N01*N10*N11*N11*Dg1*Dg1*Dg2*Dg3*Dg4*Dg4*Dg5*Dg5)
   * (Ng3*N10*Dg2 - D10*Ng2*Dg3))%Z.

Definition cleared_g12345_H15_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_15 = -e00·g1 = -(D00·Ng1)/(N00·Dg1)
     COMMON / (N00·Dg1) = N00·N01²·N10²·N11²·Dg1·Dg2²·Dg3²·Dg4²·Dg5² *)
  ((N00*N01*N01*N10*N10*N11*N11*Dg1*Dg2*Dg2*Dg3*Dg3*Dg4*Dg4*Dg5*Dg5)
   * (-(D00*Ng1)))%Z.

Definition cleared_g12345_H16_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_16 = g4 - e00·g2 = (Ng4·N00·Dg2 - D00·Ng2·Dg4)/(N00·Dg2·Dg4)
     COMMON / (N00·Dg2·Dg4) = N00·N01²·N10²·N11²·Dg1²·Dg2·Dg3²·Dg4·Dg5² *)
  ((N00*N01*N01*N10*N10*N11*N11*Dg1*Dg1*Dg2*Dg3*Dg3*Dg4*Dg5*Dg5)
   * (Ng4*N00*Dg2 - D00*Ng2*Dg4))%Z.

Definition cleared_g12345_H23_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_23 = g3 - e11·g1 = (Ng3·N11·Dg1 - D11·Ng1·Dg3)/(N11·Dg1·Dg3)
     COMMON / (N11·Dg1·Dg3) = N11·N00²·N01²·N10²·Dg1·Dg2²·Dg3·Dg4²·Dg5² *)
  ((N00*N00*N01*N01*N10*N10*N11*Dg1*Dg2*Dg2*Dg3*Dg4*Dg4*Dg5*Dg5)
   * (Ng3*N11*Dg1 - D11*Ng1*Dg3))%Z.

Definition cleared_g12345_H24_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_24 = -e11·g2 = -(D11·Ng2)/(N11·Dg2)
     COMMON / (N11·Dg2) = N11·N00²·N01²·N10²·Dg1²·Dg2·Dg3²·Dg4²·Dg5² *)
  ((N00*N00*N01*N01*N10*N10*N11*Dg1*Dg1*Dg2*Dg3*Dg3*Dg4*Dg4*Dg5*Dg5)
   * (-(D11*Ng2)))%Z.

Definition cleared_g12345_H25_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_25 = g4 - e01·g1 = (Ng4·N01·Dg1 - D01·Ng1·Dg4)/(N01·Dg1·Dg4)
     COMMON / (N01·Dg1·Dg4) = N01·N00²·N10²·N11²·Dg1·Dg2²·Dg3²·Dg4·Dg5² *)
  ((N00*N00*N01*N10*N10*N11*N11*Dg1*Dg2*Dg2*Dg3*Dg3*Dg4*Dg5*Dg5)
   * (Ng4*N01*Dg1 - D01*Ng1*Dg4))%Z.

Definition cleared_g12345_H26_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_26 = -e01·g2 = -(D01·Ng2)/(N01·Dg2)
     COMMON / (N01·Dg2) = N01·N00²·N10²·N11²·Dg1²·Dg2·Dg3²·Dg4²·Dg5² *)
  ((N00*N00*N01*N10*N10*N11*N11*Dg1*Dg1*Dg2*Dg3*Dg3*Dg4*Dg4*Dg5*Dg5)
   * (-(D01*Ng2)))%Z.

Definition cleared_g12345_H34_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_34 = -(e00·e01 + g1·g2) = -(D00·D01·Dg1·Dg2 + Ng1·Ng2·N00·N01)/(N00·N01·Dg1·Dg2)
     COMMON / (N00·N01·Dg1·Dg2) = N00·N01·N10²·N11²·Dg1·Dg2·Dg3²·Dg4²·Dg5² *)
  ((N00*N01*N10*N10*N11*N11*Dg1*Dg2*Dg3*Dg3*Dg4*Dg4*Dg5*Dg5)
   * (-(D00*D01*Dg1*Dg2 + Ng1*Ng2*N00*N01)))%Z.

Definition cleared_g12345_H35_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_35 = -e00·e10 = -(D00·D10)/(N00·N10)
     COMMON / (N00·N10) = N00·N01²·N10·N11²·Dg1²·Dg2²·Dg3²·Dg4²·Dg5² *)
  ((N00*N01*N01*N10*N11*N11*Dg1*Dg1*Dg2*Dg2*Dg3*Dg3*Dg4*Dg4*Dg5*Dg5)
   * (-(D00*D10)))%Z.

Definition cleared_g12345_H36_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_36 = g5 - e00·e11 = (Ng5·N00·N11 - D00·D11·Dg5)/(N00·N11·Dg5)
     COMMON / (N00·N11·Dg5) = N00·N01²·N10²·N11·Dg1²·Dg2²·Dg3²·Dg4²·Dg5 *)
  ((N00*N01*N01*N10*N10*N11*Dg1*Dg1*Dg2*Dg2*Dg3*Dg3*Dg4*Dg4*Dg5)
   * (Ng5*N00*N11 - D00*D11*Dg5))%Z.

Definition cleared_g12345_H45_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_45 = -g5 - e01·e10 = (-Ng5·N01·N10 - D01·D10·Dg5)/(N01·N10·Dg5)
     (the conjugate four-body cell ⟨A₁A₂B₂B₁⟩ = -⟨A₁A₂B₁B₂⟩; sign forced by
      {B₁,B₂}=0 under the matrix's ⟨B₁B₂⟩=0 assumption)
     COMMON / (N01·N10·Dg5) = N00²·N01·N10·N11²·Dg1²·Dg2²·Dg3²·Dg4²·Dg5 *)
  ((N00*N00*N01*N10*N11*N11*Dg1*Dg1*Dg2*Dg2*Dg3*Dg3*Dg4*Dg4*Dg5)
   * (- Ng5*N01*N10 - D01*D10*Dg5))%Z.

Definition cleared_g12345_H46_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_46 = -e01·e11 = -(D01·D11)/(N01·N11)
     COMMON / (N01·N11) = N00²·N01·N10²·N11·Dg1²·Dg2²·Dg3²·Dg4²·Dg5² *)
  ((N00*N00*N01*N10*N10*N11*Dg1*Dg1*Dg2*Dg2*Dg3*Dg3*Dg4*Dg4*Dg5*Dg5)
   * (-(D01*D11)))%Z.

Definition cleared_g12345_H56_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_56 = -(e10·e11 + g1·g2) = -(D10·D11·Dg1·Dg2 + Ng1·Ng2·N10·N11)/(N10·N11·Dg1·Dg2)
     COMMON / (N10·N11·Dg1·Dg2) = N00²·N01²·N10·N11·Dg1·Dg2·Dg3²·Dg4²·Dg5² *)
  ((N00*N00*N01*N01*N10*N11*Dg1*Dg2*Dg3*Dg3*Dg4*Dg4*Dg5*Dg5)
   * (-(D10*D11*Dg1*Dg2 + Ng1*Ng2*N10*N11)))%Z.

(** Helper: integer Schur step [schur_step_Z h11 hij h1i h1j := h11·hij - h1i·h1j].
    Used inline for each of the 15 scaled_S_6 entries and 10 scaled_S_5
    entries below. *)
Definition schur_step_Z (h11 hij h1i h1j : Z) : Z :=
  (h11 * hij - h1i * h1j)%Z.

(** 15 cleared scaled_S_6_{ij} numerators (4×4 Schur of row 1 of sym6 H),
    each at scaling g12345_COMMON_Z². *)

Definition cleared_g12345_S6_22_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H12_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H12_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_23_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H12_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H13_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_24_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H12_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H14_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_25_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H25_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H12_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H15_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_26_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H26_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H12_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H16_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_33_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H33_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H13_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H13_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_34_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H34_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H13_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H14_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_35_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H35_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H13_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H15_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_36_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H36_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H13_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H16_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_44_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H44_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H14_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H14_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_45_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H45_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H14_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H15_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_46_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H46_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H14_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H16_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_55_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H55_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H15_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H15_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_56_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H56_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H15_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H16_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_66_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H66_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H16_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H16_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

(** 10 cleared scaled_S_5_{ij} numerators (4×4 Schur of row 1 of the 5×5
    scaled_S_6), each at scaling g12345_COMMON_Z⁴. The "h11" of the 5×5
    is scaled_S_6_22, and rows/cols 2..5 of the 5×5 are scaled_S_6 entries
    indexed (3..6). *)

Definition cleared_g12345_S5_22_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_S6_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_33_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S5_23_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_S6_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_34_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S5_24_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_S6_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_35_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_25_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S5_25_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_S6_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_36_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_26_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S5_33_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_S6_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_44_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S5_34_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_S6_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_45_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_25_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S5_35_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_S6_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_46_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_26_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S5_44_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_S6_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_55_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_25_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_25_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S5_45_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_S6_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_56_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_25_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_26_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S5_55_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_S6_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_66_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_26_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_26_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

(** Abstract Z-bool decider on 18 integer parameters (4 (D,N) bucket pairs
    for the CHSH correlators + 5 (Ng, Dg) bucket pairs for γ_1..γ_5). The
    six positivity checks come from the sym6 → sym5 → sym4 Schur cascade. *)
Definition q1ab_g12345_check_z_kernel
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : bool :=
  ((0 <? N00)%Z)
  && ((0 <? N01)%Z)
  && ((0 <? N10)%Z)
  && ((0 <? N11)%Z)
  && ((0 <? Dg1)%Z) && ((0 <? Dg2)%Z)
  && ((0 <? Dg3)%Z) && ((0 <? Dg4)%Z) && ((0 <? Dg5)%Z)
  && ((-Dg1 <? Ng1)%Z) && ((Ng1 <? Dg1)%Z)
  && ((-Dg2 <? Ng2)%Z) && ((Ng2 <? Dg2)%Z)
  && ((-Dg3 <? Ng3)%Z) && ((Ng3 <? Dg3)%Z)
  && ((-Dg4 <? Ng4)%Z) && ((Ng4 <? Dg4)%Z)
  && ((-Dg5 <? Ng5)%Z) && ((Ng5 <? Dg5)%Z)
  (* Schur cascade, six PD checks: *)
  && ((0 <? cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)%Z)
  && ((0 <? cleared_g12345_S6_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)%Z)
  && ((0 <? sym4_d1_Z
              (cleared_g12345_S5_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_25_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_33_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_34_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_35_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_44_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_45_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_55_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5))%Z)
  && ((0 <? sym4_d2_Z
              (cleared_g12345_S5_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_25_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_33_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_34_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_35_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_44_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_45_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_55_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5))%Z)
  && ((0 <? sym4_d3_Z
              (cleared_g12345_S5_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_25_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_33_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_34_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_35_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_44_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_45_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_55_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5))%Z)
  && ((0 <? sym4_d4_Z
              (cleared_g12345_S5_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_25_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_33_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_34_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_35_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_44_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_45_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_55_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5))%Z).

(** Composite γ_12345 integer check on a WitnessCounts plus five γ-bucket
    pairs. Reads (D, N) for the four CHSH correlators from the witness
    counters and (Ng, Dg) for γ_1..γ_5 from the supplied bucket pairs. *)
Definition q1ab_g12345_full_integer_check_kernel
  (wc : WitnessCounts)
  (same_g1 diff_g1 same_g2 diff_g2
   same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 : nat) : bool :=
  let Ng1 := chsh_d_z same_g1 diff_g1 in
  let Dg1 := chsh_n_z same_g1 diff_g1 in
  let Ng2 := chsh_d_z same_g2 diff_g2 in
  let Dg2 := chsh_n_z same_g2 diff_g2 in
  let Ng3 := chsh_d_z same_g3 diff_g3 in
  let Dg3 := chsh_n_z same_g3 diff_g3 in
  let Ng4 := chsh_d_z same_g4 diff_g4 in
  let Dg4 := chsh_n_z same_g4 diff_g4 in
  let Ng5 := chsh_d_z same_g5 diff_g5 in
  let Dg5 := chsh_n_z same_g5 diff_g5 in
  andb (column_contractive_check_witness wc)
       (q1ab_g12345_check_z_kernel
          (chsh_d_z wc.(wc_same_00) wc.(wc_diff_00))
          (chsh_n_z wc.(wc_same_00) wc.(wc_diff_00))
          (chsh_d_z wc.(wc_same_01) wc.(wc_diff_01))
          (chsh_n_z wc.(wc_same_01) wc.(wc_diff_01))
          (chsh_d_z wc.(wc_same_10) wc.(wc_diff_10))
          (chsh_n_z wc.(wc_same_10) wc.(wc_diff_10))
          (chsh_d_z wc.(wc_same_11) wc.(wc_diff_11))
          (chsh_n_z wc.(wc_same_11) wc.(wc_diff_11))
          Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

(** [CHSH_HONEST_MARKER]: the [ascii_checksum] of the property string
    "CHSH:column_contractive", in the same form as the [MORPH_ASSERT]
    cert-address values. No step writes it: CHSH_LASSERT signals success by
    advancing the pc with [vm_err] unchanged. *)
Definition CHSH_HONEST_MARKER : nat :=
  ascii_checksum "CHSH:column_contractive".

Definition lassert_check_ok (s : VMState) (freg creg : nat) (kind : bool) : bool :=
  let fbase := read_reg s freg in
  let cbase := read_reg s creg in
  let hw_flen := read_mem s fbase in
  let formula_words := List.map (fun i => read_mem s (fbase + i))
                                (List.seq 0 (3 + hw_flen)) in
  let num_vars :=
    match formula_words with
    | _ :: nv :: _ => nv
    | _ => 0
    end in
  let get_model := (fun var => read_mem s (cbase + var)) in
  let get_countermodel := (fun var => read_mem s (cbase + num_vars + var)) in
  if kind then
    andb (CertCheck.check_model_binary_fn formula_words get_model)
         (CertCheck.check_countermodel_binary_fn formula_words get_countermodel)
  else false.

(** Helper for LASSERT: hw_flen is the first word at formula base. *)
Definition lassert_hw_flen (s : VMState) (freg : nat) : nat :=
  read_mem s (read_reg s freg).

(** lassert_exec_ok: combined length-match + formula check.
    Success requires BOTH:
      (1) the instruction-encoded flen equals the in-memory formula header, AND
      (2) the formula has a satisfying assignment and a falsifying assignment.
    So a successful LASSERT step pays exactly hw_flen * 8 + S(cost), not a
    programmer-declared undercount. *)
Definition lassert_exec_ok (s : VMState) (freg creg : nat) (kind : bool) (flen : nat) : bool :=
  andb (Nat.eqb (lassert_hw_flen s freg) flen)
       (lassert_check_ok s freg creg kind).

(** [vm_step] is the inductive transition relation. Its constructors cover normal and failure paths, and the accompanying proofs establish the intended total, deterministic behavior and ledger update. *)
Inductive vm_step : VMState -> vm_instruction -> VMState -> Prop :=
(** step_pnew: Claim the range [pnew_region region]. If no module number is
    left, if the range runs past data memory, or if it overlaps a module's
    region without being equal to it, the step traps (see [pnew_ok] and
    [partition_step_state]). Otherwise [graph_pnew] adds a fresh module, or
    keeps the graph when a module already owns exactly that range. *)
| step_pnew : forall s region cost graph',
    graph' = fst (graph_pnew s.(vm_graph) (pnew_region region)) ->
    vm_step s (instr_pnew region cost)
      (partition_step_state s (instr_pnew region cost)
        (pnew_ok s.(vm_graph) (pnew_region region)) graph')
(** step_psplit: Split a module's range in two with graph_hw_psplit (left
    gets the first size/2 addresses, right gets the rest), as the CPU does.
    The abstract left/right parameters are accepted but ignored. The two
    halves take two fresh module numbers; when fewer than two are left the
    step traps. *)
| step_psplit : forall s module left right cost graph',
    graph' = graph_hw_psplit s.(vm_graph) (module mod 64) ->
    vm_step s (instr_psplit module left right cost)
      (partition_step_state s (instr_psplit module left right cost)
        (module_room s.(vm_graph) 2) graph')
(** step_pmerge: Join two modules whose ranges touch. graph_hw_pmerge removes
    both and creates one module with the joined range. If the two ranges do
    not form one range ([pmerge_adjacent] fails), or no module number is
    left, the step traps. Module IDs are read modulo 64. *)
| step_pmerge : forall s m1 m2 cost graph',
    graph' = graph_hw_pmerge s.(vm_graph) (m1 mod 64) (m2 mod 64) ->
    vm_step s (instr_pmerge m1 m2 cost)
      (partition_step_state s (instr_pmerge m1 m2 cost)
        (pmerge_ok s.(vm_graph) (m1 mod 64) (m2 mod 64)) graph')
(** step_lassert: Check a formula with a binary SAT certificate.
    freg = register holding formula base address in memory.
    creg = register holding certificate base address in memory.
    kind = true: SAT certificate with non-triviality witness.
      Memory at cbase stores two assignments back-to-back:
      - cbase + k: satisfying assignment value for variable k
      - cbase + num_vars + k: falsifying assignment value for variable k
      Variables are 1-indexed; slot 0 is ignored.
    false: UNSAT (always fails here).
     flen = declared formula-unit count (drives μ-cost via flen * 8 + S cost).
     The memory encoding uses natural-number words; the factor 8 is a
     VM pricing convention, not by itself a theorem that each unit is a byte
     or that the charge is a physical information count.

     The instruction is only allowed to succeed when flen matches the in-memory
     formula header [lassert_hw_flen s freg]. A mismatch traps exactly like a
     failed witness check. So a successful LASSERT cannot claim a cheaper
     length than the words the checker reads.

     On SAT success (lassert_exec_ok = true): advance PC normally, no error.
     On failure or length mismatch: jump to LASSERT_TRAP_PC (0xF00 = 3840),
     latch vm_err.
    μ-cost is always charged regardless of outcome. You pay to check, even to fail.
 UNSAT proof checking (kind=false) is NOT implemented. It always fails.
    This is documented in the file header. The SAT path certifies only
    non-trivial constraints: formulas with both a model and a countermodel.
    That is the minimum kernel-level guard against tautology inflation. *)
| step_lassert : forall s freg creg kind flen cost,
  let check_ok := lassert_exec_ok s freg creg kind flen in
    let new_pc   := if check_ok then S s.(vm_pc) else LASSERT_TRAP_PC in
    let new_err  := if check_ok then s.(vm_err) else true in
    vm_step s (instr_lassert freg creg kind flen cost)
      {| vm_graph := s.(vm_graph);
         vm_csrs := if check_ok then s.(vm_csrs) else csr_set_err s.(vm_csrs) 1;
         vm_regs := s.(vm_regs);
         vm_mem := s.(vm_mem);
         vm_pc := new_pc;
         vm_mu := apply_cost s (instr_lassert freg creg kind flen cost);
         vm_mu_tensor := s.(vm_mu_tensor);
         vm_err := new_err;
         vm_logic_acc := s.(vm_logic_acc);
         vm_mstatus := s.(vm_mstatus);
         vm_witness := s.(vm_witness);
         vm_certified := s.(vm_certified) |}
(** step_ljoin: Reserve the cost of joining two certificates.
    The step does not compare certificate strings or touch CSR state. It
    advances and charges S mu_delta. *)
| step_ljoin : forall s c1reg c2reg cost,
    vm_step s (instr_ljoin c1reg c2reg cost)
      (advance_state s (instr_ljoin c1reg c2reg cost)
        s.(vm_graph) s.(vm_csrs) s.(vm_err))
(** step_mdlacc: Module discovery accumulator. Charges μ for looking up a module.
    No graph change. It advances PC and pays the cost. *)
| step_mdlacc : forall s module cost,
    vm_step s (instr_mdlacc module cost)
      (advance_state s (instr_mdlacc module cost) s.(vm_graph) s.(vm_csrs) s.(vm_err))
(** step_emit: Emit a payload outside the Coq state.
    The module ID and payload are accepted parameters, but this transition does
    not mutate graph, registers, memory, or CSR state. It advances PC and charges
    payload_bit_length payload + S cost. *)
| step_emit : forall s module payload cost,
    vm_step s (instr_emit module payload cost)
      (advance_state s (instr_emit module payload cost)
        s.(vm_graph) s.(vm_csrs) s.(vm_err))
(** step_reveal: Reveal bits of information and charge the μ-tensor.
    The critical difference from advance_state: it increments vm_mu_tensor at
    flat index (module mod 16), recording WHERE the revelation cost was charged.
    The certificate string is not checked in this relation; `bits` is the tensor delta. *)
| step_reveal : forall s module bits cert cost,
    vm_step s (instr_reveal module bits cert cost)
      (advance_state_reveal s (instr_reveal module bits cert cost) (module mod 16) bits
        s.(vm_graph) s.(vm_csrs) s.(vm_err))
(** step_pdiscover: Hardware-aligned PDISCOVER is pure advance.
    The evidence payload is present in the instruction, but this relation does
    not attach axioms or mutate the graph. It advances PC and charges cost. *)
| step_pdiscover : forall s module evidence cost,
    vm_step s (instr_pdiscover module evidence cost)
      (advance_state s (instr_pdiscover module evidence cost)
        s.(vm_graph) s.(vm_csrs) s.(vm_err))
(** step_chsh_trial_ok: Record a valid CHSH trial.
    x, y ∈ {0,1} are measurement settings; a, b ∈ {0,1} are outcomes.
    wc' is the updated WitnessCounts with the appropriate bucket incremented.
    The CHSH inequality is NOT checked here. That's for CHSHStatisticalBridge.v.
    This step records the trial into the unforgeable witness counters.
    μ-cost is charged. Cost can be 0 for CHSH trials because they are not cert-setters. *)
| step_chsh_trial_ok : forall s x y a b cost wc',
    chsh_bits_ok x y a b = true ->
    wc' = record_trial s.(vm_witness) x y a b ->
    vm_step s (instr_chsh_trial x y a b cost)
      ({| vm_graph := s.(vm_graph);
          vm_csrs := s.(vm_csrs);
          vm_regs := s.(vm_regs);
          vm_mem := s.(vm_mem);
          vm_pc := S s.(vm_pc);
          vm_mu := apply_cost s (instr_chsh_trial x y a b cost);
          vm_mu_tensor := s.(vm_mu_tensor);
          vm_err := s.(vm_err);
          vm_logic_acc := s.(vm_logic_acc);
          vm_mstatus := s.(vm_mstatus);
          vm_witness := wc';
          vm_certified := s.(vm_certified) |})
(** step_chsh_trial_badbits: Protocol violation. At least one of x,y,a,b is not
    in {0,1}. No trial is recorded. Error flag latches. Cost still charged. *)
| step_chsh_trial_badbits : forall s x y a b cost,
    chsh_bits_ok x y a b = false ->
    vm_step s (instr_chsh_trial x y a b cost)
      (advance_state s (instr_chsh_trial x y a b cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
(** step_xfer: Copy register src to register dst. word64 truncation on write. *)
| step_xfer : forall s dst src cost regs',
    regs' = write_reg s dst (read_reg s src) ->
    vm_step s (instr_xfer dst src cost)
      (advance_state_rm s (instr_xfer dst src cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
(** ---------------------------------------------------------------
    General-purpose compute: the compiler targets these.
    No graph changes, no cert state changes. Just registers and memory.
    --------------------------------------------------------------- *)
(** step_load_imm: Put imm (truncated to 64 bits) into dst. *)
| step_load_imm : forall s dst imm cost regs',
    regs' = write_reg s dst (word64 imm) ->
    vm_step s (instr_load_imm dst imm cost)
      (advance_state_rm s (instr_load_imm dst imm cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
(** step_load: Register-indirect load. addr = regs[rs_addr], then dst = mem[addr]. *)
| step_load : forall s dst rs_addr cost regs' value addr,
    addr = read_reg s rs_addr ->
    value = read_mem s addr ->
    regs' = write_reg s dst value ->
    vm_step s (instr_load dst rs_addr cost)
      (advance_state_rm s (instr_load dst rs_addr cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
(** step_store: Register-indirect store. addr = regs[rs_addr], mem[addr] = regs[src]. *)
| step_store : forall s rs_addr src cost mem' value addr,
    addr = read_reg s rs_addr ->
    value = read_reg s src ->
    mem' = write_mem s addr value ->
    vm_step s (instr_store rs_addr src cost)
      (advance_state_rm s (instr_store rs_addr src cost)
        s.(vm_graph) s.(vm_csrs) s.(vm_regs) mem' s.(vm_err))
(** step_add: Modular 64-bit addition. dst = (rs1 + rs2) mod 2^64. *)
| step_add : forall s dst rs1 rs2 cost regs' v1 v2,
    v1 = read_reg s rs1 ->
    v2 = read_reg s rs2 ->
    regs' = write_reg s dst (word64_add v1 v2) ->
    vm_step s (instr_add dst rs1 rs2 cost)
      (advance_state_rm s (instr_add dst rs1 rs2 cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
(** step_sub: Modular 64-bit subtraction. dst = (rs1 - rs2) mod 2^64. *)
| step_sub : forall s dst rs1 rs2 cost regs' v1 v2,
    v1 = read_reg s rs1 ->
    v2 = read_reg s rs2 ->
    regs' = write_reg s dst (word64_sub v1 v2) ->
    vm_step s (instr_sub dst rs1 rs2 cost)
      (advance_state_rm s (instr_sub dst rs1 rs2 cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
(** step_jump: Unconditional branch to target. μ-cost still charged. *)
| step_jump : forall s target cost,
    vm_step s (instr_jump target cost)
      (jump_state s (instr_jump target cost) target)
(** step_jnez_taken: Branch taken. rs is nonzero, PC jumps to target. *)
| step_jnez_taken : forall s rs target cost,
    read_reg s rs <> 0 ->
    vm_step s (instr_jnez rs target cost)
      (jump_state s (instr_jnez rs target cost) target)
(** step_jnez_not_taken: Branch not taken. rs is zero, PC advances by 1. *)
| step_jnez_not_taken : forall s rs target cost,
    read_reg s rs = 0 ->
    vm_step s (instr_jnez rs target cost)
      (advance_state s (instr_jnez rs target cost)
        s.(vm_graph) s.(vm_csrs) s.(vm_err))
(** CALL: push return address to stack (r15 = SP, ascending) then jump.
    Stack convention: r15 = REG_COUNT - 1 is SP; mem[SP] = return addr; SP = SP + 1. *)
| step_call : forall s target cost sp ret_addr mem' regs',
    sp = read_reg s 15 ->
    ret_addr = S s.(vm_pc) ->
    mem' = write_mem s sp ret_addr ->
    regs' = write_reg s 15 (word64_add sp 1) ->
    vm_step s (instr_call target cost)
      (jump_state_rm s (instr_call target cost) target regs' mem')
(** RET: pop return address from stack; SP = SP - 1; PC = mem[SP]. *)
| step_ret : forall s cost sp ret_pc regs',
    sp = word64_sub (read_reg s 15) 1 ->
    ret_pc = read_mem s sp ->
    regs' = write_reg s 15 sp ->
    vm_step s (instr_ret cost)
      (jump_state_rm s (instr_ret cost) ret_pc regs' s.(vm_mem))
(** ---------------------------------------------------------------
    GF(2) / bit-linear operations.
    XOR_ADD and XOR_SWAP are reversible; XOR_LOAD and XOR_RANK overwrite dst.
    --------------------------------------------------------------- *)
(** step_xor_load: Load from absolute address `addr` (not register-indirect).
    Despite the XOR name, this is just a plain load. No XOR involved. *)
| step_xor_load : forall s dst addr cost regs' value,
    value = read_mem s addr ->
    regs' = write_reg s dst value ->
    vm_step s (instr_xor_load dst addr cost)
      (advance_state_rm s (instr_xor_load dst addr cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
(** step_xor_add: dst = dst XOR src. Reversible: applying again restores dst. *)
| step_xor_add : forall s dst src cost regs' vdst vsrc,
    vdst = read_reg s dst ->
    vsrc = read_reg s src ->
    regs' = write_reg s dst (word64_xor vdst vsrc) ->
    vm_step s (instr_xor_add dst src cost)
      (advance_state_rm s (instr_xor_add dst src cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
(** step_xor_swap: Swap registers a and b. Uses swap_regs which does two
    in-place writes. Reversible. *)
| step_xor_swap : forall s a b cost regs',
    regs' = swap_regs s.(vm_regs) a b ->
    vm_step s (instr_xor_swap a b cost)
      (advance_state_rm s (instr_xor_swap a b cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
(** step_xor_rank: Population count (Hamming weight) of src. dst = popcount(src).
    Counts the number of 1-bits in the 64-bit value. *)
| step_xor_rank : forall s dst src cost regs' vsrc,
    vsrc = read_reg s src ->
    regs' = write_reg s dst (word64_popcount vsrc) ->
    vm_step s (instr_xor_rank dst src cost)
      (advance_state_rm s (instr_xor_rank dst src cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
(** step_checkpoint: Record an execution label. No graph or register changes.
    Advances PC, charges mu_delta. The label string is accepted but not stored
    in Coq state. The extraction layer handles it. *)
| step_checkpoint : forall s label cost,
    vm_step s (instr_checkpoint label cost)
      (advance_state s (instr_checkpoint label cost)
        s.(vm_graph) s.(vm_csrs) s.(vm_err))
(** step_read_port: Read `value` from external channel `channel_idx` into dst.
    The value is part of the instruction, so execution is deterministic
    given the instruction stream.
    Cost: bits + S mu_delta. Cert-setter, always ≥ 1 regardless of mu_delta. *)
| step_read_port : forall s dst channel_idx value bits cost regs',
    regs' = write_reg s dst value ->
    vm_step s (instr_read_port dst channel_idx value bits cost)
      (advance_state_rm s (instr_read_port dst channel_idx value bits cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
(** step_write_port: Send regs[src] to channel channel_idx. No register change,
    no graph change. Cost: mu_delta (not a cert-setter). *)
| step_write_port : forall s channel_idx src cost,
    vm_step s (instr_write_port channel_idx src cost)
      (advance_state s (instr_write_port channel_idx src cost)
        s.(vm_graph) s.(vm_csrs) s.(vm_err))
(** step_heap_load: Load from (csr_heap_base + addr) into dst.
    Heap-relative addressing: addr = regs[rs_addr], actual address = heap_base + addr.
    This avoids conflating raw memory addresses with heap-allocated offsets. *)
| step_heap_load : forall s dst rs_addr cost regs' value addr,
    addr = read_reg s rs_addr ->
    value = read_mem s (s.(vm_csrs).(csr_heap_base) + addr) ->
    regs' = write_reg s dst value ->
    vm_step s (instr_heap_load dst rs_addr cost)
      (advance_state_rm s (instr_heap_load dst rs_addr cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
(** step_heap_store: Store regs[src] to (csr_heap_base + addr). Same heap-relative
    addressing as heap_load. addr = regs[rs_addr], actual = heap_base + addr. *)
| step_heap_store : forall s rs_addr src cost mem' value addr,
    addr = read_reg s rs_addr ->
    value = read_reg s src ->
    mem' = write_mem s (s.(vm_csrs).(csr_heap_base) + addr) value ->
    vm_step s (instr_heap_store rs_addr src cost)
      (advance_state_rm s (instr_heap_store rs_addr src cost)
        s.(vm_graph) s.(vm_csrs) s.(vm_regs) mem' s.(vm_err))
(** ---------------------------------------------------------------
    Extended ALU: AND/OR/SHL/SHR/MUL/LUI/HALT. All 64-bit modular.
    No graph changes. No cert state changes. Just registers.
    --------------------------------------------------------------- *)
(** step_and: Bitwise AND. dst = rs1 AND rs2, then word64 keeps it in range. *)
| step_and : forall s dst rs1 rs2 cost regs' v1 v2,
    v1 = read_reg s rs1 ->
    v2 = read_reg s rs2 ->
    regs' = write_reg s dst (word64_and v1 v2) ->
    vm_step s (instr_and dst rs1 rs2 cost)
      (advance_state_rm s (instr_and dst rs1 rs2 cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
(** step_or: Bitwise OR. Same register-only shape as step_and. *)
| step_or : forall s dst rs1 rs2 cost regs' v1 v2,
    v1 = read_reg s rs1 ->
    v2 = read_reg s rs2 ->
    regs' = write_reg s dst (word64_or v1 v2) ->
    vm_step s (instr_or dst rs1 rs2 cost)
      (advance_state_rm s (instr_or dst rs1 rs2 cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
(** step_shl: 64-bit left shift. dst = rs1 << rs2 under word64_shl. *)
| step_shl : forall s dst rs1 rs2 cost regs' v1 v2,
    v1 = read_reg s rs1 ->
    v2 = read_reg s rs2 ->
    regs' = write_reg s dst (word64_shl v1 v2) ->
    vm_step s (instr_shl dst rs1 rs2 cost)
      (advance_state_rm s (instr_shl dst rs1 rs2 cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
(** step_shr: 64-bit right shift. dst = rs1 >> rs2 under word64_shr. *)
| step_shr : forall s dst rs1 rs2 cost regs' v1 v2,
    v1 = read_reg s rs1 ->
    v2 = read_reg s rs2 ->
    regs' = write_reg s dst (word64_shr v1 v2) ->
    vm_step s (instr_shr dst rs1 rs2 cost)
      (advance_state_rm s (instr_shr dst rs1 rs2 cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
(** step_mul: 64-bit modular multiplication. dst = rs1 * rs2 under word64_mul. *)
| step_mul : forall s dst rs1 rs2 cost regs' v1 v2,
    v1 = read_reg s rs1 ->
    v2 = read_reg s rs2 ->
    regs' = write_reg s dst (word64_mul v1 v2) ->
    vm_step s (instr_mul dst rs1 rs2 cost)
      (advance_state_rm s (instr_mul dst rs1 rs2 cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
(** step_lui: Load upper immediate. dst = imm << 8. Same shift-and-load pattern
    as RISC-V LUI, but the shift amount is 8 (not 12). *)
| step_lui : forall s dst imm cost regs',
    regs' = write_reg s dst (word64_shl imm 8) ->
    vm_step s (instr_lui dst imm cost)
      (advance_state_rm s (instr_lui dst imm cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
(** step_halt: Stop execution. PC advances past HALT (so vm_pc is well-defined
    after halt), μ-cost is charged, nothing else changes. *)
| step_halt : forall s cost,
    vm_step s (instr_halt cost)
      (advance_state s (instr_halt cost)
        s.(vm_graph) s.(vm_csrs) s.(vm_err))
(** step_certify: State-based certification with structurally positive cost.
    Cost is S mu_delta (at least 1), making "certified => mu > 0" provable. *)
| step_certify : forall s mu_delta,
    vm_step s (instr_certify mu_delta)
      ({| vm_graph := s.(vm_graph);
          vm_csrs := s.(vm_csrs);
          vm_regs := s.(vm_regs);
          vm_mem := s.(vm_mem);
          vm_pc := S s.(vm_pc);
          vm_mu := s.(vm_mu) + S mu_delta;
          vm_mu_tensor := s.(vm_mu_tensor);
          vm_err := s.(vm_err);
          vm_logic_acc := s.(vm_logic_acc);
          vm_mstatus := s.(vm_mstatus);
          vm_witness := s.(vm_witness);
          vm_certified := true |})
(** Per-module tensor instructions.
    TENSOR_SET writes a value to the per-module 4×4 metric tensor at (i,j).
    TENSOR_GET reads the per-module tensor entry at (i,j) into a register.
    Invalid indices take the same latched-error path as the extracted VM. *)
(** step_tensor_set_ok: Valid 4×4 tensor index. Mutate the module tensor entry. *)
| step_tensor_set_ok : forall s mid i j value cost,
    tensor_indices_ok i j = true ->
    vm_step s (instr_tensor_set mid i j value cost)
      (advance_state s (instr_tensor_set mid i j value cost)
        (graph_update_module_tensor s.(vm_graph) mid (i * 4 + j) value)
        s.(vm_csrs) s.(vm_err))
(** step_tensor_set_bad: Invalid tensor index. Leave the graph alone and latch error. *)
| step_tensor_set_bad : forall s mid i j value cost,
    tensor_indices_ok i j = false ->
    vm_step s (instr_tensor_set mid i j value cost)
      (advance_state s (instr_tensor_set mid i j value cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
(** step_tensor_get_ok: Valid 4×4 tensor index. Read the module tensor into dst. *)
| step_tensor_get_ok : forall s dst mid i j cost regs',
    tensor_indices_ok i j = true ->
    regs' = write_reg s dst (module_tensor_entry s mid i j) ->
    vm_step s (instr_tensor_get dst mid i j cost)
      (advance_state_rm s (instr_tensor_get dst mid i j cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
(** step_tensor_get_bad: Invalid tensor index. No read happens; error latches. *)
| step_tensor_get_bad : forall s dst mid i j cost,
    tensor_indices_ok i j = false ->
    vm_step s (instr_tensor_get dst mid i j cost)
      (advance_state s (instr_tensor_get dst mid i j cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
(** ---------------------------------------------------------------
    Categorical morphism instructions: rich-state semantics

    These instructions manipulate the PartitionGraph's morphism table.
    Each has an _ok constructor (precondition satisfied, operation succeeds)
    and a _bad constructor (precondition fails, error latches).

    The _ok cases return a morph_id in a register (for MORPH, COMPOSE,
    MORPH_ID, MORPH_TENSOR, MORPH_GET) or just advance state (MORPH_DELETE,
    MORPH_ASSERT). All charge μ-cost regardless of outcome.

    The category laws are proved in CategoryLaws.v and CategoryBridge.v.
    --------------------------------------------------------------- *)
(** step_morph_ok: Both modules exist. Add a morphism and return its ID in dst. *)
| step_morph_ok : forall s dst src_mod dst_mod coupling_idx cost src_ms dst_ms graph' morph_id,
    graph_lookup s.(vm_graph) src_mod = Some src_ms ->
    graph_lookup s.(vm_graph) dst_mod = Some dst_ms ->
    (graph', morph_id) = graph_add_morphism s.(vm_graph) src_mod dst_mod
      (load_coupling_from_mem s src_ms.(module_region) dst_ms.(module_region) coupling_idx)
      false ->
    vm_step s (instr_morph dst src_mod dst_mod coupling_idx cost)
      (advance_state_rm s (instr_morph dst src_mod dst_mod coupling_idx cost)
        graph' s.(vm_csrs) (write_reg s dst morph_id) s.(vm_mem) s.(vm_err))
(** step_morph_bad_src: Source module missing. No graph mutation; error latches. *)
| step_morph_bad_src : forall s dst src_mod dst_mod coupling_idx cost,
    graph_lookup s.(vm_graph) src_mod = None ->
    vm_step s (instr_morph dst src_mod dst_mod coupling_idx cost)
      (advance_state s (instr_morph dst src_mod dst_mod coupling_idx cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
(** step_morph_bad_dst: Destination module missing. Source exists, so this is the
    exact other failure branch for MORPH. *)
| step_morph_bad_dst : forall s dst src_mod dst_mod coupling_idx cost src_ms,
    graph_lookup s.(vm_graph) src_mod = Some src_ms ->
    graph_lookup s.(vm_graph) dst_mod = None ->
    vm_step s (instr_morph dst src_mod dst_mod coupling_idx cost)
      (advance_state s (instr_morph dst src_mod dst_mod coupling_idx cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
(** step_compose_ok: Composition exists. Store the composed morphism ID in dst. *)
| step_compose_ok : forall s dst m1_id m2_id cost graph' morph_id,
    graph_compose_morphisms s.(vm_graph) m1_id m2_id = Some (graph', morph_id) ->
    vm_step s (instr_compose dst m1_id m2_id cost)
      (advance_state_rm s (instr_compose dst m1_id m2_id cost)
        graph' s.(vm_csrs) (write_reg s dst morph_id) s.(vm_mem) s.(vm_err))
(** step_compose_bad: Composition is undefined. Leave graph/registers alone and latch error. *)
| step_compose_bad : forall s dst m1_id m2_id cost,
    graph_compose_morphisms s.(vm_graph) m1_id m2_id = None ->
    vm_step s (instr_compose dst m1_id m2_id cost)
      (advance_state s (instr_compose dst m1_id m2_id cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
(** step_morph_id_ok: Build the identity morphism for an existing module. *)
| step_morph_id_ok : forall s dst module cost graph' morph_id,
    graph_add_identity s.(vm_graph) module = Some (graph', morph_id) ->
    vm_step s (instr_morph_id dst module cost)
      (advance_state_rm s (instr_morph_id dst module cost)
        graph' s.(vm_csrs) (write_reg s dst morph_id) s.(vm_mem) s.(vm_err))
(** step_morph_id_bad: No identity morphism exists for that module, so error latches. *)
| step_morph_id_bad : forall s dst module cost,
    graph_add_identity s.(vm_graph) module = None ->
    vm_step s (instr_morph_id dst module cost)
      (advance_state s (instr_morph_id dst module cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
(** step_morph_delete_ok: Delete an existing morphism from the graph. *)
| step_morph_delete_ok : forall s morph_id cost graph',
    graph_delete_morphism s.(vm_graph) morph_id = Some graph' ->
    vm_step s (instr_morph_delete morph_id cost)
      (advance_state s (instr_morph_delete morph_id cost)
        graph' s.(vm_csrs) s.(vm_err))
(** step_morph_delete_bad: Asked to delete a missing morphism. State stays put, error latches. *)
| step_morph_delete_bad : forall s morph_id cost,
    graph_delete_morphism s.(vm_graph) morph_id = None ->
    vm_step s (instr_morph_delete morph_id cost)
      (advance_state s (instr_morph_delete morph_id cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
(** step_morph_assert_ok: The morphism exists. Mark the property by writing its
    checksum into csr_cert_addr. This is why MORPH_ASSERT is a cert-setter. *)
| step_morph_assert_ok : forall s morph_id property cert cost ms,
    graph_lookup_morphism s.(vm_graph) morph_id = Some ms ->
    vm_step s (instr_morph_assert morph_id property cert cost)
      (advance_state s (instr_morph_assert morph_id property cert cost)
        s.(vm_graph) (csr_set_cert_addr s.(vm_csrs) (ascii_checksum property)) s.(vm_err))
(** step_morph_assert_bad: Missing morphism. No certificate address is set; error latches. *)
| step_morph_assert_bad : forall s morph_id property cert cost,
    graph_lookup_morphism s.(vm_graph) morph_id = None ->
    vm_step s (instr_morph_assert morph_id property cert cost)
      (advance_state s (instr_morph_assert morph_id property cert cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
(** step_morph_tensor_ok: Tensor two morphisms and return the new morphism ID in dst. *)
| step_morph_tensor_ok : forall s dst f_id g_id cost graph' morph_id,
    graph_tensor_morphisms s.(vm_graph) f_id g_id = Some (graph', morph_id) ->
    vm_step s (instr_morph_tensor dst f_id g_id cost)
      (advance_state_rm s (instr_morph_tensor dst f_id g_id cost)
        graph' s.(vm_csrs) (write_reg s dst morph_id) s.(vm_mem) s.(vm_err))
(** step_morph_tensor_bad: Tensor product is undefined. Leave graph/registers alone and latch error. *)
| step_morph_tensor_bad : forall s dst f_id g_id cost,
    graph_tensor_morphisms s.(vm_graph) f_id g_id = None ->
    vm_step s (instr_morph_tensor dst f_id g_id cost)
      (advance_state s (instr_morph_tensor dst f_id g_id cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
(** step_morph_get_ok: Read one field out of a morphism into dst. Selector 0/1/2/3
    maps to source/target/coupling-count/is-identity; anything else returns 0. *)
| step_morph_get_ok : forall s dst morph_id selector cost ms regs',
    graph_lookup_morphism s.(vm_graph) morph_id = Some ms ->
    regs' = write_reg s dst (morphism_selector_value ms selector) ->
    vm_step s (instr_morph_get dst morph_id selector cost)
      (advance_state_rm s (instr_morph_get dst morph_id selector cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
(** step_morph_get_bad: Missing morphism. No register write; error latches. *)
| step_morph_get_bad : forall s dst morph_id selector cost,
    graph_lookup_morphism s.(vm_graph) morph_id = None ->
    vm_step s (instr_morph_get dst morph_id selector cost)
      (advance_state s (instr_morph_get dst morph_id selector cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
(** step_chsh_lassert_ok: CHSH-aware certification succeeds.
    Inspects the WitnessCounts buckets and decides
    [column_contractive_check_witness] in pure Z arithmetic. If the check
    passes, advances PC normally; csr_cert_addr is left intact (the
    cert-channel theory in RevelationRequirement.v treats MORPH_ASSERT as
    the sole cert_addr writer; CHSH_LASSERT signals its success via PC
    advance + vm_err staying false, which is exactly the same trap discipline
    LASSERT uses). μ-cost is [S mu_delta] regardless of outcome (cert-setter
    discipline). The bridge theorems
    [MuLedgerQuantumBridge.chsh_lassert_no_trap_implies_state_column_contractive]
    and [QuantumPartitionPSD.chsh_lassert_no_trap_implies_npa_psd] operate on
    this observable signature. *)
| step_chsh_lassert_ok : forall s mu_delta,
    column_contractive_check_witness s.(vm_witness) = true ->
    vm_step s (instr_chsh_lassert mu_delta)
      {| vm_graph := s.(vm_graph);
         vm_csrs := s.(vm_csrs);
         vm_regs := s.(vm_regs);
         vm_mem := s.(vm_mem);
         vm_pc := S s.(vm_pc);
         vm_mu := apply_cost s (instr_chsh_lassert mu_delta);
         vm_mu_tensor := s.(vm_mu_tensor);
         vm_err := s.(vm_err);
         vm_logic_acc := s.(vm_logic_acc);
         vm_mstatus := s.(vm_mstatus);
         vm_witness := s.(vm_witness);
         vm_certified := s.(vm_certified) |}
(** step_chsh_lassert_bad: CHSH-aware certification fails. The witness
    counters do not satisfy column-contractivity. Trap to LASSERT_TRAP_PC,
    latch vm_err. μ-cost is charged regardless (you pay to check, even to
    fail).
*)
| step_chsh_lassert_bad : forall s mu_delta,
    column_contractive_check_witness s.(vm_witness) = false ->
    vm_step s (instr_chsh_lassert mu_delta)
      {| vm_graph := s.(vm_graph);
         vm_csrs := csr_set_err s.(vm_csrs) 1;
         vm_regs := s.(vm_regs);
         vm_mem := s.(vm_mem);
         vm_pc := LASSERT_TRAP_PC;
         vm_mu := apply_cost s (instr_chsh_lassert mu_delta);
         vm_mu_tensor := s.(vm_mu_tensor);
         vm_err := true;
         vm_logic_acc := s.(vm_logic_acc);
         vm_mstatus := s.(vm_mstatus);
         vm_witness := s.(vm_witness);
         vm_certified := s.(vm_certified) |}
(** step_chsh_lassert_1ab_ok: Q_{1+AB}-aware certification succeeds.
    Runs [column_contractive_check_q1ab_kernel] which combines the Q_1
    check with the integer sum-of-squares condition on the four CHSH
    correlators. On pass: advance PC, leave cert state intact, leave
    vm_err intact. Cost is S mu_delta. *)
| step_chsh_lassert_1ab_ok : forall s mu_delta,
    column_contractive_check_q1ab_kernel s.(vm_witness) = true ->
    vm_step s (instr_chsh_lassert_1ab mu_delta)
      {| vm_graph := s.(vm_graph);
         vm_csrs := s.(vm_csrs);
         vm_regs := s.(vm_regs);
         vm_mem := s.(vm_mem);
         vm_pc := S s.(vm_pc);
         vm_mu := apply_cost s (instr_chsh_lassert_1ab mu_delta);
         vm_mu_tensor := s.(vm_mu_tensor);
         vm_err := s.(vm_err);
         vm_logic_acc := s.(vm_logic_acc);
         vm_mstatus := s.(vm_mstatus);
         vm_witness := s.(vm_witness);
         vm_certified := s.(vm_certified) |}
(** step_chsh_lassert_1ab_bad: Q_{1+AB} check fails. Trap to
    LASSERT_TRAP_PC, latch vm_err. Cost is charged regardless. *)
| step_chsh_lassert_1ab_bad : forall s mu_delta,
    column_contractive_check_q1ab_kernel s.(vm_witness) = false ->
    vm_step s (instr_chsh_lassert_1ab mu_delta)
      {| vm_graph := s.(vm_graph);
         vm_csrs := csr_set_err s.(vm_csrs) 1;
         vm_regs := s.(vm_regs);
         vm_mem := s.(vm_mem);
         vm_pc := LASSERT_TRAP_PC;
         vm_mu := apply_cost s (instr_chsh_lassert_1ab mu_delta);
         vm_mu_tensor := s.(vm_mu_tensor);
         vm_err := true;
         vm_logic_acc := s.(vm_logic_acc);
         vm_mstatus := s.(vm_mstatus);
         vm_witness := s.(vm_witness);
         vm_certified := s.(vm_certified) |}
(** step_chsh_lassert_1ab_g5_ok: Q_{1+AB}-aware γ_5 certification succeeds.
    Runs [q1ab_g5_full_integer_check_kernel] which combines the Q_1
    column-contractive check on the four CHSH correlators with the γ_5
    SOS witness inequality. On pass: advance PC, leave cert state intact,
    leave vm_err intact. Cost is S mu_delta. *)
| step_chsh_lassert_1ab_g5_ok : forall s mu_delta same_g5 diff_g5,
    q1ab_g5_full_integer_check_kernel s.(vm_witness) same_g5 diff_g5 = true ->
    vm_step s (instr_chsh_lassert_1ab_g5 mu_delta same_g5 diff_g5)
      {| vm_graph := s.(vm_graph);
         vm_csrs := s.(vm_csrs);
         vm_regs := s.(vm_regs);
         vm_mem := s.(vm_mem);
         vm_pc := S s.(vm_pc);
         vm_mu := apply_cost s (instr_chsh_lassert_1ab_g5 mu_delta same_g5 diff_g5);
         vm_mu_tensor := s.(vm_mu_tensor);
         vm_err := s.(vm_err);
         vm_logic_acc := s.(vm_logic_acc);
         vm_mstatus := s.(vm_mstatus);
         vm_witness := s.(vm_witness);
         vm_certified := s.(vm_certified) |}
(** step_chsh_lassert_1ab_g5_bad: Q_{1+AB}-aware γ_5 check fails. Trap
    to LASSERT_TRAP_PC, latch vm_err. Cost is charged regardless. *)
| step_chsh_lassert_1ab_g5_bad : forall s mu_delta same_g5 diff_g5,
    q1ab_g5_full_integer_check_kernel s.(vm_witness) same_g5 diff_g5 = false ->
    vm_step s (instr_chsh_lassert_1ab_g5 mu_delta same_g5 diff_g5)
      {| vm_graph := s.(vm_graph);
         vm_csrs := csr_set_err s.(vm_csrs) 1;
         vm_regs := s.(vm_regs);
         vm_mem := s.(vm_mem);
         vm_pc := LASSERT_TRAP_PC;
         vm_mu := apply_cost s (instr_chsh_lassert_1ab_g5 mu_delta same_g5 diff_g5);
         vm_mu_tensor := s.(vm_mu_tensor);
         vm_err := true;
         vm_logic_acc := s.(vm_logic_acc);
         vm_mstatus := s.(vm_mstatus);
         vm_witness := s.(vm_witness);
         vm_certified := s.(vm_certified) |}
(** step_chsh_lassert_1ab_g345_ok: Q_{1+AB}-aware γ_{3,4,5} certification
    succeeds. Runs [q1ab_g345_full_integer_check_kernel] which combines
    the Q_1 column-contractive check on the four CHSH correlators with
    the four leading principal minors of H_{γ_345} all > 0 (Sylvester PD
    on the 4×4 difference matrix). On pass: advance PC, leave cert state
    intact, leave vm_err intact. Cost is S mu_delta. *)
| step_chsh_lassert_1ab_g345_ok :
    forall s mu_delta same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5,
    q1ab_g345_full_integer_check_kernel s.(vm_witness)
      same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 = true ->
    vm_step s (instr_chsh_lassert_1ab_g345 mu_delta
                 same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5)
      {| vm_graph := s.(vm_graph);
         vm_csrs := s.(vm_csrs);
         vm_regs := s.(vm_regs);
         vm_mem := s.(vm_mem);
         vm_pc := S s.(vm_pc);
         vm_mu := apply_cost s (instr_chsh_lassert_1ab_g345 mu_delta
                                  same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5);
         vm_mu_tensor := s.(vm_mu_tensor);
         vm_err := s.(vm_err);
         vm_logic_acc := s.(vm_logic_acc);
         vm_mstatus := s.(vm_mstatus);
         vm_witness := s.(vm_witness);
         vm_certified := s.(vm_certified) |}
(** step_chsh_lassert_1ab_g345_bad: Q_{1+AB}-aware γ_{3,4,5} check fails.
    Trap to LASSERT_TRAP_PC, latch vm_err. Cost is charged regardless. *)
| step_chsh_lassert_1ab_g345_bad :
    forall s mu_delta same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5,
    q1ab_g345_full_integer_check_kernel s.(vm_witness)
      same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 = false ->
    vm_step s (instr_chsh_lassert_1ab_g345 mu_delta
                 same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5)
      {| vm_graph := s.(vm_graph);
         vm_csrs := csr_set_err s.(vm_csrs) 1;
         vm_regs := s.(vm_regs);
         vm_mem := s.(vm_mem);
         vm_pc := LASSERT_TRAP_PC;
         vm_mu := apply_cost s (instr_chsh_lassert_1ab_g345 mu_delta
                                  same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5);
         vm_mu_tensor := s.(vm_mu_tensor);
         vm_err := true;
         vm_logic_acc := s.(vm_logic_acc);
         vm_mstatus := s.(vm_mstatus);
         vm_witness := s.(vm_witness);
         vm_certified := s.(vm_certified) |}
(** step_chsh_lassert_1ab_g12345_ok: full Q_{1+AB} γ_{1..5}-aware check passes.
    Runs [q1ab_g12345_full_integer_check_kernel] on the witness counters
    plus the five γ-bucket pairs (the column-contractive check on the
    four CHSH correlators AND the six Schur-cascade PD checks on the
    cleared 6×6 → 5×5 → 4×4 matrix). On pass: advance PC, leave cert
    state intact, leave vm_err intact. Cost is S mu_delta. *)
| step_chsh_lassert_1ab_g12345_ok :
    forall s mu_delta same_g1 diff_g1 same_g2 diff_g2
                       same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5,
    q1ab_g12345_full_integer_check_kernel s.(vm_witness)
      same_g1 diff_g1 same_g2 diff_g2
      same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 = true ->
    vm_step s (instr_chsh_lassert_1ab_g12345 mu_delta
                 same_g1 diff_g1 same_g2 diff_g2
                 same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5)
      {| vm_graph := s.(vm_graph);
         vm_csrs := s.(vm_csrs);
         vm_regs := s.(vm_regs);
         vm_mem := s.(vm_mem);
         vm_pc := S s.(vm_pc);
         vm_mu := apply_cost s (instr_chsh_lassert_1ab_g12345 mu_delta
                                  same_g1 diff_g1 same_g2 diff_g2
                                  same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5);
         vm_mu_tensor := s.(vm_mu_tensor);
         vm_err := s.(vm_err);
         vm_logic_acc := s.(vm_logic_acc);
         vm_mstatus := s.(vm_mstatus);
         vm_witness := s.(vm_witness);
         vm_certified := s.(vm_certified) |}
(** step_chsh_lassert_1ab_g12345_bad: full Q_{1+AB} γ_{1..5}-aware check
    fails. Trap to LASSERT_TRAP_PC, latch vm_err. Cost is charged regardless. *)
| step_chsh_lassert_1ab_g12345_bad :
    forall s mu_delta same_g1 diff_g1 same_g2 diff_g2
                       same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5,
    q1ab_g12345_full_integer_check_kernel s.(vm_witness)
      same_g1 diff_g1 same_g2 diff_g2
      same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 = false ->
    vm_step s (instr_chsh_lassert_1ab_g12345 mu_delta
                 same_g1 diff_g1 same_g2 diff_g2
                 same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5)
      {| vm_graph := s.(vm_graph);
         vm_csrs := csr_set_err s.(vm_csrs) 1;
         vm_regs := s.(vm_regs);
         vm_mem := s.(vm_mem);
         vm_pc := LASSERT_TRAP_PC;
         vm_mu := apply_cost s (instr_chsh_lassert_1ab_g12345 mu_delta
                                  same_g1 diff_g1 same_g2 diff_g2
                                  same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5);
         vm_mu_tensor := s.(vm_mu_tensor);
         vm_err := true;
         vm_logic_acc := s.(vm_logic_acc);
         vm_mstatus := s.(vm_mstatus);
         vm_witness := s.(vm_witness);
         vm_certified := s.(vm_certified) |}.

(** ** What the partition operations leave alone

    PNEW, PSPLIT and PMERGE never change the module a lookup finds for an
    ID below [pg_next_id] that the instruction does not name. *)

Lemma graph_remove_or_keep_next_id : forall g victim,
  pg_next_id (match graph_remove g victim with Some (g', _) => g' | None => g end) =
  pg_next_id g.
Proof.
  intros g victim. unfold graph_remove.
  destruct (graph_remove_modules (pg_modules g) victim) as [[mods' r]|]; reflexivity.
Qed.

Lemma graph_remove_or_keep_lookup_other : forall g victim mid,
  mid <> victim ->
  graph_lookup (match graph_remove g victim with Some (g', _) => g' | None => g end) mid =
  graph_lookup g mid.
Proof.
  intros g victim mid Hne. unfold graph_remove, graph_lookup.
  destruct (graph_remove_modules (pg_modules g) victim) as [[mods' r]|] eqn:E; [|reflexivity].
  cbn [pg_modules]. exact (graph_remove_modules_lookup_other _ _ _ _ _ E Hne).
Qed.

(** graph_pnew never decreases pg_next_id. *)
Lemma graph_pnew_next_id_nondec :
  forall (g : PartitionGraph) (region : list nat),
    g.(pg_next_id) <= (fst (graph_pnew g region)).(pg_next_id).
Proof.
  intros g region. unfold graph_pnew.
  destruct (graph_find_region g (normalize_region region)); simpl; lia.
Qed.

(** graph_pnew keeps the lookup of every ID below pg_next_id. *)
Lemma graph_pnew_lookup_other :
  forall (g : PartitionGraph) (region : list nat) (mid : ModuleID),
    mid < g.(pg_next_id) ->
    graph_lookup (fst (graph_pnew g region)) mid = graph_lookup g mid.
Proof.
  intros g region mid Hlt. unfold graph_pnew.
  destruct (graph_find_region g (normalize_region region)); [reflexivity|].
  apply graph_add_module_lookup_other. exact Hlt.
Qed.

Lemma graph_hw_psplit_lookup_other : forall g victim mid,
  mid < pg_next_id g -> mid <> victim ->
  graph_lookup (graph_hw_psplit g victim) mid = graph_lookup g mid.
Proof.
  intros g victim mid Hlt Hne. unfold graph_hw_psplit.
  rewrite <- (graph_cascade_delete_morphisms_lookup g victim mid).
  set (g0 := graph_cascade_delete_morphisms g victim) in *.
  assert (Hn0 : pg_next_id g0 = pg_next_id g) by reflexivity.
  rewrite <- (graph_remove_or_keep_lookup_other g0 victim mid Hne).
  pose proof (graph_remove_or_keep_next_id g0 victim) as Hn.
  set (g1 := match graph_remove g0 victim with Some (g', _) => g' | None => g0 end) in *.
  destruct (graph_add_module g1 _ []) as [g2 id2] eqn:E2.
  destruct (graph_add_module g2 _ []) as [g3 id3] eqn:E3.
  change g3 with (fst (g3, id3)). rewrite <- E3.
  rewrite graph_add_module_lookup_other.
  - change g2 with (fst (g2, id2)). rewrite <- E2.
    apply graph_add_module_lookup_other. lia.
  - pose proof (f_equal (fun p => pg_next_id (fst p)) E2) as Ht.
    unfold graph_add_module in Ht. simpl in Ht. lia.
Qed.

Lemma graph_hw_pmerge_lookup_other : forall g m1 m2 mid,
  mid < pg_next_id g -> mid <> m1 -> mid <> m2 ->
  graph_lookup (graph_hw_pmerge g m1 m2) mid = graph_lookup g mid.
Proof.
  intros g m1 m2 mid Hlt Hne1 Hne2. unfold graph_hw_pmerge.
  rewrite <- (graph_cascade_delete_morphisms_lookup g m1 mid).
  rewrite <- (graph_cascade_delete_morphisms_lookup (graph_cascade_delete_morphisms g m1) m2 mid).
  set (g0 := graph_cascade_delete_morphisms (graph_cascade_delete_morphisms g m1) m2) in *.
  assert (Hn0 : pg_next_id g0 = pg_next_id g) by reflexivity.
  rewrite <- (graph_remove_or_keep_lookup_other g0 m1 mid Hne1).
  pose proof (graph_remove_or_keep_next_id g0 m1) as Hn1.
  set (g1 := match graph_remove g0 m1 with Some (g', _) => g' | None => g0 end) in *.
  rewrite <- (graph_remove_or_keep_lookup_other g1 m2 mid Hne2).
  pose proof (graph_remove_or_keep_next_id g1 m2) as Hn2.
  set (g2 := match graph_remove g1 m2 with Some (g', _) => g' | None => g1 end) in *.
  destruct (graph_add_module g2 _ []) as [g3 id3] eqn:E3.
  change g3 with (fst (g3, id3)). rewrite <- E3.
  apply graph_add_module_lookup_other. lia.
Qed.

(** ** The partition is a real partition of memory

    [regions_disjoint] (no address in two modules) and [regions_contiguous]
    (every region is a range) hold for a graph with no modules, and every
    [vm_step] keeps both. So every state reachable from a state with no
    modules has disjoint, contiguous module regions. *)

Definition partition_regions_ok (g : PartitionGraph) : Prop :=
  regions_disjoint g /\ regions_contiguous g.

Lemma nat_list_subset_of_incl : forall xs ys,
  incl xs ys -> nat_list_subset xs ys = true.
Proof.
  intros xs ys H. unfold nat_list_subset. apply forallb_forall.
  intros x Hx. apply nat_list_mem_In. exact (H x Hx).
Qed.

Lemma nat_list_disjoint_app_l : forall xs ys zs,
  nat_list_disjoint xs zs = true -> nat_list_disjoint ys zs = true ->
  nat_list_disjoint (xs ++ ys) zs = true.
Proof.
  intros xs ys zs H1 H2. unfold nat_list_disjoint in *.
  rewrite forallb_app, H1, H2. reflexivity.
Qed.

Lemma NoDup_app_disjoint_nat : forall (l1 l2 : list nat) x,
  NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  induction l1 as [|a l1 IH]; intros l2 x Hnd H1 H2; simpl in *.
  - contradiction.
  - inversion Hnd as [|? ? Hnotin Hnd']; subst.
    destruct H1 as [<-|H1].
    + apply Hnotin. apply in_or_app. right. exact H2.
    + exact (IH l2 x Hnd' H1 H2).
Qed.

Lemma psplit_left_incl : forall r, incl (psplit_left r) r.
Proof.
  intros r x Hx. unfold psplit_left in Hx.
  rewrite <- (firstn_skipn (Nat.div (List.length r) 2) r).
  apply in_or_app. left. exact Hx.
Qed.

Lemma psplit_right_incl : forall r, incl (psplit_right r) r.
Proof.
  intros r x Hx. unfold psplit_right in Hx.
  rewrite <- (firstn_skipn (Nat.div (List.length r) 2) r).
  apply in_or_app. right. exact Hx.
Qed.

Lemma psplit_halves_disjoint : forall r, NoDup r ->
  nat_list_disjoint (psplit_left r) (psplit_right r) = true.
Proof.
  intros r Hnd. apply nat_list_disjoint_spec. intros x H1 H2.
  unfold psplit_left, psplit_right in *.
  rewrite <- (firstn_skipn (Nat.div (List.length r) 2) r) in Hnd.
  exact (NoDup_app_disjoint_nat _ _ x Hnd H1 H2).
Qed.

(** [graph_hw_psplit_partition_valid]: the two halves PSPLIT builds form a
    valid partition of the module's (normalized) region in the sense of the
    abstract [partition_valid] check. *)
Theorem graph_hw_psplit_partition_valid : forall r,
  NoDup r -> partition_valid r (psplit_left r) (psplit_right r) = true.
Proof.
  intros r Hnd. unfold partition_valid.
  rewrite (nat_list_subset_of_incl _ _ (psplit_left_incl r)).
  rewrite (nat_list_subset_of_incl _ _ (psplit_right_incl r)).
  rewrite (psplit_halves_disjoint r Hnd).
  rewrite nat_list_subset_of_incl; [reflexivity|].
  intros x Hx. unfold nat_list_union, psplit_left, psplit_right.
  rewrite firstn_skipn. unfold normalize_region. apply nodup_In. exact Hx.
Qed.

Lemma firstn_seq_range : forall k b n, k <= n ->
  firstn k (List.seq b n) = List.seq b k.
Proof.
  induction k as [|k IH]; intros b n Hk; [reflexivity|].
  destruct n as [|n]; [lia|]. simpl. rewrite IH by lia. reflexivity.
Qed.

Lemma skipn_seq_range : forall k b n, k <= n ->
  skipn k (List.seq b n) = List.seq (b + k) (n - k).
Proof.
  induction k as [|k IH]; intros b n Hk.
  - simpl. rewrite Nat.add_0_r, Nat.sub_0_r. reflexivity.
  - destruct n as [|n]; [lia|]. simpl. rewrite IH by lia.
    replace (S b + k) with (b + S k) by lia. reflexivity.
Qed.

(** [psplit_halves_of_range]: on a range [List.seq b n] the halves are the
    ranges [List.seq b (n/2)] and [List.seq (b + n/2) (n - n/2)], the base
    and size pairs the hardware partition table stores. *)
Theorem psplit_halves_of_range : forall b n,
  psplit_left (List.seq b n) = List.seq b (Nat.div n 2) /\
  psplit_right (List.seq b n) = List.seq (b + Nat.div n 2) (n - Nat.div n 2).
Proof.
  intros b n. unfold psplit_left, psplit_right. rewrite seq_length.
  assert (Hk : Nat.div n 2 <= n) by (apply Nat.Div0.div_le_upper_bound; lia).
  split; [apply firstn_seq_range | apply skipn_seq_range]; exact Hk.
Qed.

Lemma psplit_halves_contiguous : forall r, region_contiguous r ->
  region_contiguous (psplit_left r) /\ region_contiguous (psplit_right r).
Proof.
  intros r Hr. rewrite Hr.
  destruct (psplit_halves_of_range (hd 0 r) (List.length r)) as [HL HR].
  rewrite HL, HR. split; apply region_contiguous_seq.
Qed.

(** Removing a module, or keeping the graph when the ID is absent, keeps the
    regions disjoint; every remaining region misses the region of the
    removed ID, and the remaining entries are entries of the old graph. *)
Lemma graph_remove_or_keep_regions : forall g mid,
  regions_disjoint g ->
  regions_disjoint (match graph_remove g mid with Some (g', _) => g' | None => g end) /\
  Forall (fun p => nat_list_disjoint (graph_module_region g mid) (snd p).(module_region) = true)
    (match graph_remove g mid with Some (g', _) => g' | None => g end).(pg_modules) /\
  incl (match graph_remove g mid with Some (g', _) => g' | None => g end).(pg_modules)
    g.(pg_modules).
Proof.
  intros g mid Hd. unfold graph_remove, graph_module_region, graph_lookup.
  destruct (graph_remove_modules (pg_modules g) mid) as [[mods' removed]|] eqn:E.
  - destruct (graph_remove_modules_shape _ _ _ _ E) as [Hi Hl]. rewrite Hl.
    destruct (graph_remove_modules_regions_disjoint _ _ _ _ Hd E) as [H1 H2].
    split; [exact H1 | split; [exact H2 | exact Hi]].
  - rewrite (graph_remove_modules_None _ _ E).
    split; [exact Hd | split; [|apply incl_refl]].
    apply Forall_forall. intros p _. reflexivity.
Qed.

Lemma graph_remove_or_keep_contiguous : forall g mid,
  regions_contiguous g ->
  regions_contiguous (match graph_remove g mid with Some (g', _) => g' | None => g end) /\
  region_contiguous (graph_module_region g mid).
Proof.
  intros g mid Hc. unfold graph_remove, graph_module_region, graph_lookup.
  destruct (graph_remove_modules (pg_modules g) mid) as [[mods' removed]|] eqn:E.
  - destruct (graph_remove_modules_shape _ _ _ _ E) as [_ Hl]. rewrite Hl.
    exact (graph_remove_modules_regions_contiguous _ _ _ _ Hc E).
  - rewrite (graph_remove_modules_None _ _ E). split; [exact Hc | reflexivity].
Qed.

Lemma graph_remove_or_keep_region_other : forall g mid other,
  other <> mid ->
  graph_module_region (match graph_remove g mid with Some (g', _) => g' | None => g end) other =
  graph_module_region g other.
Proof.
  intros g mid other Hne. unfold graph_remove, graph_module_region, graph_lookup.
  destruct (graph_remove_modules (pg_modules g) mid) as [[mods' removed]|] eqn:E; [|reflexivity].
  cbn [pg_modules]. rewrite (graph_remove_modules_lookup_other _ _ _ _ _ E Hne). reflexivity.
Qed.

Lemma graph_find_region_modules_None : forall modules r,
  graph_find_region_modules modules r = None ->
  Forall (fun p => nat_list_eq (snd p).(module_region) r = false) modules.
Proof.
  induction modules as [|[id m] rest IH]; intros r H; simpl in H.
  - constructor.
  - destruct (nat_list_eq (module_region m) r) eqn:E; [discriminate|].
    constructor; [exact E | exact (IH r H)].
Qed.

Theorem graph_pnew_preserves_regions_disjoint : forall g region,
  regions_disjoint g ->
  region_conflict g (pnew_region region) = false ->
  regions_disjoint (fst (graph_pnew g (pnew_region region))).
Proof.
  intros g region Hd Hc. unfold graph_pnew, graph_find_region. cbv zeta.
  rewrite !pnew_region_normalized.
  destruct (graph_find_region_modules (pg_modules g) (pnew_region region)) eqn:Hf;
    [exact Hd|].
  apply graph_add_module_preserves_regions_disjoint; [exact Hd|].
  apply graph_find_region_modules_None in Hf.
  unfold region_conflict in Hc.
  rewrite Forall_forall in Hf |- *. intros p Hp.
  destruct (nat_list_disjoint (module_region (snd p)) (pnew_region region)) eqn:Hdis.
  - apply nat_list_disjoint_true_sym. exact Hdis.
  - exfalso.
    assert (Hex : existsb (fun p => negb (nat_list_eq (snd p).(module_region) (pnew_region region)) &&
                    negb (nat_list_disjoint (snd p).(module_region) (pnew_region region)))
                    (pg_modules g) = true).
    { apply existsb_exists. exists p. split; [exact Hp|].
      rewrite (Hf p Hp), Hdis. reflexivity. }
    rewrite Hc in Hex. discriminate.
Qed.

Theorem graph_pnew_preserves_regions_contiguous : forall g region,
  regions_contiguous g ->
  regions_contiguous (fst (graph_pnew g (pnew_region region))).
Proof.
  intros g region Hc. unfold graph_pnew, graph_find_region. cbv zeta.
  rewrite !pnew_region_normalized.
  destruct (graph_find_region_modules (pg_modules g) (pnew_region region));
    [exact Hc|].
  apply graph_add_module_preserves_regions_contiguous; [exact Hc|].
  apply pnew_region_contiguous.
Qed.

Theorem graph_hw_psplit_preserves_regions_disjoint : forall g mid,
  regions_disjoint g -> regions_disjoint (graph_hw_psplit g mid).
Proof.
  intros g mid Hd. unfold graph_hw_psplit.
  set (g0 := graph_cascade_delete_morphisms g mid).
  assert (Hd0 : regions_disjoint g0) by exact Hd.
  change (graph_module_region g mid) with (graph_module_region g0 mid).
  destruct (graph_remove_or_keep_regions g0 mid Hd0) as [Hd1 [Hf1 _]].
  set (g1 := match graph_remove g0 mid with Some (g', _) => g' | None => g0 end) in *.
  set (orig := normalize_region (graph_module_region g0 mid)).
  assert (Horig : Forall (fun p => nat_list_disjoint orig (snd p).(module_region) = true)
                    (pg_modules g1)).
  { eapply Forall_impl; [|exact Hf1]. intros p Hp.
    exact (nat_list_disjoint_incl _ _ _ _ (normalize_region_incl _) (incl_refl _) Hp). }
  assert (Hnd : NoDup orig) by apply normalize_region_nodup.
  destruct (graph_add_module g1 (psplit_left orig) []) as [g2 id2] eqn:E2.
  destruct (graph_add_module g2 (psplit_right orig) []) as [g3 id3] eqn:E3.
  assert (Hg2 : g2 = fst (graph_add_module g1 (psplit_left orig) [])) by (rewrite E2; reflexivity).
  assert (Hg3 : g3 = fst (graph_add_module g2 (psplit_right orig) [])) by (rewrite E3; reflexivity).
  rewrite Hg3. apply graph_add_module_preserves_regions_disjoint.
  - rewrite Hg2. apply graph_add_module_preserves_regions_disjoint; [exact Hd1|].
    eapply Forall_impl; [|exact Horig]. intros p Hp.
    exact (nat_list_disjoint_incl _ _ _ _ (psplit_left_incl orig) (incl_refl _) Hp).
  - rewrite Hg2. unfold graph_add_module. cbn [fst pg_modules].
    constructor.
    + cbn [snd normalize_module mk_module_state module_region].
      apply (nat_list_disjoint_incl (psplit_right orig) _ (psplit_left orig) _
               (incl_refl _) (normalize_region_incl _)).
      apply nat_list_disjoint_true_sym. apply psplit_halves_disjoint. exact Hnd.
    + eapply Forall_impl; [|exact Horig]. intros p Hp.
      exact (nat_list_disjoint_incl _ _ _ _ (psplit_right_incl orig) (incl_refl _) Hp).
Qed.

Theorem graph_hw_psplit_preserves_regions_contiguous : forall g mid,
  regions_contiguous g -> regions_contiguous (graph_hw_psplit g mid).
Proof.
  intros g mid Hc. unfold graph_hw_psplit.
  set (g0 := graph_cascade_delete_morphisms g mid).
  assert (Hc0 : regions_contiguous g0) by exact Hc.
  change (graph_module_region g mid) with (graph_module_region g0 mid).
  destruct (graph_remove_or_keep_contiguous g0 mid Hc0) as [Hc1 Hr].
  set (g1 := match graph_remove g0 mid with Some (g', _) => g' | None => g0 end) in *.
  rewrite (normalize_region_contiguous _ Hr).
  destruct (psplit_halves_contiguous _ Hr) as [HL HR].
  destruct (graph_add_module g1 (psplit_left (graph_module_region g0 mid)) []) as [g2 id2] eqn:E2.
  destruct (graph_add_module g2 (psplit_right (graph_module_region g0 mid)) []) as [g3 id3] eqn:E3.
  assert (Hg2 : g2 = fst (graph_add_module g1 (psplit_left (graph_module_region g0 mid)) []))
    by (rewrite E2; reflexivity).
  assert (Hg3 : g3 = fst (graph_add_module g2 (psplit_right (graph_module_region g0 mid)) []))
    by (rewrite E3; reflexivity).
  rewrite Hg3. apply graph_add_module_preserves_regions_contiguous; [|exact HR].
  rewrite Hg2. apply graph_add_module_preserves_regions_contiguous; [exact Hc1 | exact HL].
Qed.

Lemma pmerge_region_incl : forall r1 r2, incl (pmerge_region r1 r2) (r1 ++ r2).
Proof.
  intros r1 r2 x Hx. unfold pmerge_region in Hx.
  destruct (region_contiguousb (r1 ++ r2)); [exact Hx|].
  apply in_app_or in Hx. apply in_or_app. tauto.
Qed.

Lemma pmerge_region_contiguous : forall g m1 m2,
  pmerge_adjacent g m1 m2 = true ->
  region_contiguous (pmerge_region (graph_module_region g m1) (graph_module_region g m2)).
Proof.
  intros g m1 m2 H. unfold pmerge_adjacent in H. unfold pmerge_region.
  destruct (region_contiguousb (graph_module_region g m1 ++ graph_module_region g m2)) eqn:E.
  - apply region_contiguousb_spec. exact E.
  - simpl in H. apply region_contiguousb_spec. exact H.
Qed.

(** PMERGE keeps the regions disjoint whether or not the two ranges touch:
    the joined region lies inside the two removed regions. Adjacency is what
    keeps the joined region a range. *)
Theorem graph_hw_pmerge_preserves_regions_disjoint : forall g m1 m2,
  regions_disjoint g -> regions_disjoint (graph_hw_pmerge g m1 m2).
Proof.
  intros g m1 m2 Hd. unfold graph_hw_pmerge.
  set (g0 := graph_cascade_delete_morphisms (graph_cascade_delete_morphisms g m1) m2).
  assert (Hd0 : regions_disjoint g0) by exact Hd.
  change (graph_module_region g m1) with (graph_module_region g0 m1).
  change (graph_module_region g m2) with (graph_module_region g0 m2).
  destruct (graph_remove_or_keep_regions g0 m1 Hd0) as [Hd1 [Hf1 _]].
  set (g1 := match graph_remove g0 m1 with Some (g', _) => g' | None => g0 end) in *.
  destruct (graph_remove_or_keep_regions g1 m2 Hd1) as [Hd2 [Hf2 Hi2]].
  set (g2 := match graph_remove g1 m2 with Some (g', _) => g' | None => g1 end) in *.
  set (r1 := graph_module_region g0 m1) in *.
  set (r2 := graph_module_region g0 m2).
  assert (H1 : Forall (fun p => nat_list_disjoint r1 (snd p).(module_region) = true)
                 (pg_modules g2)).
  { apply Forall_forall. intros p Hp. rewrite Forall_forall in Hf1. exact (Hf1 p (Hi2 p Hp)). }
  assert (H2 : Forall (fun p => nat_list_disjoint r2 (snd p).(module_region) = true)
                 (pg_modules g2)).
  { destruct (Nat.eq_dec m2 m1) as [E|E].
    - subst r2. rewrite E. exact H1.
    - subst r2. rewrite <- (graph_remove_or_keep_region_other g0 m1 m2 E). exact Hf2. }
  destruct (graph_add_module g2 (pmerge_region r1 r2) []) as [g3 id3] eqn:E3.
  assert (Hg3 : g3 = fst (graph_add_module g2 (pmerge_region r1 r2) []))
    by (rewrite E3; reflexivity).
  rewrite Hg3. apply graph_add_module_preserves_regions_disjoint; [exact Hd2|].
  rewrite Forall_forall in H1, H2 |- *. intros p Hp.
  apply (nat_list_disjoint_incl (r1 ++ r2) _ (module_region (snd p)) _
           (pmerge_region_incl r1 r2) (incl_refl _)).
  apply nat_list_disjoint_app_l; [exact (H1 p Hp) | exact (H2 p Hp)].
Qed.

Theorem graph_hw_pmerge_preserves_regions_contiguous : forall g m1 m2,
  regions_contiguous g -> pmerge_adjacent g m1 m2 = true ->
  regions_contiguous (graph_hw_pmerge g m1 m2).
Proof.
  intros g m1 m2 Hc Hadj. unfold graph_hw_pmerge.
  pose proof (pmerge_region_contiguous g m1 m2 Hadj) as Hm.
  set (g0 := graph_cascade_delete_morphisms (graph_cascade_delete_morphisms g m1) m2).
  assert (Hc0 : regions_contiguous g0) by exact Hc.
  destruct (graph_remove_or_keep_contiguous g0 m1 Hc0) as [Hc1 _].
  set (g1 := match graph_remove g0 m1 with Some (g', _) => g' | None => g0 end) in *.
  destruct (graph_remove_or_keep_contiguous g1 m2 Hc1) as [Hc2 _].
  set (g2 := match graph_remove g1 m2 with Some (g', _) => g' | None => g1 end) in *.
  set (merged := pmerge_region (graph_module_region g m1) (graph_module_region g m2)) in *.
  destruct (graph_add_module g2 merged []) as [g3 id3] eqn:E3.
  assert (Hg3 : g3 = fst (graph_add_module g2 merged [])) by (rewrite E3; reflexivity).
  rewrite Hg3. apply graph_add_module_preserves_regions_contiguous; [exact Hc2 | exact Hm].
Qed.

(** [vm_step_preserves_regions_disjoint]: no step puts an address into two
    modules. *)
Theorem vm_step_preserves_regions_disjoint : forall s instr s',
  vm_step s instr s' ->
  regions_disjoint s.(vm_graph) -> regions_disjoint s'.(vm_graph).
Proof.
  intros s instr s' Hstep Hd.
  inversion Hstep; subst; simpl; try exact Hd.
  all: try (match goal with
            | |- context [if ?b then _ else _] => destruct b eqn:?; simpl; try exact Hd
            end).
  all: try (match goal with
            | H : pnew_ok _ _ = true |- _ => destruct (pnew_ok_spec _ _ H) as [? [? ?]]
            end).
  all: try (apply graph_pnew_preserves_regions_disjoint; assumption).
  all: try (apply graph_hw_psplit_preserves_regions_disjoint; exact Hd).
  all: try (apply graph_hw_pmerge_preserves_regions_disjoint; exact Hd).
  all: try (apply graph_update_module_tensor_regions_disjoint; exact Hd).
  all: try (match goal with
            | H : (?g', _) = graph_add_morphism _ _ _ _ _ |- regions_disjoint ?g' =>
                unfold graph_add_morphism in H; inversion H; subst; exact Hd
            end).
  all: try (match goal with
            | H : graph_compose_morphisms _ _ _ = Some (?g', _) |- _ =>
                unfold regions_disjoint; rewrite (graph_compose_morphisms_modules _ _ _ _ _ H); exact Hd
            | H : graph_add_identity _ _ = Some (?g', _) |- _ =>
                unfold regions_disjoint; rewrite (graph_add_identity_modules _ _ _ _ H); exact Hd
            | H : graph_delete_morphism _ _ = Some ?g' |- _ =>
                unfold regions_disjoint; rewrite (graph_delete_morphism_modules _ _ _ H); exact Hd
            | H : graph_tensor_morphisms _ _ _ = Some (?g', _) |- _ =>
                unfold regions_disjoint; rewrite (graph_tensor_morphisms_modules _ _ _ _ _ H); exact Hd
            end).
Qed.

(** [vm_step_preserves_regions_contiguous]: every step keeps every module
    region a range. *)
Theorem vm_step_preserves_regions_contiguous : forall s instr s',
  vm_step s instr s' ->
  regions_contiguous s.(vm_graph) -> regions_contiguous s'.(vm_graph).
Proof.
  intros s instr s' Hstep Hc.
  inversion Hstep; subst; simpl; try exact Hc.
  all: try (match goal with
            | |- context [if ?b then _ else _] => destruct b eqn:?; simpl; try exact Hc
            end).
  all: try (match goal with
            | H : pmerge_ok _ _ _ = true |- _ => destruct (pmerge_ok_spec _ _ _ H) as [? ?]
            end).
  all: try (apply graph_pnew_preserves_regions_contiguous; assumption).
  all: try (apply graph_hw_psplit_preserves_regions_contiguous; exact Hc).
  all: try (apply graph_hw_pmerge_preserves_regions_contiguous; assumption).
  all: try (apply graph_update_module_tensor_regions_contiguous; exact Hc).
  all: try (match goal with
            | H : (?g', _) = graph_add_morphism _ _ _ _ _ |- regions_contiguous ?g' =>
                unfold graph_add_morphism in H; inversion H; subst; exact Hc
            end).
  all: try (match goal with
            | H : graph_compose_morphisms _ _ _ = Some (?g', _) |- _ =>
                unfold regions_contiguous; rewrite (graph_compose_morphisms_modules _ _ _ _ _ H); exact Hc
            | H : graph_add_identity _ _ = Some (?g', _) |- _ =>
                unfold regions_contiguous; rewrite (graph_add_identity_modules _ _ _ _ H); exact Hc
            | H : graph_delete_morphism _ _ = Some ?g' |- _ =>
                unfold regions_contiguous; rewrite (graph_delete_morphism_modules _ _ _ H); exact Hc
            | H : graph_tensor_morphisms _ _ _ = Some (?g', _) |- _ =>
                unfold regions_contiguous; rewrite (graph_tensor_morphisms_modules _ _ _ _ _ H); exact Hc
            end).
Qed.

Theorem vm_step_preserves_partition_regions_ok : forall s instr s',
  vm_step s instr s' ->
  partition_regions_ok s.(vm_graph) -> partition_regions_ok s'.(vm_graph).
Proof.
  intros s instr s' Hstep [Hd Hc]. split.
  - exact (vm_step_preserves_regions_disjoint s instr s' Hstep Hd).
  - exact (vm_step_preserves_regions_contiguous s instr s' Hstep Hc).
Qed.

(** vm_reachable s s': [s'] is reached from [s] by zero or more steps. *)
Inductive vm_reachable : VMState -> VMState -> Prop :=
| vm_reachable_refl : forall s, vm_reachable s s
| vm_reachable_step : forall s instr s' s'',
    vm_step s instr s' -> vm_reachable s' s'' -> vm_reachable s s''.

Theorem vm_reachable_preserves_partition_regions_ok : forall s s',
  vm_reachable s s' ->
  partition_regions_ok s.(vm_graph) -> partition_regions_ok s'.(vm_graph).
Proof.
  intros s s' Hr. induction Hr as [s|s instr s' s'' Hstep Hr IH]; intro H.
  - exact H.
  - apply IH. exact (vm_step_preserves_partition_regions_ok s instr s' Hstep H).
Qed.

(** [vm_reachable_regions_disjoint]: from a state with no modules (the
    initial state), every reachable state has pairwise-disjoint module
    regions, and each region is a range of addresses.
    [vm_reachable_partition_in_bounds] below adds that every address lies in
    data memory and every module number fits the 64-slot table. *)
Theorem vm_reachable_regions_disjoint : forall s s',
  s.(vm_graph).(pg_modules) = [] ->
  vm_reachable s s' ->
  regions_disjoint s'.(vm_graph) /\ regions_contiguous s'.(vm_graph).
Proof.
  intros s s' H0 Hr.
  apply (vm_reachable_preserves_partition_regions_ok s s' Hr). split.
  - apply regions_disjoint_no_modules. exact H0.
  - apply regions_contiguous_no_modules. exact H0.
Qed.

(** ** Every step keeps the graph well formed

    PSPLIT and PMERGE delete every morphism that names a module they remove,
    so no morphism ever points at a missing module. With the other graph
    operations this gives [well_formed_graph] as a standing invariant of
    [vm_step]. *)

Lemma all_ids_below_graph_insert_modules :
  forall modules bound mid m,
    all_ids_below modules bound ->
    mid < bound ->
    all_ids_below (graph_insert_modules modules mid m) bound.
Proof.
  induction modules as [|[id ms] rest IH]; intros bound mid m Hall Hlt.
  - simpl. split; [exact Hlt| exact I].
  - simpl in Hall. destruct Hall as [Hid Hrest].
    simpl. destruct (Nat.eqb id mid) eqn:Heq.
    + split; [exact Hlt| exact Hrest].
    + split.
      * exact Hid.
      * apply IH; assumption.
Qed.

Lemma graph_update_preserves_wf : forall g mid m,
  well_formed_graph g ->
  mid < pg_next_id g ->
  well_formed_graph (graph_update g mid m).
Proof.
  intros g mid m Hwf Hlt.
  unfold graph_update, well_formed_graph in *. simpl.
  destruct Hwf as [Hwf_mods [Hwf_morphs Hwf_endpoints]].
  repeat split.
  - apply all_ids_below_graph_insert_modules; assumption.
  - exact Hwf_morphs.
  - (* Morphism endpoints: graph_update doesn't change module IDs, just state *)
    clear Hwf_mods Hwf_morphs.
    induction (pg_morphisms g) as [|[morph_id ms] rest IH]; simpl; auto.
    destruct Hwf_endpoints as [Hep Hrest]. split.
    + unfold morph_endpoints_valid in *.
      destruct Hep as [Hsrc Htgt].
      split.
      * apply graph_insert_modules_preserves_in_map. exact Hsrc.
      * apply graph_insert_modules_preserves_in_map. exact Htgt.
    + apply IH. exact Hrest.
Qed.

Lemma graph_pnew_preserves_wf : forall g region,
  well_formed_graph g ->
  well_formed_graph (fst (graph_pnew g region)).
Proof.
  intros g region Hwf.
  unfold graph_pnew.
  destruct (graph_find_region g (normalize_region region)) eqn:Hfind.
  - simpl. exact Hwf.
  - simpl. apply graph_add_module_preserves_wf. exact Hwf.
Qed.

Lemma graph_update_module_tensor_preserves_wf : forall g mid k v,
  well_formed_graph g ->
  well_formed_graph (graph_update_module_tensor g mid k v).
Proof.
  intros g mid k v Hwf.
  unfold graph_update_module_tensor.
  destruct (graph_lookup g mid) eqn:Hlookup.
  - apply graph_update_preserves_wf; [exact Hwf|].
    destruct (Nat.lt_ge_cases mid (pg_next_id g)) as [Hlt|Hge]; [exact Hlt|].
    pose proof (wf_graph_lookup_beyond_next_id g mid Hwf Hge) as Hnone.
    rewrite Hlookup in Hnone. discriminate.
  - exact Hwf.
Qed.

(** No morphism left by [graph_cascade_delete_morphisms g mid] names [mid]. *)
Lemma graph_cascade_delete_morphisms_no_ref : forall g mid morph_id ms,
  In (morph_id, ms) (pg_morphisms (graph_cascade_delete_morphisms g mid)) ->
  morph_source ms <> mid /\ morph_target ms <> mid.
Proof.
  intros g mid morph_id ms Hin.
  unfold graph_cascade_delete_morphisms in Hin. cbn [pg_morphisms] in Hin.
  apply filter_In in Hin. destruct Hin as [_ Hf].
  apply andb_true_iff in Hf. destruct Hf as [Hs Ht].
  apply negb_true_iff, Nat.eqb_neq in Hs.
  apply negb_true_iff, Nat.eqb_neq in Ht.
  split; assumption.
Qed.

(** Removing a module no morphism names keeps the graph well formed, and
    leaves the morphism list as it was. *)
Lemma graph_remove_or_keep_no_ref_wf : forall g mid,
  well_formed_graph g ->
  (forall morph_id ms, In (morph_id, ms) (pg_morphisms g) ->
     morph_source ms <> mid /\ morph_target ms <> mid) ->
  well_formed_graph (match graph_remove g mid with Some (g', _) => g' | None => g end) /\
  pg_morphisms (match graph_remove g mid with Some (g', _) => g' | None => g end) =
  pg_morphisms g.
Proof.
  intros g mid Hwf Hno.
  destruct (graph_remove g mid) as [[g' m]|] eqn:E.
  - split.
    + exact (graph_remove_no_ref_preserves_wf g mid g' m Hwf Hno E).
    + unfold graph_remove in E.
      destruct (graph_remove_modules (pg_modules g) mid) as [[mods r]|]; [|discriminate].
      injection E as <- _. reflexivity.
  - split; [exact Hwf | reflexivity].
Qed.

Theorem graph_hw_psplit_preserves_wf : forall g mid,
  well_formed_graph g -> well_formed_graph (graph_hw_psplit g mid).
Proof.
  intros g mid Hwf. unfold graph_hw_psplit.
  pose proof (graph_cascade_delete_morphisms_preserves_wf g mid Hwf) as Hwf0.
  destruct (graph_remove_or_keep_no_ref_wf (graph_cascade_delete_morphisms g mid) mid Hwf0
              (graph_cascade_delete_morphisms_no_ref g mid)) as [Hwf1 _].
  set (g1 := match graph_remove (graph_cascade_delete_morphisms g mid) mid with
             | Some (g', _) => g' | None => graph_cascade_delete_morphisms g mid end) in *.
  set (orig := normalize_region (graph_module_region g mid)).
  pose proof (graph_add_module_preserves_wf g1 (psplit_left orig) [] Hwf1) as H2.
  destruct (graph_add_module g1 (psplit_left orig) []) as [g2 id2] eqn:E2.
  cbn [fst] in H2.
  pose proof (graph_add_module_preserves_wf g2 (psplit_right orig) [] H2) as H3.
  destruct (graph_add_module g2 (psplit_right orig) []) as [g3 id3] eqn:E3.
  exact H3.
Qed.

Theorem graph_hw_pmerge_preserves_wf : forall g m1 m2,
  well_formed_graph g -> well_formed_graph (graph_hw_pmerge g m1 m2).
Proof.
  intros g m1 m2 Hwf. unfold graph_hw_pmerge.
  set (g0 := graph_cascade_delete_morphisms (graph_cascade_delete_morphisms g m1) m2).
  assert (Hwf0 : well_formed_graph g0).
  { apply graph_cascade_delete_morphisms_preserves_wf.
    apply graph_cascade_delete_morphisms_preserves_wf. exact Hwf. }
  assert (Hno : forall morph_id ms, In (morph_id, ms) (pg_morphisms g0) ->
            morph_source ms <> m1 /\ morph_target ms <> m1 /\
            morph_source ms <> m2 /\ morph_target ms <> m2)
    by (intros morph_id ms Hin; exact (double_cascade_no_ref g m1 m2 morph_id ms Hin)).
  destruct (graph_remove_or_keep_no_ref_wf g0 m1 Hwf0
              (fun i ms H => let '(conj a (conj b _)) := Hno i ms H in conj a b)) as [Hwf1 Hm1].
  set (g1 := match graph_remove g0 m1 with Some (g', _) => g' | None => g0 end) in *.
  assert (Hno2 : forall morph_id ms, In (morph_id, ms) (pg_morphisms g1) ->
            morph_source ms <> m2 /\ morph_target ms <> m2).
  { intros morph_id ms Hin. rewrite Hm1 in Hin.
    destruct (Hno morph_id ms Hin) as [_ [_ [a b]]]. split; assumption. }
  destruct (graph_remove_or_keep_no_ref_wf g1 m2 Hwf1 Hno2) as [Hwf2 _].
  set (g2 := match graph_remove g1 m2 with Some (g', _) => g' | None => g1 end) in *.
  set (merged := pmerge_region (graph_module_region g m1) (graph_module_region g m2)).
  pose proof (graph_add_module_preserves_wf g2 merged [] Hwf2) as H3.
  destruct (graph_add_module g2 merged []) as [g3 id3] eqn:E3.
  exact H3.
Qed.

(** [vm_step_preserves_well_formed_graph]: every step keeps module IDs below
    [pg_next_id], morphism IDs below [pg_next_morph_id], and every morphism's
    source and target among the modules. *)
Theorem vm_step_preserves_well_formed_graph : forall s instr s',
  vm_step s instr s' ->
  well_formed_graph s.(vm_graph) -> well_formed_graph s'.(vm_graph).
Proof.
  intros s instr s' Hstep Hwf.
  inversion Hstep; subst; simpl; try exact Hwf.
  all: try (destruct (pnew_ok _ _) eqn:?; simpl;
            [apply graph_pnew_preserves_wf; exact Hwf | exact Hwf]).
  all: try (destruct (module_room _ _) eqn:?; simpl;
            [apply graph_hw_psplit_preserves_wf; exact Hwf | exact Hwf]).
  all: try (destruct (pmerge_ok _ _ _) eqn:?; simpl;
            [apply graph_hw_pmerge_preserves_wf; exact Hwf | exact Hwf]).
  all: try (apply graph_update_module_tensor_preserves_wf; exact Hwf).
  all: try (match goal with
            | H : (?g', ?m) = graph_add_morphism ?g ?src ?dst ?c ?b,
              Hs : graph_lookup ?g ?src = Some _,
              Hd : graph_lookup ?g ?dst = Some _ |- well_formed_graph ?g' =>
                change g' with (fst (g', m)); rewrite H;
                apply graph_add_morphism_preserves_wf;
                [exact Hwf | rewrite Hs; discriminate | rewrite Hd; discriminate]
            end).
  all: try (match goal with
            | H : graph_compose_morphisms _ _ _ = Some (?g', _) |- _ =>
                exact (graph_compose_morphisms_preserves_wf _ _ _ _ _ Hwf H)
            | H : graph_add_identity _ _ = Some (?g', _) |- _ =>
                exact (graph_add_identity_preserves_wf _ _ _ _ Hwf H)
            | H : graph_delete_morphism _ _ = Some ?g' |- _ =>
                exact (graph_delete_morphism_preserves_wf _ _ _ Hwf H)
            | H : graph_tensor_morphisms _ _ _ = Some (?g', _) |- _ =>
                exact (graph_tensor_morphisms_preserves_wf _ _ _ _ _ Hwf H)
            end).
Qed.

(** ** Every region lies inside data memory; every module number fits the table

    PNEW checks its range against data memory and the module numbers left;
    PSPLIT and PMERGE build their ranges from ranges already in the graph
    and check the module numbers left. So from a graph with no modules every
    reachable state keeps each region inside data memory, keeps
    [pg_next_id] at most [NUM_MODULES], holds each module number once, and
    therefore holds at most [NUM_MODULES] modules, each numbered below 64. *)

Definition regions_in_memory (g : PartitionGraph) : Prop :=
  Forall (fun p => region_in_memory (snd p).(module_region) = true) g.(pg_modules).

Lemma regions_in_memory_no_modules : forall g,
  g.(pg_modules) = [] -> regions_in_memory g.
Proof. intros g H. unfold regions_in_memory. rewrite H. constructor. Qed.

Lemma regions_in_memory_incl : forall g g',
  incl g'.(pg_modules) g.(pg_modules) -> regions_in_memory g -> regions_in_memory g'.
Proof.
  intros g g' Hi H. unfold regions_in_memory in *. rewrite Forall_forall in *.
  intros p Hp. exact (H p (Hi p Hp)).
Qed.

Lemma regions_in_memory_same : forall g g',
  g'.(pg_modules) = g.(pg_modules) -> regions_in_memory g -> regions_in_memory g'.
Proof.
  intros g g' E. apply regions_in_memory_incl. rewrite E. apply incl_refl.
Qed.

Lemma region_in_memory_incl : forall r r',
  incl r' r -> region_in_memory r = true -> region_in_memory r' = true.
Proof.
  intros r r' Hi H. rewrite region_in_memory_spec in *.
  intros a Ha. exact (H a (Hi a Ha)).
Qed.

Lemma graph_module_region_in_memory : forall g mid,
  regions_in_memory g -> region_in_memory (graph_module_region g mid) = true.
Proof.
  intros g mid H. unfold graph_module_region, graph_lookup.
  destruct (graph_lookup_modules (pg_modules g) mid) as [m|] eqn:E; [|reflexivity].
  apply graph_lookup_modules_In in E.
  unfold regions_in_memory in H. rewrite Forall_forall in H. exact (H _ E).
Qed.

Lemma graph_add_module_preserves_regions_in_memory : forall g region axioms,
  regions_in_memory g -> region_in_memory region = true ->
  regions_in_memory (fst (graph_add_module g region axioms)).
Proof.
  intros g region axioms H Hr.
  unfold regions_in_memory, graph_add_module. cbn [fst pg_modules].
  constructor; [|exact H].
  cbn [snd normalize_module mk_module_state module_region].
  exact (region_in_memory_incl _ _ (normalize_region_incl region) Hr).
Qed.

Lemma graph_remove_or_keep_incl : forall g mid,
  incl (match graph_remove g mid with Some (g', _) => g' | None => g end).(pg_modules)
       g.(pg_modules).
Proof.
  intros g mid. unfold graph_remove.
  destruct (graph_remove_modules (pg_modules g) mid) as [[mods' r]|] eqn:E.
  - exact (proj1 (graph_remove_modules_shape _ _ _ _ E)).
  - apply incl_refl.
Qed.

Theorem graph_pnew_preserves_regions_in_memory : forall g region,
  regions_in_memory g -> region_in_memory (pnew_region region) = true ->
  regions_in_memory (fst (graph_pnew g (pnew_region region))).
Proof.
  intros g region H Hr. unfold graph_pnew.
  destruct (graph_find_region g (normalize_region (pnew_region region))); [exact H|].
  apply graph_add_module_preserves_regions_in_memory; [exact H|].
  rewrite pnew_region_normalized. exact Hr.
Qed.

Theorem graph_hw_psplit_preserves_regions_in_memory : forall g mid,
  regions_in_memory g -> regions_in_memory (graph_hw_psplit g mid).
Proof.
  intros g mid H. unfold graph_hw_psplit.
  set (g0 := graph_cascade_delete_morphisms g mid).
  assert (H0 : regions_in_memory g0) by exact H.
  assert (Horig : region_in_memory (normalize_region (graph_module_region g mid)) = true)
    by exact (region_in_memory_incl _ _ (normalize_region_incl _)
                (graph_module_region_in_memory g mid H)).
  set (orig := normalize_region (graph_module_region g mid)) in *.
  pose proof (regions_in_memory_incl _ _ (graph_remove_or_keep_incl g0 mid) H0) as H1.
  set (g1 := match graph_remove g0 mid with Some (g', _) => g' | None => g0 end) in *.
  pose proof (graph_add_module_preserves_regions_in_memory g1 (psplit_left orig) [] H1
                (region_in_memory_incl _ _ (psplit_left_incl orig) Horig)) as H2.
  destruct (graph_add_module g1 (psplit_left orig) []) as [g2 id2] eqn:E2.
  cbn [fst] in H2.
  pose proof (graph_add_module_preserves_regions_in_memory g2 (psplit_right orig) [] H2
                (region_in_memory_incl _ _ (psplit_right_incl orig) Horig)) as H3.
  destruct (graph_add_module g2 (psplit_right orig) []) as [g3 id3] eqn:E3.
  exact H3.
Qed.

Theorem graph_hw_pmerge_preserves_regions_in_memory : forall g m1 m2,
  regions_in_memory g -> regions_in_memory (graph_hw_pmerge g m1 m2).
Proof.
  intros g m1 m2 H. unfold graph_hw_pmerge.
  assert (Hm : region_in_memory
                 (pmerge_region (graph_module_region g m1) (graph_module_region g m2)) = true).
  { apply (region_in_memory_incl _ _ (pmerge_region_incl _ _)).
    apply region_in_memory_spec. intros a Ha. apply in_app_or in Ha.
    destruct Ha as [Ha|Ha];
      [exact (proj1 (region_in_memory_spec _) (graph_module_region_in_memory g m1 H) a Ha)
      |exact (proj1 (region_in_memory_spec _) (graph_module_region_in_memory g m2 H) a Ha)]. }
  set (merged := pmerge_region (graph_module_region g m1) (graph_module_region g m2)) in *.
  set (g0 := graph_cascade_delete_morphisms (graph_cascade_delete_morphisms g m1) m2).
  assert (H0 : regions_in_memory g0) by exact H.
  pose proof (regions_in_memory_incl _ _ (graph_remove_or_keep_incl g0 m1) H0) as H1.
  set (g1 := match graph_remove g0 m1 with Some (g', _) => g' | None => g0 end) in *.
  pose proof (regions_in_memory_incl _ _ (graph_remove_or_keep_incl g1 m2) H1) as H2.
  set (g2 := match graph_remove g1 m2 with Some (g', _) => g' | None => g1 end) in *.
  pose proof (graph_add_module_preserves_regions_in_memory g2 merged [] H2 Hm) as H3.
  destruct (graph_add_module g2 merged []) as [g3 id3] eqn:E3.
  exact H3.
Qed.

Lemma graph_insert_modules_incl_or_new : forall modules mid m p,
  In p (graph_insert_modules modules mid m) -> In p modules \/ p = (mid, m).
Proof.
  induction modules as [|[id e] rest IH]; intros mid m p Hp; simpl in Hp.
  - destruct Hp as [Hp|[]]. right. symmetry. exact Hp.
  - destruct (Nat.eqb id mid).
    + destruct Hp as [Hp|Hp]; [right; symmetry; exact Hp | left; right; exact Hp].
    + destruct Hp as [Hp|Hp]; [left; left; exact Hp|].
      destruct (IH mid m p Hp) as [Hq|Hq]; [left; right; exact Hq | right; exact Hq].
Qed.

Lemma graph_update_module_tensor_regions_in_memory : forall g mid k v,
  regions_in_memory g -> regions_in_memory (graph_update_module_tensor g mid k v).
Proof.
  intros g mid k v H. unfold graph_update_module_tensor.
  destruct (graph_lookup g mid) as [m0|] eqn:Hl; [|exact H].
  unfold regions_in_memory, graph_update. cbn [pg_modules].
  apply Forall_forall. intros p Hp.
  destruct (graph_insert_modules_incl_or_new _ _ _ _ Hp) as [Hq|Hq].
  - unfold regions_in_memory in H. rewrite Forall_forall in H. exact (H p Hq).
  - subst p. cbn [snd normalize_module module_region].
    apply (region_in_memory_incl _ _ (normalize_region_incl _)).
    apply graph_lookup_modules_In in Hl.
    unfold regions_in_memory in H. rewrite Forall_forall in H. exact (H _ Hl).
Qed.

(** [vm_step_preserves_regions_in_memory]: no step puts an address outside
    data memory into a module's region. *)
Theorem vm_step_preserves_regions_in_memory : forall s instr s',
  vm_step s instr s' ->
  regions_in_memory s.(vm_graph) -> regions_in_memory s'.(vm_graph).
Proof.
  intros s instr s' Hstep H.
  inversion Hstep; subst; simpl; try exact H.
  all: try (match goal with
            | |- context [if ?b then _ else _] => destruct b eqn:?; simpl; try exact H
            end).
  all: try (match goal with
            | Hk : pnew_ok _ _ = true |- _ => destruct (pnew_ok_spec _ _ Hk) as [? [? ?]]
            end).
  all: try (apply graph_pnew_preserves_regions_in_memory; assumption).
  all: try (apply graph_hw_psplit_preserves_regions_in_memory; exact H).
  all: try (apply graph_hw_pmerge_preserves_regions_in_memory; exact H).
  all: try (apply graph_update_module_tensor_regions_in_memory; exact H).
  all: try (match goal with
            | Ha : (?g', _) = graph_add_morphism _ _ _ _ _ |- regions_in_memory ?g' =>
                unfold graph_add_morphism in Ha; inversion Ha; subst; exact H
            end).
  all: try (match goal with
            | Hc : graph_compose_morphisms _ _ _ = Some (?g', _) |- _ =>
                exact (regions_in_memory_same _ _ (graph_compose_morphisms_modules _ _ _ _ _ Hc) H)
            | Hc : graph_add_identity _ _ = Some (?g', _) |- _ =>
                exact (regions_in_memory_same _ _ (graph_add_identity_modules _ _ _ _ Hc) H)
            | Hc : graph_delete_morphism _ _ = Some ?g' |- _ =>
                exact (regions_in_memory_same _ _ (graph_delete_morphism_modules _ _ _ Hc) H)
            | Hc : graph_tensor_morphisms _ _ _ = Some (?g', _) |- _ =>
                exact (regions_in_memory_same _ _ (graph_tensor_morphisms_modules _ _ _ _ _ Hc) H)
            end).
Qed.

(** *** Module numbers *)

Lemma graph_pnew_next_id_le : forall g region,
  (fst (graph_pnew g region)).(pg_next_id) <= S g.(pg_next_id).
Proof.
  intros g region. unfold graph_pnew.
  destruct (graph_find_region g (normalize_region region)); simpl; lia.
Qed.

Lemma graph_hw_psplit_next_id : forall g mid,
  (graph_hw_psplit g mid).(pg_next_id) = S (S g.(pg_next_id)).
Proof.
  intros g mid. unfold graph_hw_psplit.
  pose proof (graph_remove_or_keep_next_id (graph_cascade_delete_morphisms g mid) mid) as Hn.
  set (g1 := match graph_remove (graph_cascade_delete_morphisms g mid) mid with
             | Some (g', _) => g' | None => graph_cascade_delete_morphisms g mid end) in *.
  destruct (graph_add_module g1 _ []) as [g2 id2] eqn:E2.
  destruct (graph_add_module g2 _ []) as [g3 id3] eqn:E3.
  unfold graph_add_module in E2, E3. injection E2 as <- _. injection E3 as <- _.
  cbn [pg_next_id]. rewrite Hn. reflexivity.
Qed.

Lemma graph_hw_pmerge_next_id : forall g m1 m2,
  (graph_hw_pmerge g m1 m2).(pg_next_id) = S g.(pg_next_id).
Proof.
  intros g m1 m2. unfold graph_hw_pmerge.
  set (g0 := graph_cascade_delete_morphisms (graph_cascade_delete_morphisms g m1) m2).
  pose proof (graph_remove_or_keep_next_id g0 m1) as Hn1.
  set (g1 := match graph_remove g0 m1 with Some (g', _) => g' | None => g0 end) in *.
  pose proof (graph_remove_or_keep_next_id g1 m2) as Hn2.
  set (g2 := match graph_remove g1 m2 with Some (g', _) => g' | None => g1 end) in *.
  destruct (graph_add_module g2 _ []) as [g3 id3] eqn:E3.
  unfold graph_add_module in E3. injection E3 as <- _.
  cbn [pg_next_id]. rewrite Hn2, Hn1. reflexivity.
Qed.

Lemma graph_update_module_tensor_next_id : forall g mid k v,
  (graph_update_module_tensor g mid k v).(pg_next_id) = g.(pg_next_id).
Proof.
  intros g mid k v. unfold graph_update_module_tensor.
  destruct (graph_lookup g mid); reflexivity.
Qed.

(** [vm_step_preserves_modules_bounded]: no step issues a module number at or
    above [NUM_MODULES]. *)
Theorem vm_step_preserves_modules_bounded : forall s instr s',
  vm_step s instr s' ->
  s.(vm_graph).(pg_next_id) <= NUM_MODULES ->
  s'.(vm_graph).(pg_next_id) <= NUM_MODULES.
Proof.
  intros s instr s' Hstep H.
  inversion Hstep; subst; try (rewrite partition_step_state_graph).
  all: try (match goal with
            | |- context [if pnew_ok ?g ?r then _ else _] =>
                destruct (pnew_ok g r) eqn:Hk; [|exact H];
                destruct (pnew_ok_spec _ _ Hk) as [Hroom _];
                apply module_room_spec in Hroom;
                pose proof (graph_pnew_next_id_le g r); lia
            end).
  all: try (match goal with
            | |- context [if module_room ?g 2 then _ else _] =>
                destruct (module_room g 2) eqn:Hk; [|exact H];
                apply module_room_spec in Hk; rewrite graph_hw_psplit_next_id; lia
            end).
  all: try (match goal with
            | |- context [if pmerge_ok ?g ?x ?y then _ else _] =>
                destruct (pmerge_ok g x y) eqn:Hk; [|exact H];
                destruct (pmerge_ok_spec _ _ _ Hk) as [Hroom _];
                apply module_room_spec in Hroom; rewrite graph_hw_pmerge_next_id; lia
            end).
  all: simpl; try exact H.
  all: try (match goal with
            | |- context [if ?b then _ else _] => destruct b eqn:?; simpl; try exact H
            end).
  all: try (rewrite graph_update_module_tensor_next_id; exact H).
  all: try (match goal with
            | Ha : (?g', _) = graph_add_morphism _ _ _ _ _ |- context [pg_next_id ?g'] =>
                unfold graph_add_morphism in Ha; inversion Ha; subst; exact H
            end).
  all: try (match goal with
            | Hc : graph_compose_morphisms _ _ _ = Some (?g', _) |- _ =>
                rewrite (graph_compose_morphisms_next_id_same _ _ _ _ _ Hc); exact H
            | Hc : graph_add_identity _ _ = Some (?g', _) |- _ =>
                rewrite (graph_add_identity_next_id_same _ _ _ _ Hc); exact H
            | Hc : graph_delete_morphism _ _ = Some ?g' |- _ =>
                rewrite (graph_delete_morphism_next_id_same _ _ _ Hc); exact H
            | Hc : graph_tensor_morphisms _ _ _ = Some (?g', _) |- _ =>
                rewrite (graph_tensor_morphisms_next_id_same _ _ _ _ _ Hc); exact H
            end).
Qed.

(** *** Each module number appears once *)

Definition module_ids_distinct (g : PartitionGraph) : Prop :=
  NoDup (List.map fst g.(pg_modules)).

Lemma all_ids_below_In : forall modules bound mid,
  all_ids_below modules bound -> In mid (List.map fst modules) -> mid < bound.
Proof.
  induction modules as [|[id m] rest IH]; intros bound mid Hb Hin; simpl in *.
  - contradiction.
  - destruct Hb as [Hid Hrest]. destruct Hin as [<-|Hin]; [exact Hid | exact (IH _ _ Hrest Hin)].
Qed.

Lemma graph_add_module_preserves_ids_distinct : forall g region axioms,
  well_formed_graph g -> module_ids_distinct g ->
  module_ids_distinct (fst (graph_add_module g region axioms)).
Proof.
  intros g region axioms [Hb _] Hd. unfold module_ids_distinct, graph_add_module.
  cbn [fst pg_modules List.map fst]. constructor; [|exact Hd].
  intro Hin. pose proof (all_ids_below_In _ _ _ Hb Hin). lia.
Qed.

Lemma graph_remove_modules_ids_distinct : forall modules mid modules' m,
  graph_remove_modules modules mid = Some (modules', m) ->
  NoDup (List.map fst modules) -> NoDup (List.map fst modules').
Proof.
  induction modules as [|[id e] rest IH]; intros mid modules' m Hrem Hd; simpl in Hrem.
  - discriminate.
  - simpl in Hd. inversion Hd as [|? ? Hnot Hrest]; subst.
    destruct (Nat.eqb id mid).
    + injection Hrem as <- _. exact Hrest.
    + destruct (graph_remove_modules rest mid) as [[rest' r]|] eqn:E; [|discriminate].
      injection Hrem as <- _. simpl. constructor.
      * intro Hin. apply Hnot.
        destruct (graph_remove_modules_shape _ _ _ _ E) as [Hi _].
        apply in_map_iff in Hin. destruct Hin as [[x y] [Hx Hxin]]. simpl in Hx. subst x.
        apply in_map_iff. exists (id, y). split; [reflexivity | exact (Hi _ Hxin)].
      * exact (IH _ _ _ E Hrest).
Qed.

Lemma graph_remove_or_keep_ids_distinct : forall g mid,
  module_ids_distinct g ->
  module_ids_distinct (match graph_remove g mid with Some (g', _) => g' | None => g end).
Proof.
  intros g mid Hd. unfold graph_remove.
  destruct (graph_remove_modules (pg_modules g) mid) as [[mods' r]|] eqn:E; [|exact Hd].
  exact (graph_remove_modules_ids_distinct _ _ _ _ E Hd).
Qed.

Lemma graph_insert_modules_ids : forall modules mid m,
  NoDup (List.map fst modules) -> NoDup (List.map fst (graph_insert_modules modules mid m)).
Proof.
  induction modules as [|[id e] rest IH]; intros mid m Hd; simpl.
  - constructor; [intros []|constructor].
  - simpl in Hd. inversion Hd as [|? ? Hnot Hrest]; subst.
    destruct (Nat.eqb id mid) eqn:E.
    + apply Nat.eqb_eq in E. subst. simpl. constructor; assumption.
    + simpl. constructor; [|exact (IH mid m Hrest)].
      intro Hin. apply in_map_iff in Hin. destruct Hin as [[x y] [Hx Hxin]]. simpl in Hx. subst x.
      destruct (graph_insert_modules_incl_or_new _ _ _ _ Hxin) as [Hq|Hq].
      * apply Hnot. apply in_map_iff. exists (id, y). split; [reflexivity | exact Hq].
      * injection Hq as Hq _. apply Nat.eqb_neq in E. contradiction.
Qed.

Lemma graph_update_module_tensor_ids_distinct : forall g mid k v,
  module_ids_distinct g -> module_ids_distinct (graph_update_module_tensor g mid k v).
Proof.
  intros g mid k v Hd. unfold graph_update_module_tensor.
  destruct (graph_lookup g mid); [|exact Hd].
  unfold module_ids_distinct, graph_update. cbn [pg_modules].
  apply graph_insert_modules_ids. exact Hd.
Qed.

Lemma module_ids_distinct_same : forall g g',
  g'.(pg_modules) = g.(pg_modules) -> module_ids_distinct g -> module_ids_distinct g'.
Proof. intros g g' E H. unfold module_ids_distinct. rewrite E. exact H. Qed.

Theorem graph_pnew_preserves_ids_distinct : forall g region,
  well_formed_graph g -> module_ids_distinct g ->
  module_ids_distinct (fst (graph_pnew g region)).
Proof.
  intros g region Hwf Hd. unfold graph_pnew.
  destruct (graph_find_region g (normalize_region region)); [exact Hd|].
  apply graph_add_module_preserves_ids_distinct; assumption.
Qed.

Theorem graph_hw_psplit_preserves_ids_distinct : forall g mid,
  well_formed_graph g -> module_ids_distinct g ->
  module_ids_distinct (graph_hw_psplit g mid).
Proof.
  intros g mid Hwf Hd. unfold graph_hw_psplit.
  pose proof (graph_cascade_delete_morphisms_preserves_wf g mid Hwf) as Hwf0.
  destruct (graph_remove_or_keep_no_ref_wf (graph_cascade_delete_morphisms g mid) mid Hwf0
              (graph_cascade_delete_morphisms_no_ref g mid)) as [Hwf1 _].
  pose proof (graph_remove_or_keep_ids_distinct (graph_cascade_delete_morphisms g mid) mid Hd) as Hd1.
  set (g1 := match graph_remove (graph_cascade_delete_morphisms g mid) mid with
             | Some (g', _) => g' | None => graph_cascade_delete_morphisms g mid end) in *.
  set (orig := normalize_region (graph_module_region g mid)).
  pose proof (graph_add_module_preserves_wf g1 (psplit_left orig) [] Hwf1) as W2.
  pose proof (graph_add_module_preserves_ids_distinct g1 (psplit_left orig) [] Hwf1 Hd1) as D2.
  destruct (graph_add_module g1 (psplit_left orig) []) as [g2 id2] eqn:E2.
  cbn [fst] in W2, D2.
  pose proof (graph_add_module_preserves_ids_distinct g2 (psplit_right orig) [] W2 D2) as D3.
  destruct (graph_add_module g2 (psplit_right orig) []) as [g3 id3] eqn:E3.
  exact D3.
Qed.

Lemma in_map_fst_incl : forall (l l' : list (ModuleID * ModuleState)) x,
  incl l' l -> In x (List.map fst l') -> In x (List.map fst l).
Proof.
  intros l l' x Hi Hx. apply in_map_iff in Hx. destruct Hx as [p [Hp Hin]].
  apply in_map_iff. exists p. split; [exact Hp | exact (Hi p Hin)].
Qed.

Theorem graph_hw_pmerge_preserves_ids_distinct : forall g m1 m2,
  well_formed_graph g -> module_ids_distinct g ->
  module_ids_distinct (graph_hw_pmerge g m1 m2).
Proof.
  intros g m1 m2 [Hb _] Hd. unfold graph_hw_pmerge.
  set (g0 := graph_cascade_delete_morphisms (graph_cascade_delete_morphisms g m1) m2).
  assert (Hd0 : module_ids_distinct g0) by exact Hd.
  pose proof (graph_remove_or_keep_ids_distinct g0 m1 Hd0) as D1.
  pose proof (graph_remove_or_keep_incl g0 m1) as I1.
  pose proof (graph_remove_or_keep_next_id g0 m1) as N1.
  set (g1 := match graph_remove g0 m1 with Some (g', _) => g' | None => g0 end) in *.
  pose proof (graph_remove_or_keep_ids_distinct g1 m2 D1) as D2.
  pose proof (graph_remove_or_keep_incl g1 m2) as I2.
  pose proof (graph_remove_or_keep_next_id g1 m2) as N2.
  set (g2 := match graph_remove g1 m2 with Some (g', _) => g' | None => g1 end) in *.
  set (merged := pmerge_region (graph_module_region g m1) (graph_module_region g m2)).
  destruct (graph_add_module g2 merged []) as [g3 id3] eqn:E3.
  unfold graph_add_module in E3. injection E3 as <- _.
  unfold module_ids_distinct. cbn [pg_modules List.map fst]. constructor; [|exact D2].
  intro Hin.
  assert (Hin0 : In (pg_next_id g2) (List.map fst (pg_modules g))).
  { apply (in_map_fst_incl (pg_modules g0) (pg_modules g2)); [|exact Hin].
    eapply incl_tran; [exact I2 | exact I1]. }
  pose proof (all_ids_below_In _ _ _ Hb Hin0).
  rewrite N2, N1 in *. unfold g0 in *. cbn [pg_next_id graph_cascade_delete_morphisms] in *. lia.
Qed.

(** [vm_step_preserves_module_ids_distinct]: in a well-formed graph no step
    gives two modules the same number. *)
Theorem vm_step_preserves_module_ids_distinct : forall s instr s',
  vm_step s instr s' ->
  well_formed_graph s.(vm_graph) ->
  module_ids_distinct s.(vm_graph) -> module_ids_distinct s'.(vm_graph).
Proof.
  intros s instr s' Hstep Hwf H.
  inversion Hstep; subst; simpl; try exact H.
  all: try (match goal with
            | |- context [if ?b then _ else _] => destruct b eqn:?; simpl; try exact H
            end).
  all: try (apply graph_pnew_preserves_ids_distinct; assumption).
  all: try (apply graph_hw_psplit_preserves_ids_distinct; assumption).
  all: try (apply graph_hw_pmerge_preserves_ids_distinct; assumption).
  all: try (apply graph_update_module_tensor_ids_distinct; exact H).
  all: try (match goal with
            | Ha : (?g', _) = graph_add_morphism _ _ _ _ _ |- module_ids_distinct ?g' =>
                unfold graph_add_morphism in Ha; inversion Ha; subst; exact H
            end).
  all: try (match goal with
            | Hc : graph_compose_morphisms _ _ _ = Some (?g', _) |- _ =>
                exact (module_ids_distinct_same _ _ (graph_compose_morphisms_modules _ _ _ _ _ Hc) H)
            | Hc : graph_add_identity _ _ = Some (?g', _) |- _ =>
                exact (module_ids_distinct_same _ _ (graph_add_identity_modules _ _ _ _ Hc) H)
            | Hc : graph_delete_morphism _ _ = Some ?g' |- _ =>
                exact (module_ids_distinct_same _ _ (graph_delete_morphism_modules _ _ _ Hc) H)
            | Hc : graph_tensor_morphisms _ _ _ = Some (?g', _) |- _ =>
                exact (module_ids_distinct_same _ _ (graph_tensor_morphisms_modules _ _ _ _ _ Hc) H)
            end).
Qed.

(** A well-formed graph whose module numbers are distinct and below
    [NUM_MODULES] holds at most [NUM_MODULES] modules. *)
Lemma modules_count_bounded : forall g,
  well_formed_graph g -> module_ids_distinct g -> g.(pg_next_id) <= NUM_MODULES ->
  List.length g.(pg_modules) <= NUM_MODULES.
Proof.
  intros g [Hb _] Hd Hn.
  rewrite <- (List.map_length fst).
  rewrite <- (List.seq_length NUM_MODULES 0).
  apply NoDup_incl_length; [exact Hd|].
  intros mid Hin. apply in_seq. pose proof (all_ids_below_In _ _ _ Hb Hin). lia.
Qed.

(** Reading a live module number modulo 64, as PSPLIT and PMERGE do, gives
    the number back. *)
Lemma module_id_mod_64 : forall g mid,
  well_formed_graph g -> g.(pg_next_id) <= NUM_MODULES ->
  In mid (List.map fst g.(pg_modules)) -> mid mod 64 = mid.
Proof.
  intros g mid [Hb _] Hn Hin. apply Nat.mod_small.
  pose proof (all_ids_below_In _ _ _ Hb Hin). unfold NUM_MODULES in Hn. lia.
Qed.

Definition partition_in_bounds (g : PartitionGraph) : Prop :=
  well_formed_graph g /\ regions_in_memory g /\ g.(pg_next_id) <= NUM_MODULES /\
  module_ids_distinct g.

Theorem vm_step_preserves_partition_in_bounds : forall s instr s',
  vm_step s instr s' ->
  partition_in_bounds s.(vm_graph) -> partition_in_bounds s'.(vm_graph).
Proof.
  intros s instr s' Hstep [Hwf [Hm [Hn Hd]]].
  split; [exact (vm_step_preserves_well_formed_graph s instr s' Hstep Hwf)|].
  split; [exact (vm_step_preserves_regions_in_memory s instr s' Hstep Hm)|].
  split; [exact (vm_step_preserves_modules_bounded s instr s' Hstep Hn)|].
  exact (vm_step_preserves_module_ids_distinct s instr s' Hstep Hwf Hd).
Qed.

(** [vm_reachable_partition_in_bounds]: from a well-formed state with no
    modules and [pg_next_id] at most [NUM_MODULES] (the initial state),
    every reachable state has pairwise-disjoint module regions, each a range
    of data memory, at most [NUM_MODULES] modules, and every module number
    below 64, so reading a module number modulo 64 names that module. *)
Theorem vm_reachable_partition_in_bounds : forall s s',
  well_formed_graph s.(vm_graph) ->
  s.(vm_graph).(pg_modules) = [] ->
  s.(vm_graph).(pg_next_id) <= NUM_MODULES ->
  vm_reachable s s' ->
  regions_disjoint s'.(vm_graph) /\ regions_contiguous s'.(vm_graph) /\
  regions_in_memory s'.(vm_graph) /\
  s'.(vm_graph).(pg_next_id) <= NUM_MODULES /\
  List.length s'.(vm_graph).(pg_modules) <= NUM_MODULES /\
  (forall mid, In mid (List.map fst s'.(vm_graph).(pg_modules)) -> mid mod 64 = mid).
Proof.
  intros s s' Hwf H0 Hn Hr.
  destruct (vm_reachable_regions_disjoint s s' H0 Hr) as [Hd Hc].
  assert (Hb : partition_in_bounds s'.(vm_graph)).
  { clear Hd Hc. assert (Hb0 : partition_in_bounds s.(vm_graph)).
    { split; [exact Hwf|]. split; [apply regions_in_memory_no_modules; exact H0|].
      split; [exact Hn|]. unfold module_ids_distinct. rewrite H0. constructor. }
    clear H0 Hwf Hn.
    induction Hr as [s|s instr s1 s2 Hstep Hr IH]; [exact Hb0|].
    apply IH. exact (vm_step_preserves_partition_in_bounds s instr s1 Hstep Hb0). }
  destruct Hb as [Hwf' [Hm [Hn' Hdist]]].
  split; [exact Hd|]. split; [exact Hc|]. split; [exact Hm|]. split; [exact Hn'|].
  split; [exact (modules_count_bounded _ Hwf' Hdist Hn')|].
  intros mid Hin. exact (module_id_mod_64 _ mid Hwf' Hn' Hin).
Qed.

(** I/O PORT ENVIRONMENT ORACLE

    READ_PORT bakes the observed value into the instruction at decode time.
    That makes execution deterministic: the same instruction stream, the same state.
    But it raises a question: does the μ-cost depend on what the environment returns?

    It doesn't. The three theorems below prove it. Cost = bits + S mu_delta,
    regardless of which environment produced the value.

    IOEnvironment: maps channel indices to the values they supply. *)
Definition IOEnvironment := nat -> nat.

(** io_env_mu_cost_independent: Two instructions that differ only in the observed
    value have identical μ-cost. The value field doesn't appear in instruction_cost.
    Proof is reflexivity because the definition makes it immediate. *)
Theorem io_env_mu_cost_independent :
  forall dst ch bits mu_delta (v v' : nat),
    instruction_cost (instr_read_port dst ch v  bits mu_delta) =
    instruction_cost (instr_read_port dst ch v' bits mu_delta).
Proof.
  intros. reflexivity.
Qed.

(** io_env_mu_cost_env_agnostic: Two different environments reading the same
    channel produce instructions with the same μ-cost. Follows immediately
    from io_env_mu_cost_independent. *)
Corollary io_env_mu_cost_env_agnostic :
  forall (env1 env2 : IOEnvironment) dst ch bits mu_delta,
    instruction_cost (instr_read_port dst ch (env1 ch) bits mu_delta) =
    instruction_cost (instr_read_port dst ch (env2 ch) bits mu_delta).
Proof.
  intros. reflexivity.
Qed.

(** io_read_cost_positive: Every I/O read charges at least 1 μ-unit.
    Cost is S mu_delta, so it's ≥ 1 no matter what the programmer sets mu_delta to.
    This is the structural positive-cost guarantee for READ_PORT. *)
Lemma io_read_cost_positive :
  forall dst ch v bits mu_delta,
    (instruction_cost (instr_read_port dst ch v bits mu_delta) > 0)%nat.
Proof.
  intros. simpl. lia.
Qed.

End VMStep.

Export VMStep.
