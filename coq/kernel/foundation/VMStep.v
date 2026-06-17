From Coq Require Import List Bool Arith.PeanoNat Lia.
From Coq Require Import Strings.String Strings.Ascii.
From Coq Require Import BinInt.   (* Z type and arithmetic *)
Import ListNotations.

From Kernel Require Import CertCheck VMState.

(* Force nat default scope locally: BinInt opens Z_scope which would reinterpret
   literals like [8] in [ascii_payload_bits_length] as Z. Marked [Local] so the
   scope choice does NOT propagate to importers; downstream files (like
   F3_CrossLink.v) keep their own scope discipline. *)
Local Open Scope nat_scope.

(** VMStep: How the machine actually runs.

    This file defines the 51-opcode ISA and the vm_step relation that governs
    every state transition. Every instruction has an explicit μ-cost. Every step
    either succeeds or latches the error flag. No undefined behavior.

    The Thiele Machine isn't just a model on paper. This IS the model. Every
    instruction is executable, every cost is explicit, every failure mode is
    named. If you find a step that violates μ-monotonicity or observable locality,
    the whole thing breaks. That's not a figure of speech. The proofs in
    MuLedgerConservation.v and KernelPhysics.v would literally fail to compile.

    Three properties hold for all 51 opcodes:
    - Deterministic: same (state, instruction) pair → same output state.
      Proven: SimulationProof.vm_step_deterministic.
    - μ-Monotonic: vm_mu never decreases.
      Proven: MuLedgerConservation.vm_mu_monotonic_single_step.
    - Observationally local: ops don't affect unrelated module observables.
      Proven: KernelPhysics.observational_no_signaling.

    LASSERT uses a SAT certificate plus a non-triviality witness instead of
    calling an oracle. The success path requires two checkable facts: one
    assignment satisfies the formula, and one assignment falsifies it. That
    blocks tautology inflation at the opcode boundary. UNSAT proof checking
    (kind=false) is NOT implemented. It always fails. This is documented.


    To falsify: If ANY instruction violates μ-monotonicity, NoFreeInsight
    is false. If ANY step is nondeterministic, bisimulation breaks. Test it. *)

Module VMStep.

Definition check_lrat : string -> string -> bool := CertCheck.check_lrat.
Definition check_model : string -> string -> bool := CertCheck.check_model.

(** Payload bits.

    Coq strings are lists of 8-bit [ascii] values.  For cost accounting we do
    not charge "string length" or "character length"; we expose the actual
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

    WHY μ_delta IS EXPLICIT: Kolmogorov complexity is uncomputable. The assembler
    sets the cost in the instruction encoding; the kernel applies it. This makes
    execution deterministic and verifiable from Coq to OCaml to Verilog.

    The quick reference:

    Partition ops (modify graph):
    - PNEW: Create a fresh hardware-shaped module at pg_next_id.
    - PSPLIT: Split module into two halves (hardware: equal halves).
    - PMERGE: Hardware merge by size. No abstract overlap check here.
    - PDISCOVER: Carry evidence payload; current transition is pure advance.

    Logical ops (cert-setters; cost ≥ 1 enforced by S):
    - LASSERT: Check a formula with a SAT certificate and a falsifying witness.
      Cost: flen * 8 + S mu_delta. Success requires both a model and a
      countermodel, so tautologies do not activate structural certification.
      UNSAT path always fails. That gap is documented.
    - LJOIN: Reserve certificate join cost. Current state transition is pure advance.
    - REVEAL: Reveal bits, record to μ-tensor. Cost: bits + S mu_delta.
    - EMIT: Emit payload bits outside the Coq state. Cost:
      payload_bit_length payload + S mu_delta.

    Register/memory ops:
    - XFER: dst = src (register copy).
    - LOAD_IMM: dst = imm (immediate load).
    - LOAD: dst = mem[regs[rs_addr]] (register-indirect).
    - STORE: mem[regs[rs_addr]] = src.
    - ADD/SUB: 64-bit modular arithmetic.
    - JUMP/JNEZ/CALL/RET: control flow. r31 = SP.

    GF(2) ops (reversible):
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

    To falsify: instruction_cost returns nat (≥ 0). vm_mu can never decrease.
    If any instruction could produce vm_mu' < vm_mu, MuLedgerConservation.v fails. *)
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
    buckets directly, computes the four CHSH correlators, checks the three
    integer-arithmetic column-contractivity conditions, and only activates
    the cert channel when all three hold. On failure, traps to
    LASSERT_TRAP_PC and latches vm_err. μ-cost is S mu_delta (≥ 1)
    regardless of success, matching the cert-setter cost discipline of CERTIFY,
    LJOIN, and MORPH_ASSERT. This is the kernel-level enforcement that closes
    the bridge from `vm_certified` channel activation to column-contractivity
    of the CHSH correlators. *)
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
    bucket pairs — substrate-level Q_{1+AB} closure across all five γ
    parameters simultaneously. Cost is S mu_delta. *)
| instr_chsh_lassert_1ab_g12345 (mu_delta same_g1 diff_g1 same_g2 diff_g2 same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 : nat).


(** instruction_cost: Extract the μ-cost from an instruction.

    WHY THE SPECIAL CASES:
    - LASSERT: flen * 8 + S cost. The kernel charges the encoded formula
      units as concrete bits, then adds S cost.
    - EMIT: payload_bit_length payload + S cost. The payload is unfolded into
      actual Boolean bits before charging.
    - REVEAL, READ_PORT: bits + S cost. The instruction carries the bit count.
    - LJOIN, CERTIFY, MORPH_ASSERT: S cost (always ≥ 1).
      These are the cert-setters. The S wrapper guarantees cost ≥ 1 regardless of
      what the programmer puts in mu_delta. Zero-cost certification is impossible.
    - Everything else: cost = mu_delta as declared (can be 0).

    This table is the exact specification of the cost model. If you think NoFreeInsight
    is wrong, start here. *)
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
    This isn't a policy we check. It's a structural fact baked into the ISA.
    EMIT, REVEAL, LASSERT, LJOIN, READ_PORT, CERTIFY, MORPH_ASSERT all include
    the S cost floor in instruction_cost. Some also add payload bits. No matter
    what mu_delta the programmer encodes, the cost is at least 1. You literally
    cannot write a zero-cost cert-setter. *)
Lemma cert_setter_cost_pos :
  forall instr,
    is_cert_setterb instr = true ->
    instruction_cost instr >= 1.
Proof.
  intros instr H.
  destruct instr; simpl in H; try discriminate; simpl; lia.
Qed.

(** nofi_step_always_ok: Every instruction, unconditionally, satisfies the NoFI
    cost policy. Non-cert-setters satisfy it because there is no constraint.
    Cert-setters satisfy it because cert_setter_cost_pos guarantees cost ≥ 1.
    This means the runtime check nofi_step_cost_okb never actually rejects anything.
    It's always true by construction. The proof is: cases on is_cert_setterb; true
    branch uses cert_setter_cost_pos + leb; false branch is reflexivity. *)
Lemma nofi_step_always_ok : forall instr, nofi_step_cost_okb instr = true.
Proof.
  intros instr.
  unfold nofi_step_cost_okb.
  destruct (is_cert_setterb instr) eqn:Hcert.
  - apply Nat.leb_le. apply cert_setter_cost_pos. exact Hcert.
  - reflexivity.
Qed.

(** nofi_trace_always_ok: Every trace satisfies the NoFI cost policy.
    Follows immediately from nofi_step_always_ok + forallb_forall. One line. *)
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

(** apply_cost: Apply μ-cost to current ledger.

    WHY: This is where μ-monotonicity is enforced. Every instruction has
    cost ≥ 0, so (vm_mu + cost) ≥ vm_mu always holds. The step relation
    uses this to update vm_mu, making μ-conservation true by construction.

    PROOF: instruction_cost extracts mu_delta from the instruction.
    Since mu_delta : nat, it's ≥ 0. Addition preserves ordering.
    Therefore apply_cost s i ≥ s.(vm_mu). QED.

    This is the foundational mechanism that makes No Free Insight enforceable.
*)
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
    Used by CALL (saves return address to memory, decrements SP register). *)
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

(** graph_hw_psplit: Hardware-aligned PSPLIT. Split module mid into two halves.
    The original module is removed, left gets size/2 cells, right gets the rest.
    This is a simplification vs. the abstract graph_psplit which allows arbitrary
    partition geometry. The hardware uses sequential region numbering (seq 0 n).
    Module ID wraps to mod 64 to stay within NUM_MODULES. *)
Definition graph_hw_psplit (g : PartitionGraph) (mid : nat) : PartitionGraph :=
  let orig_sz := graph_module_size g mid in
  let left_sz := Nat.div orig_sz 2 in
  let right_sz := orig_sz - left_sz in
  let g1 := match graph_remove g mid with
             | Some (g', _) => g'
             | None => g
             end in
  let '(g2, _) := graph_add_module g1 (List.seq 0 left_sz) [] in
  let '(g3, _) := graph_add_module g2 (List.seq 0 right_sz) [] in
  g3.

(** Hardware-style PMERGE: merge [m1] and [m2] by summing sizes. *)
Definition graph_hw_pmerge (g : PartitionGraph) (m1 m2 : nat) : PartitionGraph :=
  let sz1 := graph_module_size g m1 in
  let sz2 := graph_module_size g m2 in
  let merged_sz := sz1 + sz2 in
  let g1 := match graph_remove g m1 with
             | Some (g', _) => g'
             | None => g
             end in
  let g2 := match graph_remove g1 m2 with
             | Some (g', _) => g'
             | None => g1
             end in
  let '(g3, _) := graph_add_module g2 (List.seq 0 merged_sz) [] in
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
    Each n_xy must also be strictly positive (we need at least one trial per
    setting pair to compute a correlator at all). The check function below is
    decidable and runs at kernel-step time using only integer arithmetic.

    The bridge theorem (proven in MuLedgerQuantumBridge.v after we wire this
    into the step relation) is:
        column_contractive_check_witness wc = true
          -> zero_marginal_column_contractive (E_00 wc) (E_01 wc) (E_10 wc) (E_11 wc)
    which combined with [column_contractive_iff_quantum_realizable]
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
      - 10 cleared scaled_S_5 entries (Schur of Schur — 4×4 Schur of row 1
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
  (* Schur cascade — six PD checks: *)
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

(** [CHSH_HONEST_MARKER]: distinguished value written to [csr_cert_addr] when
    CHSH_LASSERT successfully verifies column-contractivity of the witness
    counters. Use [ascii_checksum] of a fixed property string for
    consistency with the [MORPH_ASSERT] cert-address discipline. *)
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
    This closes the honest-cost gap: a successful LASSERT step pays
    exactly hw_flen * 8 + S(cost), not a programmer-declared undercount. *)
Definition lassert_exec_ok (s : VMState) (freg creg : nat) (kind : bool) (flen : nat) : bool :=
  andb (Nat.eqb (lassert_hw_flen s freg) flen)
       (lassert_check_ok s freg creg kind).

(** vm_step: The operational semantics of the Thiele Machine.

    This is the step relation: a proposition that says "executing instruction I
    in state S produces state S'." It's inductive because there are multiple
    constructors (one per instruction, sometimes two for success/failure paths).

    WHY AN INDUCTIVE RELATION INSTEAD OF A FUNCTION:
    The function form (vm_apply) exists in SimulationProof.v. The relation form
    here is useful for proofs: you can pattern-match on how a step was taken,
    extract the exact constructor with its hypotheses, and reason about it.
    vm_apply is easier for computation; vm_step is easier for proof.

    ERROR HANDLING:
    Most instructions have a _bad or _badbits constructor for failure cases.
    All failure constructors: (a) still advance PC, (b) still charge μ-cost,
    (c) latch the error flag. There is NO undefined behavior. Every (state,
    instruction) pair has exactly one applicable constructor.

    DETERMINISM: vm_step is deterministic. For each (s, instr) pair, at most one
    output state is reachable. Proven by SimulationProof.vm_step_deterministic.

    To falsify: If you find two constructors that both apply to the same
    (s, instr) with different outputs, determinism is violated and bisimulation
    breaks. The proofs in SimulationProof.v would fail to compile. *)
Inductive vm_step : VMState -> vm_instruction -> VMState -> Prop :=
(** step_pnew: Create a fresh module. Uses hardware-style sequential numbering
    (seq 0 sz) rather than arbitrary region geometry. Module ID wraps mod 64. *)
| step_pnew : forall s region cost graph',
    let sz := List.length (normalize_region region) in
    graph' = fst (graph_add_module s.(vm_graph) (List.seq 0 sz) []) ->
    vm_step s (instr_pnew region cost)
      (advance_state s (instr_pnew region cost) graph' s.(vm_csrs) s.(vm_err))
(** step_psplit: Split module into two halves. Uses graph_hw_psplit (left gets
    size/2 cells, right gets the rest). The abstract left/right parameters are
    accepted but ignored. The split is always equal halves at the RTL level. *)
| step_psplit : forall s module left right cost graph',
    graph' = graph_hw_psplit s.(vm_graph) (module mod 64) ->
    vm_step s (instr_psplit module left right cost)
      (advance_state s (instr_psplit module left right cost)
        graph' s.(vm_csrs) s.(vm_err))
(** step_pmerge: Hardware merge by concatenating module sizes.
    graph_hw_pmerge removes both and creates one with sz1+sz2 cells.
    Module IDs wrap mod 64. There is no abstract overlap or m1=m2 failure check here. *)
| step_pmerge : forall s m1 m2 cost graph',
    graph' = graph_hw_pmerge s.(vm_graph) (m1 mod 64) (m2 mod 64) ->
    vm_step s (instr_pmerge m1 m2 cost)
      (advance_state s (instr_pmerge m1 m2 cost)
        graph' s.(vm_csrs) s.(vm_err))
(** step_lassert: Check a formula with a binary SAT certificate.
    freg = register holding formula base address in memory.
    creg = register holding certificate base address in memory.
    kind = true: SAT certificate with non-triviality witness.
      Memory at cbase stores two assignments back-to-back:
      - cbase + k: satisfying assignment value for variable k
      - cbase + num_vars + k: falsifying assignment value for variable k
      Variables remain 1-indexed; slot 0 is ignored as before.
    false: UNSAT (always fails here).
     flen = declared formula length in 32-bit words (drives μ-cost via flen * 8 + S cost).

     The instruction is only allowed to succeed when flen matches the in-memory
     formula header [lassert_hw_flen s freg]. A mismatch traps exactly like a
     failed witness check. This closes the underpricing gap: a successful LASSERT
     cannot claim a cheaper length than the bytes the checker actually reads.

     On SAT success (lassert_exec_ok = true): advance PC normally, no error.
     On failure or length mismatch: jump to LASSERT_TRAP_PC (0xF00 = 3840),
     latch vm_err.
    μ-cost is always charged regardless of outcome. You pay to check, even to fail.
 UNSAT proof checking (kind=false) is NOT implemented. It always fails.
    This is documented in the file header. The SAT path now certifies only
    non-trivial constraints: formulas with both a model and a countermodel.
    That is the minimum kernel-level guard against tautology inflation. *)
| step_lassert : forall s freg creg kind flen cost,
  let check_ok := lassert_exec_ok s freg creg kind flen in
    let new_pc   := if check_ok then S s.(vm_pc) else LASSERT_TRAP_PC in
    let new_err  := if check_ok then s.(vm_err) else true in
    vm_step s (instr_lassert freg creg kind flen cost)
      {| vm_graph := s.(vm_graph);
         vm_csrs := s.(vm_csrs);
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
    Current hardware-aligned semantics do not compare certificate strings or touch
    CSR state. The step advances and charges S mu_delta. *)
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
    Here we just record the trial into the unforgeable witness counters.
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
    GF(2) / bit-linear operations for partition and info work.
    XOR_LOAD, XOR_ADD, XOR_SWAP, XOR_RANK: all reversible.
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
    in-place writes. Fredkin gate primitive, reversible. *)
| step_xor_swap : forall s a b cost regs',
    regs' = swap_regs s.(vm_regs) a b ->
    vm_step s (instr_xor_swap a b cost)
      (advance_state_rm s (instr_xor_swap a b cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
(** step_xor_rank: Population count (Hamming weight) of src. dst = popcount(src).
    Counts the number of 1-bits in the 64-bit value. Used for measuring
    information density in partition region bitfields. *)
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
    The value is baked into the instruction at decode time (the IOEnvironment
    oracle does this). So execution is deterministic given the instruction stream.
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
    as RISC-V LUI, but the shift amount is 8 (not 12). Used to build 16-bit constants
    with a subsequent LOAD_IMM for the low 8 bits. *)
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

    Proven in CategoryLaws.v, CategoryBridge.v, and ThieleCanonicality.v.
    Zero Admitted for all 7 opcodes.
    --------------------------------------------------------------- *)
(** step_morph_ok: Both modules exist. Add a morphism and return its ID in dst. *)
| step_morph_ok : forall s dst src_mod dst_mod coupling_idx cost src_ms dst_ms graph' morph_id,
    graph_lookup s.(vm_graph) src_mod = Some src_ms ->
    graph_lookup s.(vm_graph) dst_mod = Some dst_ms ->
    (graph', morph_id) = graph_add_morphism s.(vm_graph) src_mod dst_mod empty_coupling_data false ->
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
    discipline). The bridge theorem
    [chsh_lassert_no_trap_implies_column_contractive] (see
    MuLedgerQuantumBridge.v) operates on this observable signature. *)
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

(** I/O PORT ENVIRONMENT ORACLE

    READ_PORT bakes the observed value into the instruction at decode time.
    That makes execution deterministic: the same instruction stream, the same state.
    But it raises a question: does the μ-cost depend on what the environment returns?

    It doesn't. The three theorems below prove it. Cost = bits + S mu_delta,
    regardless of which environment produced the value. This is what closes the
    "I/O port oracle" gap in the hardening tracker.

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
