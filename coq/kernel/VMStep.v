From Coq Require Import List Bool Arith.PeanoNat Lia.
From Coq Require Import Strings.String.
Import ListNotations.

From Kernel Require Import CertCheck VMState.

(** * VMStep: Operational semantics - how the machine actually executes

  This file defines the active 40-opcode ISA and the step relation that governs
    all state transitions. Every operation has an explicit μ-cost. Every step
    either succeeds or sets the error flag - no undefined behavior.

    WHY THIS FILE EXISTS:
    The Thiele Machine isn't just a model on paper. This file defines HOW IT RUNS.
    Every instruction is executable, every cost is explicit, every failure mode
    is specified. The proofs show this behaves correctly. If you find a step
    that violates μ-monotonicity or observable locality, the whole thing breaks.

    THE ACTIVE 40 OPCODES:
    Structural (partition operations):
      PNEW, PSPLIT, PMERGE, PDISCOVER
    Logical (assertion/revelation):
      LASSERT, LJOIN, REVEAL, EMIT
    Computational (reversible XOR-based):
      XFER, XOR_LOAD, XOR_ADD, XOR_SWAP, XOR_RANK
    General-purpose compute (compiler target):
      LOAD_IMM, LOAD, STORE, ADD, SUB, JUMP, JNEZ, CALL, RET
    Special:
      MDLACC, CHSH_TRIAL, ORACLE_HALTS, HALT
    System / checkpointing:
      CHECKPOINT, READ_PORT, WRITE_PORT
    Heap-relative:
      HEAP_LOAD, HEAP_STORE
    Certification / bitwise / ALU extensions:
      CERTIFY, AND, OR, SHL, SHR, MUL, LUI
    Per-module tensor:
      TENSOR_SET, TENSOR_GET

    KEY PROPERTIES (proven elsewhere):
    - Deterministic: Same input state + instruction → same output state
    - μ-Monotonic: vm_mu never decreases (MuLedgerConservation.v)
    - Observationally local: Operations don't affect unrelated modules (KernelPhysics.v)

    CERTIFICATE VERIFICATION:
    LASSERT uses certificates (SAT model or UNSAT proof) instead of calling
    an oracle. This makes execution deterministic and verifiable. The certificates
    are checked by CertCheck.v (LRAT for UNSAT, model checking for SAT).

    NO AXIOMS. NO ADMITS. All proofs compile with Coq 8.18+.

    FALSIFICATION: If ANY instruction violates μ-monotonicity, NoFreeInsight
    is false. If ANY step is nondeterministic, bisimulation breaks. Test it.
    *)

Module VMStep.

Definition check_lrat : string -> string -> bool := CertCheck.check_lrat.
Definition check_model : string -> string -> bool := CertCheck.check_model.

(** vm_instruction: The active 40-opcode ISA of the Thiele Machine.

    Every instruction carries an explicit μ-cost (mu_delta). The step relation
    applies (vm_mu + instruction_cost instr), forcing μ-monotonicity by
    construction. For most instructions, instruction_cost = mu_delta.
    For cert-setters (LASSERT, LJOIN, EMIT, REVEAL, READ_PORT, CERTIFY),
    instruction_cost = S mu_delta (or more — LASSERT adds |formula|_bits).

    STRUCTURAL OPERATIONS (modify partition graph):
    - PNEW: Create new module with given region. Idempotent — returns existing if present.
    - PSPLIT: Split module into left/right children. Validates partition is disjoint.
    - PMERGE: Merge two modules. Fails if regions overlap or modules don't exist.
    - PDISCOVER: Attach evidence (axioms) to module. Records structural knowledge.

    LOGICAL OPERATIONS (assertions and revelation):
    - LASSERT: Assert formula over module. Takes certificate (SAT model or UNSAT proof).
             Valid SAT: adds axiom to module. Valid UNSAT: sets error flag.
             Invalid certificate: sets error flag.
             Cost: |formula| * 8 + S mu_delta (μ denominated in bits).
    - LJOIN: Join two certificates. Succeeds if strings match. Cost: S mu_delta.
    - REVEAL: Reveal bits of information. Records revelation cost. Cost: S mu_delta.
    - EMIT: Emit payload. Updates cert_addr CSR with checksum. Cost: S mu_delta.

    REGISTER TRANSFER:
    - XFER: Copy register to register (overwrites destination).

    GF(2) / XOR-BASED ALU:
    - XOR_LOAD: Load from memory to register (plain load, despite name).
    - XOR_ADD: XOR two registers, store in dst. Reversible.
    - XOR_SWAP: Swap two registers. Fredkin gate primitive.
    - XOR_RANK: Population count (number of 1-bits). Hamming weight.

    GENERAL-PURPOSE COMPUTE (compiler target):
    - LOAD_IMM: Load immediate value into register.
    - LOAD: Load from memory into register (register-indirect addressing).
    - STORE: Store register value to memory (register-indirect addressing).
    - ADD: Integer addition (word64).
    - SUB: Integer subtraction (word64).
    - JUMP: Unconditional branch to target PC.
    - JNEZ: Branch if register nonzero.
    - CALL: Push return address, branch to target. r31 = SP.
    - RET: Pop return address from stack, branch to it. r31 = SP.

    SPECIAL:
    - MDLACC: Module discovery accumulator. Charges μ for structural access.
    - CHSH_TRIAL: CHSH inequality trial. Validates bits in {0,1}.
    - ORACLE_HALTS: Oracle call. Formal placeholder (undecidable).
    - HALT: Stop execution.

    SYSTEM / CHECKPOINTING:
    - CHECKPOINT: Record execution label. Cost: mu_delta.
    - READ_PORT: External input port — reads value into register. Cost: S mu_delta.
    - WRITE_PORT: External output port — sends register value. Cost: mu_delta.

    HEAP-RELATIVE MEMORY:
    - HEAP_LOAD: Load from (heap_base + addr). Cost: mu_delta.
    - HEAP_STORE: Store to (heap_base + addr). Cost: mu_delta.

    CERTIFICATION:
    - CERTIFY: Set vm_certified flag. Cost: S mu_delta.

    EXTENDED ALU (Phase 5):
    - AND/OR/SHL/SHR/MUL: Standard bitwise and arithmetic. Cost: mu_delta.
    - LUI: Load upper immediate (imm << 16). Cost: mu_delta.

    PER-MODULE TENSOR (Phase 6):
    - TENSOR_SET: Set entry (i,j) of module's 4x4 metric tensor. Cost: mu_delta.
    - TENSOR_GET: Get entry (i,j) of module's tensor into register. Cost: mu_delta.

    WHY μ_delta IS EXPLICIT:
    Kolmogorov complexity (the canonical information-theoretic cost) is
    uncomputable. The instruction carries cost as a parameter; the assembler
    sets it in the instruction encoding. The kernel applies it. This makes
    execution deterministic and verifiable.

    FALSIFICATION: Since instruction_cost returns a nat (>= 0), vm_mu can never
    decrease. If any instruction could produce vm_mu' < vm_mu, μ-monotonicity
    (proven in MuLedgerConservation.v) would fail to compile.
*)
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
| instr_oracle_halts (payload : string) (mu_delta : nat)
| instr_halt (mu_delta : nat)
(** Phase 2 additions — proven Coq instructions *)
| instr_checkpoint (label : string) (mu_delta : nat)
| instr_read_port (dst : nat) (channel_idx : nat) (value : nat) (bits : nat) (mu_delta : nat)
| instr_write_port (channel_idx : nat) (src : nat) (mu_delta : nat)
(** Phase 3B — heap-relative memory access *)
| instr_heap_load (dst : nat) (rs_addr : nat) (mu_delta : nat)
| instr_heap_store (rs_addr : nat) (src : nat) (mu_delta : nat)
(** Phase 4 — state-based certification *)
| instr_certify (mu_delta : nat)
(** Phase 5 — extended ALU operations *)
| instr_and (dst : nat) (rs1 : nat) (rs2 : nat) (mu_delta : nat)
| instr_or  (dst : nat) (rs1 : nat) (rs2 : nat) (mu_delta : nat)
| instr_shl (dst : nat) (rs1 : nat) (rs2 : nat) (mu_delta : nat)
| instr_shr (dst : nat) (rs1 : nat) (rs2 : nat) (mu_delta : nat)
| instr_mul (dst : nat) (rs1 : nat) (rs2 : nat) (mu_delta : nat)
| instr_lui (dst : nat) (imm : nat) (mu_delta : nat)
(** Phase 6 — per-module tensor instructions *)
| instr_tensor_set (module : ModuleID) (i j value : nat) (mu_delta : nat)
| instr_tensor_get (dst : nat) (module : ModuleID) (i j : nat) (mu_delta : nat)
(** Phase 7 — categorical structure (morphisms) *)
| instr_morph (dst : nat) (src_mod dst_mod : ModuleID) (coupling_idx : nat) (mu_delta : nat)
| instr_compose (dst : nat) (m1_id m2_id : MorphismID) (mu_delta : nat)
| instr_morph_id (dst : nat) (module : ModuleID) (mu_delta : nat)
| instr_morph_delete (morph_id : MorphismID) (mu_delta : nat)
| instr_morph_assert (morph_id : MorphismID) (property cert : string) (mu_delta : nat)
| instr_morph_tensor (dst : nat) (f_id g_id : MorphismID) (mu_delta : nat)
| instr_morph_get (dst : nat) (morph_id : MorphismID) (selector : nat) (mu_delta : nat).

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
  | instr_emit _ _ cost => S cost
  | instr_reveal _ _ _ cost => S cost
  | instr_oracle_halts _ cost => cost
  | instr_halt cost => cost
  | instr_checkpoint _ cost => cost
  | instr_read_port _ _ _ _ cost => S cost
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
  (* Phase 7: categorical instructions *)
  | instr_morph _ _ _ _ cost => cost
  | instr_compose _ _ _ cost => cost
  | instr_morph_id _ _ cost => cost
  | instr_morph_delete _ cost => cost
  | instr_morph_assert _ _ _ cost => S cost  (* cert-setter *)
  | instr_morph_tensor _ _ _ cost => cost
  | instr_morph_get _ _ _ cost => cost
  end.

(** Executable NoFreeInsight runtime policy:
    cert-setting instructions must carry strictly positive μ-cost. *)
Definition is_cert_setterb (instr : vm_instruction) : bool :=
  match instr with
  | instr_reveal _ _ _ _ => true
  | instr_emit _ _ _ => true
  | instr_ljoin _ _ _ => true
  | instr_lassert _ _ _ _ _ => true
  | instr_read_port _ _ _ _ _ => true
  | instr_certify _ => true
  | instr_morph_assert _ _ _ _ => true
  | _ => false
  end.

Definition nofi_step_cost_okb (instr : vm_instruction) : bool :=
  match is_cert_setterb instr with
  | true => Nat.leb 1 (instruction_cost instr)
  | false => true
  end.

Definition nofi_trace_cost_okb (trace : list vm_instruction) : bool :=
  forallb nofi_step_cost_okb trace.

(** cert_setter_cost_pos: cert-setters always cost ≥ 1 — by construction.
    EMIT, REVEAL, LASSERT, LJOIN, READ_PORT, CERTIFY all use S cost in
    instruction_cost, so the declared field value is irrelevant.
    This makes the NoFI policy unconditional: no programmer can write a
    zero-cost cert-setter. *)
Lemma cert_setter_cost_pos :
  forall instr,
    is_cert_setterb instr = true ->
    instruction_cost instr >= 1.
Proof.
  intros instr H.
  destruct instr; simpl in H; try discriminate; simpl; lia.
Qed.

(** nofi_step_always_ok: every instruction satisfies the NoFI cost policy.
    Follows from cert_setter_cost_pos since all cert-setters charge S cost. *)
Lemma nofi_step_always_ok : forall instr, nofi_step_cost_okb instr = true.
Proof.
  intros instr.
  unfold nofi_step_cost_okb.
  destruct (is_cert_setterb instr) eqn:Hcert.
  - apply Nat.leb_le. apply cert_setter_cost_pos. exact Hcert.
  - reflexivity.
Qed.

(** nofi_trace_always_ok: every trace satisfies the NoFI cost policy. *)
Lemma nofi_trace_always_ok : forall trace, nofi_trace_cost_okb trace = true.
Proof.
  intros trace.
  unfold nofi_trace_cost_okb.
  apply forallb_forall.
  intros instr _.
  apply nofi_step_always_ok.
Qed.

Definition is_bit (n : nat) : bool :=
  orb (Nat.eqb n 0) (Nat.eqb n 1).

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

Definition latch_err (s : VMState) (flag : bool) : bool :=
  orb flag s.(vm_err).

(** vm_mu_tensor_add_at: Increment the flat entry at index k of the
    vm_mu_tensor by delta.  Used by REVEAL to charge to a specific
    spacetime metric component. *)
Definition vm_mu_tensor_add_at (s : VMState) (k delta : nat) : list nat :=
  let old := nth k s.(vm_mu_tensor) 0 in
  list_update_at s.(vm_mu_tensor) k (old + delta).

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

Inductive vm_step : VMState -> vm_instruction -> VMState -> Prop :=
| step_pnew : forall s region cost graph' mid,
    graph_pnew s.(vm_graph) region = (graph', mid) ->
    vm_step s (instr_pnew region cost)
      (advance_state s (instr_pnew region cost) graph' s.(vm_csrs) s.(vm_err))
| step_psplit : forall s module left right cost graph' left_id right_id,
    graph_psplit s.(vm_graph) module left right = Some (graph', left_id, right_id) ->
    vm_step s (instr_psplit module left right cost)
      (advance_state s (instr_psplit module left right cost) graph' s.(vm_csrs) s.(vm_err))
| step_psplit_failure : forall s module left right cost,
    graph_psplit s.(vm_graph) module left right = None ->
    vm_step s (instr_psplit module left right cost)
      (advance_state s (instr_psplit module left right cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
| step_pmerge : forall s m1 m2 cost graph' merged_id,
    graph_pmerge s.(vm_graph) m1 m2 = Some (graph', merged_id) ->
    vm_step s (instr_pmerge m1 m2 cost)
      (advance_state s (instr_pmerge m1 m2 cost) graph' s.(vm_csrs) s.(vm_err))
| step_pmerge_failure : forall s m1 m2 cost,
    graph_pmerge s.(vm_graph) m1 m2 = None ->
    vm_step s (instr_pmerge m1 m2 cost)
      (advance_state s (instr_pmerge m1 m2 cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
| step_lassert_sat : forall s freg creg flen cost graph' formula cert,
    formula = mem_to_string s.(vm_mem) (read_reg s freg) ->
    cert = mem_to_string s.(vm_mem) (read_reg s creg) ->
    check_model formula cert = true ->
    graph' = graph_add_axiom s.(vm_graph) 0 formula ->
    vm_step s (instr_lassert freg creg true flen cost)
      (advance_state s (instr_lassert freg creg true flen cost)
        graph' (csr_set_err (csr_set_status s.(vm_csrs) 1) 0) s.(vm_err))
| step_lassert_unsat : forall s freg creg flen cost formula cert,
    formula = mem_to_string s.(vm_mem) (read_reg s freg) ->
    cert = mem_to_string s.(vm_mem) (read_reg s creg) ->
    check_lrat formula cert = true ->
    vm_step s (instr_lassert freg creg false flen cost)
      (advance_state s (instr_lassert freg creg false flen cost)
        s.(vm_graph) (csr_set_err (csr_set_status s.(vm_csrs) 1) 0) true)
(** Invalid certificate failure cases: relation is total — every LASSERT steps. *)
| step_lassert_sat_failure : forall s freg creg flen cost formula cert,
    formula = mem_to_string s.(vm_mem) (read_reg s freg) ->
    cert = mem_to_string s.(vm_mem) (read_reg s creg) ->
    check_model formula cert = false ->
    vm_step s (instr_lassert freg creg true flen cost)
      (advance_state s (instr_lassert freg creg true flen cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
| step_lassert_unsat_failure : forall s freg creg flen cost formula cert,
    formula = mem_to_string s.(vm_mem) (read_reg s freg) ->
    cert = mem_to_string s.(vm_mem) (read_reg s creg) ->
    check_lrat formula cert = false ->
    vm_step s (instr_lassert freg creg false flen cost)
      (advance_state s (instr_lassert freg creg false flen cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
| step_ljoin_equal : forall s c1reg c2reg cost cert1 cert2,
    cert1 = mem_to_string s.(vm_mem) (read_reg s c1reg) ->
    cert2 = mem_to_string s.(vm_mem) (read_reg s c2reg) ->
    String.eqb cert1 cert2 = true ->
    vm_step s (instr_ljoin c1reg c2reg cost)
      (advance_state s (instr_ljoin c1reg c2reg cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 0) s.(vm_err))
| step_ljoin_mismatch : forall s c1reg c2reg cost cert1 cert2,
    cert1 = mem_to_string s.(vm_mem) (read_reg s c1reg) ->
    cert2 = mem_to_string s.(vm_mem) (read_reg s c2reg) ->
    String.eqb cert1 cert2 = false ->
    vm_step s (instr_ljoin c1reg c2reg cost)
      (advance_state s (instr_ljoin c1reg c2reg cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
| step_mdlacc : forall s module cost,
    vm_step s (instr_mdlacc module cost)
      (advance_state s (instr_mdlacc module cost) s.(vm_graph) s.(vm_csrs) s.(vm_err))
| step_emit : forall s module payload cost csrs',
    csrs' = csr_set_cert_addr s.(vm_csrs) (ascii_checksum payload) ->
    vm_step s (instr_emit module payload cost)
      (advance_state s (instr_emit module payload cost)
        s.(vm_graph) csrs' s.(vm_err))
| step_reveal : forall s module bits cert cost csrs',
    csrs' = csr_set_cert_addr s.(vm_csrs) (ascii_checksum cert) ->
    vm_step s (instr_reveal module bits cert cost)
      (advance_state_reveal s (instr_reveal module bits cert cost) module bits
        s.(vm_graph) csrs' s.(vm_err))
| step_pdiscover : forall s module evidence cost graph',
    graph' = graph_record_discovery s.(vm_graph) module evidence ->
    vm_step s (instr_pdiscover module evidence cost)
      (advance_state s (instr_pdiscover module evidence cost)
        graph' s.(vm_csrs) s.(vm_err))
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
| step_chsh_trial_badbits : forall s x y a b cost,
    chsh_bits_ok x y a b = false ->
    vm_step s (instr_chsh_trial x y a b cost)
      (advance_state s (instr_chsh_trial x y a b cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
| step_xfer : forall s dst src cost regs',
    regs' = write_reg s dst (read_reg s src) ->
    vm_step s (instr_xfer dst src cost)
      (advance_state_rm s (instr_xfer dst src cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
(** ---------------------------------------------------------------
    General-purpose compute instructions (compiler target)
    --------------------------------------------------------------- *)
| step_load_imm : forall s dst imm cost regs',
    regs' = write_reg s dst (word64 imm) ->
    vm_step s (instr_load_imm dst imm cost)
      (advance_state_rm s (instr_load_imm dst imm cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
| step_load : forall s dst rs_addr cost regs' value addr,
    addr = read_reg s rs_addr ->
    value = read_mem s addr ->
    regs' = write_reg s dst value ->
    vm_step s (instr_load dst rs_addr cost)
      (advance_state_rm s (instr_load dst rs_addr cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
| step_store : forall s rs_addr src cost mem' value addr,
    addr = read_reg s rs_addr ->
    value = read_reg s src ->
    mem' = write_mem s addr value ->
    vm_step s (instr_store rs_addr src cost)
      (advance_state_rm s (instr_store rs_addr src cost)
        s.(vm_graph) s.(vm_csrs) s.(vm_regs) mem' s.(vm_err))
| step_add : forall s dst rs1 rs2 cost regs' v1 v2,
    v1 = read_reg s rs1 ->
    v2 = read_reg s rs2 ->
    regs' = write_reg s dst (word64_add v1 v2) ->
    vm_step s (instr_add dst rs1 rs2 cost)
      (advance_state_rm s (instr_add dst rs1 rs2 cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
| step_sub : forall s dst rs1 rs2 cost regs' v1 v2,
    v1 = read_reg s rs1 ->
    v2 = read_reg s rs2 ->
    regs' = write_reg s dst (word64_sub v1 v2) ->
    vm_step s (instr_sub dst rs1 rs2 cost)
      (advance_state_rm s (instr_sub dst rs1 rs2 cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
| step_jump : forall s target cost,
    vm_step s (instr_jump target cost)
      (jump_state s (instr_jump target cost) target)
| step_jnez_taken : forall s rs target cost,
    read_reg s rs <> 0 ->
    vm_step s (instr_jnez rs target cost)
      (jump_state s (instr_jnez rs target cost) target)
| step_jnez_not_taken : forall s rs target cost,
    read_reg s rs = 0 ->
    vm_step s (instr_jnez rs target cost)
      (advance_state s (instr_jnez rs target cost)
        s.(vm_graph) s.(vm_csrs) s.(vm_err))
(** CALL: push return address to stack (r31 = SP, ascending) then jump.
    Stack convention: r31 is SP; mem[SP] = return addr; SP = SP + 1. *)
| step_call : forall s target cost sp ret_addr mem' regs',
    sp = read_reg s 31 ->
    ret_addr = S s.(vm_pc) ->
    mem' = write_mem s sp ret_addr ->
    regs' = write_reg s 31 (word64_add sp 1) ->
    vm_step s (instr_call target cost)
      (jump_state_rm s (instr_call target cost) target regs' mem')
(** RET: pop return address from stack; SP = SP - 1; PC = mem[SP]. *)
| step_ret : forall s cost sp ret_pc regs',
    sp = word64_sub (read_reg s 31) 1 ->
    ret_pc = read_mem s sp ->
    regs' = write_reg s 31 sp ->
    vm_step s (instr_ret cost)
      (jump_state_rm s (instr_ret cost) ret_pc regs' s.(vm_mem))
(** ---------------------------------------------------------------
    Bit-linear algebra (GF(2) operations for partition/info work)
    --------------------------------------------------------------- *)
| step_xor_load : forall s dst addr cost regs' value,
    value = read_mem s addr ->
    regs' = write_reg s dst value ->
    vm_step s (instr_xor_load dst addr cost)
      (advance_state_rm s (instr_xor_load dst addr cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
| step_xor_add : forall s dst src cost regs' vdst vsrc,
    vdst = read_reg s dst ->
    vsrc = read_reg s src ->
    regs' = write_reg s dst (word64_xor vdst vsrc) ->
    vm_step s (instr_xor_add dst src cost)
      (advance_state_rm s (instr_xor_add dst src cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
| step_xor_swap : forall s a b cost regs',
    regs' = swap_regs s.(vm_regs) a b ->
    vm_step s (instr_xor_swap a b cost)
      (advance_state_rm s (instr_xor_swap a b cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
| step_xor_rank : forall s dst src cost regs' vsrc,
    vsrc = read_reg s src ->
    regs' = write_reg s dst (word64_popcount vsrc) ->
    vm_step s (instr_xor_rank dst src cost)
      (advance_state_rm s (instr_xor_rank dst src cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
| step_oracle_halts : forall s payload cost,
    vm_step s (instr_oracle_halts payload cost)
      (advance_state s (instr_oracle_halts payload cost)
        s.(vm_graph) s.(vm_csrs) s.(vm_err))
(** Phase 2 step rules *)
| step_checkpoint : forall s label cost,
    vm_step s (instr_checkpoint label cost)
      (advance_state s (instr_checkpoint label cost)
        s.(vm_graph) s.(vm_csrs) s.(vm_err))
| step_read_port : forall s dst channel_idx value bits cost regs',
    regs' = write_reg s dst value ->
    vm_step s (instr_read_port dst channel_idx value bits cost)
      (advance_state_rm s (instr_read_port dst channel_idx value bits cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
| step_write_port : forall s channel_idx src cost,
    vm_step s (instr_write_port channel_idx src cost)
      (advance_state s (instr_write_port channel_idx src cost)
        s.(vm_graph) s.(vm_csrs) s.(vm_err))
| step_heap_load : forall s dst rs_addr cost regs' value addr,
    addr = read_reg s rs_addr ->
    value = read_mem s (s.(vm_csrs).(csr_heap_base) + addr) ->
    regs' = write_reg s dst value ->
    vm_step s (instr_heap_load dst rs_addr cost)
      (advance_state_rm s (instr_heap_load dst rs_addr cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
| step_heap_store : forall s rs_addr src cost mem' value addr,
    addr = read_reg s rs_addr ->
    value = read_reg s src ->
    mem' = write_mem s (s.(vm_csrs).(csr_heap_base) + addr) value ->
    vm_step s (instr_heap_store rs_addr src cost)
      (advance_state_rm s (instr_heap_store rs_addr src cost)
        s.(vm_graph) s.(vm_csrs) s.(vm_regs) mem' s.(vm_err))
(** ---------------------------------------------------------------
    Extended ALU operations (Phase 5)
    --------------------------------------------------------------- *)
| step_and : forall s dst rs1 rs2 cost regs' v1 v2,
    v1 = read_reg s rs1 ->
    v2 = read_reg s rs2 ->
    regs' = write_reg s dst (word64_and v1 v2) ->
    vm_step s (instr_and dst rs1 rs2 cost)
      (advance_state_rm s (instr_and dst rs1 rs2 cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
| step_or : forall s dst rs1 rs2 cost regs' v1 v2,
    v1 = read_reg s rs1 ->
    v2 = read_reg s rs2 ->
    regs' = write_reg s dst (word64_or v1 v2) ->
    vm_step s (instr_or dst rs1 rs2 cost)
      (advance_state_rm s (instr_or dst rs1 rs2 cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
| step_shl : forall s dst rs1 rs2 cost regs' v1 v2,
    v1 = read_reg s rs1 ->
    v2 = read_reg s rs2 ->
    regs' = write_reg s dst (word64_shl v1 v2) ->
    vm_step s (instr_shl dst rs1 rs2 cost)
      (advance_state_rm s (instr_shl dst rs1 rs2 cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
| step_shr : forall s dst rs1 rs2 cost regs' v1 v2,
    v1 = read_reg s rs1 ->
    v2 = read_reg s rs2 ->
    regs' = write_reg s dst (word64_shr v1 v2) ->
    vm_step s (instr_shr dst rs1 rs2 cost)
      (advance_state_rm s (instr_shr dst rs1 rs2 cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
| step_mul : forall s dst rs1 rs2 cost regs' v1 v2,
    v1 = read_reg s rs1 ->
    v2 = read_reg s rs2 ->
    regs' = write_reg s dst (word64_mul v1 v2) ->
    vm_step s (instr_mul dst rs1 rs2 cost)
      (advance_state_rm s (instr_mul dst rs1 rs2 cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
| step_lui : forall s dst imm cost regs',
    regs' = write_reg s dst (word64_shl imm 8) ->
    vm_step s (instr_lui dst imm cost)
      (advance_state_rm s (instr_lui dst imm cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
| step_halt : forall s cost,
    vm_step s (instr_halt cost)
      (advance_state s (instr_halt cost)
        s.(vm_graph) s.(vm_csrs) s.(vm_err))
(** CERTIFY — state-based certification with structurally positive cost.
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
    TENSOR_GET reads the per-module tensor entry at (i,j) into a register. *)
| step_tensor_set : forall s mid i j value cost graph',
    (i < 4)%nat -> (j < 4)%nat ->
    graph' = graph_update_module_tensor s.(vm_graph) mid (i * 4 + j) value ->
    vm_step s (instr_tensor_set mid i j value cost)
      (advance_state s (instr_tensor_set mid i j value cost)
        graph' s.(vm_csrs) s.(vm_err))
| step_tensor_set_oob : forall s mid i j value cost,
    (4 <= i \/ 4 <= j)%nat ->
    vm_step s (instr_tensor_set mid i j value cost)
      (advance_state s (instr_tensor_set mid i j value cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
| step_tensor_get : forall s dst mid i j cost regs' tensor_val,
    (i < 4)%nat -> (j < 4)%nat ->
    tensor_val = module_tensor_entry s mid i j ->
    regs' = write_reg s dst tensor_val ->
    vm_step s (instr_tensor_get dst mid i j cost)
      (advance_state_rm s (instr_tensor_get dst mid i j cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
| step_tensor_get_oob : forall s dst mid i j cost,
    (4 <= i \/ 4 <= j)%nat ->
    vm_step s (instr_tensor_get dst mid i j cost)
      (advance_state s (instr_tensor_get dst mid i j cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
(** ---------------------------------------------------------------
    Categorical morphism instructions (Phase 7)
    --------------------------------------------------------------- *)
(** MORPH: Create a morphism between modules.
    coupling_idx is currently unused (simplified to empty coupling). *)
| step_morph : forall s dst src_mod dst_mod coupling_idx cost graph' morph_id,
    graph_lookup s.(vm_graph) src_mod <> None ->
    graph_lookup s.(vm_graph) dst_mod <> None ->
    let c := {| coupling_pairs := []; coupling_label := "" |} in
    (graph', morph_id) = graph_add_morphism s.(vm_graph) src_mod dst_mod c false ->
    vm_step s (instr_morph dst src_mod dst_mod coupling_idx cost)
      (advance_state_rm s (instr_morph dst src_mod dst_mod coupling_idx cost)
        graph' s.(vm_csrs) (write_reg s dst morph_id) s.(vm_mem) s.(vm_err))
| step_morph_failure : forall s dst src_mod dst_mod coupling_idx cost,
    (graph_lookup s.(vm_graph) src_mod = None \/
     graph_lookup s.(vm_graph) dst_mod = None) ->
    vm_step s (instr_morph dst src_mod dst_mod coupling_idx cost)
      (advance_state s (instr_morph dst src_mod dst_mod coupling_idx cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
(** COMPOSE: Compose two morphisms m1;m2 when m1.target = m2.source *)
| step_compose : forall s dst m1_id m2_id cost graph' new_id,
    graph_compose_morphisms s.(vm_graph) m1_id m2_id = Some (graph', new_id) ->
    vm_step s (instr_compose dst m1_id m2_id cost)
      (advance_state_rm s (instr_compose dst m1_id m2_id cost)
        graph' s.(vm_csrs) (write_reg s dst new_id) s.(vm_mem) s.(vm_err))
| step_compose_failure : forall s dst m1_id m2_id cost,
    graph_compose_morphisms s.(vm_graph) m1_id m2_id = None ->
    vm_step s (instr_compose dst m1_id m2_id cost)
      (advance_state s (instr_compose dst m1_id m2_id cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
(** MORPH_ID: Create identity morphism for a module *)
| step_morph_id : forall s dst module cost graph' new_id,
    graph_add_identity s.(vm_graph) module = Some (graph', new_id) ->
    vm_step s (instr_morph_id dst module cost)
      (advance_state_rm s (instr_morph_id dst module cost)
        graph' s.(vm_csrs) (write_reg s dst new_id) s.(vm_mem) s.(vm_err))
| step_morph_id_failure : forall s dst module cost,
    graph_add_identity s.(vm_graph) module = None ->
    vm_step s (instr_morph_id dst module cost)
      (advance_state s (instr_morph_id dst module cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
(** MORPH_DELETE: Remove a morphism *)
| step_morph_delete : forall s morph_id cost graph',
    graph_delete_morphism s.(vm_graph) morph_id = Some graph' ->
    vm_step s (instr_morph_delete morph_id cost)
      (advance_state s (instr_morph_delete morph_id cost)
        graph' s.(vm_csrs) s.(vm_err))
| step_morph_delete_failure : forall s morph_id cost,
    graph_delete_morphism s.(vm_graph) morph_id = None ->
    vm_step s (instr_morph_delete morph_id cost)
      (advance_state s (instr_morph_delete morph_id cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
(** MORPH_ASSERT: Assert property about morphism (cert-setter) *)
| step_morph_assert : forall s morph_id property cert cost csrs',
    graph_lookup_morphism s.(vm_graph) morph_id <> None ->
    csrs' = csr_set_err (csr_set_status s.(vm_csrs) 1) 0 ->
    vm_step s (instr_morph_assert morph_id property cert cost)
      (advance_state s (instr_morph_assert morph_id property cert cost)
        s.(vm_graph) (csr_set_cert_addr csrs' (ascii_checksum property)) s.(vm_err))
| step_morph_assert_failure : forall s morph_id property cert cost,
    graph_lookup_morphism s.(vm_graph) morph_id = None ->
    vm_step s (instr_morph_assert morph_id property cert cost)
      (advance_state s (instr_morph_assert morph_id property cert cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
(** MORPH_TENSOR: Tensor product f⊗g of two morphisms *)
| step_morph_tensor : forall s dst f_id g_id cost graph' new_id,
    graph_tensor_morphisms s.(vm_graph) f_id g_id = Some (graph', new_id) ->
    vm_step s (instr_morph_tensor dst f_id g_id cost)
      (advance_state_rm s (instr_morph_tensor dst f_id g_id cost)
        graph' s.(vm_csrs) (write_reg s dst new_id) s.(vm_mem) s.(vm_err))
| step_morph_tensor_failure : forall s dst f_id g_id cost,
    graph_tensor_morphisms s.(vm_graph) f_id g_id = None ->
    vm_step s (instr_morph_tensor dst f_id g_id cost)
      (advance_state s (instr_morph_tensor dst f_id g_id cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
(** MORPH_GET: Read morphism field into register.
    Selectors: 0=source, 1=target, 2=coupling_length, 3=is_identity *)
| step_morph_get : forall s dst morph_id selector cost regs' ms value,
    graph_lookup_morphism s.(vm_graph) morph_id = Some ms ->
    value = match selector with
            | 0 => ms.(morph_source)
            | 1 => ms.(morph_target)
            | 2 => List.length ms.(morph_coupling).(coupling_pairs)
            | 3 => if ms.(morph_is_identity) then 1 else 0
            | _ => 0
            end ->
    regs' = write_reg s dst value ->
    vm_step s (instr_morph_get dst morph_id selector cost)
      (advance_state_rm s (instr_morph_get dst morph_id selector cost)
        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))
| step_morph_get_failure : forall s dst morph_id selector cost,
    graph_lookup_morphism s.(vm_graph) morph_id = None ->
    vm_step s (instr_morph_get dst morph_id selector cost)
      (advance_state s (instr_morph_get dst morph_id selector cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)).

(** =========================================================================
    I/O PORT ENVIRONMENT ORACLE
    =========================================================================

    [instr_read_port] bakes the observed value into the instruction at decode
    time, making execution deterministic given the instruction stream.  Here
    we formalise the external-world interface as an [IOEnvironment] oracle and
    prove the key invariant: μ-charging is INDEPENDENT of the channel value.

    This closes the "I/O port oracle" gap: µ costs are fully determined by
    the instruction's [mu_delta] field, not by what the environment returns.
    =========================================================================*)

(** An [IOEnvironment] maps channel indices to the values they supply. *)
Definition IOEnvironment := nat -> nat.

(** The µ-cost of [instr_read_port] equals [S mu_delta] regardless of what
    value the environment supplies on the channel. *)
Theorem io_env_mu_cost_independent :
  forall dst ch bits mu_delta (v v' : nat),
    instruction_cost (instr_read_port dst ch v  bits mu_delta) =
    instruction_cost (instr_read_port dst ch v' bits mu_delta).
Proof.
  intros. reflexivity.
Qed.

(** For any two environments, the µ-cost of reading the same channel is equal. *)
Corollary io_env_mu_cost_env_agnostic :
  forall (env1 env2 : IOEnvironment) dst ch bits mu_delta,
    instruction_cost (instr_read_port dst ch (env1 ch) bits mu_delta) =
    instruction_cost (instr_read_port dst ch (env2 ch) bits mu_delta).
Proof.
  intros. reflexivity.
Qed.

(** The µ-cost is exactly [S mu_delta] — strictly positive — so every I/O
    read charges at least 1 µ unit to the ledger. *)
Lemma io_read_cost_positive :
  forall dst ch v bits mu_delta,
    (instruction_cost (instr_read_port dst ch v bits mu_delta) > 0)%nat.
Proof.
  intros. simpl. lia.
Qed.

End VMStep.

Export VMStep.
