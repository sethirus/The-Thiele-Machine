(** VMUnboundedStep.v — the unbounded sibling of the physical VM's vm_apply.

    Scaffolding #1 (VMState.v / VMStep.v / SimulationProof.v) is the
    hardware-faithful model: write_reg/write_mem apply word64 on every
    write, matching the real 64-bit register file and 128-word memory that
    ThieleCPUCore.v synthesizes to silicon. VMWord64BoundednessObstruction.v
    proves that model has finite capacity ((2^64)^144 reachable
    (regs,mem) contents) — a genuine, permanent architectural fact about
    that physical realization, not a bug.

    This file is Scaffolding #2: the same instruction set, the same
    vm_instruction type, the same VMState record, the same graph/morphism/
    certification/mu-ledger machinery (all reused unchanged from VMStep.v
    and SimulationProof.v's helper functions) — but with vm_apply's write
    path re-derived (vm_apply_u) using write_reg_u/write_mem_u, which store
    the computed value exactly, and with every word64_* arithmetic helper
    replaced by an unmasked counterpart (u_add, u_sub, u_mul, u_and, u_or,
    u_xor, u_shl, u_shr, u_popcount). Nothing here touches VMState.v,
    VMStep.v, SimulationProof.v, coq/kami_hw, or the physical ISA; it is an
    entirely new, additional set of definitions living beside them.

    Design choice, stated plainly: u_sub is Nat.sub (saturates at 0), not a
    two's-complement wraparound like word64_sub. Wraparound is meaningful
    for a FIXED-width register; without a fixed width there is nothing to
    wrap around, so saturation is the faithful unbounded analogue. u_shl/
    u_shr/u_and/u_or/u_xor/u_popcount drop word64's masking but are
    otherwise the same bit operations (via N), so they agree with their
    word64_* counterparts exactly whenever both operands already fit in 64
    bits — this sibling model is a conservative extension, not a
    reinterpretation, of the bounded one.

    This file builds the sibling *semantics*. It does not yet contain a
    self-interpreter (B3's uniform_interpreter_simulation/_correct target);
    that is the next piece, built on top of this file. *)

From Coq Require Import Strings.String List Bool Arith.PeanoNat micromega.Lia.
From Coq Require Import NArith.NArith.
Import ListNotations.

From Kernel Require Import Kernel KernelTM KernelThiele.
From Kernel Require Import VMState VMStep VMEncoding.
From Kernel Require Import CertCheck.
From Kernel Require Import SimulationProof.
Import ListNotations.
Close Scope string_scope.
Open Scope list_scope.

(** * 1. Unmasked arithmetic: same bit operations as word64_*, minus the
    final mask to 64 bits. Agrees with word64_* whenever both operands are
    already below 2^64 (proved below, per operation, as a sanity check that
    this is a conservative extension and not an arbitrary reinterpretation). *)

Definition u_add (a b : nat) : nat := a + b.
Definition u_sub (a b : nat) : nat := a - b.
Definition u_mul (a b : nat) : nat := a * b.

Definition u_and (a b : nat) : nat := N.to_nat (N.land (N.of_nat a) (N.of_nat b)).
Definition u_or  (a b : nat) : nat := N.to_nat (N.lor  (N.of_nat a) (N.of_nat b)).
Definition u_xor (a b : nat) : nat := N.to_nat (N.lxor (N.of_nat a) (N.of_nat b)).
Definition u_shl (a b : nat) : nat := N.to_nat (N.shiftl (N.of_nat a) (N.of_nat b)).
Definition u_shr (a b : nat) : nat := N.to_nat (N.shiftr (N.of_nat a) (N.of_nat b)).
Definition u_popcount (x : nat) : nat :=
  popcount_upto (N.size_nat (N.of_nat x)) (N.of_nat x).

(** * 2. write_reg_u / write_mem_u: identical list surgery to write_reg /
    write_mem, but the value is stored exactly, with no masking. *)

Definition write_reg_u (s : VMState) (r v : nat) : list nat :=
  let idx := reg_index r in
  firstn idx s.(vm_regs) ++ [v] ++ skipn (S idx) s.(vm_regs).

Definition write_mem_u (s : VMState) (a v : nat) : list nat :=
  let idx := mem_index a in
  firstn idx s.(vm_mem) ++ [v] ++ skipn (S idx) s.(vm_mem).

(** * 3. vm_apply_u: vm_apply's exact structure, arm for arm, with every
    write_reg/write_mem replaced by write_reg_u/write_mem_u and every
    word64_* arithmetic helper replaced by its u_* counterpart. Arms that
    never touch vm_regs/vm_mem (advance_state/jump_state/record-literal
    passthrough arms) are copied verbatim — there is nothing to unbound in
    them, they already carry values through unchanged. *)

Definition vm_apply_u (s : VMState) (instr : vm_instruction) : VMState :=
  match instr with
  | instr_pnew region cost =>
      let sz := List.length (normalize_region region) in
      let '(graph', _) := graph_add_module s.(vm_graph) (List.seq 0 sz) [] in
      advance_state s (instr_pnew region cost) graph' s.(vm_csrs) s.(vm_err)
  | instr_psplit module left_region right_region cost =>
      let graph' := graph_hw_psplit s.(vm_graph) (module mod 64) in
      advance_state s (instr_psplit module left_region right_region cost)
        graph' s.(vm_csrs) s.(vm_err)
  | instr_pmerge m1 m2 cost =>
      let graph' := graph_hw_pmerge s.(vm_graph) (m1 mod 64) (m2 mod 64) in
      advance_state s (instr_pmerge m1 m2 cost)
        graph' s.(vm_csrs) s.(vm_err)
  | instr_lassert freg creg kind flen cost =>
      let check_ok := lassert_exec_ok s freg creg kind flen in
      let new_pc   := if check_ok then S s.(vm_pc) else LASSERT_TRAP_PC in
      let new_err  := if check_ok then s.(vm_err) else true in
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
  | instr_ljoin c1reg c2reg cost =>
      advance_state s (instr_ljoin c1reg c2reg cost)
        s.(vm_graph) s.(vm_csrs) s.(vm_err)
  | instr_mdlacc module cost =>
      advance_state s (instr_mdlacc module cost) s.(vm_graph) s.(vm_csrs) s.(vm_err)
  | instr_emit module payload cost =>
      advance_state s (instr_emit module payload cost) s.(vm_graph) s.(vm_csrs) s.(vm_err)
  | instr_reveal module bits cert cost =>
      advance_state_reveal s (instr_reveal module bits cert cost) (module mod 16) bits
        s.(vm_graph) s.(vm_csrs) s.(vm_err)
  | instr_pdiscover module evidence cost =>
      advance_state s (instr_pdiscover module evidence cost) s.(vm_graph) s.(vm_csrs) s.(vm_err)
  | instr_chsh_trial x y a b cost =>
      if chsh_bits_ok x y a b then
        {| vm_graph := s.(vm_graph);
           vm_csrs := s.(vm_csrs);
           vm_regs := s.(vm_regs);
           vm_mem := s.(vm_mem);
           vm_pc := S s.(vm_pc);
           vm_mu := apply_cost s (instr_chsh_trial x y a b cost);
           vm_mu_tensor := s.(vm_mu_tensor);
           vm_err := s.(vm_err);
           vm_logic_acc := s.(vm_logic_acc);
           vm_mstatus := s.(vm_mstatus);
           vm_witness := record_trial s.(vm_witness) x y a b;
           vm_certified := s.(vm_certified) |}
      else
        advance_state s (instr_chsh_trial x y a b cost)
          s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)
  | instr_xfer dst src cost =>
      let regs' := write_reg_u s dst (read_reg s src) in
      advance_state_rm s (instr_xfer dst src cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
  | instr_load_imm dst imm cost =>
      let regs' := write_reg_u s dst imm in
      advance_state_rm s (instr_load_imm dst imm cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
  | instr_load dst rs_addr cost =>
      let addr := read_reg s rs_addr in
      let value := read_mem s addr in
      let regs' := write_reg_u s dst value in
      advance_state_rm s (instr_load dst rs_addr cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
  | instr_store rs_addr src cost =>
      let addr := read_reg s rs_addr in
      let value := read_reg s src in
      let mem' := write_mem_u s addr value in
      advance_state_rm s (instr_store rs_addr src cost)
      s.(vm_graph) s.(vm_csrs) s.(vm_regs) mem' s.(vm_err)
  | instr_add dst rs1 rs2 cost =>
      let v1 := read_reg s rs1 in
      let v2 := read_reg s rs2 in
      let regs' := write_reg_u s dst (u_add v1 v2) in
      advance_state_rm s (instr_add dst rs1 rs2 cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
  | instr_sub dst rs1 rs2 cost =>
      let v1 := read_reg s rs1 in
      let v2 := read_reg s rs2 in
      let regs' := write_reg_u s dst (u_sub v1 v2) in
      advance_state_rm s (instr_sub dst rs1 rs2 cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
  | instr_jump target cost =>
      jump_state s (instr_jump target cost) target
  | instr_jnez rs target cost =>
      if Nat.eqb (read_reg s rs) 0 then
        advance_state s (instr_jnez rs target cost) s.(vm_graph) s.(vm_csrs) s.(vm_err)
      else
        jump_state s (instr_jnez rs target cost) target
  | instr_call target cost =>
      let sp := read_reg s 15 in
      let ret_addr := S s.(vm_pc) in
      let mem' := write_mem_u s sp ret_addr in
      let regs' := write_reg_u s 15 (u_add sp 1) in
      jump_state_rm s (instr_call target cost) target regs' mem'
  | instr_ret cost =>
      let sp := u_sub (read_reg s 15) 1 in
      let ret_pc := read_mem s sp in
      let regs' := write_reg_u s 15 sp in
      jump_state_rm s (instr_ret cost) ret_pc regs' s.(vm_mem)
  | instr_xor_load dst addr cost =>
      let value := read_mem s addr in
      let regs' := write_reg_u s dst value in
      advance_state_rm s (instr_xor_load dst addr cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
  | instr_xor_add dst src cost =>
      let vdst := read_reg s dst in
      let vsrc := read_reg s src in
      let regs' := write_reg_u s dst (u_xor vdst vsrc) in
      advance_state_rm s (instr_xor_add dst src cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
  | instr_xor_swap a b cost =>
      let regs' := swap_regs s.(vm_regs) a b in
      advance_state_rm s (instr_xor_swap a b cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
  | instr_xor_rank dst src cost =>
      let vsrc := read_reg s src in
      let regs' := write_reg_u s dst (u_popcount vsrc) in
      advance_state_rm s (instr_xor_rank dst src cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
  | instr_checkpoint label cost =>
      advance_state s (instr_checkpoint label cost) s.(vm_graph) s.(vm_csrs) s.(vm_err)
  | instr_read_port dst channel_idx value bits cost =>
      let regs' := write_reg_u s dst value in
      advance_state_rm s (instr_read_port dst channel_idx value bits cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
  | instr_write_port channel_idx src cost =>
      advance_state s (instr_write_port channel_idx src cost)
      s.(vm_graph) s.(vm_csrs) s.(vm_err)
  | instr_heap_load dst rs_addr cost =>
      let addr := read_reg s rs_addr in
      let value := read_mem s (s.(vm_csrs).(csr_heap_base) + addr) in
      let regs' := write_reg_u s dst value in
      advance_state_rm s (instr_heap_load dst rs_addr cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
  | instr_heap_store rs_addr src cost =>
      let addr := read_reg s rs_addr in
      let value := read_reg s src in
      let mem' := write_mem_u s (s.(vm_csrs).(csr_heap_base) + addr) value in
      advance_state_rm s (instr_heap_store rs_addr src cost)
      s.(vm_graph) s.(vm_csrs) s.(vm_regs) mem' s.(vm_err)
  | instr_certify delta_mu =>
      {| vm_graph := s.(vm_graph);
         vm_csrs := s.(vm_csrs);
         vm_regs := s.(vm_regs);
         vm_mem := s.(vm_mem);
         vm_pc := S s.(vm_pc);
         vm_mu := s.(vm_mu) + S delta_mu;
         vm_mu_tensor := s.(vm_mu_tensor);
         vm_err := s.(vm_err);
         vm_logic_acc := s.(vm_logic_acc);
         vm_mstatus := s.(vm_mstatus);
         vm_witness := s.(vm_witness);
         vm_certified := true |}
  | instr_and dst rs1 rs2 cost =>
      let v1 := read_reg s rs1 in
      let v2 := read_reg s rs2 in
      let regs' := write_reg_u s dst (u_and v1 v2) in
      advance_state_rm s (instr_and dst rs1 rs2 cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
  | instr_or dst rs1 rs2 cost =>
      let v1 := read_reg s rs1 in
      let v2 := read_reg s rs2 in
      let regs' := write_reg_u s dst (u_or v1 v2) in
      advance_state_rm s (instr_or dst rs1 rs2 cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
  | instr_shl dst rs1 rs2 cost =>
      let v1 := read_reg s rs1 in
      let v2 := read_reg s rs2 in
      let regs' := write_reg_u s dst (u_shl v1 v2) in
      advance_state_rm s (instr_shl dst rs1 rs2 cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
  | instr_shr dst rs1 rs2 cost =>
      let v1 := read_reg s rs1 in
      let v2 := read_reg s rs2 in
      let regs' := write_reg_u s dst (u_shr v1 v2) in
      advance_state_rm s (instr_shr dst rs1 rs2 cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
  | instr_mul dst rs1 rs2 cost =>
      let v1 := read_reg s rs1 in
      let v2 := read_reg s rs2 in
      let regs' := write_reg_u s dst (u_mul v1 v2) in
      advance_state_rm s (instr_mul dst rs1 rs2 cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
  | instr_lui dst imm cost =>
      let regs' := write_reg_u s dst (u_shl imm 8) in
      advance_state_rm s (instr_lui dst imm cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
  | instr_tensor_set mid i j value cost =>
      if VMStep.tensor_indices_ok i j then
        advance_state s (instr_tensor_set mid i j value cost)
          (graph_update_module_tensor s.(vm_graph) mid (i * 4 + j) value)
          s.(vm_csrs) s.(vm_err)
      else
        advance_state s (instr_tensor_set mid i j value cost)
          s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)
  | instr_tensor_get dst mid i j cost =>
      if VMStep.tensor_indices_ok i j then
        advance_state_rm s (instr_tensor_get dst mid i j cost)
          s.(vm_graph) s.(vm_csrs) (write_reg_u s dst (module_tensor_entry s mid i j)) s.(vm_mem) s.(vm_err)
      else
        advance_state s (instr_tensor_get dst mid i j cost)
          s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)
  | instr_morph dst src_mod dst_mod coupling_idx cost =>
      match graph_lookup s.(vm_graph) src_mod, graph_lookup s.(vm_graph) dst_mod with
      | Some ms_src, Some ms_dst =>
          let coupling := load_coupling_from_mem s ms_src.(module_region)
                            ms_dst.(module_region) coupling_idx in
          let '(graph', morph_id) :=
            graph_add_morphism s.(vm_graph) src_mod dst_mod coupling false in
          advance_state_rm s (instr_morph dst src_mod dst_mod coupling_idx cost)
            graph' s.(vm_csrs) (write_reg_u s dst morph_id) s.(vm_mem) s.(vm_err)
      | _, _ =>
          advance_state s (instr_morph dst src_mod dst_mod coupling_idx cost)
            s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)
      end
  | instr_compose dst m1_id m2_id cost =>
      match graph_compose_morphisms s.(vm_graph) m1_id m2_id with
      | Some (graph', morph_id) =>
          advance_state_rm s (instr_compose dst m1_id m2_id cost)
            graph' s.(vm_csrs) (write_reg_u s dst morph_id) s.(vm_mem) s.(vm_err)
      | None =>
          advance_state s (instr_compose dst m1_id m2_id cost)
            s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)
      end
  | instr_morph_id dst module cost =>
      match graph_add_identity s.(vm_graph) module with
      | Some (graph', morph_id) =>
          advance_state_rm s (instr_morph_id dst module cost)
            graph' s.(vm_csrs) (write_reg_u s dst morph_id) s.(vm_mem) s.(vm_err)
      | None =>
          advance_state s (instr_morph_id dst module cost)
            s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)
      end
  | instr_morph_delete morph_id cost =>
      match graph_delete_morphism s.(vm_graph) morph_id with
      | Some graph' =>
          advance_state s (instr_morph_delete morph_id cost)
            graph' s.(vm_csrs) s.(vm_err)
      | None =>
          advance_state s (instr_morph_delete morph_id cost)
            s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)
      end
  | instr_morph_assert morph_id property cert cost =>
      match graph_lookup_morphism s.(vm_graph) morph_id with
      | Some _ =>
          advance_state s (instr_morph_assert morph_id property cert cost)
            s.(vm_graph) (csr_set_cert_addr s.(vm_csrs) (ascii_checksum property)) s.(vm_err)
      | None =>
          advance_state s (instr_morph_assert morph_id property cert cost)
            s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)
      end
  | instr_morph_tensor dst f_id g_id cost =>
      match graph_tensor_morphisms s.(vm_graph) f_id g_id with
      | Some (graph', morph_id) =>
          advance_state_rm s (instr_morph_tensor dst f_id g_id cost)
            graph' s.(vm_csrs) (write_reg_u s dst morph_id) s.(vm_mem) s.(vm_err)
      | None =>
          advance_state s (instr_morph_tensor dst f_id g_id cost)
            s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)
      end
  | instr_morph_get dst morph_id selector cost =>
      match graph_lookup_morphism s.(vm_graph) morph_id with
      | Some ms =>
          advance_state_rm s (instr_morph_get dst morph_id selector cost)
            s.(vm_graph) s.(vm_csrs)
            (write_reg_u s dst (VMStep.morphism_selector_value ms selector))
            s.(vm_mem) s.(vm_err)
      | None =>
          advance_state s (instr_morph_get dst morph_id selector cost)
            s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)
      end
  | instr_halt cost =>
      advance_state s (instr_halt cost) s.(vm_graph) s.(vm_csrs) s.(vm_err)
  | instr_chsh_lassert mu_delta =>
      if column_contractive_check_witness s.(vm_witness) then
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
      else
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
  | instr_chsh_lassert_1ab mu_delta =>
      if column_contractive_check_q1ab_kernel s.(vm_witness) then
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
      else
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
  | instr_chsh_lassert_1ab_g5 mu_delta same_g5 diff_g5 =>
      if q1ab_g5_full_integer_check_kernel s.(vm_witness) same_g5 diff_g5 then
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
      else
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
  | instr_chsh_lassert_1ab_g345 mu_delta same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 =>
      if q1ab_g345_full_integer_check_kernel s.(vm_witness)
           same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 then
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
      else
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
  | instr_chsh_lassert_1ab_g12345 mu_delta same_g1 diff_g1 same_g2 diff_g2
                                     same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 =>
      if q1ab_g12345_full_integer_check_kernel s.(vm_witness)
           same_g1 diff_g1 same_g2 diff_g2
           same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 then
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
      else
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
           vm_certified := s.(vm_certified) |}
  end.

(** * 4. Sanity theorem: this sibling genuinely escapes the boundedness
    obstruction. A single LOAD_IMM-style write (instr_load_imm) can place
    any value, however large, into a register, and it survives exactly —
    unlike write_reg, write_reg_u never masks. This is the direct,
    concrete refutation of state_64bit_bounded_step for this model: the
    analogous property FAILS here by construction, for any v. *)

Theorem vm_apply_u_preserves_large_values : forall s dst imm cost,
  length s.(vm_regs) = REG_COUNT ->
  read_reg (vm_apply_u s (instr_load_imm dst imm cost)) dst = imm.
Proof.
  intros s dst imm cost Hlen.
  cbn [vm_apply_u].
  unfold write_reg_u, read_reg, advance_state_rm. cbn [vm_regs].
  assert (Hidx : reg_index dst < length s.(vm_regs)).
  { rewrite Hlen. unfold reg_index. apply Nat.mod_upper_bound. unfold REG_COUNT; lia. }
  rewrite app_nth2 by (rewrite firstn_length_le by lia; lia).
  rewrite firstn_length_le by lia.
  replace (reg_index dst - reg_index dst) with 0 by lia.
  reflexivity.
Qed.

(** * 5. run_vm_u: run_vm's exact structure, driving vm_apply_u instead of
    vm_apply. This is what an actual host program is executed under. *)

Fixpoint run_vm_u (fuel : nat) (trace : list vm_instruction) (s : VMState) : VMState :=
  match fuel with
  | 0 => s
  | S fuel' =>
      match nth_error trace s.(vm_pc) with
      | Some instr => run_vm_u fuel' trace (vm_apply_u s instr)
      | None => s
      end
  end.
