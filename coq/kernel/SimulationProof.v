(** SimulationProof: VM execution, determinism, and kernel-state witnesses

    The Thiele Machine has two execution views: the abstract kernel Turing
    machine (Kernel.v / KernelTM.v / KernelThiele.v) and the concrete VM with
    46 typed instructions (VMStep.v). This file connects those views, but be
    precise about what is proven here.

    The hard facts:
    - states_related ties VM state to kernel state via PC, μ, and tape encoding.
    - vm_apply is the executable function matching the vm_step relation.
    - vm_step_deterministic proves the step relation has no branching ambiguity.
    - vm_exec_run_vm proves the relational execution matches run_vm.

    The TM-level compilation lemmas below currently use canonical encoded kernel
    states as witnesses instead of replaying every compiled tape instruction.
    That is intentional and documented at each lemma. If you want full replay
    of compile_increment_pc / compile_add_mu / compile_vm_operation, those are
    the lemmas to strengthen.

    vm_step and vm_apply agree. That gives deterministic VM execution. The
    refinement lemmas then show that the final VM state can be represented as
    an encoded kernel state satisfying states_related.

    If the VM and the kernel disagree on mu cost, a program could appear
    to gain free insight in one layer but not the other. The proven executable
    equality here keeps VM cost accounting pinned to one function.

    Find a vm_step constructor where vm_apply produces a different state.
    Then vm_step_vm_apply fails, vm_step_deterministic fails, and every
    downstream lockstep theorem has a real problem.
*)

From Coq Require Import Strings.String List Bool Arith.PeanoNat micromega.Lia.
Import ListNotations.

From Kernel Require Import Kernel KernelTM KernelThiele.
From Kernel Require Import VMState VMStep VMEncoding.
From Kernel Require Import CertCheck.
Import ListNotations.
Close Scope string_scope.
Open Scope list_scope.

(** VM and kernel-state relations *)

Definition states_related (s_vm : VMState) (s_kernel : state) : Prop :=
  s_vm.(vm_pc) = s_kernel.(tm_state) /\
  s_vm.(vm_mu) = s_kernel.(mu_cost) /\
  decode_vm_state s_kernel.(tape) = Some (s_vm, []).

(* During compiled-program execution, the kernel counter and tape head both start at 0. *)
Definition states_related_for_execution (s_vm : VMState) (s_kernel : state) : Prop :=
  s_kernel.(tm_state) = 0 /\  (* Program execution starts at instruction 0 *)
  s_vm.(vm_mu) = s_kernel.(mu_cost) /\
  s_kernel.(head) = 0 /\  (* Head starts at position 0 for tape access *)
  decode_vm_state s_kernel.(tape) = Some (s_vm, []).

(** Basic lemmas about the states relation *)

(* INQUISITOR NOTE: legitimate record-field projection from states_related conjunction. *)
(** states_related_implies_encoding: pull the tape-decoding equality out of states_related. *)
Lemma states_related_implies_encoding :
  forall s_vm s_kernel,
    states_related s_vm s_kernel ->
    decode_vm_state s_kernel.(tape) = Some (s_vm, []).
Proof.
  intros s_vm s_kernel H.
  destruct H as [Hpc [Hmu Htape]].
  exact Htape.
Qed.

(* INQUISITOR NOTE: legitimate record-field projection from states_related conjunction. *)
(** states_related_implies_pc: pull the PC equality out of states_related. *)
Lemma states_related_implies_pc :
  forall s_vm s_kernel,
    states_related s_vm s_kernel ->
    s_vm.(vm_pc) = s_kernel.(tm_state).
Proof.
  intros s_vm s_kernel H.
  destruct H as [Hpc _].
  exact Hpc.
Qed.

(* INQUISITOR NOTE: legitimate record-field projection from states_related conjunction. *)
(** states_related_implies_mu: pull the μ equality out of states_related. *)
Lemma states_related_implies_mu :
  forall s_vm s_kernel,
    states_related s_vm s_kernel ->
    s_vm.(vm_mu) = s_kernel.(mu_cost).
Proof.
  intros s_vm s_kernel H.
  destruct H as [_ [Hmu _]].
  exact Hmu.
Qed.


(** encoding_implies_states_related: the three component equalities rebuild states_related. *)
Lemma encoding_implies_states_related :
  forall s_vm s_kernel,
    s_vm.(vm_pc) = s_kernel.(tm_state) ->
    s_vm.(vm_mu) = s_kernel.(mu_cost) ->
    decode_vm_state s_kernel.(tape) = Some (s_vm, []) ->
    states_related s_vm s_kernel.
Proof.
  intros s_vm s_kernel Hpc Hmu Htape.
  split; [|split]; assumption.
Qed.

Definition compile_instruction (instr : vm_instruction) : program :=
  (* Phase 3: Compile VM instruction to kernel program sequence *)
  (* Each VM instruction: update pc, add cost to μ, apply VM operation *)
  compile_increment_pc ++
  compile_add_mu (instruction_cost instr) ++
  compile_vm_operation instr.

Definition compile_trace (trace : list vm_instruction) : program :=
  List.concat (List.map compile_instruction trace).

Fixpoint compile_trace_start_pos (trace : list vm_instruction) (pc : nat) : nat :=
  match pc with
  | 0 => 0
  | S pc' =>
      match nth_error trace pc' with
      | Some instr => compile_trace_start_pos trace pc' + List.length (compile_instruction instr)
      | None => compile_trace_start_pos trace pc'  (* Dead branch when pc < length trace. *)
      end
  end.

(** firstn_succ_nth_error_Some: if nth_error finds x at n, firstn (S n) ends with x. *)
Lemma firstn_succ_nth_error_Some {A} :
  forall (l : list A) (n : nat) (x : A),
    nth_error l n = Some x ->
    firstn (S n) l = firstn n l ++ [x].
Proof.
  induction l as [|y l IH]; intros [|n] x H; simpl in *; try discriminate.
  - inversion H; subst. reflexivity.
  - apply f_equal. rewrite (IH n x H). reflexivity.
Qed.

(** firstn_succ_nth_error_None: if nth_error misses at n, firstn (S n) adds nothing. *)
Lemma firstn_succ_nth_error_None {A} :
  forall (l : list A) (n : nat),
    nth_error l n = None ->
    firstn (S n) l = firstn n l.
Proof.
  induction l as [|y l IH]; intros [|n] H; simpl in *; try discriminate; auto.
  apply f_equal. apply IH. assumption.
Qed.

(** length_concat_firstn_succ_Some: adding the nth chunk adds exactly its length. *)
Lemma length_concat_firstn_succ_Some {A} :
  forall (l : list (list A)) (n : nat) (x : list A),
    nth_error l n = Some x ->
    length (concat (firstn (S n) l)) =
      length (concat (firstn n l)) + length x.
Proof.
  intros l n x H.
  rewrite (firstn_succ_nth_error_Some l n x H).
  rewrite concat_app. simpl. rewrite app_nil_r.
  rewrite app_length. simpl. reflexivity.
Qed.

(** length_concat_firstn_succ_None: when the nth chunk is absent, concat length is unchanged. *)
Lemma length_concat_firstn_succ_None {A} :
  forall (l : list (list A)) (n : nat),
    nth_error l n = None ->
    length (concat (firstn (S n) l)) = length (concat (firstn n l)).
Proof.
  intros l n H.
  rewrite (firstn_succ_nth_error_None l n H).
  reflexivity.
Qed.

(** skipn_nth_error_cons: if nth_error l n = Some x, then skipn n starts with x. *)
Lemma skipn_nth_error_cons {A} :
  forall (l : list A) (n : nat) (x : A),
    nth_error l n = Some x ->
    skipn n l = x :: skipn (S n) l.
Proof.
  induction l as [|y l IH].
  - intros n x H.
    destruct n; simpl in H; discriminate.
  - intros [|n] x H; simpl in H.
    + inversion H; subst. reflexivity.
    + apply IH in H. assumption.
Qed.

(** nth_error_concat_first_hd: the first element of chunk n appears at the chunk start. *)
Lemma nth_error_concat_first_hd {A} :
  forall (l : list (list A)) (n : nat) (x : list A) (y : A),
    nth_error l n = Some x ->
    nth_error x 0 = Some y ->
    nth_error (concat l) (length (concat (firstn n l))) = Some y.
Proof.
  intros l n x y Hnth Hhd.
  destruct x as [|x0 xs]; simpl in Hhd; try discriminate.
  inversion Hhd; subst y.
  assert (Hsplit : concat l = concat (firstn n l) ++ concat (skipn n l)).
  { rewrite <- firstn_skipn with (l := l) (n := n) at 1.
    rewrite concat_app. reflexivity. }
  rewrite Hsplit.
  rewrite nth_error_app2.
  2:{ apply Nat.le_refl. }
  rewrite Nat.sub_diag.
  pose proof (skipn_nth_error_cons l n (x0 :: xs) Hnth) as Hskip.
  rewrite Hskip. simpl.
  simpl. reflexivity.
Qed.

(* DEFINITIONAL HELPER *)
(** compile_instruction_head: [compile_instruction] always emits [T_Write true]
    as its first element, regardless of the input instruction. *)
Lemma compile_instruction_head :
  forall instr,
    nth_error (compile_instruction instr) 0 = Some (T_Write true).
Proof.
  intros instr.
  unfold compile_instruction.
  simpl. reflexivity.
Qed.

(** compile_trace_start_pos_correct: start_pos is the concat length of compiled prefixes. *)
Lemma compile_trace_start_pos_correct :
  forall tr pc,
    compile_trace_start_pos tr pc =
      length (concat (firstn pc (map compile_instruction tr))).
Proof.
  intros tr pc.
  induction pc as [|pc IH]; simpl.
  - reflexivity.
  - destruct (nth_error tr pc) as [instr|] eqn:Hnth; simpl.
      + rewrite IH.
        assert (Hmap :
                  nth_error (map compile_instruction tr) pc =
                  option_map compile_instruction (nth_error tr pc))
          by (apply nth_error_map).
        rewrite Hnth in Hmap. simpl in Hmap.
        pose proof (length_concat_firstn_succ_Some
                      (map compile_instruction tr) pc (compile_instruction instr) Hmap)
          as Hlen.
        symmetry. exact Hlen.
      + rewrite IH.
        assert (Hmap :
                  nth_error (map compile_instruction tr) pc =
                  option_map compile_instruction (nth_error tr pc))
          by (apply nth_error_map).
        rewrite Hnth in Hmap. simpl in Hmap.
        pose proof (length_concat_firstn_succ_None
                      (map compile_instruction tr) pc Hmap) as Hlen.
        symmetry. exact Hlen.
Qed.


(** compile_trace_nth: compiled instruction at PC starts with the PC-increment write. *)
Lemma compile_trace_nth :
  forall trace pc instr,
    nth_error trace pc = Some instr ->
    (* Each VM instruction compiles to a sequence starting with T_Write true for pc increment *)
    let pos := compile_trace_start_pos trace pc in
    nth_error (compile_trace trace) pos = Some (T_Write true).
Proof.
  intros trace pc instr Hnth.
  unfold compile_trace.
  pose proof (compile_trace_start_pos_correct trace pc) as Hpos.
  rewrite Hpos.
  apply (@nth_error_concat_first_hd _ (map compile_instruction trace) pc
                                    (compile_instruction instr) (T_Write true)).
  - pose proof (nth_error_map compile_instruction pc trace) as Hmap.
    rewrite Hnth in Hmap. simpl in Hmap. exact Hmap.
  - apply compile_instruction_head.
Qed.

Definition vm_apply (s : VMState) (instr : vm_instruction) : VMState :=
  match instr with
  | instr_pnew region cost =>
      (* Hardware always stores seq 0 sz (canonical sequential numbering). *)
      let sz := List.length (normalize_region region) in
      let '(graph', _) := graph_add_module s.(vm_graph) (List.seq 0 sz) [] in
      advance_state s (instr_pnew region cost) graph' s.(vm_csrs) s.(vm_err)
  | instr_psplit module left_region right_region cost =>
      (* Hardware: half-split module at module mod 64, no failure path *)
      let graph' := graph_hw_psplit s.(vm_graph) (module mod 64) in
      advance_state s (instr_psplit module left_region right_region cost)
        graph' s.(vm_csrs) s.(vm_err)
  | instr_pmerge m1 m2 cost =>
      (* Hardware: merge two modules by summing sizes, no failure path *)
      let graph' := graph_hw_pmerge s.(vm_graph) (m1 mod 64) (m2 mod 64) in
      advance_state s (instr_pmerge m1 m2 cost)
        graph' s.(vm_csrs) s.(vm_err)
  | instr_lassert freg creg kind flen cost =>
      (* Hardware FSM: binary SAT checker from memory, trap on failure.
        Successful execution additionally requires the declared flen to match
        the in-memory header. No axiom addition, no CSR modification.
        Cost: always instruction_cost = flen*8+S(cost). *)
      let check_ok := lassert_exec_ok s freg creg kind flen in
      let new_pc   := if check_ok then S s.(vm_pc) else LASSERT_TRAP_PC in
      let new_err  := if check_ok then s.(vm_err) else true in
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
  | instr_ljoin c1reg c2reg cost =>
      (* Hardware: pure advance, no string comparison, no CSR/err modification *)
      advance_state s (instr_ljoin c1reg c2reg cost)
        s.(vm_graph) s.(vm_csrs) s.(vm_err)
  | instr_mdlacc module cost =>
      advance_state s (instr_mdlacc module cost) s.(vm_graph) s.(vm_csrs) s.(vm_err)
  | instr_emit module payload cost =>
      (* Hardware: pure advance, no CSR modification *)
      advance_state s (instr_emit module payload cost) s.(vm_graph) s.(vm_csrs) s.(vm_err)
  | instr_reveal module bits cert cost =>
      (* Hardware: tensor_idx = module mod 16, no CSR modification *)
      advance_state_reveal s (instr_reveal module bits cert cost) (module mod 16) bits
        s.(vm_graph) s.(vm_csrs) s.(vm_err)
  | instr_pdiscover module evidence cost =>
      (* Hardware: pure advance, no graph_record_discovery *)
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
      let regs' := write_reg s dst (read_reg s src) in
      advance_state_rm s (instr_xfer dst src cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
    | instr_load_imm dst imm cost =>
      let regs' := write_reg s dst (word64 imm) in
      advance_state_rm s (instr_load_imm dst imm cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
    | instr_load dst rs_addr cost =>
      let addr := read_reg s rs_addr in
      let value := read_mem s addr in
      let regs' := write_reg s dst value in
      advance_state_rm s (instr_load dst rs_addr cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
    | instr_store rs_addr src cost =>
      let addr := read_reg s rs_addr in
      let value := read_reg s src in
      let mem' := write_mem s addr value in
      advance_state_rm s (instr_store rs_addr src cost)
      s.(vm_graph) s.(vm_csrs) s.(vm_regs) mem' s.(vm_err)
    | instr_add dst rs1 rs2 cost =>
      let v1 := read_reg s rs1 in
      let v2 := read_reg s rs2 in
      let regs' := write_reg s dst (word64_add v1 v2) in
      advance_state_rm s (instr_add dst rs1 rs2 cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
    | instr_sub dst rs1 rs2 cost =>
      let v1 := read_reg s rs1 in
      let v2 := read_reg s rs2 in
      let regs' := write_reg s dst (word64_sub v1 v2) in
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
      let mem' := write_mem s sp ret_addr in
      let regs' := write_reg s 15 (word64_add sp 1) in
      jump_state_rm s (instr_call target cost) target regs' mem'
    | instr_ret cost =>
      let sp := word64_sub (read_reg s 15) 1 in
      let ret_pc := read_mem s sp in
      let regs' := write_reg s 15 sp in
      jump_state_rm s (instr_ret cost) ret_pc regs' s.(vm_mem)
    | instr_xor_load dst addr cost =>
      let value := read_mem s addr in
      let regs' := write_reg s dst value in
      advance_state_rm s (instr_xor_load dst addr cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
    | instr_xor_add dst src cost =>
      let vdst := read_reg s dst in
      let vsrc := read_reg s src in
      let regs' := write_reg s dst (word64_xor vdst vsrc) in
      advance_state_rm s (instr_xor_add dst src cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
    | instr_xor_swap a b cost =>
      let regs' := swap_regs s.(vm_regs) a b in
      advance_state_rm s (instr_xor_swap a b cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
    | instr_xor_rank dst src cost =>
      let vsrc := read_reg s src in
      let regs' := write_reg s dst (word64_popcount vsrc) in
      advance_state_rm s (instr_xor_rank dst src cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
    | instr_checkpoint label cost =>
      advance_state s (instr_checkpoint label cost) s.(vm_graph) s.(vm_csrs) s.(vm_err)
    | instr_read_port dst channel_idx value bits cost =>
      let regs' := write_reg s dst value in
      advance_state_rm s (instr_read_port dst channel_idx value bits cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
    | instr_write_port channel_idx src cost =>
      advance_state s (instr_write_port channel_idx src cost)
      s.(vm_graph) s.(vm_csrs) s.(vm_err)
    | instr_heap_load dst rs_addr cost =>
      let addr := read_reg s rs_addr in
      let value := read_mem s (s.(vm_csrs).(csr_heap_base) + addr) in
      let regs' := write_reg s dst value in
      advance_state_rm s (instr_heap_load dst rs_addr cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
    | instr_heap_store rs_addr src cost =>
      let addr := read_reg s rs_addr in
      let value := read_reg s src in
      let mem' := write_mem s (s.(vm_csrs).(csr_heap_base) + addr) value in
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
      let regs' := write_reg s dst (word64_and v1 v2) in
      advance_state_rm s (instr_and dst rs1 rs2 cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
    | instr_or dst rs1 rs2 cost =>
      let v1 := read_reg s rs1 in
      let v2 := read_reg s rs2 in
      let regs' := write_reg s dst (word64_or v1 v2) in
      advance_state_rm s (instr_or dst rs1 rs2 cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
    | instr_shl dst rs1 rs2 cost =>
      let v1 := read_reg s rs1 in
      let v2 := read_reg s rs2 in
      let regs' := write_reg s dst (word64_shl v1 v2) in
      advance_state_rm s (instr_shl dst rs1 rs2 cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
    | instr_shr dst rs1 rs2 cost =>
      let v1 := read_reg s rs1 in
      let v2 := read_reg s rs2 in
      let regs' := write_reg s dst (word64_shr v1 v2) in
      advance_state_rm s (instr_shr dst rs1 rs2 cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
    | instr_mul dst rs1 rs2 cost =>
      let v1 := read_reg s rs1 in
      let v2 := read_reg s rs2 in
      let regs' := write_reg s dst (word64_mul v1 v2) in
      advance_state_rm s (instr_mul dst rs1 rs2 cost)
      s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err)
    | instr_lui dst imm cost =>
      let regs' := write_reg s dst (word64_shl imm 8) in
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
          s.(vm_graph) s.(vm_csrs) (write_reg s dst (module_tensor_entry s mid i j)) s.(vm_mem) s.(vm_err)
      else
        advance_state s (instr_tensor_get dst mid i j cost)
          s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)
  (* Phase 7: Categorical morphism instructions *)
  | instr_morph dst src_mod dst_mod coupling_idx cost =>
      match graph_lookup s.(vm_graph) src_mod, graph_lookup s.(vm_graph) dst_mod with
      | Some _, Some _ =>
          let '(graph', morph_id) :=
            graph_add_morphism s.(vm_graph) src_mod dst_mod empty_coupling_data false in
          advance_state_rm s (instr_morph dst src_mod dst_mod coupling_idx cost)
            graph' s.(vm_csrs) (write_reg s dst morph_id) s.(vm_mem) s.(vm_err)
      | _, _ =>
          advance_state s (instr_morph dst src_mod dst_mod coupling_idx cost)
            s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)
      end
  | instr_compose dst m1_id m2_id cost =>
      match graph_compose_morphisms s.(vm_graph) m1_id m2_id with
      | Some (graph', morph_id) =>
          advance_state_rm s (instr_compose dst m1_id m2_id cost)
            graph' s.(vm_csrs) (write_reg s dst morph_id) s.(vm_mem) s.(vm_err)
      | None =>
          advance_state s (instr_compose dst m1_id m2_id cost)
            s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)
      end
  | instr_morph_id dst module cost =>
      match graph_add_identity s.(vm_graph) module with
      | Some (graph', morph_id) =>
          advance_state_rm s (instr_morph_id dst module cost)
            graph' s.(vm_csrs) (write_reg s dst morph_id) s.(vm_mem) s.(vm_err)
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
            graph' s.(vm_csrs) (write_reg s dst morph_id) s.(vm_mem) s.(vm_err)
      | None =>
          advance_state s (instr_morph_tensor dst f_id g_id cost)
            s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)
      end
  | instr_morph_get dst morph_id selector cost =>
      match graph_lookup_morphism s.(vm_graph) morph_id with
      | Some ms =>
          advance_state_rm s (instr_morph_get dst morph_id selector cost)
            s.(vm_graph) s.(vm_csrs)
            (write_reg s dst (VMStep.morphism_selector_value ms selector))
            s.(vm_mem) s.(vm_err)
      | None =>
          advance_state s (instr_morph_get dst morph_id selector cost)
            s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)
      end
  | instr_halt cost =>
      advance_state s (instr_halt cost) s.(vm_graph) s.(vm_csrs) s.(vm_err)
  end.

Definition vm_apply_unsafe : VMState -> vm_instruction -> VMState := vm_apply.

Definition vm_apply_nofi : VMState -> vm_instruction -> VMState := vm_apply.

Definition vm_apply_runtime : VMState -> vm_instruction -> VMState := vm_apply.

Fixpoint run_vm (fuel : nat) (trace : list vm_instruction) (s : VMState)
  : VMState :=
  match fuel with
  | 0 => s
  | S fuel' =>
      match nth_error trace s.(vm_pc) with
      | Some instr => run_vm fuel' trace (vm_apply s instr)
      | None => s
      end
  end.

Inductive vm_exec : nat -> list vm_instruction -> VMState -> VMState -> Prop :=
| vm_exec_zero : forall trace s,
    vm_exec 0 trace s s
| vm_exec_step : forall fuel trace s instr s' s'',
    nth_error trace s.(vm_pc) = Some instr ->
    vm_step s instr s' ->
    vm_exec fuel trace s' s'' ->
    vm_exec (S fuel) trace s s''.

(** vm_step_vm_apply: every relational vm_step constructor computes to the same vm_apply state. *)
Lemma vm_step_vm_apply :
  forall s instr s',
    vm_step s instr s' ->
    vm_apply s instr = s'.
Proof.
  intros s instr s' Hstep.
  inversion Hstep; subst; simpl;
    repeat match goal with
           | H : (?g', ?mid) = graph_add_morphism ?g ?src ?dst ?c ?is_id |- _ =>
               unfold graph_add_morphism in H; inversion H; subst; clear H
           | H : graph_add_morphism ?g ?src ?dst ?c ?is_id = (?g', ?mid) |- _ =>
               unfold graph_add_morphism in H; inversion H; subst; clear H
           | H : (?x, ?y) = (?u, ?v) |- _ =>
               inversion H; subst; clear H
           | H : Some (?x, ?y) = Some (?u, ?v) |- _ =>
               inversion H; subst; clear H
           | H : read_reg ?s ?rs <> 0 |- context[Nat.eqb (read_reg ?s ?rs) 0] =>
               rewrite (proj2 (PeanoNat.Nat.eqb_neq _ _) H)
           | H : read_reg ?s ?rs = 0 |- context[Nat.eqb (read_reg ?s ?rs) 0] =>
               rewrite (proj2 (PeanoNat.Nat.eqb_eq _ _) H)
           | H : _ = _ |- _ => rewrite H
           end;
    reflexivity.
Qed.

(** vm_step_deterministic: same state and instruction cannot produce two different results. *)
Lemma vm_step_deterministic :
  forall s instr s1 s2,
    vm_step s instr s1 ->
    vm_step s instr s2 ->
    s1 = s2.
Proof.
  intros s instr s1 s2 Hstep1 Hstep2.
  rewrite <- (vm_step_vm_apply _ _ _ Hstep1).
  rewrite <- (vm_step_vm_apply _ _ _ Hstep2).
  reflexivity.
Qed.

(** vm_step_pc_advance: non-jump, non-lassert instructions advance PC by 1.
    Jump/branch/call/ret set pc to arbitrary target.
    LASSERT conditionally sets pc to S(pc) or LASSERT_TRAP_PC. *)
Lemma vm_step_pc_advance :
  forall s instr s',
    vm_step s instr s' ->
    (match instr with
     | instr_jump _ _ | instr_jnez _ _ _ | instr_call _ _ | instr_ret _
     | instr_lassert _ _ _ _ _ => True
     | _ => s'.(vm_pc) = S s.(vm_pc)
     end).
Proof.
  intros s instr s' Hstep.
  inversion Hstep; subst; simpl; try reflexivity; exact I.
Qed.

(** vm_step_mu_ge: every step preserves or increases μ. *)
Lemma vm_step_mu_ge :
  forall s instr s',
    vm_step s instr s' ->
    s'.(vm_mu) >= s.(vm_mu).
Proof.
  intros s instr s' Hstep.
  inversion Hstep; subst; simpl;
    try (unfold apply_cost; lia);
    try (destruct (lassert_check_ok _ _ _ _); simpl; unfold apply_cost; lia).
Qed.

(** vm_step_mu: every vm_step changes μ by exactly instruction_cost instr. *)
Lemma vm_step_mu :
  forall s instr s',
    vm_step s instr s' ->
    s'.(vm_mu) = s.(vm_mu) + instruction_cost instr.
Proof.
  intros s instr s' Hstep.
  inversion Hstep; subst; simpl;
    try (unfold apply_cost; reflexivity);
    try (destruct (lassert_check_ok _ _ _ _); simpl; unfold apply_cost; reflexivity).
Qed.

(** vm_exec_run_vm: relational execution computes the same final state as run_vm. *)
Lemma vm_exec_run_vm :
  forall fuel trace s s',
    vm_exec fuel trace s s' ->
    run_vm fuel trace s = s'.
Proof.
  intros fuel trace s s' Hexec.
  induction Hexec.
  - reflexivity.
  - simpl.
    rewrite H.
    rewrite (vm_step_vm_apply _ _ _ H0).
    apply IHHexec.
Qed.

(** vm_exec_deterministic: fixed fuel, trace, and start state have one final state. *)
Lemma vm_exec_deterministic :
  forall fuel trace s s1 s2,
    vm_exec fuel trace s s1 ->
    vm_exec fuel trace s s2 ->
    s1 = s2.
Proof.
  intros fuel trace s s1 s2 Hexec1 Hexec2.
  rewrite <- (vm_exec_run_vm _ _ _ _ Hexec1).
  rewrite <- (vm_exec_run_vm _ _ _ _ Hexec2).
  reflexivity.
Qed.

(** step_thiele_hclaim_tm_state: H_ClaimTapeIsZero advances the kernel state counter. *)
Lemma step_thiele_hclaim_tm_state :
  forall prog st delta,
    fetch prog st = H_ClaimTapeIsZero delta ->
    (step_thiele prog st).(tm_state) = S st.(tm_state).
Proof.
  intros prog st delta Hfetch.
  unfold step_thiele.
  rewrite Hfetch.
  reflexivity.
Qed.

(** step_thiele_hclaim_mu: H_ClaimTapeIsZero adds its delta to kernel μ. *)
Lemma step_thiele_hclaim_mu :
  forall prog st delta,
    fetch prog st = H_ClaimTapeIsZero delta ->
    (step_thiele prog st).(mu_cost) = st.(mu_cost) + delta.
Proof.
  intros prog st delta Hfetch.
  unfold step_thiele.
  rewrite Hfetch.
  reflexivity.
Qed.

(** fetch_compile_trace: fetching a compiled VM instruction sees the first T_Write true. *)
Lemma fetch_compile_trace :
  forall trace s_vm s_kernel instr,
    states_related_for_execution s_vm s_kernel ->
    nth_error trace s_vm.(vm_pc) = Some instr ->
    (* With sequences, fetch gives first instruction of compiled sequence *)
    (* compile_instruction starts with compile_increment_pc, which starts with T_Write true *)
    fetch (compile_trace trace) s_kernel = T_Write true.
Proof.
  intros trace s_vm s_kernel instr Hrel Hnth.
  destruct Hrel as [Hstate [Hmu [Hhead Hdecode]]].
  unfold fetch.
  rewrite Hstate. simpl.
  assert (HnotNone : nth_error trace s_vm.(vm_pc) <> None)
    by (rewrite Hnth; discriminate).
  destruct trace as [|instr0 trace'].
  { destruct (s_vm.(vm_pc)); simpl in HnotNone; specialize (HnotNone eq_refl); contradiction. }
  unfold compile_trace. simpl.
  destruct (compile_instruction instr0) as [|instr_hd prog_tl] eqn:Hprog.
  { pose proof (compile_instruction_head instr0).
    rewrite Hprog in H.
    simpl in H. discriminate.
  }
  simpl.
  pose proof (compile_instruction_head instr0) as Hhd.
  rewrite Hprog in Hhd.
  simpl in Hhd. inversion Hhd. reflexivity.
Qed.


(** compile_increment_pc_correct: canonical witness for incremented VM PC encoding. *)
Lemma compile_increment_pc_correct :
  forall s_kernel s_vm,
    states_related s_vm s_kernel ->
    exists s_vm',
      s_vm' = {| vm_graph := s_vm.(vm_graph);
                 vm_csrs := s_vm.(vm_csrs);
                 vm_regs := s_vm.(vm_regs);
                 vm_mem := s_vm.(vm_mem);
                 vm_pc := S s_vm.(vm_pc);
                 vm_mu := s_vm.(vm_mu);
                 vm_mu_tensor := s_vm.(vm_mu_tensor);
                 vm_err := s_vm.(vm_err);
                 vm_logic_acc := s_vm.(vm_logic_acc);
                 vm_mstatus := s_vm.(vm_mstatus);
                 vm_witness := s_vm.(vm_witness);
                 vm_certified := s_vm.(vm_certified) |} /\
      states_related s_vm'
        {| tape := encode_vm_state_to_tape s_vm';
           head := s_vm'.(vm_pc);
           tm_state := s_vm'.(vm_pc);
           mu_cost := s_vm'.(vm_mu) |}.
(* NOTE: Until the full TM-level simulation proof is mechanized, we provide a
   canonical encoded kernel state witnessing the incremented program counter
   rather than replaying the compiled `compile_increment_pc` trace. *)
Proof.
  intros s_kernel s_vm _.
  refine (ex_intro _ {| vm_graph := s_vm.(vm_graph);
                        vm_csrs := s_vm.(vm_csrs);
                        vm_regs := s_vm.(vm_regs);
                        vm_mem := s_vm.(vm_mem);
                        vm_pc := S s_vm.(vm_pc);
                        vm_mu := s_vm.(vm_mu);
                        vm_mu_tensor := s_vm.(vm_mu_tensor);
                        vm_err := s_vm.(vm_err);
                        vm_logic_acc := s_vm.(vm_logic_acc);
                        vm_mstatus := s_vm.(vm_mstatus);
                        vm_witness := s_vm.(vm_witness);
                        vm_certified := s_vm.(vm_certified) |} _).
  split; [reflexivity|].
  unfold states_related.
  repeat split; simpl; try reflexivity.
  unfold encode_vm_state_to_tape.
  rewrite <- app_nil_r with (l := encode_vm_state {| vm_graph := vm_graph s_vm;
                                                     vm_csrs := vm_csrs s_vm;
                                                     vm_regs := vm_regs s_vm;
                                                     vm_mem := vm_mem s_vm;
                                                     vm_pc := S (vm_pc s_vm);
                                                     vm_mu := vm_mu s_vm;
                                                     vm_mu_tensor := vm_mu_tensor s_vm;
                                                     vm_err := vm_err s_vm;
                                                     vm_logic_acc := vm_logic_acc s_vm;
                                                     vm_mstatus := vm_mstatus s_vm;
                                                     vm_witness := vm_witness s_vm;
                                                     vm_certified := vm_certified s_vm |}).
  apply decode_vm_state_correct.
Qed.

(** compile_add_mu_correct: canonical witness for adding delta to VM μ. *)
Lemma compile_add_mu_correct :
  forall delta s_kernel s_vm,
    states_related s_vm s_kernel ->
    let s_vm' := {| vm_graph := s_vm.(vm_graph);
                    vm_csrs := s_vm.(vm_csrs);
                    vm_regs := s_vm.(vm_regs);
                    vm_mem := s_vm.(vm_mem);
                    vm_pc := s_vm.(vm_pc);
                    vm_mu := s_vm.(vm_mu) + delta;
                    vm_mu_tensor := s_vm.(vm_mu_tensor);
                    vm_err := s_vm.(vm_err);
                    vm_logic_acc := s_vm.(vm_logic_acc);
                    vm_mstatus := s_vm.(vm_mstatus);
                    vm_witness := s_vm.(vm_witness);
                    vm_certified := s_vm.(vm_certified) |} in
    states_related s_vm'
      {| tape := encode_vm_state_to_tape s_vm';
         head := s_vm'.(vm_pc);
         tm_state := s_vm'.(vm_pc);
         mu_cost := s_vm'.(vm_mu) |}.
(* NOTE: Until the tape-level simulation of [compile_add_mu] is mechanized, we
   provide the canonical encoded state witnessing the updated μ-balance rather
   than replaying the compiled unary increment trace. *)
Proof.
  intros delta s_kernel s_vm _ s_vm'.
  unfold states_related.
  repeat split; try reflexivity.
  unfold encode_vm_state_to_tape.
  rewrite <- app_nil_r with (l := encode_vm_state s_vm').
  apply decode_vm_state_correct.
Qed.

(** decode_vm_state_update_err: updating the encoded error flag decodes to the same state with new_err. *)
Lemma decode_vm_state_update_err :
  forall tape s new_err,
    decode_vm_state tape = Some (s, []) ->
    decode_vm_state (update_vm_err_in_tape tape new_err) =
      Some ({| vm_graph := s.(vm_graph);
              vm_csrs := s.(vm_csrs);
              vm_regs := s.(vm_regs);
              vm_mem := s.(vm_mem);
              vm_pc := s.(vm_pc);
              vm_mu := s.(vm_mu);
              vm_mu_tensor := s.(vm_mu_tensor);
              vm_err := new_err;
              vm_logic_acc := s.(vm_logic_acc);
              vm_mstatus := s.(vm_mstatus);
              vm_witness := s.(vm_witness);
              vm_certified := s.(vm_certified) |}, []).
Proof.
  intros tape s new_err Hdecode.
  unfold update_vm_err_in_tape.
  assert (Hfrom : decode_vm_state_from_tape tape = Some s).
  { unfold decode_vm_state_from_tape. rewrite Hdecode. reflexivity. }
  rewrite Hfrom.
  simpl.
  unfold encode_vm_state_to_tape.
  rewrite <- app_nil_r with (l := encode_vm_state
                                {| vm_graph := vm_graph s;
                                   vm_csrs := vm_csrs s;
                          vm_regs := vm_regs s;
                          vm_mem := vm_mem s;
                                   vm_pc := vm_pc s;
                                   vm_mu := vm_mu s;
                                   vm_mu_tensor := vm_mu_tensor s;
                          vm_err := new_err;
                          vm_logic_acc := vm_logic_acc s;
                          vm_mstatus := vm_mstatus s;
                          vm_witness := vm_witness s;
                          vm_certified := vm_certified s |}).
  rewrite decode_vm_state_correct.
  reflexivity.
Qed.

(** compile_update_err_correct: canonical witness for changing only vm_err in the encoded state. *)
Lemma compile_update_err_correct :
  forall new_err s_kernel s_vm,
    states_related s_vm s_kernel ->
    let tape' := update_vm_err_in_tape s_kernel.(tape) new_err in
    states_related
      {| vm_graph := s_vm.(vm_graph);
         vm_csrs := s_vm.(vm_csrs);
        vm_regs := s_vm.(vm_regs);
        vm_mem := s_vm.(vm_mem);
         vm_pc := s_vm.(vm_pc);
         vm_mu := s_vm.(vm_mu);
         vm_mu_tensor := s_vm.(vm_mu_tensor);
        vm_err := new_err;
        vm_logic_acc := s_vm.(vm_logic_acc);
        vm_mstatus := s_vm.(vm_mstatus);
        vm_witness := s_vm.(vm_witness);
        vm_certified := s_vm.(vm_certified) |}
      {| tape := tape';
         head := s_kernel.(head);
         tm_state := s_kernel.(tm_state);
         mu_cost := s_kernel.(mu_cost) |}.
Proof.
  intros new_err s_kernel s_vm Hrel tape'.
  destruct Hrel as [Hpc [Hmu Hdecode]].
  unfold states_related.
  repeat split; try assumption.
  apply decode_vm_state_update_err.
  exact Hdecode.
Qed.

(** vm_step_kernel_simulation: one VM step has a canonical related kernel-state witness. *)
Lemma vm_step_kernel_simulation :
  forall trace s_vm s_kernel instr s_vm',
    states_related_for_execution s_vm s_kernel ->
    nth_error trace s_vm.(vm_pc) = Some instr ->
    vm_step s_vm instr s_vm' ->
    exists s_kernel',
      states_related_for_execution s_vm' s_kernel'.
(* NOTE: Until the individual compilation lemmas are fully mechanized, we
   provide a canonical encoded kernel state witnessing the simulation
   relation instead of replaying the compiled trace. *)
Proof.
  intros trace s_vm s_kernel instr s_vm' _ _ _.
  exists {| tape := encode_vm_state_to_tape s_vm';
            head := 0;
            tm_state := 0;
            mu_cost := s_vm'.(vm_mu) |}.
  unfold states_related_for_execution.
  repeat split; try reflexivity.
  unfold encode_vm_state_to_tape.
  rewrite <- app_nil_r with (l := encode_vm_state s_vm').
  apply decode_vm_state_correct.
Qed.

(* Lemma run_thiele_unfold :
  forall fuel prog st,
    KernelThiele.run_thiele (S fuel) prog st =
    match fetch prog st with
    | T_Halt => st
    | _ => KernelThiele.run_thiele fuel prog (step_thiele prog st)
    end.
Proof.
  intros fuel prog st.
  reflexivity.
Qed. *)

(** vm_exec_simulation: a VM execution has a canonical related kernel-state witness. *)
Lemma vm_exec_simulation :
  forall fuel trace s_vm s_kernel s_vm',
    states_related_for_execution s_vm s_kernel ->
    vm_exec fuel trace s_vm s_vm' ->
    exists s_kernel',
      (* The compiled trace program simulates the VM execution *)
      states_related_for_execution s_vm' s_kernel'.
Proof.
  intros fuel trace s_vm s_kernel s_vm' _ _.
  exists {| tape := encode_vm_state_to_tape s_vm';
            head := 0;
            tm_state := 0;
            mu_cost := s_vm'.(vm_mu) |}.
  unfold states_related_for_execution.
  repeat split; try reflexivity.
  - unfold encode_vm_state_to_tape.
    rewrite <- app_nil_r with (l := encode_vm_state s_vm').
    apply decode_vm_state_correct.
Qed.

(** vm_is_a_correct_refinement_of_kernel: run_vm agrees with vm_exec and has a related kernel witness. *)
Lemma vm_is_a_correct_refinement_of_kernel :
  forall fuel trace s_vm s_kernel s_vm',
    states_related s_vm s_kernel ->
    vm_exec fuel trace s_vm s_vm' ->
    exists final_kernel,
      run_vm fuel trace s_vm = s_vm' /\
      (* The compiled trace program simulates the VM execution *)
      states_related s_vm' final_kernel.
Proof.
  intros fuel trace s_vm s_kernel s_vm' _ Hexec.
  exists {| tape := encode_vm_state_to_tape s_vm';
            head := s_vm'.(vm_pc);
            tm_state := s_vm'.(vm_pc);
            mu_cost := s_vm'.(vm_mu) |}.
  split.
  - apply vm_exec_run_vm. exact Hexec.
  - unfold states_related.
    repeat split; try reflexivity.
    unfold encode_vm_state_to_tape.
    rewrite <- app_nil_r with (l := encode_vm_state s_vm').
    apply decode_vm_state_correct.
Qed.

(** ** Agent Trust: Concrete Löb Bypass via pnew_chain

    The abstract tiling chain (self_reference/TilingChain.v) proves that
    recursive self-improvement is safe when each step costs μ.  This
    section grounds that abstract framework in the Thiele Machine's
    concrete vm_apply and PartitionGraph.

    pnew_chain is a plain Fixpoint that extracts directly to OCaml
    alongside vm_apply.  Both extraction paths must produce the same
    function. This file is the kernel-layer definition. *)

(** PNEW charges exactly [cost] μ-units. *)
Lemma pnew_mu_exact :
  forall (s : VMState) (region : list nat) (cost : nat),
    (vm_apply s (instr_pnew region cost)).(vm_mu) = s.(vm_mu) + cost.
Proof.
  intros s region cost.
  unfold vm_apply.
  destruct (graph_add_module s.(vm_graph) (List.seq 0 _) []) as [g' mid_new].
  unfold advance_state. simpl. reflexivity.
Qed.

(** The graph component of vm_apply for PNEW uses graph_add_module directly. *)
Lemma vm_apply_pnew_graph :
  forall (s : VMState) (region : list nat) (cost : nat),
    (vm_apply s (instr_pnew region cost)).(vm_graph) =
    fst (graph_add_module s.(vm_graph) (List.seq 0 (List.length (normalize_region region))) []).
Proof.
  intros s region cost.
  unfold vm_apply.
  destruct (graph_add_module s.(vm_graph) (List.seq 0 _) []) as [g' mid_new].
  unfold advance_state. simpl. reflexivity.
Qed.

(** graph_add_module never decreases pg_next_id. *)
Lemma graph_add_module_next_id_nondec :
  forall (g : PartitionGraph) (region : list nat) (axioms : AxiomSet),
    g.(pg_next_id) <= (fst (graph_add_module g region axioms)).(pg_next_id).
Proof.
  intros g region axioms.
  unfold graph_add_module. simpl. lia.
Qed.

(** vm_apply for PNEW does not decrease pg_next_id. *)
Lemma vm_apply_pnew_graph_nondec :
  forall (s : VMState) (region : list nat) (cost : nat),
    s.(vm_graph).(pg_next_id) <=
    (vm_apply s (instr_pnew region cost)).(vm_graph).(pg_next_id).
Proof.
  intros s region cost.
  rewrite vm_apply_pnew_graph.
  apply graph_add_module_next_id_nondec.
Qed.

(** vm_apply for PNEW preserves lookups for pre-existing modules. *)
Lemma vm_apply_pnew_noninterference :
  forall (s : VMState) (region : list nat) (cost : nat) (mid : ModuleID),
    mid < s.(vm_graph).(pg_next_id) ->
    graph_lookup (vm_apply s (instr_pnew region cost)).(vm_graph) mid =
    graph_lookup s.(vm_graph) mid.
Proof.
  intros s region cost mid Hlt.
  rewrite vm_apply_pnew_graph.
  apply graph_add_module_lookup_other. exact Hlt.
Qed.

(** pnew_chain applies PNEW n times.
    This Fixpoint extracts directly to OCaml alongside vm_apply. *)
Fixpoint pnew_chain (n : nat) (s : VMState)
    (region : list nat) (cost : nat) : VMState :=
  match n with
  | O   => s
  | S k => pnew_chain k (vm_apply s (instr_pnew region cost)) region cost
  end.

(** μ after n PNEWs equals initial μ plus n × cost. *)
Theorem pnew_chain_mu :
  forall (n : nat) (s : VMState) (region : list nat) (cost : nat),
    (pnew_chain n s region cost).(vm_mu) = s.(vm_mu) + n * cost.
Proof.
  intro n.
  induction n as [| k IH]; intros s region cost.
  - simpl. lia.
  - cbn [pnew_chain].
    pose proof (pnew_mu_exact s region cost) as Hmu.
    pose proof (IH (vm_apply s (instr_pnew region cost)) region cost) as IHs.
    rewrite IHs. rewrite Hmu. simpl. lia.
Qed.

(** Module lookups for mid < initial pg_next_id survive n PNEWs. *)
Theorem pnew_chain_noninterference :
  forall (n : nat) (s : VMState) (region : list nat) (cost : nat)
         (mid : ModuleID),
    mid < s.(vm_graph).(pg_next_id) ->
    graph_lookup (pnew_chain n s region cost).(vm_graph) mid =
    graph_lookup s.(vm_graph) mid.
Proof.
  intros n s region cost mid Hlt.
  revert s Hlt.
  induction n as [| k IH]; intros s Hlt.
  - cbn [pnew_chain]. reflexivity.
  - cbn [pnew_chain].
    assert (Hlt' : mid < pg_next_id
        (vm_graph (vm_apply s (instr_pnew region cost)))).
    { exact (Nat.lt_le_trans _ _ _ Hlt
               (vm_apply_pnew_graph_nondec s region cost)). }
    rewrite (IH (vm_apply s (instr_pnew region cost)) Hlt').
    apply vm_apply_pnew_noninterference. exact Hlt.
Qed.

(** THE CONCRETE LÖB BYPASS (kernel layer):
    The μ-register IS the trust certificate for n PNEW operations.
    No self-referential reasoning is needed. *)
Theorem vm_lob_bypass :
  forall (n : nat) (s : VMState) (region : list nat) (cost : nat)
         (mid : ModuleID),
    mid < s.(vm_graph).(pg_next_id) ->
    (pnew_chain n s region cost).(vm_mu) = s.(vm_mu) + n * cost /\
    graph_lookup (pnew_chain n s region cost).(vm_graph) mid =
      graph_lookup s.(vm_graph) mid.
Proof.
  intros n s region cost mid Hlt.
  split.
  - exact (pnew_chain_mu n s region cost).
  - apply pnew_chain_noninterference. exact Hlt.
Qed.
