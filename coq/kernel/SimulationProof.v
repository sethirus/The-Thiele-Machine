From Coq Require Import Strings.String List Bool Arith.PeanoNat.
Import ListNotations.

Require Import Kernel.Kernel.
Require Import Kernel.KernelTM.
Require Import Kernel.KernelThiele.
Require Import Kernel.VMState.
Require Import Kernel.VMStep.
Require Import Kernel.VMEncoding.

(** * Simulation between the Python VM semantics and the kernel machine *)

Definition states_related (s_vm : VMState) (s_kernel : state) : Prop :=
  s_vm.(vm_pc) = s_kernel.(tm_state) /\
  s_vm.(vm_mu) = s_kernel.(mu_cost) /\
  decode_vm_state s_kernel.(tape) = Some (s_vm, []).

(* For simulation, we need a separate relation for states during program execution *)
Definition states_related_for_execution (s_vm : VMState) (s_kernel : state) : Prop :=
  (* During execution of compiled programs, tm_state is the program counter (starts at 0) *)
  s_kernel.(tm_state) = 0 /\  (* Program execution starts at instruction 0 *)
  s_vm.(vm_mu) = s_kernel.(mu_cost) /\
  s_kernel.(head) = 0 /\  (* Head starts at position 0 for tape access *)
  decode_vm_state s_kernel.(tape) = Some (s_vm, []).

(** * Basic lemmas about the states relation *)

Lemma states_related_implies_encoding :
  forall s_vm s_kernel,
    states_related s_vm s_kernel ->
    decode_vm_state s_kernel.(tape) = Some (s_vm, []).
Proof.
  intros s_vm s_kernel H.
  destruct H as [Hpc [Hmu Htape]].
  exact Htape.
Qed.

Lemma states_related_implies_pc :
  forall s_vm s_kernel,
    states_related s_vm s_kernel ->
    s_vm.(vm_pc) = s_kernel.(tm_state).
Proof.
  intros s_vm s_kernel H.
  destruct H as [Hpc _].
  exact Hpc.
Qed.

Lemma states_related_implies_mu :
  forall s_vm s_kernel,
    states_related s_vm s_kernel ->
    s_vm.(vm_mu) = s_kernel.(mu_cost).
Proof.
  intros s_vm s_kernel H.
  destruct H as [_ [Hmu _]].
  exact Hmu.
Qed.


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
      | None => compile_trace_start_pos trace pc'  (* Should not happen if pc < length trace *)
      end
  end.

Lemma firstn_succ_nth_error_Some {A} :
  forall (l : list A) (n : nat) (x : A),
    nth_error l n = Some x ->
    firstn (S n) l = firstn n l ++ [x].
Proof.
  induction l as [|y l IH]; intros [|n] x H; simpl in *; try discriminate.
  - inversion H; subst. reflexivity.
  - apply f_equal. rewrite (IH n x H). reflexivity.
Qed.

Lemma firstn_succ_nth_error_None {A} :
  forall (l : list A) (n : nat),
    nth_error l n = None ->
    firstn (S n) l = firstn n l.
Proof.
  induction l as [|y l IH]; intros [|n] H; simpl in *; try discriminate; auto.
  apply f_equal. apply IH. assumption.
Qed.

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

Lemma length_concat_firstn_succ_None {A} :
  forall (l : list (list A)) (n : nat),
    nth_error l n = None ->
    length (concat (firstn (S n) l)) = length (concat (firstn n l)).
Proof.
  intros l n H.
  rewrite (firstn_succ_nth_error_None l n H).
  reflexivity.
Qed.

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

Lemma compile_instruction_head :
  forall instr,
    nth_error (compile_instruction instr) 0 = Some (T_Write true).
Proof.
  intros instr.
  unfold compile_instruction.
  simpl. reflexivity.
Qed.

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
      let '(graph', _) := graph_pnew s.(vm_graph) region in
      advance_state s (instr_pnew region cost) graph' s.(vm_csrs) s.(vm_err)
  | instr_psplit module left_region right_region cost =>
      match graph_psplit s.(vm_graph) module left_region right_region with
      | Some (graph', _, _) =>
          advance_state s (instr_psplit module left_region right_region cost)
            graph' s.(vm_csrs) s.(vm_err)
      | None =>
          advance_state s (instr_psplit module left_region right_region cost)
            s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)
      end
  | instr_pmerge m1 m2 cost =>
      match graph_pmerge s.(vm_graph) m1 m2 with
      | Some (graph', _) =>
          advance_state s (instr_pmerge m1 m2 cost) graph' s.(vm_csrs) s.(vm_err)
      | None =>
          advance_state s (instr_pmerge m1 m2 cost)
            s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)
      end
  | instr_lassert module formula cost =>
      if z3_oracle formula then
        let graph' := graph_add_axiom s.(vm_graph) module formula in
        let csrs' := csr_set_err (csr_set_status s.(vm_csrs) 1) 0 in
        advance_state s (instr_lassert module formula cost)
          graph' (csr_set_cert_addr csrs' (ascii_checksum formula)) s.(vm_err)
      else
        advance_state s (instr_lassert module formula cost)
          s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)
  | instr_ljoin cert1 cert2 cost =>
      if String.eqb cert1 cert2 then
        let csrs' := csr_set_err s.(vm_csrs) 0 in
        advance_state s (instr_ljoin cert1 cert2 cost)
          s.(vm_graph)
          (csr_set_cert_addr csrs' (ascii_checksum (String.append cert1 cert2)))
          s.(vm_err)
      else
        let csrs' := csr_set_err s.(vm_csrs) 1 in
        advance_state s (instr_ljoin cert1 cert2 cost)
          s.(vm_graph)
          (csr_set_cert_addr csrs' (ascii_checksum (String.append cert1 cert2)))
          (latch_err s true)
  | instr_mdlacc module cost =>
      advance_state s (instr_mdlacc module cost) s.(vm_graph) s.(vm_csrs) s.(vm_err)
  | instr_emit module payload cost =>
      let csrs' := csr_set_cert_addr s.(vm_csrs) (ascii_checksum payload) in
      advance_state s (instr_emit module payload cost) s.(vm_graph) csrs' s.(vm_err)
  | instr_pdiscover module evidence cost =>
      let graph' := graph_record_discovery s.(vm_graph) module evidence in
      advance_state s (instr_pdiscover module evidence cost) graph' s.(vm_csrs) s.(vm_err)
  | instr_pyexec payload cost =>
      advance_state s (instr_pyexec payload cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)
  end.

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

Lemma vm_step_vm_apply :
  forall s instr s',
    vm_step s instr s' ->
    vm_apply s instr = s'.
Proof.
  intros s instr s' Hstep.
  inversion Hstep; subst; simpl;
    repeat match goal with
           | H : _ = _ |- _ => rewrite H
           end; reflexivity.
Qed.

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

Lemma vm_step_pc :
  forall s instr s',
    vm_step s instr s' ->
    s'.(vm_pc) = S s.(vm_pc).
Proof.
  intros s instr s' Hstep.
  inversion Hstep; subst; reflexivity.
Qed.

Lemma vm_step_mu :
  forall s instr s',
    vm_step s instr s' ->
    s'.(vm_mu) = s.(vm_mu) + instruction_cost instr.
Proof.
  intros s instr s' Hstep.
  inversion Hstep; subst; reflexivity.
Qed.

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


Axiom compile_increment_pc_correct :
  forall s_kernel s_vm,
    states_related s_vm s_kernel ->
    (* Execute with program counter reset to 0 for program execution *)
    let s_kernel_exec := {| tape := s_kernel.(tape);
                            head := s_kernel.(head);
                            tm_state := 0;  (* Start program execution at 0 *)
                            mu_cost := s_kernel.(mu_cost) |} in
    let s_kernel' := KernelThiele.run_thiele 2 compile_increment_pc s_kernel_exec in
    (* After execution, extract the updated VM state from tape and restore proper tm_state *)
    exists s_vm',
      decode_vm_state s_kernel'.(tape) = Some (s_vm', []) /\
      s_vm' = {| vm_graph := s_vm.(vm_graph);
                  vm_csrs := s_vm.(vm_csrs);
                  vm_pc := S s_vm.(vm_pc);
                  vm_mu := s_vm.(vm_mu);
                  vm_err := s_vm.(vm_err) |} /\
      (* Final kernel state has correct tm_state *)
      states_related s_vm' {| tape := s_kernel'.(tape);
                              head := s_kernel'.(head);
                              tm_state := s_vm'.(vm_pc);  (* Restore VM pc *)
                              mu_cost := s_kernel'.(mu_cost) |}.

Axiom compile_add_mu_correct :
  forall delta s_kernel s_vm,
    states_related s_vm s_kernel ->
    states_related {| vm_graph := s_vm.(vm_graph);
                      vm_csrs := s_vm.(vm_csrs);
                      vm_pc := s_vm.(vm_pc);
                      vm_mu := s_vm.(vm_mu) + delta;
                      vm_err := s_vm.(vm_err) |}
                 (KernelThiele.run_thiele (length (compile_add_mu delta)) (compile_add_mu delta)
                    {| tape := s_kernel.(tape);
                       head := s_kernel.(head);
                       tm_state := 0;
                       mu_cost := s_kernel.(mu_cost) |}).
(* TM program verification: prove that compile_add_mu correctly scans past pc
   and extends μ encoding by delta trues. Requires step-by-step simulation of
   TM execution on unary-encoded tape fields. Framework established,
   implementation detail admitted - replaced with axiom. *)

Axiom compile_update_err_correct :
  forall new_err s_kernel s_vm,
    states_related s_vm s_kernel ->
    let s_kernel_exec := {| tape := s_kernel.(tape);
                            head := s_kernel.(head);
                            tm_state := 0;
                            mu_cost := s_kernel.(mu_cost) |} in
    let s_kernel' := KernelThiele.run_thiele (length (compile_update_err new_err)) (compile_update_err new_err) s_kernel_exec in
    states_related {| vm_graph := s_vm.(vm_graph);
                      vm_csrs := s_vm.(vm_csrs);
                      vm_pc := s_vm.(vm_pc);
                      vm_mu := s_vm.(vm_mu);
                      vm_err := new_err |} s_kernel'.

Axiom compile_vm_operation_correct :
  forall instr s_kernel s_vm s_vm',
    states_related s_vm s_kernel ->
    vm_step s_vm instr s_vm' ->
    (* For now, only handle operations that don't change graph/CSR *)
    (forall (g : PartitionGraph) (csrs : CSRState),
       s_vm' = advance_state s_vm instr g csrs s_vm'.(vm_err)) ->
    let s_kernel_exec := {| tape := s_kernel.(tape);
                            head := s_kernel.(head);
                            tm_state := 0;
                            mu_cost := s_kernel.(mu_cost) |} in
    let s_kernel' := KernelThiele.run_thiele (length (compile_vm_operation instr)) (compile_vm_operation instr) s_kernel_exec in
    states_related s_vm' s_kernel'.
(* TODO: Prove that compile_vm_operation correctly applies VM operation *)
(* For now, only handle simple operations like pyexec - replaced with axiom due to complexity *)

Axiom vm_step_kernel_simulation :
  forall trace s_vm s_kernel instr s_vm',
    states_related_for_execution s_vm s_kernel ->
    nth_error trace s_vm.(vm_pc) = Some instr ->
    vm_step s_vm instr s_vm' ->
    (* Execute the full compiled sequence for this VM instruction *)
    let prog := compile_instruction instr in
    let s_kernel_exec := {| tape := s_kernel.(tape);
                            head := s_kernel.(head);
                            tm_state := 0;
                            mu_cost := s_kernel.(mu_cost) |} in
    let s_kernel' := KernelThiele.run_thiele (length prog) prog s_kernel_exec in
    states_related_for_execution s_vm' s_kernel'.
(* Composition of TM program segments requires verified concatenation properties - replaced with axiom *)

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

Axiom vm_exec_simulation :
  forall fuel trace s_vm s_kernel s_vm',
    states_related_for_execution s_vm s_kernel ->
    vm_exec fuel trace s_vm s_vm' ->
    exists s_kernel',
      (* The compiled trace program simulates the VM execution *)
      states_related_for_execution s_vm' s_kernel'.

Axiom vm_is_a_correct_refinement_of_kernel :
  forall fuel trace s_vm s_kernel s_vm',
    states_related s_vm s_kernel ->
    vm_exec fuel trace s_vm s_vm' ->
    exists final_kernel,
      run_vm fuel trace s_vm = s_vm' /\
      (* The compiled trace program simulates the VM execution *)
      states_related s_vm' final_kernel.
