(** BitSearchEntitlement: a run that searches a supplied candidate list.

    The candidates are every n-bit value. The hidden value sits in the
    machine's memory, one bit per word. The run asks k questions: question i
    loads bit i of the hidden value, takes the answer through a port (READ_PORT,
    a paid step that writes the answer into the receipts), compares the answer
    with the bit it loaded, and jumps to a trap that latches the error flag when
    they differ. After the last question the run allocates a module, makes its
    identity arrow and asserts it, which raises the assertion channel.

    What is proved, for n <= 64 and k <= n (with k >= 1 for strict entitlement):
    - the run on the world whose hidden value is v ends with the error flag down
      exactly when v agrees with the answers on the k asked bits;
    - after j questions, exactly 2^(n-j) of the 2^n candidates are still being
      searched;
    - the posterior (the candidates that agree with the answers) has 2^(n-k)
      members, and every candidate is represented by the survivor that agrees
      with it on the n-k bits that were never asked;
    - with the honest answers for a hidden value, all eight hypotheses of
      structural_entitlement_representation hold, so k <= mu rise, and the
      record SoundStructuralShortcut is inhabited for every such n, k and value.
    *)

From Coq Require Import String Arith.PeanoNat Lia Bool NArith List.
Import ListNotations.
Open Scope string_scope.

From Kernel Require Import VMState VMStep.
From Kernel Require Import MuInitiality.
From Kernel Require Import SimulationProof MuLedgerConservation.
From Kernel Require Import RevelationRequirement.
From Kernel Require Import NoFreeInsight InformationGainToStrengthening MuShannonBridge.
From Kernel Require Import HonestNoFI_TheoremsWithoutAssumptions.

Import RevelationProof.

(** * The program *)

(** Question i with answer b: load bit i of the hidden value into r2, take the
    answer b through port 0 into r5, xor them, trap if they differ. *)
Definition question (trap i : nat) (b : bool) : list vm_instruction :=
  [ instr_load_imm 3 i 0;
    instr_load 2 3 0;
    instr_read_port 5 0 (Nat.b2n b) 1 0;
    instr_xor_add 2 5 0;
    instr_jnez 2 trap 0 ].

Fixpoint questions (trap i : nat) (answers : list bool) : list vm_instruction :=
  match answers with
  | [] => []
  | b :: rest => question trap i b ++ questions trap (S i) rest
  end.

Definition search_suffix : list vm_instruction :=
  [ instr_pnew [0] 0;
    instr_morph_id 0 0 0;
    instr_morph_assert 1 "found" "cert" 0 ].

Definition search_trap (k : nat) : nat := 5 * k + 4.
Definition search_end (k : nat) : nat := 5 * k + 5.

(** The whole program for an answer list: the questions, the assertion suffix,
    a jump past the end, and the trap (a CHSH trial with an out-of-range bit,
    which latches the error flag). *)
Definition search_prog (answers : list bool) : list vm_instruction :=
  questions (search_trap (length answers)) 0 answers ++
  search_suffix ++
  [ instr_jump (search_end (length answers)) 0;
    instr_chsh_trial 2 0 0 0 0 ].

Definition search_fuel (k : nat) : nat := 5 * k + 5.

(** * The candidates *)

Definition mem_of (v : list bool) : list nat :=
  map Nat.b2n v ++ repeat 0 (MEM_SIZE - length v).

(** The world whose hidden value is v: the initial state with v in memory. *)
Definition world (v : list bool) : VMState :=
  {| vm_graph := init_graph;
     vm_csrs := init_csrs;
     vm_regs := repeat 0 REG_COUNT;
     vm_mem := mem_of v;
     vm_pc := 0;
     vm_mu := 0;
     vm_mu_tensor := vm_mu_tensor_default;
     vm_err := false;
     vm_logic_acc := 0;
     vm_mstatus := 0;
     vm_witness := witness_counts_zero;
     vm_certified := false |}.

Fixpoint all_bits (n : nat) : list (list bool) :=
  match n with
  | 0 => [[]]
  | S n' => map (cons false) (all_bits n') ++ map (cons true) (all_bits n')
  end.

(** The supplied prior: one world per n-bit value. *)
Definition prior (n : nat) : list VMState := map world (all_bits n).

(** * Basic lemmas *)

Lemma questions_length : forall trap i answers,
  length (questions trap i answers) = 5 * length answers.
Proof.
  intros trap i answers. revert i.
  induction answers as [|b rest IH]; intros i; simpl; [reflexivity|].
  rewrite IH. lia.
Qed.

Lemma nth_error_questions : forall answers trap i j t,
  j < length answers -> t < 5 ->
  nth_error (questions trap i answers) (t + 5 * j) =
  nth_error (question trap (i + j) (nth j answers false)) t.
Proof.
  induction answers as [|b rest IH]; intros trap i j t Hj Ht; simpl in Hj; [lia|].
  change (questions trap i (b :: rest)) with (question trap i b ++ questions trap (S i) rest).
  destruct j as [|j].
  - rewrite Nat.mul_0_r, Nat.add_0_r, Nat.add_0_r.
    rewrite nth_error_app1 by (simpl; lia). reflexivity.
  - rewrite nth_error_app2 by (simpl; lia).
    replace (t + 5 * S j - length (question trap i b)) with (t + 5 * j)
      by (simpl; lia).
    rewrite IH by lia. simpl. replace (i + S j) with (S i + j) by lia.
    reflexivity.
Qed.

Lemma nth_error_prog_question : forall answers j t,
  j < length answers -> t < 5 ->
  nth_error (search_prog answers) (t + 5 * j) =
  nth_error (question (search_trap (length answers)) j (nth j answers false)) t.
Proof.
  intros answers j t Hj Ht. unfold search_prog.
  rewrite nth_error_app1 by (rewrite questions_length; lia).
  apply nth_error_questions; assumption.
Qed.

Lemma nth_error_prog_tail : forall answers t,
  nth_error (search_prog answers) (t + 5 * length answers) =
  nth_error (search_suffix ++
    [ instr_jump (search_end (length answers)) 0;
      instr_chsh_trial 2 0 0 0 0 ]) t.
Proof.
  intros answers t. unfold search_prog.
  rewrite nth_error_app2 by (rewrite questions_length; lia).
  rewrite questions_length. f_equal. lia.
Qed.

Lemma search_prog_length : forall answers,
  length (search_prog answers) = search_end (length answers).
Proof.
  intros answers. unfold search_prog, search_end.
  rewrite !app_length, questions_length. simpl. lia.
Qed.

Lemma run_vm_step_at : forall f p s pc i,
  s.(vm_pc) = pc -> nth_error p pc = Some i ->
  run_vm (S f) p s = run_vm f p (vm_apply s i).
Proof. intros f p s pc i Hpc H. simpl. rewrite Hpc, H. reflexivity. Qed.

Lemma cse_step_at : forall f p s pc i,
  s.(vm_pc) = pc -> nth_error p pc = Some i ->
  cert_setter_executions (S f) p s =
  (if is_cert_setterb i then 1 else 0) + cert_setter_executions f p (vm_apply s i).
Proof. intros f p s pc i Hpc H. simpl. rewrite Hpc, H. reflexivity. Qed.

Lemma run_vm_step_some : forall f p s i,
  nth_error p s.(vm_pc) = Some i ->
  run_vm (S f) p s = run_vm f p (vm_apply s i).
Proof. intros f p s i H. simpl. rewrite H. reflexivity. Qed.

Lemma cse_step_some : forall f p s i,
  nth_error p s.(vm_pc) = Some i ->
  cert_setter_executions (S f) p s =
  (if is_cert_setterb i then 1 else 0) + cert_setter_executions f p (vm_apply s i).
Proof. intros f p s i H. simpl. rewrite H. reflexivity. Qed.

Lemma run_vm_stopped : forall f p s,
  nth_error p s.(vm_pc) = None -> run_vm f p s = s.
Proof. intros [|f] p s H; simpl; [reflexivity|]. rewrite H. reflexivity. Qed.

Lemma cse_stopped : forall f p s,
  nth_error p s.(vm_pc) = None -> cert_setter_executions f p s = 0.
Proof. intros [|f] p s H; simpl; [reflexivity|]. rewrite H. reflexivity. Qed.

Lemma run_vm_add : forall a b p s,
  run_vm (a + b) p s = run_vm b p (run_vm a p s).
Proof.
  induction a as [|a IH]; intros b p s; simpl; [reflexivity|].
  destruct (nth_error p (vm_pc s)) as [i|] eqn:Hn.
  - apply IH.
  - symmetry. apply run_vm_stopped. exact Hn.
Qed.

Lemma cse_add : forall a b p s,
  cert_setter_executions (a + b) p s =
  cert_setter_executions a p s + cert_setter_executions b p (run_vm a p s).
Proof.
  induction a as [|a IH]; intros b p s; simpl; [reflexivity|].
  destruct (nth_error p (vm_pc s)) as [i|] eqn:Hn.
  - rewrite IH. lia.
  - rewrite cse_stopped by exact Hn. reflexivity.
Qed.

Lemma word64_small : forall x, x < 64 -> word64 x = x.
Proof.
  intros x Hx. unfold word64, word64_mask.
  rewrite N.land_ones.
  rewrite N.mod_small.
  - apply Nat2N.id.
  - apply N.lt_trans with 64%N; [lia|]. vm_compute. reflexivity.
Qed.

Lemma word64_b2n : forall x : bool, word64 (Nat.b2n x) = Nat.b2n x.
Proof. intros []; vm_compute; reflexivity. Qed.

Lemma word64_xor_b2n : forall x b : bool,
  word64 (word64_xor (Nat.b2n x) (Nat.b2n b)) = Nat.b2n (xorb x b).
Proof. intros [] []; vm_compute; reflexivity. Qed.

Lemma nth_mem_of : forall v j,
  j < length v -> nth j (mem_of v) 0 = Nat.b2n (nth j v false).
Proof.
  intros v j Hj. unfold mem_of.
  rewrite app_nth1 by (rewrite map_length; exact Hj).
  change 0 with (Nat.b2n false). apply map_nth.
Qed.

Lemma mem_of_length : forall v, length v <= MEM_SIZE -> length (mem_of v) = MEM_SIZE.
Proof.
  intros v Hv. unfold mem_of. rewrite app_length, map_length, repeat_length. lia.
Qed.

(** * The invariant the run keeps while it searches *)

Definition searching (v : list bool) (s : VMState) (pc : nat) : Prop :=
  s.(vm_graph) = init_graph /\ s.(vm_csrs) = init_csrs /\
  s.(vm_mem) = mem_of v /\ s.(vm_pc) = pc /\ s.(vm_err) = false /\
  length s.(vm_regs) = REG_COUNT.

Lemma world_searching : forall v, searching v (world v) 0.
Proof. intros v. unfold searching, world. simpl. repeat split. Qed.

Ltac regs16 regs Hlen :=
  let r0 := fresh "r" in let r1 := fresh "r" in let r2 := fresh "r" in
  let r3 := fresh "r" in let r4 := fresh "r" in let r5 := fresh "r" in
  let r6 := fresh "r" in let r7 := fresh "r" in let r8 := fresh "r" in
  let r9 := fresh "r" in let r10 := fresh "r" in let r11 := fresh "r" in
  let r12 := fresh "r" in let r13 := fresh "r" in let r14 := fresh "r" in
  let r15 := fresh "r" in let rest := fresh "rest" in
  destruct regs as [|r0 [|r1 [|r2 [|r3 [|r4 [|r5 [|r6 [|r7 [|r8 [|r9 [|r10
    [|r11 [|r12 [|r13 [|r14 [|r15 rest]]]]]]]]]]]]]]]];
  simpl in Hlen; try discriminate Hlen;
  destruct rest; simpl in Hlen; try discriminate Hlen.

(** One question, run on a state that is still searching at that question. *)
Lemma question_run : forall answers v s j,
  j < length answers -> length answers <= length v -> length v <= 64 ->
  searching v s (5 * j) ->
  let p := search_prog answers in
  let s' := run_vm 5 p s in
  s'.(vm_mu) = s.(vm_mu) + 2 /\
  cert_setter_executions 5 p s = 1 /\
  (nth j v false = nth j answers false -> searching v s' (5 * (S j))) /\
  (nth j v false <> nth j answers false ->
     searching v s' (search_trap (length answers))).
Proof.
  intros answers v s j Hj Hav Hv64 [Hg [Hc [Hm [Hpc [He Hlen]]]]] p s'.
  assert (Hq : forall t, t < 5 ->
    nth_error p (t + 5 * j) =
    nth_error (question (search_trap (length answers)) j (nth j answers false)) t)
    by (intros t Ht; apply nth_error_prog_question; assumption).
  destruct s as [g c regs mem pc mu mt err la ms wit cert]; simpl in Hg, Hc, Hm, Hpc, He, Hlen.
  subst g c mem pc err.
  unfold REG_COUNT in Hlen. regs16 regs Hlen.
  assert (Hj64 : j < 64) by lia.
  assert (Hjv : j < length v) by lia.
  subst s' p.
  set (x := nth j v false) in *.
  set (b := nth j answers false) in *.
  set (P := search_prog answers) in *.
  set (T := search_trap (length answers)) in *.
  assert (H0 : nth_error P (0 + 5 * j) = Some (instr_load_imm 3 j 0)) by (rewrite Hq by lia; reflexivity).
  assert (H1 : nth_error P (1 + 5 * j) = Some (instr_load 2 3 0)) by (rewrite Hq by lia; reflexivity).
  assert (H2 : nth_error P (2 + 5 * j) = Some (instr_read_port 5 0 (Nat.b2n b) 1 0)) by (rewrite Hq by lia; reflexivity).
  assert (H3 : nth_error P (3 + 5 * j) = Some (instr_xor_add 2 5 0)) by (rewrite Hq by lia; reflexivity).
  assert (H4 : nth_error P (4 + 5 * j) = Some (instr_jnez 2 T 0)) by (rewrite Hq by lia; reflexivity).
  clear Hq.
  erewrite (run_vm_step_at 4 P _ (0 + 5 * j) _ _ H0) by reflexivity.
  erewrite (cse_step_at 4 P _ (0 + 5 * j) _ _ H0) by reflexivity.
  erewrite (run_vm_step_at 3 P _ (1 + 5 * j) _ _ H1) by reflexivity.
  erewrite (cse_step_at 3 P _ (1 + 5 * j) _ _ H1) by reflexivity.
  erewrite (run_vm_step_at 2 P _ (2 + 5 * j) _ _ H2) by reflexivity.
  erewrite (cse_step_at 2 P _ (2 + 5 * j) _ _ H2) by reflexivity.
  erewrite (run_vm_step_at 1 P _ (3 + 5 * j) _ _ H3) by reflexivity.
  erewrite (cse_step_at 1 P _ (3 + 5 * j) _ _ H3) by reflexivity.
  erewrite (run_vm_step_at 0 P _ (4 + 5 * j) _ _ H4) by reflexivity.
  erewrite (cse_step_at 0 P _ (4 + 5 * j) _ _ H4) by reflexivity.
  simpl run_vm. simpl cert_setter_executions.
  assert (Hmi : mem_index j = j)
    by (unfold mem_index, MEM_SIZE; apply Nat.mod_small; lia).
  unfold vm_apply, read_reg, write_reg, read_mem, reg_index, REG_COUNT.
  cbn -[word64 word64_xor mem_of mem_index Nat.b2n].
  rewrite !(word64_small j Hj64).
  rewrite Hmi.
  rewrite (nth_mem_of v j Hjv). fold x.
  rewrite !word64_b2n, !word64_xor_b2n.
  clearbody x b. clear H0 H1 H2 H3 H4.
  unfold searching, search_trap in *.
  destruct x, b; cbn;
    repeat split; intros; try congruence; try lia.
  Unshelve. all: reflexivity.
Qed.


(** * The run, question by question *)

Definition agree_upto (j : nat) (v answers : list bool) : Prop :=
  forall i, i < j -> nth i v false = nth i answers false.

(** While the hidden value agrees with the answers, the run keeps searching:
    after j questions it is at question j, it has paid 2 per question, and it
    has executed j paid steps. *)
Lemma run_prefix : forall answers v j,
  j <= length answers -> length answers <= length v -> length v <= 64 ->
  agree_upto j v answers ->
  let p := search_prog answers in
  searching v (run_vm (5 * j) p (world v)) (5 * j) /\
  (run_vm (5 * j) p (world v)).(vm_mu) = 2 * j /\
  cert_setter_executions (5 * j) p (world v) = j.
Proof.
  intros answers v j Hj Hav Hv64 Hagree p.
  induction j as [|j IH].
  - simpl. split; [apply world_searching|]. split; reflexivity.
  - assert (Hagree' : agree_upto j v answers)
      by (intros i Hi; apply Hagree; lia).
    destruct (IH ltac:(lia) Hagree') as [Hs [Hmu Hcse]].
    destruct (question_run answers v (run_vm (5 * j) p (world v)) j
                ltac:(lia) Hav Hv64 Hs) as [Hmu' [Hcse' [Hok _]]].
    fold p in Hmu', Hcse', Hok.
    replace (5 * S j) with (5 * j + 5) in * by lia.
    rewrite run_vm_add, cse_add.
    split; [apply Hok; apply Hagree; lia|].
    split; [rewrite Hmu', Hmu; lia|].
    rewrite Hcse, Hcse'. lia.
Qed.

Lemma prog_stopped : forall answers s,
  s.(vm_pc) = search_end (length answers) ->
  nth_error (search_prog answers) s.(vm_pc) = None.
Proof.
  intros answers s H. rewrite H. apply nth_error_None.
  rewrite search_prog_length. lia.
Qed.

(** The trap: a searching state at the trap address latches the error flag and
    leaves the program. *)
Lemma trap_run : forall answers v s f,
  searching v s (search_trap (length answers)) ->
  let s' := run_vm (S f) (search_prog answers) s in
  s'.(vm_err) = true /\ s'.(vm_pc) = search_end (length answers).
Proof.
  intros answers v s f [Hg [Hc [Hm [Hpc [He Hlen]]]]] s'.
  assert (Ht : nth_error (search_prog answers) (4 + 5 * length answers) =
               Some (instr_chsh_trial 2 0 0 0 0))
    by (rewrite nth_error_prog_tail; reflexivity).
  subst s'.
  rewrite (run_vm_step_at f _ s (4 + 5 * length answers) _)
    by (try rewrite Hpc; unfold search_trap; try lia; exact Ht).
  rewrite run_vm_stopped.
  - destruct s; simpl in *; subst. split; [reflexivity|].
    unfold search_trap, search_end. lia.
  - apply prog_stopped. destruct s; simpl in *; subst.
    unfold search_trap, search_end. lia.
Qed.

(** The assertion suffix: from a searching state after the last question, the
    run raises the assertion channel, keeps the error flag down, pays 1 more,
    and leaves the program. *)
Lemma suffix_run : forall answers v s f,
  searching v s (5 * length answers) ->
  let p := search_prog answers in
  let s' := run_vm (4 + f) p s in
  s'.(vm_err) = false /\ s'.(vm_csrs).(csr_cert_addr) <> 0 /\
  s'.(vm_pc) = search_end (length answers) /\
  s'.(vm_mu) = s.(vm_mu) + 1 /\
  cert_setter_executions (4 + f) p s = 1.
Proof.
  intros answers v s f [Hg [Hc [Hm [Hpc [He Hlen]]]]] p s'.
  set (k := length answers) in *.
  assert (Ht : forall t, nth_error p (t + 5 * k) =
    nth_error (search_suffix ++ [instr_jump (search_end k) 0; instr_chsh_trial 2 0 0 0 0]) t)
    by (intros t; apply nth_error_prog_tail).
  assert (H0 : nth_error p (0 + 5 * k) = Some (instr_pnew [0] 0)) by (rewrite Ht; reflexivity).
  assert (H1 : nth_error p (1 + 5 * k) = Some (instr_morph_id 0 0 0)) by (rewrite Ht; reflexivity).
  assert (H2 : nth_error p (2 + 5 * k) = Some (instr_morph_assert 1 "found" "cert" 0))
    by (rewrite Ht; reflexivity).
  assert (H3 : nth_error p (3 + 5 * k) = Some (instr_jump (search_end k) 0))
    by (rewrite Ht; reflexivity).
  clear Ht.
  destruct s as [g c regs mem pc mu mt err la ms wit cert];
    simpl in Hg, Hc, Hm, Hpc, He, Hlen. subst g c mem pc err.
  subst s'.
  change (4 + f) with (S (S (S (S f)))).
  erewrite (run_vm_step_at _ p _ (0 + 5 * k) _ _ H0) by reflexivity.
  erewrite (cse_step_at _ p _ (0 + 5 * k) _ _ H0) by reflexivity.
  erewrite (run_vm_step_at _ p _ (1 + 5 * k) _ _ H1) by reflexivity.
  erewrite (cse_step_at _ p _ (1 + 5 * k) _ _ H1) by reflexivity.
  erewrite (run_vm_step_at _ p _ (2 + 5 * k) _ _ H2) by reflexivity.
  erewrite (cse_step_at _ p _ (2 + 5 * k) _ _ H2) by reflexivity.
  erewrite (run_vm_step_at _ p _ (3 + 5 * k) _ _ H3) by reflexivity.
  erewrite (cse_step_at _ p _ (3 + 5 * k) _ _ H3) by reflexivity.
  Unshelve. 2-9: reflexivity.
  rewrite run_vm_stopped, cse_stopped.
  - split; [vm_compute; reflexivity|].
    split; [vm_compute; intro Hx; discriminate Hx|].
    split; [reflexivity|].
    split; [|reflexivity].
    rewrite !vm_apply_mu. simpl. lia.
  - apply prog_stopped. reflexivity.
  - apply prog_stopped. reflexivity.
Qed.

Lemma first_mismatch : forall k v answers,
  agree_upto k v answers \/
  exists j, j < k /\ agree_upto j v answers /\ nth j v false <> nth j answers false.
Proof.
  induction k as [|k IH]; intros v answers.
  - left. intros i Hi. lia.
  - destruct (IH v answers) as [Hall|[j [Hj [Ha Hn]]]].
    + destruct (bool_dec (nth k v false) (nth k answers false)) as [Heq|Hneq].
      * left. intros i Hi. destruct (Nat.eq_dec i k) as [->|Hik]; [exact Heq|].
        apply Hall. lia.
      * right. exists k. repeat split; [lia|exact Hall|exact Hneq].
    + right. exists j. repeat split; [lia|exact Ha|exact Hn].
Qed.

(** When the hidden value agrees with every answer, the run ends error-free with
    the assertion channel raised, having paid 2 per question plus 1, and having
    executed k + 1 paid steps. *)
Theorem search_run_agrees : forall answers v,
  length answers <= length v -> length v <= 64 ->
  agree_upto (length answers) v answers ->
  let k := length answers in
  let p := search_prog answers in
  let s' := run_vm (search_fuel k) p (world v) in
  s'.(vm_err) = false /\ s'.(vm_csrs).(csr_cert_addr) <> 0 /\
  s'.(vm_mu) = 2 * k + 1 /\
  cert_setter_executions (search_fuel k) p (world v) = k + 1.
Proof.
  intros answers v Hav Hv64 Hagree k p s'.
  destruct (run_prefix answers v k ltac:(lia) Hav Hv64 Hagree)
    as [Hs [Hmu Hcse]].
  fold k p in Hs, Hmu, Hcse.
  subst s'. unfold search_fuel.
  replace (5 * k + 5) with (5 * k + (4 + 1)) by lia.
  rewrite run_vm_add, cse_add.
  destruct (suffix_run answers v (run_vm (5 * k) p (world v)) 1 Hs)
    as [He [Hc [_ [Hmu' Hcse']]]].
  fold p in He, Hc, Hmu', Hcse'.
  repeat split; try assumption.
  - rewrite Hmu', Hmu. lia.
  - rewrite Hcse, Hcse'. lia.
Qed.

(** When the hidden value disagrees with answer j (and agrees before it), the
    run jumps to the trap at question j and ends with the error flag latched. *)
Theorem search_run_mismatch : forall answers v j,
  j < length answers -> length answers <= length v -> length v <= 64 ->
  agree_upto j v answers -> nth j v false <> nth j answers false ->
  forall f, 5 * j + 6 <= f ->
  (run_vm f (search_prog answers) (world v)).(vm_err) = true /\
  (run_vm f (search_prog answers) (world v)).(vm_pc) =
    search_end (length answers).
Proof.
  intros answers v j Hj Hav Hv64 Hagree Hneq f Hf.
  set (p := search_prog answers).
  destruct (run_prefix answers v j ltac:(lia) Hav Hv64 Hagree) as [Hs _].
  fold p in Hs.
  destruct (question_run answers v (run_vm (5 * j) p (world v)) j
              Hj Hav Hv64 Hs) as [_ [_ [_ Hbad]]].
  specialize (Hbad Hneq). fold p in Hbad.
  replace f with (5 * j + (5 + S (f - 5 * j - 6))) by lia.
  rewrite run_vm_add, run_vm_add.
  exact (trap_run answers v _ _ Hbad).
Qed.

(** The genuine link: the run on the world whose hidden value is v ends with
    the error flag down exactly when v agrees with the answers on the asked
    bits. *)
Theorem search_certifies_iff_agrees : forall answers v,
  length answers <= length v -> length v <= 64 ->
  (run_vm (search_fuel (length answers)) (search_prog answers) (world v)).(vm_err)
    = false <->
  agree_upto (length answers) v answers.
Proof.
  intros answers v Hav Hv64. split.
  - intro He.
    destruct (first_mismatch (length answers) v answers) as [Hall|[j [Hj [Ha Hn]]]];
      [exact Hall|].
    destruct (search_run_mismatch answers v j Hj Hav Hv64 Ha Hn
                (search_fuel (length answers))) as [Herr _].
    + unfold search_fuel. lia.
    + rewrite He in Herr. discriminate.
  - intro Hagree. apply (search_run_agrees answers v Hav Hv64 Hagree).
Qed.

(** * Progressive elimination *)

(** A candidate is still being searched after j questions when the run on its
    world is at question j with the error flag down. *)
Definition still_searching (answers : list bool) (j : nat) (s : VMState) : bool :=
  let s' := run_vm (5 * j) (search_prog answers) s in
  Nat.eqb s'.(vm_pc) (5 * j) && negb s'.(vm_err).

Lemma still_searching_iff : forall answers v j,
  j <= length answers -> length answers <= length v -> length v <= 64 ->
  still_searching answers j (world v) = true <-> agree_upto j v answers.
Proof.
  intros answers v j Hj Hav Hv64. unfold still_searching. split.
  - intro H. apply andb_true_iff in H. destruct H as [Hpc He].
    apply Nat.eqb_eq in Hpc.
    destruct (first_mismatch j v answers) as [Hall|[i [Hi [Ha Hn]]]];
      [exact Hall|exfalso].
    set (p := search_prog answers) in *.
    destruct (run_prefix answers v i ltac:(lia) Hav Hv64 Ha) as [Hs _].
    fold p in Hs.
    destruct (question_run answers v (run_vm (5 * i) p (world v)) i
                ltac:(lia) Hav Hv64 Hs) as [_ [_ [_ Hbad]]].
    specialize (Hbad Hn). fold p in Hbad.
    destruct (Nat.eq_dec j (S i)) as [->|Hji].
    + replace (5 * S i) with (5 * i + 5) in Hpc by lia.
      rewrite run_vm_add in Hpc.
      destruct Hbad as [_ [_ [_ [Hp _]]]]. rewrite Hp in Hpc.
      unfold search_trap in Hpc. lia.
    + replace (5 * j) with (5 * i + (5 + S (5 * j - 5 * i - 6))) in Hpc by lia.
      rewrite run_vm_add, run_vm_add in Hpc.
      destruct (trap_run answers v _ (5 * j - 5 * i - 6) Hbad) as [_ Hp].
      fold p in Hp. rewrite Hp in Hpc. unfold search_end in Hpc. lia.
  - intro Hagree.
    destruct (run_prefix answers v j Hj Hav Hv64 Hagree) as [[_ [_ [_ [Hpc [He _]]]]] _].
    rewrite Hpc, He, Nat.eqb_refl. reflexivity.
Qed.

(** * Counting the candidates *)

Lemma all_bits_length : forall n, length (all_bits n) = 2 ^ n.
Proof.
  induction n as [|n IH]; simpl; [reflexivity|].
  rewrite app_length, !map_length, IH. lia.
Qed.

Lemma in_all_bits : forall n v, In v (all_bits n) <-> length v = n.
Proof.
  induction n as [|n IH]; intros v; simpl.
  - split.
    + intros [<-|[]]. reflexivity.
    + intro H. destruct v; [left; reflexivity|discriminate].
  - rewrite in_app_iff, !in_map_iff. split.
    + intros [[w [<- Hw]]|[w [<- Hw]]]; simpl; f_equal; apply IH; exact Hw.
    + intro H. destruct v as [|[] w]; simpl in H; [discriminate| |].
      * right. exists w. split; [reflexivity|]. apply IH. lia.
      * left. exists w. split; [reflexivity|]. apply IH. lia.
Qed.

Fixpoint agreesb (c v : list bool) : bool :=
  match c, v with
  | [], _ => true
  | x :: c', y :: v' => Bool.eqb x y && agreesb c' v'
  | _ :: _, [] => false
  end.

Lemma agreesb_spec : forall c v,
  length c <= length v ->
  agreesb c v = true <-> agree_upto (length c) v c.
Proof.
  induction c as [|x c IH]; intros v Hl; simpl.
  - split; [intros _ i Hi; lia|reflexivity].
  - destruct v as [|y v]; simpl in Hl; [lia|].
    rewrite andb_true_iff, IH by lia. split.
    + intros [Hxy Hrest] i Hi. destruct i as [|i]; simpl.
      * apply eqb_prop in Hxy. symmetry. exact Hxy.
      * apply Hrest. lia.
    + intro H. split.
      * apply eqb_true_iff. symmetry. exact (H 0 ltac:(lia)).
      * intros i Hi. exact (H (S i) ltac:(lia)).
Qed.

Lemma filter_app' : forall {A} (f : A -> bool) l1 l2,
  filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
  intros A f l1 l2. induction l1 as [|a l1 IH]; simpl; [reflexivity|].
  destruct (f a); simpl; rewrite IH; reflexivity.
Qed.

Lemma filter_map' : forall {A B} (f : B -> bool) (g : A -> B) l,
  filter f (map g l) = map g (filter (fun a => f (g a)) l).
Proof.
  intros A B f g l. induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (f (g a)); simpl; rewrite IH; reflexivity.
Qed.

Lemma filter_ext_in' : forall {A} (f g : A -> bool) l,
  (forall a, In a l -> f a = g a) -> filter f l = filter g l.
Proof.
  intros A f g l H. induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite (H a (or_introl eq_refl)).
  rewrite IH by (intros b Hb; apply H; right; exact Hb). reflexivity.
Qed.

Lemma filter_false' : forall {A} (l : list A), filter (fun _ => false) l = [].
Proof. intros A l. induction l; simpl; auto. Qed.

Lemma filter_true' : forall {A} (l : list A), filter (fun _ => true) l = l.
Proof. intros A l. induction l; simpl; f_equal; auto. Qed.

(** Of the 2^n candidates, exactly 2^(n - length c) agree with c on its bits. *)
Lemma count_agrees : forall c n,
  length c <= n ->
  length (filter (agreesb c) (all_bits n)) = 2 ^ (n - length c).
Proof.
  induction c as [|x c IH]; intros n Hn.
  - rewrite (filter_ext_in' (agreesb []) (fun _ => true)) by (intros a _; reflexivity).
    rewrite filter_true', all_bits_length. simpl. f_equal. lia.
  - destruct n as [|n]; simpl in Hn; [lia|].
    simpl all_bits. rewrite filter_app', !filter_map', app_length, !map_length.
    simpl agreesb.
    destruct x; simpl; rewrite ?filter_false'; simpl;
      rewrite IH by lia; lia.
Qed.

Definition prior_size (n : nat) : length (prior n) = 2 ^ n :=
  eq_trans (map_length world (all_bits n)) (all_bits_length n).

Lemma agree_upto_firstn : forall j v answers,
  j <= length answers ->
  agree_upto j v answers <->
  agree_upto (length (firstn j answers)) v (firstn j answers).
Proof.
  intros j v answers Hj.
  rewrite firstn_length, Nat.min_l by exact Hj.
  assert (Hn : forall i, i < j -> nth i (firstn j answers) false = nth i answers false).
  { intros i Hi.
    rewrite <- (firstn_skipn j answers) at 2.
    rewrite app_nth1; [reflexivity|].
    rewrite firstn_length. lia. }
  split; intros H i Hi; rewrite ?Hn by exact Hi; [exact (H i Hi)|].
  rewrite <- Hn by exact Hi. exact (H i Hi).
Qed.

(** After j questions, exactly 2^(n-j) of the 2^n candidates are still being
    searched: each question halves the live candidates. *)
Theorem search_progress_count : forall n answers j,
  j <= length answers -> length answers <= n -> n <= 64 ->
  length (filter (still_searching answers j) (prior n)) = 2 ^ (n - j).
Proof.
  intros n answers j Hj Hn H64. unfold prior.
  rewrite filter_map', map_length.
  rewrite (filter_ext_in' _ (agreesb (firstn j answers))).
  - rewrite count_agrees; rewrite firstn_length, Nat.min_l by exact Hj; [reflexivity|lia].
  - intros v Hv. apply in_all_bits in Hv.
    apply eq_iff_eq_true.
    rewrite still_searching_iff by lia.
    rewrite agreesb_spec by (rewrite firstn_length; lia).
    apply agree_upto_firstn. exact Hj.
Qed.

(** * The posterior, the observations and the decoder *)

(** The posterior: the candidates that agree with the answers on the asked
    bits, one for each setting of the n - k bits that were never asked. *)
Definition posterior (n : nat) (answers : list bool) : list VMState :=
  map (fun u => world (answers ++ u)) (all_bits (n - length answers)).

Definition answer_instr (x : nat) : vm_instruction := instr_read_port 5 0 x 1 0.

(** The distinguishing observation: the answers a state gives to the k asked
    questions, written as the READ_PORT receipts a run would carry. *)
Definition asked_obs (k : nat) (s : VMState) : list vm_instruction :=
  map (fun i => answer_instr (read_mem s i)) (seq 0 k).

(** The representative observation: the answers a state gives to the n - k
    questions that were never asked. *)
Definition unasked_obs (n k : nat) (s : VMState) : list vm_instruction :=
  map (fun i => answer_instr (read_mem s i)) (seq k (n - k)).

(** The decoder keeps the answer receipts of the program and drops the rest. *)
Definition is_answer (i : vm_instruction) : bool :=
  match i with instr_read_port _ _ _ _ _ => true | _ => false end.

Definition answer_decoder : NoFreeInsight.receipt_decoder vm_instruction := filter is_answer.

Definition receipt_eqb (o1 o2 : list vm_instruction) : bool :=
  if list_eq_dec vm_instruction_eq_dec o1 o2 then true else false.

Lemma receipt_eqb_spec : forall o1 o2, receipt_eqb o1 o2 = true <-> o1 = o2.
Proof.
  intros o1 o2. unfold receipt_eqb.
  destruct (list_eq_dec vm_instruction_eq_dec o1 o2); split; congruence.
Qed.

(** Reading the hidden value back out of the state. *)
Definition decode (n : nat) (s : VMState) : list bool :=
  map (fun i => Nat.eqb (read_mem s i) 1) (seq 0 n).

(** The fibre of a survivor: every candidate that shares its unasked bits. *)
Definition fiber_of (n k : nat) (t : VMState) : list VMState :=
  map (fun p => world (p ++ skipn k (decode n t))) (all_bits k).

Lemma read_mem_world : forall v i,
  i < length v -> length v <= 64 ->
  read_mem (world v) i = Nat.b2n (nth i v false).
Proof.
  intros v i Hi H64. unfold read_mem, world. simpl.
  unfold mem_index, MEM_SIZE. rewrite Nat.mod_small by lia.
  apply nth_mem_of. exact Hi.
Qed.

Lemma map_nth_seq_self : forall {A} (l : list A) d,
  map (fun i => nth i l d) (seq 0 (length l)) = l.
Proof.
  intros A l d. induction l as [|a l IH]; simpl; [reflexivity|].
  f_equal. rewrite <- seq_shift, map_map. simpl. exact IH.
Qed.

Lemma decode_world : forall v,
  length v <= 64 -> decode (length v) (world v) = v.
Proof.
  intros v H64. unfold decode.
  rewrite (map_ext_in _ (fun i => nth i v false)).
  - apply map_nth_seq_self.
  - intros i Hi. apply in_seq in Hi.
    rewrite read_mem_world by lia. destruct (nth i v false); reflexivity.
Qed.

Lemma world_inj : forall v w,
  length v = length w -> length v <= 64 -> world v = world w -> v = w.
Proof.
  intros v w Hl H64 H.
  rewrite <- (decode_world v H64), <- (decode_world w ltac:(lia)).
  rewrite <- Hl, H. reflexivity.
Qed.

Lemma decoder_search_prog : forall answers,
  answer_decoder (search_prog answers) =
  map (fun b => answer_instr (Nat.b2n b)) answers.
Proof.
  intros answers. unfold answer_decoder, search_prog.
  rewrite filter_app'. simpl. rewrite app_nil_r.
  generalize 0. generalize (search_trap (length answers)).
  induction answers as [|b rest IH]; intros trap i; simpl; [reflexivity|].
  f_equal. apply IH.
Qed.

Lemma asked_obs_world : forall v k,
  k <= length v -> length v <= 64 ->
  asked_obs k (world v) = map (fun i => answer_instr (Nat.b2n (nth i v false))) (seq 0 k).
Proof.
  intros v k Hk H64. unfold asked_obs. apply map_ext_in.
  intros i Hi. apply in_seq in Hi. rewrite read_mem_world by lia. reflexivity.
Qed.

Lemma app_agree : forall answers u,
  agree_upto (length answers) (answers ++ u) answers.
Proof. intros answers u i Hi. apply app_nth1. exact Hi. Qed.

Lemma agree_split : forall answers v,
  length answers <= length v -> agree_upto (length answers) v answers ->
  v = answers ++ skipn (length answers) v.
Proof.
  intros answers v Hl H.
  rewrite <- (firstn_skipn (length answers) v) at 1. f_equal.
  apply nth_ext with (d := false) (d' := false).
  - rewrite firstn_length. lia.
  - intros i Hi. rewrite firstn_length in Hi.
    rewrite <- H by lia.
    rewrite <- (firstn_skipn (length answers) v) at 2.
    rewrite app_nth1; [reflexivity|]. rewrite firstn_length. lia.
Qed.

(** The posterior is exactly the set of candidates whose run ends error-free. *)
Theorem posterior_is_what_the_run_certifies : forall n answers v,
  length answers <= n -> n <= 64 -> length v = n ->
  In (world v) (posterior n answers) <->
  (run_vm (search_fuel (length answers)) (search_prog answers) (world v)).(vm_err)
    = false.
Proof.
  intros n answers v Hn H64 Hv.
  rewrite search_certifies_iff_agrees by lia. unfold posterior.
  rewrite in_map_iff. split.
  - intros [u [Hw Hu]]. apply in_all_bits in Hu.
    apply world_inj in Hw; [| rewrite app_length; lia | rewrite app_length; lia].
    rewrite <- Hw. apply app_agree.
  - intro H. exists (skipn (length answers) v). split.
    + f_equal. symmetry. apply agree_split; [lia|exact H].
    + apply in_all_bits. rewrite skipn_length. lia.
Qed.

Lemma posterior_size : forall n answers,
  length (posterior n answers) = 2 ^ (n - length answers).
Proof. intros. unfold posterior. rewrite map_length. apply all_bits_length. Qed.

Lemma complete_tree_depth : forall d, decision_tree_depth (complete_tree d) = d.
Proof.
  induction d as [|d IH]; simpl; [reflexivity|]. rewrite IH, Nat.max_id. reflexivity.
Qed.

Lemma fold_add_const : forall {A} (c : nat) (l : list A),
  fold_right Nat.add 0 (map (fun _ => c) l) = length l * c.
Proof. intros A c l. induction l; simpl; [reflexivity|]. rewrite IHl. lia. Qed.

(** * The eight hypotheses, discharged for every size *)

Section Instance.

Variables (n : nat) (answers hidden : list bool).
Hypothesis Hk1 : 1 <= length answers.
Hypothesis Hkn : length answers <= n.
Hypothesis Hn64 : n <= 64.
Hypothesis Hhidden : length hidden = n.
(** The answers are true of the hidden value. *)
Hypothesis Hhonest : agree_upto (length answers) hidden answers.

Let k := length answers.
Let p := search_prog answers.
Let fuel := search_fuel k.

Lemma bs_prior_member : forall v, length v = n -> In (world v) (prior n).
Proof. intros v Hv. apply in_map. apply in_all_bits. exact Hv. Qed.

Lemma bs_posterior_in_prior : forall s, In s (posterior n answers) -> In s (prior n).
Proof.
  intros s Hs. unfold posterior in Hs. apply in_map_iff in Hs.
  destruct Hs as [u [<- Hu]]. apply in_all_bits in Hu.
  apply bs_prior_member. rewrite app_length. fold k. lia.
Qed.

Definition bs_witness_bits : list bool :=
  negb (nth 0 answers false) :: repeat false (n - 1).

Lemma bs_witness_length : length bs_witness_bits = n.
Proof. unfold bs_witness_bits. simpl. rewrite repeat_length. unfold k in *. lia. Qed.

Lemma bs_asked_head : forall s,
  exists rest, asked_obs k s = answer_instr (read_mem s 0) :: rest.
Proof.
  intros s. unfold asked_obs. fold k in Hk1.
  destruct k as [|k']; [lia|]. simpl. eexists. reflexivity.
Qed.

Lemma bs_distinguishing :
  exists w, In w (prior n) /\ ~ In w (posterior n answers) /\
    observation_distinguishes (asked_obs k) w (posterior n answers).
Proof.
  exists (world bs_witness_bits).
  assert (Hpost : forall t, In t (posterior n answers) ->
            read_mem t 0 = Nat.b2n (nth 0 answers false)).
  { intros t Ht. unfold posterior in Ht. apply in_map_iff in Ht.
    destruct Ht as [u [<- Hu]]. apply in_all_bits in Hu.
    rewrite read_mem_world by (rewrite app_length; unfold k in *; lia).
    rewrite app_nth1 by (fold k; lia). reflexivity. }
  assert (Hw0 : read_mem (world bs_witness_bits) 0 =
                Nat.b2n (negb (nth 0 answers false))).
  { rewrite read_mem_world by (rewrite bs_witness_length; lia). reflexivity. }
  split; [apply bs_prior_member; apply bs_witness_length|].
  split.
  - intro Hin. apply Hpost in Hin. rewrite Hw0 in Hin.
    destruct (nth 0 answers false); discriminate.
  - intros t Ht Heq.
    destruct (bs_asked_head (world bs_witness_bits)) as [r1 E1].
    destruct (bs_asked_head t) as [r2 E2].
    rewrite E1, E2 in Heq. injection Heq as Heq _.
    rewrite Hw0, (Hpost t Ht) in Heq.
    destruct (nth 0 answers false); discriminate.
Qed.

Lemma bs_strict_subset : is_strict_subset (posterior n answers) (prior n).
Proof.
  split; [exact bs_posterior_in_prior|].
  destruct bs_distinguishing as [w [Hw [Hnw _]]]. exists w. split; assumption.
Qed.

Lemma bs_hidden_in_posterior : In (world hidden) (posterior n answers).
Proof.
  apply (proj2 (posterior_is_what_the_run_certifies n answers hidden Hkn Hn64 Hhidden)).
  exact (proj1 (search_run_agrees answers hidden ltac:(lia) ltac:(lia) Hhonest)).
Qed.

Lemma bs_obs_hidden : asked_obs k (world hidden) = answer_decoder p.
Proof.
  unfold p, k. rewrite decoder_search_prog.
  rewrite asked_obs_world by lia.
  transitivity (map (fun i => answer_instr (Nat.b2n (nth i answers false)))
                   (seq 0 (length answers))).
  - apply map_ext_in. intros i Hi. apply in_seq in Hi.
    rewrite Hhonest by lia. reflexivity.
  - pose proof (f_equal (fun bs : list bool => map (fun b => answer_instr (Nat.b2n b)) bs)
                 (map_nth_seq_self answers false)) as Hmap.
    rewrite map_map in Hmap. exact Hmap.
Qed.

Lemma bs_certified :
  NoFreeInsight.Certified (run_vm fuel p (world hidden)) answer_decoder
    (omega_predicate receipt_eqb (posterior n answers) (asked_obs k)) p.
Proof.
  destruct (search_run_agrees answers hidden ltac:(lia) ltac:(lia) Hhonest)
    as [He [Hc _]].
  unfold NoFreeInsight.Certified, NoFreeInsight.CertifiedWithSupra, NoFreeInsight.CertifiedObs, has_supra_cert.
  split; [split|].
  - exact He.
  - unfold omega_predicate. apply existsb_exists.
    exists (world hidden). split; [exact bs_hidden_in_posterior|].
    apply receipt_eqb_spec. exact bs_obs_hidden.
  - exact Hc.
Qed.

Lemma bs_tree_realized :
  decision_tree_realized_by_trace fuel p (world hidden) (complete_tree k).
Proof.
  unfold decision_tree_realized_by_trace. rewrite complete_tree_depth.
  destruct (search_run_agrees answers hidden ltac:(lia) ltac:(lia) Hhonest)
    as [_ [_ [_ Hcse]]].
  unfold fuel, p, k. rewrite Hcse. lia.
Qed.

Lemma bs_posterior_nonempty : feasible_size (posterior n answers) > 0.
Proof.
  unfold feasible_size. rewrite posterior_size.
  pose proof (Nat.pow_nonzero 2 (n - length answers)). lia.
Qed.

Lemma bs_representatives :
  PosteriorRepresentativeReduction (unasked_obs n k) (complete_tree k)
    (prior n) (posterior n answers).
Proof.
  exists (fiber_of n k). split; [|split].
  - intros s Hs. unfold prior in Hs. apply in_map_iff in Hs.
    destruct Hs as [v [<- Hv]]. apply in_all_bits in Hv.
    exists (world (answers ++ skipn k v)).
    assert (Hlen : length (answers ++ skipn k v) = n)
      by (rewrite app_length, skipn_length; fold k; lia).
    split; [|split].
    + unfold posterior. apply in_map_iff. exists (skipn k v).
      split; [reflexivity|]. apply in_all_bits.
      rewrite skipn_length. unfold k. lia.
    + unfold fiber_of. rewrite <- Hlen, decode_world by lia.
      assert (Hskip : skipn k (answers ++ skipn k v) = skipn k v).
      { unfold k. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
      rewrite Hskip.
      apply in_map_iff. exists (firstn k v). split.
      * rewrite firstn_skipn. reflexivity.
      * apply in_all_bits. rewrite firstn_length. lia.
    + unfold observation_equiv, unasked_obs. apply map_ext_in.
      intros i Hi. apply in_seq in Hi.
      rewrite !read_mem_world by lia. f_equal.
      rewrite app_nth2 by (fold k; lia).
      rewrite <- (firstn_skipn k v) at 1.
      rewrite app_nth2 by (rewrite firstn_length; lia).
      rewrite firstn_length, Nat.min_l by lia. fold k. reflexivity.
  - unfold feasible_size.
    rewrite (map_ext (fun s_post => length (fiber_of n k s_post)) (fun _ => 2 ^ k))
      by (intros t; unfold fiber_of; rewrite map_length; apply all_bits_length).
    rewrite fold_add_const, posterior_size, prior_size.
    rewrite <- Nat.pow_add_r. fold k. replace (n - k + k) with n by lia. lia.
  - intros t _. unfold feasible_size, fiber_of.
    rewrite map_length, all_bits_length, complete_tree_leaf_count. lia.
Qed.

(** The structural-entitlement bound, instantiated by a genuine search. *)
Theorem bit_search_entitlement :
  let P_prior := omega_predicate receipt_eqb (prior n) (asked_obs k) in
  let P_posterior := omega_predicate receipt_eqb (posterior n answers) (asked_obs k) in
  NoFreeInsight.strictly_stronger P_posterior P_prior /\
  NoFreeInsight.has_structure_addition fuel p (world hidden) /\
  Nat.log2_up (feasible_size (prior n)) - Nat.log2_up (feasible_size (posterior n answers))
    <= (run_vm fuel p (world hidden)).(vm_mu) - (world hidden).(vm_mu).
Proof.
  exact (structural_entitlement_representation fuel p (world hidden)
    answer_decoder (asked_obs k) (unasked_obs n k) receipt_eqb
    (prior n) (posterior n answers) (complete_tree k)
    receipt_eqb_spec bs_strict_subset bs_distinguishing eq_refl bs_certified
    bs_tree_realized bs_posterior_nonempty bs_representatives).
Qed.

(** What the bound reads on this run: k index bits narrowed, and the counter
    rose by exactly 2k + 1 (2 per answer through the port, 1 for the
    assertion). *)
Corollary bit_search_bound_reads :
  Nat.log2_up (feasible_size (prior n)) - Nat.log2_up (feasible_size (posterior n answers))
    = k /\
  k <= (run_vm fuel p (world hidden)).(vm_mu) - (world hidden).(vm_mu) /\
  (run_vm fuel p (world hidden)).(vm_mu) - (world hidden).(vm_mu) = 2 * k + 1.
Proof.
  destruct (search_run_agrees answers hidden ltac:(lia) ltac:(lia) Hhonest)
    as [_ [_ [Hmu _]]].
  assert (Hbits : Nat.log2_up (feasible_size (prior n)) -
                  Nat.log2_up (feasible_size (posterior n answers)) = k).
  { unfold feasible_size. rewrite prior_size, posterior_size.
    rewrite !Nat.log2_up_pow2 by lia. fold k. lia. }
  fold k p in Hmu. unfold fuel. rewrite Hmu. simpl vm_mu.
  split; [exact Hbits|]. split; lia.
Qed.

(** The structural-shortcut record, inhabited by this run. *)
Definition bit_search_shortcut : SoundStructuralShortcut fuel p (world hidden) :=
  sound_shortcut_from_components fuel p (world hidden)
    answer_decoder (asked_obs k) (unasked_obs n k) receipt_eqb
    (prior n) (posterior n answers) (complete_tree k)
    receipt_eqb_spec bs_strict_subset bs_distinguishing eq_refl bs_certified
    bs_tree_realized bs_posterior_nonempty bs_representatives.

End Instance.
