(** Candidate two-counter access under the unchanged abstract ISA.
    Both differences can be updated; the second guard/branch theorem requires
    first-counter equality. The rejection theorem applies to this layout only
    and is not a nonuniversality theorem for the VM. *)
From Coq Require Import ZArith Lia Bool.
From Kernel Require Import VMState VMStep.
Definition two_counter_witness (u v a b : nat) : WitnessCounts :=
 {| wc_same_00 := S u; wc_diff_00 := S v;
    wc_same_01 := S a; wc_diff_01 := S b;
    wc_same_10 := 1; wc_diff_10 := 0;
    wc_same_11 := 1; wc_diff_11 := 1 |}.
Theorem first_test : forall u v a b,
 column_contractive_check_witness (two_counter_witness u v a b) = true <-> u = v.
Proof.
 intros u v a b.
 unfold column_contractive_check_witness, chsh_n_z, chsh_d_z.
 cbn [two_counter_witness wc_same_00 wc_diff_00 wc_same_01 wc_diff_01 wc_same_10 wc_diff_10 wc_same_11 wc_diff_11].
 repeat rewrite Bool.andb_true_iff.
 repeat rewrite Z.ltb_lt. repeat rewrite Z.leb_le.
 rewrite !Nat2Z.inj_succ.
 split; intros H; [nia|subst; repeat split; nia].
Qed.
Theorem second_test_when_first_zero : forall u a b,
 sum_E_sq_check_witness (two_counter_witness u u a b) = true <-> a = b.
Proof.
 intros u a b.
 unfold sum_E_sq_check_witness, chsh_n_z, chsh_d_z.
 cbn [two_counter_witness wc_same_00 wc_diff_00 wc_same_01 wc_diff_01 wc_same_10 wc_diff_10 wc_same_11 wc_diff_11].
 rewrite Z.leb_le. rewrite !Nat2Z.inj_succ.
 split; intros H.
 - assert (Hu : (0 < (Z.of_nat u + 1) * (Z.of_nat u + 1))%Z) by nia.
   pose proof (Z.square_nonneg (Z.of_nat a - Z.of_nat b)) as Hab.
   assert (Hz : (((Z.of_nat u + 1) * (Z.of_nat u + 1)) *
                 ((Z.of_nat a - Z.of_nat b) * (Z.of_nat a - Z.of_nat b)) <= 0)%Z) by nia.
   assert (He : ((Z.of_nat a - Z.of_nat b) * (Z.of_nat a - Z.of_nat b) = 0)%Z) by nia.
   nia.
 - subst; nia.
Qed.
Theorem combined_test : forall u v a b,
 column_contractive_check_q1ab_kernel (two_counter_witness u v a b) = true <-> u = v /\ a = b.
Proof.
 intros u v a b. unfold column_contractive_check_q1ab_kernel.
 rewrite andb_true_iff, first_test.
 split.
 - intros [E H]. subst. apply second_test_when_first_zero in H. auto.
 - intros [E H]. subst. split; [reflexivity|]. apply second_test_when_first_zero. reflexivity.
Qed.
Lemma increment_first : forall u v a b,
 record_trial (two_counter_witness u v a b) 0 0 0 0 = two_counter_witness (S u) v a b.
Proof. reflexivity. Qed.
Lemma decrement_first : forall u v a b,
 record_trial (two_counter_witness u v a b) 0 0 0 1 = two_counter_witness u (S v) a b.
Proof. reflexivity. Qed.
Lemma increment_second : forall u v a b,
 record_trial (two_counter_witness u v a b) 0 1 0 0 = two_counter_witness u v (S a) b.
Proof. reflexivity. Qed.
Lemma decrement_second : forall u v a b,
 record_trial (two_counter_witness u v a b) 0 1 0 1 = two_counter_witness u v a (S b).
Proof. reflexivity. Qed.

Lemma first_nonzero_rejects : forall u v a b,
 u <> v -> column_contractive_check_witness (two_counter_witness u v a b) = false.
Proof.
 intros u v a b Hne.
 destruct (column_contractive_check_witness (two_counter_witness u v a b)) eqn:E; [|reflexivity].
 apply first_test in E. contradiction.
Qed.
Theorem all_extended_guards_reject : forall u v a b g1 h1 g2 h2 g3 h3 g4 h4 g5 h5,
 u <> v ->
 column_contractive_check_q1ab_kernel (two_counter_witness u v a b) = false /\
 q1ab_g5_full_integer_check_kernel (two_counter_witness u v a b) g5 h5 = false /\
 q1ab_g345_full_integer_check_kernel (two_counter_witness u v a b) g3 h3 g4 h4 g5 h5 = false /\
 q1ab_g12345_full_integer_check_kernel (two_counter_witness u v a b) g1 h1 g2 h2 g3 h3 g4 h4 g5 h5 = false.
Proof.
 intros u v a b g1 h1 g2 h2 g3 h3 g4 h4 g5 h5 Hne.
 unfold column_contractive_check_q1ab_kernel, q1ab_g5_full_integer_check_kernel,
 q1ab_g345_full_integer_check_kernel, q1ab_g12345_full_integer_check_kernel.
 rewrite (first_nonzero_rejects u v a b Hne). repeat split; reflexivity.
Qed.

From Coq Require Import List.
From Kernel Require Import SimulationProof VMCounterBranch.
Theorem second_branch_when_first_zero : forall p s u a b yes no,
 vm_witness s = two_counter_witness u u a b ->
 nth_error p (vm_pc s) = Some (instr_chsh_lassert_1ab 0) ->
 nth_error p (S (vm_pc s)) = Some (instr_jump yes 0) ->
 nth_error p LASSERT_TRAP_PC = Some (instr_jump no 0) ->
 run_vm 2 p s = counter_branch_result s (if Nat.eqb a b then yes else no) (Nat.eqb a b).
Proof.
 intros p s u a b yes no Hw Hguard Hyes Hno.
 cbn [run_vm]. rewrite Hguard. cbn [vm_apply]. rewrite Hw.
 destruct (column_contractive_check_q1ab_kernel (two_counter_witness u u a b)) eqn:Hcheck.
 - apply combined_test in Hcheck. destruct Hcheck as [_ H]. subst b. rewrite Nat.eqb_refl.
   cbn [vm_pc]. rewrite Hyes. cbn [vm_apply run_vm].
   unfold counter_branch_result, jump_state, apply_cost; cbn.
   rewrite Nat.add_0_r, Hw. reflexivity.
 - assert (Hne : a <> b).
   { intro H; subst. assert (Ht : column_contractive_check_q1ab_kernel (two_counter_witness u u b b) = true).
     { apply combined_test. auto. } congruence. }
   apply Nat.eqb_neq in Hne. rewrite Hne.
   cbn [vm_pc]. rewrite Hno. cbn [vm_apply run_vm].
   unfold counter_branch_result, jump_state, apply_cost; cbn.
   rewrite Nat.add_0_r, Hw. reflexivity.
Qed.

(** Actual one-step update macro for either represented difference, retaining
    the other difference and all ordinary data, CSR and error observations. *)
Definition two_counter_update_result (s : VMState) (wc : WitnessCounts) : VMState :=
 {| vm_graph := s.(vm_graph); vm_csrs := s.(vm_csrs);
    vm_regs := s.(vm_regs); vm_mem := s.(vm_mem); vm_pc := S s.(vm_pc);
    vm_mu := s.(vm_mu); vm_mu_tensor := s.(vm_mu_tensor); vm_err := s.(vm_err);
    vm_logic_acc := s.(vm_logic_acc); vm_mstatus := s.(vm_mstatus);
    vm_witness := wc; vm_certified := s.(vm_certified) |}.
Definition two_counter_next u v a b (second different : bool) :=
 if second then
   if different then two_counter_witness u v a (S b) else two_counter_witness u v (S a) b
 else
   if different then two_counter_witness u (S v) a b else two_counter_witness (S u) v a b.
Theorem two_counter_update_correct : forall p s u v a b (second different : bool),
 vm_witness s = two_counter_witness u v a b ->
 nth_error p (vm_pc s) = Some (instr_chsh_trial 0 (if second then 1 else 0)
                                                 0 (if different then 1 else 0) 0) ->
 run_vm 1 p s = two_counter_update_result s (two_counter_next u v a b second different).
Proof.
 intros p s u v a b second different Hw Hfetch.
 destruct second, different; cbn [run_vm]; rewrite Hfetch;
 unfold vm_apply; cbn;
 unfold two_counter_update_result, apply_cost, two_counter_next; cbn;
 rewrite Hw, Nat.add_0_r; reflexivity.
Qed.
