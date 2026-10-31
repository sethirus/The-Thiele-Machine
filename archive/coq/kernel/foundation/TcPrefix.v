(** TcPrefix.v: the prefix of the Rice reduction, as a vendored two-register
    program.

    Given a two-register program P and its start (a0, b0), the program
    [tc_pre P K], with K = 2^b0 * 3^a0, does this from a state with the plain
    input n in counter A and 0 in counter B:

      1. A := (6n + 5) * K            (multiply by 6, add 5, multiply by K)
      2. run the compiled P inside A  (A = (6n + 5) * 2^b * 3^a all along)
      3. divide A by 2 and by 3 as often as possible, leaving 6n + 5
      4. subtract 5 and divide by 6, leaving n.

    If P stops on (a0, b0), the prefix stops with n in A and 0 in B, one past
    its end, for every n [tc_pre_halts]. If P does not stop, the prefix does
    not stop, for every n [tc_pre_diverges]. The input n is never lost
    because 6n + 5 is prime to 2 and to 3.

    Dependencies: Coq standard library, the vendored coq-undecidability
    library, TcGodel.v, TcCompile.v, TcBridge.v, TcRiceMM.v, TcGadget.v. No
    axioms and no unfinished proofs.                                                    *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the two-counter machine of EarnedCore.v (its
   programs, runs and the numbering of programs). The machine's link to the
   abstract record (a CertificationSystem with the trace cost floor, and a
   Thiele-complete machine) lives in EarnedCoreLinks.v and ThieleComplete.v. *)


From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils gcd godel_coding pos vec subcode sss compiler_correction.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.MMA Require Import mma_defs mma_utils.
Require Import Kernel.TcGodel Kernel.TcCompile Kernel.TcBridge Kernel.TcRiceMM Kernel.TcGadget.
Set Default Goal Selector "!".

(* ------------------------------------------------------------------ *)
(* Numbers prime to 2 and 3                                           *)
(* ------------------------------------------------------------------ *)

Lemma tc_gcd2_res : forall n, Nat.gcd 2 (6 * n + 5) = 1.
Proof.
  intro n. replace (6 * n + 5) with (5 + (3 * n) * 2) by lia.
  rewrite Nat.gcd_add_mult_diag_r. reflexivity.
Qed.

Lemma tc_gcd3_res : forall n, Nat.gcd 3 (6 * n + 5) = 1.
Proof.
  intro n. replace (6 * n + 5) with (2 + (2 * n + 1) * 3) by lia.
  rewrite Nat.gcd_add_mult_diag_r. reflexivity.
Qed.

Lemma tc_res_hyp : forall n, forall p : pos 2, Nat.gcd (gc_pr tc_gc2 p) (6 * n + 5) = 1.
Proof.
  intros n p. pos_inv p; simpl.
  - apply tc_gcd2_res.
  - pos_inv p; simpl; [apply tc_gcd3_res | invert pos p].
Qed.

Lemma tc_coprime_not_div : forall m y, 1 < m -> Nat.gcd m y = 1 -> ~ divides m y.
Proof.
  intros m y Hm Hg [c Hc].
  assert (Hd : Nat.divide m y) by (exists c; exact Hc).
  assert (H1 : Nat.divide m 1) by (rewrite <- Hg; apply Nat.gcd_greatest; [apply Nat.divide_refl | exact Hd]).
  apply Nat.divide_1_r in H1. lia.
Qed.

Lemma tc_gcd_pow3 : forall e, Nat.gcd 2 (3 ^ e) = 1.
Proof. intro e. apply tc_gcd_pow. reflexivity. Qed.

Lemma tc_not2 : forall n e, ~ divides 2 ((6 * n + 5) * 3 ^ e).
Proof.
  intros n e. apply tc_coprime_not_div; [lia |].
  apply tc_gcd_mul; [apply tc_gcd2_res | apply tc_gcd_pow3].
Qed.

Lemma tc_not3 : forall n, ~ divides 3 (6 * n + 5).
Proof. intro n. apply tc_coprime_not_div; [lia | apply tc_gcd3_res]. Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

Definition tc_i1 (K : nat) : nat := 28 + K.
Definition tc_i2 (P : list (mm_instr (pos 2))) (K : nat) : nat := tc_i1 K + length (tc_Q P (tc_i1 K)).
Definition tc_i3 (P : list (mm_instr (pos 2))) (K : nat) : nat := tc_i2 P K + 67.
Definition tc_end (P : list (mm_instr (pos 2))) (K : nat) : nat := tc_i3 P K + 75.

Definition tc_p1 : list (mm_instr (pos 2)) := mma_mult_cst_with_zero tcA tcB 6 1.
Definition tc_p2 : list (mm_instr (pos 2)) := mma_incs tcA 5.
Definition tc_p3 (K : nat) : list (mm_instr (pos 2)) := mma_mult_cst_with_zero tcA tcB K 20.
Definition tc_p4 (P : list (mm_instr (pos 2))) (K : nat) := tc_Q P (tc_i1 K).
Definition tc_p5 (P : list (mm_instr (pos 2))) (K : nat) := mma_div_branch tcA tcB 2 (tc_i2 P K) (tc_i2 P K).
Definition tc_p6 (P : list (mm_instr (pos 2))) (K : nat) :=
  mma_div_branch tcA tcB 3 (tc_i2 P K + 30) (tc_i2 P K + 30).
Definition tc_p7 (P : list (mm_instr (pos 2))) (K : nat) :=
  mma_decs tcA (tc_i3 P K + 17) (tc_i3 P K + 17) 5 (tc_i3 P K).
Definition tc_p8 (P : list (mm_instr (pos 2))) (K : nat) :=
  mma_div_branch tcA tcB 6 (tc_i3 P K + 17) (tc_i3 P K + 75).

Definition tc_pre (P : list (mm_instr (pos 2))) (K : nat) : list (mm_instr (pos 2)) :=
  tc_p1 ++ tc_p2 ++ tc_p3 K ++ tc_p4 P K ++ tc_p5 P K ++ tc_p6 P K ++ tc_p7 P K ++ tc_p8 P K.

Lemma tc_p1_len : length tc_p1 = 14.
Proof. unfold tc_p1. rewrite mma_mult_cst_with_zero_length. reflexivity. Qed.
Lemma tc_p2_len : length tc_p2 = 5.
Proof. unfold tc_p2. apply mma_incs_length. Qed.
Lemma tc_p3_len : forall K, length (tc_p3 K) = 8 + K.
Proof. intro K. unfold tc_p3. apply mma_mult_cst_with_zero_length. Qed.
Lemma tc_p5_len : forall P K, length (tc_p5 P K) = 30.
Proof. intros P K. unfold tc_p5. rewrite mma_div_branch_length. reflexivity. Qed.
Lemma tc_p6_len : forall P K, length (tc_p6 P K) = 37.
Proof. intros P K. unfold tc_p6. rewrite mma_div_branch_length. reflexivity. Qed.
Lemma tc_p7_len : forall P K, length (tc_p7 P K) = 17.
Proof. intros P K. unfold tc_p7. rewrite mma_decs_length. reflexivity. Qed.
Lemma tc_p8_len : forall P K, length (tc_p8 P K) = 58.
Proof. intros P K. unfold tc_p8. rewrite mma_div_branch_length. reflexivity. Qed.

Lemma tc_pre_length : forall P K, 1 + length (tc_pre P K) = tc_end P K.
Proof.
  intros P K. unfold tc_pre, tc_end. rewrite !app_length, tc_p1_len, tc_p2_len, tc_p3_len,
    tc_p5_len, tc_p6_len, tc_p7_len, tc_p8_len.
  unfold tc_p4, tc_i3, tc_i2, tc_i1. lia.
Qed.

Lemma tc_sc : forall (l1 G l2 : list (mm_instr (pos 2))) i m,
  i = m + length l1 -> subcode (i, G) (m, l1 ++ G ++ l2).
Proof. intros l1 G l2 i m H. exists l1, l2. split; [reflexivity | exact H]. Qed.

Ltac tc_sub :=
  match goal with
  | |- subcode (_, ?G) (_, _) => idtac
  end.

Section Pieces.
  Variable (P : list (mm_instr (pos 2))) (K : nat).
  Let pre := tc_pre P K.

  Lemma tc_sc1 : subcode (1, tc_p1) (1, pre).
  Proof. exists [], (tc_p2 ++ tc_p3 K ++ tc_p4 P K ++ tc_p5 P K ++ tc_p6 P K ++ tc_p7 P K ++ tc_p8 P K).
    split; [reflexivity | reflexivity]. Qed.

  Lemma tc_sc2 : subcode (15, tc_p2) (1, pre).
  Proof. exists tc_p1, (tc_p3 K ++ tc_p4 P K ++ tc_p5 P K ++ tc_p6 P K ++ tc_p7 P K ++ tc_p8 P K).
    split; [reflexivity | rewrite tc_p1_len; lia]. Qed.

  Lemma tc_sc3 : subcode (20, tc_p3 K) (1, pre).
  Proof. exists (tc_p1 ++ tc_p2), (tc_p4 P K ++ tc_p5 P K ++ tc_p6 P K ++ tc_p7 P K ++ tc_p8 P K).
    split; [unfold pre, tc_pre; rewrite <- !app_assoc; reflexivity |
            rewrite app_length, tc_p1_len, tc_p2_len; lia]. Qed.

  Lemma tc_sc4 : subcode (tc_i1 K, tc_p4 P K) (1, pre).
  Proof. exists (tc_p1 ++ tc_p2 ++ tc_p3 K), (tc_p5 P K ++ tc_p6 P K ++ tc_p7 P K ++ tc_p8 P K).
    split; [unfold pre, tc_pre; rewrite <- !app_assoc; reflexivity |
            rewrite !app_length, tc_p1_len, tc_p2_len, tc_p3_len; unfold tc_i1; lia]. Qed.

  Lemma tc_sc5 : subcode (tc_i2 P K, tc_p5 P K) (1, pre).
  Proof. exists (tc_p1 ++ tc_p2 ++ tc_p3 K ++ tc_p4 P K), (tc_p6 P K ++ tc_p7 P K ++ tc_p8 P K).
    split; [unfold pre, tc_pre; rewrite <- !app_assoc; reflexivity |
            rewrite !app_length, tc_p1_len, tc_p2_len, tc_p3_len; unfold tc_p4, tc_i2, tc_i1; lia]. Qed.

  Lemma tc_sc6 : subcode (tc_i2 P K + 30, tc_p6 P K) (1, pre).
  Proof. exists (tc_p1 ++ tc_p2 ++ tc_p3 K ++ tc_p4 P K ++ tc_p5 P K), (tc_p7 P K ++ tc_p8 P K).
    split; [unfold pre, tc_pre; rewrite <- !app_assoc; reflexivity |
            rewrite !app_length, tc_p1_len, tc_p2_len, tc_p3_len, tc_p5_len; unfold tc_p4, tc_i2, tc_i1; lia]. Qed.

  Lemma tc_sc7 : subcode (tc_i3 P K, tc_p7 P K) (1, pre).
  Proof. exists (tc_p1 ++ tc_p2 ++ tc_p3 K ++ tc_p4 P K ++ tc_p5 P K ++ tc_p6 P K), (tc_p8 P K).
    split; [unfold pre, tc_pre; rewrite <- !app_assoc; reflexivity |
            rewrite !app_length, tc_p1_len, tc_p2_len, tc_p3_len, tc_p5_len, tc_p6_len;
            unfold tc_p4, tc_i3, tc_i2, tc_i1; lia]. Qed.

  Lemma tc_sc8 : subcode (tc_i3 P K + 17, tc_p8 P K) (1, pre).
  Proof. exists (tc_p1 ++ tc_p2 ++ tc_p3 K ++ tc_p4 P K ++ tc_p5 P K ++ tc_p6 P K ++ tc_p7 P K), [].
    split; [unfold pre, tc_pre; rewrite <- !app_assoc; rewrite app_nil_r; reflexivity |
            rewrite !app_length, tc_p1_len, tc_p2_len, tc_p3_len, tc_p5_len, tc_p6_len, tc_p7_len;
            unfold tc_p4, tc_i3, tc_i2, tc_i1; lia]. Qed.
End Pieces.

Print Assumptions tc_sc8.

(* ------------------------------------------------------------------ *)
(* The three phases of the run                                         *)
(* ------------------------------------------------------------------ *)

Lemma tc_phase1 : forall P K n,
  sss_compute (@mma_sss 2) (1, tc_pre P K) (1, tc_tovec n 0)
    (tc_i1 K, tc_tovec ((6 * n + 5) * K) 0).
Proof.
  intros P K n.
  assert (E : (6 * n + 5) * K = K * (5 + 6 * n)) by ring. rewrite E.
  eapply sss_compute_trans.
  { apply sss_progress_compute. eapply subcode_sss_progress; [apply tc_sc1 | apply tc_mult]. }
  eapply sss_compute_trans.
  { eapply subcode_sss_compute; [apply tc_sc2 | apply tc_incs]. }
  replace (tc_i1 K) with (8 + K + 20) by (unfold tc_i1; lia).
  apply sss_progress_compute. eapply subcode_sss_progress; [apply tc_sc3 | apply tc_mult].
Qed.

Lemma tc_phase3 : forall P K n a1 b1,
  sss_compute (@mma_sss 2) (1, tc_pre P K)
    (tc_i2 P K, tc_tovec ((6 * n + 5) * (2 ^ b1 * (3 ^ a1 * 1))) 0)
    (tc_end P K, tc_tovec n 0).
Proof.
  intros P K n a1 b1.
  assert (E1 : (6 * n + 5) * (2 ^ b1 * (3 ^ a1 * 1)) = ((6 * n + 5) * 3 ^ a1) * 2 ^ b1) by ring.
  rewrite E1.
  eapply sss_compute_trans.
  { eapply subcode_sss_compute; [apply tc_sc5 | apply tc_div_loop; [lia | apply tc_not2]]. }
  assert (E2 : tc_i2 P K + 30 = 16 + 7 * 2 + tc_i2 P K) by lia.
  assert (E3 : (6 * n + 5) * 3 ^ a1 = (6 * n + 5) * 3 ^ a1) by reflexivity.
  replace (16 + 7 * 2 + tc_i2 P K) with (tc_i2 P K + 30) by lia.
  eapply sss_compute_trans.
  { eapply subcode_sss_compute; [apply tc_sc6 |].
    replace (tc_i2 P K + 30) with (tc_i2 P K + 30) by reflexivity.
    apply (tc_div_loop 3 (tc_i2 P K + 30) (6 * n + 5)); [lia | apply tc_not3]. }
  replace (16 + 7 * 3 + (tc_i2 P K + 30)) with (tc_i3 P K - 0) by (unfold tc_i3; lia).
  eapply sss_compute_trans.
  { apply sss_progress_compute. eapply subcode_sss_progress; [apply tc_sc7 | apply tc_decs; lia]. }
  replace (6 * n + 5 - 5) with (n * 6) by lia.
  apply sss_progress_compute. 
  replace (tc_end P K) with (tc_i3 P K + 75) by reflexivity.
  eapply subcode_sss_progress; [apply tc_sc8 |].
  apply tc_div_yes; [lia | lia].
Qed.

Theorem tc_pre_halts : forall P a0 b0 j a1 b1,
  sss_output (@mma_sss 2) (1, P) (1, tc_tovec a0 b0) (j, tc_tovec a1 b1) ->
  forall n,
  sss_output (@mma_sss 2) (1, tc_pre P (tc_code (tc_tovec a0 b0)))
    (1, tc_tovec n 0) (tc_end P (tc_code (tc_tovec a0 b0)), tc_tovec n 0).
Proof.
  intros P a0 b0 j a1 b1 Hout n.
  set (K := tc_code (tc_tovec a0 b0)).
  pose proof (tc_Q_halts P a0 b0 j a1 b1 Hout (6 * n + 5) (tc_res_hyp n) (tc_i1 K)) as HQ.
  destruct HQ as [HQc _].
  split.
  - eapply sss_compute_trans; [apply tc_phase1 |].
    eapply sss_compute_trans.
    + eapply subcode_sss_compute; [apply tc_sc4 |]. exact HQc.
    + replace (tc_i1 K + length (tc_Q P (tc_i1 K))) with (tc_i2 P K) by reflexivity.
      apply tc_phase3.
  - unfold out_code, code_end. cbn [fst snd]. right. pose proof (tc_pre_length P K). lia.
Qed.

Theorem tc_pre_diverges : forall P a0 b0,
  ~ sss_terminates (@mma_sss 2) (1, P) (1, tc_tovec a0 b0) ->
  forall n,
  ~ sss_terminates (@mma_sss 2) (1, tc_pre P (tc_code (tc_tovec a0 b0))) (1, tc_tovec n 0).
Proof.
  intros P a0 b0 Hnt n Ht.
  set (K := tc_code (tc_tovec a0 b0)) in *.
  destruct Ht as [st3 [Hc Ho]].
  assert (Hc1 := tc_phase1 P K n).
  pose proof (@sss_compute_inv _ _ (@mma_sss 2) (@mma_sss_fun 2) _ _ _ _ Ho Hc1 Hc) as H2.
  assert (Hterm : sss_terminates (@mma_sss 2) (1, tc_pre P K) (tc_i1 K, tc_tovec ((6 * n + 5) * K) 0)).
  { exists st3. split; assumption. }
  apply subcode_sss_terminates with (P := (tc_i1 K, tc_Q P (tc_i1 K))) in Hterm; [| apply tc_sc4].
  exact (tc_Q_diverges P a0 b0 Hnt (6 * n + 5) (tc_res_hyp n) (tc_i1 K) Hterm).
Qed.

Print Assumptions tc_pre_halts.
Print Assumptions tc_pre_diverges.
