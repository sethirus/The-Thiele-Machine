(** ChshArith.v: the CHSH_LASSERT hardware check. [chsh_check_nat] is the
    natural-number form of the FSM's computation (sums, absolute differences
    with sign bits, unsigned magnitudes); [chsh_check_word] is its word-level
    form over the step rule's latches. Both equal the VM's
    [column_contractive_check_witness] for all 32-bit counters. *)
Require Import Kami.Kami Kami.Lib.NatLib.
Require Import Kernel.VMState Kernel.VMStep.
Import VMStep.VMStep.
From Coq Require Import Arith ZArith Lia Bool.
Local Open Scope nat_scope.

(** Unsigned less-than as a boolean. *)
Definition hw_ltb {n} (a b : word n) : bool := if wlt_dec a b then true else false.
Definition hw_absdiffw {n} (x y : word n) : word n :=
  if negb (hw_ltb x y) then wminus x y else wminus y x.

(** Products as the FSM forms them: both operands zero-extended to 384 and
    then 768 bits, one 768-bit multiplication, truncation to the result width. *)
Definition m128 (x y : word 64) : word 128 :=
  split1 128 640 (wmult (evalZeroExtendTrunc 768 (evalZeroExtendTrunc 384 x))
                        (evalZeroExtendTrunc 768 (evalZeroExtendTrunc 384 y))).
Definition m256 (x y : word 128) : word 256 :=
  split1 256 512 (wmult (evalZeroExtendTrunc 768 (evalZeroExtendTrunc 384 x))
                        (evalZeroExtendTrunc 768 (evalZeroExtendTrunc 384 y))).
Definition m384 (x y : word 256) : word 384 :=
  split1 384 384 (wmult (evalZeroExtendTrunc 768 (evalZeroExtendTrunc 384 x))
                        (evalZeroExtendTrunc 768 (evalZeroExtendTrunc 384 y))).

Lemma evalZeroExtendTrunc_nat : forall n1 n2 (w : word n1),
  n1 < n2 -> wordToNat (evalZeroExtendTrunc n2 w) = wordToNat w.
Proof.
  intros n1 n2 w H. unfold evalZeroExtendTrunc.
  destruct (Compare_dec.lt_dec n1 n2) as [Hlt|Hge]; [|lia].
  unfold eq_rec_r, eq_rec. rewrite wordToNat_eq_rect. apply wordToNat_zext.
Qed.

Lemma hw_ltb_nat : forall n (a b : word n), hw_ltb a b = Nat.ltb (wordToNat a) (wordToNat b).
Proof.
  intros n a b. unfold hw_ltb. destruct (wlt_dec a b) as [L|L].
  - symmetry. apply Nat.ltb_lt. apply wlt_lt. exact L.
  - symmetry. apply Nat.ltb_ge. destruct (Nat.le_gt_cases (wordToNat b) (wordToNat a)) as [H|H]; [exact H|].
    exfalso. apply L. apply lt_wlt. exact H.
Qed.

Lemma wordToNat_wminus_le' : forall sz (a b : word sz),
  wordToNat b <= wordToNat a -> wordToNat (wminus a b) = wordToNat a - wordToNat b.
Proof.
  intros sz a b H.
  assert (E : a = wplus (natToWord sz (wordToNat a - wordToNat b)) b).
  { apply wordToNat_inj. rewrite wordToNat_wplus.
    pose proof (wordToNat_bound a) as Ba.
    rewrite wordToNat_natToWord_2 by lia.
    replace (wordToNat a - wordToNat b + wordToNat b) with (wordToNat a) by lia.
    rewrite Nat.mod_small by exact Ba. reflexivity. }
  rewrite E at 1.
  rewrite wminus_def, <- wplus_assoc, wminus_inv.
  rewrite wplus_comm, wplus_unit.
  pose proof (wordToNat_bound a). apply wordToNat_natToWord_2. lia.
Qed.

Lemma hw_absdiffw_nat : forall n (x y : word n),
  wordToNat (hw_absdiffw x y) =
  if Nat.leb (wordToNat y) (wordToNat x) then wordToNat x - wordToNat y else wordToNat y - wordToNat x.
Proof.
  intros n x y. unfold hw_absdiffw. rewrite hw_ltb_nat.
  destruct (Nat.ltb_spec (wordToNat x) (wordToNat y)); destruct (Nat.leb_spec (wordToNat y) (wordToNat x));
    cbn [negb]; try lia; apply wordToNat_wminus_le'; lia.
Qed.

Lemma pow2_mono : forall a b, a <= b -> pow2 a <= pow2 b.
Proof. intros. apply Nat.pow_le_mono_r; lia. Qed.

Lemma m128_nat : forall x y, wordToNat x * wordToNat y < pow2 128 ->
  wordToNat (m128 x y) = wordToNat x * wordToNat y.
Proof.
  intros x y H. unfold m128. rewrite (wordToNat_split1 128 640), wordToNat_wmult, !evalZeroExtendTrunc_nat by lia.
  rewrite (Nat.mod_small (wordToNat x * wordToNat y)) by (eapply Nat.lt_le_trans; [exact H|apply pow2_mono; lia]).
  apply Nat.mod_small. exact H.
Qed.

Lemma m256_nat : forall x y, wordToNat x * wordToNat y < pow2 256 ->
  wordToNat (m256 x y) = wordToNat x * wordToNat y.
Proof.
  intros x y H. unfold m256. rewrite (wordToNat_split1 256 512), wordToNat_wmult, !evalZeroExtendTrunc_nat by lia.
  rewrite (Nat.mod_small (wordToNat x * wordToNat y)) by (eapply Nat.lt_le_trans; [exact H|apply pow2_mono; lia]).
  apply Nat.mod_small. exact H.
Qed.

Lemma m384_nat : forall x y, wordToNat x * wordToNat y < pow2 384 ->
  wordToNat (m384 x y) = wordToNat x * wordToNat y.
Proof.
  intros x y H. unfold m384. rewrite (wordToNat_split1 384 384), wordToNat_wmult, !evalZeroExtendTrunc_nat by lia.
  rewrite (Nat.mod_small (wordToNat x * wordToNat y)) by (eapply Nat.lt_le_trans; [exact H|apply pow2_mono; lia]).
  apply Nat.mod_small. exact H.
Qed.

Lemma mul_pow2_lt : forall x y a b, x < pow2 a -> y < pow2 b -> x * y < pow2 (a + b).
Proof. intros. rewrite Nat.pow_add_r. nia. Qed.

Lemma lt_pow2_mono : forall x a b, x < pow2 a -> a <= b -> x < pow2 b.
Proof. intros. eapply Nat.lt_le_trans; [eassumption|apply pow2_mono; lia]. Qed.

Definition hw_eqb {n} (a b : word n) : bool := if weq a b then true else false.

Lemma hw_eqb_nat : forall n (a b : word n), hw_eqb a b = Nat.eqb (wordToNat a) (wordToNat b).
Proof.
  intros n a b. unfold hw_eqb. destruct (weq a b) as [E|E].
  - subst. symmetry. apply Nat.eqb_refl.
  - symmetry. apply Nat.eqb_neq. intro H. apply E. apply wordToNat_inj. exact H.
Qed.

(** Values the step rule latches for one setting pair. *)
Definition chsh_latch_n (s d : word 32) : word 64 := wplus (zext s 32) (zext d 32).
Definition chsh_latch_sign (s d : word 32) : bool := hw_ltb (zext s 32) (zext d 32).
Definition chsh_latch_abs (s d : word 32) : word 64 :=
  if chsh_latch_sign s d then wminus (zext d 32) (zext s 32) else wminus (zext s 32) (zext d 32).

(** The FSM's arithmetic over the latched values. *)
Definition chsh_check_word (n00 n01 n10 n11 a00 a01 a10 a11 : word 64) (g00 g01 g10 g11 : bool) : bool :=
  let n00sq := m128 n00 n00 in let n01sq := m128 n01 n01 in
  let n10sq := m128 n10 n10 in let n11sq := m128 n11 n11 in
  let d00sq := m128 a00 a00 in let d01sq := m128 a01 a01 in
  let d10sq := m128 a10 a10 in let d11sq := m128 a11 a11 in
  let A_pos := m256 n00sq n10sq in
  let A_neg := wplus (m256 d00sq n10sq) (m256 d10sq n00sq) in
  let B_pos := m256 n01sq n11sq in
  let B_neg := wplus (m256 d01sq n11sq) (m256 d11sq n01sq) in
  let C1 := m256 (m128 a00 a01) (m128 n10 n11) in
  let C2 := m256 (m128 a10 a11) (m128 n00 n01) in
  let absC := if Bool.eqb (xorb g00 g01) (xorb g10 g11) then wplus C1 C2 else hw_absdiffw C1 C2 in
  let A_ge0 := negb (hw_ltb A_pos A_neg) in
  let B_ge0 := negb (hw_ltb B_pos B_neg) in
  let Csq := m384 absC absC in
  let AB := m384 (hw_absdiffw A_pos A_neg) (hw_absdiffw B_pos B_neg) in
  andb (andb (andb (andb (negb (hw_eqb n00 (natToWord 64 0))) (negb (hw_eqb n01 (natToWord 64 0))))
                   (andb (negb (hw_eqb n10 (natToWord 64 0))) (negb (hw_eqb n11 (natToWord 64 0)))))
             (andb A_ge0 B_ge0))
       (negb (hw_ltb AB Csq)).



(** Natural-number form of the CHSH_LASSERT hardware check: sums, absolute
    differences with sign bits, and unsigned magnitudes with sign tracking. *)
Definition chsh_absd (s d : nat) : nat := if Nat.ltb s d then d - s else s - d.
Definition chsh_sign (s d : nat) : bool := Nat.ltb s d.
Definition chsh_absdiff (x y : nat) : nat := if Nat.leb y x then x - y else y - x.

Definition chsh_absC (s1 s2 : bool) (c1 c2 : nat) : nat :=
  if Bool.eqb s1 s2 then c1 + c2 else chsh_absdiff c1 c2.

Definition chsh_check_nat (s00 d00 s01 d01 s10 d10 s11 d11 : nat) : bool :=
  let n00 := s00 + d00 in let n01 := s01 + d01 in
  let n10 := s10 + d10 in let n11 := s11 + d11 in
  let a00 := chsh_absd s00 d00 in let a01 := chsh_absd s01 d01 in
  let a10 := chsh_absd s10 d10 in let a11 := chsh_absd s11 d11 in
  let A_pos := (n00 * n00) * (n10 * n10) in
  let A_neg := (a00 * a00) * (n10 * n10) + (a10 * a10) * (n00 * n00) in
  let B_pos := (n01 * n01) * (n11 * n11) in
  let B_neg := (a01 * a01) * (n11 * n11) + (a11 * a11) * (n01 * n01) in
  let C1 := (a00 * a01) * (n10 * n11) in
  let C2 := (a10 * a11) * (n00 * n01) in
  let absC := chsh_absC (xorb (chsh_sign s00 d00) (chsh_sign s01 d01))
                        (xorb (chsh_sign s10 d10) (chsh_sign s11 d11)) C1 C2 in
  let A_ge0 := Nat.leb A_neg A_pos in
  let B_ge0 := Nat.leb B_neg B_pos in
  let absA := chsh_absdiff A_pos A_neg in
  let absB := chsh_absdiff B_pos B_neg in
  andb (andb (andb (andb (negb (Nat.eqb n00 0)) (negb (Nat.eqb n01 0)))
                   (andb (negb (Nat.eqb n10 0)) (negb (Nat.eqb n11 0))))
             (andb A_ge0 B_ge0))
       (Nat.leb (absC * absC) (absA * absB)).

(** The signed difference is the sign-adjusted magnitude. *)
Lemma chsh_d_z_absd : forall s d,
  chsh_d_z s d = if chsh_sign s d then (- Z.of_nat (chsh_absd s d))%Z else Z.of_nat (chsh_absd s d).
Proof.
  intros s d. unfold chsh_d_z, chsh_sign, chsh_absd.
  destruct (Nat.ltb_spec s d); rewrite Nat2Z.inj_sub by lia; lia.
Qed.

Lemma chsh_n_z_nat : forall s d, chsh_n_z s d = Z.of_nat (s + d).
Proof. intros. unfold chsh_n_z. lia. Qed.

Lemma chsh_d_z_sq : forall s d,
  (chsh_d_z s d * chsh_d_z s d)%Z = Z.of_nat (chsh_absd s d * chsh_absd s d).
Proof.
  intros s d. rewrite chsh_d_z_absd, Nat2Z.inj_mul.
  destruct (chsh_sign s d); ring.
Qed.

Lemma Z_of_nat_absdiff : forall x y,
  Z.of_nat (chsh_absdiff x y) = Z.abs (Z.of_nat x - Z.of_nat y).
Proof.
  intros x y. unfold chsh_absdiff. destruct (Nat.leb_spec y x); rewrite Nat2Z.inj_sub by lia; lia.
Qed.

Lemma sign_mult : forall (s1 s2 : bool) (x y : Z),
  ((if s1 then - x else x) * (if s2 then - y else y))%Z =
  (if xorb s1 s2 then - (x * y) else x * y)%Z.
Proof. intros [|] [|] x y; cbn; ring. Qed.

Lemma abs_C_nat : forall (s1 s2 : bool) (c1 c2 : nat),
  Z.of_nat (chsh_absC s1 s2 c1 c2 * chsh_absC s1 s2 c1 c2) =
  (((if s1 then - Z.of_nat c1 else Z.of_nat c1) + (if s2 then - Z.of_nat c2 else Z.of_nat c2)) *
   ((if s1 then - Z.of_nat c1 else Z.of_nat c1) + (if s2 then - Z.of_nat c2 else Z.of_nat c2)))%Z.
Proof.
  intros s1 s2 c1 c2. unfold chsh_absC. rewrite Nat2Z.inj_mul.
  assert (Sq : forall u : Z, (Z.abs u * Z.abs u = u * u)%Z)
    by (intro u; rewrite <- Z.abs_mul; apply Z.abs_eq; nia).
  destruct s1, s2; cbn [Bool.eqb]; rewrite ?Nat2Z.inj_add, ?Z_of_nat_absdiff, ?Sq; ring.
Qed.

Lemma Zltb_0_nat : forall n, Z.ltb 0 (Z.of_nat n) = negb (Nat.eqb n 0).
Proof. intro n. destruct n; reflexivity. Qed.

Lemma Zleb_0_sub_nat : forall p q, Z.leb 0 (Z.of_nat p - Z.of_nat q) = Nat.leb q p.
Proof.
  intros p q. destruct (Nat.leb_spec q p); [apply Z.leb_le|apply Z.leb_gt]; lia.
Qed.

Lemma Z_absdiff_ge : forall p q, q <= p -> Z.of_nat (chsh_absdiff p q) = (Z.of_nat p - Z.of_nat q)%Z.
Proof. intros p q H. unfold chsh_absdiff. rewrite (proj2 (Nat.leb_le q p) H). lia. Qed.

Lemma Zleb_nat : forall x y, Z.leb (Z.of_nat x) (Z.of_nat y) = Nat.leb x y.
Proof. intros x y. destruct (Nat.leb_spec x y); [apply Z.leb_le|apply Z.leb_gt]; lia. Qed.

Local Open Scope nat_scope.
Theorem chsh_check_nat_correct : forall s00 d00 s01 d01 s10 d10 s11 d11,
  chsh_check_nat s00 d00 s01 d01 s10 d10 s11 d11 =
  column_contractive_check_witness
    {| wc_same_00 := s00; wc_diff_00 := d00; wc_same_01 := s01; wc_diff_01 := d01;
       wc_same_10 := s10; wc_diff_10 := d10; wc_same_11 := s11; wc_diff_11 := d11 |}.
Proof.
  intros. unfold column_contractive_check_witness, chsh_check_nat.
  cbn [wc_same_00 wc_diff_00 wc_same_01 wc_diff_01 wc_same_10 wc_diff_10 wc_same_11 wc_diff_11].
  cbv zeta.
  rewrite !chsh_n_z_nat, !chsh_d_z_sq, !Zltb_0_nat.
  set (N00 := s00 + d00). set (N01 := s01 + d01). set (N10 := s10 + d10). set (N11 := s11 + d11).
  set (a00 := chsh_absd s00 d00). set (a01 := chsh_absd s01 d01).
  set (a10 := chsh_absd s10 d10). set (a11 := chsh_absd s11 d11).
  set (Ap := N00 * N00 * (N10 * N10)). set (An := a00 * a00 * (N10 * N10) + a10 * a10 * (N00 * N00)).
  set (Bp := N01 * N01 * (N11 * N11)). set (Bn := a01 * a01 * (N11 * N11) + a11 * a11 * (N01 * N01)).
  assert (HA : (Z.of_nat N00 * Z.of_nat N00 * (Z.of_nat N10 * Z.of_nat N10) -
                Z.of_nat (a00 * a00) * (Z.of_nat N10 * Z.of_nat N10) -
                Z.of_nat (a10 * a10) * (Z.of_nat N00 * Z.of_nat N00))%Z =
               (Z.of_nat Ap - Z.of_nat An)%Z)
    by (unfold Ap, An; rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_mul; ring).
  assert (HB : (Z.of_nat N01 * Z.of_nat N01 * (Z.of_nat N11 * Z.of_nat N11) -
                Z.of_nat (a01 * a01) * (Z.of_nat N11 * Z.of_nat N11) -
                Z.of_nat (a11 * a11) * (Z.of_nat N01 * Z.of_nat N01))%Z =
               (Z.of_nat Bp - Z.of_nat Bn)%Z)
    by (unfold Bp, Bn; rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_mul; ring).
  rewrite HA, HB, !Zleb_0_sub_nat.
  set (C1 := a00 * a01 * (N10 * N11)). set (C2 := a10 * a11 * (N00 * N01)).
  set (absC := chsh_absC (xorb (chsh_sign s00 d00) (chsh_sign s01 d01))
                         (xorb (chsh_sign s10 d10) (chsh_sign s11 d11)) C1 C2).
  assert (HC : ((chsh_d_z s00 d00 * chsh_d_z s01 d01 * Z.of_nat N10 * Z.of_nat N11 +
                 chsh_d_z s10 d10 * chsh_d_z s11 d11 * Z.of_nat N00 * Z.of_nat N01) *
                (chsh_d_z s00 d00 * chsh_d_z s01 d01 * Z.of_nat N10 * Z.of_nat N11 +
                 chsh_d_z s10 d10 * chsh_d_z s11 d11 * Z.of_nat N00 * Z.of_nat N01))%Z =
                Z.of_nat (absC * absC)).
  { unfold absC. rewrite abs_C_nat. unfold C1, C2. rewrite !chsh_d_z_absd. fold a00 a01 a10 a11.
    destruct (chsh_sign s00 d00), (chsh_sign s01 d01), (chsh_sign s10 d10), (chsh_sign s11 d11);
      cbn [xorb]; rewrite !Nat2Z.inj_mul; ring. }
  rewrite HC.
  destruct (Nat.leb_spec An Ap) as [LA|LA]; destruct (Nat.leb_spec Bn Bp) as [LB|LB];
    rewrite ?andb_false_r, ?andb_false_l; cbn [andb];
    destruct (Nat.eqb N00 0), (Nat.eqb N01 0), (Nat.eqb N10 0), (Nat.eqb N11 0); cbn [negb andb];
    try reflexivity.
  all: unfold chsh_absdiff; rewrite (proj2 (Nat.leb_le _ _) LA), (proj2 (Nat.leb_le _ _) LB).
  all: rewrite <- Zleb_nat; f_equal; rewrite Nat2Z.inj_mul, !Nat2Z.inj_sub by lia; reflexivity.
Qed.

Lemma add_pow2_lt : forall x y a, x < pow2 a -> y < pow2 a -> x + y < pow2 (S a).
Proof. intros. rewrite Nat.pow_succ_r'. lia. Qed.

Lemma absd_lt : forall s d a, s < pow2 a -> d < pow2 a -> chsh_absd s d < pow2 a.
Proof. intros. unfold chsh_absd. destruct (Nat.ltb s d); lia. Qed.

Lemma absdiff_lt : forall x y a, x < pow2 a -> y < pow2 a -> chsh_absdiff x y < pow2 a.
Proof. intros. unfold chsh_absdiff. destruct (Nat.leb y x); lia. Qed.

Lemma latch_n_nat : forall s d : word 32, wordToNat (chsh_latch_n s d) = wordToNat s + wordToNat d.
Proof.
  intros s d. unfold chsh_latch_n. rewrite wordToNat_wplus', !wordToNat_zext; [reflexivity|].
  rewrite !wordToNat_zext. eapply lt_pow2_mono; [apply add_pow2_lt; apply wordToNat_bound|lia].
Qed.

Lemma latch_sign_nat : forall s d : word 32, chsh_latch_sign s d = chsh_sign (wordToNat s) (wordToNat d).
Proof. intros. unfold chsh_latch_sign, chsh_sign. rewrite hw_ltb_nat, !wordToNat_zext. reflexivity. Qed.

Lemma latch_abs_nat : forall s d : word 32, wordToNat (chsh_latch_abs s d) = chsh_absd (wordToNat s) (wordToNat d).
Proof.
  intros s d. unfold chsh_latch_abs, chsh_absd. rewrite latch_sign_nat. unfold chsh_sign.
  destruct (Nat.ltb_spec (wordToNat s) (wordToNat d));
    rewrite wordToNat_wminus_le', !wordToNat_zext; rewrite ?wordToNat_zext; lia.
Qed.

Theorem chsh_check_word_correct : forall s00 d00 s01 d01 s10 d10 s11 d11 : word 32,
  chsh_check_word (chsh_latch_n s00 d00) (chsh_latch_n s01 d01) (chsh_latch_n s10 d10) (chsh_latch_n s11 d11)
    (chsh_latch_abs s00 d00) (chsh_latch_abs s01 d01) (chsh_latch_abs s10 d10) (chsh_latch_abs s11 d11)
    (chsh_latch_sign s00 d00) (chsh_latch_sign s01 d01) (chsh_latch_sign s10 d10) (chsh_latch_sign s11 d11) =
  chsh_check_nat (wordToNat s00) (wordToNat d00) (wordToNat s01) (wordToNat d01)
    (wordToNat s10) (wordToNat d10) (wordToNat s11) (wordToNat d11).
Proof.
  intros. unfold chsh_check_word, chsh_check_nat. cbv zeta.
  rewrite !latch_sign_nat.
  pose proof (wordToNat_bound s00) as Bs00. pose proof (wordToNat_bound d00) as Bd00.
  set (nw00 := chsh_latch_n s00 d00). set (aw00 := chsh_latch_abs s00 d00).
  assert (En00 : wordToNat nw00 = wordToNat s00 + wordToNat d00) by apply latch_n_nat.
  assert (Ea00 : wordToNat aw00 = chsh_absd (wordToNat s00) (wordToNat d00)) by apply latch_abs_nat.
  assert (BN00 : wordToNat s00 + wordToNat d00 < pow2 33) by exact (add_pow2_lt _ _ 32 Bs00 Bd00).
  assert (BA00 : chsh_absd (wordToNat s00) (wordToNat d00) < pow2 33) by exact (lt_pow2_mono _ 32 33 (absd_lt _ _ 32 Bs00 Bd00) ltac:(lia)).
  pose proof (wordToNat_bound s01) as Bs01. pose proof (wordToNat_bound d01) as Bd01.
  set (nw01 := chsh_latch_n s01 d01). set (aw01 := chsh_latch_abs s01 d01).
  assert (En01 : wordToNat nw01 = wordToNat s01 + wordToNat d01) by apply latch_n_nat.
  assert (Ea01 : wordToNat aw01 = chsh_absd (wordToNat s01) (wordToNat d01)) by apply latch_abs_nat.
  assert (BN01 : wordToNat s01 + wordToNat d01 < pow2 33) by exact (add_pow2_lt _ _ 32 Bs01 Bd01).
  assert (BA01 : chsh_absd (wordToNat s01) (wordToNat d01) < pow2 33) by exact (lt_pow2_mono _ 32 33 (absd_lt _ _ 32 Bs01 Bd01) ltac:(lia)).
  pose proof (wordToNat_bound s10) as Bs10. pose proof (wordToNat_bound d10) as Bd10.
  set (nw10 := chsh_latch_n s10 d10). set (aw10 := chsh_latch_abs s10 d10).
  assert (En10 : wordToNat nw10 = wordToNat s10 + wordToNat d10) by apply latch_n_nat.
  assert (Ea10 : wordToNat aw10 = chsh_absd (wordToNat s10) (wordToNat d10)) by apply latch_abs_nat.
  assert (BN10 : wordToNat s10 + wordToNat d10 < pow2 33) by exact (add_pow2_lt _ _ 32 Bs10 Bd10).
  assert (BA10 : chsh_absd (wordToNat s10) (wordToNat d10) < pow2 33) by exact (lt_pow2_mono _ 32 33 (absd_lt _ _ 32 Bs10 Bd10) ltac:(lia)).
  pose proof (wordToNat_bound s11) as Bs11. pose proof (wordToNat_bound d11) as Bd11.
  set (nw11 := chsh_latch_n s11 d11). set (aw11 := chsh_latch_abs s11 d11).
  assert (En11 : wordToNat nw11 = wordToNat s11 + wordToNat d11) by apply latch_n_nat.
  assert (Ea11 : wordToNat aw11 = chsh_absd (wordToNat s11) (wordToNat d11)) by apply latch_abs_nat.
  assert (BN11 : wordToNat s11 + wordToNat d11 < pow2 33) by exact (add_pow2_lt _ _ 32 Bs11 Bd11).
  assert (BA11 : chsh_absd (wordToNat s11) (wordToNat d11) < pow2 33) by exact (lt_pow2_mono _ 32 33 (absd_lt _ _ 32 Bs11 Bd11) ltac:(lia)).
  assert (Enn00 : wordToNat (m128 nw00 nw00) = (wordToNat s00 + wordToNat d00) * (wordToNat s00 + wordToNat d00)) by (rewrite m128_nat; rewrite ?En00, ?En00; [reflexivity|eapply lt_pow2_mono; [apply (mul_pow2_lt _ _ 33 33); [exact BN00|exact BN00]|lia]]).
  assert (Eaa00 : wordToNat (m128 aw00 aw00) = (chsh_absd (wordToNat s00) (wordToNat d00)) * (chsh_absd (wordToNat s00) (wordToNat d00))) by (rewrite m128_nat; rewrite ?Ea00, ?Ea00; [reflexivity|eapply lt_pow2_mono; [apply (mul_pow2_lt _ _ 33 33); [exact BA00|exact BA00]|lia]]).
  assert (Enn01 : wordToNat (m128 nw01 nw01) = (wordToNat s01 + wordToNat d01) * (wordToNat s01 + wordToNat d01)) by (rewrite m128_nat; rewrite ?En01, ?En01; [reflexivity|eapply lt_pow2_mono; [apply (mul_pow2_lt _ _ 33 33); [exact BN01|exact BN01]|lia]]).
  assert (Eaa01 : wordToNat (m128 aw01 aw01) = (chsh_absd (wordToNat s01) (wordToNat d01)) * (chsh_absd (wordToNat s01) (wordToNat d01))) by (rewrite m128_nat; rewrite ?Ea01, ?Ea01; [reflexivity|eapply lt_pow2_mono; [apply (mul_pow2_lt _ _ 33 33); [exact BA01|exact BA01]|lia]]).
  assert (Enn10 : wordToNat (m128 nw10 nw10) = (wordToNat s10 + wordToNat d10) * (wordToNat s10 + wordToNat d10)) by (rewrite m128_nat; rewrite ?En10, ?En10; [reflexivity|eapply lt_pow2_mono; [apply (mul_pow2_lt _ _ 33 33); [exact BN10|exact BN10]|lia]]).
  assert (Eaa10 : wordToNat (m128 aw10 aw10) = (chsh_absd (wordToNat s10) (wordToNat d10)) * (chsh_absd (wordToNat s10) (wordToNat d10))) by (rewrite m128_nat; rewrite ?Ea10, ?Ea10; [reflexivity|eapply lt_pow2_mono; [apply (mul_pow2_lt _ _ 33 33); [exact BA10|exact BA10]|lia]]).
  assert (Enn11 : wordToNat (m128 nw11 nw11) = (wordToNat s11 + wordToNat d11) * (wordToNat s11 + wordToNat d11)) by (rewrite m128_nat; rewrite ?En11, ?En11; [reflexivity|eapply lt_pow2_mono; [apply (mul_pow2_lt _ _ 33 33); [exact BN11|exact BN11]|lia]]).
  assert (Eaa11 : wordToNat (m128 aw11 aw11) = (chsh_absd (wordToNat s11) (wordToNat d11)) * (chsh_absd (wordToNat s11) (wordToNat d11))) by (rewrite m128_nat; rewrite ?Ea11, ?Ea11; [reflexivity|eapply lt_pow2_mono; [apply (mul_pow2_lt _ _ 33 33); [exact BA11|exact BA11]|lia]]).
  assert (Ep1 : wordToNat (m128 aw00 aw01) = (chsh_absd (wordToNat s00) (wordToNat d00)) * (chsh_absd (wordToNat s01) (wordToNat d01))) by (rewrite m128_nat; rewrite ?Ea00, ?Ea01; [reflexivity|eapply lt_pow2_mono; [apply (mul_pow2_lt _ _ 33 33); [exact BA00|exact BA01]|lia]]).
  assert (Eq1 : wordToNat (m128 nw10 nw11) = (wordToNat s10 + wordToNat d10) * (wordToNat s11 + wordToNat d11)) by (rewrite m128_nat; rewrite ?En10, ?En11; [reflexivity|eapply lt_pow2_mono; [apply (mul_pow2_lt _ _ 33 33); [exact BN10|exact BN11]|lia]]).
  assert (Ep2 : wordToNat (m128 aw10 aw11) = (chsh_absd (wordToNat s10) (wordToNat d10)) * (chsh_absd (wordToNat s11) (wordToNat d11))) by (rewrite m128_nat; rewrite ?Ea10, ?Ea11; [reflexivity|eapply lt_pow2_mono; [apply (mul_pow2_lt _ _ 33 33); [exact BA10|exact BA11]|lia]]).
  assert (Eq2 : wordToNat (m128 nw00 nw01) = (wordToNat s00 + wordToNat d00) * (wordToNat s01 + wordToNat d01)) by (rewrite m128_nat; rewrite ?En00, ?En01; [reflexivity|eapply lt_pow2_mono; [apply (mul_pow2_lt _ _ 33 33); [exact BN00|exact BN01]|lia]]).
  assert (Sq66 : forall x y, x < pow2 33 -> y < pow2 33 -> x * y < pow2 66)
    by (intros x y Hx Hy; exact (mul_pow2_lt _ _ 33 33 Hx Hy)).
  assert (P132 : forall x y, x < pow2 66 -> y < pow2 66 -> x * y < pow2 132)
    by (intros x y Hx Hy; exact (mul_pow2_lt _ _ 66 66 Hx Hy)).
  assert (EAp : wordToNat (m256 (m128 nw00 nw00) (m128 nw10 nw10)) = ((wordToNat s00 + wordToNat d00) * (wordToNat s00 + wordToNat d00)) * ((wordToNat s10 + wordToNat d10) * (wordToNat s10 + wordToNat d10))) by (rewrite m256_nat; rewrite ?Enn00, ?Enn10; [reflexivity|eapply lt_pow2_mono; [apply P132; [apply Sq66; apply BN00|apply Sq66; apply BN10]|lia]]).
  assert (EAn1 : wordToNat (m256 (m128 aw00 aw00) (m128 nw10 nw10)) = ((chsh_absd (wordToNat s00) (wordToNat d00)) * (chsh_absd (wordToNat s00) (wordToNat d00))) * ((wordToNat s10 + wordToNat d10) * (wordToNat s10 + wordToNat d10))) by (rewrite m256_nat; rewrite ?Eaa00, ?Enn10; [reflexivity|eapply lt_pow2_mono; [apply P132; [apply Sq66; apply BA00|apply Sq66; apply BN10]|lia]]).
  assert (EAn2 : wordToNat (m256 (m128 aw10 aw10) (m128 nw00 nw00)) = ((chsh_absd (wordToNat s10) (wordToNat d10)) * (chsh_absd (wordToNat s10) (wordToNat d10))) * ((wordToNat s00 + wordToNat d00) * (wordToNat s00 + wordToNat d00))) by (rewrite m256_nat; rewrite ?Eaa10, ?Enn00; [reflexivity|eapply lt_pow2_mono; [apply P132; [apply Sq66; apply BA10|apply Sq66; apply BN00]|lia]]).
  assert (EBp : wordToNat (m256 (m128 nw01 nw01) (m128 nw11 nw11)) = ((wordToNat s01 + wordToNat d01) * (wordToNat s01 + wordToNat d01)) * ((wordToNat s11 + wordToNat d11) * (wordToNat s11 + wordToNat d11))) by (rewrite m256_nat; rewrite ?Enn01, ?Enn11; [reflexivity|eapply lt_pow2_mono; [apply P132; [apply Sq66; apply BN01|apply Sq66; apply BN11]|lia]]).
  assert (EBn1 : wordToNat (m256 (m128 aw01 aw01) (m128 nw11 nw11)) = ((chsh_absd (wordToNat s01) (wordToNat d01)) * (chsh_absd (wordToNat s01) (wordToNat d01))) * ((wordToNat s11 + wordToNat d11) * (wordToNat s11 + wordToNat d11))) by (rewrite m256_nat; rewrite ?Eaa01, ?Enn11; [reflexivity|eapply lt_pow2_mono; [apply P132; [apply Sq66; apply BA01|apply Sq66; apply BN11]|lia]]).
  assert (EBn2 : wordToNat (m256 (m128 aw11 aw11) (m128 nw01 nw01)) = ((chsh_absd (wordToNat s11) (wordToNat d11)) * (chsh_absd (wordToNat s11) (wordToNat d11))) * ((wordToNat s01 + wordToNat d01) * (wordToNat s01 + wordToNat d01))) by (rewrite m256_nat; rewrite ?Eaa11, ?Enn01; [reflexivity|eapply lt_pow2_mono; [apply P132; [apply Sq66; apply BA11|apply Sq66; apply BN01]|lia]]).
  assert (EC1 : wordToNat (m256 (m128 aw00 aw01) (m128 nw10 nw11)) = ((chsh_absd (wordToNat s00) (wordToNat d00)) * (chsh_absd (wordToNat s01) (wordToNat d01))) * ((wordToNat s10 + wordToNat d10) * (wordToNat s11 + wordToNat d11))) by (rewrite m256_nat; rewrite ?Ep1, ?Eq1; [reflexivity|eapply lt_pow2_mono; [apply P132; [apply Sq66; [apply BA00|apply BA01]|apply Sq66; [apply BN10|apply BN11]]|lia]]).
  assert (EC2 : wordToNat (m256 (m128 aw10 aw11) (m128 nw00 nw01)) = ((chsh_absd (wordToNat s10) (wordToNat d10)) * (chsh_absd (wordToNat s11) (wordToNat d11))) * ((wordToNat s00 + wordToNat d00) * (wordToNat s01 + wordToNat d01))) by (rewrite m256_nat; rewrite ?Ep2, ?Eq2; [reflexivity|eapply lt_pow2_mono; [apply P132; [apply Sq66; [apply BA10|apply BA11]|apply Sq66; [apply BN00|apply BN01]]|lia]]).
  rewrite !hw_ltb_nat, !hw_eqb_nat.
  assert (BAp : (wordToNat s00 + wordToNat d00) * (wordToNat s00 + wordToNat d00) * ((wordToNat s10 + wordToNat d10) * (wordToNat s10 + wordToNat d10)) < pow2 132) by exact (P132 _ _ (Sq66 _ _ BN00 BN00) (Sq66 _ _ BN10 BN10)).
  assert (BAn : (chsh_absd (wordToNat s00) (wordToNat d00)) * (chsh_absd (wordToNat s00) (wordToNat d00)) * ((wordToNat s10 + wordToNat d10) * (wordToNat s10 + wordToNat d10)) + (chsh_absd (wordToNat s10) (wordToNat d10)) * (chsh_absd (wordToNat s10) (wordToNat d10)) * ((wordToNat s00 + wordToNat d00) * (wordToNat s00 + wordToNat d00)) < pow2 133) by exact (add_pow2_lt _ _ 132 (P132 _ _ (Sq66 _ _ BA00 BA00) (Sq66 _ _ BN10 BN10)) (P132 _ _ (Sq66 _ _ BA10 BA10) (Sq66 _ _ BN00 BN00))).
  assert (BBp : (wordToNat s01 + wordToNat d01) * (wordToNat s01 + wordToNat d01) * ((wordToNat s11 + wordToNat d11) * (wordToNat s11 + wordToNat d11)) < pow2 132) by exact (P132 _ _ (Sq66 _ _ BN01 BN01) (Sq66 _ _ BN11 BN11)).
  assert (BBn : (chsh_absd (wordToNat s01) (wordToNat d01)) * (chsh_absd (wordToNat s01) (wordToNat d01)) * ((wordToNat s11 + wordToNat d11) * (wordToNat s11 + wordToNat d11)) + (chsh_absd (wordToNat s11) (wordToNat d11)) * (chsh_absd (wordToNat s11) (wordToNat d11)) * ((wordToNat s01 + wordToNat d01) * (wordToNat s01 + wordToNat d01)) < pow2 133) by exact (add_pow2_lt _ _ 132 (P132 _ _ (Sq66 _ _ BA01 BA01) (Sq66 _ _ BN11 BN11)) (P132 _ _ (Sq66 _ _ BA11 BA11) (Sq66 _ _ BN01 BN01))).
  assert (BC1 : (chsh_absd (wordToNat s00) (wordToNat d00)) * (chsh_absd (wordToNat s01) (wordToNat d01)) * ((wordToNat s10 + wordToNat d10) * (wordToNat s11 + wordToNat d11)) < pow2 132) by exact (P132 _ _ (Sq66 _ _ BA00 BA01) (Sq66 _ _ BN10 BN11)).
  assert (BC2 : (chsh_absd (wordToNat s10) (wordToNat d10)) * (chsh_absd (wordToNat s11) (wordToNat d11)) * ((wordToNat s00 + wordToNat d00) * (wordToNat s01 + wordToNat d01)) < pow2 132) by exact (P132 _ _ (Sq66 _ _ BA10 BA11) (Sq66 _ _ BN00 BN01)).
  assert (EAnw : wordToNat (wplus (m256 (m128 aw00 aw00) (m128 nw10 nw10)) (m256 (m128 aw10 aw10) (m128 nw00 nw00))) = (chsh_absd (wordToNat s00) (wordToNat d00)) * (chsh_absd (wordToNat s00) (wordToNat d00)) * ((wordToNat s10 + wordToNat d10) * (wordToNat s10 + wordToNat d10)) + (chsh_absd (wordToNat s10) (wordToNat d10)) * (chsh_absd (wordToNat s10) (wordToNat d10)) * ((wordToNat s00 + wordToNat d00) * (wordToNat s00 + wordToNat d00))).
  { rewrite wordToNat_wplus', EAn1, EAn2; [reflexivity|]. rewrite EAn1, EAn2.
    exact (lt_pow2_mono _ 133 256 BAn ltac:(lia)). }
  assert (EBnw : wordToNat (wplus (m256 (m128 aw01 aw01) (m128 nw11 nw11)) (m256 (m128 aw11 aw11) (m128 nw01 nw01))) = (chsh_absd (wordToNat s01) (wordToNat d01)) * (chsh_absd (wordToNat s01) (wordToNat d01)) * ((wordToNat s11 + wordToNat d11) * (wordToNat s11 + wordToNat d11)) + (chsh_absd (wordToNat s11) (wordToNat d11)) * (chsh_absd (wordToNat s11) (wordToNat d11)) * ((wordToNat s01 + wordToNat d01) * (wordToNat s01 + wordToNat d01))).
  { rewrite wordToNat_wplus', EBn1, EBn2; [reflexivity|]. rewrite EBn1, EBn2.
    exact (lt_pow2_mono _ 133 256 BBn ltac:(lia)). }
  assert (EabsA : wordToNat (hw_absdiffw (m256 (m128 nw00 nw00) (m128 nw10 nw10)) (wplus (m256 (m128 aw00 aw00) (m128 nw10 nw10)) (m256 (m128 aw10 aw10) (m128 nw00 nw00)))) = chsh_absdiff ((wordToNat s00 + wordToNat d00) * (wordToNat s00 + wordToNat d00) * ((wordToNat s10 + wordToNat d10) * (wordToNat s10 + wordToNat d10))) ((chsh_absd (wordToNat s00) (wordToNat d00)) * (chsh_absd (wordToNat s00) (wordToNat d00)) * ((wordToNat s10 + wordToNat d10) * (wordToNat s10 + wordToNat d10)) + (chsh_absd (wordToNat s10) (wordToNat d10)) * (chsh_absd (wordToNat s10) (wordToNat d10)) * ((wordToNat s00 + wordToNat d00) * (wordToNat s00 + wordToNat d00))))
    by (rewrite hw_absdiffw_nat, EAp, EAnw; reflexivity).
  assert (EabsB : wordToNat (hw_absdiffw (m256 (m128 nw01 nw01) (m128 nw11 nw11)) (wplus (m256 (m128 aw01 aw01) (m128 nw11 nw11)) (m256 (m128 aw11 aw11) (m128 nw01 nw01)))) = chsh_absdiff ((wordToNat s01 + wordToNat d01) * (wordToNat s01 + wordToNat d01) * ((wordToNat s11 + wordToNat d11) * (wordToNat s11 + wordToNat d11))) ((chsh_absd (wordToNat s01) (wordToNat d01)) * (chsh_absd (wordToNat s01) (wordToNat d01)) * ((wordToNat s11 + wordToNat d11) * (wordToNat s11 + wordToNat d11)) + (chsh_absd (wordToNat s11) (wordToNat d11)) * (chsh_absd (wordToNat s11) (wordToNat d11)) * ((wordToNat s01 + wordToNat d01) * (wordToNat s01 + wordToNat d01))))
    by (rewrite hw_absdiffw_nat, EBp, EBnw; reflexivity).
  assert (BabsA : chsh_absdiff ((wordToNat s00 + wordToNat d00) * (wordToNat s00 + wordToNat d00) * ((wordToNat s10 + wordToNat d10) * (wordToNat s10 + wordToNat d10))) ((chsh_absd (wordToNat s00) (wordToNat d00)) * (chsh_absd (wordToNat s00) (wordToNat d00)) * ((wordToNat s10 + wordToNat d10) * (wordToNat s10 + wordToNat d10)) + (chsh_absd (wordToNat s10) (wordToNat d10)) * (chsh_absd (wordToNat s10) (wordToNat d10)) * ((wordToNat s00 + wordToNat d00) * (wordToNat s00 + wordToNat d00))) < pow2 133)
    by exact (absdiff_lt _ _ 133 (lt_pow2_mono _ 132 133 BAp ltac:(lia)) BAn).
  assert (BabsB : chsh_absdiff ((wordToNat s01 + wordToNat d01) * (wordToNat s01 + wordToNat d01) * ((wordToNat s11 + wordToNat d11) * (wordToNat s11 + wordToNat d11))) ((chsh_absd (wordToNat s01) (wordToNat d01)) * (chsh_absd (wordToNat s01) (wordToNat d01)) * ((wordToNat s11 + wordToNat d11) * (wordToNat s11 + wordToNat d11)) + (chsh_absd (wordToNat s11) (wordToNat d11)) * (chsh_absd (wordToNat s11) (wordToNat d11)) * ((wordToNat s01 + wordToNat d01) * (wordToNat s01 + wordToNat d01))) < pow2 133)
    by exact (absdiff_lt _ _ 133 (lt_pow2_mono _ 132 133 BBp ltac:(lia)) BBn).
  assert (EabsC : wordToNat (if Bool.eqb (xorb (chsh_sign (wordToNat s00) (wordToNat d00)) (chsh_sign (wordToNat s01) (wordToNat d01))) (xorb (chsh_sign (wordToNat s10) (wordToNat d10)) (chsh_sign (wordToNat s11) (wordToNat d11))) then wplus (m256 (m128 aw00 aw01) (m128 nw10 nw11)) (m256 (m128 aw10 aw11) (m128 nw00 nw01)) else hw_absdiffw (m256 (m128 aw00 aw01) (m128 nw10 nw11)) (m256 (m128 aw10 aw11) (m128 nw00 nw01))) = chsh_absC (xorb (chsh_sign (wordToNat s00) (wordToNat d00)) (chsh_sign (wordToNat s01) (wordToNat d01))) (xorb (chsh_sign (wordToNat s10) (wordToNat d10)) (chsh_sign (wordToNat s11) (wordToNat d11))) ((chsh_absd (wordToNat s00) (wordToNat d00)) * (chsh_absd (wordToNat s01) (wordToNat d01)) * ((wordToNat s10 + wordToNat d10) * (wordToNat s11 + wordToNat d11))) ((chsh_absd (wordToNat s10) (wordToNat d10)) * (chsh_absd (wordToNat s11) (wordToNat d11)) * ((wordToNat s00 + wordToNat d00) * (wordToNat s01 + wordToNat d01)))).
  { unfold chsh_absC. destruct (Bool.eqb _ _).
    - rewrite wordToNat_wplus', EC1, EC2; [reflexivity|]. rewrite EC1, EC2.
      exact (lt_pow2_mono _ 133 256 (add_pow2_lt _ _ 132 BC1 BC2) ltac:(lia)).
    - rewrite hw_absdiffw_nat, EC1, EC2. reflexivity. }
  assert (BabsC : chsh_absC (xorb (chsh_sign (wordToNat s00) (wordToNat d00)) (chsh_sign (wordToNat s01) (wordToNat d01))) (xorb (chsh_sign (wordToNat s10) (wordToNat d10)) (chsh_sign (wordToNat s11) (wordToNat d11))) ((chsh_absd (wordToNat s00) (wordToNat d00)) * (chsh_absd (wordToNat s01) (wordToNat d01)) * ((wordToNat s10 + wordToNat d10) * (wordToNat s11 + wordToNat d11))) ((chsh_absd (wordToNat s10) (wordToNat d10)) * (chsh_absd (wordToNat s11) (wordToNat d11)) * ((wordToNat s00 + wordToNat d00) * (wordToNat s01 + wordToNat d01))) < pow2 133).
  { unfold chsh_absC. destruct (Bool.eqb _ _).
    - exact (add_pow2_lt _ _ 132 BC1 BC2).
    - exact (absdiff_lt _ _ 133 (lt_pow2_mono _ 132 133 BC1 ltac:(lia)) (lt_pow2_mono _ 132 133 BC2 ltac:(lia))). }
  assert (P266 : forall x y, x < pow2 133 -> y < pow2 133 -> x * y < pow2 384)
    by (intros x y Hx Hy; exact (lt_pow2_mono _ 266 384 (mul_pow2_lt _ _ 133 133 Hx Hy) ltac:(lia))).
  rewrite (m384_nat ((if Bool.eqb (xorb (chsh_sign (wordToNat s00) (wordToNat d00)) (chsh_sign (wordToNat s01) (wordToNat d01))) (xorb (chsh_sign (wordToNat s10) (wordToNat d10)) (chsh_sign (wordToNat s11) (wordToNat d11))) then wplus (m256 (m128 aw00 aw01) (m128 nw10 nw11)) (m256 (m128 aw10 aw11) (m128 nw00 nw01)) else hw_absdiffw (m256 (m128 aw00 aw01) (m128 nw10 nw11)) (m256 (m128 aw10 aw11) (m128 nw00 nw01)))) ((if Bool.eqb (xorb (chsh_sign (wordToNat s00) (wordToNat d00)) (chsh_sign (wordToNat s01) (wordToNat d01))) (xorb (chsh_sign (wordToNat s10) (wordToNat d10)) (chsh_sign (wordToNat s11) (wordToNat d11))) then wplus (m256 (m128 aw00 aw01) (m128 nw10 nw11)) (m256 (m128 aw10 aw11) (m128 nw00 nw01)) else hw_absdiffw (m256 (m128 aw00 aw01) (m128 nw10 nw11)) (m256 (m128 aw10 aw11) (m128 nw00 nw01))))) by (rewrite EabsC; exact (P266 _ _ BabsC BabsC)).
  rewrite (m384_nat (hw_absdiffw (m256 (m128 nw00 nw00) (m128 nw10 nw10)) (wplus (m256 (m128 aw00 aw00) (m128 nw10 nw10)) (m256 (m128 aw10 aw10) (m128 nw00 nw00)))) (hw_absdiffw (m256 (m128 nw01 nw01) (m128 nw11 nw11)) (wplus (m256 (m128 aw01 aw01) (m128 nw11 nw11)) (m256 (m128 aw11 aw11) (m128 nw01 nw01)))))
    by (rewrite EabsA, EabsB; exact (P266 _ _ BabsA BabsB)).
  rewrite EabsC, EabsA, EabsB, EAp, EAnw, EBp, EBnw, En00, En01, En10, En11.
  change (wordToNat (natToWord 64 0)) with 0.
  rewrite <- !Nat.leb_antisym. reflexivity.
Qed.

(** The hardware check over the latched counters is the VM's column-contractive check. *)
Theorem chsh_check_word_spec : forall s00 d00 s01 d01 s10 d10 s11 d11 : word 32,
  chsh_check_word (chsh_latch_n s00 d00) (chsh_latch_n s01 d01) (chsh_latch_n s10 d10) (chsh_latch_n s11 d11)
    (chsh_latch_abs s00 d00) (chsh_latch_abs s01 d01) (chsh_latch_abs s10 d10) (chsh_latch_abs s11 d11)
    (chsh_latch_sign s00 d00) (chsh_latch_sign s01 d01) (chsh_latch_sign s10 d10) (chsh_latch_sign s11 d11) =
  column_contractive_check_witness
    {| wc_same_00 := wordToNat s00; wc_diff_00 := wordToNat d00;
       wc_same_01 := wordToNat s01; wc_diff_01 := wordToNat d01;
       wc_same_10 := wordToNat s10; wc_diff_10 := wordToNat d10;
       wc_same_11 := wordToNat s11; wc_diff_11 := wordToNat d11 |}.
Proof. intros. rewrite chsh_check_word_correct. apply chsh_check_nat_correct. Qed.

(** The FSM's final boolean in the hardware's own form: left-nested
    conjunctions, and sign agreement through [bool_dec]. *)
Definition hw_bool_neq (x y : bool) : bool := negb (if bool_dec x y then true else false).

Definition chsh_check_word_hw (n00 n01 n10 n11 a00 a01 a10 a11 : word 64) (g00 g01 g10 g11 : bool) : bool :=
  let n00sq := m128 n00 n00 in let n01sq := m128 n01 n01 in
  let n10sq := m128 n10 n10 in let n11sq := m128 n11 n11 in
  let d00sq := m128 a00 a00 in let d01sq := m128 a01 a01 in
  let d10sq := m128 a10 a10 in let d11sq := m128 a11 a11 in
  let A_pos := m256 n00sq n10sq in
  let A_neg := wplus (m256 d00sq n10sq) (m256 d10sq n00sq) in
  let B_pos := m256 n01sq n11sq in
  let B_neg := wplus (m256 d01sq n11sq) (m256 d11sq n01sq) in
  let C1 := m256 (m128 a00 a01) (m128 n10 n11) in
  let C2 := m256 (m128 a10 a11) (m128 n00 n01) in
  let agree := if bool_dec (hw_bool_neq g00 g01) (hw_bool_neq g10 g11) then true else false in
  let absC := if agree then wplus C1 C2 else hw_absdiffw C1 C2 in
  let A_ge0 := negb (hw_ltb A_pos A_neg) in
  let B_ge0 := negb (hw_ltb B_pos B_neg) in
  let Csq := m384 absC absC in
  let AB := m384 (hw_absdiffw A_pos A_neg) (hw_absdiffw B_pos B_neg) in
  andb (andb (andb (andb (andb (andb (negb (hw_eqb n00 (natToWord 64 0))) (negb (hw_eqb n01 (natToWord 64 0))))
                   (negb (hw_eqb n10 (natToWord 64 0)))) (negb (hw_eqb n11 (natToWord 64 0))))
             A_ge0) B_ge0)
       (negb (hw_ltb AB Csq)).

Lemma andb_regroup7 : forall a b c d e f g : bool,
  andb (andb (andb (andb (andb (andb a b) c) d) e) f) g =
  andb (andb (andb (andb a b) (andb c d)) (andb e f)) g.
Proof. intros [|] [|] [|] [|] [|] [|] [|]; reflexivity. Qed.

Lemma hw_sign_agree : forall g00 g01 g10 g11 : bool,
  (if bool_dec (hw_bool_neq g00 g01) (hw_bool_neq g10 g11) then true else false) =
  Bool.eqb (xorb g00 g01) (xorb g10 g11).
Proof. intros [|] [|] [|] [|]; reflexivity. Qed.

Lemma chsh_check_word_hw_eq : forall n00 n01 n10 n11 a00 a01 a10 a11 g00 g01 g10 g11,
  chsh_check_word_hw n00 n01 n10 n11 a00 a01 a10 a11 g00 g01 g10 g11 =
  chsh_check_word n00 n01 n10 n11 a00 a01 a10 a11 g00 g01 g10 g11.
Proof.
  intros. unfold chsh_check_word_hw, chsh_check_word. cbv zeta.
  rewrite hw_sign_agree. apply andb_regroup7.
Qed.

Theorem chsh_check_word_hw_spec : forall s00 d00 s01 d01 s10 d10 s11 d11 : word 32,
  chsh_check_word_hw (chsh_latch_n s00 d00) (chsh_latch_n s01 d01) (chsh_latch_n s10 d10) (chsh_latch_n s11 d11)
    (chsh_latch_abs s00 d00) (chsh_latch_abs s01 d01) (chsh_latch_abs s10 d10) (chsh_latch_abs s11 d11)
    (chsh_latch_sign s00 d00) (chsh_latch_sign s01 d01) (chsh_latch_sign s10 d10) (chsh_latch_sign s11 d11) =
  column_contractive_check_witness
    {| wc_same_00 := wordToNat s00; wc_diff_00 := wordToNat d00;
       wc_same_01 := wordToNat s01; wc_diff_01 := wordToNat d01;
       wc_same_10 := wordToNat s10; wc_diff_10 := wordToNat d10;
       wc_same_11 := wordToNat s11; wc_diff_11 := wordToNat d11 |}.
Proof. intros. rewrite chsh_check_word_hw_eq. apply chsh_check_word_spec. Qed.
