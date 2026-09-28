(** Executable variable-width encoding for the fixed Minsky interpreter. *)
From Coq Require Import Arith Lia List.
From Coq Require Import NArith.NArith.
Import ListNotations.
From Kernel Require Import VMState VMUnboundedStep VMUnboundedInterpreterSlots.
From Kernel Require Import VMUnboundedMinskyInterpreter.

Fixpoint encode_minsky_program_N (width : nat) (p : list MinskyInstrU) : N :=
  match p with
  | [] => 0%N
  | i :: rest =>
      (N.of_nat (encode_minsky_instr i) +
       2 ^ N.of_nat width * encode_minsky_program_N width rest)%N
  end.

Definition encode_minsky_program (width : nat) (p : list MinskyInstrU) : nat :=
  N.to_nat (encode_minsky_program_N width p).

Definition minsky_program_fits (width : nat) (p : list MinskyInstrU) : Prop :=
  Forall (fun i => (N.of_nat (encode_minsky_instr i) < 2 ^ N.of_nat width)%N) p.

(** A computable width for every finite guest program.  It is deliberately
    simple rather than minimal: every encoded word is at most this maximum,
    and [n < 2^n] (with the zero case included) supplies the required fit. *)
Fixpoint minsky_max_word (p : list MinskyInstrU) : nat :=
  match p with
  | [] => 0
  | i :: rest => Nat.max (encode_minsky_instr i) (minsky_max_word rest)
  end.

Definition minsky_encoding_width (p : list MinskyInstrU) : nat :=
  minsky_max_word p.

Lemma minsky_word_le_max : forall p i,
  In i p -> encode_minsky_instr i <= minsky_max_word p.
Proof.
  induction p as [|head rest IH]; intros i Hin; cbn in *.
  - contradiction.
  - destruct Hin as [->|Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

Lemma nat_to_N_le : forall a b,
  a <= b -> (N.of_nat a <= N.of_nat b)%N.
Proof.
  intros a b Hab. apply (proj1 (N.compare_le_iff _ _)).
  rewrite <- Nat2N.inj_compare.
  apply (proj2 (Nat.compare_le_iff _ _)). exact Hab.
Qed.

Theorem minsky_program_fits_encoding_width : forall p,
  minsky_program_fits (minsky_encoding_width p) p.
Proof.
  intro p. apply Forall_forall. intros i Hin.
  eapply N.le_lt_trans.
  - apply nat_to_N_le. apply minsky_word_le_max. exact Hin.
  - unfold minsky_encoding_width. apply N.pow_gt_lin_r. lia.
Qed.

Definition minsky_fetch_N (code : N) (width pc : nat) : N :=
  N.land (N.shiftr code (N.of_nat pc * N.of_nat width)) (N.ones (N.of_nat width)).

Lemma encode_minsky_drop_head : forall width i rest,
  (N.of_nat (encode_minsky_instr i) < 2 ^ N.of_nat width)%N ->
  N.shiftr (encode_minsky_program_N width (i :: rest)) (N.of_nat width) =
  encode_minsky_program_N width rest.
Proof.
  intros width i rest Hfit. cbn [encode_minsky_program_N].
  rewrite N.shiftr_div_pow2.
  replace (2 ^ N.of_nat width * encode_minsky_program_N width rest)%N with
          (encode_minsky_program_N width rest * 2 ^ N.of_nat width)%N by lia.
  rewrite N.div_add by (pose proof (N.pow_nonzero 2 (N.of_nat width) ltac:(lia)); lia).
  rewrite N.div_small by exact Hfit. lia.
Qed.

Theorem encode_minsky_program_fetch_N : forall p width pc,
  minsky_program_fits width p -> pc < length p ->
  minsky_fetch_N (encode_minsky_program_N width p) width pc =
  N.of_nat (encode_minsky_instr (nth pc p MU_Halt)).
Proof.
  induction p as [|i rest IH]; intros width [|pc] Hfit Hpc; cbn [length] in Hpc; try lia.
  - inversion Hfit as [|? ? Hi Hrest]; subst.
    cbn [encode_minsky_program_N nth]. unfold minsky_fetch_N.
    replace (N.of_nat 0 * N.of_nat width)%N with 0%N by reflexivity.
    rewrite N.shiftr_0_r.
    rewrite N.land_ones.
    symmetry. apply (N.mod_unique _ (2 ^ N.of_nat width)
      (encode_minsky_program_N width rest) (N.of_nat (encode_minsky_instr i))).
    + exact Hi.
    + ring.
  - inversion Hfit as [|? ? Hi Hrest]; subst.
    unfold minsky_fetch_N.
    replace (N.of_nat (S pc) * N.of_nat width)%N with
            (N.of_nat width + N.of_nat pc * N.of_nat width)%N by
      (rewrite Nat2N.inj_succ; lia).
    rewrite <- N.shiftr_shiftr, encode_minsky_drop_head by exact Hi.
    change (minsky_fetch_N (encode_minsky_program_N width rest) width pc =
      N.of_nat (encode_minsky_instr (nth pc rest MU_Halt))).
    apply IH; [exact Hrest|lia].
Qed.

Theorem encode_minsky_program_fetch_N_outside : forall p width pc,
  minsky_program_fits width p -> length p <= pc ->
  minsky_fetch_N (encode_minsky_program_N width p) width pc = 0%N.
Proof.
  induction p as [|i rest IH]; intros width [|pc] Hfit Hpc.
  - unfold minsky_fetch_N. cbn [encode_minsky_program_N]. rewrite N.shiftr_0_l.
    reflexivity.
  - unfold minsky_fetch_N. cbn [encode_minsky_program_N]. rewrite N.shiftr_0_l.
    reflexivity.
  - cbn [length] in Hpc. lia.
  - inversion Hfit as [|? ? Hi Hrest]; subst. unfold minsky_fetch_N.
    replace (N.of_nat (S pc) * N.of_nat width)%N with
            (N.of_nat width + N.of_nat pc * N.of_nat width)%N by
      (rewrite Nat2N.inj_succ; lia).
    rewrite <- N.shiftr_shiftr, encode_minsky_drop_head by exact Hi.
    change (minsky_fetch_N (encode_minsky_program_N width rest) width pc = 0%N).
    apply IH; [exact Hrest|cbn [length] in Hpc; lia].
Qed.

Lemma minsky_word_N : forall code width pc,
  N.of_nat (minsky_word code width pc) =
  minsky_fetch_N (N.of_nat code) width pc.
Proof.
  intros code width pc. unfold minsky_word, minsky_fetch_N.
  rewrite N_of_nat_u_and, N_of_nat_u_shr, nat_ones_eq, N2Nat.id.
  rewrite Nat2N.inj_mul. reflexivity.
Qed.

Theorem encode_minsky_program_fetch : forall p width pc,
  minsky_program_fits width p -> pc < length p ->
  minsky_word (encode_minsky_program width p) width pc =
  encode_minsky_instr (nth pc p MU_Halt).
Proof.
  intros p width pc Hfit Hpc. apply Nat2N.inj.
  rewrite minsky_word_N. unfold encode_minsky_program. rewrite N2Nat.id.
  apply encode_minsky_program_fetch_N; assumption.
Qed.

Theorem encode_minsky_program_fetch_outside : forall p width pc,
  minsky_program_fits width p -> length p <= pc ->
  minsky_word (encode_minsky_program width p) width pc = 0.
Proof.
  intros p width pc Hfit Hpc. apply Nat2N.inj. rewrite minsky_word_N.
  unfold encode_minsky_program. rewrite N2Nat.id.
  rewrite encode_minsky_program_fetch_N_outside by assumption. reflexivity.
Qed.

(** The concrete B3 input encoding.  Guest program and input counters vary
    only in data; the host instruction list remains fixed. *)
Definition minsky_input_encoding (ambient : VMState) (p : list MinskyInstrU)
    (width x0 x1 : nat) : VMState :=
  minsky_boundary ambient (encode_minsky_program width p) width
    {| mc_pc := 0; mc_c0 := x0; mc_c1 := x1 |}.

Definition minsky_config_encoding (ambient : VMState) (p : list MinskyInstrU)
    (width : nat) (c : MinskyConfigU) : VMState :=
  minsky_boundary ambient (encode_minsky_program width p) width c.

(** Total executable data encodings used by the premise-free B3 theorems. *)
Definition minsky_total_input_encoding (ambient : VMState)
    (p : list MinskyInstrU) (x0 x1 : nat) : VMState :=
  minsky_input_encoding ambient p (minsky_encoding_width p) x0 x1.

Definition minsky_total_config_encoding (ambient : VMState)
    (p : list MinskyInstrU) (c : MinskyConfigU) : VMState :=
  minsky_config_encoding ambient p (minsky_encoding_width p) c.
