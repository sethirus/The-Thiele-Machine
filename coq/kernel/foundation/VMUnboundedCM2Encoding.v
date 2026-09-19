(** CM2 variant: jump on successful decrement; zero falls through.
    This is the control convention of Dudenhefner, FSCD 2022, Definition 2.
    The earlier zero-branch Minsky modules are preserved with their own scope.
    https://doi.org/10.4230/LIPIcs.FSCD.2022.16 *)
(** Executable variable-width encoding for the fixed CM2 interpreter. *)
From Coq Require Import Arith Lia List.
From Coq Require Import NArith.NArith.
Import ListNotations.
From Kernel Require Import VMState VMUnboundedStep VMUnboundedInterpreterSlots.
From Kernel Require Import VMUnboundedCM2Interpreter.

Fixpoint encode_cm2_program_N (width : nat) (p : list CM2InstrU) : N :=
  match p with
  | [] => 0%N
  | i :: rest =>
      (N.of_nat (encode_cm2_instr i) +
       2 ^ N.of_nat width * encode_cm2_program_N width rest)%N
  end.

Definition encode_cm2_program (width : nat) (p : list CM2InstrU) : nat :=
  N.to_nat (encode_cm2_program_N width p).

Definition cm2_program_fits (width : nat) (p : list CM2InstrU) : Prop :=
  Forall (fun i => (N.of_nat (encode_cm2_instr i) < 2 ^ N.of_nat width)%N) p.

(** A computable width for every finite guest program.  It is deliberately
    simple rather than minimal: every encoded word is at most this maximum,
    and [n < 2^n] (with the zero case included) supplies the required fit. *)
Fixpoint cm2_max_word (p : list CM2InstrU) : nat :=
  match p with
  | [] => 0
  | i :: rest => Nat.max (encode_cm2_instr i) (cm2_max_word rest)
  end.

Definition cm2_encoding_width (p : list CM2InstrU) : nat :=
  cm2_max_word p.

Lemma cm2_word_le_max : forall p i,
  In i p -> encode_cm2_instr i <= cm2_max_word p.
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

Theorem cm2_program_fits_encoding_width : forall p,
  cm2_program_fits (cm2_encoding_width p) p.
Proof.
  intro p. apply Forall_forall. intros i Hin.
  eapply N.le_lt_trans.
  - apply nat_to_N_le. apply cm2_word_le_max. exact Hin.
  - unfold cm2_encoding_width. apply N.pow_gt_lin_r. lia.
Qed.

Definition cm2_fetch_N (code : N) (width pc : nat) : N :=
  N.land (N.shiftr code (N.of_nat pc * N.of_nat width)) (N.ones (N.of_nat width)).

Lemma encode_cm2_drop_head : forall width i rest,
  (N.of_nat (encode_cm2_instr i) < 2 ^ N.of_nat width)%N ->
  N.shiftr (encode_cm2_program_N width (i :: rest)) (N.of_nat width) =
  encode_cm2_program_N width rest.
Proof.
  intros width i rest Hfit. cbn [encode_cm2_program_N].
  rewrite N.shiftr_div_pow2.
  replace (2 ^ N.of_nat width * encode_cm2_program_N width rest)%N with
          (encode_cm2_program_N width rest * 2 ^ N.of_nat width)%N by lia.
  rewrite N.div_add by (pose proof (N.pow_nonzero 2 (N.of_nat width) ltac:(lia)); lia).
  rewrite N.div_small by exact Hfit. lia.
Qed.

Theorem encode_cm2_program_fetch_N : forall p width pc,
  cm2_program_fits width p -> pc < length p ->
  cm2_fetch_N (encode_cm2_program_N width p) width pc =
  N.of_nat (encode_cm2_instr (nth pc p CM2_Halt)).
Proof.
  induction p as [|i rest IH]; intros width [|pc] Hfit Hpc; cbn [length] in Hpc; try lia.
  - inversion Hfit as [|? ? Hi Hrest]; subst.
    cbn [encode_cm2_program_N nth]. unfold cm2_fetch_N.
    replace (N.of_nat 0 * N.of_nat width)%N with 0%N by reflexivity.
    rewrite N.shiftr_0_r.
    rewrite N.land_ones.
    symmetry. apply (N.mod_unique _ (2 ^ N.of_nat width)
      (encode_cm2_program_N width rest) (N.of_nat (encode_cm2_instr i))).
    + exact Hi.
    + ring.
  - inversion Hfit as [|? ? Hi Hrest]; subst.
    unfold cm2_fetch_N.
    replace (N.of_nat (S pc) * N.of_nat width)%N with
            (N.of_nat width + N.of_nat pc * N.of_nat width)%N by
      (rewrite Nat2N.inj_succ; lia).
    rewrite <- N.shiftr_shiftr, encode_cm2_drop_head by exact Hi.
    change (cm2_fetch_N (encode_cm2_program_N width rest) width pc =
      N.of_nat (encode_cm2_instr (nth pc rest CM2_Halt))).
    apply IH; [exact Hrest|lia].
Qed.

Theorem encode_cm2_program_fetch_N_outside : forall p width pc,
  cm2_program_fits width p -> length p <= pc ->
  cm2_fetch_N (encode_cm2_program_N width p) width pc = 0%N.
Proof.
  induction p as [|i rest IH]; intros width [|pc] Hfit Hpc.
  - unfold cm2_fetch_N. cbn [encode_cm2_program_N]. rewrite N.shiftr_0_l.
    reflexivity.
  - unfold cm2_fetch_N. cbn [encode_cm2_program_N]. rewrite N.shiftr_0_l.
    reflexivity.
  - cbn [length] in Hpc. lia.
  - inversion Hfit as [|? ? Hi Hrest]; subst. unfold cm2_fetch_N.
    replace (N.of_nat (S pc) * N.of_nat width)%N with
            (N.of_nat width + N.of_nat pc * N.of_nat width)%N by
      (rewrite Nat2N.inj_succ; lia).
    rewrite <- N.shiftr_shiftr, encode_cm2_drop_head by exact Hi.
    change (cm2_fetch_N (encode_cm2_program_N width rest) width pc = 0%N).
    apply IH; [exact Hrest|cbn [length] in Hpc; lia].
Qed.

Lemma cm2_word_N : forall code width pc,
  N.of_nat (cm2_word code width pc) =
  cm2_fetch_N (N.of_nat code) width pc.
Proof.
  intros code width pc. unfold cm2_word, cm2_fetch_N.
  rewrite N_of_nat_u_and, N_of_nat_u_shr, nat_ones_eq, N2Nat.id.
  rewrite Nat2N.inj_mul. reflexivity.
Qed.

Theorem encode_cm2_program_fetch : forall p width pc,
  cm2_program_fits width p -> pc < length p ->
  cm2_word (encode_cm2_program width p) width pc =
  encode_cm2_instr (nth pc p CM2_Halt).
Proof.
  intros p width pc Hfit Hpc. apply Nat2N.inj.
  rewrite cm2_word_N. unfold encode_cm2_program. rewrite N2Nat.id.
  apply encode_cm2_program_fetch_N; assumption.
Qed.

Theorem encode_cm2_program_fetch_outside : forall p width pc,
  cm2_program_fits width p -> length p <= pc ->
  cm2_word (encode_cm2_program width p) width pc = 0.
Proof.
  intros p width pc Hfit Hpc. apply Nat2N.inj. rewrite cm2_word_N.
  unfold encode_cm2_program. rewrite N2Nat.id.
  rewrite encode_cm2_program_fetch_N_outside by assumption. reflexivity.
Qed.

(** The concrete B3 input encoding.  Guest program and input counters vary
    only in data; the host instruction list remains fixed. *)
Definition cm2_input_encoding (ambient : VMState) (p : list CM2InstrU)
    (width x0 x1 : nat) : VMState :=
  cm2_boundary ambient (encode_cm2_program width p) width
    {| cc_pc := 0; cc_c0 := x0; cc_c1 := x1 |}.

Definition cm2_config_encoding (ambient : VMState) (p : list CM2InstrU)
    (width : nat) (c : CM2ConfigU) : VMState :=
  cm2_boundary ambient (encode_cm2_program width p) width c.

(** Total executable data encodings used by the premise-free B3 theorems. *)
Definition cm2_total_input_encoding (ambient : VMState)
    (p : list CM2InstrU) (x0 x1 : nat) : VMState :=
  cm2_input_encoding ambient p (cm2_encoding_width p) x0 x1.

Definition cm2_total_config_encoding (ambient : VMState)
    (p : list CM2InstrU) (c : CM2ConfigU) : VMState :=
  cm2_config_encoding ambient p (cm2_encoding_width p) c.
