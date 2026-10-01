(** VMGuestMMAInit.v: a cost-free guest prologue that turns the guest input
    [z] into the three-counter start registers that [mma_output_to_guest_r0]
    expects for a one-input [MMA_computable] program with [n] extra counters.

    The start vector of such a program is [(0 :: [z]) ++ Vector.const 0 n].
    Extending it by one output counter, casting it to dimension [3 + n] and
    packing it down to three counters leaves exactly one nonzero counter
    (position 1), whose value is the [n]-fold iterate of
    [x |-> gc_enc godel_coding_235 (0 ## x ## 0 ## vec_nil)] applied to [z].

    The vendored [godel_coding_235] is closed with [Qed], so the numbers
    inside it are not available by computation.  Its recorded law [gc_succ]
    still forces the code of [0 ## x ## 0 ## vec_nil] to be
    [mma_enc_base * mma_enc_step ^ x] for two fixed naturals: the code of the
    zero vector and the prime attached to position 1.  The guest program
    loads those two naturals as immediates and computes the iterate with
    nested multiplication loops.  Under the transparent body of
    [godel_coding_235] they would be 1 and 3, and the iterate would be the
    tower [3 ^ (3 ^ ... z)]; that reading is not provable here because the
    body is opaque, and nothing below depends on it. *)

From Coq Require Import Arith Lia List.
From Undecidability.Shared.Libs.DLW.Utils Require Import godel_coding.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.MinskyMachines Require Import MM MMA.
From Kernel Require Import VMUnboundedStep VMSelfGuest VMSelfRun VMSelfRice
  MMAOutputEpilogue VMMMA3GuestCompiler VMMMAReduction.

Import ListNotations.

(** * 1. The start vector and the guest target registers. *)

(** The start vector of a one-input [MMA_computable] program with [n] extra
    counters, written exactly as [(0 :: v) ++ Vector.const 0 n] with
    [v = [z]] under [VectorNotations]. *)
Definition mma_init_start (z n : nat) : Vector.t nat (S (S n)) :=
  Vector.append (Vector.cons nat 0 1 (Vector.cons nat z 0 (Vector.nil nat)))
    (Vector.const 0 n).

Lemma mma_init_start_cons : forall z n,
  mma_init_start z n = 0 ## z ## Vector.const 0 n.
Proof. reflexivity. Qed.

Definition mma_init_start3 (z n : nat) : vec nat 3 :=
  mma_pack_all n
    (mma_cast_vec (mma_dim_eq n) (mma_extend_vec (mma_init_start z n) 0)).

Definition mma_init_target (z n : nat) : GRegs :=
  gc_g (mma3_guest_start (mma3_swap_vec (mma_init_start3 z n))).

(** * 2. The packing map in closed form. *)

Definition mma_enc (x : nat) : nat :=
  gc_enc godel_coding_235 (0 ## x ## 0 ## vec_nil).

Definition mma_enc_base : nat := gc_enc godel_coding_235 (0 ## 0 ## 0 ## vec_nil).

Definition mma_enc_step : nat := gc_pr godel_coding_235 pos1.

Lemma mma_enc_closed : forall x, mma_enc x = mma_enc_base * mma_enc_step ^ x.
Proof.
  induction x as [|x IH].
  - unfold mma_enc, mma_enc_base. rewrite Nat.pow_0_r, Nat.mul_1_r. reflexivity.
  - unfold mma_enc in *.
    transitivity (gc_pr godel_coding_235 pos1 *
                  gc_enc godel_coding_235 (0 ## x ## 0 ## vec_nil)).
    + rewrite (gc_succ godel_coding_235 pos1 (0 ## x ## 0 ## vec_nil)).
      reflexivity.
    + rewrite IH. unfold mma_enc_step. rewrite Nat.pow_succ_r'. ring.
Qed.

Lemma mma_enc_step_pos : 0 < mma_enc_step.
Proof. apply gc_pr_nz. Qed.

(** The packed value: the [n]-fold iterate of [mma_enc]. *)
Definition mma_tower (n z : nat) : nat := Nat.iter n mma_enc z.

Lemma mma_tower_0 : forall z, mma_tower 0 z = z.
Proof. reflexivity. Qed.

Lemma mma_tower_S : forall n z, mma_tower (S n) z = mma_enc (mma_tower n z).
Proof. reflexivity. Qed.

Lemma mma_iter_shift : forall m (f : nat -> nat) x,
  Nat.iter m f (f x) = Nat.iter (S m) f x.
Proof.
  induction m as [|m IH]; intros f x; [reflexivity|].
  change (f (Nat.iter m f (f x)) = f (Nat.iter (S m) f x)). rewrite IH. reflexivity.
Qed.

(** * 3. Shape of the vectors along the packing chain.

    [mma_shape x v] says that position 1 of [v] holds [x] and every other
    position holds 0. *)

Definition mma_shape {k} (x : nat) (v : vec nat k) : Prop :=
  forall p, vec_pos v p = if Nat.eqb (pos2nat p) 1 then x else 0.

Lemma mma_vec_pos_const : forall n (p : pos n), vec_pos (Vector.const 0 n) p = 0.
Proof.
  induction n as [|n IH]; intro p; pos_inv p; [reflexivity|]. apply IH.
Qed.

Lemma mma_shape_start : forall z n, mma_shape z (mma_init_start z n).
Proof.
  intros z n p. rewrite mma_init_start_cons.
  pos_inv p; [reflexivity|]. pos_inv p; [reflexivity|].
  rewrite !pos2nat_nxt. cbn [Nat.eqb].
  change (vec_pos (Vector.const 0 n) p = 0). apply mma_vec_pos_const.
Qed.

Lemma mma_shape_extend : forall k x (v : vec nat k),
  2 <= k -> mma_shape x v -> mma_shape x (mma_extend_vec v 0).
Proof.
  intros k x v Hk Hv p. unfold mma_extend_vec.
  rewrite <- (pos_lr_both k 1 p). destruct (pos_both k 1 p) as [q|q]; cbn [pos_lr].
  - rewrite vec_pos_app_left, pos2nat_left. apply Hv.
  - rewrite vec_pos_app_right, pos2nat_right.
    replace (Nat.eqb (k + pos2nat q) 1) with false
      by (symmetry; apply Nat.eqb_neq; lia).
    pos_inv q; [reflexivity|]. pos_inv q.
Qed.

Lemma mma_shape_cast : forall a b (e : a = b) x (v : vec nat a),
  mma_shape x v -> mma_shape x (mma_cast_vec e v).
Proof. intros a b e x v Hv. destruct e. exact Hv. Qed.

Lemma mma_shape_pack : forall m x (v : vec nat (3 + m)),
  mma_shape x v -> mma_shape (mma_enc x) (mma_pack_vec m v).
Proof.
  intros m x v Hv.
  assert (Hfront : fst (vec_split 3 m v) = 0 ## x ## 0 ## vec_nil).
  { apply vec_pos_ext. intro p. unfold vec_split. cbn [fst].
    rewrite vec_pos_set, Hv, pos2nat_left.
    destruct (fin3_cases p) as [-> | [-> | ->]]; reflexivity. }
  destruct (mma_pack_vec_sim m v) as (H0 & H1 & Hr).
  intro p. change (pos (S (S m))) in p. pos_inv p.
  - rewrite H0. reflexivity.
  - pos_inv p.
    + rewrite H1, Hfront. reflexivity.
    + change (pos_nxt (pos_nxt p)) with (@pos_right 2 m p).
      rewrite <- Hr, Hv, !pos2nat_right. reflexivity.
Qed.

Lemma mma_shape_pack_all : forall n x (v : vec nat (3 + n)),
  mma_shape x v -> mma_shape (Nat.iter n mma_enc x) (mma_pack_all n v).
Proof.
  induction n as [|n IH]; intros x v Hv; [exact Hv|].
  cbn [mma_pack_all]. rewrite <- mma_iter_shift.
  apply IH, mma_shape_pack, Hv.
Qed.

Lemma mma_shape_start3 : forall z n, mma_shape (mma_tower n z) (mma_init_start3 z n).
Proof.
  intros z n. unfold mma_init_start3, mma_tower.
  apply mma_shape_pack_all, mma_shape_cast, mma_shape_extend;
    [lia|apply mma_shape_start].
Qed.

(** The target registers in closed form: registers 0, 2 and 3 are zero and
    register 1 holds the [n]-fold iterate of [mma_enc] applied to [z]. *)
Theorem mma_init_target_closed : forall z n,
  mma_init_target z n =
  {| gr0 := 0; gr1 := mma_tower n z; gr2 := 0; gr3 := 0 |}.
Proof.
  intros z n. pose proof (mma_shape_start3 z n) as Hs.
  unfold mma_init_target, mma3_guest_start. cbn [gc_g].
  rewrite !mma3_swap_vec_lookup.
  change (mma3_swap_pos pos0) with (pos2 : pos 3).
  change (mma3_swap_pos pos1) with (pos1 : pos 3).
  change (mma3_swap_pos pos2) with (pos0 : pos 3).
  rewrite (Hs pos0), (Hs pos1), (Hs pos2). reflexivity.
Qed.

Corollary mma_init_target_tower : forall z n,
  gr0 (mma_init_target z n) = 0 /\ gr2 (mma_init_target z n) = 0 /\
  gr3 (mma_init_target z n) = 0 /\
  gr1 (mma_init_target z n) = mma_tower n z /\
  mma_tower 0 z = z /\
  (forall k, mma_tower (S k) z =
             mma_enc_base * mma_enc_step ^ mma_tower k z).
Proof.
  intros z n. rewrite mma_init_target_closed. cbn [gr0 gr1 gr2 gr3].
  repeat split. intro k. rewrite mma_tower_S. apply mma_enc_closed.
Qed.

(** * 4. The guest program.

    Register 1 carries the running value, register 3 counts the remaining
    packing rounds, register 2 counts the exponent inside one round, and
    register 0 holds the constants the arithmetic opcodes need.

    0      r1 := r0 (the input z)
    1      r3 := n
    2..3   if r3 = 0 then go to 16
    4..5   r2 := r1;  r1 := mma_enc_base
    6..7   if r2 = 0 then go to 13
    8..12  r1 := r1 * mma_enc_step;  r2 := r2 - 1;  go to 6
    13..15 r3 := r3 - 1;  go to 2
    16     r0 := 0 *)

Definition g_mma_init (n : nat) : list GInstr :=
  [ GXfer 1 0 0;
    GLoadImm 3 n 0;
    GJnez 3 4 0;
    GJump 16 0;
    GXfer 2 1 0;
    GLoadImm 1 mma_enc_base 0;
    GJnez 2 8 0;
    GJump 13 0;
    GLoadImm 0 mma_enc_step 0;
    GMul 1 1 0 0;
    GLoadImm 0 1 0;
    GSub 2 2 0 0;
    GJump 6 0;
    GLoadImm 0 1 0;
    GSub 3 3 0 0;
    GJump 2 0;
    GLoadImm 0 0 0 ].

Lemma g_mma_init_length : forall n, length (g_mma_init n) = 17.
Proof. reflexivity. Qed.

Lemma g_mma_init_wf : forall n, g_wf_program (g_mma_init n).
Proof.
  intro n. unfold g_wf_program, g_mma_init.
  repeat (apply Forall_cons; [unfold g_wf; cbn; lia|]). apply Forall_nil.
Qed.

Lemma g_mma_init_cost_zero : forall n, Forall (fun i => g_cost i = 0) (g_mma_init n).
Proof.
  intro n. unfold g_mma_init.
  repeat (apply Forall_cons; [reflexivity|]). apply Forall_nil.
Qed.

(** * 5. Running the program. *)

Definition mma_cfg (pc r0 r1 r2 r3 : nat) : GConf :=
  {| gc_pc := pc; gc_mu := 0;
     gc_g := {| gr0 := r0; gr1 := r1; gr2 := r2; gr3 := r3 |} |}.

(** One round of the inner loop multiplies register 1 by [mma_enc_step]
    once per unit of register 2. *)
Lemma g_mma_init_inner : forall n k a r0 r3, exists f r0',
  g_run f (g_mma_init n) (mma_cfg 6 r0 a k r3) =
  mma_cfg 13 r0' (a * mma_enc_step ^ k) 0 r3.
Proof.
  intros n k. induction k as [|k IH]; intros a r0 r3.
  - exists 2, r0. rewrite Nat.pow_0_r, Nat.mul_1_r. reflexivity.
  - destruct (IH (a * mma_enc_step) 1 r3) as (f & r0' & Hf).
    exists (6 + f), r0'. rewrite g_run_add.
    replace (g_run 6 (g_mma_init n) (mma_cfg 6 r0 a (S k) r3))
      with (mma_cfg 6 1 (a * mma_enc_step) k r3)
      by (cbn; rewrite Nat.sub_0_r; reflexivity).
    rewrite Hf, Nat.pow_succ_r', Nat.mul_assoc. reflexivity.
Qed.

(** The outer loop applies [mma_enc] once per unit of register 3. *)
Lemma g_mma_init_outer : forall n c a r0, exists f r0',
  g_run f (g_mma_init n) (mma_cfg 2 r0 a 0 c) =
  mma_cfg 16 r0' (Nat.iter c mma_enc a) 0 0.
Proof.
  intros n c. induction c as [|c IH]; intros a r0.
  - exists 2, r0. reflexivity.
  - destruct (g_mma_init_inner n a mma_enc_base r0 (S c)) as (f1 & r1 & Hf1).
    destruct (IH (mma_enc a) 1) as (f2 & r0' & Hf2).
    exists (3 + (f1 + (3 + f2))), r0'. rewrite !g_run_add.
    replace (g_run 3 (g_mma_init n) (mma_cfg 2 r0 a 0 (S c)))
      with (mma_cfg 6 r0 mma_enc_base a (S c)) by reflexivity.
    rewrite Hf1.
    replace (g_run 3 (g_mma_init n) (mma_cfg 13 r1 (mma_enc_base * mma_enc_step ^ a) 0 (S c)))
      with (mma_cfg 2 1 (mma_enc a) 0 c)
      by (cbn; rewrite Nat.sub_0_r, mma_enc_closed; reflexivity).
    rewrite Hf2, mma_iter_shift. reflexivity.
Qed.

Theorem g_mma_init_run : forall n z, exists fuel,
  g_run fuel (g_mma_init n) (g_input z) =
  {| gc_pc := length (g_mma_init n); gc_mu := 0;
     gc_g := gc_g (mma3_guest_start (mma3_swap_vec (mma_init_start3 z n))) |}.
Proof.
  intros n z.
  change (gc_g (mma3_guest_start (mma3_swap_vec (mma_init_start3 z n))))
    with (mma_init_target z n).
  rewrite mma_init_target_closed, g_mma_init_length.
  destruct (g_mma_init_outer n n z z) as (f & r0' & Hf).
  exists (2 + (f + 1)). rewrite !g_run_add.
  replace (g_run 2 (g_mma_init n) (g_input z)) with (mma_cfg 2 z z 0 n)
    by reflexivity.
  rewrite Hf. reflexivity.
Qed.

(** The run ends terminal, with the ledger untouched and the registers of
    the target in closed form. *)
Corollary g_mma_init_run_closed : forall n z, exists fuel,
  g_terminal (g_mma_init n) (g_run fuel (g_mma_init n) (g_input z)) /\
  g_run fuel (g_mma_init n) (g_input z) =
  {| gc_pc := 17; gc_mu := 0;
     gc_g := {| gr0 := 0; gr1 := mma_tower n z; gr2 := 0; gr3 := 0 |} |}.
Proof.
  intros n z. destruct (g_mma_init_run n z) as (fuel & Hrun).
  exists fuel. fold (mma_init_target z n) in Hrun.
  rewrite mma_init_target_closed, g_mma_init_length in Hrun.
  rewrite Hrun. split; [unfold g_terminal; rewrite g_mma_init_length; cbn; lia|reflexivity].
Qed.

Print Assumptions mma_init_start_cons.
Print Assumptions mma_enc_closed.
Print Assumptions mma_init_target_closed.
Print Assumptions mma_init_target_tower.
Print Assumptions g_mma_init_wf.
Print Assumptions g_mma_init_cost_zero.
Print Assumptions g_mma_init_run.
Print Assumptions g_mma_init_run_closed.
