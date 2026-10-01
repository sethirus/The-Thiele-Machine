(** VMGuestExactEpilogue.v: an exact output epilogue for the four-register
    guest.

    The surrounding construction leaves one natural number in register 0.
    The epilogue below decodes that number into all four guest registers and
    charges the mu ledger by an exact, data-dependent amount.  Instruction
    costs are immediate fields, so the charge is paid by a loop that runs one
    cost-1 instruction once per unit; every other instruction costs 0.

    Packing.  With s = a + b + c + d for the target registers (a, b, c, d),
      body   = b + 2^s * (d + 2^s * c)
      inner  = (2 * body + 1) * 2^s
      packed = (2 * inner + 1) * 2^m.
    The first loop strips the trailing zeros of [packed], paying one unit per
    zero, which charges exactly m and leaves [inner].  The second loop counts
    the trailing zeros of [inner] at cost 0, which recovers s and leaves
    [body].  Since b, c and d are at most s, which is below 2^s, shifts by s
    split [body] into b, d and c.  Register 0 keeps s until the very end and
    then becomes a = s - b - c - d, so no fifth register is needed.

    The packing uses only addition, multiplication and a plain recursive
    power of two, so it can be transported to other models of computation
    without division or binary numerals. *)

From Coq Require Import Arith Lia List.
From Coq Require Import NArith.NArith.
Import ListNotations.
From Kernel Require Import VMUnboundedStep VMSelfGuest VMSelfRun.

(** * 1. The packing. *)

Fixpoint pow2 (k : nat) : nat :=
  match k with
  | 0 => 1
  | S k' => pow2 k' + pow2 k'
  end.

Definition g_out_sum (g : GRegs) : nat := gr0 g + gr1 g + gr2 g + gr3 g.

Definition g_out_body (g : GRegs) : nat :=
  gr1 g + pow2 (g_out_sum g) * (gr3 g + pow2 (g_out_sum g) * gr2 g).

Definition g_out_pack (g : GRegs) (m : nat) : nat :=
  (2 * ((2 * g_out_body g + 1) * pow2 (g_out_sum g)) + 1) * pow2 m.

Lemma pow2_eq : forall k, pow2 k = 2 ^ k.
Proof. induction k as [|k IH]; cbn [pow2 Nat.pow]; lia. Qed.

(** * 2. Arithmetic facts about the guest operations used here. *)

Lemma u_shr_div : forall x k, u_shr x k = x / 2 ^ k.
Proof.
  intros x k. unfold u_shr. rewrite N.shiftr_div_pow2.
  rewrite N2Nat.inj_div, N2Nat.inj_pow, !Nat2N.id. reflexivity.
Qed.

Lemma u_shl_mul : forall x k, u_shl x k = x * 2 ^ k.
Proof.
  intros x k. unfold u_shl. rewrite N.shiftl_mul_pow2.
  rewrite N2Nat.inj_mul, N2Nat.inj_pow, !Nat2N.id. reflexivity.
Qed.

Lemma u_and_one : forall x, u_and x 1 = x mod 2.
Proof.
  intro x. unfold u_and. change (N.of_nat 1) with (N.ones 1).
  rewrite N.land_ones, N2Nat.inj_mod, N2Nat.inj_pow, Nat2N.id. reflexivity.
Qed.

Lemma pow2_ne0 : forall k, 2 ^ k <> 0.
Proof. intro k. apply Nat.pow_nonzero. lia. Qed.

Lemma div_low : forall lo q k, lo < 2 ^ k -> (lo + 2 ^ k * q) / 2 ^ k = q.
Proof.
  intros lo q k H. rewrite Nat.add_comm, Nat.mul_comm.
  rewrite Nat.div_add_l by apply pow2_ne0.
  rewrite Nat.div_small by exact H. lia.
Qed.

Lemma tz_odd_mod : forall y, (2 * y + 1) mod 2 = 1.
Proof.
  intro y. rewrite Nat.add_comm, Nat.mul_comm, Nat.Div0.mod_add. reflexivity.
Qed.

Lemma tz_odd_div : forall y, (2 * y + 1) / 2 = y.
Proof.
  intro y. replace (2 * y + 1) with (1 + 2 ^ 1 * y) by (cbn; lia).
  apply div_low. cbn. lia.
Qed.

Lemma tz_even_mod : forall y k, ((2 * y + 1) * 2 ^ S k) mod 2 = 0.
Proof.
  intros y k.
  replace ((2 * y + 1) * 2 ^ S k) with (((2 * y + 1) * 2 ^ k) * 2)
    by (rewrite Nat.pow_succ_r'; ring).
  apply Nat.Div0.mod_mul.
Qed.

Lemma tz_even_div : forall y k, ((2 * y + 1) * 2 ^ S k) / 2 = (2 * y + 1) * 2 ^ k.
Proof.
  intros y k. rewrite Nat.pow_succ_r'.
  replace ((2 * y + 1) * (2 * 2 ^ k)) with (((2 * y + 1) * 2 ^ k) * 2) by ring.
  apply Nat.div_mul. lia.
Qed.

(** * 3. A trailing-zero block, placed at an arbitrary base address.

    From pc [base] with register 0 holding (2y+1)*2^k it leaves y in
    register 0, k in register 3, 1 in registers 1 and 2, pc at base + 8, and
    the ledger increased by cost * k. *)

Definition tz_block (base cost : nat) : list GInstr :=
  [ GLoadImm 1 1 0;           (* base+0: r1 := 1 *)
    GLoadImm 3 0 0;           (* base+1: r3 := 0 *)
    GAnd 2 0 1 0;             (* base+2: r2 := r0 land 1 *)
    GJnez 2 (base + 7) 0;     (* base+3: odd, leave the loop *)
    GShr 0 0 1 0;             (* base+4: r0 := r0 / 2 *)
    GAdd 3 3 1 cost;          (* base+5: r3 := r3 + 1, pay cost *)
    GJump (base + 2) 0;       (* base+6 *)
    GShr 0 0 1 0 ].           (* base+7: r0 := (r0 - 1) / 2 *)

(** [p] contains [blk] starting at address [base]. *)
Definition emb (p : list GInstr) (base : nat) (blk : list GInstr) : Prop :=
  forall i, i < length blk -> nth_error p (base + i) = nth_error blk i.

Ltac tz_fetch He :=
  unfold g_step; cbn [gc_pc gc_mu gc_g];
  rewrite He by (cbn [length tz_block]; lia);
  cbn [tz_block nth_error g_next g_cost g_get g_set gr0 gr1 gr2 gr3 Nat.eqb];
  rewrite <- ?Nat.add_succ_r.

Section TzBlock.

Variables (p : list GInstr) (base cost : nat).
Variable He : emb p base (tz_block base cost).

Lemma tz_s0 : forall mu v r1 r2 r3,
  g_step p {| gc_pc := base + 0; gc_mu := mu;
              gc_g := {| gr0 := v; gr1 := r1; gr2 := r2; gr3 := r3 |} |} =
  {| gc_pc := base + 1; gc_mu := mu;
     gc_g := {| gr0 := v; gr1 := 1; gr2 := r2; gr3 := r3 |} |}.
Proof. intros. tz_fetch He. rewrite Nat.add_0_r. reflexivity. Qed.

Lemma tz_s1 : forall mu v r2 r3,
  g_step p {| gc_pc := base + 1; gc_mu := mu;
              gc_g := {| gr0 := v; gr1 := 1; gr2 := r2; gr3 := r3 |} |} =
  {| gc_pc := base + 2; gc_mu := mu;
     gc_g := {| gr0 := v; gr1 := 1; gr2 := r2; gr3 := 0 |} |}.
Proof. intros. tz_fetch He. rewrite Nat.add_0_r. reflexivity. Qed.

Lemma tz_s2 : forall mu v t j,
  g_step p {| gc_pc := base + 2; gc_mu := mu;
              gc_g := {| gr0 := v; gr1 := 1; gr2 := t; gr3 := j |} |} =
  {| gc_pc := base + 3; gc_mu := mu;
     gc_g := {| gr0 := v; gr1 := 1; gr2 := v mod 2; gr3 := j |} |}.
Proof. intros. tz_fetch He. rewrite Nat.add_0_r, u_and_one. reflexivity. Qed.

Lemma tz_s3_zero : forall mu v j,
  g_step p {| gc_pc := base + 3; gc_mu := mu;
              gc_g := {| gr0 := v; gr1 := 1; gr2 := 0; gr3 := j |} |} =
  {| gc_pc := base + 4; gc_mu := mu;
     gc_g := {| gr0 := v; gr1 := 1; gr2 := 0; gr3 := j |} |}.
Proof. intros. tz_fetch He. rewrite Nat.add_0_r. reflexivity. Qed.

Lemma tz_s3_one : forall mu v j,
  g_step p {| gc_pc := base + 3; gc_mu := mu;
              gc_g := {| gr0 := v; gr1 := 1; gr2 := 1; gr3 := j |} |} =
  {| gc_pc := base + 7; gc_mu := mu;
     gc_g := {| gr0 := v; gr1 := 1; gr2 := 1; gr3 := j |} |}.
Proof. intros. tz_fetch He. rewrite Nat.add_0_r. reflexivity. Qed.

Lemma tz_s4 : forall mu v t j,
  g_step p {| gc_pc := base + 4; gc_mu := mu;
              gc_g := {| gr0 := v; gr1 := 1; gr2 := t; gr3 := j |} |} =
  {| gc_pc := base + 5; gc_mu := mu;
     gc_g := {| gr0 := v / 2; gr1 := 1; gr2 := t; gr3 := j |} |}.
Proof.
  intros. tz_fetch He. rewrite Nat.add_0_r, u_shr_div. reflexivity.
Qed.

Lemma tz_s5 : forall mu v t j,
  g_step p {| gc_pc := base + 5; gc_mu := mu;
              gc_g := {| gr0 := v; gr1 := 1; gr2 := t; gr3 := j |} |} =
  {| gc_pc := base + 6; gc_mu := mu + cost;
     gc_g := {| gr0 := v; gr1 := 1; gr2 := t; gr3 := j + 1 |} |}.
Proof. intros. tz_fetch He. reflexivity. Qed.

Lemma tz_s6 : forall mu v t j,
  g_step p {| gc_pc := base + 6; gc_mu := mu;
              gc_g := {| gr0 := v; gr1 := 1; gr2 := t; gr3 := j |} |} =
  {| gc_pc := base + 2; gc_mu := mu;
     gc_g := {| gr0 := v; gr1 := 1; gr2 := t; gr3 := j |} |}.
Proof. intros. tz_fetch He. rewrite Nat.add_0_r. reflexivity. Qed.

Lemma tz_s7 : forall mu v t j,
  g_step p {| gc_pc := base + 7; gc_mu := mu;
              gc_g := {| gr0 := v; gr1 := 1; gr2 := t; gr3 := j |} |} =
  {| gc_pc := base + 8; gc_mu := mu;
     gc_g := {| gr0 := v / 2; gr1 := 1; gr2 := t; gr3 := j |} |}.
Proof.
  intros. tz_fetch He. rewrite Nat.add_0_r, u_shr_div. reflexivity.
Qed.

Lemma tz_loop : forall y k mu t j,
  g_run (5 * k + 3) p
    {| gc_pc := base + 2; gc_mu := mu;
       gc_g := {| gr0 := (2 * y + 1) * 2 ^ k; gr1 := 1; gr2 := t; gr3 := j |} |} =
  {| gc_pc := base + 8; gc_mu := mu + cost * k;
     gc_g := {| gr0 := y; gr1 := 1; gr2 := 1; gr3 := j + k |} |}.
Proof.
  intros y k. induction k as [|k IH]; intros mu t j.
  - change (5 * 0 + 3) with 3. cbn [g_run]. rewrite tz_s2. rewrite Nat.mul_1_r, tz_odd_mod.
    rewrite tz_s3_one, tz_s7, tz_odd_div.
    rewrite !Nat.mul_0_r, !Nat.add_0_r. reflexivity.
  - replace (5 * S k + 3) with (5 + (5 * k + 3)) by lia.
    rewrite g_run_add. cbn [g_run].
    rewrite tz_s2, tz_even_mod, tz_s3_zero, tz_s4, tz_even_div, tz_s5, tz_s6.
    rewrite IH. f_equal; [lia|]. f_equal. lia.
Qed.

Lemma tz_block_run : forall y k mu r1 r2 r3,
  g_run (5 * k + 5) p
    {| gc_pc := base; gc_mu := mu;
       gc_g := {| gr0 := (2 * y + 1) * 2 ^ k; gr1 := r1; gr2 := r2; gr3 := r3 |} |} =
  {| gc_pc := base + 8; gc_mu := mu + cost * k;
     gc_g := {| gr0 := y; gr1 := 1; gr2 := 1; gr3 := k |} |}.
Proof.
  intros. replace (5 * k + 5) with (2 + (5 * k + 3)) by lia.
  rewrite g_run_add. cbn [g_run].
  replace base with (base + 0) at 1 by lia.
  rewrite tz_s0, tz_s1, tz_loop. reflexivity.
Qed.

End TzBlock.

(** * 4. The epilogue program. *)

(** Instructions 16..27: register 0 holds s and register 1 holds the body
    b + 2^s * (d + 2^s * c). *)
Definition g_unpack_tail : list GInstr :=
  [ GXfer 1 0 0;        (* 16: r1 := body *)
    GXfer 0 3 0;        (* 17: r0 := s *)
    GShr 3 1 0 0;       (* 18: r3 := d + 2^s * c *)
    GShl 2 3 0 0;       (* 19: r2 := (d + 2^s * c) * 2^s *)
    GSub 1 1 2 0;       (* 20: r1 := b *)
    GShr 2 3 0 0;       (* 21: r2 := c *)
    GShl 2 2 0 0;       (* 22: r2 := c * 2^s *)
    GSub 3 3 2 0;       (* 23: r3 := d *)
    GShr 2 2 0 0;       (* 24: r2 := c *)
    GSub 0 0 1 0;       (* 25: r0 := s - b *)
    GSub 0 0 2 0;       (* 26: r0 := s - b - c *)
    GSub 0 0 3 0 ].     (* 27: r0 := a *)

Definition g_exact_epilogue : list GInstr :=
  tz_block 0 1 ++ tz_block 8 0 ++ g_unpack_tail.

Lemma g_exact_epilogue_length : length g_exact_epilogue = 28.
Proof. reflexivity. Qed.

Lemma g_exact_epilogue_wf : g_wf_program g_exact_epilogue.
Proof.
  unfold g_wf_program, g_exact_epilogue, tz_block, g_unpack_tail.
  cbn [app].
  repeat (constructor; [unfold g_wf; cbn [g_dst g_rs1 g_rs2 g_cost]; lia|]).
  constructor.
Qed.

Lemma g_exact_epilogue_emb0 : emb g_exact_epilogue 0 (tz_block 0 1).
Proof.
  intros i Hi. cbn [length tz_block] in Hi.
  do 8 (destruct i as [|i]; [reflexivity|]). lia.
Qed.

Lemma g_exact_epilogue_emb8 : emb g_exact_epilogue 8 (tz_block 8 0).
Proof.
  intros i Hi. cbn [length tz_block] in Hi.
  do 8 (destruct i as [|i]; [reflexivity|]). lia.
Qed.

Lemma g_unpack_run : forall mu a b c d,
  let s := a + b + c + d in
  g_run 12 g_exact_epilogue
    {| gc_pc := 16; gc_mu := mu;
       gc_g := {| gr0 := b + 2 ^ s * (d + 2 ^ s * c); gr1 := 1; gr2 := 1;
                  gr3 := s |} |} =
  {| gc_pc := 28; gc_mu := mu;
     gc_g := {| gr0 := a; gr1 := b; gr2 := c; gr3 := d |} |}.
Proof.
  intros mu a b c d s.
  cbn [g_run g_step g_exact_epilogue tz_block g_unpack_tail app nth_error
       g_next g_cost g_get g_set gc_pc gc_mu gc_g gr0 gr1 gr2 gr3].
  unfold u_sub. rewrite !u_shr_div, !u_shl_mul.
  assert (Hs : s < 2 ^ s) by (apply Nat.pow_gt_lin_r; lia).
  rewrite (div_low b) by lia.
  rewrite (Nat.mul_comm (d + 2 ^ s * c) (2 ^ s)).
  rewrite (div_low d) by lia.
  rewrite Nat.div_mul by apply pow2_ne0.
  rewrite Nat.add_sub.
  rewrite (Nat.mul_comm c (2 ^ s)), Nat.add_sub.
  rewrite !Nat.add_0_r.
  f_equal. f_equal. unfold s. lia.
Qed.

(** * 5. The epilogue theorem. *)

Theorem g_exact_epilogue_run : forall g m mu0 r1 r2 r3,
  exists fuel,
    g_run fuel g_exact_epilogue
      {| gc_pc := 0; gc_mu := mu0;
         gc_g := {| gr0 := g_out_pack g m; gr1 := r1; gr2 := r2; gr3 := r3 |} |} =
    {| gc_pc := length g_exact_epilogue; gc_mu := mu0 + m; gc_g := g |}.
Proof.
  intros [a b c d] m mu0 r1 r2 r3.
  set (s := a + b + c + d).
  exists ((5 * m + 5) + ((5 * s + 5) + 12)).
  rewrite (g_run_add (5 * m + 5)), (g_run_add (5 * s + 5)).
  unfold g_out_pack, g_out_body, g_out_sum. cbn [gr0 gr1 gr2 gr3].
  fold s. rewrite !pow2_eq.
  rewrite (tz_block_run _ 0 1 g_exact_epilogue_emb0).
  change (0 + 8) with 8.
  rewrite (tz_block_run _ 8 0 g_exact_epilogue_emb8).
  change (8 + 8) with 16.
  rewrite Nat.mul_0_l, Nat.add_0_r, Nat.mul_1_l.
  unfold s. rewrite g_unpack_run. reflexivity.
Qed.

(** The run theorem determines g and m from the packed number, so the
    packing is injective. *)
Corollary g_out_pack_inj : forall g m g' m',
  g_out_pack g m = g_out_pack g' m' -> g = g' /\ m = m'.
Proof.
  intros g m g' m' Heq.
  destruct (g_exact_epilogue_run g m 0 0 0 0) as [f Hf].
  destruct (g_exact_epilogue_run g' m' 0 0 0 0) as [f' Hf'].
  rewrite Heq in Hf.
  assert (Hterm : forall cf, gc_pc cf = length g_exact_epilogue ->
            g_terminal g_exact_epilogue cf)
    by (intros cf H; unfold g_terminal; lia).
  pose proof (g_run_add f f' g_exact_epilogue
    {| gc_pc := 0; gc_mu := 0;
       gc_g := {| gr0 := g_out_pack g' m'; gr1 := 0; gr2 := 0; gr3 := 0 |} |}) as H1.
  pose proof (g_run_add f' f g_exact_epilogue
    {| gc_pc := 0; gc_mu := 0;
       gc_g := {| gr0 := g_out_pack g' m'; gr1 := 0; gr2 := 0; gr3 := 0 |} |}) as H2.
  rewrite Hf in H1. rewrite Hf' in H2.
  rewrite (g_run_terminal f' g_exact_epilogue
    {| gc_pc := length g_exact_epilogue; gc_mu := 0 + m; gc_g := g |})
    in H1 by (apply Hterm; reflexivity).
  rewrite (g_run_terminal f g_exact_epilogue
    {| gc_pc := length g_exact_epilogue; gc_mu := 0 + m'; gc_g := g' |})
    in H2 by (apply Hterm; reflexivity).
  rewrite Nat.add_comm, H2 in H1.
  injection H1 as Hm Hg. split; [symmetry; exact Hg|lia].
Qed.

Print Assumptions g_out_pack_inj.
Print Assumptions g_exact_epilogue_wf.
Print Assumptions g_exact_epilogue_run.
