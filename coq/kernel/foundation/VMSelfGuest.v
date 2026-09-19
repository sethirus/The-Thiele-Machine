(** VMSelfGuest.v: B3, part 1: the guest language of the uniform
    self-interpreter, and its executable data encoding.

    The guest of this interpreter is the unbounded VM itself, restricted to
    an explicitly stated fragment: the arithmetic, transfer and control
    opcodes over guest registers 0..3, with unbounded register values.  A
    guest program is literally a [list vm_instruction] (the image of
    [map g_denote]) and a guest step is literally [vm_apply_u]; nothing
    about the host's execution semantics is redefined for the guest.

    Stated fragment (the guest/input domain of the B3 theorems):
      - guest instructions: HALT, LOAD_IMM, XFER, ADD, SUB, MUL, AND, OR,
        SHL, SHR, JUMP, JNEZ;
      - guest register fields range over 0..3 and guest register values are
        arbitrary naturals (no width bound);
      - guest immediates and jump targets are arbitrary naturals;
      - guest per-instruction cost fields range over 0..255.
    Registers 4..15 of the guest state are never read or written by the
    fragment; they are carried as an opaque tail and proved preserved.

    The word layout below is the executable encoding E(p,x): each guest
    instruction becomes one natural-number word, words are packed into a
    single natural at a per-program bit width, and the guest's input is its
    initial register values.  Opcode 0 is reserved as the fetch sentinel
    for "no instruction here", which is exactly the VM's own termination
    condition ([nth_error] returning [None]); opcodes 13..15 are the
    malformed tags.  [instr_halt] is NOT that condition: in the VM's own
    semantics it advances the program counter like any other instruction,
    so it is encoded as a real opcode (1). *)

From Coq Require Import Arith Lia List.
From Coq Require Import NArith.NArith.
Import ListNotations.
From Kernel Require Import VMState VMStep VMUnboundedStep.
From Kernel Require Import VMUnboundedInterpreterSlots.

Close Scope string_scope.
Open Scope list_scope.

(** * 1. Guest syntax and its denotation into the VM's own instruction type. *)

Inductive GInstr : Type :=
| GHalt    (cost : nat)
| GLoadImm (d imm cost : nat)
| GXfer    (d s cost : nat)
| GAdd     (d a b cost : nat)
| GSub     (d a b cost : nat)
| GMul     (d a b cost : nat)
| GAnd     (d a b cost : nat)
| GOr      (d a b cost : nat)
| GShl     (d a b cost : nat)
| GShr     (d a b cost : nat)
| GJump    (target cost : nat)
| GJnez    (r target cost : nat).

Definition g_denote (i : GInstr) : vm_instruction :=
  match i with
  | GHalt c          => instr_halt c
  | GLoadImm d imm c => instr_load_imm d imm c
  | GXfer d s c      => instr_xfer d s c
  | GAdd d a b c     => instr_add d a b c
  | GSub d a b c     => instr_sub d a b c
  | GMul d a b c     => instr_mul d a b c
  | GAnd d a b c     => instr_and d a b c
  | GOr d a b c      => instr_or d a b c
  | GShl d a b c     => instr_shl d a b c
  | GShr d a b c     => instr_shr d a b c
  | GJump t c        => instr_jump t c
  | GJnez r t c      => instr_jnez r t c
  end.

Definition g_program (p : list GInstr) : list vm_instruction := map g_denote p.

(** * 2. Word layout.

    bits 0..3   opcode      1..12 real, 0 sentinel, 13..15 malformed
    bits 4..5   dst
    bits 6..7   rs1
    bits 8..9   rs2
    bits 10..17 cost
    bits 18..   immediate / jump target *)

Definition g_opcode (i : GInstr) : nat :=
  match i with
  | GHalt _ => 1 | GLoadImm _ _ _ => 2 | GXfer _ _ _ => 3
  | GAdd _ _ _ _ => 4 | GSub _ _ _ _ => 5 | GMul _ _ _ _ => 6
  | GAnd _ _ _ _ => 7 | GOr _ _ _ _ => 8 | GShl _ _ _ _ => 9
  | GShr _ _ _ _ => 10 | GJump _ _ => 11 | GJnez _ _ _ => 12
  end.

Definition g_dst (i : GInstr) : nat :=
  match i with
  | GHalt _ => 0 | GLoadImm d _ _ => d | GXfer d _ _ => d
  | GAdd d _ _ _ => d | GSub d _ _ _ => d | GMul d _ _ _ => d
  | GAnd d _ _ _ => d | GOr d _ _ _ => d | GShl d _ _ _ => d
  | GShr d _ _ _ => d | GJump _ _ => 0 | GJnez _ _ _ => 0
  end.

Definition g_rs1 (i : GInstr) : nat :=
  match i with
  | GHalt _ => 0 | GLoadImm _ _ _ => 0 | GXfer _ s _ => s
  | GAdd _ a _ _ => a | GSub _ a _ _ => a | GMul _ a _ _ => a
  | GAnd _ a _ _ => a | GOr _ a _ _ => a | GShl _ a _ _ => a
  | GShr _ a _ _ => a | GJump _ _ => 0 | GJnez r _ _ => r
  end.

Definition g_rs2 (i : GInstr) : nat :=
  match i with
  | GAdd _ _ b _ => b | GSub _ _ b _ => b | GMul _ _ b _ => b
  | GAnd _ _ b _ => b | GOr _ _ b _ => b | GShl _ _ b _ => b
  | GShr _ _ b _ => b | _ => 0
  end.

Definition g_cost (i : GInstr) : nat :=
  match i with
  | GHalt c => c | GLoadImm _ _ c => c | GXfer _ _ c => c
  | GAdd _ _ _ c => c | GSub _ _ _ c => c | GMul _ _ _ c => c
  | GAnd _ _ _ c => c | GOr _ _ _ c => c | GShl _ _ _ c => c
  | GShr _ _ _ c => c | GJump _ c => c | GJnez _ _ c => c
  end.

Definition g_imm (i : GInstr) : nat :=
  match i with
  | GLoadImm _ imm _ => imm | GJump t _ => t | GJnez _ t _ => t | _ => 0
  end.

(** The word is built in [N] with nested small multipliers.  Writing it as
    a flat sum of [nat] literals (16, 64, 256, 1024, 262144) would make
    [cbn] and [lia] expand unary numerals of size 262144; every numeral
    here is either an [N] literal or a small exponent. *)

Definition g_word_N (i : GInstr) : N :=
  (N.of_nat (g_opcode i)
   + 2 ^ 4 * (N.of_nat (g_dst i)
   + 2 ^ 2 * (N.of_nat (g_rs1 i)
   + 2 ^ 2 * (N.of_nat (g_rs2 i)
   + 2 ^ 2 * (N.of_nat (g_cost i)
   + 2 ^ 8 * N.of_nat (g_imm i))))))%N.

Definition g_word (i : GInstr) : nat := N.to_nat (g_word_N i).

(** Well-formedness of a guest instruction: exactly the stated field ranges. *)
Definition g_wf (i : GInstr) : Prop :=
  g_dst i < 4 /\ g_rs1 i < 4 /\ g_rs2 i < 4 /\ g_cost i < 256.

Definition g_wf_program (p : list GInstr) : Prop := Forall g_wf p.

Lemma g_opcode_lt : forall i, g_opcode i < 16.
Proof. intro i; destruct i; unfold g_opcode; lia. Qed.

Lemma g_opcode_pos : forall i, 0 < g_opcode i.
Proof. intro i; destruct i; unfold g_opcode; lia. Qed.

(** * 3. Field recovery.

    One helper does every field: dividing out a low field that already fits
    below its own power of two leaves the rest of the word, and taking the
    next field's modulus recovers it. *)

Lemma N_div_add_small : forall a k X,
  (a < 2 ^ k)%N -> ((a + 2 ^ k * X) / 2 ^ k)%N = X.
Proof.
  intros a k X Ha.
  rewrite N.mul_comm, N.div_add by (apply N.pow_nonzero; lia).
  rewrite N.div_small by exact Ha. lia.
Qed.

Lemma N_mod_add_small : forall b m Y,
  (b < 2 ^ m)%N -> ((b + 2 ^ m * Y) mod 2 ^ m)%N = b.
Proof.
  intros b m Y Hb.
  rewrite N.mul_comm, N.Div0.mod_add by (apply N.pow_nonzero; lia).
  apply N.mod_small. exact Hb.
Qed.

Lemma g_opcode_fits : forall i, (N.of_nat (g_opcode i) < 2 ^ 4)%N.
Proof. intro i. pose proof (g_opcode_lt i). lia. Qed.

(** The nested tails of the word, named so the field lemmas can peel them. *)
Definition g_tail1 (i : GInstr) : N :=
  (N.of_nat (g_dst i)
   + 2 ^ 2 * (N.of_nat (g_rs1 i)
   + 2 ^ 2 * (N.of_nat (g_rs2 i)
   + 2 ^ 2 * (N.of_nat (g_cost i)
   + 2 ^ 8 * N.of_nat (g_imm i)))))%N.
Definition g_tail2 (i : GInstr) : N :=
  (N.of_nat (g_rs1 i)
   + 2 ^ 2 * (N.of_nat (g_rs2 i)
   + 2 ^ 2 * (N.of_nat (g_cost i)
   + 2 ^ 8 * N.of_nat (g_imm i))))%N.
Definition g_tail3 (i : GInstr) : N :=
  (N.of_nat (g_rs2 i)
   + 2 ^ 2 * (N.of_nat (g_cost i)
   + 2 ^ 8 * N.of_nat (g_imm i)))%N.
Definition g_tail4 (i : GInstr) : N :=
  (N.of_nat (g_cost i) + 2 ^ 8 * N.of_nat (g_imm i))%N.

Lemma g_word_N_unfold : forall i,
  g_word_N i = (N.of_nat (g_opcode i) + 2 ^ 4 * g_tail1 i)%N.
Proof. reflexivity. Qed.

Lemma g_tail1_unfold : forall i,
  g_tail1 i = (N.of_nat (g_dst i) + 2 ^ 2 * g_tail2 i)%N.
Proof. reflexivity. Qed.
Lemma g_tail2_unfold : forall i,
  g_tail2 i = (N.of_nat (g_rs1 i) + 2 ^ 2 * g_tail3 i)%N.
Proof. reflexivity. Qed.
Lemma g_tail3_unfold : forall i,
  g_tail3 i = (N.of_nat (g_rs2 i) + 2 ^ 2 * g_tail4 i)%N.
Proof. reflexivity. Qed.
Lemma g_tail4_unfold : forall i,
  g_tail4 i = (N.of_nat (g_cost i) + 2 ^ 8 * N.of_nat (g_imm i))%N.
Proof. reflexivity. Qed.

(** Division by each field offset, expressed as the matching tail. *)
Lemma g_div4 : forall i, (g_word_N i / 2 ^ 4)%N = g_tail1 i.
Proof.
  intro i. rewrite g_word_N_unfold. apply N_div_add_small, g_opcode_fits.
Qed.

Lemma g_div6 : forall i, g_wf i -> (g_word_N i / 2 ^ 6)%N = g_tail2 i.
Proof.
  intros i (Hd & _ & _ & _).
  replace (2 ^ 6)%N with (2 ^ 4 * 2 ^ 2)%N by reflexivity.
  rewrite <- N.Div0.div_div by (apply N.pow_nonzero; lia).
  rewrite g_div4, g_tail1_unfold. apply N_div_add_small. lia.
Qed.

Lemma g_div8 : forall i, g_wf i -> (g_word_N i / 2 ^ 8)%N = g_tail3 i.
Proof.
  intros i Hwf. pose proof Hwf as (Hd & Ha & _ & _).
  replace (2 ^ 8)%N with (2 ^ 6 * 2 ^ 2)%N by reflexivity.
  rewrite <- N.Div0.div_div by (apply N.pow_nonzero; lia).
  rewrite g_div6 by exact Hwf.
  rewrite g_tail2_unfold. apply N_div_add_small. lia.
Qed.

Lemma g_div10 : forall i, g_wf i -> (g_word_N i / 2 ^ 10)%N = g_tail4 i.
Proof.
  intros i Hwf. pose proof Hwf as (Hd & Ha & Hb & Hc).
  replace (2 ^ 10)%N with (2 ^ 8 * 2 ^ 2)%N by reflexivity.
  rewrite <- N.Div0.div_div by (apply N.pow_nonzero; lia).
  rewrite g_div8 by exact Hwf. rewrite g_tail3_unfold.
  apply N_div_add_small. lia.
Qed.

Lemma g_div18 : forall i, g_wf i -> (g_word_N i / 2 ^ 18)%N = N.of_nat (g_imm i).
Proof.
  intros i Hwf. pose proof Hwf as (Hd & Ha & Hb & Hc).
  replace (2 ^ 18)%N with (2 ^ 10 * 2 ^ 8)%N by reflexivity.
  rewrite <- N.Div0.div_div by (apply N.pow_nonzero; lia).
  rewrite g_div10 by exact Hwf. rewrite g_tail4_unfold.
  apply N_div_add_small. lia.
Qed.

Lemma g_mod_opcode : forall i, (g_word_N i mod 2 ^ 4)%N = N.of_nat (g_opcode i).
Proof.
  intro i. rewrite g_word_N_unfold. apply N_mod_add_small, g_opcode_fits.
Qed.

Lemma g_mod_dst : forall i, g_wf i -> ((g_word_N i / 2 ^ 4) mod 2 ^ 2)%N = N.of_nat (g_dst i).
Proof.
  intros i (Hd & _ & _ & _). rewrite g_div4, g_tail1_unfold.
  apply N_mod_add_small. lia.
Qed.

Lemma g_mod_rs1 : forall i, g_wf i -> ((g_word_N i / 2 ^ 6) mod 2 ^ 2)%N = N.of_nat (g_rs1 i).
Proof.
  intros i Hwf. pose proof Hwf as (Hd & Ha & _ & _).
  rewrite g_div6 by exact Hwf. rewrite g_tail2_unfold.
  apply N_mod_add_small. lia.
Qed.

Lemma g_mod_rs2 : forall i, g_wf i -> ((g_word_N i / 2 ^ 8) mod 2 ^ 2)%N = N.of_nat (g_rs2 i).
Proof.
  intros i Hwf. pose proof Hwf as (Hd & Ha & Hb & _).
  rewrite g_div8 by exact Hwf. rewrite g_tail3_unfold.
  apply N_mod_add_small. lia.
Qed.

Lemma g_mod_cost : forall i, g_wf i -> ((g_word_N i / 2 ^ 10) mod 2 ^ 8)%N = N.of_nat (g_cost i).
Proof.
  intros i Hwf. pose proof Hwf as (Hd & Ha & Hb & Hc).
  rewrite g_div10 by exact Hwf. rewrite g_tail4_unfold.
  apply N_mod_add_small. lia.
Qed.

(** Every real guest instruction has a nonzero word: the fetch sentinel
    (opcode 0, produced by reading past the end of the encoded program) can
    never be confused with an encoded guest instruction. *)
Lemma g_word_N_nonzero : forall i, g_word_N i <> 0%N.
Proof.
  intro i. intro Heq.
  pose proof (g_mod_opcode i) as Hm. rewrite Heq in Hm.
  change ((0 mod 2 ^ 4)%N) with 0%N in Hm. pose proof (g_opcode_pos i). lia.
Qed.

Lemma g_word_nonzero : forall i, g_word i <> 0.
Proof.
  intro i. unfold g_word. intro Heq.
  apply g_word_N_nonzero with (i := i).
  rewrite <- (N2Nat.id (g_word_N i)), Heq. reflexivity.
Qed.

(** * 4. Host-side field extraction.

    These are the exact expressions the host program evaluates on a fetched
    word [w]: a right shift by the field offset followed by a mask. *)

Lemma u_field_N : forall w k m,
  N.of_nat (u_and (u_shr w k) (u_sub (u_shl 1 m) 1)) =
  ((N.of_nat w / 2 ^ N.of_nat k) mod 2 ^ N.of_nat m)%N.
Proof.
  intros w k m. rewrite N_of_nat_u_and, N_of_nat_u_shr, nat_ones_eq, N2Nat.id.
  rewrite N.land_ones, N.shiftr_div_pow2. reflexivity.
Qed.

Lemma g_host_opcode : forall i,
  u_and (g_word i) 15 = g_opcode i.
Proof.
  intro i. apply Nat2N.inj.
  change 15 with (u_sub (u_shl 1 4) 1).
  rewrite N_of_nat_u_and, nat_ones_eq, N2Nat.id, N.land_ones.
  unfold g_word. rewrite N2Nat.id. apply g_mod_opcode.
Qed.

Lemma g_host_dst : forall i, g_wf i ->
  u_and (u_shr (g_word i) 4) 3 = g_dst i.
Proof.
  intros i Hwf. apply Nat2N.inj.
  change 3 with (u_sub (u_shl 1 2) 1). rewrite u_field_N.
  unfold g_word. rewrite N2Nat.id. apply g_mod_dst, Hwf.
Qed.

Lemma g_host_rs1 : forall i, g_wf i ->
  u_and (u_shr (g_word i) 6) 3 = g_rs1 i.
Proof.
  intros i Hwf. apply Nat2N.inj.
  change 3 with (u_sub (u_shl 1 2) 1). rewrite u_field_N.
  unfold g_word. rewrite N2Nat.id. apply g_mod_rs1, Hwf.
Qed.

Lemma g_host_rs2 : forall i, g_wf i ->
  u_and (u_shr (g_word i) 8) 3 = g_rs2 i.
Proof.
  intros i Hwf. apply Nat2N.inj.
  change 3 with (u_sub (u_shl 1 2) 1). rewrite u_field_N.
  unfold g_word. rewrite N2Nat.id. apply g_mod_rs2, Hwf.
Qed.

Lemma g_host_cost : forall i, g_wf i ->
  u_and (u_shr (g_word i) 10) 255 = g_cost i.
Proof.
  intros i Hwf. apply Nat2N.inj.
  change 255 with (u_sub (u_shl 1 8) 1). rewrite u_field_N.
  unfold g_word. rewrite N2Nat.id. apply g_mod_cost, Hwf.
Qed.

Lemma g_host_imm : forall i, g_wf i ->
  u_shr (g_word i) 18 = g_imm i.
Proof.
  intros i Hwf. apply Nat2N.inj.
  rewrite N_of_nat_u_shr, N.shiftr_div_pow2.
  unfold g_word. rewrite N2Nat.id. apply g_div18, Hwf.
Qed.

(** * 5. Packed program code at a per-program bit width. *)

Fixpoint g_code_N (width : nat) (p : list GInstr) : N :=
  match p with
  | [] => 0%N
  | i :: rest => (g_word_N i + 2 ^ N.of_nat width * g_code_N width rest)%N
  end.

Definition g_code (width : nat) (p : list GInstr) : nat := N.to_nat (g_code_N width p).

Definition g_fits (width : nat) (p : list GInstr) : Prop :=
  Forall (fun i => (g_word_N i < 2 ^ N.of_nat width)%N) p.

(** The word the host fetches at guest pc [pc]. *)
Definition g_fetch (code width pc : nat) : nat :=
  u_and (u_shr code (pc * width)) (u_sub (u_shl 1 width) 1).

Lemma g_code_drop_head : forall width i rest,
  (g_word_N i < 2 ^ N.of_nat width)%N ->
  N.shiftr (g_code_N width (i :: rest)) (N.of_nat width) = g_code_N width rest.
Proof.
  intros width i rest Hfit. cbn [g_code_N].
  rewrite N.shiftr_div_pow2. apply N_div_add_small. exact Hfit.
Qed.

Definition g_fetch_N (code : N) (width pc : nat) : N :=
  N.land (N.shiftr code (N.of_nat pc * N.of_nat width)) (N.ones (N.of_nat width)).

Lemma g_fetch_N_eq : forall code width pc,
  N.of_nat (g_fetch code width pc) = g_fetch_N (N.of_nat code) width pc.
Proof.
  intros. unfold g_fetch, g_fetch_N.
  rewrite N_of_nat_u_and, N_of_nat_u_shr, nat_ones_eq, N2Nat.id, Nat2N.inj_mul.
  reflexivity.
Qed.

Lemma g_code_fetch_N : forall p width pc,
  g_fits width p -> pc < length p ->
  g_fetch_N (g_code_N width p) width pc = g_word_N (nth pc p (GHalt 0)).
Proof.
  induction p as [|i rest IH]; intros width [|pc] Hfit Hpc; cbn [length] in Hpc; try lia.
  - inversion Hfit as [|? ? Hi Hrest]; subst. cbn [nth]. unfold g_fetch_N.
    replace (N.of_nat 0 * N.of_nat width)%N with 0%N by reflexivity.
    rewrite N.shiftr_0_r, N.land_ones. cbn [g_code_N].
    apply N_mod_add_small. exact Hi.
  - inversion Hfit as [|? ? Hi Hrest]; subst. unfold g_fetch_N.
    replace (N.of_nat (S pc) * N.of_nat width)%N with
            (N.of_nat width + N.of_nat pc * N.of_nat width)%N
      by (rewrite Nat2N.inj_succ; lia).
    rewrite <- N.shiftr_shiftr, g_code_drop_head by exact Hi.
    apply (IH width pc Hrest). lia.
Qed.

Lemma g_code_fetch_N_outside : forall p width pc,
  g_fits width p -> length p <= pc ->
  g_fetch_N (g_code_N width p) width pc = 0%N.
Proof.
  induction p as [|i rest IH]; intros width pc Hfit Hpc.
  - unfold g_fetch_N. cbn [g_code_N]. rewrite N.shiftr_0_l. reflexivity.
  - destruct pc as [|pc]; cbn [length] in Hpc; [lia|].
    inversion Hfit as [|? ? Hi Hrest]; subst. unfold g_fetch_N.
    replace (N.of_nat (S pc) * N.of_nat width)%N with
            (N.of_nat width + N.of_nat pc * N.of_nat width)%N
      by (rewrite Nat2N.inj_succ; lia).
    rewrite <- N.shiftr_shiftr, g_code_drop_head by exact Hi.
    apply (IH width pc Hrest). lia.
Qed.

Theorem g_code_fetch : forall p width pc,
  g_fits width p -> pc < length p ->
  g_fetch (g_code width p) width pc = g_word (nth pc p (GHalt 0)).
Proof.
  intros p width pc Hfit Hpc. apply Nat2N.inj.
  rewrite g_fetch_N_eq. unfold g_code, g_word. rewrite !N2Nat.id.
  apply g_code_fetch_N; assumption.
Qed.

Theorem g_code_fetch_outside : forall p width pc,
  g_fits width p -> length p <= pc ->
  g_fetch (g_code width p) width pc = 0.
Proof.
  intros p width pc Hfit Hpc. apply Nat2N.inj.
  rewrite g_fetch_N_eq. unfold g_code. rewrite N2Nat.id.
  rewrite g_code_fetch_N_outside by assumption. reflexivity.
Qed.

(** A computable width for every finite guest program: the bit size of the
    largest word.  Every word is below two to the power of its own size. *)
Fixpoint g_max_word_N (p : list GInstr) : N :=
  match p with
  | [] => 0%N
  | i :: rest => N.max (g_word_N i) (g_max_word_N rest)
  end.

Definition g_width (p : list GInstr) : nat := N.to_nat (N.size (g_max_word_N p)).

Lemma g_max_word_ge : forall p i, In i p -> (g_word_N i <= g_max_word_N p)%N.
Proof.
  induction p as [|j rest IH]; intros i Hin; cbn in *; [contradiction|].
  destruct Hin as [->|Hin]; [apply N.le_max_l|].
  eapply N.le_trans; [apply IH, Hin|apply N.le_max_r].
Qed.

Theorem g_width_fits : forall p, g_fits (g_width p) p.
Proof.
  intro p. apply Forall_forall. intros i Hin.
  unfold g_width. rewrite N2Nat.id.
  eapply N.le_lt_trans; [apply g_max_word_ge, Hin|].
  apply N.size_gt.
Qed.

(** * 6. Guest states.

    A guest state is an actual [VMState].  Guest registers 0..3 are the
    fragment's register file; the remaining twelve are an arbitrary tail
    [tl] that the fragment never touches.  Every non-register field comes
    from an arbitrary ambient state.  The guest ledger is the guest state's
    own [vm_mu]. *)

Definition g_state (amb : VMState) (pc mu g0 g1 g2 g3 : nat) (tl : list nat) : VMState :=
  {| vm_graph := amb.(vm_graph); vm_csrs := amb.(vm_csrs);
     vm_regs := g0 :: g1 :: g2 :: g3 :: tl; vm_mem := amb.(vm_mem);
     vm_pc := pc; vm_mu := mu; vm_mu_tensor := amb.(vm_mu_tensor);
     vm_err := amb.(vm_err); vm_logic_acc := amb.(vm_logic_acc);
     vm_mstatus := amb.(vm_mstatus); vm_witness := amb.(vm_witness);
     vm_certified := amb.(vm_certified) |}.

Record GRegs := { gr0 : nat; gr1 : nat; gr2 : nat; gr3 : nat }.

Definition g_get (g : GRegs) (r : nat) : nat :=
  match r with 0 => g.(gr0) | 1 => g.(gr1) | 2 => g.(gr2) | _ => g.(gr3) end.

Definition g_set (g : GRegs) (r v : nat) : GRegs :=
  match r with
  | 0 => {| gr0 := v; gr1 := g.(gr1); gr2 := g.(gr2); gr3 := g.(gr3) |}
  | 1 => {| gr0 := g.(gr0); gr1 := v; gr2 := g.(gr2); gr3 := g.(gr3) |}
  | 2 => {| gr0 := g.(gr0); gr1 := g.(gr1); gr2 := v; gr3 := g.(gr3) |}
  | _ => {| gr0 := g.(gr0); gr1 := g.(gr1); gr2 := g.(gr2); gr3 := v |}
  end.

Definition g_st (amb : VMState) (pc mu : nat) (g : GRegs) (tl : list nat) : VMState :=
  g_state amb pc mu g.(gr0) g.(gr1) g.(gr2) g.(gr3) tl.

(** The abstract one-step result of a fragment instruction, stated with
    [GRegs] operations only.  [g_step_is_vm_apply_u] proves it is exactly
    [vm_apply_u] on the corresponding guest [VMState]. *)
Definition g_next (i : GInstr) (pc mu : nat) (g : GRegs) : nat * nat * GRegs :=
  let mu' := mu + g_cost i in
  match i with
  | GHalt _          => (S pc, mu', g)
  | GLoadImm d imm _ => (S pc, mu', g_set g d imm)
  | GXfer d s _      => (S pc, mu', g_set g d (g_get g s))
  | GAdd d a b _     => (S pc, mu', g_set g d (u_add (g_get g a) (g_get g b)))
  | GSub d a b _     => (S pc, mu', g_set g d (u_sub (g_get g a) (g_get g b)))
  | GMul d a b _     => (S pc, mu', g_set g d (u_mul (g_get g a) (g_get g b)))
  | GAnd d a b _     => (S pc, mu', g_set g d (u_and (g_get g a) (g_get g b)))
  | GOr d a b _      => (S pc, mu', g_set g d (u_or (g_get g a) (g_get g b)))
  | GShl d a b _     => (S pc, mu', g_set g d (u_shl (g_get g a) (g_get g b)))
  | GShr d a b _     => (S pc, mu', g_set g d (u_shr (g_get g a) (g_get g b)))
  | GJump t _        => (t, mu', g)
  | GJnez r t _      => (if Nat.eqb (g_get g r) 0 then S pc else t, mu', g)
  end.

Theorem g_step_is_vm_apply_u : forall amb pc mu g tl i,
  g_wf i ->
  let '(pc', mu', g') := g_next i pc mu g in
  vm_apply_u (g_st amb pc mu g tl) (g_denote i) = g_st amb pc' mu' g' tl.
Proof.
  intros amb pc mu [g0 g1 g2 g3] tl i (Hd & Ha & Hb & _).
  destruct i; cbn [g_dst g_rs1 g_rs2] in *;
  repeat match goal with
         | H : ?x < 4 |- _ =>
             destruct x as [|[|[|[|?]]]]; [| | | | exfalso; lia]; clear H
         end;
  cbn; try reflexivity.
  (* GJnez: case on the tested register's value *)
  all: match goal with
       | |- context [Nat.eqb ?v 0] => destruct (Nat.eqb v 0); reflexivity
       end.
Qed.
