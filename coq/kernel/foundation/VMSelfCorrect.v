(** VMSelfCorrect.v: B3, part 3: one guest step of the self-interpreter.

    Boundary relation.  At every interpreter boundary the host is at address
    0 with the guest registers in R0..R3, status R9 = 0, the guest ledger in
    R11, the guest pc in R12, the width in R13 and the packed code in R14.
    The scratch registers R4..R8, R10 and R15 are arbitrary.  All
    non-register host fields, including the host's own [vm_mu], are the
    fixed parameters [amb] and [hmu]; the relation therefore also states the
    host frame. *)

From Coq Require Import Arith Lia List.
Import ListNotations.
From Kernel Require Import VMState VMStep VMUnboundedStep.
From Kernel Require Import VMUnboundedInterpreterCompose.
From Kernel Require Import VMSelfGuest VMSelfProgram.

Record HScratch := {
  hs4 : nat; hs5 : nat; hs6 : nat; hs7 : nat; hs8 : nat; hs10 : nat; hs15 : nat
}.

Definition hb (amb : VMState) (hmu code width pc mu : nat) (g : GRegs)
    (z : HScratch) : VMState :=
  hst amb hmu 0 [g.(gr0); g.(gr1); g.(gr2); g.(gr3);
                 z.(hs4); z.(hs5); z.(hs6); z.(hs7); z.(hs8); 0; z.(hs10);
                 mu; pc; width; code; z.(hs15)].

Definition h_rep (amb : VMState) (hmu code width pc mu : nat) (g : GRegs)
    (s : VMState) : Prop :=
  exists z, s = hb amb hmu code width pc mu g z.

Lemma g4_get : forall k g, k < 4 ->
  g4 k g.(gr0) g.(gr1) g.(gr2) g.(gr3) = g_get g k.
Proof. intros k g Hk. destruct k as [|[|[|[|k]]]]; try lia; reflexivity. Qed.

(** Host steps from a boundary to the opcode dispatch point. *)
Definition h_prefix (i : GInstr) : nat :=
  7 + (4 + (rc (g_rs1 i) + (4 + (rc (g_rs2 i) + 2)))).

Lemma h_prefix_run : forall amb hmu code width pc mu g z i,
  g_wf i ->
  g_fetch code width pc = g_word i ->
  run_vm_u (h_prefix i) U (hb amb hmu code width pc mu g z) =
  hst amb hmu 41 [g.(gr0); g.(gr1); g.(gr2); g.(gr3);
                  g_get g (g_rs1 i); g_get g (g_rs2 i); z.(hs6); g_opcode i;
                  g_word i; 0; 1; mu; pc; width; code; 3].
Proof.
  intros amb hmu code width pc mu g [z4 z5 z6 z7 z8 z10 z15] i Hwf Hfetch.
  pose proof Hwf as (Hd & Ha & Hb & Hc).
  unfold hb, h_prefix; cbn [hs4 hs5 hs6 hs7 hs8 hs10 hs15].
  rewrite run_vm_u_split, ph_fetch, Hfetch.
  rewrite run_vm_u_split, ph_rs1_index, (g_host_rs1 i Hwf).
  rewrite run_vm_u_split, ph_read_rs1 by exact Ha.
  rewrite run_vm_u_split, ph_rs2_index, (g_host_rs2 i Hwf).
  rewrite run_vm_u_split, ph_read_rs2 by exact Hb.
  rewrite ph_opcode, g_host_opcode.
  rewrite !g4_get by assumption. reflexivity.
Qed.

(** * Suffixes back to the next boundary. *)

Definition h_write (d : nat) : nat := 4 + (rc d + (1 + 6)).

Lemma h_write_run : forall amb hmu code width pc mu g i v r4 r5 r7 r15,
  g_wf i ->
  h_rep amb hmu code width (S pc) (mu + g_cost i) (g_set g (g_dst i) v)
    (run_vm_u (h_write (g_dst i)) U
       (hst amb hmu 99 [g.(gr0); g.(gr1); g.(gr2); g.(gr3); r4; r5; v; r7;
                        g_word i; 0; 1; mu; pc; width; code; r15])).
Proof.
  intros amb hmu code width pc mu [g0 g1 g2 g3] i v r4 r5 r7 r15 Hwf.
  pose proof Hwf as (Hd & Ha & Hb & Hc).
  unfold h_write; cbn [gr0 gr1 gr2 gr3].
  rewrite run_vm_u_split, ph_dst_index, (g_host_dst i Hwf).
  rewrite run_vm_u_split, ph_write by exact Hd.
  rewrite run_vm_u_split, ph_advpc, ph_advmu, (g_host_cost i Hwf).
  exists {| hs4 := r4; hs5 := r5; hs6 := v; hs7 := g_cost i; hs8 := g_word i;
            hs10 := 1; hs15 := 255 |}.
  unfold hb; cbn [hs4 hs5 hs6 hs7 hs8 hs10 hs15].
  replace (u_add pc 1) with (S pc) by (unfold u_add; lia).
  replace (u_add mu (g_cost i)) with (mu + g_cost i) by (unfold u_add; lia).
  destruct (g_dst i) as [|[|[|[|d]]]]; try lia; reflexivity.
Qed.

Lemma h_advmu_run : forall amb hmu code width pc' mu g i r4 r5 r6 r7 r15,
  g_wf i ->
  h_rep amb hmu code width pc' (mu + g_cost i) g
    (run_vm_u 6 U
       (hst amb hmu 116 [g.(gr0); g.(gr1); g.(gr2); g.(gr3); r4; r5; r6; r7;
                         g_word i; 0; 1; mu; pc'; width; code; r15])).
Proof.
  intros amb hmu code width pc' mu [g0 g1 g2 g3] i r4 r5 r6 r7 r15 Hwf.
  rewrite ph_advmu, (g_host_cost i Hwf).
  exists {| hs4 := r4; hs5 := r5; hs6 := r6; hs7 := g_cost i; hs8 := g_word i;
            hs10 := 1; hs15 := 255 |}.
  unfold hb; cbn [hs4 hs5 hs6 hs7 hs8 hs10 hs15 gr0 gr1 gr2 gr3].
  replace (u_add mu (g_cost i)) with (mu + g_cost i) by (unfold u_add; lia).
  reflexivity.
Qed.

(** * One guest step. *)

Definition h_tail (i : GInstr) (g : GRegs) : nat :=
  match i with
  | GHalt _          => 4 + (1 + 6)
  | GLoadImm d _ _   => 8 + h_write d
  | GXfer d _ _      => 9 + h_write d
  | GAdd d _ _ _     => (2 * 4 + 3) + h_write d
  | GSub d _ _ _     => (2 * 5 + 3) + h_write d
  | GMul d _ _ _     => (2 * 6 + 3) + h_write d
  | GAnd d _ _ _     => (2 * 7 + 3) + h_write d
  | GOr d _ _ _      => (2 * 8 + 3) + h_write d
  | GShl d _ _ _     => (2 * 9 + 3) + h_write d
  | GShr d _ _ _     => (2 * 10 + 3) + h_write d
  | GJump _ _        => 26 + 6
  | GJnez r _ _      => (if Nat.eqb (g_get g r) 0 then 28 else 29) + 6
  end.

Definition h_steps (i : GInstr) (g : GRegs) : nat := h_prefix i + h_tail i g.

Lemma h_steps_pos : forall i g, 0 < h_steps i g.
Proof. intros. unfold h_steps, h_prefix. lia. Qed.

Ltac alu_case k :=
  rewrite run_vm_u_split, (ph_op_alu _ _ _ _ _ _ _ _ _ k) by lia;
  apply h_write_run; assumption.

Theorem h_step : forall amb hmu code width pc mu g z i,
  g_wf i ->
  g_fetch code width pc = g_word i ->
  let '(pc', mu', g') := g_next i pc mu g in
  h_rep amb hmu code width pc' mu' g'
    (run_vm_u (h_steps i g) U (hb amb hmu code width pc mu g z)).
Proof.
  intros amb hmu code width pc mu g z i Hwf Hfetch.
  unfold h_steps. rewrite run_vm_u_split, (h_prefix_run amb hmu code width pc mu g z i Hwf Hfetch).
  pose proof Hwf as (Hd & Ha & Hb & Hc).
  destruct i; cbn [g_opcode g_rs1 g_rs2 g_next h_tail] in *.
  - (* HALT *)
    rewrite run_vm_u_split, ph_op_halt, run_vm_u_split, ph_advpc.
    replace (u_add pc 1) with (S pc) by (unfold u_add; lia).
    exact (h_advmu_run _ _ _ _ _ _ _ (GHalt cost) _ _ _ _ _ Hwf).
  - (* LOAD_IMM *)
    rewrite run_vm_u_split, ph_op_loadimm, (g_host_imm _ Hwf).
    exact (h_write_run _ _ _ _ _ _ _ (GLoadImm d imm cost) _ _ _ _ _ Hwf).
  - (* XFER *)
    rewrite run_vm_u_split, ph_op_xfer.
    exact (h_write_run _ _ _ _ _ _ _ (GXfer d s cost) _ _ _ _ _ Hwf).
  - alu_case 4.
  - alu_case 5.
  - alu_case 6.
  - alu_case 7.
  - alu_case 8.
  - alu_case 9.
  - alu_case 10.
  - (* JUMP *)
    rewrite run_vm_u_split, ph_op_jump, (g_host_imm _ Hwf).
    exact (h_advmu_run _ _ _ _ _ _ _ (GJump target cost) _ _ _ _ _ Hwf).
  - (* JNEZ *)
    destruct (Nat.eqb (g_get g r) 0) eqn:Ez.
    + apply Nat.eqb_eq in Ez. rewrite Ez.
      rewrite run_vm_u_split, ph_op_jnez_zero.
      replace (u_add pc 1) with (S pc) by (unfold u_add; lia).
      exact (h_advmu_run _ _ _ _ _ _ _ (GJnez r target cost) _ _ _ _ _ Hwf).
    + apply Nat.eqb_neq in Ez.
      rewrite run_vm_u_split, ph_op_jnez_nonzero by exact Ez.
      rewrite (g_host_imm _ Hwf).
      exact (h_advmu_run _ _ _ _ _ _ _ (GJnez r target cost) _ _ _ _ _ Hwf).
Qed.
