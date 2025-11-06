(* Force recompile *)


Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import Nat.
Require Import Lia.
Require Import ThieleUniversal.UTM_CoreLemmas.
Require Import ThieleUniversal_Program.
Import UTM_Program.
Import ThieleUniversal_Program.
Require Import ThieleUniversal.UTM_Encode.
Import UTM_Encode.
Require Import CPU.

(* Note: read_reg_write_reg_commute was removed - available in UTM_CoreLemmas if needed *)

Import ListNotations.
Open Scope Z_scope.
Open Scope nat_scope.
Require Import ThieleUniversal.TM.

(* Execute one decoded instruction. *)
Definition run1 (s : CPU.State) : CPU.State :=
  CPU.step (decode_instr s) s.

Lemma step_mem_preserved_if_no_store : forall i s,
  (match i with StoreIndirect _ _ => False | _ => True end) ->
  (CPU.step i s).(mem) = s.(mem).
Proof.
  intros i s H.
  destruct i; simpl in H; simpl.
  - reflexivity.
  - reflexivity.
  - contradiction.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (Nat.eqb (read_reg rc s) 0); simpl; reflexivity.
  - destruct (Nat.eqb (read_reg rc s) 0); simpl; reflexivity.
  - reflexivity.
Qed.

Lemma run1_mem_preserved_if_no_store : forall s,
  (match decode_instr s with StoreIndirect _ _ => False | _ => True end) ->
  (run1 s).(mem) = s.(mem).
Proof.
  intros s H.
  unfold run1.
  apply step_mem_preserved_if_no_store.
  exact H.
Qed.

Lemma read_mem_mem_eq : forall st1 st2 addr,
  mem st1 = mem st2 ->
  read_mem addr st1 = read_mem addr st2.
Proof.
  intros st1 st2 addr Hmem.
  unfold read_mem.
  rewrite Hmem.
  reflexivity.
Qed.

Lemma run1_preserves_reg_copyreg : forall st dst src r,
  decode_instr st = CopyReg dst src ->
  REG_PC < length (regs st) ->
  dst < length (regs st) ->
  r < length (regs st) ->
  r <> dst ->
  r <> REG_PC ->
  read_reg r (run1 st) = read_reg r st.
Proof.
  intros st dst src r Hdecode Hpc_bound Hdst_bound Hr_bound Hneq_dst Hneq_pc.
  unfold run1.
  rewrite Hdecode.
  unfold step; cbn.
  set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
  assert (Hlen_pc : length (regs st_pc) = length (regs st)).
  { unfold st_pc.
    apply length_regs_write_reg.
    exact Hpc_bound. }
  assert (Hdst_pc_bound : dst < length (regs st_pc)) by (rewrite Hlen_pc; exact Hdst_bound).
  assert (Hr_pc_bound : r < length (regs st_pc)) by (rewrite Hlen_pc; exact Hr_bound).
  assert (Hneq_pc_sym : REG_PC <> r) by (intro Heq; apply Hneq_pc; symmetry; exact Heq).
  assert (Hr_pc_eq : read_reg r st_pc = read_reg r st).
  { unfold st_pc.
    apply (read_reg_write_reg_other st REG_PC r (S (read_reg REG_PC st)) Hpc_bound Hr_bound).
    exact Hneq_pc_sym. }
  rewrite <- Hr_pc_eq.
  fold (read_reg r st_pc).
  apply (read_reg_write_reg_other st_pc dst r (read_reg src st) Hdst_pc_bound Hr_pc_bound).
  intros Hcontra. apply Hneq_dst. symmetry. exact Hcontra.
Qed.

Lemma run1_preserves_reg_subreg : forall st dst src1 src2 r,
  decode_instr st = SubReg dst src1 src2 ->
  REG_PC < length (regs st) ->
  dst < length (regs st) ->
  r < length (regs st) ->
  r <> dst ->
  r <> REG_PC ->
  read_reg r (run1 st) = read_reg r st.
Proof.
  intros st dst src1 src2 r Hdecode Hpc_bound Hdst_bound Hr_bound Hneq_dst Hneq_pc.
  unfold run1.
  rewrite Hdecode.
  unfold step; cbn.
  set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
  assert (Hlen_pc : length (regs st_pc) = length (regs st)).
  { unfold st_pc.
    apply length_regs_write_reg.
    exact Hpc_bound. }
  assert (Hdst_pc_bound : dst < length (regs st_pc)) by (rewrite Hlen_pc; exact Hdst_bound).
  assert (Hr_pc_bound : r < length (regs st_pc)) by (rewrite Hlen_pc; exact Hr_bound).
  assert (Hneq_pc_sym : REG_PC <> r) by (intro Heq; apply Hneq_pc; symmetry; exact Heq).
  assert (Hr_pc_eq : read_reg r st_pc = read_reg r st).
  { unfold st_pc.
    apply (read_reg_write_reg_other st REG_PC r (S (read_reg REG_PC st)) Hpc_bound Hr_bound).
    exact Hneq_pc_sym. }
  rewrite <- Hr_pc_eq.
  fold (read_reg r st_pc).
  apply (read_reg_write_reg_other st_pc dst r (read_reg src1 st - read_reg src2 st) Hdst_pc_bound Hr_pc_bound).
  intros Hcontra. apply Hneq_dst. symmetry. exact Hcontra.
Qed.

Lemma run1_subreg_result : forall st dst src1 src2,
  decode_instr st = SubReg dst src1 src2 ->
  REG_PC < length (regs st) ->
  dst < length (regs st) ->
  read_reg dst (run1 st) = read_reg src1 st - read_reg src2 st.
Proof.
  intros st dst src1 src2 Hdecode Hpc_bound Hdst_bound.
  unfold run1.
  rewrite Hdecode.
  unfold step; cbn.
  set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
  assert (Hlen_pc : length (regs st_pc) = length (regs st)).
  { unfold st_pc.
    apply length_regs_write_reg.
    exact Hpc_bound. }
  assert (Hdst_pc_bound : dst < length (regs st_pc)) by (rewrite Hlen_pc; exact Hdst_bound).
  apply (read_reg_write_reg_same st_pc dst (read_reg src1 st - read_reg src2 st) Hdst_pc_bound).
Qed.

Lemma run1_copyreg_result : forall st dst src,
  decode_instr st = CopyReg dst src ->
  REG_PC < length (regs st) ->
  dst < length (regs st) ->
  read_reg dst (run1 st) = read_reg src st.
Proof.
  intros st dst src Hdecode Hpc_bound Hdst_bound.
  unfold run1.
  rewrite Hdecode.
  unfold step; cbn.
  set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
  assert (Hlen_pc : length (regs st_pc) = length (regs st)).
  { unfold st_pc.
    apply length_regs_write_reg.
    exact Hpc_bound. }
  assert (Hdst_pc_bound : dst < length (regs st_pc)) by (rewrite Hlen_pc; exact Hdst_bound).
  apply (read_reg_write_reg_same st_pc dst (read_reg src st) Hdst_pc_bound).
Qed.

Lemma run1_preserves_reg_addconst : forall st dst n r,
  decode_instr st = AddConst dst n ->
  REG_PC < length (regs st) ->
  dst < length (regs st) ->
  r < length (regs st) ->
  r <> dst ->
  r <> REG_PC ->
  read_reg r (run1 st) = read_reg r st.
Proof.
  intros st dst n r Hdecode Hpc_bound Hdst_bound Hr_bound Hneq_dst Hneq_pc.
  unfold run1.
  rewrite Hdecode.
  unfold step; cbn.
  set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
  assert (Hlen_pc : length (regs st_pc) = length (regs st)).
  { unfold st_pc.
    apply length_regs_write_reg.
    exact Hpc_bound. }
  assert (Hdst_pc_bound : dst < length (regs st_pc)) by (rewrite Hlen_pc; exact Hdst_bound).
  assert (Hr_pc_bound : r < length (regs st_pc)) by (rewrite Hlen_pc; exact Hr_bound).
  assert (Hneq_dst_sym : dst <> r) by (intro Heq; apply Hneq_dst; symmetry; exact Heq).
  assert (Hneq_pc_sym : REG_PC <> r) by (intro Heq; apply Hneq_pc; symmetry; exact Heq).
  assert (Hr_pc_eq : read_reg r st_pc = read_reg r st).
  { unfold st_pc.
    apply (read_reg_write_reg_other st REG_PC r (S (read_reg REG_PC st)) Hpc_bound Hr_bound).
    exact Hneq_pc_sym. }
  rewrite <- Hr_pc_eq.
  fold (read_reg r st_pc).
  apply (read_reg_write_reg_other st_pc dst r (read_reg dst st + n) Hdst_pc_bound Hr_pc_bound).
  exact Hneq_dst_sym.
Qed.

Lemma run1_addconst_result : forall st dst n,
  decode_instr st = AddConst dst n ->
  REG_PC < length (regs st) ->
  dst < length (regs st) ->
  read_reg dst (run1 st) = read_reg dst st + n.
Proof.
  intros st dst n Hdecode Hpc_bound Hdst_bound.
  unfold run1.
  rewrite Hdecode.
  unfold step; cbn.
  set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
  assert (Hlen_pc : length (regs st_pc) = length (regs st)).
  { unfold st_pc.
    apply length_regs_write_reg.
    exact Hpc_bound. }
  assert (Hdst_pc_bound : dst < length (regs st_pc)) by (rewrite Hlen_pc; exact Hdst_bound).
  apply (read_reg_write_reg_same st_pc dst (read_reg dst st + n) Hdst_pc_bound).
Qed.

Lemma run1_addreg_result : forall st dst src1 src2,
  decode_instr st = AddReg dst src1 src2 ->
  REG_PC < length (regs st) ->
  dst < length (regs st) ->
  read_reg dst (run1 st) = read_reg src1 st + read_reg src2 st.
Proof.
  intros st dst src1 src2 Hdecode Hpc_bound Hdst_bound.
  unfold run1.
  rewrite Hdecode.
  unfold step; cbn.
  set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
  assert (Hlen_pc : length (regs st_pc) = length (regs st)).
  { unfold st_pc.
    apply length_regs_write_reg.
    exact Hpc_bound. }
  assert (Hdst_pc_bound : dst < length (regs st_pc)) by (rewrite Hlen_pc; exact Hdst_bound).
  apply (read_reg_write_reg_same st_pc dst (read_reg src1 st + read_reg src2 st) Hdst_pc_bound).
Qed.

Lemma run1_preserves_reg_addreg : forall st dst src1 src2 r,
  decode_instr st = AddReg dst src1 src2 ->
  REG_PC < length (regs st) ->
  dst < length (regs st) ->
  r < length (regs st) ->
  r <> dst ->
  r <> REG_PC ->
  read_reg r (run1 st) = read_reg r st.
Proof.
  intros st dst src1 src2 r Hdecode Hpc_bound Hdst_bound Hr_bound Hneq_dst Hneq_pc.
  unfold run1.
  rewrite Hdecode.
  unfold step; cbn.
  set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
  assert (Hlen_pc : length (regs st_pc) = length (regs st)).
  { unfold st_pc.
    apply length_regs_write_reg.
    exact Hpc_bound. }
  assert (Hdst_pc_bound : dst < length (regs st_pc)) by (rewrite Hlen_pc; exact Hdst_bound).
  assert (Hr_pc_bound : r < length (regs st_pc)) by (rewrite Hlen_pc; exact Hr_bound).
  assert (Hneq_dst_sym : dst <> r) by (intro Heq; apply Hneq_dst; symmetry; exact Heq).
  assert (Hneq_pc_sym : REG_PC <> r) by (intro Heq; apply Hneq_pc; symmetry; exact Heq).
  assert (Hr_pc_eq : read_reg r st_pc = read_reg r st).
  { unfold st_pc.
    apply (read_reg_write_reg_other st REG_PC r (S (read_reg REG_PC st)) Hpc_bound Hr_bound).
    exact Hneq_pc_sym. }
  rewrite <- Hr_pc_eq.
  fold (read_reg r st_pc).
  apply (read_reg_write_reg_other
           st_pc dst r (read_reg src1 st + read_reg src2 st)
           Hdst_pc_bound Hr_pc_bound).
  exact Hneq_dst_sym.
Qed.

Lemma run1_preserves_reg_loadindirect : forall st dst src r,
  decode_instr st = LoadIndirect dst src ->
  REG_PC < length (regs st) ->
  dst < length (regs st) ->
  r < length (regs st) ->
  r <> dst ->
  r <> REG_PC ->
  read_reg r (run1 st) = read_reg r st.
Proof.
  intros st dst src r Hdecode Hpc_bound Hdst_bound Hr_bound Hneq_dst Hneq_pc.
  unfold run1.
  rewrite Hdecode.
  unfold step; cbn.
  set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
  assert (Hlen_pc : length (regs st_pc) = length (regs st)).
  { unfold st_pc.
    apply length_regs_write_reg.
    exact Hpc_bound. }
  assert (Hdst_pc_bound : dst < length (regs st_pc)) by (rewrite Hlen_pc; exact Hdst_bound).
  assert (Hr_pc_bound : r < length (regs st_pc)) by (rewrite Hlen_pc; exact Hr_bound).
  assert (Hneq_dst_sym : dst <> r) by (intro Heq; apply Hneq_dst; symmetry; exact Heq).
  assert (Hneq_pc_sym : REG_PC <> r) by (intro Heq; apply Hneq_pc; symmetry; exact Heq).
  assert (Hr_pc_eq : read_reg r st_pc = read_reg r st).
  { unfold st_pc.
    apply (read_reg_write_reg_other st REG_PC r (S (read_reg REG_PC st)) Hpc_bound Hr_bound).
    exact Hneq_pc_sym. }
  rewrite <- Hr_pc_eq.
  fold (read_reg r st_pc).
  apply (read_reg_write_reg_other st_pc dst r (read_mem (read_reg src st) st) Hdst_pc_bound Hr_pc_bound).
  exact Hneq_dst_sym.
Qed.

Lemma run1_loadindirect_result : forall st dst src,
  decode_instr st = LoadIndirect dst src ->
  REG_PC < length (regs st) ->
  dst < length (regs st) ->
  read_reg dst (run1 st) = read_mem (read_reg src st) st.
Proof.
  intros st dst src Hdecode Hpc_bound Hdst_bound.
  unfold run1.
  rewrite Hdecode.
  unfold step; cbn.
  set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
  assert (Hlen_pc : length (regs st_pc) = length (regs st)).
  { unfold st_pc.
    apply length_regs_write_reg.
    exact Hpc_bound. }
  assert (Hdst_pc_bound : dst < length (regs st_pc)) by (rewrite Hlen_pc; exact Hdst_bound).
  apply (read_reg_write_reg_same st_pc dst (read_mem (read_reg src st) st) Hdst_pc_bound).
Qed.

Lemma run1_preserves_reg_loadconst : forall st dst val r,
  decode_instr st = LoadConst dst val ->
  REG_PC < length (regs st) ->
  dst < length (regs st) ->
  r < length (regs st) ->
  r <> dst ->
  r <> REG_PC ->
  read_reg r (run1 st) = read_reg r st.
Proof.
  intros st dst val r Hdecode Hpc_bound Hdst_bound Hr_bound Hneq_dst Hneq_pc.
  unfold run1.
  rewrite Hdecode.
  unfold step; cbn.
  set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
  assert (Hlen_pc : length (regs st_pc) = length (regs st)).
  { unfold st_pc.
    apply length_regs_write_reg.
    exact Hpc_bound. }
  assert (Hdst_pc_bound : dst < length (regs st_pc)) by (rewrite Hlen_pc; exact Hdst_bound).
  assert (Hr_pc_bound : r < length (regs st_pc)) by (rewrite Hlen_pc; exact Hr_bound).
    assert (Hneq_dst_sym : dst <> r) by (intro Heq; apply Hneq_dst; symmetry; exact Heq).
    assert (Hneq_pc_sym : REG_PC <> r) by (intro Heq; apply Hneq_pc; symmetry; exact Heq).
  assert (Hr_pc_eq : read_reg r st_pc = read_reg r st).
  { unfold st_pc.
    apply (read_reg_write_reg_other st REG_PC r (S (read_reg REG_PC st)) Hpc_bound Hr_bound).
    exact Hneq_pc_sym. }
  rewrite <- Hr_pc_eq.
  fold (read_reg r st_pc).
  apply (read_reg_write_reg_other st_pc dst r val Hdst_pc_bound Hr_pc_bound).
  exact Hneq_dst_sym.
Qed.

Lemma run1_loadconst_result : forall st dst val,
  decode_instr st = LoadConst dst val ->
  REG_PC < length (regs st) ->
  dst < length (regs st) ->
  read_reg dst (run1 st) = val.
Proof.
  intros st dst val Hdecode Hpc_bound Hdst_bound.
  unfold run1.
  rewrite Hdecode.
  unfold step; cbn.
  set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
  assert (Hlen_pc : length (regs st_pc) = length (regs st)).
  { unfold st_pc.
    apply length_regs_write_reg.
    exact Hpc_bound. }
  assert (Hdst_pc_bound : dst < length (regs st_pc)) by (rewrite Hlen_pc; exact Hdst_bound).
  apply (read_reg_write_reg_same st_pc dst val Hdst_pc_bound).
Qed.

Lemma read_reg_step_jz_true : forall st rc target r,
  Nat.eqb (read_reg rc st) 0 = true ->
  read_reg r (CPU.step (Jz rc target) st) = read_reg r (write_reg REG_PC target st).
Proof.
  intros st rc target r Hguard.
  unfold CPU.step.
  rewrite Hguard.
  reflexivity.
Qed.

Lemma read_reg_step_jz_false : forall st rc target r,
  Nat.eqb (read_reg rc st) 0 = false ->
  read_reg r (CPU.step (Jz rc target) st) = read_reg r (write_reg REG_PC (S (read_reg REG_PC st)) st).
Proof.
  intros st rc target r Hguard.
  unfold CPU.step.
  rewrite Hguard.
  reflexivity.
Qed.

Lemma read_reg_step_jnz_true : forall st rc target r,
  Nat.eqb (read_reg rc st) 0 = true ->
  read_reg r (CPU.step (Jnz rc target) st) = read_reg r (write_reg REG_PC (S (read_reg REG_PC st)) st).
Proof.
  intros st rc target r Hguard.
  unfold CPU.step.
  rewrite Hguard.
  reflexivity.
Qed.

Lemma read_reg_step_jnz_false : forall st rc target r,
  Nat.eqb (read_reg rc st) 0 = false ->
  read_reg r (CPU.step (Jnz rc target) st) = read_reg r (write_reg REG_PC target st).
Proof.
  intros st rc target r Hguard.
  unfold CPU.step.
  rewrite Hguard.
  reflexivity.
Qed.

Lemma run1_jz_true_read : forall st rc target r,
  decode_instr st = Jz rc target ->
  Nat.eqb (read_reg rc st) 0 = true ->
  read_reg r (run1 st) = read_reg r (write_reg REG_PC target st).
Proof.
  intros st rc target r Hdecode Heqb.
  unfold run1.
  rewrite Hdecode.
  apply read_reg_step_jz_true.
  exact Heqb.
Qed.

Lemma run1_jz_false_read : forall st rc target r,
  decode_instr st = Jz rc target ->
  Nat.eqb (read_reg rc st) 0 = false ->
  read_reg r (run1 st) = read_reg r (write_reg REG_PC (S (read_reg REG_PC st)) st).
Proof.
  intros st rc target r Hdecode Heqb.
  unfold run1.
  rewrite Hdecode.
  apply read_reg_step_jz_false.
  exact Heqb.
Qed.

Lemma run1_jnz_true_read : forall st rc target r,
  decode_instr st = Jnz rc target ->
  Nat.eqb (read_reg rc st) 0 = true ->
  read_reg r (run1 st) = read_reg r (write_reg REG_PC (S (read_reg REG_PC st)) st).
Proof.
  intros st rc target r Hdecode Heqb.
  unfold run1.
  rewrite Hdecode.
  apply read_reg_step_jnz_true.
  exact Heqb.
Qed.

Lemma run1_jnz_false_read : forall st rc target r,
  decode_instr st = Jnz rc target ->
  Nat.eqb (read_reg rc st) 0 = false ->
  read_reg r (run1 st) = read_reg r (write_reg REG_PC target st).
Proof.
  intros st rc target r Hdecode Heqb.
  unfold run1.
  rewrite Hdecode.
  apply read_reg_step_jnz_false.
  exact Heqb.
Qed.

Lemma run1_preserves_reg_jz_true : forall st rc target r,
  decode_instr st = Jz rc target ->
  Nat.eqb (read_reg rc st) 0 = true ->
  REG_PC < length (regs st) ->
  r < length (regs st) ->
  r <> REG_PC ->
  read_reg r (run1 st) = read_reg r st.
Proof.
  intros st rc target r Hdecode Heqb Hpc_bound Hr_bound Hr_neq.
  pose proof (run1_jz_true_read st rc target r Hdecode Heqb) as Hstep.
  rewrite Hstep.
  apply (read_reg_write_reg_other st REG_PC r target Hpc_bound Hr_bound).
  intro Heq. apply Hr_neq. symmetry. exact Heq.
Qed.

Lemma run1_preserves_reg_jz_false : forall st rc target r,
  decode_instr st = Jz rc target ->
  Nat.eqb (read_reg rc st) 0 = false ->
  REG_PC < length (regs st) ->
  r < length (regs st) ->
  r <> REG_PC ->
  read_reg r (run1 st) = read_reg r st.
Proof.
  intros st rc target r Hdecode Heqb_false Hpc_bound Hr_bound Hr_neq.
  pose proof (run1_jz_false_read st rc target r Hdecode Heqb_false) as Hstep.
  rewrite Hstep.
  apply (read_reg_write_reg_other st REG_PC r (S (read_reg REG_PC st)) Hpc_bound Hr_bound).
  intro Heq. apply Hr_neq. symmetry. exact Heq.
Qed.

Lemma run1_preserves_reg_jnz_false : forall st rc target r,
  decode_instr st = Jnz rc target ->
  Nat.eqb (read_reg rc st) 0 = false ->
  REG_PC < length (regs st) ->
  r < length (regs st) ->
  r <> REG_PC ->
  read_reg r (run1 st) = read_reg r st.
Proof.
  intros st rc target r Hdecode Heqb_false Hpc_bound Hr_bound Hr_neq.
  pose proof (run1_jnz_false_read st rc target r Hdecode Heqb_false) as Hstep.
  rewrite Hstep.
  apply (read_reg_write_reg_other st REG_PC r target Hpc_bound Hr_bound).
  intro Heq. apply Hr_neq. symmetry. exact Heq.
Qed.

(* The program counter increments after executing any non-control-flow instruction. *)
Lemma run1_pc_succ : forall s,
  CPU.pc_unchanged (decode_instr s) ->
  read_reg REG_PC (run1 s) = S (read_reg REG_PC s).
Proof.
  intros s Hdec. unfold run1.
  apply CPU.step_pc_succ. exact Hdec.
Qed.

Lemma run1_pc_succ_instr : forall s instr,
  decode_instr s = instr ->
  CPU.pc_unchanged instr ->
  read_reg REG_PC (run1 s) = S (read_reg REG_PC s).
Proof.
  intros s instr Hdecode Hunchanged.
  subst instr.
  apply run1_pc_succ. exact Hunchanged.
Qed.

Lemma run1_pc_after_apply : forall st,
  read_reg REG_PC st = 29 ->
  firstn (length program) (mem st) = program ->
  read_reg REG_PC (run1 st) = 30.
Proof.
  intros st Hpc Hmem.
  pose proof (decode_instr_apply_start st Hpc Hmem) as Hdecode.
  assert (Hunchanged : CPU.pc_unchanged (CopyReg REG_TEMP1 REG_HEAD)).
  { unfold CPU.pc_unchanged. simpl. discriminate. }
  pose proof (run1_pc_succ_instr st _ Hdecode Hunchanged) as Hsucc.
  rewrite Hpc in Hsucc.
  exact Hsucc.
Qed.

Lemma run1_pc_monotonic_after_apply : forall st,
  29 <= read_reg REG_PC st < 48 ->
  firstn (length program) (mem st) = program ->
  29 <= read_reg REG_PC (run1 st).
Proof.
  intros st Hpc_range Hmem.
  destruct Hpc_range as [Hpc_min Hpc_max].
  pose proof UTM_Program.program_instrs_length_gt_48 as Hlen_gt.
  assert (Hpc_bound : read_reg REG_PC st < length UTM_Program.program_instrs) by lia.
  pose proof (decode_instr_program_state st Hpc_bound Hmem) as Hdecode.
  pose proof (UTM_Program.program_instrs_monotonic_after_apply (read_reg REG_PC st)
                 (conj Hpc_min Hpc_max)) as Hmono.
  pose proof (decode_instr_program_at_pc (read_reg REG_PC st) Hpc_bound) as Hinstr_eq.
  rewrite Hinstr_eq in Hdecode.
  destruct (nth (read_reg REG_PC st) UTM_Program.program_instrs Halt) as
    [rd val | rd ra | ra rv | rd rs | rd val | rd r1 r2 | rd r1 r2 | rc target | rc target | ] eqn:Hinstr;
    simpl in Hmono.
  - (* LoadConst *)
    pose proof (run1_pc_succ_instr st (LoadConst rd val) Hdecode) as Hsucc.
    apply Hsucc in Hmono.
    rewrite Hmono. lia.
  - (* LoadIndirect *)
    pose proof (run1_pc_succ_instr st (LoadIndirect rd ra) Hdecode) as Hsucc.
    apply Hsucc in Hmono.
    rewrite Hmono. lia.
  - (* StoreIndirect *)
    pose proof (run1_pc_succ_instr st (StoreIndirect ra rv) Hdecode) as Hsucc.
    assert (Htrue : True) by exact I.
    apply Hsucc in Htrue.
    rewrite Htrue. lia.
  - (* CopyReg *)
    pose proof (run1_pc_succ_instr st (CopyReg rd rs) Hdecode) as Hsucc.
    apply Hsucc in Hmono.
    rewrite Hmono. lia.
  - (* AddConst *)
    pose proof (run1_pc_succ_instr st (AddConst rd val) Hdecode) as Hsucc.
    apply Hsucc in Hmono.
    rewrite Hmono. lia.
  - (* AddReg *)
    pose proof (run1_pc_succ_instr st (AddReg rd r1 r2) Hdecode) as Hsucc.
    apply Hsucc in Hmono.
    rewrite Hmono. lia.
  - (* SubReg *)
    pose proof (run1_pc_succ_instr st (SubReg rd r1 r2) Hdecode) as Hsucc.
    apply Hsucc in Hmono.
    rewrite Hmono. lia.
  - (* Jz case *)
    destruct (Nat.eqb (read_reg rc st) 0) eqn:Heq.
    + pose proof (CPU.step_jz_true rc target st Heq) as Hpc.
      unfold run1. rewrite Hdecode. rewrite Hpc. exact Hmono.
    + pose proof (CPU.step_jz_false rc target st Heq) as Hpc.
      unfold run1. rewrite Hdecode. rewrite Hpc. lia.
  - (* Jnz case *)
    destruct (Nat.eqb (read_reg rc st) 0) eqn:Heq.
    + pose proof (CPU.step_jnz_true rc target st Heq) as Hpc.
      unfold run1. rewrite Hdecode. rewrite Hpc. lia.
    + pose proof (CPU.step_jnz_false rc target st Heq) as Hpc.
      unfold run1. rewrite Hdecode. rewrite Hpc. exact Hmono.
  - (* Halt *)
    unfold run1. rewrite (eq_trans Hdecode (eq_sym Hinstr)). simpl. lia.
Qed.

(* Run the program for n steps. *)
Fixpoint run_n (s : CPU.State) (n : nat) : CPU.State :=
  match n with
  | 0 => s
  | S k => run_n (run1 s) k
  end.

(* Unfolding lemma for [run_n]. *)
Lemma run_n_succ : forall s n, run_n s (S n) = run_n (run1 s) n.
Proof. reflexivity. Qed.

Lemma run1_run_n : forall a s,
  run_n (run1 s) a = run1 (run_n s a).
Proof.
  induction a as [|a IH]; intros s; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* Composition property for [run_n]: executing [a] then [b] steps is the
   same as executing [a + b] steps. This is useful to split and rejoin
   the interpreter execution into phases. *)
Lemma run_n_add : forall s a b,
  run_n s (a + b) = run_n (run_n s a) b.
Proof.
  intros s a b.
  revert s a.
  induction b as [|b IH]; intros s a; simpl.
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite Nat.add_succ_r. simpl.
    specialize (IH (run1 s) a).
    rewrite IH.
    rewrite run1_run_n.
    reflexivity.
  Qed.

(* Helper tactic: normalize nested [run1]/[run_n] expressions into a
   canonical shape. This centralizes the small rewriting steps that
   commonly cause fragile proof scripts when witnesses are constructed
   by hand. Use [normalize_run_n] before attempting [rewrite] across
   equivalences involving [run_n] and [run1]. *)
Ltac normalize_run_n :=
  repeat (match goal with
  | |- context[run_n ?s (S ?n)] => rewrite (run_n_succ s n)
  | |- context[run_n (run1 ?s) ?n] => rewrite (run1_run_n n s)
  | |- context[run_n ?s (?a + ?b)] => rewrite (run_n_add s a b)
  | H: context[run_n ?s (S ?n)] |- _ => rewrite (run_n_succ s n) in H
  | H: context[run_n (run1 ?s) ?n] |- _ => rewrite (run1_run_n n s) in H
  | H: context[run_n ?s (?a + ?b)] |- _ => rewrite (run_n_add s a b) in H
  end).

Lemma run1_pc_before_apply_le : forall st,
  read_reg REG_PC st < 29 ->
  firstn (length program) (mem st) = program ->
  read_reg REG_PC (run1 st) <= 29.
Proof.
  intros st Hpc Hmem.
  pose proof (decode_instr_before_apply_not_store st Hpc Hmem) as Hnotstore.
  pose proof (decode_instr_before_apply_jump_target_lt st Hpc Hmem) as Htarget.
  pose proof (decode_instr_before_apply_pc_unchanged st Hpc Hmem) as Hunchanged.
  destruct (decode_instr st) as [rd val | rd ra | ra rv | rd rs | rd val | rd r1 r2 | rd r1 r2 | rc target | rc target | ] eqn:Hinstr.
  - simpl in Hunchanged.
    pose proof (run1_pc_succ_instr st _ Hinstr Hunchanged) as Hpc_succ.
    rewrite Hpc_succ.
    lia.
  - simpl in Hunchanged.
    pose proof (run1_pc_succ_instr st _ Hinstr Hunchanged) as Hpc_succ.
    rewrite Hpc_succ.
    lia.
  - now inversion Hnotstore.
  - simpl in Hunchanged.
    pose proof (run1_pc_succ_instr st _ Hinstr Hunchanged) as Hpc_succ.
    rewrite Hpc_succ.
    lia.
  - simpl in Hunchanged.
    pose proof (run1_pc_succ_instr st _ Hinstr Hunchanged) as Hpc_succ.
    rewrite Hpc_succ.
    lia.
  - simpl in Hunchanged.
    pose proof (run1_pc_succ_instr st _ Hinstr Hunchanged) as Hpc_succ.
    rewrite Hpc_succ.
    lia.
  - simpl in Hunchanged.
    pose proof (run1_pc_succ_instr st _ Hinstr Hunchanged) as Hpc_succ.
    rewrite Hpc_succ.
    lia.
  - simpl in Htarget.
    destruct (Nat.eqb (read_reg rc st) 0) eqn:Heq.
    + pose proof (run1_jz_true_read st rc target REG_PC Hinstr Heq) as Hpc_run.
      rewrite Hpc_run.
      rewrite read_pc_write_pc.
      apply Nat.lt_le_incl; exact Htarget.
    + pose proof (run1_jz_false_read st rc target REG_PC Hinstr Heq) as Hpc_run.
      rewrite Hpc_run.
      rewrite read_pc_write_pc.
      lia.
  - simpl in Htarget.
    destruct (Nat.eqb (read_reg rc st) 0) eqn:Heq.
    + pose proof (run1_jnz_true_read st rc target REG_PC Hinstr Heq) as Hpc_run.
      rewrite Hpc_run.
      rewrite read_pc_write_pc.
      lia.
    + pose proof (run1_jnz_false_read st rc target REG_PC Hinstr Heq) as Hpc_run.
      rewrite Hpc_run.
      rewrite read_pc_write_pc.
      apply Nat.lt_le_incl; exact Htarget.
  - unfold run1; rewrite Hinstr; simpl.
    apply Nat.lt_le_incl; exact Hpc.
Qed.

Lemma run1_pc_before_apply_hits_29 : forall st,
  read_reg REG_PC st < 29 ->
  firstn (length program) (mem st) = program ->
  read_reg REG_PC (run1 st) = 29 ->
  read_reg REG_PC st = 28.
Proof.
  intros st Hpc Hmem Hfinal.
  pose proof (decode_instr_before_apply_not_store st Hpc Hmem) as Hnotstore.
  pose proof (decode_instr_before_apply_jump_target_lt st Hpc Hmem) as Htarget.
  pose proof (decode_instr_before_apply_pc_unchanged st Hpc Hmem) as Hunchanged.
  destruct (decode_instr st) as [rd val | rd ra | ra rv | rd rs | rd val | rd r1 r2
                               | rd r1 r2 | rc target | rc target | ] eqn:Hinstr;
    simpl in Hunchanged; try (simpl in Htarget);
    try now inversion Hnotstore;
    try (unfold run1 in Hfinal; rewrite Hinstr in Hfinal; simpl in Hfinal; lia).
  - pose proof (run1_pc_succ_instr st _ Hinstr Hunchanged) as Hsucc.
    rewrite Hsucc in Hfinal.
    lia.
  - pose proof (run1_pc_succ_instr st _ Hinstr Hunchanged) as Hsucc.
    rewrite Hsucc in Hfinal.
    lia.
  - pose proof (run1_pc_succ_instr st _ Hinstr Hunchanged) as Hsucc.
    rewrite Hsucc in Hfinal.
    lia.
  - pose proof (run1_pc_succ_instr st _ Hinstr Hunchanged) as Hsucc.
    rewrite Hsucc in Hfinal.
    lia.
  - pose proof (run1_pc_succ_instr st _ Hinstr Hunchanged) as Hsucc.
    rewrite Hsucc in Hfinal.
    lia.
  - pose proof (run1_pc_succ_instr st _ Hinstr Hunchanged) as Hsucc.
    rewrite Hsucc in Hfinal.
    lia.
  - simpl in Htarget.
    destruct (Nat.eqb (read_reg rc st) 0) eqn:Hcond.
    + pose proof (run1_jz_true_read st rc target REG_PC Hinstr Hcond) as Hpc_run.
      rewrite Hpc_run in Hfinal.
      rewrite read_pc_write_pc in Hfinal.
      lia.
    + pose proof (run1_jz_false_read st rc target REG_PC Hinstr Hcond) as Hpc_run.
      rewrite Hpc_run in Hfinal.
      rewrite read_pc_write_pc in Hfinal.
      lia.
  - simpl in Htarget.
    destruct (Nat.eqb (read_reg rc st) 0) eqn:Hcond.
    + pose proof (run1_jnz_true_read st rc target REG_PC Hinstr Hcond) as Hpc_run.
      rewrite Hpc_run in Hfinal.
      rewrite read_pc_write_pc in Hfinal.
      lia.
    + pose proof (run1_jnz_false_read st rc target REG_PC Hinstr Hcond) as Hpc_run.
      rewrite Hpc_run in Hfinal.
      rewrite read_pc_write_pc in Hfinal.
      lia.
Qed.

Lemma length_regs_write_reg_10 : forall st reg val,
  length (regs st) = 10 ->
  reg < length (regs st) ->
  length (regs (write_reg reg val st)) = 10.
Proof.
  intros st reg val Hlen Hlt.
  pose proof (length_regs_write_reg st reg val Hlt) as Hlen'.
  rewrite Hlen in Hlen'.
  exact Hlen'.
Qed.

Lemma length_regs_step_jz_10 : forall st rc target,
  length (regs st) = 10 ->
  length (regs (CPU.step (Jz rc target) st)) = 10.
Proof.
  intros st rc target Hlen.
  unfold CPU.step.
  destruct (Nat.eqb (read_reg rc st) 0) eqn:Hcond.
  - set (st_pc := write_reg REG_PC target st).
    change (length (regs st_pc) = 10).
    subst st_pc.
    apply length_regs_write_reg_10; [exact Hlen|rewrite Hlen; unfold REG_PC; lia].
  - set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    change (length (regs st_pc) = 10).
    subst st_pc.
    apply length_regs_write_reg_10; [exact Hlen|rewrite Hlen; unfold REG_PC; lia].
Qed.

Lemma length_regs_step_jnz_10 : forall st rc target,
  length (regs st) = 10 ->
  length (regs (CPU.step (Jnz rc target) st)) = 10.
Proof.
  intros st rc target Hlen.
  unfold CPU.step.
  destruct (Nat.eqb (read_reg rc st) 0) eqn:Hcond.
  - set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    change (length (regs st_pc) = 10).
    apply length_regs_write_reg_10; [exact Hlen|rewrite Hlen; unfold REG_PC; lia].
  - set (st_pc := write_reg REG_PC target st).
    change (length (regs st_pc) = 10).
    apply length_regs_write_reg_10; [exact Hlen|rewrite Hlen; unfold REG_PC; lia].
Qed.

Lemma decode_instr_before_apply_reg_bound : forall st,
  read_reg REG_PC st < 29 ->
  firstn (length program) (mem st) = program ->
  match decode_instr st with
| LoadConst rd _
| LoadIndirect rd _
| CopyReg rd _
| AddConst rd _
| AddReg rd _ _
| SubReg rd _ _ => rd < 10
| Jz rc _
| Jnz rc _ => rc < 10
| _ => True
end.
Proof.
  intros st Hpc Hmem.
  assert (Hpc_len : read_reg REG_PC st < length UTM_Program.program_instrs)
    by (pose proof program_instrs_length_gt_29; lia).
  pose proof (decode_instr_program_state st Hpc_len Hmem) as Hdecode.
  rewrite Hdecode.
  rewrite decode_instr_program_at_pc by exact Hpc_len.
  apply UTM_Program.program_instrs_before_apply_reg_bound.
  exact Hpc.
Qed.

Lemma run1_regs_length_before_apply : forall st,
  read_reg REG_PC st < 29 ->
  firstn (length program) (mem st) = program ->
  length (regs st) = 10 ->
  length (regs (run1 st)) = 10.
Proof.
  intros st Hpc Hmem Hlen.
  unfold run1.
  pose proof (decode_instr_before_apply_reg_bound st Hpc Hmem) as Hbound.
  destruct (decode_instr st) eqn:Hdecode;
    simpl in Hbound;
    simpl.
  - (* LoadConst *)
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = 10)
      by (subst st_pc;
          apply length_regs_write_reg_10; [exact Hlen|rewrite Hlen; unfold REG_PC; lia]).
    assert (Hdst : rd < length (regs st_pc))
      by (rewrite Hlen_pc; rewrite Hlen in Hbound; exact Hbound).
    pose proof (length_regs_write_reg st_pc rd n Hdst) as Hlen_final.
    now rewrite Hlen_pc in Hlen_final.
  - (* LoadIndirect *)
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = 10)
      by (subst st_pc;
          apply length_regs_write_reg_10; [exact Hlen|rewrite Hlen; unfold REG_PC; lia]).
    assert (Hdst : rd < length (regs st_pc))
      by (rewrite Hlen_pc; rewrite Hlen in Hbound; exact Hbound).
    pose proof (length_regs_write_reg st_pc rd (read_mem (read_reg ra st) st) Hdst) as Hlen_final.
    now rewrite Hlen_pc in Hlen_final.
  - (* StoreIndirect *)
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = 10)
      by (subst st_pc;
          apply length_regs_write_reg_10; [exact Hlen|rewrite Hlen; unfold REG_PC; lia]).
    now rewrite Hlen_pc.
  - (* CopyReg *)
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = 10)
      by (subst st_pc;
          apply length_regs_write_reg_10; [exact Hlen|rewrite Hlen; unfold REG_PC; lia]).
    assert (Hdst : rd < length (regs st_pc))
      by (rewrite Hlen_pc; rewrite Hlen in Hbound; exact Hbound).
    pose proof (length_regs_write_reg st_pc rd (read_reg rs st) Hdst) as Hlen_final.
    now rewrite Hlen_pc in Hlen_final.
  - (* AddConst *)
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = 10)
      by (subst st_pc;
          apply length_regs_write_reg_10; [exact Hlen|rewrite Hlen; unfold REG_PC; lia]).
    assert (Hdst : rd < length (regs st_pc))
      by (rewrite Hlen_pc; rewrite Hlen in Hbound; exact Hbound).
    pose proof (length_regs_write_reg st_pc rd (read_reg rd st + n) Hdst) as Hlen_final.
    now rewrite Hlen_pc in Hlen_final.
  - (* AddReg *)
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = 10)
      by (subst st_pc;
          apply length_regs_write_reg_10; [exact Hlen|rewrite Hlen; unfold REG_PC; lia]).
    assert (Hdst : rd < length (regs st_pc))
      by (rewrite Hlen_pc; rewrite Hlen in Hbound; exact Hbound).
    pose proof (length_regs_write_reg st_pc rd (read_reg rs1 st + read_reg rs2 st) Hdst) as Hlen_final.
    now rewrite Hlen_pc in Hlen_final.
  - (* SubReg *)
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = 10)
      by (subst st_pc;
          apply length_regs_write_reg_10; [exact Hlen|rewrite Hlen; unfold REG_PC; lia]).
    assert (Hdst : rd < length (regs st_pc))
      by (rewrite Hlen_pc; rewrite Hlen in Hbound; exact Hbound).
    pose proof (length_regs_write_reg st_pc rd (read_reg rs1 st - read_reg rs2 st) Hdst) as Hlen_final.
    now rewrite Hlen_pc in Hlen_final.
  - (* Jz *)
    apply length_regs_step_jz_10; assumption.
  - (* Jnz *)
    apply length_regs_step_jnz_10; assumption.
  - (* Halt *) exact Hlen.
Qed.

Lemma run1_program_prefix_before_apply : forall st,
  read_reg REG_PC st < 29 ->
  firstn (length program) (mem st) = program ->
  firstn (length program) (mem (run1 st)) = program.
Proof.
  intros st Hpc Hmem.
  pose proof (decode_instr_before_apply_not_store st Hpc Hmem) as Hnostore.
  assert ((run1 st).(mem) = st.(mem))
    by (apply run1_mem_preserved_if_no_store; exact Hnostore).
  rewrite H.
  exact Hmem.
Qed.

Lemma run_n_program_prefix_before_apply : forall st k,
  (forall j, j < k -> read_reg REG_PC (run_n st j) < 29) ->
  firstn (length program) (mem st) = program ->
  firstn (length program) (mem (run_n st k)) = program.
Proof.
  intros st k.
  revert st.
  induction k as [|k IH]; intros st Hguard Hmem.
  - exact Hmem.
  - rewrite run_n_succ.
    set (st1 := run1 st).
    assert (Hpc_st : read_reg REG_PC st < 29).
    { specialize (Hguard 0).
      assert (0 < S k) by lia.
      specialize (Hguard H).
      simpl in Hguard.
      exact Hguard.
    }
    assert (Hmem_st1 : firstn (length program) (mem st1) = program).
    { apply run1_program_prefix_before_apply; assumption. }
    assert (Hguard_st1 : forall j, j < k -> read_reg REG_PC (run_n st1 j) < 29).
    { intros j Hj.
      unfold st1.
      specialize (Hguard (S j)).
      assert (S j < S k) by lia.
      specialize (Hguard H).
      rewrite run_n_succ in Hguard.
      exact Hguard.
    }
    specialize (IH st1 Hguard_st1 Hmem_st1).
    exact IH.
  Qed.

Lemma run_n_regs_length_before_apply : forall st k,
  length (regs st) = 10 ->
  firstn (length program) (mem st) = program ->
  (forall j, j < k -> read_reg REG_PC (run_n st j) < 29) ->
  length (regs (run_n st k)) = 10.
Proof.
  intros st k Hlen Hprog Hguard.
  induction k as [|k IH]. 
  - exact Hlen.
  - rewrite run_n_succ.
    set (st_k := run_n st k).
    assert (Hpc_k : read_reg REG_PC st_k < 29).
    { apply Hguard. lia. }
    assert (Hprog_k : firstn (length program) (mem st_k) = program).
    { apply run_n_program_prefix_before_apply.
      - intros j Hj.
        apply Hguard.
        lia.
      - exact Hprog.
    }
    assert (Hlen_k : length (regs st_k) = 10).
    { apply IH; try assumption.
      intros j Hj.
      apply Hguard.
      lia.
    }
    rewrite run1_run_n.
    apply run1_regs_length_before_apply; assumption.
  Qed.

Lemma run1_mem_preserved_if_pc_le_29 : forall st,
  read_reg REG_PC st <= 29 ->
  firstn (length program) (mem st) = program ->
  (run1 st).(mem) = st.(mem).
Proof.
  intros st Hpc Hmem.
  destruct (Nat.lt_ge_cases (read_reg REG_PC st) 29) as [Hlt|Hge].
  - pose proof (decode_instr_before_apply_not_store st Hlt Hmem) as Hnostore.
    apply run1_mem_preserved_if_no_store; exact Hnostore.
  - assert (read_reg REG_PC st = 29) by lia.
    pose proof (decode_instr_apply_start st H Hmem) as Hdecode.
    apply run1_mem_preserved_if_no_store.
    now rewrite Hdecode.
Qed.

Lemma step_pc22_copy_addr : forall st,
  read_reg REG_PC st = 22 ->
  firstn (length program) (mem st) = program ->
  length (regs st) = 10 ->
  read_reg REG_PC (run1 st) = 23 /\
  mem (run1 st) = mem st /\
  read_reg REG_TEMP1 (run1 st) = read_reg REG_ADDR st /\
  read_reg REG_ADDR (run1 st) = read_reg REG_ADDR st /\
  length (regs (run1 st)) = 10.
Proof.
  intros st Hpc Hprog Hlen.
  pose proof (eq_sym Hpc) as Hpc_sym.
  assert (Hpc_lt : read_reg REG_PC st < length UTM_Program.program_instrs)
    by (rewrite Hpc; pose proof UTM_Program.program_instrs_length_gt_48; lia).
  pose proof (decode_instr_program_state st Hpc_lt Hprog) as Hdecode_prog.
  assert (Haddr_rewrite :
              decode_instr_from_mem program (4 * read_reg REG_PC st) =
              decode_instr_from_mem program (4 * 22))
    by (rewrite Hpc; reflexivity).
  rewrite Haddr_rewrite in Hdecode_prog.
  rewrite decode_instr_program_at_pc with (pc := 22) in Hdecode_prog
    by (pose proof UTM_Program.program_instrs_length_gt_48; lia).
  assert (Hdecode : decode_instr st = CopyReg REG_TEMP1 REG_ADDR)
    by exact Hdecode_prog.
  split.
  { assert (Hunchanged : CPU.pc_unchanged (CopyReg REG_TEMP1 REG_ADDR))
      by (unfold CPU.pc_unchanged, REG_PC; simpl; intro Heq; discriminate).
    pose proof (run1_pc_succ_instr st _ Hdecode Hunchanged) as Hsucc.
rewrite Hpc in Hsucc. simpl in Hsucc. exact Hsucc. }
  split.
  { unfold run1. rewrite Hdecode.
    cbn [CPU.step read_reg write_reg read_mem].
    reflexivity.
  }
  split.
  { unfold run1. rewrite Hdecode.
    cbn [CPU.step read_reg write_reg read_mem].
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = 10).
    { subst st_pc.
      assert (Hlt : REG_PC < length (regs st))
        by (rewrite Hlen; unfold REG_PC; lia).
      pose proof (length_regs_write_reg st REG_PC (S (read_reg REG_PC st)) Hlt)
        as Hlen'.
      rewrite Hlen in Hlen'. exact Hlen'. }
    assert (Htemp_len : REG_TEMP1 < length (regs st_pc))
      by (rewrite Hlen_pc; unfold REG_TEMP1; lia).
    pose proof (read_reg_write_reg_same st_pc REG_TEMP1 (read_reg REG_ADDR st) Htemp_len) as Htemp_eq.
    exact Htemp_eq.
  }
  split.
  { unfold run1. rewrite Hdecode.
    cbn [CPU.step read_reg write_reg read_mem].
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = 10).
    { subst st_pc.
      assert (Hlt : REG_PC < length (regs st))
        by (rewrite Hlen; unfold REG_PC; lia).
      pose proof (length_regs_write_reg st REG_PC (S (read_reg REG_PC st)) Hlt)
        as Hlen_pc_raw.
      rewrite Hlen in Hlen_pc_raw.
      exact Hlen_pc_raw. }
    assert (Htemp1 : REG_TEMP1 < length (regs st_pc)) by (rewrite Hlen_pc; unfold REG_TEMP1; lia).
    assert (Htemp2 : REG_ADDR < length (regs st_pc)) by (rewrite Hlen_pc; unfold REG_ADDR; lia).
    assert (Hneq_temp : REG_TEMP1 <> REG_ADDR) by (unfold REG_TEMP1, REG_ADDR; lia).
    eapply eq_trans.
    2: {
      subst st_pc.
      assert (Hpc_len : REG_PC < length (regs st))
        by (rewrite Hlen; unfold REG_PC; lia).
      assert (Haddr_len : REG_ADDR < length (regs st)) by (rewrite Hlen; unfold REG_ADDR; lia).
      assert (Hneq_pc : REG_PC <> REG_ADDR) by (unfold REG_PC, REG_ADDR; lia).
      pose proof (read_reg_write_reg_other st REG_PC REG_ADDR (S (read_reg REG_PC st))
                     Hpc_len Haddr_len Hneq_pc) as Haddr_base.
      exact Haddr_base. }
    pose proof (read_reg_write_reg_other st_pc REG_TEMP1 REG_ADDR (read_reg REG_ADDR st)
                   Htemp1 Htemp2 Hneq_temp) as Haddr_temp.
    exact Haddr_temp.
  }
  { unfold run1. rewrite Hdecode.
    cbn [CPU.step read_reg write_reg read_mem].
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = 10).
    { subst st_pc.
      assert (Hlt : REG_PC < length (regs st))
        by (rewrite Hlen; unfold REG_PC; lia).
      pose proof (length_regs_write_reg st REG_PC (S (read_reg REG_PC st)) Hlt)
        as Hlen_pc_raw.
      rewrite Hlen in Hlen_pc_raw.
      exact Hlen_pc_raw. }
    assert (Htemp_len : REG_TEMP1 < length (regs st_pc))
      by (rewrite Hlen_pc; unfold REG_TEMP1; lia).
    pose proof (length_regs_write_reg st_pc REG_TEMP1 (read_reg REG_ADDR st) Htemp_len)
      as Hlen_final.
    rewrite Hlen_pc in Hlen_final.
    exact Hlen_final.
  }
Qed.

Lemma step_pc23_add_temp1_2 : forall st,
  read_reg REG_PC st = 23 ->
  firstn (length program) (mem st) = program ->
  length (regs st) = 10 ->
  read_reg REG_PC (run1 st) = 24 /\
  mem (run1 st) = mem st /\
  read_reg REG_TEMP1 (run1 st) = read_reg REG_TEMP1 st + 2 /\
  length (regs (run1 st)) = 10.
Proof.
  intros st Hpc Hprog Hlen.
  pose proof (eq_sym Hpc) as Hpc_sym.
  assert (Hpc_lt : read_reg REG_PC st < length program_instrs)
    by (rewrite Hpc; pose proof program_instrs_length_gt_48; lia).
  pose proof (decode_instr_program_state st Hpc_lt Hprog) as Hdecode_prog.
  assert (Haddr_rewrite :
            decode_instr_from_mem program (4 * read_reg REG_PC st) =
            decode_instr_from_mem program (4 * 23))
    by (rewrite Hpc; reflexivity).
  rewrite Haddr_rewrite in Hdecode_prog.
  rewrite decode_instr_program_at_pc with (pc := 23) in Hdecode_prog
    by (pose proof program_instrs_length_gt_48; lia).
  assert (Hdecode : decode_instr st = AddConst REG_TEMP1 2)
    by exact Hdecode_prog.
  split.
  { assert (Hunchanged : CPU.pc_unchanged (AddConst REG_TEMP1 2))
        by (unfold CPU.pc_unchanged, REG_PC; simpl; intro Heq; discriminate).
    pose proof (run1_pc_succ_instr st _ Hdecode Hunchanged) as Hsucc.
    rewrite Hpc in Hsucc. simpl in Hsucc. exact Hsucc. }
  split.
  { unfold run1. rewrite Hdecode.
    cbn [CPU.step read_reg write_reg read_mem].
    reflexivity. }
  split.
  { unfold run1. rewrite Hdecode.
    cbn [CPU.step read_reg write_reg read_mem].
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = 10).
    { subst st_pc.
      assert (Hlt : REG_PC < length (regs st))
        by (rewrite Hlen; unfold REG_PC; lia).
      pose proof (length_regs_write_reg st REG_PC (S (read_reg REG_PC st)) Hlt)
        as Hlen'.
      rewrite Hlen in Hlen'. exact Hlen'. }
    assert (Htemp_len : REG_TEMP1 < length (regs st_pc))
      by (rewrite Hlen_pc; unfold REG_TEMP1; lia).
    pose proof (read_reg_write_reg_same st_pc REG_TEMP1 (read_reg REG_TEMP1 st + 2) Htemp_len)
      as Htemp_eq.
    exact Htemp_eq. }
  { unfold run1. rewrite Hdecode.
    cbn [CPU.step read_reg write_reg read_mem].
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = 10).
    { subst st_pc.
      assert (Hpc_len : REG_PC < length (regs st))
        by (rewrite Hlen; unfold REG_PC; lia).
      pose proof (length_regs_write_reg st REG_PC (S (read_reg REG_PC st)) Hpc_len)
        as Hlen_pc_raw.
      rewrite Hlen in Hlen_pc_raw.
      exact Hlen_pc_raw. }
    assert (Htemp_len : REG_TEMP1 < length (regs st_pc))
      by (rewrite Hlen_pc; unfold REG_TEMP1; lia).
    pose proof (length_regs_write_reg st_pc REG_TEMP1 (read_reg REG_TEMP1 st + 2) Htemp_len)
      as Hlen_final.
    rewrite Hlen_pc in Hlen_final.
    exact Hlen_final. }
Qed.

Lemma run_apply_phase_temp1 : forall st,
  read_reg REG_PC st = 22 ->
  firstn (length program) (mem st) = program ->
  length (regs st) = 10 ->
  let addr := read_reg REG_ADDR st in
  let st29 := run_n st 7 in
  read_reg REG_PC st29 = 29 /\
  mem st29 = mem st /\
  read_reg REG_Q' st29 = read_mem (addr + 2) st /\
  read_reg REG_WRITE st29 = read_mem (addr + 3) st /\
  read_reg REG_MOVE st29 = read_mem (addr + 4) st /\
  read_reg REG_TEMP1 st29 = addr + 4 /\
  length (regs st29) = 10.
Proof.
  intros st Hpc22 Hprog Hlen.
  set (addr := read_reg REG_ADDR st).
  set (st23 := run1 st).
  destruct (step_pc22_copy_addr st Hpc22 Hprog Hlen)
    as [Hpc23 [Hmem23 [Htemp1_copy [Haddr_copy Hlen23]]]].
  assert (Hprog23 : firstn (length program) (mem st23) = program).
  { unfold st23.
    rewrite Hmem23.
    exact Hprog. }
  assert (Hmem23_base : mem st23 = mem st).
  { unfold st23.
    exact Hmem23. }
  set (st24 := run1 st23).
  destruct (step_pc23_add_temp1_2 st23 Hpc23 Hprog23 Hlen23)
    as [Hpc24 [Hmem24 [Htemp1_plus2 Hlen24]]].
  assert (Hprog24 : firstn (length program) (mem st24) = program).
  { unfold st24.
    rewrite Hmem24.
    unfold st23.
    rewrite Hmem23.
    exact Hprog. }
  assert (Hmem24_base : mem st24 = mem st).
  { unfold st24.
    rewrite Hmem24.
    exact Hmem23_base. }
  assert (Htemp1_st24 : read_reg REG_TEMP1 st24 = addr + 2).
  { unfold st24.
    rewrite Htemp1_plus2.
    unfold st23.
    rewrite Htemp1_copy.
    reflexivity. }
  set (st25 := run1 st24).
  destruct (step_pc24_load_qprime st24 Hpc24 Hprog24 Hlen24)
    as [Hpc25 [Hmem25 [Hqprime_load [Htemp1_pres Hlen25]]]].
  assert (Hlen25_const : length (regs st25) = 10).
  { unfold st25.
    exact Hlen25. }
  assert (Hprog25 : firstn (length program) (mem st25) = program).
  { unfold st25.
    rewrite Hmem25.
    unfold st24.
    rewrite Hmem24.
    unfold st23.
    rewrite Hmem23.
    exact Hprog. }
  assert (Hmem25_base : mem st25 = mem st).
  { unfold st25.
    rewrite Hmem25.
    exact Hmem24_base. }
  assert (Htemp1_st25 : read_reg REG_TEMP1 st25 = addr + 2).
  { unfold st25.
    rewrite Htemp1_pres, Htemp1_st24.
    reflexivity. }
  assert (Hqprime_st25 : read_reg REG_Q' st25 = read_mem (addr + 2) st).
  { unfold st25.
    rewrite Hqprime_load, Htemp1_st24.
    rewrite (read_mem_mem_eq st24 st (addr + 2) Hmem24_base).
    reflexivity. }
  set (st26 := run1 st25).
  destruct (step_pc25_add_temp1_1 st25 Hpc25 Hprog25 Hlen25)
    as [Hpc26 [Hmem26 [Htemp1_plus1 Hlen26]]].
  assert (Hlen26_const : length (regs st26) = 10).
  { unfold st26.
    exact Hlen26. }
  assert (Hprog26 : firstn (length program) (mem st26) = program).
  { unfold st26.
    rewrite Hmem26.
    unfold st25.
    rewrite Hmem25.
    unfold st24.
    rewrite Hmem24.
    unfold st23.
    rewrite Hmem23.
    exact Hprog. }
  assert (Hmem26_base : mem st26 = mem st).
  { unfold st26.
    rewrite Hmem26.
    exact Hmem25_base. }
  assert (Htemp1_st26 : read_reg REG_TEMP1 st26 = addr + 3).
  { unfold st26.
    rewrite Htemp1_plus1, Htemp1_st25.
    lia. }
  assert (Hdecode25 : decode_instr st25 = AddConst REG_TEMP1 1).
  { assert (Hpc25_lt : read_reg REG_PC st25 < length program_instrs)
        by (unfold st25; rewrite Hpc25; pose proof program_instrs_length_gt_48; lia).
    pose proof (decode_instr_program_state st25 Hpc25_lt Hprog25) as Hdecode_prog.
    unfold st25 in Hdecode_prog.
    rewrite Hpc25 in Hdecode_prog.
    rewrite decode_instr_program_at_pc with (pc := 25) in Hdecode_prog
      by (pose proof program_instrs_length_gt_48; lia).
    exact Hdecode_prog. }
  assert (Hqprime_st26 : read_reg REG_Q' st26 = read_reg REG_Q' st25).
  { apply (run1_preserves_reg_addconst st25 REG_TEMP1 1 REG_Q').
    - exact Hdecode25.
    - rewrite Hlen25_const. unfold REG_PC. lia.
    - rewrite Hlen25_const. unfold REG_TEMP1. lia.
    - rewrite Hlen25_const. unfold REG_Q'. lia.
    - unfold REG_Q', REG_TEMP1. lia.
    - unfold REG_Q', REG_PC. lia. }
  set (st27 := run1 st26).
  destruct (step_pc26_load_write st26 Hpc26 Hprog26 Hlen26)
    as [Hpc27 [Hmem27 [Hwrite_load [Htemp1_pres26 Hlen27]]]].
  assert (Hlen27_const : length (regs st27) = 10).
  { unfold st27.
    exact Hlen27. }
  assert (Hprog27 : firstn (length program) (mem st27) = program).
  { unfold st27.
    rewrite Hmem27.
    unfold st26.
    rewrite Hmem26.
    unfold st25.
    rewrite Hmem25.
    unfold st24.
    rewrite Hmem24.
    unfold st23.
    rewrite Hmem23.
    exact Hprog. }
  assert (Hmem27_base : mem st27 = mem st).
  { unfold st27.
    rewrite Hmem27.
    exact Hmem26_base. }
  assert (Htemp1_st27 : read_reg REG_TEMP1 st27 = addr + 3).
  { unfold st27.
    rewrite Htemp1_pres26, Htemp1_st26.
    reflexivity. }
  assert (Hwrite_st27 : read_reg REG_WRITE st27 = read_mem (addr + 3) st).
  { unfold st27.
    rewrite Hwrite_load, Htemp1_st26.
    rewrite (read_mem_mem_eq st26 st (addr + 3) Hmem26_base).
    reflexivity. }
  assert (Hdecode26 : decode_instr st26 = LoadIndirect REG_WRITE REG_TEMP1).
  { assert (Hpc26_lt : read_reg REG_PC st26 < length program_instrs)
        by (unfold st26; rewrite Hpc26; pose proof program_instrs_length_gt_48; lia).
    pose proof (decode_instr_program_state st26 Hpc26_lt Hprog26) as Hdecode_prog.
    unfold st26 in Hdecode_prog.
    rewrite Hpc26 in Hdecode_prog.
    rewrite decode_instr_program_at_pc with (pc := 26) in Hdecode_prog
      by (pose proof program_instrs_length_gt_48; lia).
    exact Hdecode_prog. }
  assert (Hqprime_st27 : read_reg REG_Q' st27 = read_reg REG_Q' st26).
  { apply (run1_preserves_reg_loadindirect st26 REG_WRITE REG_TEMP1 REG_Q').
    - exact Hdecode26.
    - rewrite Hlen26_const. unfold REG_PC. lia.
    - rewrite Hlen26_const. unfold REG_WRITE. lia.
    - rewrite Hlen26_const. unfold REG_Q'. lia.
    - unfold REG_Q', REG_WRITE. lia.
    - unfold REG_Q', REG_PC. lia. }
  assert (Hwrite_st28 : read_reg REG_WRITE st27 = read_reg REG_WRITE st26).
  { apply (run1_preserves_reg_loadindirect st26 REG_WRITE REG_TEMP1 REG_WRITE).
    - exact Hdecode26.
    - rewrite Hlen26_const. unfold REG_PC. lia.
    - rewrite Hlen26_const. unfold REG_WRITE. lia.
    - rewrite Hlen26_const. unfold REG_WRITE. lia.
    - unfold REG_WRITE, REG_WRITE. lia.
    - unfold REG_WRITE, REG_PC. lia. }
  set (st28 := run1 st27).
  destruct (step_pc27_add_temp1_1 st27 Hpc27 Hprog27 Hlen27)
    as [Hpc28 [Hmem28 [Htemp1_plus1_2 Hlen28]]].
  assert (Hlen28_const : length (regs st28) = 10).
  { unfold st28.
    exact Hlen28. }
  assert (Hprog28 : firstn (length program) (mem st28) = program).
  { unfold st28.
    rewrite Hmem28.
    unfold st27.
    rewrite Hmem27.
    unfold st26.
    rewrite Hmem26.
    unfold st25.
    rewrite Hmem25.
    unfold st24.
    rewrite Hmem24.
    unfold st23.
    rewrite Hmem23.
    exact Hprog. }
  assert (Hmem28_base : mem st28 = mem st).
  { unfold st28.
    rewrite Hmem28.
    exact Hmem27_base. }
  assert (Htemp1_st28 : read_reg REG_TEMP1 st28 = addr + 4).
  { unfold st28.
    rewrite Htemp1_plus1_2, Htemp1_st27.
    lia. }
  assert (Hdecode27 : decode_instr st27 = AddConst REG_TEMP1 1).
  { assert (Hpc27_lt : read_reg REG_PC st27 < length program_instrs)
        by (unfold st27; rewrite Hpc27; pose proof program_instrs_length_gt_48; lia).
    pose proof (decode_instr_program_state st27 Hpc27_lt Hprog27) as Hdecode_prog.
    unfold st27 in Hdecode_prog.
    rewrite Hpc27 in Hdecode_prog.
    rewrite decode_instr_program_at_pc with (pc := 27) in Hdecode_prog
      by (pose proof program_instrs_length_gt_48; lia).
    exact Hdecode_prog. }
  assert (Hqprime_st28 : read_reg REG_Q' st28 = read_reg REG_Q' st27).
  { apply (run1_preserves_reg_addconst st27 REG_TEMP1 1 REG_Q').
    - exact Hdecode27.
    - rewrite Hlen27_const. unfold REG_PC. lia.
    - rewrite Hlen27_const. unfold REG_TEMP1. lia.
    - rewrite Hlen27_const. unfold REG_Q'. lia.
    - unfold REG_Q', REG_TEMP1. lia.
    - unfold REG_Q', REG_PC. lia. }
  assert (Hwrite_st28_final : read_reg REG_WRITE st28 = read_reg REG_WRITE st27).
  { apply (run1_preserves_reg_addconst st27 REG_TEMP1 1 REG_WRITE).
    - exact Hdecode27.
    - rewrite Hlen27_const. unfold REG_PC. lia.
    - rewrite Hlen27_const. unfold REG_TEMP1. lia.
    - rewrite Hlen27_const. unfold REG_WRITE. lia.
    - unfold REG_WRITE, REG_TEMP1. lia.
    - unfold REG_WRITE, REG_PC. lia. }
  set (st29 := run1 st28).
  destruct (step_pc28_load_move st28 Hpc28 Hprog28 Hlen28)
    as [Hpc29 [Hmem29 [Hmove_load [Htemp1_pres_final Hlen29]]]].
  assert (Hlen29_const : length (regs st29) = 10).
  { unfold st29.
    exact Hlen29. }
  assert (Hmem29_base : mem st29 = mem st).
  { unfold st29.
    rewrite Hmem29.
    exact Hmem28_base. }
  assert (Hdecode28 : decode_instr st28 = LoadIndirect REG_MOVE REG_TEMP1).
  { assert (Hpc28_lt : read_reg REG_PC st28 < length program_instrs)
        by (unfold st28; rewrite Hpc28; pose proof program_instrs_length_gt_48; lia).
    pose proof (decode_instr_program_state st28 Hpc28_lt Hprog28) as Hdecode_prog.
    unfold st28 in Hdecode_prog.
    rewrite Hpc28 in Hdecode_prog.
    rewrite decode_instr_program_at_pc with (pc := 28) in Hdecode_prog
      by (pose proof program_instrs_length_gt_48; lia).
    exact Hdecode_prog. }
  assert (Hqprime_st29 : read_reg REG_Q' st29 = read_reg REG_Q' st28).
  { apply (run1_preserves_reg_loadindirect st28 REG_MOVE REG_TEMP1 REG_Q').
    - exact Hdecode28.
    - rewrite Hlen28_const. unfold REG_PC. lia.
    - rewrite Hlen28_const. unfold REG_MOVE. lia.
    - rewrite Hlen28_const. unfold REG_Q'. lia.
    - unfold REG_Q', REG_MOVE. lia.
    - unfold REG_Q', REG_PC. lia. }
  assert (Hwrite_st29 : read_reg REG_WRITE st29 = read_reg REG_WRITE st28).
  { apply (run1_preserves_reg_loadindirect st28 REG_MOVE REG_TEMP1 REG_WRITE).
    - exact Hdecode28.
    - rewrite Hlen28_const. unfold REG_PC. lia.
    - rewrite Hlen28_const. unfold REG_MOVE. lia.
    - rewrite Hlen28_const. unfold REG_WRITE. lia.
    - unfold REG_WRITE, REG_MOVE. lia.
    - unfold REG_WRITE, REG_PC. lia. }
  assert (Hmove_st29 : read_reg REG_MOVE st29 = read_mem (addr + 4) st).
  { unfold st29.
    rewrite Hmove_load, Htemp1_st28.
    rewrite (read_mem_mem_eq st28 st (addr + 4) Hmem28_base).
    reflexivity. }
  assert (Hrun7 : run_n st 7 = st29).
  { unfold st29, st28, st27, st26, st25, st24, st23.
    simpl.
    repeat (rewrite run1_run_n).
    reflexivity. }
  assert (Hqprime_chain : read_reg REG_Q' st29 = read_reg REG_Q' st25).
  { rewrite Hqprime_st29, Hqprime_st28, Hqprime_st27.
    exact Hqprime_st26. }
  assert (Hwrite_chain : read_reg REG_WRITE st29 = read_reg REG_WRITE st27).
  { rewrite Hwrite_st29, Hwrite_st28_final.
    reflexivity. }
  repeat split.
  - rewrite Hrun7. exact Hpc29.
  - rewrite Hrun7. exact Hmem29_base.
  - rewrite Hrun7, Hqprime_chain.
    exact Hqprime_st25.
  - rewrite Hrun7, Hwrite_chain.
    exact Hwrite_st27.
  - rewrite Hrun7.
    exact Hmove_st29.
  - rewrite Hrun7.
    unfold st29.
    rewrite Htemp1_pres_final, Htemp1_st28.
    reflexivity.
  - rewrite Hrun7.
    rewrite Hlen29_const.
    reflexivity.
Qed.