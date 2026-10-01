(** A direct compiler from three-counter alternate Minsky machines to the
    four-register guest.  Counters occupy R0--R2 and R3 is scratch. *)

From Coq Require Import Arith Lia List.
Import ListNotations.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.Shared.Libs.DLW.Code Require Import subcode sss.
From Undecidability.MinskyMachines Require Import MM MMA.
From Kernel Require Import VMUnboundedStep VMSelfGuest VMSelfRun.

Definition mma3_reg (x : Fin.t 3) : nat := proj1_sig (Fin.to_nat x).

Definition mma3_addr (len pc : nat) : nat :=
  if pc =? 0 then 5 * len else 5 * (pc - 1).

Definition mma3_block (a len : nat) (i : mm_instr (Fin.t 3)) : list GInstr :=
  match i with
  | mm_inc x =>
      [GLoadImm 3 1 0;
       GAdd (mma3_reg x) (mma3_reg x) 3 0;
       GJump (5 * S a) 0;
       GHalt 0;
       GHalt 0]
  | mm_dec x target =>
      [GJnez (mma3_reg x) (5 * a + 2) 0;
       GJump (5 * S a) 0;
       GLoadImm 3 1 0;
       GSub (mma3_reg x) (mma3_reg x) 3 0;
       GJump (mma3_addr len target) 0]
  end.

Fixpoint mma3_compile_aux
    (a len : nat) (p : list (mm_instr (Fin.t 3))) : list GInstr :=
  match p with
  | [] => []
  | i :: rest => mma3_block a len i ++ mma3_compile_aux (S a) len rest
  end.

Definition mma3_compile (p : list (mm_instr (Fin.t 3))) : list GInstr :=
  mma3_compile_aux 0 (length p) p.

Lemma mma3_reg_lt : forall x, mma3_reg x < 3.
Proof. intros x. unfold mma3_reg. apply (proj2_sig (Fin.to_nat x)). Qed.

Lemma fin3_cases : forall x : Fin.t 3, x = pos0 \/ x = pos1 \/ x = pos2.
Proof.
  intro x. refine (Fin.caseS' x
    (fun z => z = pos0 \/ z = pos1 \/ z = pos2) _ _).
  - left. reflexivity.
  - intro x1. refine (Fin.caseS' x1
      (fun z => Fin.FS z = pos0 \/ Fin.FS z = pos1 \/ Fin.FS z = pos2) _ _).
    + right. left. reflexivity.
    + intro x2. refine (Fin.caseS' x2
        (fun z => Fin.FS (Fin.FS z) = pos0 \/
          Fin.FS (Fin.FS z) = pos1 \/ Fin.FS (Fin.FS z) = pos2) _ _).
      * right. right. reflexivity.
      * intro x0. exact (Fin.case0
          (fun z => Fin.FS (Fin.FS (Fin.FS z)) = pos0 \/
            Fin.FS (Fin.FS (Fin.FS z)) = pos1 \/
            Fin.FS (Fin.FS (Fin.FS z)) = pos2) x0).
Qed.

Lemma mma3_reg_pos0 : mma3_reg pos0 = 0. Proof. reflexivity. Qed.
Lemma mma3_reg_pos1 : mma3_reg pos1 = 1. Proof. reflexivity. Qed.
Lemma mma3_reg_pos2 : mma3_reg pos2 = 2. Proof. reflexivity. Qed.

Lemma mma3_block_length : forall a len i,
  length (mma3_block a len i) = 5.
Proof. intros a len []; reflexivity. Qed.

Lemma mma3_compile_aux_length : forall p a len,
  length (mma3_compile_aux a len p) = 5 * length p.
Proof.
  induction p as [|i p IH]; intros a len; [reflexivity|].
  cbn [mma3_compile_aux length]. rewrite app_length, mma3_block_length, IH.
  lia.
Qed.

Lemma mma3_compile_length : forall p,
  length (mma3_compile p) = 5 * length p.
Proof. intro p. apply mma3_compile_aux_length. Qed.

Lemma mma3_compile_aux_nth : forall p base len a i j,
  nth_error p a = Some i -> j < 5 ->
  nth_error (mma3_compile_aux base len p) (5 * a + j) =
  nth_error (mma3_block (base + a) len i) j.
Proof.
  induction p as [|x p IH]; intros base len a i j Ha Hj;
    [destruct a; discriminate|].
  destruct a as [|a]; cbn [nth_error] in Ha.
  - inversion Ha; subst x. cbn [mma3_compile_aux].
    rewrite nth_error_app1 by (rewrite mma3_block_length; lia).
    rewrite Nat.add_0_r. reflexivity.
  - cbn [mma3_compile_aux].
    rewrite nth_error_app2 by (rewrite mma3_block_length; lia).
    rewrite mma3_block_length.
    replace (5 * S a + j - 5) with (5 * a + j) by lia.
    rewrite (IH (S base) len a i j Ha Hj).
    replace (S base + a) with (base + S a) by lia. reflexivity.
Qed.

Lemma mma3_compile_nth : forall p a i j,
  nth_error p a = Some i -> j < 5 ->
  nth_error (mma3_compile p) (5 * a + j) =
  nth_error (mma3_block a (length p) i) j.
Proof.
  intros. unfold mma3_compile.
  rewrite (mma3_compile_aux_nth p 0 _ a i j); auto.
Qed.

Lemma mma3_compile_aux_wf : forall p a len,
  g_wf_program (mma3_compile_aux a len p).
Proof.
  unfold g_wf_program.
  induction p as [|i p IH]; intros a len; [constructor|].
  cbn [mma3_compile_aux]. apply Forall_app. split; [|apply IH].
  destruct i as [x|x target]; cbn [mma3_block];
    repeat (constructor;
      [unfold g_wf; cbn [g_dst g_rs1 g_rs2 g_cost];
       pose proof (mma3_reg_lt x); lia|]); constructor.
Qed.

Theorem mma3_compile_wf : forall p, g_wf_program (mma3_compile p).
Proof. intro p. apply mma3_compile_aux_wf. Qed.

Definition mma3_rel (len : nat) (s : nat * vec nat 3) (c : GConf) : Prop :=
  let '(pc, v) := s in
  gc_pc c = mma3_addr len pc /\
  gr0 (gc_g c) = vec_pos v pos0 /\
  gr1 (gc_g c) = vec_pos v pos1 /\
  gr2 (gc_g c) = vec_pos v pos2.

Lemma mma3_g_step_blk : forall p a i j c,
  nth_error p a = Some i -> j < 5 -> gc_pc c = 5 * a + j ->
  g_step (mma3_compile p) c =
  match nth_error (mma3_block a (length p) i) j with
  | Some gi =>
      let '(pc', mu', g') := g_next gi (gc_pc c) (gc_mu c) (gc_g c) in
      {| gc_pc := pc'; gc_mu := mu'; gc_g := g' |}
  | None => c
  end.
Proof.
  intros p a i j c Ha Hj Hpc. unfold g_step.
  rewrite Hpc, (mma3_compile_nth p a i j Ha Hj). reflexivity.
Qed.

Lemma mma3_g_run_blk : forall n p a i j c,
  nth_error p a = Some i -> j < 5 -> gc_pc c = 5 * a + j ->
  g_run (S n) (mma3_compile p) c =
  g_run n (mma3_compile p)
    (match nth_error (mma3_block a (length p) i) j with
     | Some gi =>
         let '(pc', mu', g') := g_next gi (gc_pc c) (gc_mu c) (gc_g c) in
         {| gc_pc := pc'; gc_mu := mu'; gc_g := g' |}
     | None => c
     end).
Proof. intros. cbn [g_run]. f_equal. apply mma3_g_step_blk; assumption. Qed.

Ltac mma3_blk_step Ha j :=
  rewrite (mma3_g_run_blk _ _ _ _ j _ Ha) by (cbn [gc_pc]; lia);
  cbn [mma3_block nth_error g_next gc_pc gc_mu gc_g g_set g_get
    gr0 gr1 gr2 gr3].

Lemma mma3_step_sim : forall p a i v s1 gc,
  nth_error p a = Some i ->
  @mma_sss 3 i (S a, v) s1 ->
  mma3_rel (length p) (S a, v) gc ->
  exists fuel, 0 < fuel /\
    mma3_rel (length p) s1 (g_run fuel (mma3_compile p) gc).
Proof.
  intros p a i v s1 [gpc mu [r0 r1 r2 r3]] Hi Hstep Hrel.
  unfold mma3_rel, mma3_addr in Hrel.
  cbn [gc_pc gc_g gr0 gr1 gr2] in Hrel.
  destruct Hrel as (Hpc & H0 & H1 & H2).
  cbn [Nat.eqb] in Hpc. subst gpc.
  inversion Hstep; subst; clear Hstep.
  - destruct (fin3_cases x) as [-> | [-> | ->]].
    all: cbn [mma3_reg Fin.to_nat] in *.
    all: exists 3; split; [lia|
      mma3_blk_step Hi 0; mma3_blk_step Hi 1; mma3_blk_step Hi 2;
      cbn [g_run]; unfold mma3_rel, mma3_addr, u_add;
      cbn [Nat.eqb gc_pc gc_g gr0 gr1 gr2];
      rew vec; rewrite ?mma3_reg_pos0, ?mma3_reg_pos1, ?mma3_reg_pos2;
      cbn [g_get g_set gr0 gr1 gr2 gr3 Nat.eqb]; repeat split; lia].
  - destruct (fin3_cases x) as [-> | [-> | ->]];
      cbn [mma3_reg Fin.to_nat] in *.
    all: exists 2; split; [lia|
      mma3_blk_step Hi 0;
      rewrite ?mma3_reg_pos0, ?mma3_reg_pos1, ?mma3_reg_pos2;
      cbn [g_get g_set gr0 gr1 gr2 gr3];
      match goal with Hzero : vec_pos ?vv _ = 0 |- _ => rewrite Hzero end;
      cbn [Nat.eqb]; mma3_blk_step Hi 1; cbn [g_run];
      unfold mma3_rel, mma3_addr;
      cbn [Nat.eqb gc_pc gc_g gr0 gr1 gr2]; repeat split; try reflexivity; lia].
  - destruct (fin3_cases x) as [-> | [-> | ->]];
      cbn [mma3_reg Fin.to_nat] in *.
    all: exists 4; split; [lia|
      mma3_blk_step Hi 0;
      rewrite ?mma3_reg_pos0, ?mma3_reg_pos1, ?mma3_reg_pos2;
      cbn [g_get g_set gr0 gr1 gr2 gr3];
      match goal with Hsucc : vec_pos ?vv _ = S ?z |- _ => rewrite Hsucc end;
      cbn [Nat.eqb]; mma3_blk_step Hi 2; mma3_blk_step Hi 3;
      mma3_blk_step Hi 4; cbn [g_run]; unfold mma3_rel, u_sub;
      rewrite ?mma3_reg_pos0, ?mma3_reg_pos1, ?mma3_reg_pos2;
      cbn [g_get g_set gc_pc gc_g gr0 gr1 gr2]; rew vec;
      repeat split; try reflexivity; lia].
Qed.

Lemma mma3_sss_step_fetch : forall p pc v s1,
  sss_step (@mma_sss 3) (1, p) (pc, v) s1 ->
  exists a i, pc = S a /\ nth_error p a = Some i /\
    @mma_sss 3 i (pc, v) s1.
Proof.
  intros p pc v s1 (k & left & i & right & data & Hcode & Hstate & Hstep).
  inversion Hcode; subst k. inversion Hstate; subst pc data.
  exists (length left), i. split; [lia|]. split; [|exact Hstep].
  rewrite nth_error_app2 by lia.
  replace (length left - length left) with 0 by lia. reflexivity.
Qed.

Lemma mma3_steps_sim : forall p n s s' gc,
  sss_steps (@mma_sss 3) (1, p) n s s' ->
  mma3_rel (length p) s gc ->
  exists fuel, mma3_rel (length p) s'
    (g_run fuel (mma3_compile p) gc).
Proof.
  intros p n s s' gc Hsteps. revert gc.
  induction Hsteps as [s|n s mid final Hone Hrest IH]; intros gc Hrel.
  - exists 0. exact Hrel.
  - destruct s as [pc v].
    destruct (mma3_sss_step_fetch p pc v mid Hone)
      as (a & i & Hpc & Hi & Hinstr). subst pc.
    destruct (mma3_step_sim p a i v mid gc Hi Hinstr Hrel)
      as (first & _ & Hfirst).
    destruct (IH _ Hfirst) as (rest & Hfinal).
    exists (first + rest). rewrite g_run_add. exact Hfinal.
Qed.

Theorem mma3_compile_output : forall p start final gc,
  sss_output (@mma_sss 3) (1, p) start final ->
  mma3_rel (length p) start gc ->
  exists fuel,
    g_terminal (mma3_compile p) (g_run fuel (mma3_compile p) gc) /\
    mma3_rel (length p) final (g_run fuel (mma3_compile p) gc).
Proof.
  intros p start [pc v] gc ((n & Hsteps) & Hout) Hrel.
  destruct (mma3_steps_sim p n start (pc, v) gc Hsteps Hrel)
    as (fuel & Hfinal).
  exists fuel. split; [|exact Hfinal].
  unfold g_terminal. rewrite mma3_compile_length.
  unfold mma3_rel in Hfinal. cbn in Hfinal.
  destruct Hfinal as (Hpc & _). rewrite Hpc.
  unfold out_code, code_start, code_end in Hout. cbn in Hout.
  unfold mma3_addr. destruct Hout as [Hlow|Hhigh].
  - assert (pc = 0) by lia. subst pc. cbn. lia.
  - destruct (pc =? 0) eqn:Hz; [lia|].
    apply Nat.eqb_neq in Hz. lia.
Qed.

Print Assumptions mma3_compile_wf.
Print Assumptions mma3_step_sim.
Print Assumptions mma3_compile_output.
