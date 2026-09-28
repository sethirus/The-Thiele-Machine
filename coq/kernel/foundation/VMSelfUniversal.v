(** VMSelfUniversal.v: B3, part 5: the stated guest fragment is universal.

    [cm2_compile] translates every CM2 program into a guest program of the
    fragment, five guest instructions per CM2 instruction.  Counter 0 is
    guest register 0, counter 1 is guest register 1, and register 3 is a
    scratch constant.  CM2 halting (explicit HALT or falloff) corresponds in
    both directions to guest termination with the same counters.  With the
    pinned MM2 bridge ([mm2_termination_guest_iff]) this places MM2 halting
    inside the self-interpreter's guest domain. *)

From Coq Require Import Arith Lia List.
Import ListNotations.
From Kernel Require Import VMState VMStep VMUnboundedStep.
From Kernel Require Import VMUnboundedCM2Interpreter VMUnboundedCM2InterpreterProof.
From Kernel Require Import VMUnboundedCM2Encoding VMUnboundedCM2Correctness.
From Kernel Require Import VMSelfGuest VMSelfRun.

Definition cm2_block (a len : nat) (i : CM2InstrU) : list GInstr :=
  match i with
  | CM2_Halt => [GJump (5 * len) 0; GHalt 0; GHalt 0; GHalt 0; GHalt 0]
  | CM2_Inc0 => [GLoadImm 3 1 0; GAdd 0 0 3 0; GJump (5 * S a) 0; GHalt 0; GHalt 0]
  | CM2_Inc1 => [GLoadImm 3 1 0; GAdd 1 1 3 0; GJump (5 * S a) 0; GHalt 0; GHalt 0]
  | CM2_DecJump0 t =>
      [GJnez 0 (5 * a + 2) 0; GJump (5 * S a) 0; GLoadImm 3 1 0; GSub 0 0 3 0; GJump (5 * t) 0]
  | CM2_DecJump1 t =>
      [GJnez 1 (5 * a + 2) 0; GJump (5 * S a) 0; GLoadImm 3 1 0; GSub 1 1 3 0; GJump (5 * t) 0]
  end.

Fixpoint compile_aux (a len : nat) (p : list CM2InstrU) : list GInstr :=
  match p with
  | [] => []
  | i :: r => cm2_block a len i ++ compile_aux (S a) len r
  end.

Definition cm2_compile (p : list CM2InstrU) : list GInstr :=
  compile_aux 0 (length p) p.

Lemma cm2_block_length : forall a len i, length (cm2_block a len i) = 5.
Proof. intros a len i; destruct i; reflexivity. Qed.

Lemma compile_aux_length : forall p a len, length (compile_aux a len p) = 5 * length p.
Proof.
  induction p as [|i r IH]; intros a len; cbn [compile_aux length]; [reflexivity|].
  rewrite app_length, cm2_block_length, IH. lia.
Qed.

Lemma cm2_compile_length : forall p, length (cm2_compile p) = 5 * length p.
Proof. intro p. apply compile_aux_length. Qed.

Lemma compile_aux_nth : forall p base len a i j,
  nth_error p a = Some i -> j < 5 ->
  nth_error (compile_aux base len p) (5 * a + j) = nth_error (cm2_block (base + a) len i) j.
Proof.
  induction p as [|x r IH]; intros base len a i j Ha Hj; [destruct a; discriminate|].
  destruct a as [|a]; cbn [nth_error] in Ha.
  - inversion Ha; subst x. cbn [compile_aux]. rewrite nth_error_app1
      by (rewrite cm2_block_length; lia).
    rewrite Nat.add_0_r. reflexivity.
  - cbn [compile_aux]. rewrite nth_error_app2 by (rewrite cm2_block_length; lia).
    rewrite cm2_block_length.
    replace (5 * S a + j - 5) with (5 * a + j) by lia.
    rewrite (IH (S base) len a i j Ha Hj).
    replace (S base + a) with (base + S a) by lia. reflexivity.
Qed.

Lemma cm2_compile_nth : forall p a i j,
  nth_error p a = Some i -> j < 5 ->
  nth_error (cm2_compile p) (5 * a + j) = nth_error (cm2_block a (length p) i) j.
Proof. intros. unfold cm2_compile. rewrite (compile_aux_nth p 0 _ a i j); auto. Qed.

Lemma compile_aux_wf : forall p a len, g_wf_program (compile_aux a len p).
Proof.
  unfold g_wf_program.
  induction p as [|i r IH]; intros a len; cbn [compile_aux]; [constructor|].
  apply Forall_app. split; [|apply IH].
  destruct i; cbn [cm2_block];
    repeat (apply Forall_cons; [unfold g_wf; cbn [g_dst g_rs1 g_rs2 g_cost]; lia|]);
    apply Forall_nil.
Qed.

Lemma cm2_compile_wf : forall p, g_wf_program (cm2_compile p).
Proof. intro p. apply compile_aux_wf. Qed.

(** * Relation between CM2 and guest configurations. *)

Definition crel (c : CM2ConfigU) (gc : GConf) : Prop :=
  gc.(gc_pc) = 5 * c.(cc_pc) /\ gc.(gc_g).(gr0) = c.(cc_c0) /\ gc.(gc_g).(gr1) = c.(cc_c1).

Lemma g_step_blk : forall p a i j c,
  nth_error p a = Some i -> j < 5 -> c.(gc_pc) = 5 * a + j ->
  g_step (cm2_compile p) c =
  match nth_error (cm2_block a (length p) i) j with
  | Some gi => let '(pc', mu', g') := g_next gi c.(gc_pc) c.(gc_mu) c.(gc_g) in
               {| gc_pc := pc'; gc_mu := mu'; gc_g := g' |}
  | None => c
  end.
Proof.
  intros p a i j c Ha Hj Hpc. unfold g_step. rewrite Hpc, (cm2_compile_nth p a i j Ha Hj).
  reflexivity.
Qed.

Lemma g_run_blk : forall n p a i j c,
  nth_error p a = Some i -> j < 5 -> c.(gc_pc) = 5 * a + j ->
  g_run (S n) (cm2_compile p) c =
  g_run n (cm2_compile p)
    (match nth_error (cm2_block a (length p) i) j with
     | Some gi => let '(pc', mu', g') := g_next gi c.(gc_pc) c.(gc_mu) c.(gc_g) in
                  {| gc_pc := pc'; gc_mu := mu'; gc_g := g' |}
     | None => c
     end).
Proof. intros. cbn [g_run]. f_equal. apply g_step_blk; assumption. Qed.

Ltac blk_step Ha j :=
  rewrite (g_run_blk _ _ _ _ j _ Ha) by (cbn [gc_pc]; lia);
  cbn [cm2_block nth_error g_next gc_pc gc_mu gc_g g_set g_get gr0 gr1 gr2 gr3].

(** One CM2 step is a finite, positive guest run. *)
Lemma cm2_step_sim : forall p c i c1 gc,
  nth_error p c.(cc_pc) = Some i ->
  cm2_step_instr i c = Some c1 ->
  crel c gc ->
  exists k, 0 < k /\ crel c1 (g_run k (cm2_compile p) gc).
Proof.
  intros p [pc c0 c1v] i c1 [gpc mu [x0 x1 x2 x3]] Hi Hs (Hp & H0 & H1).
  cbn [cc_pc cc_c0 cc_c1 gc_pc gc_g gr0 gr1] in *. subst gpc x0 x1.
  replace (5 * pc) with (5 * pc + 0) by lia.
  destruct i; cbn [cm2_step_instr cc_c0 cc_c1 cc_pc] in Hs; try discriminate.
  - inversion Hs; subst c1. exists 3. split; [lia|].
    blk_step Hi 0. blk_step Hi 1. blk_step Hi 2. cbn [g_run].
    unfold crel, u_add; cbn; lia.
  - inversion Hs; subst c1. exists 3. split; [lia|].
    blk_step Hi 0. blk_step Hi 1. blk_step Hi 2. cbn [g_run].
    unfold crel, u_add; cbn; lia.
  - destruct (Nat.eqb c0 0) eqn:Ez; inversion Hs; subst c1.
    + apply Nat.eqb_eq in Ez. subst c0. exists 2. split; [lia|].
      blk_step Hi 0. cbn [Nat.eqb]. blk_step Hi 1. cbn [g_run].
      unfold crel; cbn; lia.
    + apply Nat.eqb_neq in Ez. exists 4. split; [lia|].
      blk_step Hi 0. rewrite (proj2 (Nat.eqb_neq c0 0) Ez).
      blk_step Hi 2. blk_step Hi 3. blk_step Hi 4. cbn [g_run].
      unfold crel, u_sub; cbn; lia.
  - destruct (Nat.eqb c1v 0) eqn:Ez; inversion Hs; subst c1.
    + apply Nat.eqb_eq in Ez. subst c1v. exists 2. split; [lia|].
      blk_step Hi 0. cbn [Nat.eqb]. blk_step Hi 1. cbn [g_run].
      unfold crel; cbn; lia.
    + apply Nat.eqb_neq in Ez. exists 4. split; [lia|].
      blk_step Hi 0. rewrite (proj2 (Nat.eqb_neq c1v 0) Ez).
      blk_step Hi 2. blk_step Hi 3. blk_step Hi 4. cbn [g_run].
      unfold crel, u_sub; cbn; lia.
Qed.

(** * Halting correspondence. *)

Lemma CM2InstrU_eq_halt : forall i, {i = CM2_Halt} + {i <> CM2_Halt}.
Proof. intro i; destruct i; [left; reflexivity|right; discriminate..]. Qed.

Definition ccnt (c : CM2ConfigU) (gc : GConf) : Prop :=
  gc.(gc_g).(gr0) = c.(cc_c0) /\ gc.(gc_g).(gr1) = c.(cc_c1).

Lemma cm2_run_sim : forall p c final gc,
  cm2_run p c final -> crel c gc ->
  exists n, crel final (g_run n (cm2_compile p) gc).
Proof.
  intros p c final gc Hr. revert gc.
  induction Hr as [c|c i c1 c2 Hi Hs Hr IH]; intros gc Hc.
  - exists 0. exact Hc.
  - destruct (cm2_step_sim p c i c1 gc Hi Hs Hc) as (k & _ & Hk).
    destruct (IH _ Hk) as (n & Hn).
    exists (k + n). rewrite g_run_add. exact Hn.
Qed.

Lemma cm2_nonhalt_steps : forall i c,
  i <> CM2_Halt -> exists c1, cm2_step_instr i c = Some c1.
Proof.
  intros i c Hi. destruct i; cbn [cm2_step_instr]; try (eexists; reflexivity).
  - contradiction.
  - destruct (Nat.eqb (cc_c0 c) 0); eexists; reflexivity.
  - destruct (Nat.eqb (cc_c1 c) 0); eexists; reflexivity.
Qed.

Lemma cm2_halts_prepend : forall p c i c1 final,
  nth_error p c.(cc_pc) = Some i -> cm2_step_instr i c = Some c1 ->
  cm2_halts p c1 final -> cm2_halts p c final.
Proof.
  intros p c i c1 final Hi Hs Hh. destruct Hh as [f Hr Hf|f Hr Hf].
  - apply cm2_halts_explicit; [econstructor; eassumption|exact Hf].
  - apply cm2_halts_falloff; [econstructor; eassumption|exact Hf].
Qed.

(** Completeness: a halting CM2 run gives a terminating guest run with the
    same final counters. *)
Theorem cm2_compile_complete : forall p c final gc,
  cm2_halts p c final -> crel c gc ->
  exists n, g_terminal (cm2_compile p) (g_run n (cm2_compile p) gc) /\
            ccnt final (g_run n (cm2_compile p) gc).
Proof.
  intros p c final gc Hh Hc.
  destruct Hh as [f Hr Hf|f Hr Hf];
    destruct (cm2_run_sim p c f gc Hr Hc) as (n & Hn).
  - exists (n + 1). rewrite g_run_add.
    destruct (g_run n (cm2_compile p) gc) as [gpc mu [x0 x1 x2 x3]] eqn:E.
    destruct Hn as (Hp & H0 & H1). cbn [gc_pc gc_g gr0 gr1] in Hp, H0, H1.
    replace gpc with (5 * cc_pc f + 0) in * by lia.
    rewrite (g_run_blk 0 p (cc_pc f) CM2_Halt 0 _ Hf) by (cbn; lia).
    cbn. unfold g_terminal, ccnt. rewrite cm2_compile_length. cbn. lia.
  - exists n. destruct Hn as (Hp & H0 & H1). split.
    + unfold g_terminal. rewrite cm2_compile_length, Hp.
      apply nth_error_None in Hf. lia.
    + split; assumption.
Qed.

(** Soundness: a terminating guest run decodes an actual CM2 halting run. *)
Theorem cm2_compile_sound : forall p n c gc,
  crel c gc ->
  g_terminal (cm2_compile p) (g_run n (cm2_compile p) gc) ->
  exists final, cm2_halts p c final /\ ccnt final (g_run n (cm2_compile p) gc).
Proof.
  intros p n. induction n as [n IH] using lt_wf_ind. intros c gc Hc Ht.
  unfold g_terminal in Ht. rewrite cm2_compile_length in Ht.
  destruct (nth_error p (cc_pc c)) as [i|] eqn:Ei.
  - assert (Hlt : cc_pc c < length p)
      by (apply nth_error_Some; rewrite Ei; discriminate).
    destruct (CM2InstrU_eq_halt i) as [->|Hnh].
    + exists c. split; [apply cm2_halts_explicit; [constructor|exact Ei]|].
      destruct n as [|m].
      * exfalso. cbn [g_run] in Ht. destruct Hc as (Hp & _). lia.
      * destruct gc as [gpc mu [x0 x1 x2 x3]]. destruct Hc as (Hp & H0 & H1).
        cbn [gc_pc gc_g gr0 gr1] in Hp, H0, H1.
        replace gpc with (5 * cc_pc c + 0) in * by lia.
        rewrite (g_run_blk m p (cc_pc c) CM2_Halt 0 _ Ei) in Ht |- * by (cbn; lia).
        cbn [cm2_block nth_error g_next gc_pc gc_mu gc_g] in Ht |- *.
        rewrite g_run_terminal by (unfold g_terminal; cbn; rewrite cm2_compile_length; lia).
        unfold ccnt; cbn; split; assumption.
    + destruct (cm2_nonhalt_steps i c Hnh) as (c1 & Hs).
      destruct (cm2_step_sim p c i c1 gc Ei Hs Hc) as (k & Hk & Hc1).
      destruct (le_lt_dec k n) as [Hle|Hlt'].
      * replace n with (k + (n - k)) in Ht |- * by lia.
        rewrite g_run_add in Ht |- *.
        assert (Ht' : g_terminal (cm2_compile p) (g_run (n - k) (cm2_compile p) (g_run k (cm2_compile p) gc)))
          by (unfold g_terminal; rewrite cm2_compile_length; exact Ht).
        destruct (IH (n - k) ltac:(lia) c1 _ Hc1 Ht') as (final & Hh & Hcnt).
        exists final. split; [eapply cm2_halts_prepend; eassumption|exact Hcnt].
      * assert (Htn : g_terminal (cm2_compile p) (g_run n (cm2_compile p) gc))
          by (unfold g_terminal; rewrite cm2_compile_length; exact Ht).
        assert (Heq : g_run k (cm2_compile p) gc = g_run n (cm2_compile p) gc).
        { replace k with (n + (k - n)) by lia. rewrite g_run_add.
          apply g_run_terminal, Htn. }
        rewrite Heq in Hc1. destruct Hc1 as (Hp1 & H01 & H11).
        exists c1. split.
        -- eapply cm2_halts_prepend; [exact Ei|exact Hs|].
           apply cm2_halts_falloff; [constructor|].
           apply nth_error_None. lia.
        -- split; assumption.
  - exists c. split; [apply cm2_halts_falloff; [constructor|exact Ei]|].
    rewrite g_run_terminal.
    + destruct Hc as (_ & H0 & H1). split; assumption.
    + unfold g_terminal. rewrite cm2_compile_length. destruct Hc as (Hp & _).
      apply nth_error_None in Ei. lia.
Qed.
