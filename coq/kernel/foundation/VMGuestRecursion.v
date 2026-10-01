(** Internal foundations for Kleene recursion in the four-register guest.

    The earlier [g_specialize] overwrites the external input.  The prefix
    below implements genuine binary specialization: a program expecting
    [pair x y] receives the fixed first argument [x] and retains its runtime
    argument [y].  All instructions use registers 0 through 2 and cost zero. *)

From Coq Require Import Arith Lia List.
Import ListNotations.
From Kernel Require Import VMUnboundedStep VMSelfGuest VMSelfRun VMSelfRice
  VMDynamicEval VMRecursionTarget.

Definition g_pair (x y : nat) : nat := (2 * y + 1) * 2 ^ x.

Definition g_pair_prefix (x tail : nat) : list GInstr :=
  [ GLoadImm 2 1 0;
    GAdd 0 0 0 0;
    GAdd 0 0 2 0;
    GLoadImm 1 x 0;
    GJnez 1 7 0;
    GLoadImm 2 0 0;
    GJump tail 0;
    GAdd 0 0 0 0;
    GSub 1 1 2 0;
    GJump 4 0 ].

Definition g_pair_specialize (p : list GInstr) (x : nat) : list GInstr :=
  g_pair_prefix x 10 ++ reloc 10 p.

(** Administrative computations used by the diagonal program must not leak
    their ledger into the program whose behaviour is being reproduced. *)
Definition g_zero_instr (i : GInstr) : GInstr :=
  match i with
  | GHalt _ => GHalt 0
  | GLoadImm d n _ => GLoadImm d n 0
  | GXfer d s _ => GXfer d s 0
  | GAdd d a b _ => GAdd d a b 0
  | GSub d a b _ => GSub d a b 0
  | GMul d a b _ => GMul d a b 0
  | GAnd d a b _ => GAnd d a b 0
  | GOr d a b _ => GOr d a b 0
  | GShl d a b _ => GShl d a b 0
  | GShr d a b _ => GShr d a b 0
  | GJump t _ => GJump t 0
  | GJnez r t _ => GJnez r t 0
  end.

Definition g_zero_program (p : list GInstr) : list GInstr :=
  map g_zero_instr p.

Definition g_zero_conf (c : GConf) : GConf :=
  {| gc_pc := gc_pc c; gc_mu := 0; gc_g := gc_g c |}.

Lemma g_zero_instr_wf : forall i, g_wf i -> g_wf (g_zero_instr i).
Proof.
  intros i H. destruct i; unfold g_wf in *;
    cbn [g_zero_instr g_dst g_rs1 g_rs2 g_cost] in *; lia.
Qed.

Lemma g_zero_program_wf : forall p,
  g_wf_program p -> g_wf_program (g_zero_program p).
Proof.
  intros p Hp. induction Hp; constructor; auto using g_zero_instr_wf.
Qed.

Lemma g_zero_step : forall p c,
  g_step (g_zero_program p) (g_zero_conf c) =
  g_zero_conf (g_step p c).
Proof.
  intros p [pc mu g]. unfold g_step, g_zero_conf, g_zero_program.
  cbn [gc_pc gc_mu gc_g]. rewrite nth_error_map.
  destruct (nth_error p pc) as [i|] eqn:Hi; cbn [option_map]; [|reflexivity].
  destruct i; cbn [g_zero_instr g_next g_cost gc_pc gc_mu gc_g];
    reflexivity.
Qed.

Lemma g_zero_run : forall fuel p c,
  g_run fuel (g_zero_program p) (g_zero_conf c) =
  g_zero_conf (g_run fuel p c).
Proof.
  induction fuel as [|fuel IH]; intros p c; [reflexivity|].
  cbn [g_run]. rewrite g_zero_step, IH. reflexivity.
Qed.

Lemma g_zero_terminal : forall p c,
  g_terminal (g_zero_program p) (g_zero_conf c) <-> g_terminal p c.
Proof.
  intros. unfold g_terminal, g_zero_program, g_zero_conf.
  rewrite map_length. reflexivity.
Qed.

Theorem g_zero_behaviour : forall p x g,
  g_beh (g_zero_program p) x g 0 <-> exists mu, g_beh p x g mu.
Proof.
  intros p x g. split.
  - intros (n & Hterm & Hregs & Hmu).
    exists (gc_mu (g_run n p (g_input x))), n.
    pose proof (g_zero_run n p (g_input x)) as Hrun.
    change (g_run n (g_zero_program p) (g_input x) =
      g_zero_conf (g_run n p (g_input x))) in Hrun.
    rewrite Hrun in Hterm, Hregs, Hmu.
    apply (proj1 (g_zero_terminal p (g_run n p (g_input x)))) in Hterm.
    unfold g_zero_conf in *. cbn [gc_pc gc_mu gc_g] in *.
    split; [exact Hterm|]. split; [exact Hregs|reflexivity].
  - intros (mu & n & Hterm & Hregs & Hmu).
    exists n. pose proof (g_zero_run n p (g_input x)) as Hrun.
    change (g_run n (g_zero_program p) (g_input x) =
      g_zero_conf (g_run n p (g_input x))) in Hrun.
    rewrite Hrun.
    split.
    + apply (proj2 (g_zero_terminal p (g_run n p (g_input x)))). exact Hterm.
    + unfold g_zero_conf. cbn [gc_pc gc_mu gc_g].
      split; [exact Hregs|reflexivity].
Qed.

Lemma g_pair_prefix_length : forall x tail,
  length (g_pair_prefix x tail) = 10.
Proof. reflexivity. Qed.

Lemma g_pair_prefix_wf : forall x tail,
  g_wf_program (g_pair_prefix x tail).
Proof.
  intros. unfold g_wf_program, g_pair_prefix.
  repeat (constructor; [unfold g_wf; cbn [g_dst g_rs1 g_rs2 g_cost]; lia|]).
  constructor.
Qed.

Lemma g_pair_specialize_wf : forall p x,
  g_wf_program p -> g_wf_program (g_pair_specialize p x).
Proof.
  intros p x Hp. unfold g_pair_specialize, g_wf_program.
  apply Forall_app. split; [apply g_pair_prefix_wf|apply reloc_wf; exact Hp].
Qed.

Lemma g_pair_specialize_nth_prefix : forall p x i,
  i < 10 ->
  nth_error (g_pair_specialize p x) i = nth_error (g_pair_prefix x 10) i.
Proof.
  intros p x i Hi. unfold g_pair_specialize.
  apply nth_error_app1. rewrite g_pair_prefix_length. exact Hi.
Qed.

Lemma g_pair_step_0 : forall p x y,
  g_step (g_pair_specialize p x) (g_input y) =
  {| gc_pc := 1; gc_mu := 0;
     gc_g := {| gr0 := y; gr1 := 0; gr2 := 1; gr3 := 0 |} |}.
Proof.
  intros. unfold g_step, g_input. cbn [gc_pc].
  rewrite g_pair_specialize_nth_prefix by lia.
  reflexivity.
Qed.

Lemma g_pair_step_1 : forall p x y,
  g_step (g_pair_specialize p x)
    {| gc_pc := 1; gc_mu := 0;
       gc_g := {| gr0 := y; gr1 := 0; gr2 := 1; gr3 := 0 |} |} =
  {| gc_pc := 2; gc_mu := 0;
     gc_g := {| gr0 := 2 * y; gr1 := 0; gr2 := 1; gr3 := 0 |} |}.
Proof.
  intros. unfold g_step. cbn [gc_pc].
  rewrite g_pair_specialize_nth_prefix by lia.
  cbn [g_pair_prefix nth_error g_next g_cost g_get g_set gc_mu gc_g
    gr0 gr1 gr2 gr3]. unfold u_add.
  replace (y + y) with (2 * y) by lia. reflexivity.
Qed.

Lemma g_pair_step_2 : forall p x y,
  g_step (g_pair_specialize p x)
    {| gc_pc := 2; gc_mu := 0;
       gc_g := {| gr0 := 2 * y; gr1 := 0; gr2 := 1; gr3 := 0 |} |} =
  {| gc_pc := 3; gc_mu := 0;
     gc_g := {| gr0 := 2 * y + 1; gr1 := 0; gr2 := 1; gr3 := 0 |} |}.
Proof.
  intros. unfold g_step. cbn [gc_pc].
  rewrite g_pair_specialize_nth_prefix by lia.
  cbn [g_pair_prefix nth_error g_next g_cost g_get g_set gc_mu gc_g
    gr0 gr1 gr2 gr3]. unfold u_add. reflexivity.
Qed.

Lemma g_pair_step_3 : forall p x y,
  g_step (g_pair_specialize p x)
    {| gc_pc := 3; gc_mu := 0;
       gc_g := {| gr0 := 2 * y + 1; gr1 := 0; gr2 := 1; gr3 := 0 |} |} =
  {| gc_pc := 4; gc_mu := 0;
     gc_g := {| gr0 := 2 * y + 1; gr1 := x; gr2 := 1; gr3 := 0 |} |}.
Proof.
  intros. unfold g_step. cbn [gc_pc].
  rewrite g_pair_specialize_nth_prefix by lia.
  reflexivity.
Qed.

Lemma g_pair_setup : forall p x y,
  g_run 4 (g_pair_specialize p x) (g_input y) =
  {| gc_pc := 4; gc_mu := 0;
     gc_g := {| gr0 := 2 * y + 1; gr1 := x; gr2 := 1; gr3 := 0 |} |}.
Proof.
  intros. cbn [g_run].
  rewrite g_pair_step_0, g_pair_step_1, g_pair_step_2, g_pair_step_3.
  reflexivity.
Qed.

Lemma g_pair_step_4_nonzero : forall p x k v,
  g_step (g_pair_specialize p x)
    {| gc_pc := 4; gc_mu := 0;
       gc_g := {| gr0 := v; gr1 := S k; gr2 := 1; gr3 := 0 |} |} =
  {| gc_pc := 7; gc_mu := 0;
     gc_g := {| gr0 := v; gr1 := S k; gr2 := 1; gr3 := 0 |} |}.
Proof.
  intros. unfold g_step. cbn [gc_pc].
  rewrite g_pair_specialize_nth_prefix by lia.
  cbn [g_pair_prefix nth_error g_next g_cost g_get g_set gc_mu gc_g
    gr0 gr1 gr2 gr3]. reflexivity.
Qed.

Lemma g_pair_step_7 : forall p x k v,
  g_step (g_pair_specialize p x)
    {| gc_pc := 7; gc_mu := 0;
       gc_g := {| gr0 := v; gr1 := S k; gr2 := 1; gr3 := 0 |} |} =
  {| gc_pc := 8; gc_mu := 0;
     gc_g := {| gr0 := 2 * v; gr1 := S k; gr2 := 1; gr3 := 0 |} |}.
Proof.
  intros. unfold g_step. cbn [gc_pc].
  rewrite g_pair_specialize_nth_prefix by lia.
  cbn [g_pair_prefix nth_error g_next g_cost g_get g_set gc_mu gc_g
    gr0 gr1 gr2 gr3 u_add].
  unfold u_add. replace (v + v) with (2 * v) by lia. reflexivity.
Qed.

Lemma g_pair_step_8 : forall p x k v,
  g_step (g_pair_specialize p x)
    {| gc_pc := 8; gc_mu := 0;
       gc_g := {| gr0 := v; gr1 := S k; gr2 := 1; gr3 := 0 |} |} =
  {| gc_pc := 9; gc_mu := 0;
     gc_g := {| gr0 := v; gr1 := k; gr2 := 1; gr3 := 0 |} |}.
Proof.
  intros. unfold g_step. cbn [gc_pc].
  rewrite g_pair_specialize_nth_prefix by lia.
  cbn [g_pair_prefix nth_error g_next g_cost g_get g_set gc_mu gc_g
    gr0 gr1 gr2 gr3].
  unfold u_sub. replace (S k - 1) with k by lia. reflexivity.
Qed.

Lemma g_pair_step_9 : forall p x k v,
  g_step (g_pair_specialize p x)
    {| gc_pc := 9; gc_mu := 0;
       gc_g := {| gr0 := v; gr1 := k; gr2 := 1; gr3 := 0 |} |} =
  {| gc_pc := 4; gc_mu := 0;
     gc_g := {| gr0 := v; gr1 := k; gr2 := 1; gr3 := 0 |} |}.
Proof.
  intros. unfold g_step. cbn [gc_pc].
  rewrite g_pair_specialize_nth_prefix by lia.
  cbn [g_pair_prefix nth_error g_next g_cost g_get g_set gc_mu gc_g
    gr0 gr1 gr2 gr3]. reflexivity.
Qed.

Lemma g_pair_loop_step : forall p x k v,
  g_run 4 (g_pair_specialize p x)
    {| gc_pc := 4; gc_mu := 0;
       gc_g := {| gr0 := v; gr1 := S k; gr2 := 1; gr3 := 0 |} |} =
  {| gc_pc := 4; gc_mu := 0;
     gc_g := {| gr0 := 2 * v; gr1 := k; gr2 := 1; gr3 := 0 |} |}.
Proof.
  intros. cbn [g_run].
  rewrite g_pair_step_4_nonzero, g_pair_step_7, g_pair_step_8,
    g_pair_step_9. reflexivity.
Qed.

Lemma g_pair_loop : forall p x k v,
  g_run (4 * k + 3) (g_pair_specialize p x)
    {| gc_pc := 4; gc_mu := 0;
       gc_g := {| gr0 := v; gr1 := k; gr2 := 1; gr3 := 0 |} |} =
  {| gc_pc := 10; gc_mu := 0;
     gc_g := {| gr0 := v * 2 ^ k; gr1 := 0; gr2 := 0; gr3 := 0 |} |}.
Proof.
  intros p x k. induction k as [|k IH]; intro v.
  - cbn [g_run]. unfold g_step.
    repeat rewrite g_pair_specialize_nth_prefix by lia.
    cbn [g_pair_prefix nth_error g_next g_cost g_get g_set u_add u_sub].
    rewrite Nat.mul_1_r. reflexivity.
  - replace (4 * S k + 3) with (4 + (4 * k + 3)) by lia.
    rewrite g_run_add.
    rewrite g_pair_loop_step, IH. f_equal. cbn. f_equal. ring.
Qed.

Lemma g_pair_prefix_run : forall p x y,
  g_run (4 * x + 7) (g_pair_specialize p x) (g_input y) =
  rconf 10 (length p) (g_input (g_pair x y)).
Proof.
  intros p x y.
  replace (4 * x + 7) with (4 + (4 * x + 3)) by lia.
  rewrite g_run_add.
  rewrite g_pair_setup.
  rewrite g_pair_loop.
  unfold rconf, rpc, g_pair, g_input. cbn [gc_pc gc_mu gc_g].
  destruct (0 <? length p) eqn:Hlen.
  - reflexivity.
  - apply Nat.ltb_ge in Hlen.
    assert (length p = 0) by lia. rewrite H. reflexivity.
Qed.

Lemma g_pair_specialize_embeds : forall p x,
  embeds (g_pair_specialize p x) 10 p.
Proof.
  intros p x i Hi. unfold embeds, g_pair_specialize.
  rewrite nth_error_app2 by (rewrite g_pair_prefix_length; lia).
  rewrite g_pair_prefix_length.
  replace (10 + i - 10) with i by lia. reflexivity.
Qed.

Lemma g_pair_specialize_length : forall p x,
  length (g_pair_specialize p x) = 10 + length p.
Proof.
  intros. unfold g_pair_specialize. rewrite app_length, g_pair_prefix_length,
    reloc_length. reflexivity.
Qed.

Theorem g_pair_smn : forall p x y g mu,
  g_beh (g_pair_specialize p x) y g mu <-> g_beh p (g_pair x y) g mu.
Proof.
  intros p x y g mu.
  eapply tail_beh_from with (K := 10) (N0 := 4 * x + 7).
  - apply g_pair_specialize_embeds.
  - apply g_pair_specialize_length.
  - apply g_pair_prefix_run.
Qed.

(** * The internal recursion theorem

    The diagonal program is [g_pair_specialize e (guest_program_code e)] where
    [e] is the guest pipeline for the Minsky machine of the evaluator
    relation [RD D]. On input [y] it pairs its own code with [y], runs the
    evaluator inside the guest, and ends with the registers and ledger of
    [F] applied to itself on [y], or never halts when that program never
    halts. *)

From Coq Require Import Lia.
From Undecidability.MinskyMachines Require Import MMA.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.Shared.Libs.DLW.Code Require Import sss.
From Kernel Require Import VMGuestEvalNat VMGuestEvalTuple VMGuestExactEpilogue.
From Kernel Require Import VMGuestMMAInit VMGuestMMAPipeline VMGuestEvalL.

Lemma g_pair_npair : forall x y, g_pair x y = npair x y.
Proof. intros x y. unfold g_pair, npair. rewrite VMGuestEvalNat.pow2_spec. reflexivity. Qed.

Lemma sp_g_pair_specialize : forall p x, sp p x = g_pair_specialize p x.
Proof. reflexivity. Qed.

Theorem vm_guest_recursion_theorem_closed : vm_guest_recursion_theorem.
Proof.
  intros F D HF HD.
  destruct (RD_MMA D) as (n & P & HP).
  set (e := g_pipeline n P).
  assert (He : g_wf_program e) by apply g_pipeline_wf.
  set (c := guest_program_code e).
  exists (g_pair_specialize e c). split.
  - apply g_pair_specialize_wf. exact He.
  - intros y g mu. rewrite g_pair_smn.
    set (z := g_pair c y).
    assert (Hz : z = npair (genc e) y) by (subst z c; rewrite g_pair_npair, genc_code; reflexivity).
    (* the Minsky program's outputs on z are exactly the values of RD D at [z] *)
    assert (Hout : forall m, RD D (Vector.cons nat z 0 (Vector.nil nat)) m <->
              exists pc final,
                sss_output (@mma_sss (S (S n))) (1, P) (1, mma_init_start z n) (pc, final) /\
                vec_pos final pos0 = m).
    { intro m. rewrite (HP (Vector.cons nat z 0 (Vector.nil nat)) m). split.
      - intros (pc & v' & Hrun). exists pc, (Vector.cons nat m _ v'). split; [exact Hrun | reflexivity].
      - intros (pc & final & Hrun & Hm). exists pc, (Vector.tl final).
        revert Hrun Hm. apply (Vector.caseS' final). intros h t Hrun Hm.
        cbn in Hm. subst m. exact Hrun. }
    (* RD D at [z] is the evaluator relation *)
    assert (Hsem : forall m, RD D (Vector.cons nat z 0 (Vector.nil nat)) m <->
              exists g' mu', m = g_out_pack g' mu' /\ g_beh (F (sp e (genc e))) y g' mu').
    { intro m. unfold RD. cbn [Vector.hd]. rewrite <- (@hfun_sem g_out_pack D F e y m HD He).
      rewrite Hz. split; intros [k Hk]; exists k; [rewrite <- thfun_spec | rewrite thfun_spec]; exact Hk. }
    unfold e at 1. rewrite (@g_pipeline_beh_pack n P z g mu).
    + rewrite <- (Hout (g_out_pack g mu)), Hsem.
      rewrite genc_code. fold c. rewrite sp_g_pair_specialize. split.
      * intros (g' & mu' & Hpack & Hb).
        destruct (@g_out_pack_inj _ _ _ _ Hpack) as [-> ->]. exact Hb.
      * intro Hb. exists g, mu. split; [reflexivity | exact Hb].
    + intros pc final Hrun.
      assert (Hr : RD D (Vector.cons nat z 0 (Vector.nil nat)) (vec_pos final pos0))
        by (apply Hout; exists pc, final; split; [exact Hrun | reflexivity]).
      apply Hsem in Hr. destruct Hr as (g' & mu' & Hm & _). exists g', mu'. exact Hm.
Qed.


Print Assumptions g_pair_smn.
Print Assumptions vm_guest_recursion_theorem_closed.
