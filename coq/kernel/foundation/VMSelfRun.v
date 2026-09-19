(** VMSelfRun.v: B3, part 4: whole-run correctness of the self-interpreter.

    Guest semantics.  A guest configuration is (pc, ledger, registers 0..3).
    [g_run] iterates [g_next] on the instruction at pc and stops once pc is
    outside the program; [g_run_is_run_vm_u] proves this is exactly the VM's
    own [run_vm_u] on [g_program p].  Guest termination is the VM's own
    termination condition: no instruction at pc.

    Host observation.  The host result is read only from an actual host run
    that reaches address [U_END] (the host's own termination condition):
    status R9, guest registers R0..R3, ledger R11 and guest pc R12. *)

From Coq Require Import Arith Lia List.
From Coq Require Import NArith.NArith.
Import ListNotations.
From Kernel Require Import VMState VMStep VMUnboundedStep.
From Kernel Require Import VMUnboundedInterpreterCompose VMUnboundedInterpreterSlots.
From Kernel Require Import VMSelfGuest VMSelfProgram VMSelfCorrect.

(** * 1. Guest configurations and runs. *)

Record GConf := { gc_pc : nat; gc_mu : nat; gc_g : GRegs }.

Definition g_step (p : list GInstr) (c : GConf) : GConf :=
  match nth_error p c.(gc_pc) with
  | Some i =>
      let '(pc', mu', g') := g_next i c.(gc_pc) c.(gc_mu) c.(gc_g) in
      {| gc_pc := pc'; gc_mu := mu'; gc_g := g' |}
  | None => c
  end.

Fixpoint g_run (n : nat) (p : list GInstr) (c : GConf) : GConf :=
  match n with
  | 0 => c
  | S n' => g_run n' p (g_step p c)
  end.

Definition g_terminal (p : list GInstr) (c : GConf) : Prop :=
  length p <= c.(gc_pc).

Definition gc_state (amb : VMState) (tl : list nat) (c : GConf) : VMState :=
  g_st amb c.(gc_pc) c.(gc_mu) c.(gc_g) tl.

Lemma g_run_terminal_aux : forall n p c,
  nth_error p (gc_pc c) = None -> g_run n p c = c.
Proof.
  induction n as [|n IH]; intros p c H; [reflexivity|].
  cbn [g_run]. replace (g_step p c) with c by (unfold g_step; rewrite H; reflexivity).
  apply IH, H.
Qed.

Theorem g_run_is_run_vm_u : forall p amb tl n c,
  g_wf_program p ->
  run_vm_u n (g_program p) (gc_state amb tl c) = gc_state amb tl (g_run n p c).
Proof.
  intros p amb tl n. induction n as [|n IH]; intros c Hwf; [reflexivity|].
  change (run_vm_u (S n) (g_program p) (gc_state amb tl c)) with
    (match nth_error (g_program p) (gc_pc c) with
     | Some instr => run_vm_u n (g_program p) (vm_apply_u (gc_state amb tl c) instr)
     | None => gc_state amb tl c
     end).
  cbn [g_run]. unfold g_program. rewrite nth_error_map.
  unfold g_step. destruct (nth_error p (gc_pc c)) as [i|] eqn:Ei; cbn [option_map].
  - assert (Hwi : g_wf i) by (eapply Forall_forall; [exact Hwf|eapply nth_error_In; exact Ei]).
    pose proof (g_step_is_vm_apply_u amb (gc_pc c) (gc_mu c) (gc_g c) tl i Hwi) as Hs.
    destruct (g_next i (gc_pc c) (gc_mu c) (gc_g c)) as [[pc' mu'] g'] eqn:En.
    change (gc_state amb tl c) with (g_st amb (gc_pc c) (gc_mu c) (gc_g c) tl).
    rewrite Hs.
    exact (IH {| gc_pc := pc'; gc_mu := mu'; gc_g := g' |} Hwf).
  - symmetry. rewrite g_run_terminal_aux by exact Ei. reflexivity.
Qed.

Lemma g_step_terminal : forall p c, g_terminal p c -> g_step p c = c.
Proof.
  intros p c Ht. unfold g_step. apply nth_error_None in Ht. rewrite Ht. reflexivity.
Qed.

Lemma g_run_terminal : forall n p c, g_terminal p c -> g_run n p c = c.
Proof.
  induction n as [|n IH]; intros p c Ht; [reflexivity|].
  cbn [g_run]. rewrite g_step_terminal by exact Ht. apply IH, Ht.
Qed.

Lemma g_run_add : forall a b p c, g_run (a + b) p c = g_run b p (g_run a p c).
Proof. induction a as [|a IH]; intros b p c; [reflexivity|]. cbn. apply IH. Qed.

(** * 2. The host termination block. *)

Definition h_done (amb : VMState) (hmu code width pc mu : nat) (g : GRegs)
    (s : VMState) : Prop :=
  exists z4 z5 z6 z7 z8 z10 z15,
    s = hst amb hmu U_END [g.(gr0); g.(gr1); g.(gr2); g.(gr3);
                           z4; z5; z6; z7; z8; 1; z10; mu; pc; width; code; z15].

Definition H_TERM : nat := 7 + (4 + (3 + (4 + (3 + (2 + 3))))).

Lemma h_terminal_run : forall amb hmu code width pc mu g z,
  g_fetch code width pc = 0 ->
  h_done amb hmu code width pc mu g
    (run_vm_u H_TERM U (hb amb hmu code width pc mu g z)).
Proof.
  intros amb hmu code width pc mu [g0 g1 g2 g3] [z4 z5 z6 z7 z8 z10 z15] Hf.
  unfold H_TERM, hb; cbn [gr0 gr1 gr2 gr3 hs4 hs5 hs6 hs7 hs8 hs10 hs15].
  rewrite run_vm_u_split, ph_fetch, Hf.
  rewrite run_vm_u_split, ph_rs1_index.
  change (u_and (u_shr 0 6) 3) with 0.
  rewrite run_vm_u_split, (ph_read_rs1 _ _ _ _ _ _ _ _ _ 0) by lia.
  rewrite run_vm_u_split, ph_rs2_index.
  change (u_and (u_shr 0 8) 3) with 0.
  rewrite run_vm_u_split, (ph_read_rs2 _ _ _ _ _ _ _ _ _ 0) by lia.
  rewrite run_vm_u_split, ph_opcode.
  change (u_and 0 15) with 0.
  rewrite ph_op_sentinel.
  do 7 eexists. reflexivity.
Qed.

(** * 3. Host termination is stable, and a boundary is not terminal. *)

Lemma U_nth_END : nth_error U U_END = None.
Proof. reflexivity. Qed.

Lemma h_terminal_stable : forall k m s,
  (run_vm_u k U s).(vm_pc) = U_END ->
  run_vm_u (k + m) U s = run_vm_u k U s.
Proof.
  intros k m s H. rewrite run_vm_u_split.
  apply run_vm_u_halted_stable. rewrite H. exact U_nth_END.
Qed.

Lemma hb_pc : forall amb hmu code width pc mu g z,
  (hb amb hmu code width pc mu g z).(vm_pc) = 0.
Proof. reflexivity. Qed.

(** * 4. Host simulation of guest runs.

    [p] is a well-formed guest program packed at a width [w] that fits every
    word.  The guest program and input are data in R12..R14 and R0..R3; the
    host program is always [U]. *)

Section HostRuns.

Variables (amb : VMState) (hmu w : nat) (p : list GInstr).
Hypothesis Hwf : g_wf_program p.
Hypothesis Hfit : g_fits w p.

Definition code := g_code w p.

Definition hbc (c : GConf) (z : HScratch) : VMState :=
  hb amb hmu code w c.(gc_pc) c.(gc_mu) c.(gc_g) z.

Lemma h_block : forall c z, ~ g_terminal p c ->
  exists k z', 0 < k /\ run_vm_u k U (hbc c z) = hbc (g_step p c) z'.
Proof.
  intros [pc mu g] z Hnt. unfold g_terminal in Hnt; cbn [gc_pc] in Hnt.
  destruct (nth_error p pc) as [i|] eqn:Ei.
  2: { apply nth_error_None in Ei. lia. }
  assert (Hwi : g_wf i) by (eapply Forall_forall; [exact Hwf|eapply nth_error_In; exact Ei]).
  assert (Hlt : pc < length p) by lia.
  assert (Hfetch : g_fetch code w pc = g_word i).
  { unfold code. rewrite g_code_fetch by assumption.
    erewrite nth_error_nth by exact Ei. reflexivity. }
  pose proof (h_step amb hmu code w pc mu g z i Hwi Hfetch) as Hs.
  unfold g_step; cbn [gc_pc gc_mu gc_g]; rewrite Ei.
  destruct (g_next i pc mu g) as [[pc' mu'] g'].
  destruct Hs as [z' Hz']. exists (h_steps i g), z'. split; [apply h_steps_pos|].
  exact Hz'.
Qed.

Lemma h_simulation : forall n c z,
  exists k z', run_vm_u k U (hbc c z) = hbc (g_run n p c) z'.
Proof.
  induction n as [|n IH]; intros c z.
  - exists 0, z. reflexivity.
  - cbn [g_run].
    destruct (le_lt_dec (length p) c.(gc_pc)) as [Ht|Hnt].
    + rewrite (g_step_terminal p c Ht). apply IH.
    + destruct (h_block c z ltac:(unfold g_terminal; lia)) as (k1 & z1 & _ & H1).
      destruct (IH (g_step p c) z1) as (k2 & z2 & H2).
      exists (k1 + k2), z2. rewrite run_vm_u_split, H1. exact H2.
Qed.

Lemma h_fetch_terminal : forall c, g_terminal p c -> g_fetch code w c.(gc_pc) = 0.
Proof. intros c Ht. unfold code. apply g_code_fetch_outside; assumption. Qed.

Definition h_done_c (c : GConf) (s : VMState) : Prop :=
  h_done amb hmu code w c.(gc_pc) c.(gc_mu) c.(gc_g) s.

(** Completeness: a terminating guest run is produced by an actual host run
    that reaches the host's own termination address. *)
Theorem self_interpreter_complete : forall n c z,
  g_terminal p (g_run n p c) ->
  exists F, (run_vm_u F U (hbc c z)).(vm_pc) = U_END /\
            h_done_c (g_run n p c) (run_vm_u F U (hbc c z)).
Proof.
  intros n c z Ht.
  destruct (h_simulation n c z) as (k & z' & Hk).
  pose proof (h_terminal_run amb hmu code w (gc_pc (g_run n p c)) (gc_mu (g_run n p c))
    (gc_g (g_run n p c)) z' (h_fetch_terminal _ Ht)) as Hd.
  exists (k + H_TERM). rewrite run_vm_u_split, Hk. unfold hbc.
  split; [|exact Hd].
  destruct Hd as (a & b & c' & d & e & f & g' & ->). reflexivity.
Qed.

(** Raw soundness: any actual host run that reaches [U_END] from an encoded
    guest configuration has decoded an actual terminal guest run.  The only
    execution premise is the host's own termination; there is no guest trace
    or fuel assumption. *)
Theorem self_interpreter_sound : forall F c z,
  (run_vm_u F U (hbc c z)).(vm_pc) = U_END ->
  exists n, g_terminal p (g_run n p c) /\
            h_done_c (g_run n p c) (run_vm_u F U (hbc c z)).
Proof.
  induction F as [F IH] using lt_wf_ind. intros c z HF.
  unfold h_done_c. unfold hbc in HF |- *.
  destruct (le_lt_dec (length p) c.(gc_pc)) as [Ht|Hnt].
  - exists 0. cbn [g_run]. split; [exact Ht|].
    pose proof (h_terminal_run amb hmu code w (gc_pc c) (gc_mu c) (gc_g c) z
      (h_fetch_terminal c Ht)) as Hd.
    assert (Hend : (run_vm_u H_TERM U (hb amb hmu code w (gc_pc c) (gc_mu c) (gc_g c) z)).(vm_pc) = U_END)
      by (destruct Hd as (a & b & c' & d & e & f & g' & Hd); rewrite Hd; reflexivity).
    destruct (le_lt_dec F H_TERM) as [Hle|Hgt].
    + replace H_TERM with (F + (H_TERM - F)) in Hd by lia.
      rewrite (h_terminal_stable F (H_TERM - F) _ HF) in Hd. exact Hd.
    + replace F with (H_TERM + (F - H_TERM)) by lia.
      rewrite h_terminal_stable by exact Hend. exact Hd.
  - destruct (h_block c z ltac:(unfold g_terminal; lia)) as (k & z' & Hk & Hrun).
    destruct (le_lt_dec k F) as [Hle|Hlt].
    + replace F with (k + (F - k)) in HF |- * by lia.
      fold (hbc c z) in HF |- *.
      rewrite run_vm_u_split, Hrun in HF |- *.
      destruct (IH (F - k) ltac:(lia) (g_step p c) z' HF) as (n & Htn & Hdn).
      exists (S n). cbn [g_run]. split; assumption.
    + exfalso.
      fold (hbc c z) in HF.
      pose proof (h_terminal_stable F (k - F) (hbc c z) HF) as Hst.
      replace (F + (k - F)) with k in Hst by lia.
      rewrite Hrun in Hst.
      assert (Hpc0 : (hbc (g_step p c) z').(vm_pc) = 0) by reflexivity.
      rewrite Hst, HF in Hpc0. discriminate.
Qed.

(** Result correctness in both directions for the observation
    "terminal guest configuration", read from the actual host run. *)
Theorem self_interpreter_correct : forall c z c',
  (exists n, g_terminal p (g_run n p c) /\ g_run n p c = c') <->
  (exists F, (run_vm_u F U (hbc c z)).(vm_pc) = U_END /\
             h_done_c c' (run_vm_u F U (hbc c z))).
Proof.
  intros c z c'. split.
  - intros (n & Ht & <-). apply self_interpreter_complete, Ht.
  - intros (F & HF & Hd).
    destruct (self_interpreter_sound F c z HF) as (n & Ht & Hd').
    exists n. split; [exact Ht|].
    destruct Hd as (a1 & a2 & a3 & a4 & a5 & a6 & a7 & E1).
    destruct Hd' as (b1 & b2 & b3 & b4 & b5 & b6 & b7 & E2).
    rewrite E1 in E2. unfold hst in E2. injection E2 as Hreg.
    destruct c' as [pc1 mu1 [x0 x1 x2 x3]], (g_run n p c) as [pc2 mu2 [y0 y1 y2 y3]].
    cbn in *. inversion Hreg. subst. reflexivity.
Qed.

(** Divergence: the guest never terminates exactly when no actual host run
    ever reaches [U_END].  Exhausting a fuel budget is not used as a
    definition of divergence. *)
Theorem self_interpreter_divergence : forall c z,
  (forall n, ~ g_terminal p (g_run n p c)) <->
  (forall F, (run_vm_u F U (hbc c z)).(vm_pc) <> U_END).
Proof.
  intros c z. split.
  - intros Hg F HF. destruct (self_interpreter_sound F c z HF) as (n & Ht & _).
    exact (Hg n Ht).
  - intros Hh n Ht. destruct (self_interpreter_complete n c z Ht) as (F & HF & _).
    exact (Hh F HF).
Qed.

End HostRuns.

(** * 5. Host pc bound and the available-instruction form of divergence. *)

Lemma U_step_bound : Forall (fun i => forall s, s.(vm_pc) < U_END ->
                                      (vm_apply_u s i).(vm_pc) <= U_END) U.
Proof.
  unfold U, self_interpreter_program.
  repeat (apply Forall_cons;
          [intros s Hs; cbn [vm_apply_u advance_state advance_state_rm jump_state vm_pc];
           try (destruct (Nat.eqb _ 0); cbn [advance_state jump_state vm_pc]);
           unfold U_END in *; lia|]).
  apply Forall_nil.
Qed.

Lemma U_pc_bound : forall F s, s.(vm_pc) <= U_END -> (run_vm_u F U s).(vm_pc) <= U_END.
Proof.
  induction F as [|F IH]; intros s Hs; [exact Hs|].
  cbn [run_vm_u]. destruct (nth_error U (vm_pc s)) as [i|] eqn:Ei; [|exact Hs].
  apply IH.
  assert (Hlt : vm_pc s < U_END)
    by (rewrite <- U_length; apply nth_error_Some; rewrite Ei; discriminate).
  pose proof (proj1 (Forall_forall _ U) U_step_bound i (nth_error_In _ _ Ei)) as Hb.
  apply Hb, Hlt.
Qed.

Theorem self_interpreter_divergence_live : forall amb hmu w p c z,
  g_wf_program p -> g_fits w p ->
  (forall n, ~ g_terminal p (g_run n p c)) ->
  forall F, exists instr,
    nth_error U (run_vm_u F U (hbc amb hmu w p c z)).(vm_pc) = Some instr.
Proof.
  intros amb hmu w p c z Hwf Hfit Hdiv F.
  pose proof (proj1 (self_interpreter_divergence amb hmu w p Hwf Hfit c z) Hdiv F) as Hne.
  pose proof (U_pc_bound F (hbc amb hmu w p c z) ltac:(cbn; unfold U_END; lia)) as Hle.
  destruct (nth_error U _) as [i|] eqn:Ei; [exists i; reflexivity|].
  apply nth_error_None in Ei. rewrite U_length in Ei. lia.
Qed.

(** * 6. Malformed words.

    For arbitrary packed data (not only the canonical encoding), a fetched
    word whose low four bits are 13, 14 or 15 makes the host leave [U] with
    status 2 and the guest registers, ledger and pc unchanged.  Canonical
    encodings never produce such a word: [self_interpreter_sound] shows every
    terminating host run from them ends with status 1. *)

Lemma u_and_3_lt : forall x, u_and x 3 < 4.
Proof.
  intro x. pose proof (N.mod_lt (N.of_nat x) 4 ltac:(discriminate)) as H.
  assert (E : N.of_nat (u_and x 3) = (N.of_nat x mod 4)%N).
  { change 3 with (u_sub (u_shl 1 2) 1).
    rewrite N_of_nat_u_and, nat_ones_eq, N2Nat.id, N.land_ones. reflexivity. }
  lia.
Qed.

Definition h_malformed_steps (w : nat) : nat :=
  7 + (4 + (rc (u_and (u_shr w 6) 3) + (4 + (rc (u_and (u_shr w 8) 3) + (2 + 27))))).

Theorem self_interpreter_malformed : forall amb hmu code width pc mu g z,
  13 <= u_and (g_fetch code width pc) 15 <= 15 ->
  exists z4 z5 z6 z7 z8 z10 z15,
    run_vm_u (h_malformed_steps (g_fetch code width pc)) U (hb amb hmu code width pc mu g z) =
    hst amb hmu U_END [g.(gr0); g.(gr1); g.(gr2); g.(gr3);
                       z4; z5; z6; z7; z8; 2; z10; mu; pc; width; code; z15].
Proof.
  intros amb hmu code width pc mu [g0 g1 g2 g3] [a4 a5 a6 a7 a8 a10 a15] Hop.
  unfold h_malformed_steps, hb; cbn [gr0 gr1 gr2 gr3 hs4 hs5 hs6 hs7 hs8 hs10 hs15].
  set (wd := g_fetch code width pc) in *.
  rewrite run_vm_u_split, ph_fetch. fold wd.
  rewrite run_vm_u_split, ph_rs1_index.
  rewrite run_vm_u_split, ph_read_rs1 by apply u_and_3_lt.
  rewrite run_vm_u_split, ph_rs2_index.
  rewrite run_vm_u_split, ph_read_rs2 by apply u_and_3_lt.
  rewrite run_vm_u_split, ph_opcode.
  rewrite ph_op_malformed by exact Hop.
  do 7 eexists. reflexivity.
Qed.
