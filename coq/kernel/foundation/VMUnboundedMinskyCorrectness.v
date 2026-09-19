(** Multi-step and result correctness for the fixed unbounded interpreter. *)
From Coq Require Import Arith Lia List.
Import ListNotations.
From Kernel Require Import VMState VMStep VMUnboundedStep VMUnboundedInterpreterCompose.
From Kernel Require Import VMUnboundedMinskyInterpreter.
From Kernel Require Import VMUnboundedMinskyInterpreterProof.
From Kernel Require Import VMUnboundedMinskyEncoding.

Lemma minsky_rep_config_unique : forall code width c c' s,
  minsky_rep code width c s -> minsky_rep code width c' s -> c = c'.
Proof.
  intros code width [pc c0 c1] [pc' c0' c1'] s
    (a & z & ->) (a' & z' & H).
  pose proof (f_equal vm_regs H) as Hr. cbn [minsky_boundary_s] in Hr.
  inversion Hr. reflexivity.
Qed.

Theorem uniform_interpreter_run_simulation : forall p width c c' s,
  minsky_program_fits width p ->
  minsky_run p c c' ->
  minsky_rep (encode_minsky_program width p) width c s ->
  exists fuel s',
    run_vm_u fuel minsky_interpreter_program s = s' /\
    minsky_rep (encode_minsky_program width p) width c' s'.
Proof.
  intros p width c c' s Hfit Hrun.
  revert s. induction Hrun as [c|c i c1 c2 Hnth Hstep Htail IH]; intros s Hrep.
  - exists 0, s. split; [reflexivity|exact Hrep].
  - assert (Hpc : c.(mc_pc) < length p).
    { apply nth_error_Some. rewrite Hnth. discriminate. }
    assert (Hword : minsky_word (encode_minsky_program width p) width c.(mc_pc) =
                    encode_minsky_instr i).
    { rewrite encode_minsky_program_fetch by assumption.
      apply nth_error_nth with (d := MU_Halt) in Hnth. rewrite Hnth. reflexivity. }
    destruct (uniform_interpreter_simulation
      (encode_minsky_program width p) width c s i c1 Hrep Hword Hstep)
      as (s1 & Hpos & Hone & Hrep1).
    destruct (IH s1 Hrep1) as (fuel2 & s2 & Htwo & Hrep2).
    exists (minsky_host_steps i c + fuel2), s2. split.
    + rewrite run_vm_u_split, Hone. exact Htwo.
    + exact Hrep2.
Qed.

Inductive minsky_halts (p : list MinskyInstrU) (start : MinskyConfigU)
    : MinskyConfigU -> Prop :=
| minsky_halts_explicit : forall final,
    minsky_run p start final ->
    nth_error p final.(mc_pc) = Some MU_Halt ->
    minsky_halts p start final
| minsky_halts_falloff : forall final,
    minsky_run p start final ->
    nth_error p final.(mc_pc) = None ->
    minsky_halts p start final.

(** Actual host executions segmented only at interpreter boundaries.  The
    constructor records the instruction found in encoded guest data and
    the resulting represented boundary, but does not assume a guest step. *)
Inductive interpreter_boundary_run (p : list MinskyInstrU) (width : nat)
    : MinskyConfigU -> VMState -> MinskyConfigU -> VMState -> Prop :=
| interpreter_boundary_refl : forall c s,
    minsky_rep (encode_minsky_program width p) width c s ->
    interpreter_boundary_run p width c s c s
| interpreter_boundary_step : forall c s c1 s1 c2 s2 i,
    minsky_rep (encode_minsky_program width p) width c s ->
    nth_error p c.(mc_pc) = Some i ->
    i <> MU_Halt ->
    run_vm_u (minsky_host_steps i c) minsky_interpreter_program s = s1 ->
    minsky_rep (encode_minsky_program width p) width c1 s1 ->
    interpreter_boundary_run p width c1 s1 c2 s2 ->
    interpreter_boundary_run p width c s c2 s2.

Theorem interpreter_boundary_run_sound : forall p width c s c' s',
  minsky_program_fits width p ->
  interpreter_boundary_run p width c s c' s' ->
  minsky_run p c c'.
Proof.
  intros p width c s c' s' Hfit Hhost.
  induction Hhost as [c s Hrep|c s c1 s1 c2 s2 i Hrep Hnth Hnhalt Hactual Hrep1 Htail IH].
  - constructor.
  - assert (Hpc : c.(mc_pc) < length p).
    { apply nth_error_Some. rewrite Hnth. discriminate. }
    assert (Hword : minsky_word (encode_minsky_program width p) width c.(mc_pc) =
                    encode_minsky_instr i).
    { rewrite encode_minsky_program_fetch by assumption.
      apply nth_error_nth with (d := MU_Halt) in Hnth. rewrite Hnth. reflexivity. }
    assert (Hex : exists expected, minsky_step_instr i c = Some expected).
    { destruct i; try contradiction; destruct c as [gpc cnt0 cnt1];
        cbn [minsky_step_instr]; try (eexists; reflexivity);
        destruct Nat.eqb; eexists; reflexivity. }
    destruct Hex as [expected Hstep].
    destruct (uniform_interpreter_simulation
      (encode_minsky_program width p) width c s i expected Hrep Hword Hstep)
      as (se & Hpos & Hexpected & Hrepe).
    rewrite Hactual in Hexpected. subst se.
    assert (Hc : c1 = expected)
      by (eapply minsky_rep_config_unique; [exact Hrep1|exact Hrepe]). subst expected.
    econstructor; eauto.
Qed.

Theorem interpreter_boundary_run_complete : forall p width c c' s,
  minsky_program_fits width p ->
  minsky_run p c c' ->
  minsky_rep (encode_minsky_program width p) width c s ->
  exists s', interpreter_boundary_run p width c s c' s'.
Proof.
  intros p width c c' s Hfit Hrun. revert s.
  induction Hrun as [c|c i c1 c2 Hnth Hstep Htail IH]; intros s Hrep.
  - exists s. constructor. exact Hrep.
  - assert (Hpc : c.(mc_pc) < length p).
    { apply nth_error_Some. rewrite Hnth. discriminate. }
    assert (Hword : minsky_word (encode_minsky_program width p) width c.(mc_pc) =
                    encode_minsky_instr i).
    { rewrite encode_minsky_program_fetch by assumption.
      apply nth_error_nth with (d := MU_Halt) in Hnth. rewrite Hnth. reflexivity. }
    destruct (uniform_interpreter_simulation
      (encode_minsky_program width p) width c s i c1 Hrep Hword Hstep)
      as (s1 & Hpos & Hone & Hrep1).
    destruct (IH s1 Hrep1) as [s2 Hrest]. exists s2.
    econstructor; eauto. intro Heq. subst i. cbn [minsky_step_instr] in Hstep. discriminate.
Qed.

Lemma interpreter_one_boundary_sound : forall p width c s c1 s1 i,
  minsky_program_fits width p ->
  minsky_rep (encode_minsky_program width p) width c s ->
  nth_error p c.(mc_pc) = Some i -> i <> MU_Halt ->
  run_vm_u (minsky_host_steps i c) minsky_interpreter_program s = s1 ->
  minsky_rep (encode_minsky_program width p) width c1 s1 ->
  minsky_step_instr i c = Some c1.
Proof.
  intros p width c s c1 s1 i Hfit Hrep Hnth Hnhalt Hactual Hrep1.
  assert (Hpc : c.(mc_pc) < length p).
  { apply nth_error_Some. rewrite Hnth. discriminate. }
  assert (Hword : minsky_word (encode_minsky_program width p) width c.(mc_pc) =
                  encode_minsky_instr i).
  { rewrite encode_minsky_program_fetch by assumption.
    apply nth_error_nth with (d := MU_Halt) in Hnth. rewrite Hnth. reflexivity. }
  assert (Hex : exists expected, minsky_step_instr i c = Some expected).
  { destruct i; try contradiction; destruct c as [gpc cnt0 cnt1];
      cbn [minsky_step_instr]; try (eexists; reflexivity);
      destruct Nat.eqb; eexists; reflexivity. }
  destruct Hex as [expected Hstep].
  destruct (uniform_interpreter_simulation
    (encode_minsky_program width p) width c s i expected Hrep Hword Hstep)
    as (se & Hpos & Hexpected & Hrepe).
  rewrite Hactual in Hexpected. subst se.
  assert (c1 = expected) by (eapply minsky_rep_config_unique; eauto). subst expected.
  exact Hstep.
Qed.

Inductive interpreter_boundary_run_n (p : list MinskyInstrU) (width : nat)
    : nat -> MinskyConfigU -> VMState -> MinskyConfigU -> VMState -> Prop :=
| interpreter_boundary_n_zero : forall c s,
    minsky_rep (encode_minsky_program width p) width c s ->
    interpreter_boundary_run_n p width 0 c s c s
| interpreter_boundary_n_succ : forall n c s c1 s1 c2 s2 i,
    minsky_rep (encode_minsky_program width p) width c s ->
    nth_error p c.(mc_pc) = Some i -> i <> MU_Halt ->
    run_vm_u (minsky_host_steps i c) minsky_interpreter_program s = s1 ->
    minsky_rep (encode_minsky_program width p) width c1 s1 ->
    interpreter_boundary_run_n p width n c1 s1 c2 s2 ->
    interpreter_boundary_run_n p width (S n) c s c2 s2.

Theorem interpreter_boundary_run_n_sound : forall p width n c s c' s',
  minsky_program_fits width p ->
  interpreter_boundary_run_n p width n c s c' s' ->
  minsky_run_n p n c c'.
Proof.
  intros p width n c s c' s' Hfit Hrun. induction Hrun.
  - constructor.
  - econstructor; [exact H0| |exact IHHrun].
    eapply interpreter_one_boundary_sound; eauto.
Qed.

Theorem interpreter_boundary_run_n_complete : forall p width n c c' s,
  minsky_program_fits width p -> minsky_run_n p n c c' ->
  minsky_rep (encode_minsky_program width p) width c s ->
  exists s', interpreter_boundary_run_n p width n c s c' s'.
Proof.
  intros p width n c c' s Hfit Hrun. revert s.
  induction Hrun as [c|n c i c1 c2 Hnth Hstep Htail IH]; intros s Hrep.
  - exists s. constructor. exact Hrep.
  - assert (Hpc : c.(mc_pc) < length p).
    { apply nth_error_Some. rewrite Hnth. discriminate. }
    assert (Hword : minsky_word (encode_minsky_program width p) width c.(mc_pc) =
                    encode_minsky_instr i).
    { rewrite encode_minsky_program_fetch by assumption.
      apply nth_error_nth with (d := MU_Halt) in Hnth. rewrite Hnth. reflexivity. }
    destruct (uniform_interpreter_simulation
      (encode_minsky_program width p) width c s i c1 Hrep Hword Hstep)
      as (s1 & Hpos & Hone & Hrep1).
    destruct (IH s1 Hrep1) as [s2 Hrest]. exists s2.
    econstructor; eauto. intro Heq. subst i. cbn [minsky_step_instr] in Hstep. discriminate.
Qed.

Definition interpreter_diverges (ambient : VMState) (p : list MinskyInstrU)
    (width : nat) (start : MinskyConfigU) : Prop :=
  forall n, exists c s,
    interpreter_boundary_run_n p width n start
      (minsky_config_encoding ambient p width start) c s.

Theorem uniform_interpreter_divergence : forall ambient p width start,
  minsky_program_fits width p ->
  (minsky_diverges p start <-> interpreter_diverges ambient p width start).
Proof.
  intros ambient p width start Hfit. split.
  - intros Hdiv n. destruct (Hdiv n) as [c Hrun].
    destruct (interpreter_boundary_run_n_complete p width n start c
      (minsky_config_encoding ambient p width start) Hfit Hrun) as [s Hhost].
    { unfold minsky_config_encoding. apply minsky_boundary_is_rep. }
    exists c, s. exact Hhost.
  - intros Hdiv n. destruct (Hdiv n) as (c & s & Hhost).
    exists c. eapply interpreter_boundary_run_n_sound; eauto.
Qed.

Definition interpreter_produces (ambient : VMState) (p : list MinskyInstrU)
    (width : nat) (start final : MinskyConfigU) : Prop :=
  exists boundary terminal,
    interpreter_boundary_run p width start
      (minsky_config_encoding ambient p width start) final boundary /\
    (nth_error p final.(mc_pc) = Some MU_Halt \/ nth_error p final.(mc_pc) = None) /\
    run_vm_u 12 minsky_interpreter_program boundary = terminal /\
    minsky_halt_rep (encode_minsky_program width p) width final terminal.

Theorem uniform_interpreter_correct_sound : forall ambient p width start final,
  minsky_program_fits width p ->
  interpreter_produces ambient p width start final ->
  minsky_halts p start final.
Proof.
  intros ambient p width start final Hfit
    (boundary & terminal & Hrun & [Hhalt|Hfall] & Hactual & Hterminal).
  - apply minsky_halts_explicit; [eapply interpreter_boundary_run_sound; eauto|exact Hhalt].
  - apply minsky_halts_falloff; [eapply interpreter_boundary_run_sound; eauto|exact Hfall].
Qed.

Theorem uniform_interpreter_correct : forall ambient p width start final,
  minsky_program_fits width p ->
  (minsky_halts p start final <->
   interpreter_produces ambient p width start final).
Proof.
  intros ambient p width start final Hfit. split.
  - intro Hhalt.
    assert (Hrun : minsky_run p start final).
    { inversion Hhalt; assumption. }
    destruct (interpreter_boundary_run_complete p width start final
      (minsky_config_encoding ambient p width start) Hfit Hrun) as [boundary Hboundary].
    { unfold minsky_config_encoding. apply minsky_boundary_is_rep. }
    assert (Hrep : minsky_rep (encode_minsky_program width p) width final boundary).
    { clear Hhalt Hrun. induction Hboundary; assumption. }
    destruct Hrep as (ambient' & z & ->).
    exists (minsky_boundary_s ambient' (encode_minsky_program width p) width final z),
      (run_vm_u 12 minsky_interpreter_program
        (minsky_boundary_s ambient' (encode_minsky_program width p) width final z)).
    split; [exact Hboundary|]. split.
    + inversion Hhalt; [left|right]; assumption.
    + split; [reflexivity|]. apply minsky_rep_halt.
      inversion Hhalt as [f Hr Hnth|f Hr Hnone]; subst f.
      * assert (Hpc : final.(mc_pc) < length p).
        { apply nth_error_Some. rewrite Hnth. discriminate. }
        rewrite encode_minsky_program_fetch by assumption.
        apply nth_error_nth with (d := MU_Halt) in Hnth. rewrite Hnth. reflexivity.
      * apply encode_minsky_program_fetch_outside; [exact Hfit|].
        apply nth_error_None. exact Hnone.
  - apply uniform_interpreter_correct_sound. exact Hfit.
Qed.

Theorem uniform_interpreter_correct_complete : forall ambient p width start final,
  minsky_program_fits width p ->
  minsky_halts p start final ->
  exists fuel s_boundary s_final,
    run_vm_u fuel minsky_interpreter_program
      (minsky_boundary ambient (encode_minsky_program width p) width start) = s_boundary /\
    minsky_rep (encode_minsky_program width p) width final s_boundary /\
    run_vm_u 12 minsky_interpreter_program s_boundary = s_final /\
    minsky_halt_rep (encode_minsky_program width p) width final s_final.
Proof.
  intros ambient p width start final Hfit Hhalt.
  inversion Hhalt as [f Hrun Hnth|f Hrun Hnone]; subst f.
  - destruct (uniform_interpreter_run_simulation p width start final
      (minsky_boundary ambient (encode_minsky_program width p) width start)
      Hfit Hrun (minsky_boundary_is_rep _ _ _ _)) as (fuel & sb & Hrunhost & Hrep).
    destruct Hrep as (ambient' & z & ->).
    assert (Hpc : final.(mc_pc) < length p).
    { apply nth_error_Some. rewrite Hnth. discriminate. }
    assert (Hword : minsky_word (encode_minsky_program width p) width final.(mc_pc) = 0).
    { rewrite encode_minsky_program_fetch by assumption.
      apply nth_error_nth with (d := MU_Halt) in Hnth. rewrite Hnth. reflexivity. }
    exists fuel,
      (minsky_boundary_s ambient' (encode_minsky_program width p) width final z),
      (run_vm_u 12 minsky_interpreter_program
        (minsky_boundary_s ambient' (encode_minsky_program width p) width final z)).
    split; [exact Hrunhost|]. split.
    + exists ambient', z. reflexivity.
    + split; [reflexivity|]. apply minsky_rep_halt. exact Hword.
  - destruct (uniform_interpreter_run_simulation p width start final
      (minsky_boundary ambient (encode_minsky_program width p) width start)
      Hfit Hrun (minsky_boundary_is_rep _ _ _ _)) as (fuel & sb & Hrunhost & Hrep).
    destruct Hrep as (ambient' & z & ->).
    assert (Hpc : length p <= final.(mc_pc)) by (apply nth_error_None; exact Hnone).
    assert (Hword : minsky_word (encode_minsky_program width p) width final.(mc_pc) = 0)
      by (apply encode_minsky_program_fetch_outside; assumption).
    exists fuel,
      (minsky_boundary_s ambient' (encode_minsky_program width p) width final z),
      (run_vm_u 12 minsky_interpreter_program
        (minsky_boundary_s ambient' (encode_minsky_program width p) width final z)).
    split; [exact Hrunhost|]. split.
    + exists ambient', z. reflexivity.
    + split; [reflexivity|]. apply minsky_rep_halt. exact Hword.
Qed.

(** Premise-free public forms: the executable width selector makes the data
    encoding applicable to every finite guest program. *)
Theorem uniform_interpreter_simulation_total : forall ambient p c i c',
  nth_error p c.(mc_pc) = Some i ->
  minsky_step_instr i c = Some c' ->
  exists s',
    0 < minsky_host_steps i c /\
    run_vm_u (minsky_host_steps i c) minsky_interpreter_program
      (minsky_total_config_encoding ambient p c) = s' /\
    minsky_rep
      (encode_minsky_program (minsky_encoding_width p) p)
      (minsky_encoding_width p) c' s'.
Proof.
  intros ambient p c i c' Hnth Hstep.
  assert (Hpc : c.(mc_pc) < length p).
  { apply nth_error_Some. rewrite Hnth. discriminate. }
  assert (Hword :
    minsky_word (encode_minsky_program (minsky_encoding_width p) p)
      (minsky_encoding_width p) c.(mc_pc) = encode_minsky_instr i).
  { rewrite encode_minsky_program_fetch.
    - apply nth_error_nth with (d := MU_Halt) in Hnth. rewrite Hnth. reflexivity.
    - apply minsky_program_fits_encoding_width.
    - exact Hpc. }
  unfold minsky_total_config_encoding, minsky_config_encoding.
  eapply uniform_interpreter_simulation.
  - apply minsky_boundary_is_rep.
  - exact Hword.
  - exact Hstep.
Qed.

Theorem uniform_interpreter_divergence_total : forall ambient p start,
  minsky_diverges p start <->
  interpreter_diverges ambient p (minsky_encoding_width p) start.
Proof.
  intros. apply uniform_interpreter_divergence.
  apply minsky_program_fits_encoding_width.
Qed.

Theorem uniform_interpreter_correct_total : forall ambient p start final,
  minsky_halts p start final <->
  interpreter_produces ambient p (minsky_encoding_width p) start final.
Proof.
  intros. apply uniform_interpreter_correct.
  apply minsky_program_fits_encoding_width.
Qed.

Theorem uniform_interpreter_correct_complete_total : forall ambient p start final,
  minsky_halts p start final ->
  exists fuel s_boundary s_final,
    run_vm_u fuel minsky_interpreter_program
      (minsky_total_config_encoding ambient p start) = s_boundary /\
    minsky_rep
      (encode_minsky_program (minsky_encoding_width p) p)
      (minsky_encoding_width p) final s_boundary /\
    run_vm_u 12 minsky_interpreter_program s_boundary = s_final /\
    minsky_halt_rep
      (encode_minsky_program (minsky_encoding_width p) p)
      (minsky_encoding_width p) final s_final.
Proof.
  intros ambient p start final Hhalt.
  unfold minsky_total_config_encoding, minsky_config_encoding.
  eapply uniform_interpreter_correct_complete.
  - apply minsky_program_fits_encoding_width.
  - exact Hhalt.
Qed.

Theorem total_encoding_never_malformed_opcode : forall p pc,
  pc < length p ->
  u_and
    (minsky_word
      (encode_minsky_program (minsky_encoding_width p) p)
      (minsky_encoding_width p) pc) 7 <= 4.
Proof.
  intros p pc Hpc. rewrite encode_minsky_program_fetch.
  - apply encode_minsky_opcode_valid.
  - apply minsky_program_fits_encoding_width.
  - exact Hpc.
Qed.

(** Raw host observations: no guest trace or segmentation is assumed. *)
Definition minsky_result (s : VMState) : MinskyConfigU :=
  {| mc_pc := read_reg s 12; mc_c0 := read_reg s 11; mc_c1 := read_reg s 10 |}.

Lemma minsky_halt_rep_result : forall code width c s,
  minsky_halt_rep code width c s -> minsky_result s = c.
Proof.
  intros code width [pc c0 c1] s (a & z & ->).
  unfold minsky_result, read_reg, reg_index, REG_COUNT. reflexivity.
Qed.

Lemma minsky_terminal_stable : forall s fuel,
  s.(vm_pc) = 60 -> run_vm_u fuel minsky_interpreter_program s = s.
Proof.
  intros s [|fuel] Hpc; [reflexivity|]. cbn [run_vm_u].
  rewrite Hpc. reflexivity.
Qed.

Lemma minsky_rep_not_terminal : forall code width c s,
  minsky_rep code width c s -> s.(vm_pc) <> 60.
Proof. intros code width c s (a & z & ->). discriminate. Qed.

Lemma minsky_terminal_compare_fuels : forall s n k,
  (run_vm_u n minsky_interpreter_program s).(vm_pc) = 60 ->
  (run_vm_u k minsky_interpreter_program s).(vm_pc) = 60 ->
  run_vm_u n minsky_interpreter_program s =
  run_vm_u k minsky_interpreter_program s.
Proof.
  intros s n k Hn Hk. destruct (le_dec n k).
  - replace k with (n + (k-n)) by lia. rewrite run_vm_u_split.
    symmetry. apply minsky_terminal_stable. exact Hn.
  - replace n with (k + (n-k)) by lia. rewrite run_vm_u_split.
    apply minsky_terminal_stable. exact Hk.
Qed.

Theorem uniform_interpreter_raw_sound : forall fuel p width start s,
  minsky_program_fits width p ->
  minsky_rep (encode_minsky_program width p) width start s ->
  (run_vm_u fuel minsky_interpreter_program s).(vm_pc) = 60 ->
  minsky_halts p start (minsky_result (run_vm_u fuel minsky_interpreter_program s)) /\
  minsky_halted (run_vm_u fuel minsky_interpreter_program s).
Proof.
  intro fuel. induction fuel using lt_wf_ind.
  intros p width start s Hfit Hrep Hterminal.
  destruct (nth_error p start.(mc_pc)) as [i|] eqn:Hnth.
  - assert (Hpc : start.(mc_pc) < length p).
    { apply nth_error_Some. rewrite Hnth. discriminate. }
    assert (Hword : minsky_word (encode_minsky_program width p) width start.(mc_pc) =
                    encode_minsky_instr i).
    { rewrite encode_minsky_program_fetch by assumption.
      apply nth_error_nth with (d := MU_Halt) in Hnth. rewrite Hnth. reflexivity. }
    destruct i as [| | |target|target].
    { destruct Hrep as (a & z & ->).
      pose proof (minsky_rep_halt a _ _ start z Hword) as Hr.
      pose proof (minsky_halt_rep_observed _ _ _ _ Hr) as Ho.
      destruct Ho as [Hpcend Hstatus]. rewrite minsky_interpreter_program_length in Hpcend.
      pose proof (minsky_terminal_compare_fuels _ _ _ Hterminal Hpcend) as Heq.
      rewrite Heq. split.
      * rewrite (minsky_halt_rep_result _ _ _ _ Hr).
        apply minsky_halts_explicit; [constructor|exact Hnth].
      * apply minsky_halt_rep_observed in Hr. exact Hr. }
    all: assert (Hex : exists next, minsky_step_instr
      ltac:(match type of Hword with _ = encode_minsky_instr ?i => exact i end)
      start = Some next) by
      (cbn [minsky_step_instr]; try (eexists; reflexivity);
       destruct Nat.eqb; eexists; reflexivity).
    all: destruct Hex as [next Hstep].
    all: destruct (uniform_interpreter_simulation _ _ _ _ _ _ Hrep Hword Hstep)
      as (s1 & Hpos & Hexec & Hr1).
    all: match type of Hpos with 0 < ?k => set (steps := k) in * end.
    all: assert (Hk : steps <= fuel).
    all: try (destruct (le_dec (steps) fuel); [assumption|];
      exfalso; assert (E : run_vm_u (steps) minsky_interpreter_program s =
                            run_vm_u fuel minsky_interpreter_program s) by
        (replace (steps) with
          (fuel + (steps - fuel)) by lia;
         rewrite run_vm_u_split; apply minsky_terminal_stable; exact Hterminal);
      rewrite Hexec in E; apply (minsky_rep_not_terminal _ _ _ _ Hr1);
      rewrite E; exact Hterminal).
    all: assert (Erun : run_vm_u fuel minsky_interpreter_program s =
      run_vm_u (fuel - steps)
        minsky_interpreter_program s1) by
      (replace fuel with (steps + (fuel - steps))
        at 1 by lia; rewrite run_vm_u_split, Hexec; reflexivity).
    all: rewrite Erun in Hterminal |- *.
    all: destruct (H (fuel - steps) ltac:(lia) p width next s1 Hfit Hr1 Hterminal) as [Hhalt Hobs].
    all: split; [inversion Hhalt; subst;
      [apply minsky_halts_explicit|apply minsky_halts_falloff];
      try (econstructor; eauto); assumption|exact Hobs].
  - assert (Hword : minsky_word (encode_minsky_program width p) width start.(mc_pc) = 0).
    { apply encode_minsky_program_fetch_outside; [exact Hfit|].
      apply nth_error_None. exact Hnth. }
    destruct Hrep as (a & z & ->).
    pose proof (minsky_rep_halt a _ _ start z Hword) as Hr.
    pose proof (minsky_halt_rep_observed _ _ _ _ Hr) as Ho.
    destruct Ho as [Hpcend Hstatus]. rewrite minsky_interpreter_program_length in Hpcend.
    pose proof (minsky_terminal_compare_fuels _ _ _ Hterminal Hpcend) as Heq.
    rewrite Heq. split.
    + rewrite (minsky_halt_rep_result _ _ _ _ Hr).
      apply minsky_halts_falloff; [constructor|exact Hnth].
    + apply minsky_halt_rep_observed in Hr. exact Hr.
Qed.

Definition interpreter_raw_produces (ambient : VMState) (p : list MinskyInstrU)
    (start final : MinskyConfigU) : Prop :=
  exists fuel,
    minsky_halted (run_vm_u fuel minsky_interpreter_program
      (minsky_total_config_encoding ambient p start)) /\
    minsky_result (run_vm_u fuel minsky_interpreter_program
      (minsky_total_config_encoding ambient p start)) = final.

Theorem uniform_interpreter_raw_correct_total : forall ambient p start final,
  minsky_halts p start final <-> interpreter_raw_produces ambient p start final.
Proof.
  intros ambient p start final. split.
  - intro Hhalt.
    destruct (uniform_interpreter_correct_complete_total ambient p start final Hhalt)
      as (fuel & sb & sf & Hrun & Hrep & Hlast & Hfinal).
    exists (fuel + 12). rewrite run_vm_u_split, Hrun, Hlast. split.
    + eapply minsky_halt_rep_observed; eauto.
    + eapply minsky_halt_rep_result; eauto.
  - intros (fuel & Hhalt & Hresult).
    destruct (uniform_interpreter_raw_sound fuel p (minsky_encoding_width p) start
      (minsky_total_config_encoding ambient p start)) as [Hguest Hhost].
    + apply minsky_program_fits_encoding_width.
    + unfold minsky_total_config_encoding, minsky_config_encoding.
      apply minsky_boundary_is_rep.
    + destruct Hhalt as [Hpc _]. rewrite minsky_interpreter_program_length in Hpc.
      exact Hpc.
    + rewrite Hresult in Hguest. exact Hguest.
Qed.

Theorem uniform_interpreter_raw_never_malformed : forall ambient p start fuel,
  ~ minsky_malformed (run_vm_u fuel minsky_interpreter_program
      (minsky_total_config_encoding ambient p start)).
Proof.
  intros ambient p start fuel Hbad.
  destruct (uniform_interpreter_raw_sound fuel p (minsky_encoding_width p) start
    (minsky_total_config_encoding ambient p start)) as [Hguest Hhost].
  - apply minsky_program_fits_encoding_width.
  - unfold minsky_total_config_encoding, minsky_config_encoding.
    apply minsky_boundary_is_rep.
  - destruct Hbad as [Hpc _]. rewrite minsky_interpreter_program_length in Hpc.
    exact Hpc.
  - eapply minsky_halt_malformed_disjoint; eauto.
Qed.

Lemma minsky_run_n_prefix : forall p n c final,
  minsky_run_n p n c final -> forall k, k <= n ->
  exists mid, minsky_run_n p k c mid.
Proof.
  intros p n c final Hr. induction Hr; intros k Hk.
  - assert (k = 0) by lia. subst. eexists. constructor.
  - destruct k as [|k]; [eexists; constructor|].
    destruct (IHHr k ltac:(lia)) as [mid Hmid].
    exists mid. econstructor; eauto.
Qed.

Lemma minsky_halts_finite_bound : forall p c final,
  minsky_halts p c final ->
  exists n, forall c', ~ minsky_run_n p n c c'.
Proof.
  intros p c final Hhalt.
  assert (Hr : minsky_run p c final) by (inversion Hhalt; assumption).
  assert (Hend : nth_error p final.(mc_pc) = Some MU_Halt \/
                 nth_error p final.(mc_pc) = None) by
    (inversion Hhalt; [left|right]; assumption).
  clear Hhalt. induction Hr as [c|c i c1 c2 Hnth Hstep Htail IH].
  - exists 1. intros c' Hn. inversion Hn; subst.
    destruct Hend as [He|He]; rewrite He in H0; inversion H0; subst.
    discriminate H1.
  - destruct (IH Hend) as [n Hn]. exists (S n). intros c' Hrun.
    inversion Hrun; subst.
    match goal with
    | Hi : nth_error p (mc_pc c) = Some ?j,
      Hs : minsky_step_instr ?j c = Some ?next |- _ =>
        rewrite Hnth in Hi; inversion Hi; subst j;
        rewrite Hstep in Hs; inversion Hs; subst next
    end.
    eapply Hn; eauto.
Qed.

Lemma minsky_halts_not_diverges : forall p c final,
  minsky_halts p c final -> ~ minsky_diverges p c.
Proof.
  intros p c final Hhalt Hdiv.
  destruct (minsky_halts_finite_bound _ _ _ Hhalt) as [n Hn].
  destruct (Hdiv n) as [c' Hr]. eapply Hn; eauto.
Qed.

Lemma minsky_no_halt_prefixes : forall p start,
  (forall final, ~ minsky_halts p start final) -> minsky_diverges p start.
Proof.
  intros p start Hnone n. revert start Hnone.
  induction n as [|n IH]; intros start Hnone.
  - exists start. constructor.
  - destruct (nth_error p start.(mc_pc)) as [i|] eqn:Hnth.
    2: { exfalso. apply (Hnone start). apply minsky_halts_falloff; [constructor|exact Hnth]. }
    assert (Hex : exists next, minsky_step_instr i start = Some next).
    { destruct i; cbn [minsky_step_instr]; try (eexists; reflexivity);
        try (destruct Nat.eqb; eexists; reflexivity).
      exfalso. apply (Hnone start). apply minsky_halts_explicit; [constructor|exact Hnth]. }
    destruct Hex as [next Hstep].
    destruct (IH next) as [final Hrun].
    + intros final Hhalt. apply (Hnone final). inversion Hhalt; subst;
        [apply minsky_halts_explicit|apply minsky_halts_falloff];
        try (econstructor; eauto); assumption.
    + exists final. econstructor; eauto.
Qed.

(** Infinite execution means arbitrarily many available host steps, not
    exhaustion of any particular fuel budget.  From encoded boundaries,
    terminal PC 60 is the sole exit, as the raw soundness proof certifies
    every such exit and step simulation supplies every live guest prefix. *)
Definition interpreter_raw_diverges (ambient : VMState) (p : list MinskyInstrU)
    (start : MinskyConfigU) : Prop :=
  forall fuel, (run_vm_u fuel minsky_interpreter_program
    (minsky_total_config_encoding ambient p start)).(vm_pc) <> 60.

Theorem uniform_interpreter_raw_divergence_total : forall ambient p start,
  minsky_diverges p start <-> interpreter_raw_diverges ambient p start.
Proof.
  intros ambient p start. split.
  - intros Hdiv fuel Hterminal.
    destruct (uniform_interpreter_raw_sound fuel p (minsky_encoding_width p) start
      (minsky_total_config_encoding ambient p start)) as [Hhalt Hobs].
    + apply minsky_program_fits_encoding_width.
    + unfold minsky_total_config_encoding, minsky_config_encoding.
      apply minsky_boundary_is_rep.
    + exact Hterminal.
    + eapply minsky_halts_not_diverges; eauto.
  - intro Hdiv. apply minsky_no_halt_prefixes. intros final Hhalt.
    apply (proj1 (uniform_interpreter_raw_correct_total ambient p start final)) in Hhalt.
    destruct Hhalt as (fuel & [Hpc Hstatus] & Hresult).
    rewrite minsky_interpreter_program_length in Hpc. exact (Hdiv fuel Hpc).
Qed.

(** Structural/ledger observations are independent of the guest registers
    and host scratch.  Every raw host prefix preserves this full frame. *)
Definition minsky_ambient (s : VMState) : VMState :=
  {| vm_graph := s.(vm_graph); vm_csrs := s.(vm_csrs);
     vm_regs := []; vm_mem := s.(vm_mem); vm_pc := 0;
     vm_mu := s.(vm_mu); vm_mu_tensor := s.(vm_mu_tensor);
     vm_err := s.(vm_err); vm_logic_acc := s.(vm_logic_acc);
     vm_mstatus := s.(vm_mstatus); vm_witness := s.(vm_witness);
     vm_certified := s.(vm_certified) |}.

Lemma minsky_instruction_frame_and_pc :
  Forall (fun i => forall s, s.(vm_pc) < 60 ->
    minsky_ambient (vm_apply_u s i) = minsky_ambient s /\
    (vm_apply_u s i).(vm_pc) <= 60) minsky_interpreter_program.
Proof.
  apply Forall_forall. intros i Hi.
  cbn [minsky_interpreter_program In] in Hi.
  repeat destruct Hi as [<-|Hi]; try contradiction; intros s Hpc;
    cbn [vm_apply_u];
    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b eqn:?
    end;
    unfold minsky_ambient, VMStep.advance_state_rm, VMStep.advance_state,
      VMStep.jump_state, VMStep.apply_cost, VMStep.instruction_cost;
    cbn; rewrite ?Nat.add_0_r; split; try reflexivity; lia.
Qed.

Theorem uniform_interpreter_raw_frame : forall fuel s,
  minsky_ambient (run_vm_u fuel minsky_interpreter_program s) = minsky_ambient s.
Proof.
  induction fuel as [|fuel IH]; intro s; [reflexivity|]. cbn [run_vm_u].
  destruct (nth_error minsky_interpreter_program s.(vm_pc)) as [i|] eqn:Hi;
    [|reflexivity]. rewrite IH.
  assert (Hpc : s.(vm_pc) < 60).
  { rewrite <- minsky_interpreter_program_length. apply nth_error_Some.
    rewrite Hi. discriminate. }
  pose proof minsky_instruction_frame_and_pc as H.
  rewrite Forall_forall in H.
  apply (proj1 (H i (nth_error_In _ _ Hi) s Hpc)).
Qed.

Theorem uniform_interpreter_raw_pc_bound : forall fuel s,
  s.(vm_pc) <= 60 -> (run_vm_u fuel minsky_interpreter_program s).(vm_pc) <= 60.
Proof.
  induction fuel as [|fuel IH]; intros s Hpc; [exact Hpc|]. cbn [run_vm_u].
  destruct (nth_error minsky_interpreter_program s.(vm_pc)) as [i|] eqn:Hi;
    [|exact Hpc]. apply IH.
  assert (Hlive : s.(vm_pc) < 60).
  { rewrite <- minsky_interpreter_program_length. apply nth_error_Some.
    rewrite Hi. discriminate. }
  pose proof minsky_instruction_frame_and_pc as H.
  rewrite Forall_forall in H.
  apply (proj2 (H i (nth_error_In _ _ Hi) s Hlive)).
Qed.

Theorem uniform_interpreter_divergence_live_prefixes : forall ambient p start,
  minsky_diverges p start <->
  forall fuel, exists i,
    nth_error minsky_interpreter_program
      (run_vm_u fuel minsky_interpreter_program
        (minsky_total_config_encoding ambient p start)).(vm_pc) = Some i.
Proof.
  intros ambient p start. rewrite (uniform_interpreter_raw_divergence_total ambient p start).
  split.
  - intros Hdiv fuel. destruct (nth_error minsky_interpreter_program
      (run_vm_u fuel minsky_interpreter_program
        (minsky_total_config_encoding ambient p start)).(vm_pc)) as [i|] eqn:Hi.
    + eauto.
    + apply nth_error_None in Hi. rewrite minsky_interpreter_program_length in Hi.
      pose proof (uniform_interpreter_raw_pc_bound fuel
        (minsky_total_config_encoding ambient p start) ltac:(change (0 <= 60); lia)) as Hb.
      exfalso. apply (Hdiv fuel). lia.
  - intros Hlive fuel Hpc. destruct (Hlive fuel) as [i Hi].
    rewrite Hpc in Hi. discriminate.
Qed.
