(** CM2 variant: jump on successful decrement; zero falls through.
    This is the control convention of Dudenhefner, FSCD 2022, Definition 2.
    The earlier zero-branch Minsky modules are preserved with their own scope.
    https://doi.org/10.4230/LIPIcs.FSCD.2022.16 *)
(** Multi-step and result correctness for the fixed unbounded interpreter. *)
From Coq Require Import Arith Lia List.
Import ListNotations.
From Kernel Require Import VMState VMStep VMUnboundedStep VMUnboundedInterpreterCompose.
From Kernel Require Import VMUnboundedCM2Interpreter.
From Kernel Require Import VMUnboundedCM2InterpreterProof.
From Kernel Require Import VMUnboundedCM2Encoding.

Lemma cm2_rep_config_unique : forall code width c c' s,
  cm2_rep code width c s -> cm2_rep code width c' s -> c = c'.
Proof.
  intros code width [pc c0 c1] [pc' c0' c1'] s
    (a & z & ->) (a' & z' & H).
  pose proof (f_equal vm_regs H) as Hr. cbn [cm2_boundary_s] in Hr.
  inversion Hr. reflexivity.
Qed.

Theorem cm2_uniform_interpreter_run_simulation : forall p width c c' s,
  cm2_program_fits width p ->
  cm2_run p c c' ->
  cm2_rep (encode_cm2_program width p) width c s ->
  exists fuel s',
    run_vm_u fuel cm2_interpreter_program s = s' /\
    cm2_rep (encode_cm2_program width p) width c' s'.
Proof.
  intros p width c c' s Hfit Hrun.
  revert s. induction Hrun as [c|c i c1 c2 Hnth Hstep Htail IH]; intros s Hrep.
  - exists 0, s. split; [reflexivity|exact Hrep].
  - assert (Hpc : c.(cc_pc) < length p).
    { apply nth_error_Some. rewrite Hnth. discriminate. }
    assert (Hword : cm2_word (encode_cm2_program width p) width c.(cc_pc) =
                    encode_cm2_instr i).
    { rewrite encode_cm2_program_fetch by assumption.
      apply nth_error_nth with (d := CM2_Halt) in Hnth. rewrite Hnth. reflexivity. }
    destruct (cm2_uniform_interpreter_simulation
      (encode_cm2_program width p) width c s i c1 Hrep Hword Hstep)
      as (s1 & Hpos & Hone & Hrep1).
    destruct (IH s1 Hrep1) as (fuel2 & s2 & Htwo & Hrep2).
    exists (cm2_host_steps i c + fuel2), s2. split.
    + rewrite run_vm_u_split, Hone. exact Htwo.
    + exact Hrep2.
Qed.

Inductive cm2_halts (p : list CM2InstrU) (start : CM2ConfigU)
    : CM2ConfigU -> Prop :=
| cm2_halts_explicit : forall final,
    cm2_run p start final ->
    nth_error p final.(cc_pc) = Some CM2_Halt ->
    cm2_halts p start final
| cm2_halts_falloff : forall final,
    cm2_run p start final ->
    nth_error p final.(cc_pc) = None ->
    cm2_halts p start final.

(** Actual host executions segmented only at interpreter boundaries.  The
    constructor records the instruction found in encoded guest data and
    the resulting represented boundary, but does not assume a guest step. *)
Inductive interpreter_boundary_run (p : list CM2InstrU) (width : nat)
    : CM2ConfigU -> VMState -> CM2ConfigU -> VMState -> Prop :=
| interpreter_boundary_refl : forall c s,
    cm2_rep (encode_cm2_program width p) width c s ->
    interpreter_boundary_run p width c s c s
| interpreter_boundary_step : forall c s c1 s1 c2 s2 i,
    cm2_rep (encode_cm2_program width p) width c s ->
    nth_error p c.(cc_pc) = Some i ->
    i <> CM2_Halt ->
    run_vm_u (cm2_host_steps i c) cm2_interpreter_program s = s1 ->
    cm2_rep (encode_cm2_program width p) width c1 s1 ->
    interpreter_boundary_run p width c1 s1 c2 s2 ->
    interpreter_boundary_run p width c s c2 s2.

Theorem interpreter_boundary_run_sound : forall p width c s c' s',
  cm2_program_fits width p ->
  interpreter_boundary_run p width c s c' s' ->
  cm2_run p c c'.
Proof.
  intros p width c s c' s' Hfit Hhost.
  induction Hhost as [c s Hrep|c s c1 s1 c2 s2 i Hrep Hnth Hnhalt Hactual Hrep1 Htail IH].
  - constructor.
  - assert (Hpc : c.(cc_pc) < length p).
    { apply nth_error_Some. rewrite Hnth. discriminate. }
    assert (Hword : cm2_word (encode_cm2_program width p) width c.(cc_pc) =
                    encode_cm2_instr i).
    { rewrite encode_cm2_program_fetch by assumption.
      apply nth_error_nth with (d := CM2_Halt) in Hnth. rewrite Hnth. reflexivity. }
    assert (Hex : exists expected, cm2_step_instr i c = Some expected).
    { destruct i; try contradiction; destruct c as [gpc cnt0 cnt1];
        cbn [cm2_step_instr]; try (eexists; reflexivity);
        destruct Nat.eqb; eexists; reflexivity. }
    destruct Hex as [expected Hstep].
    destruct (cm2_uniform_interpreter_simulation
      (encode_cm2_program width p) width c s i expected Hrep Hword Hstep)
      as (se & Hpos & Hexpected & Hrepe).
    rewrite Hactual in Hexpected. subst se.
    assert (Hc : c1 = expected)
      by (eapply cm2_rep_config_unique; [exact Hrep1|exact Hrepe]). subst expected.
    econstructor; eauto.
Qed.

Theorem interpreter_boundary_run_complete : forall p width c c' s,
  cm2_program_fits width p ->
  cm2_run p c c' ->
  cm2_rep (encode_cm2_program width p) width c s ->
  exists s', interpreter_boundary_run p width c s c' s'.
Proof.
  intros p width c c' s Hfit Hrun. revert s.
  induction Hrun as [c|c i c1 c2 Hnth Hstep Htail IH]; intros s Hrep.
  - exists s. constructor. exact Hrep.
  - assert (Hpc : c.(cc_pc) < length p).
    { apply nth_error_Some. rewrite Hnth. discriminate. }
    assert (Hword : cm2_word (encode_cm2_program width p) width c.(cc_pc) =
                    encode_cm2_instr i).
    { rewrite encode_cm2_program_fetch by assumption.
      apply nth_error_nth with (d := CM2_Halt) in Hnth. rewrite Hnth. reflexivity. }
    destruct (cm2_uniform_interpreter_simulation
      (encode_cm2_program width p) width c s i c1 Hrep Hword Hstep)
      as (s1 & Hpos & Hone & Hrep1).
    destruct (IH s1 Hrep1) as [s2 Hrest]. exists s2.
    econstructor; eauto. intro Heq. subst i. cbn [cm2_step_instr] in Hstep. discriminate.
Qed.

Lemma interpreter_one_boundary_sound : forall p width c s c1 s1 i,
  cm2_program_fits width p ->
  cm2_rep (encode_cm2_program width p) width c s ->
  nth_error p c.(cc_pc) = Some i -> i <> CM2_Halt ->
  run_vm_u (cm2_host_steps i c) cm2_interpreter_program s = s1 ->
  cm2_rep (encode_cm2_program width p) width c1 s1 ->
  cm2_step_instr i c = Some c1.
Proof.
  intros p width c s c1 s1 i Hfit Hrep Hnth Hnhalt Hactual Hrep1.
  assert (Hpc : c.(cc_pc) < length p).
  { apply nth_error_Some. rewrite Hnth. discriminate. }
  assert (Hword : cm2_word (encode_cm2_program width p) width c.(cc_pc) =
                  encode_cm2_instr i).
  { rewrite encode_cm2_program_fetch by assumption.
    apply nth_error_nth with (d := CM2_Halt) in Hnth. rewrite Hnth. reflexivity. }
  assert (Hex : exists expected, cm2_step_instr i c = Some expected).
  { destruct i; try contradiction; destruct c as [gpc cnt0 cnt1];
      cbn [cm2_step_instr]; try (eexists; reflexivity);
      destruct Nat.eqb; eexists; reflexivity. }
  destruct Hex as [expected Hstep].
  destruct (cm2_uniform_interpreter_simulation
    (encode_cm2_program width p) width c s i expected Hrep Hword Hstep)
    as (se & Hpos & Hexpected & Hrepe).
  rewrite Hactual in Hexpected. subst se.
  assert (c1 = expected) by (eapply cm2_rep_config_unique; eauto). subst expected.
  exact Hstep.
Qed.

Inductive interpreter_boundary_run_n (p : list CM2InstrU) (width : nat)
    : nat -> CM2ConfigU -> VMState -> CM2ConfigU -> VMState -> Prop :=
| interpreter_boundary_n_zero : forall c s,
    cm2_rep (encode_cm2_program width p) width c s ->
    interpreter_boundary_run_n p width 0 c s c s
| interpreter_boundary_n_succ : forall n c s c1 s1 c2 s2 i,
    cm2_rep (encode_cm2_program width p) width c s ->
    nth_error p c.(cc_pc) = Some i -> i <> CM2_Halt ->
    run_vm_u (cm2_host_steps i c) cm2_interpreter_program s = s1 ->
    cm2_rep (encode_cm2_program width p) width c1 s1 ->
    interpreter_boundary_run_n p width n c1 s1 c2 s2 ->
    interpreter_boundary_run_n p width (S n) c s c2 s2.

Theorem interpreter_boundary_run_n_sound : forall p width n c s c' s',
  cm2_program_fits width p ->
  interpreter_boundary_run_n p width n c s c' s' ->
  cm2_run_n p n c c'.
Proof.
  intros p width n c s c' s' Hfit Hrun. induction Hrun.
  - constructor.
  - econstructor; [exact H0| |exact IHHrun].
    eapply interpreter_one_boundary_sound; eauto.
Qed.

Theorem interpreter_boundary_run_n_complete : forall p width n c c' s,
  cm2_program_fits width p -> cm2_run_n p n c c' ->
  cm2_rep (encode_cm2_program width p) width c s ->
  exists s', interpreter_boundary_run_n p width n c s c' s'.
Proof.
  intros p width n c c' s Hfit Hrun. revert s.
  induction Hrun as [c|n c i c1 c2 Hnth Hstep Htail IH]; intros s Hrep.
  - exists s. constructor. exact Hrep.
  - assert (Hpc : c.(cc_pc) < length p).
    { apply nth_error_Some. rewrite Hnth. discriminate. }
    assert (Hword : cm2_word (encode_cm2_program width p) width c.(cc_pc) =
                    encode_cm2_instr i).
    { rewrite encode_cm2_program_fetch by assumption.
      apply nth_error_nth with (d := CM2_Halt) in Hnth. rewrite Hnth. reflexivity. }
    destruct (cm2_uniform_interpreter_simulation
      (encode_cm2_program width p) width c s i c1 Hrep Hword Hstep)
      as (s1 & Hpos & Hone & Hrep1).
    destruct (IH s1 Hrep1) as [s2 Hrest]. exists s2.
    econstructor; eauto. intro Heq. subst i. cbn [cm2_step_instr] in Hstep. discriminate.
Qed.

Definition interpreter_diverges (ambient : VMState) (p : list CM2InstrU)
    (width : nat) (start : CM2ConfigU) : Prop :=
  forall n, exists c s,
    interpreter_boundary_run_n p width n start
      (cm2_config_encoding ambient p width start) c s.

Theorem cm2_uniform_interpreter_divergence : forall ambient p width start,
  cm2_program_fits width p ->
  (cm2_diverges p start <-> interpreter_diverges ambient p width start).
Proof.
  intros ambient p width start Hfit. split.
  - intros Hdiv n. destruct (Hdiv n) as [c Hrun].
    destruct (interpreter_boundary_run_n_complete p width n start c
      (cm2_config_encoding ambient p width start) Hfit Hrun) as [s Hhost].
    { unfold cm2_config_encoding. apply cm2_boundary_is_rep. }
    exists c, s. exact Hhost.
  - intros Hdiv n. destruct (Hdiv n) as (c & s & Hhost).
    exists c. eapply interpreter_boundary_run_n_sound; eauto.
Qed.

Definition interpreter_produces (ambient : VMState) (p : list CM2InstrU)
    (width : nat) (start final : CM2ConfigU) : Prop :=
  exists boundary terminal,
    interpreter_boundary_run p width start
      (cm2_config_encoding ambient p width start) final boundary /\
    (nth_error p final.(cc_pc) = Some CM2_Halt \/ nth_error p final.(cc_pc) = None) /\
    run_vm_u 12 cm2_interpreter_program boundary = terminal /\
    cm2_halt_rep (encode_cm2_program width p) width final terminal.

Theorem cm2_uniform_interpreter_correct_sound : forall ambient p width start final,
  cm2_program_fits width p ->
  interpreter_produces ambient p width start final ->
  cm2_halts p start final.
Proof.
  intros ambient p width start final Hfit
    (boundary & terminal & Hrun & [Hhalt|Hfall] & Hactual & Hterminal).
  - apply cm2_halts_explicit; [eapply interpreter_boundary_run_sound; eauto|exact Hhalt].
  - apply cm2_halts_falloff; [eapply interpreter_boundary_run_sound; eauto|exact Hfall].
Qed.

Theorem cm2_uniform_interpreter_correct : forall ambient p width start final,
  cm2_program_fits width p ->
  (cm2_halts p start final <->
   interpreter_produces ambient p width start final).
Proof.
  intros ambient p width start final Hfit. split.
  - intro Hhalt.
    assert (Hrun : cm2_run p start final).
    { inversion Hhalt; assumption. }
    destruct (interpreter_boundary_run_complete p width start final
      (cm2_config_encoding ambient p width start) Hfit Hrun) as [boundary Hboundary].
    { unfold cm2_config_encoding. apply cm2_boundary_is_rep. }
    assert (Hrep : cm2_rep (encode_cm2_program width p) width final boundary).
    { clear Hhalt Hrun. induction Hboundary; assumption. }
    destruct Hrep as (ambient' & z & ->).
    exists (cm2_boundary_s ambient' (encode_cm2_program width p) width final z),
      (run_vm_u 12 cm2_interpreter_program
        (cm2_boundary_s ambient' (encode_cm2_program width p) width final z)).
    split; [exact Hboundary|]. split.
    + inversion Hhalt; [left|right]; assumption.
    + split; [reflexivity|]. apply cm2_rep_halt.
      inversion Hhalt as [f Hr Hnth|f Hr Hnone]; subst f.
      * assert (Hpc : final.(cc_pc) < length p).
        { apply nth_error_Some. rewrite Hnth. discriminate. }
        rewrite encode_cm2_program_fetch by assumption.
        apply nth_error_nth with (d := CM2_Halt) in Hnth. rewrite Hnth. reflexivity.
      * apply encode_cm2_program_fetch_outside; [exact Hfit|].
        apply nth_error_None. exact Hnone.
  - apply cm2_uniform_interpreter_correct_sound. exact Hfit.
Qed.

Theorem cm2_uniform_interpreter_correct_complete : forall ambient p width start final,
  cm2_program_fits width p ->
  cm2_halts p start final ->
  exists fuel s_boundary s_final,
    run_vm_u fuel cm2_interpreter_program
      (cm2_boundary ambient (encode_cm2_program width p) width start) = s_boundary /\
    cm2_rep (encode_cm2_program width p) width final s_boundary /\
    run_vm_u 12 cm2_interpreter_program s_boundary = s_final /\
    cm2_halt_rep (encode_cm2_program width p) width final s_final.
Proof.
  intros ambient p width start final Hfit Hhalt.
  inversion Hhalt as [f Hrun Hnth|f Hrun Hnone]; subst f.
  - destruct (cm2_uniform_interpreter_run_simulation p width start final
      (cm2_boundary ambient (encode_cm2_program width p) width start)
      Hfit Hrun (cm2_boundary_is_rep _ _ _ _)) as (fuel & sb & Hrunhost & Hrep).
    destruct Hrep as (ambient' & z & ->).
    assert (Hpc : final.(cc_pc) < length p).
    { apply nth_error_Some. rewrite Hnth. discriminate. }
    assert (Hword : cm2_word (encode_cm2_program width p) width final.(cc_pc) = 0).
    { rewrite encode_cm2_program_fetch by assumption.
      apply nth_error_nth with (d := CM2_Halt) in Hnth. rewrite Hnth. reflexivity. }
    exists fuel,
      (cm2_boundary_s ambient' (encode_cm2_program width p) width final z),
      (run_vm_u 12 cm2_interpreter_program
        (cm2_boundary_s ambient' (encode_cm2_program width p) width final z)).
    split; [exact Hrunhost|]. split.
    + exists ambient', z. reflexivity.
    + split; [reflexivity|]. apply cm2_rep_halt. exact Hword.
  - destruct (cm2_uniform_interpreter_run_simulation p width start final
      (cm2_boundary ambient (encode_cm2_program width p) width start)
      Hfit Hrun (cm2_boundary_is_rep _ _ _ _)) as (fuel & sb & Hrunhost & Hrep).
    destruct Hrep as (ambient' & z & ->).
    assert (Hpc : length p <= final.(cc_pc)) by (apply nth_error_None; exact Hnone).
    assert (Hword : cm2_word (encode_cm2_program width p) width final.(cc_pc) = 0)
      by (apply encode_cm2_program_fetch_outside; assumption).
    exists fuel,
      (cm2_boundary_s ambient' (encode_cm2_program width p) width final z),
      (run_vm_u 12 cm2_interpreter_program
        (cm2_boundary_s ambient' (encode_cm2_program width p) width final z)).
    split; [exact Hrunhost|]. split.
    + exists ambient', z. reflexivity.
    + split; [reflexivity|]. apply cm2_rep_halt. exact Hword.
Qed.

(** Premise-free public forms: the executable width selector makes the data
    encoding applicable to every finite guest program. *)
Theorem cm2_uniform_interpreter_simulation_total : forall ambient p c i c',
  nth_error p c.(cc_pc) = Some i ->
  cm2_step_instr i c = Some c' ->
  exists s',
    0 < cm2_host_steps i c /\
    run_vm_u (cm2_host_steps i c) cm2_interpreter_program
      (cm2_total_config_encoding ambient p c) = s' /\
    cm2_rep
      (encode_cm2_program (cm2_encoding_width p) p)
      (cm2_encoding_width p) c' s'.
Proof.
  intros ambient p c i c' Hnth Hstep.
  assert (Hpc : c.(cc_pc) < length p).
  { apply nth_error_Some. rewrite Hnth. discriminate. }
  assert (Hword :
    cm2_word (encode_cm2_program (cm2_encoding_width p) p)
      (cm2_encoding_width p) c.(cc_pc) = encode_cm2_instr i).
  { rewrite encode_cm2_program_fetch.
    - apply nth_error_nth with (d := CM2_Halt) in Hnth. rewrite Hnth. reflexivity.
    - apply cm2_program_fits_encoding_width.
    - exact Hpc. }
  unfold cm2_total_config_encoding, cm2_config_encoding.
  eapply cm2_uniform_interpreter_simulation.
  - apply cm2_boundary_is_rep.
  - exact Hword.
  - exact Hstep.
Qed.

Theorem cm2_uniform_interpreter_divergence_total : forall ambient p start,
  cm2_diverges p start <->
  interpreter_diverges ambient p (cm2_encoding_width p) start.
Proof.
  intros. apply cm2_uniform_interpreter_divergence.
  apply cm2_program_fits_encoding_width.
Qed.

Theorem cm2_uniform_interpreter_correct_total : forall ambient p start final,
  cm2_halts p start final <->
  interpreter_produces ambient p (cm2_encoding_width p) start final.
Proof.
  intros. apply cm2_uniform_interpreter_correct.
  apply cm2_program_fits_encoding_width.
Qed.

Theorem cm2_uniform_interpreter_correct_complete_total : forall ambient p start final,
  cm2_halts p start final ->
  exists fuel s_boundary s_final,
    run_vm_u fuel cm2_interpreter_program
      (cm2_total_config_encoding ambient p start) = s_boundary /\
    cm2_rep
      (encode_cm2_program (cm2_encoding_width p) p)
      (cm2_encoding_width p) final s_boundary /\
    run_vm_u 12 cm2_interpreter_program s_boundary = s_final /\
    cm2_halt_rep
      (encode_cm2_program (cm2_encoding_width p) p)
      (cm2_encoding_width p) final s_final.
Proof.
  intros ambient p start final Hhalt.
  unfold cm2_total_config_encoding, cm2_config_encoding.
  eapply cm2_uniform_interpreter_correct_complete.
  - apply cm2_program_fits_encoding_width.
  - exact Hhalt.
Qed.

Theorem total_encoding_never_malformed_opcode : forall p pc,
  pc < length p ->
  u_and
    (cm2_word
      (encode_cm2_program (cm2_encoding_width p) p)
      (cm2_encoding_width p) pc) 7 <= 4.
Proof.
  intros p pc Hpc. rewrite encode_cm2_program_fetch.
  - apply encode_cm2_opcode_valid.
  - apply cm2_program_fits_encoding_width.
  - exact Hpc.
Qed.

(** Raw host observations: no guest trace or segmentation is assumed. *)
Definition cm2_result (s : VMState) : CM2ConfigU :=
  {| cc_pc := read_reg s 12; cc_c0 := read_reg s 11; cc_c1 := read_reg s 10 |}.

Lemma cm2_halt_rep_result : forall code width c s,
  cm2_halt_rep code width c s -> cm2_result s = c.
Proof.
  intros code width [pc c0 c1] s (a & z & ->).
  unfold cm2_result, read_reg, reg_index, REG_COUNT. reflexivity.
Qed.

Lemma cm2_terminal_stable : forall s fuel,
  s.(vm_pc) = 60 -> run_vm_u fuel cm2_interpreter_program s = s.
Proof.
  intros s [|fuel] Hpc; [reflexivity|]. cbn [run_vm_u].
  rewrite Hpc. reflexivity.
Qed.

Lemma cm2_rep_not_terminal : forall code width c s,
  cm2_rep code width c s -> s.(vm_pc) <> 60.
Proof. intros code width c s (a & z & ->). discriminate. Qed.

Lemma cm2_terminal_compare_fuels : forall s n k,
  (run_vm_u n cm2_interpreter_program s).(vm_pc) = 60 ->
  (run_vm_u k cm2_interpreter_program s).(vm_pc) = 60 ->
  run_vm_u n cm2_interpreter_program s =
  run_vm_u k cm2_interpreter_program s.
Proof.
  intros s n k Hn Hk. destruct (le_dec n k).
  - replace k with (n + (k-n)) by lia. rewrite run_vm_u_split.
    symmetry. apply cm2_terminal_stable. exact Hn.
  - replace n with (k + (n-k)) by lia. rewrite run_vm_u_split.
    apply cm2_terminal_stable. exact Hk.
Qed.

Theorem cm2_uniform_interpreter_raw_sound : forall fuel p width start s,
  cm2_program_fits width p ->
  cm2_rep (encode_cm2_program width p) width start s ->
  (run_vm_u fuel cm2_interpreter_program s).(vm_pc) = 60 ->
  cm2_halts p start (cm2_result (run_vm_u fuel cm2_interpreter_program s)) /\
  cm2_halted (run_vm_u fuel cm2_interpreter_program s).
Proof.
  intro fuel. induction fuel using lt_wf_ind.
  intros p width start s Hfit Hrep Hterminal.
  destruct (nth_error p start.(cc_pc)) as [i|] eqn:Hnth.
  - assert (Hpc : start.(cc_pc) < length p).
    { apply nth_error_Some. rewrite Hnth. discriminate. }
    assert (Hword : cm2_word (encode_cm2_program width p) width start.(cc_pc) =
                    encode_cm2_instr i).
    { rewrite encode_cm2_program_fetch by assumption.
      apply nth_error_nth with (d := CM2_Halt) in Hnth. rewrite Hnth. reflexivity. }
    destruct i as [| | |target|target].
    { destruct Hrep as (a & z & ->).
      pose proof (cm2_rep_halt a _ _ start z Hword) as Hr.
      pose proof (cm2_halt_rep_observed _ _ _ _ Hr) as Ho.
      destruct Ho as [Hpcend Hstatus]. rewrite cm2_interpreter_program_length in Hpcend.
      pose proof (cm2_terminal_compare_fuels _ _ _ Hterminal Hpcend) as Heq.
      rewrite Heq. split.
      * rewrite (cm2_halt_rep_result _ _ _ _ Hr).
        apply cm2_halts_explicit; [constructor|exact Hnth].
      * apply cm2_halt_rep_observed in Hr. exact Hr. }
    all: assert (Hex : exists next, cm2_step_instr
      ltac:(match type of Hword with _ = encode_cm2_instr ?i => exact i end)
      start = Some next) by
      (cbn [cm2_step_instr]; try (eexists; reflexivity);
       destruct Nat.eqb; eexists; reflexivity).
    all: destruct Hex as [next Hstep].
    all: destruct (cm2_uniform_interpreter_simulation _ _ _ _ _ _ Hrep Hword Hstep)
      as (s1 & Hpos & Hexec & Hr1).
    all: match type of Hpos with 0 < ?k => set (steps := k) in * end.
    all: assert (Hk : steps <= fuel).
    all: try (destruct (le_dec (steps) fuel); [assumption|];
      exfalso; assert (E : run_vm_u (steps) cm2_interpreter_program s =
                            run_vm_u fuel cm2_interpreter_program s) by
        (replace (steps) with
          (fuel + (steps - fuel)) by lia;
         rewrite run_vm_u_split; apply cm2_terminal_stable; exact Hterminal);
      rewrite Hexec in E; apply (cm2_rep_not_terminal _ _ _ _ Hr1);
      rewrite E; exact Hterminal).
    all: assert (Erun : run_vm_u fuel cm2_interpreter_program s =
      run_vm_u (fuel - steps)
        cm2_interpreter_program s1) by
      (replace fuel with (steps + (fuel - steps))
        at 1 by lia; rewrite run_vm_u_split, Hexec; reflexivity).
    all: rewrite Erun in Hterminal |- *.
    all: destruct (H (fuel - steps) ltac:(lia) p width next s1 Hfit Hr1 Hterminal) as [Hhalt Hobs].
    all: split; [inversion Hhalt; subst;
      [apply cm2_halts_explicit|apply cm2_halts_falloff];
      try (econstructor; eauto); assumption|exact Hobs].
  - assert (Hword : cm2_word (encode_cm2_program width p) width start.(cc_pc) = 0).
    { apply encode_cm2_program_fetch_outside; [exact Hfit|].
      apply nth_error_None. exact Hnth. }
    destruct Hrep as (a & z & ->).
    pose proof (cm2_rep_halt a _ _ start z Hword) as Hr.
    pose proof (cm2_halt_rep_observed _ _ _ _ Hr) as Ho.
    destruct Ho as [Hpcend Hstatus]. rewrite cm2_interpreter_program_length in Hpcend.
    pose proof (cm2_terminal_compare_fuels _ _ _ Hterminal Hpcend) as Heq.
    rewrite Heq. split.
    + rewrite (cm2_halt_rep_result _ _ _ _ Hr).
      apply cm2_halts_falloff; [constructor|exact Hnth].
    + apply cm2_halt_rep_observed in Hr. exact Hr.
Qed.

Definition interpreter_raw_produces (ambient : VMState) (p : list CM2InstrU)
    (start final : CM2ConfigU) : Prop :=
  exists fuel,
    cm2_halted (run_vm_u fuel cm2_interpreter_program
      (cm2_total_config_encoding ambient p start)) /\
    cm2_result (run_vm_u fuel cm2_interpreter_program
      (cm2_total_config_encoding ambient p start)) = final.

Theorem cm2_uniform_interpreter_raw_correct_total : forall ambient p start final,
  cm2_halts p start final <-> interpreter_raw_produces ambient p start final.
Proof.
  intros ambient p start final. split.
  - intro Hhalt.
    destruct (cm2_uniform_interpreter_correct_complete_total ambient p start final Hhalt)
      as (fuel & sb & sf & Hrun & Hrep & Hlast & Hfinal).
    exists (fuel + 12). rewrite run_vm_u_split, Hrun, Hlast. split.
    + eapply cm2_halt_rep_observed; eauto.
    + eapply cm2_halt_rep_result; eauto.
  - intros (fuel & Hhalt & Hresult).
    destruct (cm2_uniform_interpreter_raw_sound fuel p (cm2_encoding_width p) start
      (cm2_total_config_encoding ambient p start)) as [Hguest Hhost].
    + apply cm2_program_fits_encoding_width.
    + unfold cm2_total_config_encoding, cm2_config_encoding.
      apply cm2_boundary_is_rep.
    + destruct Hhalt as [Hpc _]. rewrite cm2_interpreter_program_length in Hpc.
      exact Hpc.
    + rewrite Hresult in Hguest. exact Hguest.
Qed.

Theorem cm2_uniform_interpreter_raw_never_malformed : forall ambient p start fuel,
  ~ cm2_malformed (run_vm_u fuel cm2_interpreter_program
      (cm2_total_config_encoding ambient p start)).
Proof.
  intros ambient p start fuel Hbad.
  destruct (cm2_uniform_interpreter_raw_sound fuel p (cm2_encoding_width p) start
    (cm2_total_config_encoding ambient p start)) as [Hguest Hhost].
  - apply cm2_program_fits_encoding_width.
  - unfold cm2_total_config_encoding, cm2_config_encoding.
    apply cm2_boundary_is_rep.
  - destruct Hbad as [Hpc _]. rewrite cm2_interpreter_program_length in Hpc.
    exact Hpc.
  - eapply cm2_halt_malformed_disjoint; eauto.
Qed.

Lemma cm2_run_n_prefix : forall p n c final,
  cm2_run_n p n c final -> forall k, k <= n ->
  exists mid, cm2_run_n p k c mid.
Proof.
  intros p n c final Hr. induction Hr; intros k Hk.
  - assert (k = 0) by lia. subst. eexists. constructor.
  - destruct k as [|k]; [eexists; constructor|].
    destruct (IHHr k ltac:(lia)) as [mid Hmid].
    exists mid. econstructor; eauto.
Qed.

Lemma cm2_halts_finite_bound : forall p c final,
  cm2_halts p c final ->
  exists n, forall c', ~ cm2_run_n p n c c'.
Proof.
  intros p c final Hhalt.
  assert (Hr : cm2_run p c final) by (inversion Hhalt; assumption).
  assert (Hend : nth_error p final.(cc_pc) = Some CM2_Halt \/
                 nth_error p final.(cc_pc) = None) by
    (inversion Hhalt; [left|right]; assumption).
  clear Hhalt. induction Hr as [c|c i c1 c2 Hnth Hstep Htail IH].
  - exists 1. intros c' Hn. inversion Hn; subst.
    destruct Hend as [He|He]; rewrite He in H0; inversion H0; subst.
    discriminate H1.
  - destruct (IH Hend) as [n Hn]. exists (S n). intros c' Hrun.
    inversion Hrun; subst.
    match goal with
    | Hi : nth_error p (cc_pc c) = Some ?j,
      Hs : cm2_step_instr ?j c = Some ?next |- _ =>
        rewrite Hnth in Hi; inversion Hi; subst j;
        rewrite Hstep in Hs; inversion Hs; subst next
    end.
    eapply Hn; eauto.
Qed.

Lemma cm2_halts_not_diverges : forall p c final,
  cm2_halts p c final -> ~ cm2_diverges p c.
Proof.
  intros p c final Hhalt Hdiv.
  destruct (cm2_halts_finite_bound _ _ _ Hhalt) as [n Hn].
  destruct (Hdiv n) as [c' Hr]. eapply Hn; eauto.
Qed.

Lemma cm2_no_halt_prefixes : forall p start,
  (forall final, ~ cm2_halts p start final) -> cm2_diverges p start.
Proof.
  intros p start Hnone n. revert start Hnone.
  induction n as [|n IH]; intros start Hnone.
  - exists start. constructor.
  - destruct (nth_error p start.(cc_pc)) as [i|] eqn:Hnth.
    2: { exfalso. apply (Hnone start). apply cm2_halts_falloff; [constructor|exact Hnth]. }
    assert (Hex : exists next, cm2_step_instr i start = Some next).
    { destruct i; cbn [cm2_step_instr]; try (eexists; reflexivity);
        try (destruct Nat.eqb; eexists; reflexivity).
      exfalso. apply (Hnone start). apply cm2_halts_explicit; [constructor|exact Hnth]. }
    destruct Hex as [next Hstep].
    destruct (IH next) as [final Hrun].
    + intros final Hhalt. apply (Hnone final). inversion Hhalt; subst;
        [apply cm2_halts_explicit|apply cm2_halts_falloff];
        try (econstructor; eauto); assumption.
    + exists final. econstructor; eauto.
Qed.

(** Infinite execution means arbitrarily many available host steps, not
    exhaustion of any particular fuel budget.  From encoded boundaries,
    terminal PC 60 is the sole exit, as the raw soundness proof certifies
    every such exit and step simulation supplies every live guest prefix. *)
Definition interpreter_raw_diverges (ambient : VMState) (p : list CM2InstrU)
    (start : CM2ConfigU) : Prop :=
  forall fuel, (run_vm_u fuel cm2_interpreter_program
    (cm2_total_config_encoding ambient p start)).(vm_pc) <> 60.

Theorem cm2_uniform_interpreter_raw_divergence_total : forall ambient p start,
  cm2_diverges p start <-> interpreter_raw_diverges ambient p start.
Proof.
  intros ambient p start. split.
  - intros Hdiv fuel Hterminal.
    destruct (cm2_uniform_interpreter_raw_sound fuel p (cm2_encoding_width p) start
      (cm2_total_config_encoding ambient p start)) as [Hhalt Hobs].
    + apply cm2_program_fits_encoding_width.
    + unfold cm2_total_config_encoding, cm2_config_encoding.
      apply cm2_boundary_is_rep.
    + exact Hterminal.
    + eapply cm2_halts_not_diverges; eauto.
  - intro Hdiv. apply cm2_no_halt_prefixes. intros final Hhalt.
    apply (proj1 (cm2_uniform_interpreter_raw_correct_total ambient p start final)) in Hhalt.
    destruct Hhalt as (fuel & [Hpc Hstatus] & Hresult).
    rewrite cm2_interpreter_program_length in Hpc. exact (Hdiv fuel Hpc).
Qed.

(** Structural/ledger observations are independent of the guest registers
    and host scratch.  Every raw host prefix preserves this full frame. *)
Definition cm2_ambient (s : VMState) : VMState :=
  {| vm_graph := s.(vm_graph); vm_csrs := s.(vm_csrs);
     vm_regs := []; vm_mem := s.(vm_mem); vm_pc := 0;
     vm_mu := s.(vm_mu); vm_mu_tensor := s.(vm_mu_tensor);
     vm_err := s.(vm_err); vm_logic_acc := s.(vm_logic_acc);
     vm_mstatus := s.(vm_mstatus); vm_witness := s.(vm_witness);
     vm_certified := s.(vm_certified) |}.

Lemma cm2_instruction_frame_and_pc :
  Forall (fun i => forall s, s.(vm_pc) < 60 ->
    cm2_ambient (vm_apply_u s i) = cm2_ambient s /\
    (vm_apply_u s i).(vm_pc) <= 60) cm2_interpreter_program.
Proof.
  apply Forall_forall. intros i Hi.
  cbn [cm2_interpreter_program In] in Hi.
  repeat destruct Hi as [<-|Hi]; try contradiction; intros s Hpc;
    cbn [vm_apply_u];
    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b eqn:?
    end;
    unfold cm2_ambient, VMStep.advance_state_rm, VMStep.advance_state,
      VMStep.jump_state, VMStep.apply_cost, VMStep.instruction_cost;
    cbn; rewrite ?Nat.add_0_r; split; try reflexivity; lia.
Qed.

Theorem cm2_uniform_interpreter_raw_frame : forall fuel s,
  cm2_ambient (run_vm_u fuel cm2_interpreter_program s) = cm2_ambient s.
Proof.
  induction fuel as [|fuel IH]; intro s; [reflexivity|]. cbn [run_vm_u].
  destruct (nth_error cm2_interpreter_program s.(vm_pc)) as [i|] eqn:Hi;
    [|reflexivity]. rewrite IH.
  assert (Hpc : s.(vm_pc) < 60).
  { rewrite <- cm2_interpreter_program_length. apply nth_error_Some.
    rewrite Hi. discriminate. }
  pose proof cm2_instruction_frame_and_pc as H.
  rewrite Forall_forall in H.
  apply (proj1 (H i (nth_error_In _ _ Hi) s Hpc)).
Qed.

Theorem cm2_uniform_interpreter_raw_pc_bound : forall fuel s,
  s.(vm_pc) <= 60 -> (run_vm_u fuel cm2_interpreter_program s).(vm_pc) <= 60.
Proof.
  induction fuel as [|fuel IH]; intros s Hpc; [exact Hpc|]. cbn [run_vm_u].
  destruct (nth_error cm2_interpreter_program s.(vm_pc)) as [i|] eqn:Hi;
    [|exact Hpc]. apply IH.
  assert (Hlive : s.(vm_pc) < 60).
  { rewrite <- cm2_interpreter_program_length. apply nth_error_Some.
    rewrite Hi. discriminate. }
  pose proof cm2_instruction_frame_and_pc as H.
  rewrite Forall_forall in H.
  apply (proj2 (H i (nth_error_In _ _ Hi) s Hlive)).
Qed.

Theorem cm2_uniform_interpreter_divergence_live_prefixes : forall ambient p start,
  cm2_diverges p start <->
  forall fuel, exists i,
    nth_error cm2_interpreter_program
      (run_vm_u fuel cm2_interpreter_program
        (cm2_total_config_encoding ambient p start)).(vm_pc) = Some i.
Proof.
  intros ambient p start. rewrite (cm2_uniform_interpreter_raw_divergence_total ambient p start).
  split.
  - intros Hdiv fuel. destruct (nth_error cm2_interpreter_program
      (run_vm_u fuel cm2_interpreter_program
        (cm2_total_config_encoding ambient p start)).(vm_pc)) as [i|] eqn:Hi.
    + eauto.
    + apply nth_error_None in Hi. rewrite cm2_interpreter_program_length in Hi.
      pose proof (cm2_uniform_interpreter_raw_pc_bound fuel
        (cm2_total_config_encoding ambient p start) ltac:(change (0 <= 60); lia)) as Hb.
      exfalso. apply (Hdiv fuel). lia.
  - intros Hlive fuel Hpc. destruct (Hlive fuel) as [i Hi].
    rewrite Hpc in Hi. discriminate.
Qed.
