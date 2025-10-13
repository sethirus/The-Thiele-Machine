(* ================================================================= *)
(* Simulation: TM in Thiele Machine                                  *)
(* ================================================================= *)

From Coq Require Import List Arith Lia PeanoNat Bool.
Import ListNotations.

From ThieleMachine.Modular_Proofs Require Import TM_Basics Encoding EncodingBounds.

(* Local definitions to avoid conflicts *)
Record State := {
  pc : nat
}.

Definition ThieleProgram := list nat.

Definition thiele_step (P : ThieleProgram) (s : State) : State :=
  {| pc := S s.(pc) |}.

Fixpoint thiele_run_n (P : ThieleProgram) (s : State) (n : nat) : State :=
  match n with
  | 0 => s
  | S n' => thiele_run_n P (thiele_step P s) n'
  end.

(* ----------------------------------------------------------------- *)
(* Universal TM Simulator Program                                    *)
(* ----------------------------------------------------------------- *)

(* Placeholder for the universal program *)
Parameter utm_prog : ThieleProgram.

(* Encode TM config into Thiele state *)
Definition encode_tm_config (conf : TMConfig) : State :=
  let '(q, tape, head) := conf in {| pc := encode_config q tape head |}.

(* Decode Thiele state into TM config *)
Definition decode_tm_config (s : State) : TMConfig :=
  let '(q, tape, head) := decode_config s.(pc) in (q, tape, head).

Definition tm_config_ok (conf : TMConfig) : Prop :=
  let '(q, tape, head) := conf in digits_ok tape /\ length tape <= SHIFT_LEN /\ head < SHIFT_LEN.

Definition tm_config_tape (conf : TMConfig) : list nat :=
  let '(_, tape, _) := conf in tape.

Definition tm_config_head (conf : TMConfig) : nat :=
  let '(_, _, head) := conf in head.

Lemma tm_config_ok_change_state :
  forall q1 q2 tape head,
    tm_config_ok (q1, tape, head) ->
    tm_config_ok (q2, tape, head).
Proof.
  intros q1 q2 tape head Hok.
  exact Hok.
Qed.

Lemma tm_config_ok_update_write :
  forall q tape head write,
    tm_config_ok (q, tape, head) ->
    write < BASE ->
    tm_config_ok (q, replace_nth tape head write, head).
Proof.
  intros q tape head write Hok Hwrite.
  destruct Hok as [Hdigs [Hlen Hhead]].
  repeat split.
  - apply replace_nth_Forall; assumption.
  - rewrite replace_nth_length. exact Hlen.
  - exact Hhead.
Qed.

Lemma tm_config_ok_update_head :
  forall q tape head head',
    tm_config_ok (q, tape, head) ->
    head' < SHIFT_LEN ->
    tm_config_ok (q, tape, head').
Proof.
  intros q tape head head' Hok Hhead'.
  destruct Hok as [Hdigs [Hlen _]].
  repeat split; try assumption.
Qed.

(* ----------------------------------------------------------------- *)
(* Simulation Lemmas                                                 *)
(* ----------------------------------------------------------------- *)

(* Encoding round-trip *)
Lemma encode_decode_roundtrip : forall conf,
  tm_config_ok conf ->
  decode_tm_config (encode_tm_config conf) = conf.
Proof.
  intros conf Hconf.
  destruct conf as [q [tape head]].
  simpl in *.
  destruct Hconf as [Hdigs [Hlen Hhead]].
  pose proof (EncodingBounds.le_SHIFT_LEN_lt_SHIFT_BIG
                BASE SHIFT_LEN BASE_ge_2 SHIFT_LEN_ge_1
                head (Nat.lt_le_incl _ _ Hhead)) as Hhead_big.
  apply encode_decode_config; auto.
Qed.

(* One-step simulation obligations (to be proven constructively) *)
Record SimulationObligations (tm : TMTransition) := {
  sim_step_preserves_ok :
    forall conf, tm_config_ok conf -> tm_config_ok (tm_step tm conf);
  sim_step_progress :
    forall conf, tm_config_ok conf ->
      thiele_step utm_prog (encode_tm_config conf)
      = encode_tm_config (tm_step tm conf)
}.

Record StepInvariantAssumptions (tm : TMTransition) := {
  step_write_in_base :
    forall conf,
      tm_config_ok conf ->
      let '(q, tape, head) := conf in
      let '(_, write, _) := tm q (nth head tape 0) in
      write < BASE;
  step_head_within_len :
    forall conf,
      tm_config_ok conf ->
      let '(q, tape, head) := conf in
      let '(_, _, move) := tm q (nth head tape 0) in
      let head' := if Nat.eqb move 0 then head
                   else if Nat.eqb move 1 then head + 1
                   else head - 1 in
      head' < SHIFT_LEN
}.

Record StepInvariantBounds (tm : TMTransition) := {
  bounds_write_in_base :
    forall conf,
      tm_config_ok conf ->
      let '(q, tape, head) := conf in
      let '(_, write, _) := tm q (nth head tape 0) in
      write < BASE;
  bounds_head_within_len :
    forall conf,
      tm_config_ok conf ->
      let '(q, tape, head) := conf in
      let '(_, _, move) := tm q (nth head tape 0) in
      let head' := if Nat.eqb move 0 then head
                   else if Nat.eqb move 1 then head + 1
                   else head - 1 in
      head' < SHIFT_LEN
}.

Arguments bounds_write_in_base {tm} _.
Arguments bounds_head_within_len {tm} _.

Definition bounds_to_assumptions (tm : TMTransition)
  (B : StepInvariantBounds tm)
  : StepInvariantAssumptions tm :=
  {| step_write_in_base := bounds_write_in_base B;
     step_head_within_len := bounds_head_within_len B |}.

Lemma step_assumptions_preserve_ok :
  forall tm,
    StepInvariantAssumptions tm ->
    forall conf,
      tm_config_ok conf ->
      tm_config_ok (tm_step tm conf).
Proof.
  intros tm [Hwrite Hhead] [[q tape] head] Hok.
  simpl in *.
  pose proof Hok as Hok_all.
  specialize (Hwrite _ Hok_all).
  specialize (Hhead _ Hok_all).
  unfold tm_step; simpl.
  remember (tm q (nth head tape 0)) as step eqn:Hstep.
  destruct step as [[q' write] move]; simpl in *.
  rewrite Hstep in Hwrite, Hhead.
  set (tape' := replace_nth tape head write).
  set (head' := if Nat.eqb move 0 then head
                else if Nat.eqb move 1 then head + 1 else head - 1).
  pose proof (tm_config_ok_change_state q q' tape head Hok) as Hok_state.
  pose proof (tm_config_ok_update_write q' tape head write Hok_state Hwrite) as Hok_write.
  apply tm_config_ok_update_head with (head':=head').
  - exact Hok_write.
  - exact Hhead.
Qed.

Definition simulation_obligations_of (tm : TMTransition)
  (assm : StepInvariantAssumptions tm)
  (progress : forall conf,
      tm_config_ok conf ->
      thiele_step utm_prog (encode_tm_config conf)
      = encode_tm_config (tm_step tm conf))
  : SimulationObligations tm :=
  {| sim_step_preserves_ok := step_assumptions_preserve_ok tm assm;
     sim_step_progress := progress |}.

Definition simulation_obligations_from_bounds (tm : TMTransition)
  (B : StepInvariantBounds tm)
  (progress : forall conf,
      tm_config_ok conf ->
      thiele_step utm_prog (encode_tm_config conf)
      = encode_tm_config (tm_step tm conf))
  : SimulationObligations tm :=
  simulation_obligations_of tm (bounds_to_assumptions tm B) progress.

Section WithObligations.
  Context (tm : TMTransition).
  Context (Ob : SimulationObligations tm).

  Local Notation step_preserves_ok := (sim_step_preserves_ok tm Ob).
  Local Notation step_progress := (sim_step_progress tm Ob).

  Lemma simulate_one_step_decode_with : forall conf,
    tm_config_ok conf ->
    decode_tm_config (thiele_step utm_prog (encode_tm_config conf)) = tm_step tm conf.
  Proof.
    intros conf Hok.
    rewrite (step_progress conf Hok).
    apply encode_decode_roundtrip.
    apply step_preserves_ok; exact Hok.
  Qed.

  Lemma tm_run_n_preserves_ok_with : forall n cfg,
    tm_config_ok cfg -> tm_config_ok (tm_run_n tm cfg n).
  Proof.
    induction n as [|n IH]; intros cfg Hok; simpl.
    - exact Hok.
    - apply IH.
      apply step_preserves_ok; exact Hok.
  Qed.

  (* Multi-step simulation follows from the one-step equality. *)
Lemma utm_simulation_steps_with : forall n cfg,
    tm_config_ok cfg ->
    decode_tm_config (thiele_run_n utm_prog (encode_tm_config cfg) n) = tm_run_n tm cfg n.
  Proof.
    induction n as [|n IH]; intros cfg Hok; simpl.
    - apply encode_decode_roundtrip; exact Hok.
    - rewrite (step_progress cfg Hok).
      apply IH.
      apply step_preserves_ok; exact Hok.
  Qed.
End WithObligations.

Parameter tm_step_bounds : forall tm, StepInvariantBounds tm.

Parameter tm_progress : forall tm conf,
  tm_config_ok conf ->
  thiele_step utm_prog (encode_tm_config conf) = encode_tm_config (tm_step tm conf).

Definition tm_step_assumptions (tm : TMTransition) : StepInvariantAssumptions tm :=
  bounds_to_assumptions tm (tm_step_bounds tm).

Definition tm_obligations (tm : TMTransition) : SimulationObligations tm :=
  simulation_obligations_of tm (tm_step_assumptions tm) (tm_progress tm).

Definition tm_step_preserves_ok tm :
  forall conf, tm_config_ok conf -> tm_config_ok (tm_step tm conf) :=
  sim_step_preserves_ok tm (tm_obligations tm).

Definition simulate_one_step tm :
  forall conf, tm_config_ok conf ->
    thiele_step utm_prog (encode_tm_config conf) = encode_tm_config (tm_step tm conf) :=
  sim_step_progress tm (tm_obligations tm).

Lemma simulate_one_step_decode : forall tm conf,
  tm_config_ok conf ->
  decode_tm_config (thiele_step utm_prog (encode_tm_config conf)) = tm_step tm conf.
Proof.
  intros tm conf Hok.
  pose (Ob := tm_obligations tm).
  exact (simulate_one_step_decode_with tm Ob conf Hok).
Qed.

Lemma tm_run_n_preserves_ok : forall tm conf n,
  tm_config_ok conf -> tm_config_ok (tm_run_n tm conf n).
Proof.
  intros tm conf n Hok.
  pose (Ob := tm_obligations tm).
  exact (tm_run_n_preserves_ok_with tm Ob conf n Hok).
Qed.

Lemma utm_simulation_steps : forall tm conf n,
  tm_config_ok conf ->
  decode_tm_config (thiele_run_n utm_prog (encode_tm_config conf) n) = tm_run_n tm conf n.
Proof.
  intros tm conf n Hok.
  pose (Ob := tm_obligations tm).
  exact (utm_simulation_steps_with tm Ob conf n Hok).
Qed.

Lemma simulate_one_step_decode_from_bounds :
  forall tm (B : StepInvariantBounds tm)
         (progress : forall conf,
             tm_config_ok conf ->
             thiele_step utm_prog (encode_tm_config conf)
             = encode_tm_config (tm_step tm conf)) conf,
    tm_config_ok conf ->
    decode_tm_config (thiele_step utm_prog (encode_tm_config conf)) = tm_step tm conf.
Proof.
  intros tm B progress conf Hok.
  pose (Ob := simulation_obligations_from_bounds tm B progress).
  exact (simulate_one_step_decode_with tm Ob conf Hok).
Qed.

Lemma tm_run_n_preserves_ok_from_bounds :
  forall tm (B : StepInvariantBounds tm)
         (progress : forall conf,
             tm_config_ok conf ->
             thiele_step utm_prog (encode_tm_config conf)
             = encode_tm_config (tm_step tm conf)) conf n,
    tm_config_ok conf -> tm_config_ok (tm_run_n tm conf n).
Proof.
  intros tm B progress conf n Hok.
  pose (Ob := simulation_obligations_from_bounds tm B progress).
  exact (tm_run_n_preserves_ok_with tm Ob conf n Hok).
Qed.

Lemma utm_simulation_steps_from_bounds :
  forall tm (B : StepInvariantBounds tm)
         (progress : forall conf,
             tm_config_ok conf ->
             thiele_step utm_prog (encode_tm_config conf)
             = encode_tm_config (tm_step tm conf)) conf n,
    tm_config_ok conf ->
    decode_tm_config (thiele_run_n utm_prog (encode_tm_config conf) n) = tm_run_n tm conf n.
Proof.
  intros tm B progress conf n Hok.
  pose (Ob := simulation_obligations_from_bounds tm B progress).
  exact (utm_simulation_steps_with tm Ob conf n Hok).
Qed.

Lemma step_invariant_bounds_static_head :
  forall tm,
    (forall q sym,
        let '(_, write, _) := tm q sym in write < BASE) ->
    (forall q sym,
        let '(_, _, move) := tm q sym in move = 0) ->
    StepInvariantBounds tm.
Proof.
  intros tm Hwrite_static Hmove_static.
  refine ({| bounds_write_in_base := _; bounds_head_within_len := _ |}).
  - intros conf Hok.
    destruct conf as [[q tape] head].
    simpl in *.
    specialize (Hwrite_static q (nth head tape 0)).
    now destruct (tm q (nth head tape 0)) as [[q' write] move].
  - intros conf Hok.
    destruct conf as [[q tape] head].
    simpl in *.
    specialize (Hmove_static q (nth head tape 0)).
    destruct (tm q (nth head tape 0)) as [[q' write] move].
    simpl in *.
    rewrite Hmove_static.
    destruct Hok as [_ [_ Hhead]].
    exact Hhead.
Qed.
