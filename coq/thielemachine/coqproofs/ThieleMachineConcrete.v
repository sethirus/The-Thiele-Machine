(*
 * Concrete Instantiation of the Thiele Machine
 *
 * This module provides an executable step function that mirrors the
 * instrumented Python VM.  Each instruction deterministically produces a
 * post-state and an observation record, letting receipts replay the run
 * step-by-step.
 *)

From Coq Require Import List String Ascii ZArith Bool Lia.
Import ListNotations.
Local Notation length := List.length.
Open Scope string_scope.
Open Scope Z_scope.

(* ================================================================= *)
(* Concrete Hash Implementation *)
(* ================================================================= *)

Definition Hash : Type := string.
Definition H0 : Hash := EmptyString.

(* ================================================================= *)
(* Concrete Instruction Set and Events *)
(* ================================================================= *)

Inductive ThieleInstr : Type :=
  | LASSERT : string -> ThieleInstr
  | MDLACC : ThieleInstr
  | PNEW : list nat -> ThieleInstr
  | PYEXEC : string -> ThieleInstr
  | CHSH_TRIAL : nat -> nat -> nat -> nat -> ThieleInstr
  | EMIT : string -> ThieleInstr.

Inductive ThieleEvent : Type :=
  | PolicyCheck : string -> ThieleEvent
  | InferenceComplete : ThieleEvent
  | ChshTrial : nat -> nat -> nat -> nat -> ThieleEvent
  | ErrorOccurred : string -> ThieleEvent.

(* ================================================================= *)
(* Concrete State Representation *)
(* ================================================================= *)

Record ConcreteState : Type := {
  pc : nat;
  status : Z;
  mu_acc : Z;
  cert_addr : string;
}.

Definition default_concrete_state : ConcreteState :=
  {| pc := 0;
     status := 0;
     mu_acc := 0;
     cert_addr := EmptyString |}.

(* ================================================================= *)
(* Certificates and Observations *)
(* ================================================================= *)

Record ConcreteCert : Type := {
  smt_query : string;
  solver_reply : string;
  metadata : string;
  timestamp : Z;
  sequence : nat;
}.

Record StepObs : Type := {
  ev : option ThieleEvent;
  mu_delta : Z;
  cert : ConcreteCert;
}.

Record StepResult : Type := {
  post_state : ConcreteState;
  observation : StepObs;
}.

Definition default_cert : ConcreteCert :=
  {| smt_query := EmptyString;
     solver_reply := EmptyString;
     metadata := EmptyString;
     timestamp := 0;
     sequence := 0 |}.

Definition cert_for_pyexec (code : string) : ConcreteCert :=
  if String.eqb code "alice_measurement"%string then
    {| smt_query := EmptyString;
       solver_reply := EmptyString;
       metadata := EmptyString;
       timestamp := 0;
       sequence := 0%nat |}
  else if String.eqb code "bob_measurement"%string then
    {| smt_query := EmptyString;
       solver_reply := EmptyString;
       metadata := EmptyString;
       timestamp := 1;
       sequence := 0%nat |}
  else default_cert.

Definition bit_char01 (n : nat) : ascii :=
  if Nat.eqb n 0 then "0"%char else "1"%char.

Definition bit_string01 (n : nat) : string :=
  String (bit_char01 n) EmptyString.

Definition is_bit_nat (n : nat) : bool :=
  (Nat.eqb n 0 || Nat.eqb n 1)%bool.

Definition cert_for_chsh_trial (x y a b : nat) : ConcreteCert :=
  {| smt_query := EmptyString;
     solver_reply := EmptyString;
     metadata := "CHSH_" ++ bit_string01 x ++ bit_string01 y ++ bit_string01 a ++ bit_string01 b;
     timestamp := 0;
     sequence := 0%nat |}.


Definition advance_pc (s : ConcreteState) : ConcreteState :=
  {| pc := S s.(pc);
     status := s.(status);
     mu_acc := s.(mu_acc);
     cert_addr := s.(cert_addr) |}.

Definition add_mu (s : ConcreteState) (delta : Z) : ConcreteState :=
  {| pc := s.(pc);
     status := s.(status);
     mu_acc := s.(mu_acc) + delta;
     cert_addr := s.(cert_addr) |}.

Definition with_pc_mu (s : ConcreteState) (delta : Z) : ConcreteState :=
  add_mu (advance_pc s) delta.

Definition set_status (s : ConcreteState) (st : Z) : ConcreteState :=
  {| pc := s.(pc);
     status := st;
     mu_acc := s.(mu_acc);
     cert_addr := s.(cert_addr) |}.

Definition record_cert (s : ConcreteState) (addr : string) : ConcreteState :=
  {| pc := s.(pc);
     status := s.(status);
     mu_acc := s.(mu_acc);
     cert_addr := addr |}.

(* ================================================================= *)
(* Concrete Step Function *)
(* ================================================================= *)

Definition cert_for_query (query : string) : ConcreteCert :=
  {| smt_query := query;
     solver_reply := EmptyString;
     metadata := EmptyString;
     timestamp := 0;
     sequence := 0 |}.

(** HELPER: Base case property *)
(** HELPER: Base case property *)
Lemma cert_for_query_metadata_empty : forall q, (cert_for_query q).(metadata) = EmptyString.
Proof. intros; reflexivity. Qed.
(** HELPER: Base case property *)

(** HELPER: Base case property *)
Lemma cert_for_pyexec_metadata_empty : forall code, (cert_for_pyexec code).(metadata) = EmptyString.
Proof.
  intro code.
  unfold cert_for_pyexec.
  destruct (String.eqb code "alice_measurement") eqn:Ha; [reflexivity|].
  destruct (String.eqb code "bob_measurement") eqn:Hb; reflexivity.
Qed.

Definition concrete_step (instr : ThieleInstr) (s : ConcreteState) : StepResult :=
  match instr with
  | LASSERT query =>
      let mu := (Z.of_nat (String.length query)) * 8 in
      {| post_state := with_pc_mu s mu;
         observation := {| ev := Some (PolicyCheck query);
                           mu_delta := mu;
                           cert := cert_for_query query |} |}
  | MDLACC =>
      {| post_state := advance_pc s;
         observation := {| ev := None;
                           mu_delta := 0;
                           cert := default_cert |} |}
  | PNEW _ =>
      {| post_state := advance_pc s;
         observation := {| ev := Some InferenceComplete;
                           mu_delta := 0;
                           cert := default_cert |} |}
  | PYEXEC code =>
      {| post_state := advance_pc s;
         observation := {| ev := Some (PolicyCheck code);
                           mu_delta := 0;
                           cert := cert_for_pyexec code |} |}
  | CHSH_TRIAL x y a b =>
      if (is_bit_nat x && is_bit_nat y && is_bit_nat a && is_bit_nat b)%bool then
        {| post_state := advance_pc s;
          observation := {| ev := Some (ChshTrial x y a b);
                      mu_delta := 0;
                      cert := cert_for_chsh_trial x y a b |} |}
      else
        {| post_state := advance_pc s;
          observation := {| ev := Some (ErrorOccurred "CHSH_BADBITS"%string);
                      mu_delta := 0;
                      cert := default_cert |} |}
  | EMIT payload =>
      {| post_state := advance_pc s;
         observation := {| ev := Some (ErrorOccurred payload);
                           mu_delta := 0;
                           cert := default_cert |} |}
  end.

(** [chsh_metadata_only_from_chsh_trial]: formal specification. *)
Lemma chsh_metadata_only_from_chsh_trial :
  forall instr s,
    String.eqb
      (String.substring 0 5 (concrete_step instr s).(observation).(cert).(metadata))
      "CHSH_" = true ->
    exists x y a b, instr = CHSH_TRIAL x y a b.
Proof.
  intros instr s H.
  destruct instr; cbn in H.
  - (* LASSERT *) vm_compute in H. discriminate.
  - (* MDLACC *) vm_compute in H. discriminate.
  - (* PNEW *) vm_compute in H. discriminate.
  - (* PYEXEC *) rewrite cert_for_pyexec_metadata_empty in H. vm_compute in H. discriminate.
  - (* CHSH_TRIAL *) eexists; eexists; eexists; eexists; reflexivity.
  - (* EMIT *) vm_compute in H. discriminate.
Qed.

(** [chsh_event_only_from_chsh_trial]: formal specification. *)
Lemma chsh_event_only_from_chsh_trial :
  forall instr s x y a b,
    (concrete_step instr s).(observation).(ev) = Some (ChshTrial x y a b) ->
    instr = CHSH_TRIAL x y a b.
Proof.
  intros instr s x y a b H.
  destruct instr; cbn in H; try discriminate.
  destruct (is_bit_nat n && is_bit_nat n0 && is_bit_nat n1 && is_bit_nat n2)%bool; cbn in H; try discriminate.
  inversion H. subst. reflexivity.
Qed.

(* ================================================================= *)
(* Boolean Equality Helpers *)
(* ================================================================= *)

Definition concrete_state_eqb (s1 s2 : ConcreteState) : bool :=
  Nat.eqb s1.(pc) s2.(pc)
    && Z.eqb s1.(status) s2.(status)
    && Z.eqb s1.(mu_acc) s2.(mu_acc)
(** HELPER: Reflexivity/transitivity/symmetry property *)
    && String.eqb s1.(cert_addr) s2.(cert_addr).

(** HELPER: Reflexivity/transitivity/symmetry property *)
Lemma concrete_state_eqb_refl : forall s, concrete_state_eqb s s = true.
Proof.
  intros s.
  unfold concrete_state_eqb.
  repeat rewrite Bool.andb_true_iff.
  repeat split; try apply Nat.eqb_refl;
    try apply Z.eqb_refl;
    try apply String.eqb_refl.
Qed.

Definition thiele_event_eqb (e1 e2 : ThieleEvent) : bool :=
  match e1, e2 with
  | PolicyCheck a, PolicyCheck b => String.eqb a b
  | InferenceComplete, InferenceComplete => true
  | ChshTrial x1 y1 a1 b1, ChshTrial x2 y2 a2 b2 =>
      Nat.eqb x1 x2 && Nat.eqb y1 y2 && Nat.eqb a1 a2 && Nat.eqb b1 b2
  | ErrorOccurred a, ErrorOccurred b => String.eqb a b
  | _, _ => false
  end.

Definition option_event_eqb (e1 e2 : option ThieleEvent) : bool :=
  match e1, e2 with
  | None, None => true
  | Some a, Some b => thiele_event_eqb a b
  | _, _ => false
  end.

Definition concrete_cert_eqb (c1 c2 : ConcreteCert) : bool :=
  String.eqb c1.(smt_query) c2.(smt_query)
    && String.eqb c1.(solver_reply) c2.(solver_reply)
    && String.eqb c1.(metadata) c2.(metadata)
    && Z.eqb c1.(timestamp) c2.(timestamp)
    && Nat.eqb c1.(sequence) c2.(sequence).

Definition step_obs_eqb (o1 o2 : StepObs) : bool :=
  option_event_eqb o1.(ev) o2.(ev)
(** HELPER: Reflexivity/transitivity/symmetry property *)
    && Z.eqb o1.(mu_delta) o2.(mu_delta)
    && concrete_cert_eqb o1.(cert) o2.(cert).

(** HELPER: Reflexivity/transitivity/symmetry property *)
Lemma thiele_event_eqb_refl : forall e, thiele_event_eqb e e = true.
Proof.
  intros e. destruct e; simpl; try apply String.eqb_refl; try reflexivity.
(** HELPER: Reflexivity/transitivity/symmetry property *)
  repeat rewrite Nat.eqb_refl.
  reflexivity.
Qed.

(** HELPER: Reflexivity/transitivity/symmetry property *)
Lemma concrete_cert_eqb_refl : forall cert, concrete_cert_eqb cert cert = true.
Proof.
  intros [query reply meta ts seq].
(** HELPER: Reflexivity/transitivity/symmetry property *)
  unfold concrete_cert_eqb; simpl.
  repeat rewrite Bool.andb_true_iff.
  repeat split; try apply String.eqb_refl; try apply Z.eqb_refl; try apply Nat.eqb_refl.
Qed.

(** HELPER: Reflexivity/transitivity/symmetry property *)
Lemma step_obs_eqb_refl : forall obs, step_obs_eqb obs obs = true.
Proof.
  intros [oev mu cert].
  unfold step_obs_eqb, option_event_eqb; simpl.
  destruct oev; simpl;
    rewrite ?thiele_event_eqb_refl;
    rewrite ?Z.eqb_refl;
    rewrite concrete_cert_eqb_refl;
    reflexivity.
Qed.

Definition receipt_matches (instr : ThieleInstr)
           (spre spost : ConcreteState) (obs : StepObs) : bool :=
  let res := concrete_step instr spre in
  concrete_state_eqb res.(post_state) spost
    && step_obs_eqb res.(observation) obs.

(* ================================================================= *)
(* Receipt Structures and Replay *)
(* ================================================================= *)

Record ConcreteReceipt : Type := {
  receipt_instr : ThieleInstr;
  receipt_pre : ConcreteState;
  receipt_post : ConcreteState;
  receipt_obs : StepObs;
}.

Definition concrete_check_step (r : ConcreteReceipt) : bool :=
  receipt_matches r.(receipt_instr) r.(receipt_pre) r.(receipt_post) r.(receipt_obs).

Fixpoint concrete_replay_ok (s0 : ConcreteState) (rs : list ConcreteReceipt) : bool :=
  match rs with
  | [] => true
  | r :: tl =>
      if negb (concrete_state_eqb s0 r.(receipt_pre)) then false
      else if concrete_check_step r
           then concrete_replay_ok r.(receipt_post) tl
           else false
  end.

(* ================================================================= *)
(* Aggregations *)
(* ================================================================= *)

Definition concrete_bitsize (c : ConcreteCert) : Z :=
  Z.of_nat (String.length c.(smt_query)
            + String.length c.(solver_reply)) * 8.

(** [concrete_bitsize_cert_for_query]: formal specification. *)
Lemma concrete_bitsize_cert_for_query :
  forall query,
    concrete_bitsize (cert_for_query query) =
    (Z.of_nat (String.length query)) * 8.
Proof.
  intros query.
(** HELPER: Base case property *)
  unfold concrete_bitsize, cert_for_query.
  simpl.
  rewrite Nat.add_0_r.
  reflexivity.
Qed.

(** HELPER: Base case property *)
Lemma concrete_bitsize_default_cert_zero :
  concrete_bitsize default_cert = 0.
Proof.
  unfold concrete_bitsize, default_cert.
  simpl.
  reflexivity.
Qed.

Fixpoint concrete_sum_bits (rs : list ConcreteReceipt) : Z :=
  match rs with
  | [] => 0
  | r :: tl => concrete_bitsize r.(receipt_obs).(cert) + concrete_sum_bits tl
  end.

(** [concrete_bitsize_cert_for_pyexec]: formal specification. *)
Lemma concrete_bitsize_cert_for_pyexec :
  forall code, concrete_bitsize (cert_for_pyexec code) = 0.
Proof.
  intros code.
  unfold cert_for_pyexec.
  destruct (String.eqb code "alice_measurement"%string); simpl; try reflexivity.
  destruct (String.eqb code "bob_measurement"%string); simpl; reflexivity.
Qed.

(* DEFINITIONAL — cert_for_chsh_trial produces a zero-bitsize certificate *)
(** [concrete_bitsize_cert_for_chsh_trial]: formal specification. *)
Lemma concrete_bitsize_cert_for_chsh_trial :
  forall x y a b, concrete_bitsize (cert_for_chsh_trial x y a b) = 0.
Proof.
  intros x y a b.
  unfold concrete_bitsize, cert_for_chsh_trial.
  simpl.
  reflexivity.
Qed.

Fixpoint concrete_sum_mu (tr : list (ConcreteState * StepObs)) : Z :=
  match tr with
  | [] => 0
  | (_, obs) :: tl => obs.(mu_delta) + concrete_sum_mu tl
  end.

(* ================================================================= *)
(* Deterministic Execution Trace *)
(* ================================================================= *)

Fixpoint concrete_trace_of (s : ConcreteState) (prog : list ThieleInstr)
  : list (ConcreteState * StepObs) :=
  match prog with
  | [] => []
  | instr :: tl =>
      let res := concrete_step instr s in
      (res.(post_state), res.(observation)) :: concrete_trace_of res.(post_state) tl
  end.

Fixpoint concrete_receipts_of (s : ConcreteState) (prog : list ThieleInstr)
  : list ConcreteReceipt :=
  match prog with
  | [] => []
  | instr :: tl =>
      let res := concrete_step instr s in
(** HELPER: Accessor/projection *)
      {| receipt_instr := instr;
         receipt_pre := s;
         receipt_post := res.(post_state);
         receipt_obs := res.(observation) |}
        :: concrete_receipts_of res.(post_state) tl
  end.

(** HELPER: Accessor/projection *)
Lemma concrete_receipts_length :
  forall s prog,
    length (concrete_receipts_of s prog) = length prog.
Proof.
  intros s prog.
  revert s.
  induction prog as [|instr tl IH]; intros s; simpl.
  - reflexivity.
  - destruct (concrete_step instr s) as [post obs].
    simpl.
    specialize (IH post).
    rewrite IH.
    reflexivity.
Qed.

(** [concrete_receipts_instrs]: formal specification. *)
Lemma concrete_receipts_instrs :
  forall s prog,
    List.map receipt_instr (concrete_receipts_of s prog) = prog.
Proof.
  intros s prog.
  revert s.
(** HELPER: Accessor/projection *)
  induction prog as [|instr tl IH]; intros s; simpl.
  - reflexivity.
  - destruct (concrete_step instr s) as [post obs].
    simpl.
    f_equal.
    apply IH.
Qed.

(** HELPER: Accessor/projection *)
Lemma concrete_trace_length :
  forall s prog,
    length (concrete_trace_of s prog) = length prog.
Proof.
  intros s prog.
  revert s.
  induction prog as [|instr tl IH]; intros s; simpl.
  - reflexivity.
  - destruct (concrete_step instr s) as [post obs].
    simpl.
    specialize (IH post).
    rewrite IH.
    reflexivity.
Qed.

(* ================================================================= *)
(* Execution Relation *)
(* ================================================================= *)

Inductive ConcreteExec : list ThieleInstr -> ConcreteState -> list (ConcreteState * StepObs) -> Prop :=
| cexec_nil : forall s, ConcreteExec [] s []
| cexec_cons : forall instr prog s s' obs tr,
    concrete_step instr s = {| post_state := s'; observation := obs |} ->
    ConcreteExec prog s' tr ->
    ConcreteExec (instr :: prog) s ((s', obs) :: tr).

(** [concrete_exec_trace_deterministic]: formal specification. *)
Lemma concrete_exec_trace_deterministic :
  forall prog s tr,
    ConcreteExec prog s tr ->
    tr = concrete_trace_of s prog.
Proof.
  intros prog s tr Hexec.
  induction Hexec; simpl.
  - reflexivity.
  - rewrite H. simpl. f_equal. apply IHHexec.
Qed.

(** [concrete_exec_receipts_ok]: formal specification. *)
Lemma concrete_exec_receipts_ok :
  forall prog s tr,
    ConcreteExec prog s tr ->
    concrete_replay_ok s (concrete_receipts_of s prog) = true.
Proof.
  intros prog s tr Hexec.
  induction Hexec; simpl.
  - reflexivity.
  - destruct (concrete_state_eqb s s) eqn:Hpre.
    + unfold concrete_check_step, receipt_matches.
      rewrite H.
      simpl.
      destruct (concrete_state_eqb (post_state (concrete_step instr s)) s') eqn:Hpost.
      * destruct (step_obs_eqb (observation (concrete_step instr s)) obs) eqn:Hobs; simpl.
        -- apply IHHexec.
        -- rewrite H in Hobs. simpl in Hobs.
           rewrite (step_obs_eqb_refl obs) in Hobs. discriminate.
      * rewrite H in Hpost. simpl in Hpost.
        rewrite (concrete_state_eqb_refl s') in Hpost. discriminate.
    + rewrite (concrete_state_eqb_refl s) in Hpre. discriminate.
Qed.

(** [concrete_sum_bits_trace]: formal specification. *)
Lemma concrete_sum_bits_trace :
  forall s prog,
    concrete_sum_bits (concrete_receipts_of s prog) =
    concrete_sum_mu (concrete_trace_of s prog).
Proof.
  intros s prog.
  revert s.
  induction prog as [|instr tl IH]; intros s; simpl; auto.
  destruct instr as [query | | params | code | x y a b | payload]; simpl.
  - set (mu := (Z.of_nat (String.length query)) * 8).
    simpl.
    rewrite concrete_bitsize_cert_for_query.
    simpl.
    rewrite (IH (with_pc_mu s mu)).
    reflexivity.
  - simpl.
    rewrite (IH (advance_pc s)). reflexivity.
  - simpl.
    rewrite (IH (advance_pc s)). reflexivity.
  - simpl.
    rewrite concrete_bitsize_cert_for_pyexec.
    rewrite (IH (advance_pc s)). reflexivity.
  - simpl.
    destruct (is_bit_nat x && is_bit_nat y && is_bit_nat a && is_bit_nat b)%bool; simpl.
    + unfold concrete_bitsize, cert_for_chsh_trial.
(** HELPER: Accessor/projection *)
      simpl.
      rewrite (IH (advance_pc s)). reflexivity.
    + unfold concrete_bitsize, default_cert.
      simpl.
      rewrite (IH (advance_pc s)). reflexivity.
  - simpl.
    rewrite (IH (advance_pc s)). reflexivity.
Qed.

(** HELPER: Accessor/projection *)
Lemma concrete_exec_length :
  forall prog s tr,
    ConcreteExec prog s tr -> length tr = length prog.
Proof.
  intros prog s tr Hexec.
  rewrite (concrete_exec_trace_deterministic _ _ _ Hexec).
  apply concrete_trace_length.
Qed.

(** [ConcreteThieleMachine_exists]: formal specification. *)
Theorem ConcreteThieleMachine_exists :
  exists (prog : list ThieleInstr) (s0 : ConcreteState),
    forall tr,
      ConcreteExec prog s0 tr ->
      exists rs,
        length rs = length tr /\
        concrete_replay_ok s0 rs = true /\
        Z.le (concrete_sum_bits rs) (concrete_sum_mu tr).
Proof.
  exists [].
  exists default_concrete_state.
  intros tr Hexec.
  inversion Hexec; subst.
  exists [].
  repeat split; simpl; try lia.
Qed.
