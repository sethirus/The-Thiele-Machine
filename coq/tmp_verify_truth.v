From Coq Require Import String ZArith List Bool.
From ThieleMachine Require Import ThieleMachineConcrete BellInequality.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition step0_pre : ConcreteState :=
  {| pc := 0;
     status := 0;
     mu_acc := 0;
     cert_addr := "" |}.

Definition step0_post : ConcreteState :=
  {| pc := 1;
     status := 0;
     mu_acc := 0;
     cert_addr := "" |}.

Definition step0_obs : StepObs :=
  {| ev := Some InferenceComplete;
     mu_delta := 0;
     cert := {| smt_query := "";
     solver_reply := "";
     metadata := "";
     timestamp := 0;
     sequence := 0 |} |}.

Definition receipt0 : ConcreteReceipt :=
  {| receipt_instr := (PNEW [0%nat; 1%nat]);
     receipt_pre := step0_pre;
     receipt_post := step0_post;
     receipt_obs := step0_obs |}.

Definition step1_pre : ConcreteState :=
  {| pc := 1;
     status := 0;
     mu_acc := 0;
     cert_addr := "" |}.

Definition step1_post : ConcreteState :=
  {| pc := 2;
     status := 0;
     mu_acc := 0;
     cert_addr := "" |}.

Definition step1_obs : StepObs :=
  {| ev := Some (PolicyCheck "prepare_shared_partition");
     mu_delta := 0;
     cert := {| smt_query := "";
     solver_reply := "";
     metadata := "";
     timestamp := 0;
     sequence := 0 |} |}.

Definition receipt1 : ConcreteReceipt :=
  {| receipt_instr := (PYEXEC "prepare_shared_partition");
     receipt_pre := step1_pre;
     receipt_post := step1_post;
     receipt_obs := step1_obs |}.

Definition step2_pre : ConcreteState :=
  {| pc := 2;
     status := 0;
     mu_acc := 0;
     cert_addr := "" |}.

Definition step2_post : ConcreteState :=
  {| pc := 3;
     status := 0;
     mu_acc := 0;
     cert_addr := "" |}.

Definition step2_obs : StepObs :=
  {| ev := Some (PolicyCheck "alice_measurement");
     mu_delta := 0;
     cert := {| smt_query := "";
     solver_reply := "";
     metadata := "";
     timestamp := 0;
     sequence := 0 |} |}.

Definition receipt2 : ConcreteReceipt :=
  {| receipt_instr := (PYEXEC "alice_measurement");
     receipt_pre := step2_pre;
     receipt_post := step2_post;
     receipt_obs := step2_obs |}.

Definition step3_pre : ConcreteState :=
  {| pc := 3;
     status := 0;
     mu_acc := 0;
     cert_addr := "" |}.

Definition step3_post : ConcreteState :=
  {| pc := 4;
     status := 0;
     mu_acc := 0;
     cert_addr := "" |}.

Definition step3_obs : StepObs :=
  {| ev := Some (PolicyCheck "bob_measurement");
     mu_delta := 0;
     cert := {| smt_query := "";
     solver_reply := "";
     metadata := "";
     timestamp := 1;
     sequence := 0 |} |}.

Definition receipt3 : ConcreteReceipt :=
  {| receipt_instr := (PYEXEC "bob_measurement");
     receipt_pre := step3_pre;
     receipt_post := step3_post;
     receipt_obs := step3_obs |}.

Definition step4_pre : ConcreteState :=
  {| pc := 4;
     status := 0;
     mu_acc := 0;
     cert_addr := "" |}.

Definition step4_post : ConcreteState :=
  {| pc := 5;
     status := 0;
     mu_acc := 0;
     cert_addr := "" |}.

Definition step4_obs : StepObs :=
  {| ev := Some (ErrorOccurred "tsirelson_outcome");
     mu_delta := 0;
     cert := {| smt_query := "";
     solver_reply := "";
     metadata := "";
     timestamp := 0;
     sequence := 0 |} |}.

Definition receipt4 : ConcreteReceipt :=
  {| receipt_instr := (EMIT "tsirelson_outcome");
     receipt_pre := step4_pre;
     receipt_post := step4_post;
     receipt_obs := step4_obs |}.

Definition recorded_program : list ThieleInstr :=
  [(PNEW [0%nat; 1%nat]); (PYEXEC "prepare_shared_partition"); (PYEXEC "alice_measurement"); (PYEXEC "bob_measurement"); (EMIT "tsirelson_outcome")].

Definition recorded_receipts : list ConcreteReceipt :=
  [receipt0; receipt1; receipt2; receipt3; receipt4].

Definition recorded_frames : list (BridgeReceiptFrame ThieleInstr ConcreteState StepObs) :=
  map concrete_receipt_frame recorded_receipts.

Definition recorded_start : ConcreteState := step0_pre.

Lemma recorded_receipts_correct :
  concrete_receipts_of recorded_start recorded_program = recorded_receipts.
Proof. reflexivity. Qed.

Lemma recorded_frames_sound :
  @receipts_sound _ _ _ concrete_step_frame recorded_start recorded_frames.
Proof.
  unfold recorded_frames.
  rewrite <- recorded_receipts_correct.
  apply concrete_receipts_sound.
Qed.
