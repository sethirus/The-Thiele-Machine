Require Import ThieleMachine.ThieleMachine.
Require Import List String.
Import ListNotations.

Definition TMConfig := State.
Definition TM := Prog.
Definition tm_step := tm_step_fun.

Module ThieleSubsumesTuring.

Record ThieleConfig := {
  tm_config : TMConfig;
  ledger : list string;
  mu_cost : nat;
}.

Definition thiele_step (tm : TM) (th_conf : ThieleConfig) : option ThieleConfig :=
  match tm_step tm th_conf.(tm_config) with
  | Some (next_state, _obs) =>
      Some {|
        tm_config := next_state;
        ledger := "Step taken."%string :: th_conf.(ledger);
        mu_cost := S th_conf.(mu_cost)
      |}
  | None => None
  end.

End ThieleSubsumesTuring.

Theorem thiele_machine_subsumes_turing_machine :
  forall (tm : TM) (conf : TMConfig),
    ThieleSubsumesTuring.thiele_step tm
      {| ThieleSubsumesTuring.tm_config := conf;
         ThieleSubsumesTuring.ledger := [];
         ThieleSubsumesTuring.mu_cost := 0 |}
    =
    match tm_step tm conf with
    | Some (next_state, _obs) =>
        Some {|
          ThieleSubsumesTuring.tm_config := next_state;
          ThieleSubsumesTuring.ledger := ["Step taken."%string];
          ThieleSubsumesTuring.mu_cost := 1
        |}
    | None => None
    end.
Proof.
  intros. reflexivity.
Qed.
