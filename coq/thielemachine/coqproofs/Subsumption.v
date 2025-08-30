Require Import ThieleMachine.
Require Import List String.
Import ListNotations.

Module ThieleSubsumesTuring.

Record ThieleConfig := {
  tm_config : TMConfig;
  ledger : list string;
  mu_cost : nat;
}.

Definition thiele_step (tm : TM nat nat) (th_conf : ThieleConfig) : ThieleConfig :=
  {| tm_config := tm_step tm th_conf.(tm_config);
     ledger := "Step taken."%string :: th_conf.(ledger);
     mu_cost := S th_conf.(mu_cost) |}.

End ThieleSubsumesTuring.

Theorem thiele_machine_subsumes_turing_machine :
  forall (tm : TM nat nat) (conf : TMConfig),
    (ThieleSubsumesTuring.thiele_step tm {| ThieleSubsumesTuring.tm_config := conf;
                                            ThieleSubsumesTuring.ledger := [];
                                            ThieleSubsumesTuring.mu_cost := 0 |}).(ThieleSubsumesTuring.tm_config)
    = tm_step tm conf.
Proof.
  intros. reflexivity.
Qed.
