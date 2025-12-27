(* ================================================================= *)
(* Thiele Machine Modular Interface                                   *)
(* ================================================================= *)
(* The modular development treats the universal interpreter through a  *)
(* compact interface.  A concrete instantiation must expose how Thiele  *)
(* states encode Turing configurations, how a single interpreter step   *)
(* updates that state, and how multi-step execution iterates the        *)
(* single-step behaviour.                                              *)
(* ================================================================= *)

From Coq Require Import Arith.

From ModularProofs Require Import TM_Basics.

Record ModularThieleSemantics (tm : TMTransition) := {
  mts_state : Type;
  mts_encode : TMConfig -> mts_state;
  mts_decode : mts_state -> TMConfig;
  mts_run1 : mts_state -> mts_state;
  mts_run_n : mts_state -> nat -> mts_state;
  mts_run_n_zero : forall s, mts_run_n s 0 = s;
  mts_run_n_succ : forall s n, mts_run_n s (S n) = mts_run_n (mts_run1 s) n;
  mts_decode_encode : forall conf,
      tm_config_ok conf ->
      mts_decode (mts_encode conf) = conf;
  mts_run_n_simulates : forall conf n,
      tm_config_ok conf ->
      mts_decode (mts_run_n (mts_encode conf) n) = tm_run_n tm conf n
}.

Arguments mts_state {tm} _.
Arguments mts_encode {tm} _ _.
Arguments mts_decode {tm} _ _.
Arguments mts_run1 {tm} _ _.
Arguments mts_run_n {tm} _ _ _.
Arguments mts_run_n_zero {tm} _ _.
Arguments mts_run_n_succ {tm} _ _ _.
Arguments mts_decode_encode {tm} _ _ _.

Section HelperLemmas.
  Context {tm : TMTransition}.
  Context (sem : ModularThieleSemantics tm).

  Lemma mts_run_n_S :
    forall s n,
      mts_run_n sem s (S n) = mts_run_n sem (mts_run1 sem s) n.
  Proof.
    intros s n.
    apply mts_run_n_succ.
  Qed.

  Lemma mts_run_n_one :
    forall s,
      mts_run_n sem s 1 = mts_run1 sem s.
  Proof.
    intro s.
    rewrite (mts_run_n_S s 0).
    rewrite mts_run_n_zero.
    reflexivity.
  Qed.
End HelperLemmas.
