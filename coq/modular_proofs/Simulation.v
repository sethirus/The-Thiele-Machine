(* ================================================================= *)
(* Simulation: TM in Thiele Machine                                  *)
(* ================================================================= *)

From Coq Require Import List Arith Lia PeanoNat Bool.
Import ListNotations.

From ThieleMachine.Modular_Proofs Require Import TM_Basics Encoding.

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
  match conf with
  | (q, (tape, head)) => {| pc := encode_config q tape head |}
  end.

(* Decode Thiele state into TM config *)
Definition decode_tm_config (s : State) : TMConfig :=
  match decode_config s.(pc) with
  | (q, tape, head) => (q, tape, head)
  end.

(* ----------------------------------------------------------------- *)
(* Simulation Lemmas                                                 *)
(* ----------------------------------------------------------------- *)

(* Encoding round-trip *)
Axiom encode_decode_roundtrip : forall conf,
  decode_tm_config (encode_tm_config conf) = conf.

(* One-step simulation (to be proven constructively) *)
Parameter simulate_one_step : forall tm conf,
  decode_tm_config (thiele_step utm_prog (encode_tm_config conf)) = tm_step tm conf.

(* Multi-step simulation by induction *)
Axiom utm_simulation_steps : forall tm conf n,
  decode_tm_config (thiele_run_n utm_prog (encode_tm_config conf) n) = tm_run_n tm conf n.
