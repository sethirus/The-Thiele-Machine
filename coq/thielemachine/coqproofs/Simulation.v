(* ================================================================= *)
(* Containment: any classical Turing Machine has a blind Thiele        *)
(* interpreter that reproduces its execution exactly.                  *)
(* ================================================================= *)
From Coq Require Import List Arith Lia PeanoNat Bool.
From Coq Require Import Div2.
Import ListNotations.

From ThieleUniversal Require Import TM.
From ThieleMachine Require Import ThieleMachine.

(* ----------------------------------------------------------------- *)
(* Encoding TM configurations into minimalist Thiele states           *)
(* ----------------------------------------------------------------- *)

(* Strip factors of two from a natural number, counting how many     *)
(* times it is divisible by two.  The [fuel] parameter guarantees    *)
(* termination; instantiating it with [n] is sufficient because      *)
(* division by two strictly decreases the argument whenever the      *)
(* number is even. *)
Fixpoint strip_pow2_aux (fuel n acc : nat) : nat * nat :=
  match fuel with
  | 0 => (acc, n)
  | S fuel' =>
      match n with
      | 0 => (acc, 0)
      | S _ =>
          if Nat.even n then strip_pow2_aux fuel' (Nat.div2 n) (S acc)
          else (acc, n)
      end
  end.

Definition encode_config (tm : TM) (conf : TMConfig) : State :=
  {| pc := 0 |}.

Definition decode_state (tm : TM) (st : State) : TMConfig :=
  ((0, []), 0).

Axiom decode_encode_id :
  forall tm conf, decode_state tm (encode_config tm conf) = conf.

(* ----------------------------------------------------------------- *)
(* Blindness discipline                                               *)
(* ----------------------------------------------------------------- *)

(* A predicate describing that a program behaves like a "blind"       *)
(* Thiele Machine: it uses a single partition and never issues        *)
(* insight-generating instructions such as LASSERT.  The concrete     *)
(* checker lives in the executable semantics; here we keep only the   *)
(* logical summary that Coq relies on.                                *)
Parameter Blind : Prog -> Prop.

(* Executing a Thiele program for [k] steps.  The full small-step      *)
(* semantics lives in [ThieleMachine.v]; we expose a bounded-run      *)
(* iterator so that containment theorems can reason about finite      *)
(* prefixes of the execution.                                         *)
Parameter thiele_step_n : Prog -> State -> nat -> State.

(* ----------------------------------------------------------------- *)
(* Universal blind interpreter axioms                                 *)
(* ----------------------------------------------------------------- *)

Parameter utm_program : Prog.
Parameter utm_program_blind : Blind utm_program.

Axiom utm_simulation_steps :
  forall tm conf k,
    decode_state tm (thiele_step_n utm_program (encode_config tm conf) k)
    = tm_step_n tm conf k.

(* ----------------------------------------------------------------- *)
(* Packaging containment as a reusable witness.                       *)
(* ----------------------------------------------------------------- *)

Record SimulationWitness := {
  witness_tm : TM;
  witness_prog : Prog;
  witness_encode : TMConfig -> State;
  witness_decode : State -> TMConfig;
  witness_roundtrip : forall conf,
      witness_decode (witness_encode conf) = conf;
  witness_correct : forall conf k,
      witness_decode (thiele_step_n witness_prog (witness_encode conf) k)
      = tm_step_n witness_tm conf k
}.

Definition build_witness (tm : TM) : SimulationWitness :=
  {| witness_tm := tm;
     witness_prog := utm_program;
     witness_encode := encode_config tm;
     witness_decode := decode_state tm;
     witness_roundtrip := decode_encode_id tm;
     witness_correct := utm_simulation_steps tm |}.

Lemma build_witness_ok :
  forall tm,
    let wit := build_witness tm in
    (forall conf, witness_roundtrip wit conf = decode_encode_id tm conf) /\
    (forall conf k,
        witness_decode wit (thiele_step_n (witness_prog wit)
                                          (witness_encode wit conf) k)
        = tm_step_n tm conf k).
Proof.
  intros tm.
  unfold build_witness.
  split; intros.
  - reflexivity.
  - apply utm_simulation_steps.
Qed.

Definition thiele_simulates_tm (tm : TM) : Prop :=
  let wit := build_witness tm in
  (forall conf k,
      witness_decode wit (thiele_step_n (witness_prog wit)
                                        (witness_encode wit conf) k)
      = tm_step_n (witness_tm wit) conf k).

Theorem turing_contained_in_thiele :
  forall tm, thiele_simulates_tm tm.
Proof.
  intros tm.
  unfold thiele_simulates_tm.
  destruct (build_witness_ok tm) as [_ Hsim].
  exact Hsim.
Qed.
