(** SmTallyL.v: the five tallies of a host program's final record as
    Minsky machines.

    Every function of SmTally.v is turned into a term of the lambda calculus
    L (the extraction tactic needs MetaCoq Template), and the evaluator with a
    selector, which is monotone in its fuel, defines an L-computable relation
    of two numbers by unbounded search over the fuel [sm_L_computable_fuel2].
    The vendored theorem [L_computable_to_MMA_computable] turns it into a
    program of the vendored alternate Minsky machine with the two inputs in
    counters 1 and 2 and the answer in counter 0.

    [sm2_ev_MMA]: for every selector sel and every number t, the relation
    "some fuel makes the evaluator find m on x and c" is MMA_computable.

    Dependencies: as SmEvalL.v, and SmTally.v and SmFuel.v. No axioms, no
    Admitted.                                                              *)

From Undecidability.L Require Import L Tactics.LTactics Datatypes.LNat Datatypes.LOptions
  Datatypes.LProd Datatypes.Lists Datatypes.LBool.
From Undecidability.L Require Import Datatypes.List.List_nat.
From Undecidability.MinskyMachines Require Import MMA.
From Undecidability.MinskyMachines.Reductions Require Import L_computable_to_MMA_computable.
Require Minimal.UniversalCodes.
Require Import Sm.SmHostBlocks Sm.SmCodes Sm.SmInterp Sm.SmEvalL Sm.SmFuel Sm.SmTally.

Instance term_sm2_kcost : computable sm2_kcost. Proof. extract. Qed.
Instance term_sm2_kfires : computable sm2_kfires. Proof. extract. Qed.
Instance term_sm2_kstep : computable sm2_kstep. Proof. extract. Qed.
Instance term_sm2_krun : computable sm2_krun. Proof. extract. Qed.
Instance term_sm2_kstart : computable sm2_kstart. Proof. extract. Qed.
Instance term_sm2_fe : computable sm2_fe. Proof. extract. Qed.
Instance term_sm2_nf : computable sm2_nf. Proof. extract. Qed.
Instance term_sm2_rest : computable sm2_rest. Proof. extract. Qed.
Instance term_sm2_comp : computable sm2_comp. Proof. extract. Qed.
Instance term_sm2_tal : computable sm2_tal. Proof. extract. Qed.
Instance term_sm2_ev : computable sm2_ev. Proof. extract. Qed.

(* The selector and the number of the transformation as one parameter. *)
Definition sm2_evw (w : nat * nat) (fuel x c : nat) : option nat :=
  sm2_ev (fst w) (snd w) fuel x c.

Instance term_sm2_evw : computable sm2_evw. Proof. extract. Qed.

Definition sm2_Rev (sel t : nat) (v : Vector.t nat 2) (m : nat) : Prop :=
  exists n, sm2_ev sel t n (Vector.hd v) (Vector.hd (Vector.tl v)) = Some m.

Theorem sm2_ev_MMA : forall sel t, MMA_computable (sm2_Rev sel t).
Proof.
  intros sel t. apply L_computable_to_MMA_computable.
  exact (@sm_L_computable_fuel2 (nat * nat) _ sm2_evw _ (sel, t)
           (fun n n' x c m H Hle => sm2_ev_mono sel t n n' x c m Hle H)).
Qed.

Print Assumptions sm2_ev_MMA.
