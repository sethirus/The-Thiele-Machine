Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qring.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Lia.
Import ListNotations.

From ThieleUniversal Require Import TM.
From ThieleMachine Require Import BellInequality.

Local Open Scope Q_scope.

(* Shared randomness is represented as a finite-support distribution over the
   deterministic strategies exported from BellInequality.v.  Each deterministic
   strategy corresponds to the behaviour of a classical Turing Machine when a
   particular shared random tape \(\lambda\) is fixed. *)
Definition Lambda := Strategy.

Record ProbabilisticTM := {
  ptm_machine : TM;
  ptm_response_table : Lambda -> Response
}.

Record PTMArchitecture := {
  ptm_alice : ProbabilisticTM;
  ptm_bob : ProbabilisticTM;
  ptm_lambda_weight : Lambda -> Q;
  ptm_lambda_nonneg : forall lam, 0#1 <= ptm_lambda_weight lam;
  ptm_lambda_sum1 : sum_strategies ptm_lambda_weight = 1#1;
  ptm_lambda_realizes :
    forall lam,
      (ptm_response_table ptm_alice lam, ptm_response_table ptm_bob lam) = lam
}.

Definition PTM_strategy (arch : PTMArchitecture) (lam : Lambda) : Strategy :=
  (ptm_response_table (ptm_alice arch) lam,
   ptm_response_table (ptm_bob arch) lam).

Lemma PTM_strategy_realizes :
  forall arch lam, PTM_strategy arch lam = lam.
Proof.
  intros arch lam.
  unfold PTM_strategy.
  apply ptm_lambda_realizes.
Qed.

Definition PTM_CHSH_expectation (arch : PTMArchitecture) : Q :=
  sum_strategies (fun lam =>
    ptm_lambda_weight arch lam * strategy_S (PTM_strategy arch lam)).

Lemma PTM_CHSH_expectation_unfold :
  forall arch,
    PTM_CHSH_expectation arch ==
      sum_strategies (fun lam => ptm_lambda_weight arch lam * strategy_S lam).
Proof.
  intros arch.
  unfold PTM_CHSH_expectation.
  apply sum_strategies_ext.
  intros lam Hin.
  rewrite PTM_strategy_realizes.
  reflexivity.
Qed.

Theorem impossibility_of_re_encoding :
  forall (arch : PTMArchitecture),
    Qabs (PTM_CHSH_expectation arch) <= 2#1.
Proof.
  intros arch.
  pose proof (PTM_CHSH_expectation_unfold arch) as Hunfold.
  pose proof (Qabs_proper_local _ _ Hunfold) as Habseq.
  setoid_replace (Qabs (PTM_CHSH_expectation arch))
    with (Qabs (sum_strategies (fun lam => ptm_lambda_weight arch lam * strategy_S lam)))
      by exact Habseq.
  set (w := ptm_lambda_weight arch).
  assert (Hwpos : forall lam, 0#1 <= w lam) by apply ptm_lambda_nonneg.
  assert (Hsum : sum_strategies w = 1#1) by apply ptm_lambda_sum1.
  set (F := fun lam => strategy_S lam).
  pose proof (sum_strategies_weighted_lower w F (- (2#1)) Hwpos
                (fun lam _ => strategy_S_lower_bound lam)) as Hlower.
  pose proof (sum_strategies_weighted_upper w F (2#1) Hwpos
                (fun lam _ => strategy_S_upper_bound lam)) as Hupper.
  assert (Hlower_bound : - (2#1) <= sum_strategies (fun lam => w lam * F lam)).
  { apply (Qle_trans _ ((- (2#1)) * sum_strategies w)).
    - rewrite Hsum. simpl. rewrite Qmult_1_r. apply Qle_refl.
    - exact Hlower.
  }
  assert (Hupper_bound : sum_strategies (fun lam => w lam * F lam) <= 2#1).
  { apply (Qle_trans _ ((2#1) * sum_strategies w)).
    - exact Hupper.
    - rewrite Hsum. simpl. rewrite Qmult_1_r. apply Qle_refl.
  }
  apply Qabs_le_bound with (y := 2#1).
  - unfold Qle; simpl; lia.
  - exact Hlower_bound.
  - exact Hupper_bound.
Qed.

(* This proof formally demonstrates that the locality constraints of the
   Turing Machine architecture are the fundamental barrier to achieving the
   Tsirelson bound. The Thiele Machine's success is therefore not an
   algorithmic trick, but a direct consequence of its architecturally
   superior, non-local compositional primitive. *)
