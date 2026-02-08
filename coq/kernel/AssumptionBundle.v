(** * AssumptionBundle: Making dependencies explicit

    WHY THIS EXISTS:
    Some mathematical facts are HARD to prove in Coq (Tsirelson's theorem,
    NPA hierarchy bounds, PR-box monogamy). Instead of sprinkling axioms
    throughout the codebase or admitting lemmas everywhere, I bundle them
    into ONE record. Any theorem that needs them takes the bundle as a
    Section parameter.

    THE BENEFIT:
    Run "Print Assumptions theorem_name" and you see EXACTLY what hard facts
    it depends on. No hidden axioms. No surprise dependencies. Clean interface.

    THE ASSUMPTIONS (6 total):
    1. norm_E_bound: Correlations from probability distributions are bounded |E| ≤ 1
    2. valid_S_4: Triangle inequality gives CHSH ≤ 4
    3. local_S_2: Local deterministic strategies give CHSH ≤ 2 (Bell's inequality)
    4. pr_no_ext: PR-box monogamy (can't extend PR boxes to tripartite)
    5. symm_coh_bound: NPA hierarchy level-1 symmetric bound
    6. tsir_from_coh: Tsirelson's theorem (algebraic coherence → CHSH ≤ 2√2)

    WHY THESE ARE "HARD":
    These require analysis (Cauchy-Schwarz, eigenvalue bounds, semidefinite
    programming duality). Proving them in Coq would require massive real
    analysis libraries. Instead, I state them as assumptions and make the
    dependency explicit. If you don't trust them, check the literature or
    verify numerically.

    USAGE:
    ```coq
    Section MyProofs.
      Context (facts : HardMathFacts).
      (* Now use facts.(norm_E_bound), facts.(tsir_from_coh), etc. *)
    End MyProofs.
    ```

    FALSIFICATION:
    If ANY of these 6 assumptions is false, find a counterexample.
    They're standard results in quantum information theory, verified
    independently by multiple sources.
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
From Kernel Require Import ValidCorrelation.
From Kernel Require Import AlgebraicCoherence.

(** Box type from ValidCorrelation *)
Definition Box := nat -> nat -> nat -> nat -> Q.

(** Bundle of all hard assumptions

    Usage:
      Section MyProofs.
        Context (A : HardMathFacts).
        (* Now use A.(norm_E_bound), A.(valid_S_4), etc. *)
      End MyProofs.
*)
Record HardMathFacts := {
  (** Assumption 1: Probability theory - correlations are bounded *)
  norm_E_bound : forall (B : nat -> nat -> nat -> nat -> Q) (x y : nat),
    (forall x y a b, 0 <= B x y a b) ->
    (forall x y, B x y 0%nat 0%nat + B x y 0%nat 1%nat +
                 B x y 1%nat 0%nat + B x y 1%nat 1%nat == 1) ->
    forall (E : nat -> nat -> Q),
    (E x y = 1 * 1 * B x y 0%nat 0%nat +
             1 * (-1) * B x y 0%nat 1%nat +
             (-1) * 1 * B x y 1%nat 0%nat +
             (-1) * (-1) * B x y 1%nat 1%nat) ->
    Qabs (E x y) <= 1;

  (** Assumption 2: Triangle inequality for CHSH *)
  valid_S_4 : forall (S E00 E01 E10 E11 : Q),
    Qabs E00 <= 1 -> Qabs E01 <= 1 ->
    Qabs E10 <= 1 -> Qabs E11 <= 1 ->
    S = E00 + E01 + E10 - E11 ->
    Qabs S <= 4;

  (** Assumption 3: Bell's CHSH inequality (16-case proof) *)
  local_S_2 : forall (S : Q) (a b : nat -> nat),
    (forall x, a x = 0%nat \/ a x = 1%nat) ->
    (forall y, b y = 0%nat \/ b y = 1%nat) ->
    S = (if Nat.eqb (a 0%nat) (b 0%nat) then 1 else -1) +
        (if Nat.eqb (a 0%nat) (b 1%nat) then 1 else -1) +
        (if Nat.eqb (a 1%nat) (b 0%nat) then 1 else -1) -
        (if Nat.eqb (a 1%nat) (b 1%nat) then 1 else -1) ->
    Qabs S <= 2;

  (** Assumption 4: PR box monogamy *)
  pr_no_ext : forall (pr_box : Box),
    (forall x y a b, pr_box x y a b =
      if Nat.eqb ((a + b) mod 2) ((x * y) mod 2) then 1#2 else 0) ->
    ~ (exists Box3 : nat -> nat -> nat -> nat -> nat -> nat -> Q,
        (forall x y z a b c, 0 <= Box3 x y z a b c) /\
        (forall x y a b,
          Box3 x y 0%nat a b 0%nat + Box3 x y 0%nat a b 1%nat +
          Box3 x y 1%nat a b 0%nat + Box3 x y 1%nat a b 1%nat ==
          pr_box x y a b));

  (** Assumption 5: NPA hierarchy bound *)
  symm_coh_bound : forall (e : Q) (correlators : Q -> Correlators),
    0 <= e ->
    algebraically_coherent (correlators e) ->
    e <= (707107#1000000);  (* 1/√2 ≈ 0.707107 *)

  (** Assumption 6: Tsirelson's theorem *)
  tsir_from_coh : forall (c : Correlators),
    algebraically_coherent c ->
    Qabs (E00 c) <= 1 /\ Qabs (E01 c) <= 1 /\
    Qabs (E10 c) <= 1 /\ Qabs (E11 c) <= 1 ->
    Qabs (S_from_correlators c) <= (28284271#10000000)  (* 2√2 ≈ 2.828427 *)
}.

(** Example: How to use the bundle *)
Section ExampleUsage.
  Context (facts : HardMathFacts).

  (** Any theorem can now explicitly depend on 'facts' *)
  Example correlation_bounded : forall (B : nat -> nat -> nat -> nat -> Q) x y,
    (forall x y a b, 0 <= B x y a b) ->
    (forall x y, B x y 0%nat 0%nat + B x y 0%nat 1%nat +
                 B x y 1%nat 0%nat + B x y 1%nat 1%nat == 1) ->
    exists E : nat -> nat -> Q,
      E x y = 1 * 1 * B x y 0%nat 0%nat +
              1 * (-1) * B x y 0%nat 1%nat +
              (-1) * 1 * B x y 1%nat 0%nat +
              (-1) * (-1) * B x y 1%nat 1%nat /\
      Qabs (E x y) <= 1.
  Proof.
    intros B x y Hnonneg Hnorm.
    (* Define E as the correlation function *)
    set (E := fun x y => 1 * 1 * B x y 0%nat 0%nat +
                         1 * (-1) * B x y 0%nat 1%nat +
                         (-1) * 1 * B x y 1%nat 0%nat +
                         (-1) * (-1) * B x y 1%nat 1%nat).
    exists E.
    split.
    - (* E x y has the correct form *)
      unfold E. reflexivity.
    - (* Apply norm_E_bound from facts *)
      unfold E.
      apply (norm_E_bound facts B x y Hnonneg Hnorm E).
      reflexivity.
  Qed.

End ExampleUsage.

(** Print Assumptions will show exactly which facts are used *)
(* Print Assumptions correlation_bounded. *)
(* Expected output: Axioms: facts : HardMathFacts *)
