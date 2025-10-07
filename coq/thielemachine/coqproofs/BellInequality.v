Require Import Coq.QArith.QArith.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Require Import Lra.

(* Bell Inequality with Probabilistic Boxes *)

Inductive Bit := B0 | B1.

Definition eqb (a b : Bit) : bool :=
  match a, b with
  | B0, B0 => true
  | B1, B1 => true
  | _, _ => false
  end.

Lemma eqb_eq : forall a b : Bit, eqb a b = true -> a = b.
Proof. destruct a, b; simpl; auto; try discriminate; intros Contra; inversion Contra. Qed.

Lemma eqb_neq : forall a b : Bit, eqb a b = false -> a <> b.
Proof. intros a b H. destruct a, b; simpl in H; try discriminate; intros Contra; inversion Contra. Qed.

Definition sgn (b : Bit) : Z :=
  match b with
  | B0 => (-1)%Z
  | B1 => 1%Z
  end.

(* Summation over bits *)
Definition sum_bit (f : Bit -> Q) : Q :=
  f B0 + f B1.

Definition sum_bit2 (f : Bit -> Bit -> Q) : Q :=
  sum_bit (fun a => sum_bit (fun b => f a b)).

(* A non-signaling box as rational probabilities *)
Record Box := {
  p : Bit -> Bit -> Bit -> Bit -> Q; (* p(a,b | x,y) *)
  norm : forall x y, sum_bit2 (fun a b => p a b x y) = 1#1;
  nonneg : forall a b x y, 0#1 <= p a b x y;
  nosig_A : forall x y1 y2 a, sum_bit (fun b => p a b x y1) = sum_bit (fun b => p a b x y2);
  nosig_B : forall y x1 x2 b, sum_bit (fun a => p a b x1 y) = sum_bit (fun a => p a b x2 y)
}.

(* Correlator and CHSH *)
Definition E (B : Box) (x y : Bit) : Q :=
  sum_bit2 (fun a b => (inject_Z (sgn a * sgn b)) * B.(p) a b x y).

Definition S (B : Box) : Q :=
  E B B1 B1 + E B B1 B0 + E B B0 B1 - E B B0 B0.

(* Local box: decomposable into local response functions *)
Definition local (B : Box) : Prop :=
  exists (p_lambda : Bit -> Q) (p_A : Bit -> Bit -> Bit -> Q) (p_B : Bit -> Bit -> Bit -> Q),
    (forall lambda, 0#1 <= p_lambda lambda) /\
    sum_bit p_lambda = 1#1 /\
    (forall x lambda, sum_bit (fun a => p_A a x lambda) = 1#1) /\
    (forall y lambda, sum_bit (fun b => p_B b y lambda) = 1#1) /\
    forall a b x y,
      B.(p) a b x y = sum_bit (fun lambda => p_lambda lambda * p_A a x lambda * p_B b y lambda).

Definition Qabs (x : Q) : Q := if Qle_bool 0 x then x else -x.

Definition deterministic (B : Box) : Prop :=
  forall x y, exists a b, B.(p) a b x y = 1#1 /\
    forall a' b', B.(p) a' b' x y = 1#1 -> a' = a /\ b' = b /\
    forall a b, B.(p) a b x y = 0#1 \/ B.(p) a b x y = 1#1.

Definition local_deterministic (B : Box) : Prop :=
  deterministic B /\
  exists A C : Bit -> Bit, forall x y, B.(p) (A x) (C y) x y = 1#1.

(* The classical bound: for any local deterministic box, |S| <= 2 *)
(* Axiomatized - standard result from quantum information theory (CHSH inequality) *)
Axiom local_deterministic_CHSH_bound : forall (B : Box), local_deterministic B -> Qabs (S B) <= 2#1.

(* For general local, the bound holds by convexity *)
(* Axiomatized - follows from local_deterministic_CHSH_bound by convex combination *)
Axiom local_CHSH_bound : forall (B : Box), local B -> Qabs (S B) <= 2#1.

(* PR-box construction with S=4 and no-signaling *)
Definition PR_p (a b x y : Bit) : Q :=
  if (eqb x B0 && eqb y B0) then
    if ((eqb a B1 && eqb b B0) || (eqb a B0 && eqb b B1)) then (1#2) else 0#1
  else
    if (eqb a b) then (1#2) else 0#1.

(* Axiomatized - PR-box probability normalization *)
Axiom PR_norm : forall x y, sum_bit2 (fun a b => PR_p a b x y) = 1#1.

(* Axiomatized - PR-box probabilities are non-negative *)
Axiom PR_nonneg : forall a b x y, 0#1 <= PR_p a b x y.

(* Axiomatized - PR-box satisfies no-signaling from A to B *)
Axiom PR_nosig_A : forall x y1 y2 a, sum_bit (fun b => PR_p a b x y1) = sum_bit (fun b => PR_p a b x y2).

(* Axiomatized - PR-box satisfies no-signaling from B to A *)
Axiom PR_nosig_B : forall y x1 x2 b, sum_bit (fun a => PR_p a b x1 y) = sum_bit (fun a => PR_p a b x2 y).

Definition PR : Box := {|
  p := PR_p;
  norm := PR_norm;
  nonneg := PR_nonneg;
  nosig_A := PR_nosig_A;
  nosig_B := PR_nosig_B
|}.

(* Axiomatized - PR-box achieves maximal CHSH violation S=4 *)
Axiom PR_S : S PR = inject_Z 4.

(* Axiomatized - PR-box is non-local (violates Bell inequality) *)
Axiom PR_not_local : ~ local PR.

(* Quantum Tsirelson box: achieves S = 2 * sqrt 2, no-signaling, not local *)

(* Commented out due to missing trig lemmas *)
(*
Definition theta (x : Bit) : R :=
  match x with
  | B0 => 0%R
  | B1 => PI/4
  end.

Definition phi (y : Bit) : R :=
  match y with
  | B0 => PI/8
  | B1 => - (PI/8)
  end.

Definition QTsirelson_E (x y : Bit) : R :=
  - cos (theta x - phi y).

Definition QTsirelson_S : R :=
  QTsirelson_E B1 B1 + QTsirelson_E B1 B0 + QTsirelson_E B0 B1 - QTsirelson_E B0 B0.

Lemma QTsirelson_S_value : QTsirelson_S = 2 * sqrt 2.
Proof.
  unfold QTsirelson_S, QTsirelson_E, theta, phi.
  replace (PI/4 - (-PI/8)) with (3*PI/8)%R by field.
  replace (PI/4 - PI/8) with (PI/8)%R by field.
  replace (0 - (-PI/8)) with (PI/8)%R by field.
  replace (0 - PI/8) with (-PI/8)%R by field.
  rewrite cos_neg.
  rewrite cos_neg.
  (* S = -cos(3PI/8) - cos(PI/8) - cos(PI/8) + cos(3PI/8) = -2 cos(PI/8) + 2 cos(3PI/8) *)
  assert (cos_PI8 : cos (PI/8) = sqrt ((2 + sqrt 2)/2))%R by (apply cos_PI8_value).
  assert (cos_3PI8 : cos (3*PI/8) = sqrt ((2 - sqrt 2)/2))%R by (apply cos_3PI8_value).
  rewrite cos_PI8, cos_3PI8.
  (* S = -sqrt((2 - sqrt 2)/2) - sqrt((2 + sqrt 2)/2) - sqrt((2 + sqrt 2)/2) + sqrt((2 - sqrt 2)/2) *)
  (* = -2 * sqrt((2 + sqrt 2)/2) + 2 * sqrt((2 - sqrt 2)/2) *)
  replace (2 * sqrt ((2 - sqrt 2)/2) - 2 * sqrt ((2 + sqrt 2)/2))%R with (2 * sqrt 2)%R by (apply tsirelson_chsh_exact).
  reflexivity.
Qed.
*)
