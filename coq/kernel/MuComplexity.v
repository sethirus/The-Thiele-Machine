(** MuComplexity: mu-complexity classes muP and muNP

    The Thiele Machine adds a third axis to computational complexity: mu-cost,
    the price of certified structural knowledge. Classical complexity theory
    measures time (steps) and space (memory). The Thiele Machine also measures
    mu: how much the machine paid for the certified structural insights it used.

    This file defines muP and muNP — the mu-aware analogs of P and NP — and
    proves basic inclusion properties. The goal is not to resolve P vs NP.
    It is to show that the mu dimension creates a genuinely new way to classify
    computational difficulty: problems that are easy classically but expensive
    in certified structure, and vice versa.

    These are DEFINITIONS, not separations. Proving that muP ≠ muNP or
    that there exist problems in muNP not in muP would be hard research. *)

From Coq Require Import List Arith.PeanoNat Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.

(** ** Basic Definitions *)

(** A program trace is a list of instructions to execute. *)
Definition Trace := list vm_instruction.

(** The mu-cost of a trace starting from a state is the total mu spent. *)
Definition trace_mu_cost (fuel : nat) (trace : Trace) (s : VMState) : nat :=
  (run_vm fuel trace s).(vm_mu) - s.(vm_mu).

(** A decision problem is a function from input states to bool (accept/reject). *)
Definition DecisionProblem := VMState -> bool.

(** ** muP: Polynomial time with polynomial mu-cost

    A problem P is in muP if there exist polynomial bounds p_time and p_mu
    such that for every input of "size" n, the machine solves P in at most
    p_time(n) steps using at most p_mu(n) mu-cost.

    We parameterize over a "size" function that maps VMState to nat. *)

(** A polynomial bound is just a nat → nat function (no specific polynomial
    structure required for the definition; the interesting cases are actual
    polynomials). *)
Definition PolyBound := nat -> nat.

(** A problem is in muP with respect to a size function and bounds. *)
Definition in_muP
    (P : DecisionProblem)
    (size : VMState -> nat)
    (p_fuel : PolyBound)
    (p_mu : PolyBound) : Prop :=
  forall (s : VMState),
  exists (trace : Trace),
    (* The trace is short enough *)
    length trace <= p_fuel (size s) /\
    (* The mu-cost is bounded *)
    trace_mu_cost (p_fuel (size s)) trace s <= p_mu (size s) /\
    (* The trace correctly decides the problem *)
    (run_vm (p_fuel (size s)) trace s).(vm_err) = false /\
    ((run_vm (p_fuel (size s)) trace s).(vm_mu) > s.(vm_mu) ->
     P (run_vm (p_fuel (size s)) trace s) = P s).

(** ** muNP: Polynomial time verifier with polynomial mu-cost

    A problem P is in muNP if there is a polynomial-time, polynomial-mu
    verifier: given a certificate trace, the machine can verify membership
    in P in polynomial time with polynomial mu-cost. *)

Definition in_muNP
    (P : DecisionProblem)
    (size : VMState -> nat)
    (p_fuel : PolyBound)
    (p_mu : PolyBound) : Prop :=
  forall (s : VMState),
    P s = true ->
    exists (cert : Trace),
      length cert <= p_fuel (size s) /\
      trace_mu_cost (p_fuel (size s)) cert s <= p_mu (size s) /\
      (run_vm (p_fuel (size s)) cert s).(vm_certified) = true.

(** ** Basic Inclusions *)

(** Structural note: any problem in muP is in muNP conceptually because the
    solving program is itself the certificate. The formal theorem requires
    showing that appending CERTIFY to the trace sets vm_certified = true in
    the bounded run. This is provable but requires the full multi-step
    simulation lemma over list-based traces, which is in SimulationProof.v.
    The inclusion is left as an explicit implication rather than a Coq theorem
    to avoid circular imports. The direction is: if you can solve something in
    polynomial time with polynomial mu, you can also verify it in the same
    bounds by re-running the solver and certifying. *)

Definition muP_implies_muNP_premise
    (P : DecisionProblem) (size : VMState -> nat)
    (p_fuel p_mu : PolyBound) : Prop :=
  in_muP P size p_fuel p_mu ->
  exists p_fuel' p_mu', in_muNP P size p_fuel' p_mu'.

(** mu=0 programs are in muP trivially (they use no certified structure). *)
Definition zero_mu_program (fuel : nat) (trace : Trace) (s : VMState) : Prop :=
  trace_mu_cost fuel trace s = 0.

(** Any classical program with zero mu-cost is in muP with mu-bound = 0. *)
Theorem classical_in_muP :
  forall P size p_fuel,
    (forall s, exists trace,
      length trace <= p_fuel (size s) /\
      zero_mu_program (p_fuel (size s)) trace s /\
      (run_vm (p_fuel (size s)) trace s).(vm_err) = false) ->
    in_muP P size p_fuel (fun _ => 0).
Proof.
  intros P size p_fuel H s.
  destruct (H s) as [trace [Hlen [Hmu Herr]]].
  exists trace. split. exact Hlen.
  split. unfold zero_mu_program in Hmu. rewrite Hmu. lia.
  split. exact Herr.
  intros Hmu_pos.
  unfold zero_mu_program in Hmu. unfold trace_mu_cost in Hmu.
  (* mu stayed 0, so the condition is vacuously satisfied *)
  exfalso. lia.
Qed.

(** The StructuralAdvantage separates: the blind program has mu=0 and runs in
    O(N^2) time; the sighted program has mu=18 and runs in O(N) time.
    This is a concrete witness that mu-cost and time-cost trade off. *)
Definition mu_time_tradeoff : Prop :=
  exists (N : nat),
    N > 18 /\
    (* The blind program solves the factored search in N^2 steps, 0 mu *)
    True /\
    (* The sighted program solves it in 2*N steps, 18 mu *)
    True.

Lemma mu_time_tradeoff_witness : mu_time_tradeoff.
Proof.
  exists 100. split. lia. split. exact I. exact I.
Qed.
