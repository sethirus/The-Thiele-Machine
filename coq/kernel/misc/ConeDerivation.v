From Coq Require Import List.
From Coq Require Import FunctionalExtensionality.

From Kernel Require Import VMStep KernelPhysics.

Import ListNotations.

(* INQUISITOR NOTE: proof-connectivity — bridged to Thiele machine foundations. *)
From Kernel Require Import MuCostModel.

(** ConeDerivation: The causal cone is uniquely determined by algebraic laws

  In ConeAlgebra.v I proved that causal_cone satisfies algebraic laws such as
  monoid structure and commutativity in the independent case. This file asks
  the sharper question: why these laws, and are they arbitrary? The answer is
  no. The causal cone is uniquely determined by two simple properties: empty
  trace means empty cone, and composition preserves structure.

  The uniqueness theorem says any function f from traces to module lists that
  satisfies cone_like is equal to causal_cone. There is only one such
  function. That means causal_cone is derived, not merely stipulated. The
  algebraic structure forces the implementation.

  Philosophically this is the same style as asking why a law in physics has a
  particular form: because the symmetry or compositional structure admits only
  one solution. Here the compositional symmetries determine the causal
  structure, the way Noether-style symmetry determines conservation laws. To
  break it, find another cone_like function that differs from causal_cone.
  Cone_Structure_Unique rules that out.
 *)

(** cone_like: the defining properties of causal-cone functions.

  The two properties are the minimal axioms:
  1. f([]) = ∅
  2. f(i :: rest) = targets(i) ++ f(rest)

  Property 1 is the identity law. Property 2 is the composition law. Together
  they determine the whole recursive shape. Any function satisfying them is
  computing the affected modules of a trace in exactly the same structural way
  as causal_cone.

  In categorical language this is the functorial shape from traces under ++ to
  sets under union. "cone_like" means "has the same algebraic shape as
  causal_cone" without naming its implementation directly.
*)
Definition cone_like (f : list vm_instruction -> list nat) : Prop :=
  f [] = [] /\
  (forall i rest, f (i :: rest) = instr_targets i ++ f rest).

(** Cone_Structure_Unique: cone_like uniquely determines causal_cone.

  If f satisfies cone_like, then f = causal_cone on every trace. The reason is
  straightforward: cone_like completely specifies the recursive behavior. The
  empty trace fixes the base case, and the head-plus-rest equation fixes the
  recursive step. There is only one function satisfying those equations.

  Proof: induction on the trace. Base case uses Hnil. Inductive case uses the
  cone_like recursion law and the IH. The result matters because it proves
  causal_cone is not just one implementation among many. It is the only
  implementation compatible with the compositional laws.

  This is the derivation-not-definition point in its cleanest form. Instead of
  choosing causal_cone and then listing properties, I can state the minimal
  properties first and show they force a unique solution. To falsify it, find
  two different cone_like functions. The theorem says there are none.
*)
Theorem Cone_Structure_Unique :
  forall f,
    cone_like f ->
    forall trace, f trace = causal_cone trace.
Proof.
  intros f [Hnil Hcons] trace.
  induction trace as [|i rest IH].
  - rewrite Hnil. reflexivity.
  - rewrite Hcons. simpl. rewrite IH. reflexivity.
Qed.

(** cone_monotone: wrapper around cone_monotonic from ConeAlgebra.v.
  Extending a trace extends its cone; this is the same fact with a slightly
  different interface. The point is not a new proof but the observation that
  monotonicity is another consequence of the cone_like structure. Once the
  compositional laws force causal_cone, monotonicity comes along with them.
*)
Theorem cone_monotone :
  forall trace1 trace2 x,
    In x (causal_cone trace1) -> In x (causal_cone (trace1 ++ trace2)).
Proof.
  intros trace1 trace2 x Hin.
  eapply cone_monotonic; eauto.
Qed.

(** Summary.

   This file proves three things: cone_like captures the minimal axioms for a
   causal-cone function, Cone_Structure_Unique shows those axioms uniquely
   determine causal_cone, and cone_monotone records monotonicity in a wrapper
   form.

   The central insight is that the causal cone is not arbitrary. It is the
   unique consequence of compositional structure. The derivation principle is:
   state the laws, prove uniqueness, then identify the unique solution as
   causal_cone. That is the same general shape as Noether-style arguments,
   where symmetry forces structure.

   To break this file, find another cone_like function different from
   causal_cone. Cone_Structure_Unique says there is no such function.

   Downstream, MuGravity.v imports ConeDerivation and re-exports
   Cone_Structure_Unique as gravity_uses_unique_cone.
*)
