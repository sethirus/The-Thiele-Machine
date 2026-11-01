(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file exhibits the one hole in the premise-free step law, a partial step that stops, and shows that totalising the halt turns it into a merge; it stands alone from the certification-system kernel. *)
(* Break attempt: halting. A machine with a partial step (no successor = stopped) can raise a
   permanent reading on finitely many states with NO merge: two states, a -> b, b stops.
   So the premise-free law needs the step to be total. Here is the exact statement of the hole,
   and the exact statement of what closes it: making the halt a fixed point (the deterministic
   model's halting convention) turns it into a merge. *)
Require Import Arith Lia.

Inductive S2 := A | B.
Definition pstep (s : S2) : option S2 := match s with A => Some B | B => None end.
Definition reading (s : S2) := match s with A => false | B => true end.

(* the partial machine raises the reading and has no collision *)
Theorem partial_raises_without_merge :
  reading A = false /\ pstep A = Some B /\ reading B = true /\
  (forall x y z, pstep x = Some z -> pstep y = Some z -> x = y).
Proof. repeat split; auto. intros x y z Hx Hy. destruct x, y; simpl in *; congruence. Qed.

(* close the hole: totalise with halt = stay. now the raise is a merge *)
Definition tstep (s : S2) : S2 := match pstep s with Some t => t | None => s end.
Theorem totalised_halt_is_merge : tstep A = tstep B /\ A <> B.
Proof. split. reflexivity. discriminate. Qed.
