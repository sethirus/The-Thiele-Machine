(** ShadowPricing: the exact price of certification cannot be read off the
    shadow.

    [exact_commitment_pricing_characterization] says the only charge that
    meets the certification floor and never overcharges is the one that
    charges exactly the certification flips, one unit each. This file asks
    who can compute that charge.

    A shadow account sees only a window onto the state: the observation
    before a step and the observation after it. Its price for a step is a
    function of that observed transition. The theorem here says:

    - If two steps show the same observed transition, and one of them flips
      the certification reading while the other does not, then no shadow
      account prices exactly. Any shadow price that meets the floor charges
      the step that did not certify.
    - If the window shows the reading, a shadow account prices exactly.

    So exact pricing needs the reading in what the account carries. On the
    VM both windows the book names, [bare_observable] and [forget], have such
    a collision from the clean start: [CERTIFY] against a [JUMP] with the
    same visible effect. The exact price lives in the step, or in a window
    that shows certification; the read/write shadow cannot carry it. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.
From Kernel Require Import NecessityAbstract.
From Kernel Require Import BlindnessRepresentation.
From Kernel Require Import ProjectionNonExistence.

Section ShadowPricing.

Variables (S I O : Type).
Variable step : S -> I -> S.
Variable cert : S -> bool.
Variable obs : S -> O.

(** The step flips the reading on. *)
Definition flips (s : S) (i : I) : bool :=
  negb (cert s) && cert (step s i).

(** A shadow price reads only the observed transition. *)
Definition shadow_cost (price : O -> O -> nat) (s : S) (i : I) : nat :=
  price (obs s) (obs (step s i)).

Definition meets_floor (cost : S -> I -> nat) : Prop :=
  forall s i, flips s i = true -> cost s i >= 1.

Definition never_overcharges (cost : S -> I -> nat) : Prop :=
  forall s i, flips s i = false -> cost s i = 0.

(** Two steps that look the same through the window, one certifying and one
    not. *)
Definition shadow_collision : Prop :=
  exists s1 i1 s2 i2,
    obs s1 = obs s2 /\
    obs (step s1 i1) = obs (step s2 i2) /\
    flips s1 i1 = true /\
    flips s2 i2 = false.

(** Every shadow price that meets the floor charges a step that did not
    certify. *)
Theorem shadow_floor_overcharges :
  shadow_collision ->
  forall price,
    meets_floor (shadow_cost price) ->
    exists s i, flips s i = false /\ shadow_cost price s i >= 1.
Proof.
  intros [s1 [i1 [s2 [i2 [Hpre [Hpost [Hf1 Hf2]]]]]]] price Hfloor.
  exists s2, i2. split; [exact Hf2 |].
  unfold shadow_cost. rewrite <- Hpre, <- Hpost.
  exact (Hfloor s1 i1 Hf1).
Qed.

(** So no shadow price is exact. *)
Theorem shadow_cannot_price_exactly :
  shadow_collision ->
  forall price,
    ~ (meets_floor (shadow_cost price) /\
       never_overcharges (shadow_cost price)).
Proof.
  intros Hcol price [Hfloor Hno].
  destruct (shadow_floor_overcharges Hcol price Hfloor) as [s [i [Hf Hc]]].
  rewrite (Hno s i Hf) in Hc. inversion Hc.
Qed.

(** The exact price is a function of the step itself. *)
Definition step_price (s : S) (i : I) : nat :=
  if flips s i then 1 else 0.

Theorem step_price_is_exact :
  meets_floor step_price /\ never_overcharges step_price.
Proof.
  split; intros s i H; unfold step_price; rewrite H; [unfold ge; apply le_n | reflexivity].
Qed.

(** A window that shows the reading prices exactly. *)
Theorem window_showing_reading_prices_exactly :
  forall read : O -> bool,
    (forall s, cert s = read (obs s)) ->
    exists price,
      meets_floor (shadow_cost price) /\ never_overcharges (shadow_cost price).
Proof.
  intros read Hread.
  exists (fun o o' => if negb (read o) && read o' then 1 else 0).
  assert (Heq : forall s i,
             shadow_cost (fun o o' => if negb (read o) && read o' then 1 else 0) s i
             = step_price s i).
  { intros s i. unfold shadow_cost, step_price, flips.
    rewrite <- (Hread s), <- (Hread (step s i)). reflexivity. }
  split; intros s i H; rewrite Heq; unfold step_price; rewrite H;
    [unfold ge; apply le_n | reflexivity].
Qed.

(** A window that shows the reading has no collision. *)
Theorem window_showing_reading_has_no_collision :
  forall read : O -> bool,
    (forall s, cert s = read (obs s)) ->
    ~ shadow_collision.
Proof.
  intros read Hread [s1 [i1 [s2 [i2 [Hpre [Hpost [Hf1 Hf2]]]]]]].
  unfold flips in Hf1, Hf2.
  rewrite (Hread s1), (Hread (step s1 i1)) in Hf1.
  rewrite (Hread s2), (Hread (step s2 i2)) in Hf2.
  rewrite <- Hpre, <- Hpost in Hf2.
  rewrite Hf1 in Hf2. discriminate.
Qed.

End ShadowPricing.

Arguments flips {S I}.
Arguments shadow_cost {S I O}.
Arguments meets_floor {S I}.
Arguments never_overcharges {S I}.
Arguments shadow_collision {S I O}.

(** * The VM *)

Definition vm_cert (s : VMState) : bool := s.(vm_certified).

(** From the clean start, [CERTIFY 0] and [JUMP 1 0] leave the same program
    counter, registers, and memory. One certifies, the other does not. *)
Theorem vm_bare_observable_collision :
  shadow_collision vm_apply vm_cert bare_observable.
Proof.
  exists abs_zero, (instr_certify 0), abs_zero, (instr_jump 1 0).
  repeat split; reflexivity.
Qed.

(** From the clean start, [CERTIFY 0] and [JUMP 1 1] also agree on the
    ledger, so the four-field [forget] window has a collision too. *)
Theorem vm_forget_collision :
  shadow_collision vm_apply vm_cert forget.
Proof.
  exists abs_zero, (instr_certify 0), abs_zero, (instr_jump 1 1).
  repeat split; reflexivity.
Qed.

(** No account that prices from the bare shadow prices VM certification
    exactly. *)
Theorem vm_bare_shadow_cannot_price_exactly :
  forall price,
    ~ (meets_floor vm_apply vm_cert (shadow_cost vm_apply bare_observable price) /\
       never_overcharges vm_apply vm_cert (shadow_cost vm_apply bare_observable price)).
Proof.
  apply shadow_cannot_price_exactly. exact vm_bare_observable_collision.
Qed.

(** The same holds with the ledger in the window. *)
Theorem vm_forget_shadow_cannot_price_exactly :
  forall price,
    ~ (meets_floor vm_apply vm_cert (shadow_cost vm_apply forget price) /\
       never_overcharges vm_apply vm_cert (shadow_cost vm_apply forget price)).
Proof.
  apply shadow_cannot_price_exactly. exact vm_forget_collision.
Qed.
