(** CzLink: nesting by simulation, in the abstract.

    A driven system is a machine that runs by itself: states that carry their
    own ledger, a step that may stop, and a record bit.  A link from X to Y,
    both started somewhere, says that Y runs X inside it:

      every point of X's run is matched by a point of Y's run;
      at the matched points the record bits are equal and the ledger of Y is
      the ledger of X plus a surcharge s;
      the surcharge is 0 while the record is down and lies between lo and hi
      once it is up;
      X halts exactly when Y halts, and X's record ever rises exactly when
      Y's does;
      the matched states are related by the relation of the link (the
      decoding of Y's state back to X's).

    What is proved here, for links in general:

      cmpz_link_id          every system is linked to itself, with no
                            surcharge;
      cmpz_link_compose     links compose: the record is still exactly
                            preserved, the relation is the composite
                            relation, halting and the record's rising still
                            correspond, and the surcharges add: the bounds
                            of the composite are the sums of the bounds;
      cmpz_tower            a tower of k links, from level 0 to level k,
                            keeps the record bit exactly at every point,
                            adds no surcharge while the record is down, and
                            once it is up adds between the sum of the k lower
                            bounds and the sum of the k upper bounds;
      cmpz_tower_uniform    a tower of k links with the same bounds adds
                            between k lo and k hi.

    CzTower instantiates this with the real links of the repository (a
    computably presented machine run by the fixed host program U_P, and a
    priced guest run by U_P). *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file is
   about driven systems in the abstract (states with a ledger, a step that may
   stop, a record bit) and imports nothing but the standard library. Its
   instances over the repository's machines, the computably presented machine
   and the priced guest run by U_P, are in CzTower.v. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.

Record cmpz_ds : Type := mk_ds {
  ds_state : Type;
  ds_next : ds_state -> option ds_state;
  ds_led : ds_state -> nat;
  ds_rec : ds_state -> bool
}.

Fixpoint ds_run (D : cmpz_ds) (n : nat) (s : ds_state D) : ds_state D :=
  match n with
  | 0 => s
  | S n' => match ds_next D s with None => s | Some s' => ds_run D n' s' end
  end.

Definition ds_halted (D : cmpz_ds) (s : ds_state D) : Prop := ds_next D s = None.

Lemma ds_run_add : forall D m n s, ds_run D (m + n) s = ds_run D n (ds_run D m s).
Proof.
  intros D. induction m as [| m IH]; intros n s; simpl; [reflexivity |].
  destruct (ds_next D s) as [s' |] eqn:E; [apply IH |].
  destruct n as [| n]; simpl; [reflexivity | rewrite E; reflexivity].
Qed.

Record cmpz_link (X Y : cmpz_ds) (x0 : ds_state X) (y0 : ds_state Y) (lo hi : nat)
    (rel : ds_state X -> ds_state Y -> Prop) : Prop := mk_link {
  lk_points : forall n, exists t s,
    rel (ds_run X n x0) (ds_run Y t y0) /\
    ds_rec Y (ds_run Y t y0) = ds_rec X (ds_run X n x0) /\
    ds_led Y (ds_run Y t y0) = ds_led X (ds_run X n x0) + s /\
    (ds_rec X (ds_run X n x0) = false -> s = 0) /\
    (ds_rec X (ds_run X n x0) = true -> lo <= s /\ s <= hi);
  lk_halting :
    (exists n, ds_halted X (ds_run X n x0)) <-> (exists t, ds_halted Y (ds_run Y t y0));
  lk_flag :
    (exists t, ds_rec Y (ds_run Y t y0) = true) <-> (exists n, ds_rec X (ds_run X n x0) = true)
}.

Theorem cmpz_link_id : forall D d0, cmpz_link D D d0 d0 0 0 (fun x y => x = y).
Proof.
  intros D d0. split.
  - intro n. exists n, 0. repeat split; try reflexivity; try lia.
  - split; intro H; exact H.
  - split; intro H; exact H.
Qed.

Definition cmpz_rel_comp {X Y Z : cmpz_ds}
    (r1 : ds_state X -> ds_state Y -> Prop) (r2 : ds_state Y -> ds_state Z -> Prop) :
    ds_state X -> ds_state Z -> Prop :=
  fun x z => exists y, r1 x y /\ r2 y z.

Theorem cmpz_link_compose : forall {X Y Z x0 y0 z0 lo1 hi1 lo2 hi2 r1 r2},
  cmpz_link X Y x0 y0 lo1 hi1 r1 -> cmpz_link Y Z y0 z0 lo2 hi2 r2 ->
  cmpz_link X Z x0 z0 (lo1 + lo2) (hi1 + hi2) (cmpz_rel_comp r1 r2).
Proof.
  intros X Y Z x0 y0 z0 lo1 hi1 lo2 hi2 r1 r2 L1 L2. split.
  - intro n. destruct (lk_points _ _ _ _ _ _ _ L1 n) as [t1 [s1 [R1 [E1 [W1 [D1 U1]]]]]].
    destruct (lk_points _ _ _ _ _ _ _ L2 t1) as [t2 [s2 [R2 [E2 [W2 [D2 U2]]]]]].
    exists t2, (s1 + s2). split; [exists (ds_run Y t1 y0); split; assumption |].
    split; [rewrite E2, E1; reflexivity |].
    split; [rewrite W2, W1; lia |].
    split.
    + intro Hr. rewrite (D1 Hr). rewrite E1 in D2. rewrite (D2 Hr). lia.
    + intro Hr. destruct (U1 Hr) as [A1 B1]. rewrite E1 in U2. destruct (U2 Hr) as [A2 B2]. lia.
  - split; intro H.
    + apply (proj1 (lk_halting _ _ _ _ _ _ _ L1)) in H. apply (proj1 (lk_halting _ _ _ _ _ _ _ L2)) in H. exact H.
    + apply (proj2 (lk_halting _ _ _ _ _ _ _ L2)) in H. apply (proj2 (lk_halting _ _ _ _ _ _ _ L1)) in H. exact H.
  - split; intro H.
    + apply (proj1 (lk_flag _ _ _ _ _ _ _ L2)) in H. apply (proj1 (lk_flag _ _ _ _ _ _ _ L1)) in H. exact H.
    + apply (proj2 (lk_flag _ _ _ _ _ _ _ L1)) in H. apply (proj2 (lk_flag _ _ _ _ _ _ _ L2)) in H. exact H.
Qed.

(** A link whose bounds are loosened is a link. *)
Theorem cmpz_link_weaken : forall {X Y x0 y0 lo hi lo' hi' r},
  cmpz_link X Y x0 y0 lo hi r -> lo' <= lo -> hi <= hi' -> cmpz_link X Y x0 y0 lo' hi' r.
Proof.
  intros X Y x0 y0 lo hi lo' hi' r L Hlo Hhi. split.
  - intro n. destruct (lk_points _ _ _ _ _ _ _ L n) as [t [s [R [E [W [D U]]]]]].
    exists t, s. split; [exact R |]. split; [exact E |]. split; [exact W |]. split; [exact D |].
    intro Hr. destruct (U Hr) as [A B]. split; lia.
  - exact (lk_halting _ _ _ _ _ _ _ L).
  - exact (lk_flag _ _ _ _ _ _ _ L).
Qed.

(** * Towers *)

Section Tower.

Variable D : nat -> cmpz_ds.
Variable d0 : forall i, ds_state (D i).
Variable lo hi : nat -> nat.
Variable rel : forall i, ds_state (D i) -> ds_state (D (S i)) -> Prop.
Variable L : forall i, cmpz_link (D i) (D (S i)) (d0 i) (d0 (S i)) (lo i) (hi i) (rel i).

Fixpoint cmpz_sum (f : nat -> nat) (k : nat) : nat :=
  match k with 0 => 0 | S k' => cmpz_sum f k' + f k' end.

Fixpoint cmpz_tower_rel (k : nat) : ds_state (D 0) -> ds_state (D k) -> Prop :=
  match k with
  | 0 => fun x y => x = y
  | S k' => cmpz_rel_comp (cmpz_tower_rel k') (rel k')
  end.

(** A tower of k links keeps the record exactly, adds nothing while the record
    is down, and adds between the sum of the lower bounds and the sum of the
    upper bounds once it is up. *)
Theorem cmpz_tower : forall k,
  cmpz_link (D 0) (D k) (d0 0) (d0 k) (cmpz_sum lo k) (cmpz_sum hi k) (cmpz_tower_rel k).
Proof.
  induction k as [| k IH].
  - exact (cmpz_link_id (D 0) (d0 0)).
  - exact (cmpz_link_compose IH (L k)).
Qed.

End Tower.

(** A tower whose links all have the same bounds adds k times them. *)
Corollary cmpz_tower_uniform : forall (D : nat -> cmpz_ds) (d0 : forall i, ds_state (D i)) lo hi
    (rel : forall i, ds_state (D i) -> ds_state (D (S i)) -> Prop),
  (forall i, cmpz_link (D i) (D (S i)) (d0 i) (d0 (S i)) lo hi (rel i)) ->
  forall k, cmpz_link (D 0) (D k) (d0 0) (d0 k) (k * lo) (k * hi) (cmpz_tower_rel D rel k).
Proof.
  intros D d0 lo hi rel L k.
  assert (Hs : forall c k, cmpz_sum (fun _ => c) k = k * c).
  { intros c k0. induction k0 as [| k0 IH]; simpl; [reflexivity | rewrite IH; lia]. }
  pose proof (cmpz_tower D d0 (fun _ => lo) (fun _ => hi) rel L k) as T.
  rewrite !Hs in T. exact T.
Qed.

Print Assumptions cmpz_link_id.
Print Assumptions cmpz_link_compose.
Print Assumptions cmpz_link_weaken.
Print Assumptions cmpz_tower.
Print Assumptions cmpz_tower_uniform.
