(** AxWindow: the price of moving along the axis cannot be read off a window
    of the shadow unless the window sees the movement.

    A window shows the observation before a step and after it.  A shadow
    price is a function of that observed transition.  The exact price of a
    step is 1 when the step leaves the down-set of the record and 0
    otherwise.

    Results (all closed):

      ax_window_collision_overcharges   if two steps look the same through the
                                        window and one leaves the down-set
                                        while the other does not, every shadow
                                        price that meets the floor charges a
                                        step that moved nothing.
      ax_window_no_exact_price          so no shadow price is exact.
      ax_window_sees_record_exact       a window that shows the record prices
                                        exactly, and has no collision.
      ax_window_exact_iff_no_collision  on a finite system an exact shadow
                                        price exists exactly when there is no
                                        collision.
      ax_overcharge_tight               the least overcharge along a run is
                                        the number of shadowed non-moving
                                        steps, and it is attained.
      ax_exact_without_position         a window can price exactly without
                                        showing where the record is: on a
                                        counter with rising and quiet steps,
                                        parity flips exactly on the rises,
                                        no constant price is exact, and the
                                        parity window prices every step
                                        exactly. Pricing needs the movement,
                                        not the position.
      ax_threshold_window_blind         a window that shows one threshold only
                                        prices that threshold exactly and no
                                        other.

    The book's statements for one bit ([shadow_cannot_price_exactly],
    [window_showing_reading_prices_exactly]) are the two-point case
    ([two_point_shadow_cannot_price_exactly]). *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import ShadowPricing.
From Kernel Require Import AxCore.

Section Window.

Variable A : Type.
Variable P : BPre A.
Variable X : AxSys A P.
Variable O : Type.
Variable obs : ax_state A P X -> O.

Local Notation S := (ax_state A P X).
Local Notation I := (ax_instr A P X).
Local Notation step := (ax_step A P X).
Local Notation rc := (ax_rec A P X).

Definition ax_shadow_cost (price : O -> O -> nat) (s : S) (i : I) : nat :=
  price (obs s) (obs (step s i)).

Definition ax_meets_floor (cost : S -> I -> nat) : Prop :=
  forall s i, ax_exits (X := X) s i -> cost s i >= 1.

Definition ax_never_overcharges (cost : S -> I -> nat) : Prop :=
  forall s i, ~ ax_exits (X := X) s i -> cost s i = 0.

Definition ax_window_collision : Prop :=
  exists s1 i1 s2 i2,
    obs s1 = obs s2 /\ obs (step s1 i1) = obs (step s2 i2) /\
    ax_exits (X := X) s1 i1 /\ ~ ax_exits (X := X) s2 i2.

Theorem ax_window_collision_overcharges :
  ax_window_collision ->
  forall price, ax_meets_floor (ax_shadow_cost price) ->
    exists s i, ~ ax_exits (X := X) s i /\ ax_shadow_cost price s i >= 1.
Proof.
  intros [s1 [i1 [s2 [i2 [Hpre [Hpost [Hf1 Hf2]]]]]]] price Hfloor.
  exists s2, i2. split; [exact Hf2 |].
  unfold ax_shadow_cost. rewrite <- Hpre, <- Hpost. exact (Hfloor s1 i1 Hf1).
Qed.

Theorem ax_window_no_exact_price :
  ax_window_collision ->
  forall price,
    ~ (ax_meets_floor (ax_shadow_cost price) /\
       ax_never_overcharges (ax_shadow_cost price)).
Proof.
  intros Hcol price [Hfloor Hno].
  destruct (ax_window_collision_overcharges Hcol price Hfloor) as [s [i [Hf Hc]]].
  rewrite (Hno s i Hf) in Hc. inversion Hc.
Qed.

(** The exact price is a function of the step. *)
Definition ax_step_price (s : S) (i : I) : nat :=
  if bp_leb A P (rc (step s i)) (rc s) then 0 else 1.

Theorem ax_step_price_exact :
  ax_meets_floor ax_step_price /\ ax_never_overcharges ax_step_price.
Proof.
  split.
  - intros s i H. unfold ax_step_price.
    destruct (bp_leb A P (rc (step s i)) (rc s)) eqn:E; [| lia].
    exfalso. apply H. exact E.
  - intros s i H. unfold ax_step_price.
    destruct (bp_leb A P (rc (step s i)) (rc s)) eqn:E; [reflexivity |].
    exfalso. apply H. unfold ax_exits, bp_le. rewrite E. discriminate.
Qed.

(** A window that shows the record prices exactly. *)
Theorem ax_window_sees_record_exact :
  forall read : O -> A, (forall s, rc s = read (obs s)) ->
    (exists price, ax_meets_floor (ax_shadow_cost price) /\
                   ax_never_overcharges (ax_shadow_cost price)) /\
    ~ ax_window_collision.
Proof.
  intros read Hread. split.
  - exists (fun o o' => if bp_leb A P (read o') (read o) then 0 else 1).
    assert (Heq : forall s i,
      ax_shadow_cost (fun o o' => if bp_leb A P (read o') (read o) then 0 else 1) s i
      = ax_step_price s i).
    { intros s i. unfold ax_shadow_cost, ax_step_price.
      rewrite <- (Hread s), <- (Hread (step s i)). reflexivity. }
    split; intros s i H; rewrite Heq; [apply (proj1 ax_step_price_exact) | apply (proj2 ax_step_price_exact)]; exact H.
  - intros [s1 [i1 [s2 [i2 [Hpre [Hpost [Hf1 Hf2]]]]]]]. apply Hf2.
    unfold ax_exits in *. intro Hle. apply Hf1.
    unfold bp_le in *. rewrite (Hread s1), (Hread (step s1 i1)), Hpre, Hpost.
    rewrite <- (Hread s2), <- (Hread (step s2 i2)). exact Hle.
Qed.

(** ** Finite systems: exact pricing through a window is exactly the absence
    of a collision. *)

Variable obs_eq_dec : forall a b : O, {a = b} + {a <> b}.

Theorem ax_window_exact_iff_no_collision :
  forall (allS : list S) (allI : list I),
    (forall s, In s allS) -> (forall i, In i allI) ->
    ((exists price, ax_meets_floor (ax_shadow_cost price) /\
                    ax_never_overcharges (ax_shadow_cost price))
     <-> ~ ax_window_collision).
Proof.
  intros allS allI HS HI. split.
  - intros [price [Hf Hn]] Hcol. exact (ax_window_no_exact_price Hcol price (conj Hf Hn)).
  - intros Hnc.
    set (flipb := fun o o' =>
      existsb (fun s => existsb (fun i =>
         andb (if obs_eq_dec (obs s) o then true else false)
              (andb (if obs_eq_dec (obs (step s i)) o' then true else false)
                    (negb (bp_leb A P (rc (step s i)) (rc s))))) allI) allS).
    exists (fun o o' => if flipb o o' then 1 else 0).
    assert (Hkey : forall s i, flipb (obs s) (obs (step s i)) = true <->
                               ax_exits (X := X) s i).
    { intros s i. unfold flipb. split.
      - intro H. apply existsb_exists in H as [s' [_ H]].
        apply existsb_exists in H as [i' [_ H]].
        apply andb_true_iff in H as [H1 H]. apply andb_true_iff in H as [H2 H3].
        destruct (obs_eq_dec (obs s') (obs s)) as [E1 |]; [| discriminate].
        destruct (obs_eq_dec (obs (step s' i')) (obs (step s i))) as [E2 |]; [| discriminate].
        destruct (bp_leb A P (rc (step s i)) (rc s)) eqn:Eb.
        + exfalso. apply Hnc. exists s', i', s, i.
          split; [exact E1 |]. split; [exact E2 |]. split.
          * unfold ax_exits, bp_le. intro Hle.
            rewrite (negb_true_iff _ ) in H3. rewrite Hle in H3. discriminate.
          * unfold ax_exits, bp_le. intro Hn. apply Hn. exact Eb.
        + unfold ax_exits, bp_le. rewrite Eb. discriminate.
      - intro H. apply existsb_exists. exists s. split; [apply HS |].
        apply existsb_exists. exists i. split; [apply HI |].
        destruct (obs_eq_dec (obs s) (obs s)) as [_ | Hne]; [| exfalso; apply Hne; reflexivity].
        destruct (obs_eq_dec (obs (step s i)) (obs (step s i))) as [_ | Hne];
          [| exfalso; apply Hne; reflexivity].
        simpl. destruct (bp_leb A P (rc (step s i)) (rc s)) eqn:Eb; [| reflexivity].
        exfalso. apply H. exact Eb. }
    split.
    + intros s i H. unfold ax_shadow_cost.
      destruct (flipb (obs s) (obs (step s i))) eqn:E; [lia |].
      exfalso. assert (Hx : flipb (obs s) (obs (step s i)) = true) by (apply Hkey; exact H).
      congruence.
    + intros s i H. unfold ax_shadow_cost.
      destruct (flipb (obs s) (obs (step s i))) eqn:E; [| reflexivity].
      exfalso. apply H. apply Hkey. exact E.
Qed.

(** ** The least overcharge *)

(** A step is shadowed when some step that does leave the down-set looks
    the same through the window. *)
Definition ax_shadowed (s : S) (i : I) : Prop :=
  exists s' i', obs s' = obs s /\ obs (step s' i') = obs (step s i) /\
                ax_exits (X := X) s' i'.

Fixpoint ax_shadowed_count (tr : list I) (s : S) (dec : forall s i, {ax_shadowed s i} + {~ ax_shadowed s i})
    (decx : forall s i, {ax_exits (X := X) s i} + {~ ax_exits (X := X) s i}) : nat :=
  match tr with
  | [] => 0
  | i :: rest =>
      (if decx s i then 0 else if dec s i then 1 else 0)
      + ax_shadowed_count rest (step s i) dec decx
  end.

(** Every shadow price that meets the floor charges every shadowed step at
    least 1, so along a run it charges at least the number of shadowed
    steps that do not move. *)
Theorem ax_overcharge_lower :
  forall price, ax_meets_floor (ax_shadow_cost price) ->
  forall (dec : forall s i, {ax_shadowed s i} + {~ ax_shadowed s i})
         (decx : forall s i, {ax_exits (X := X) s i} + {~ ax_exits (X := X) s i})
         tr s,
    (fix total (l : list I) (s : S) : nat :=
       match l with [] => 0 | i :: r => ax_shadow_cost price s i + total r (step s i) end) tr s
    >= ax_shadowed_count tr s dec decx.
Proof.
  intros price Hf dec decx tr. induction tr as [| i rest IH]; intro s; simpl; [lia |].
  specialize (IH (step s i)).
  destruct (decx s i) as [Hx | Hnx].
  - lia.
  - destruct (dec s i) as [Hsh | Hnsh]; [| lia].
    destruct Hsh as [s' [i' [Hpre [Hpost Hex']]]].
    assert (Hc : ax_shadow_cost price s i >= 1).
    { unfold ax_shadow_cost. rewrite <- Hpre, <- Hpost. exact (Hf s' i' Hex'). }
    lia.
Qed.

(** The bound is attained: charge 1 on exactly the shadowed transitions. *)
Theorem ax_overcharge_tight :
  forall (decobs : forall o o', {exists s i, obs s = o /\ obs (step s i) = o' /\
                                    ax_exits (X := X) s i} +
                                 {~ exists s i, obs s = o /\ obs (step s i) = o' /\
                                    ax_exits (X := X) s i}),
  exists price, ax_meets_floor (ax_shadow_cost price) /\
    forall s i, ~ ax_exits (X := X) s i ->
      (ax_shadow_cost price s i = 1 <-> ax_shadowed s i) /\
      (~ ax_shadowed s i -> ax_shadow_cost price s i = 0).
Proof.
  intro decobs.
  exists (fun o o' => if decobs o o' then 1 else 0). split.
  - intros s i H. unfold ax_shadow_cost.
    destruct (decobs (obs s) (obs (step s i))) as [_ | Hn]; [lia |].
    exfalso. apply Hn. exists s, i. auto.
  - intros s i Hnx. unfold ax_shadow_cost.
    destruct (decobs (obs s) (obs (step s i))) as [Hy | Hn].
    + split.
      * split; [intros _; destruct Hy as [s' [i' [H1 [H2 H3]]]]; exists s', i'; auto
               | intros _; reflexivity].
      * intro Hns. exfalso. apply Hns. destruct Hy as [s' [i' [H1 [H2 H3]]]]. exists s', i'. auto.
    + split.
      * split; [intro H; discriminate H |].
        intro Hsh. exfalso. apply Hn. destruct Hsh as [s' [i' [H1 [H2 H3]]]].
        exists s', i'. rewrite H1, H2. auto.
      * intros _. reflexivity.
Qed.

End Window.

Arguments ax_shadow_cost {A P X O}.
Arguments ax_meets_floor {A P} X.
Arguments ax_never_overcharges {A P} X.
Arguments ax_window_collision {A P} X {O}.
Arguments ax_step_price {A P} X.

(** * Pricing needs the movement, not the position *)

(** A counter with two moves, one that raises the record (true) and one
    that leaves it alone (false), seen through its parity. The parity flips
    exactly on the rises. The window does not show the record, no constant
    price is exact (some steps rise and some don't), and yet no collision
    exists: charging one exactly when the parity changed prices every step
    exactly. *)
Definition parity_sys : AxSys nat nat_pre :=
  mk_axsys nat nat_pre nat bool (fun n b => if b then S n else n)
    (fun b => if b then 1 else 0) (fun n => n).

Theorem ax_exact_without_position :
  (forall s, ax_exits (X := parity_sys) s true) /\
  (forall s, ~ ax_exits (X := parity_sys) s false) /\
  (forall s i, Nat.even (ax_step nat nat_pre parity_sys s i) <> Nat.even s
               <-> ax_exits (X := parity_sys) s i) /\
  ~ ax_window_collision parity_sys (O := bool) Nat.even /\
  (exists price, ax_meets_floor parity_sys (ax_shadow_cost (X := parity_sys) Nat.even price) /\
                 ax_never_overcharges parity_sys (ax_shadow_cost (X := parity_sys) Nat.even price)) /\
  (forall c : nat,
     ~ (ax_meets_floor parity_sys (ax_shadow_cost (X := parity_sys) Nat.even (fun _ _ => c)) /\
        ax_never_overcharges parity_sys (ax_shadow_cost (X := parity_sys) Nat.even (fun _ _ => c)))) /\
  ~ exists read : bool -> nat, forall s, s = read (Nat.even s).
Proof.
  assert (Hup : forall s, ax_exits (X := parity_sys) s true).
  { intro s. unfold ax_exits. simpl. rewrite nat_pre_le. lia. }
  assert (Hq : forall s, ~ ax_exits (X := parity_sys) s false).
  { intros s H. apply H. simpl. rewrite nat_pre_le. lia. }
  assert (Hflip : forall s i, Nat.even (ax_step nat nat_pre parity_sys s i) <> Nat.even s
                              <-> ax_exits (X := parity_sys) s i).
  { intros s [|].
    - change (ax_step nat nat_pre parity_sys s true) with (S s).
      split; [intros _; apply Hup |]. intros _. rewrite Nat.even_succ, <- Nat.negb_even.
      destruct (Nat.even s); discriminate.
    - change (ax_step nat nat_pre parity_sys s false) with s.
      split; [intro H; exfalso; apply H; reflexivity | intro H; exfalso; exact (Hq s H)]. }
  refine (conj Hup (conj Hq (conj Hflip (conj _ (conj _ (conj _ _)))))).
  - intros [s1 [i1 [s2 [i2 [Hpre [Hpost [Hf1 Hf2]]]]]]].
    apply Hf2. apply (proj1 (Hflip s2 i2)). intro E. apply (proj2 (Hflip s1 i1) Hf1).
    rewrite Hpre, Hpost. exact E.
  - exists (fun o o' => if Bool.eqb o o' then 0 else 1). split.
    + intros s i H. unfold ax_shadow_cost.
      destruct (Bool.eqb (Nat.even s) (Nat.even (ax_step nat nat_pre parity_sys s i))) eqn:E; [| lia].
      exfalso. apply Bool.eqb_prop in E. apply (proj2 (Hflip s i) H). symmetry. exact E.
    + intros s i H. unfold ax_shadow_cost.
      destruct (Bool.eqb (Nat.even s) (Nat.even (ax_step nat nat_pre parity_sys s i))) eqn:E; [reflexivity |].
      exfalso. apply H. apply (proj1 (Hflip s i)). intro E'. rewrite E' in E.
      rewrite Bool.eqb_reflx in E. discriminate.
  - intros c [Hfl Hno]. specialize (Hfl 0 true (Hup 0)). specialize (Hno 0 false (Hq 0)).
    unfold ax_shadow_cost in Hfl, Hno. lia.
  - intros [read Hread]. assert (H0 := Hread 0). assert (H2 := Hread 2).
    simpl in H0, H2. rewrite <- H0 in H2. discriminate.
Qed.

(** A window that shows one threshold prices exactly the crossings of that
    threshold and no others: it can see the move across a and not the move
    across b. *)
Theorem ax_threshold_window_blind :
  exists (X : AxSys nat nat_pre) (obs : ax_state nat nat_pre X -> bool),
    (forall s, obs s = Nat.leb 1 (ax_rec nat nat_pre X s)) /\
    ax_window_collision X obs.
Proof.
  exists (mk_axsys nat nat_pre nat bool (fun n b => if b then n else S n) (fun _ => 1) (fun n => n)).
  exists (fun n => Nat.leb 1 n). split; [intro s; reflexivity |].
  exists 1, false, 1, true. simpl. split; [reflexivity |]. split; [reflexivity |].
  split.
  - unfold ax_exits. simpl. rewrite nat_pre_le. lia.
  - unfold ax_exits. simpl. rewrite nat_pre_le. lia.
Qed.

(** * Certification as the two-point case *)

Theorem two_point_shadow_cannot_price_exactly :
  forall (S I O : Type) (step : S -> I -> S) (cert : S -> bool) (obs : S -> O),
    shadow_collision step cert obs ->
    forall price, ~ (meets_floor step cert (shadow_cost step obs price) /\
                     never_overcharges step cert (shadow_cost step obs price)).
Proof.
  intros S I O step cert obs Hcol price [Hfloor Hno].
  set (X := mk_axsys bool two_pre S I step (fun _ => 0) cert).
  assert (Hex : forall s i, ax_exits (X := X) s i <-> flips step cert s i = true).
  { intros s i. unfold ax_exits, flips, bp_le. simpl.
    destruct (cert s), (cert (step s i)); simpl; split; intro H; auto; try discriminate;
      try (exfalso; apply H; reflexivity). }
  destruct Hcol as [s1 [i1 [s2 [i2 [Hpre [Hpost [Hf1 Hf2]]]]]]].
  assert (Hcol' : ax_window_collision X (O := O) obs).
  { exists s1, i1, s2, i2. split; [exact Hpre |]. split; [exact Hpost |].
    split; [apply Hex; exact Hf1 |]. intro H. apply Hex in H. congruence. }
  apply (ax_window_no_exact_price bool two_pre X O obs Hcol' price). split.
  - intros s i H. apply Hfloor. apply Hex. exact H.
  - intros s i H. apply Hno. destruct (flips step cert s i) eqn:E; [| reflexivity].
    exfalso. apply H. apply Hex. exact E.
Qed.

Print Assumptions ax_window_collision_overcharges.
Print Assumptions ax_window_no_exact_price.
Print Assumptions ax_step_price_exact.
Print Assumptions ax_window_sees_record_exact.
Print Assumptions ax_window_exact_iff_no_collision.
Print Assumptions ax_overcharge_lower.
Print Assumptions ax_overcharge_tight.
Print Assumptions ax_exact_without_position.
Print Assumptions ax_threshold_window_blind.
Print Assumptions two_point_shadow_cannot_price_exactly.
