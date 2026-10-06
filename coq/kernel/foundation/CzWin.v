(** CzWin: windows and the shadow theorem under the product.

    A window shows the observation of a state, and a shadow price is a
    function of the observed transition.  The product of two machines is
    seen through the pair of the two windows.

    What survives.

      cmpz_win_blind_left, cmpz_win_blind_right
          a window collision in one part is a collision of the pair of
          windows, so no shadow price of the product is exact (blindness is
          preserved);
      cmpz_window_sees_record
          if each window shows its record, the pair shows the record of the
          product and prices it exactly;
      cmpz_prod_shadow_theorem
          the four parts of the shadow theorem (independence of the record
          and of the ledger from the shadow, conservativity of the compiled
          moves, priced movement) hold for the product of two Thiele-complete
          machines;
      cmpz_pair_independence, cmpz_pair_ledger_independence
          the record, and the ledger, of the product are not functions of
          the PAIR of windows;
      cmpz_pair_every_window_printed
          every pair of shadow states is the shadow of a state of the
          product at the floors of both parts, one free move from a clean
          start in each part.

    What does not survive: exactness.  Two machines whose windows both price
    exactly can have a product whose pair of windows does not.  The exact
    statement is [cmpz_win_collision_iff]: the pair of windows collides
    exactly when one part collides, or when one part has a step that leaves
    the down-set of its record without changing what its window shows and the
    other part has a step that does not leave the down-set and does not
    change what its window shows.  The second kind of step is a stutter, and
    a stutter of one part looks like an invisible certification of the
    other.  [cmpz_exactness_not_preserved] is a pair of machines for which
    the first part's only invisible step is a certification and the second
    part's only step is a stutter. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import AxCore.
From Kernel Require Import AxLatch.
From Kernel Require Import AxComplete.
From Kernel Require Import AxComplete2.
From Kernel Require Import AxWindow.
From Kernel Require Import CzProd CzProdTC.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.

Section Win.

Context {A B : Type} {P : BPre A} {Q : BPre B}.
Variable M : amachine A P.
Variable N : amachine B Q.
Context {O1 O2 : Type}.
Variable obs1 : am_state M -> O1.
Variable obs2 : am_state N -> O2.

Definition cmpz_obs (s : am_state (cmpz_prod M N)) : O1 * O2 :=
  (obs1 (fst s), obs2 (snd s)).

(** A step that leaves the down-set and that the window does not see. *)
Definition cmpz_inv_exit {A' P'} (X : amachine A' P') {O : Type} (obs : am_state X -> O) : Prop :=
  exists s i, ax_exits (X := am_axsys X) s i /\ obs (am_step X s i) = obs s.

(** A step that does not leave the down-set and that the window does not see. *)
Definition cmpz_inv_stay {A' P'} (X : amachine A' P') {O : Type} (obs : am_state X -> O) : Prop :=
  exists s i, ~ ax_exits (X := am_axsys X) s i /\ obs (am_step X s i) = obs s.

Theorem cmpz_win_collision_iff : forall (s0 : am_state M) (t0 : am_state N),
  ax_window_collision (am_axsys (cmpz_prod M N)) cmpz_obs <->
  ax_window_collision (am_axsys M) obs1 \/ ax_window_collision (am_axsys N) obs2 \/
  (cmpz_inv_exit M obs1 /\ cmpz_inv_stay N obs2) \/
  (cmpz_inv_exit N obs2 /\ cmpz_inv_stay M obs1).
Proof.
  intros s0 t0. split.
  - intros [[s1 t1] [i1 [[s2 t2] [i2 [Hpre [Hpost [Hx1 Hx2]]]]]]].
    unfold cmpz_obs in Hpre. cbn in Hpre. injection Hpre as E1 E2.
    destruct i1 as [x1 | y1], i2 as [x2 | y2].
    + left. exists s1, x1, s2, x2.
      cbn in Hpost. injection Hpost as E3 E4.
      split; [exact E1 |]. split; [exact E3 |].
      split; [apply (cmpz_exits_inl_iff M N (s1, t1) x1); exact Hx1 |].
      intro H. apply Hx2. apply (cmpz_exits_inl_iff M N (s2, t2) x2). exact H.
    + right. right. left. cbn in Hpost. injection Hpost as E3 E4.
      split.
      * exists s1, x1. split; [apply (cmpz_exits_inl_iff M N (s1, t1) x1); exact Hx1 |].
        cbn in E3. rewrite E3. symmetry. exact E1.
      * exists t2, y2. split; [intro H; apply Hx2; apply (cmpz_exits_inr_iff M N (s2, t2) y2); exact H |].
        cbn in E4. rewrite <- E4. exact E2.
    + right. right. right. cbn in Hpost. injection Hpost as E3 E4.
      split.
      * exists t1, y1. split; [apply (cmpz_exits_inr_iff M N (s1, t1) y1); exact Hx1 |].
        cbn in E4. rewrite E4. symmetry. exact E2.
      * exists s2, x2. split; [intro H; apply Hx2; apply (cmpz_exits_inl_iff M N (s2, t2) x2); exact H |].
        cbn in E3. rewrite <- E3. exact E1.
    + right. left. cbn in Hpost. injection Hpost as E3 E4.
      exists t1, y1, t2, y2.
      split; [exact E2 |]. split; [exact E4 |].
      split; [apply (cmpz_exits_inr_iff M N (s1, t1) y1); exact Hx1 |].
      intro H. apply Hx2. apply (cmpz_exits_inr_iff M N (s2, t2) y2). exact H.
  - intros [[s1 [x1 [s2 [x2 [Hpre [Hpost [Hx1 Hx2]]]]]]] | [[t1 [y1 [t2 [y2 [Hpre [Hpost [Hx1 Hx2]]]]]]] | [[[s [x [Hex Hinv]]] [t [y [Hnex Hinv2]]]] | [[t [y [Hex Hinv]]] [s [x [Hnex Hinv2]]]]]]].
    + exists (s1, t0), (inl x1), (s2, t0), (inl x2).
      unfold cmpz_obs. cbn. split; [f_equal; exact Hpre |].
      split; [f_equal; exact Hpost |].
      split; [apply (cmpz_exits_inl_iff M N (s1, t0) x1); exact Hx1 |].
      intro H. apply Hx2. apply (cmpz_exits_inl_iff M N (s2, t0) x2). exact H.
    + exists (s0, t1), (inr y1), (s0, t2), (inr y2).
      unfold cmpz_obs. cbn. split; [f_equal; exact Hpre |].
      split; [f_equal; exact Hpost |].
      split; [apply (cmpz_exits_inr_iff M N (s0, t1) y1); exact Hx1 |].
      intro H. apply Hx2. apply (cmpz_exits_inr_iff M N (s0, t2) y2). exact H.
    + exists (s, t), (inl x), (s, t), (inr y).
      unfold cmpz_obs. cbn. split; [reflexivity |].
      split; [rewrite Hinv, Hinv2; reflexivity |].
      split; [apply (cmpz_exits_inl_iff M N (s, t) x); exact Hex |].
      intro H. apply Hnex. apply (cmpz_exits_inr_iff M N (s, t) y). exact H.
    + exists (s, t), (inr y), (s, t), (inl x).
      unfold cmpz_obs. cbn. split; [reflexivity |].
      split; [rewrite Hinv, Hinv2; reflexivity |].
      split; [apply (cmpz_exits_inr_iff M N (s, t) y); exact Hex |].
      intro H. apply Hnex. apply (cmpz_exits_inl_iff M N (s, t) x); exact H.
Qed.

(** Blindness is preserved: a collision in either part is a collision of the
    pair, so no shadow price of the product through the pair of windows is
    exact. *)
Theorem cmpz_win_collision_left : forall (t0 : am_state N),
  ax_window_collision (am_axsys M) obs1 ->
  ax_window_collision (am_axsys (cmpz_prod M N)) cmpz_obs.
Proof.
  intros t0 Hc. pose proof Hc as Hc0. destruct Hc0 as [s1 _].
  apply (proj2 (cmpz_win_collision_iff s1 t0)). left. exact Hc.
Qed.

Theorem cmpz_win_collision_right : forall (s0 : am_state M),
  ax_window_collision (am_axsys N) obs2 ->
  ax_window_collision (am_axsys (cmpz_prod M N)) cmpz_obs.
Proof.
  intros s0 Hc. pose proof Hc as Hc0. destruct Hc0 as [t1 _].
  apply (proj2 (cmpz_win_collision_iff s0 t1)). right. left. exact Hc.
Qed.

Theorem cmpz_win_blind_left : forall (t0 : am_state N),
  ax_window_collision (am_axsys M) obs1 ->
  forall price : O1 * O2 -> O1 * O2 -> nat,
  ~ (ax_meets_floor (am_axsys (cmpz_prod M N)) (ax_shadow_cost (X := am_axsys (cmpz_prod M N)) cmpz_obs price) /\
     ax_never_overcharges (am_axsys (cmpz_prod M N)) (ax_shadow_cost (X := am_axsys (cmpz_prod M N)) cmpz_obs price)).
Proof.
  intros t0 Hc price.
  exact (ax_window_no_exact_price (A * B) (cmpz_pair_pre P Q) (am_axsys (cmpz_prod M N)) _ cmpz_obs
           (cmpz_win_collision_left t0 Hc) price).
Qed.

Theorem cmpz_win_blind_right : forall (s0 : am_state M),
  ax_window_collision (am_axsys N) obs2 ->
  forall price : O1 * O2 -> O1 * O2 -> nat,
  ~ (ax_meets_floor (am_axsys (cmpz_prod M N)) (ax_shadow_cost (X := am_axsys (cmpz_prod M N)) cmpz_obs price) /\
     ax_never_overcharges (am_axsys (cmpz_prod M N)) (ax_shadow_cost (X := am_axsys (cmpz_prod M N)) cmpz_obs price)).
Proof.
  intros s0 Hc price.
  exact (ax_window_no_exact_price (A * B) (cmpz_pair_pre P Q) (am_axsys (cmpz_prod M N)) _ cmpz_obs
           (cmpz_win_collision_right s0 Hc) price).
Qed.

(** If each window shows its record, the pair shows the record of the product
    and prices it exactly. *)
Theorem cmpz_window_sees_record :
  forall (read1 : O1 -> A) (read2 : O2 -> B),
  (forall s, am_rec M s = read1 (obs1 s)) -> (forall t, am_rec N t = read2 (obs2 t)) ->
  (exists price, ax_meets_floor (am_axsys (cmpz_prod M N)) (ax_shadow_cost (X := am_axsys (cmpz_prod M N)) cmpz_obs price) /\
                 ax_never_overcharges (am_axsys (cmpz_prod M N)) (ax_shadow_cost (X := am_axsys (cmpz_prod M N)) cmpz_obs price)) /\
  ~ ax_window_collision (am_axsys (cmpz_prod M N)) cmpz_obs.
Proof.
  intros read1 read2 H1 H2.
  apply (ax_window_sees_record_exact (A * B) (cmpz_pair_pre P Q) (am_axsys (cmpz_prod M N)) _ cmpz_obs
           (fun o => (read1 (fst o), read2 (snd o)))).
  intro s. cbn. unfold cmpz_obs. cbn. rewrite (H1 (fst s)), (H2 (snd s)). reflexivity.
Qed.

End Win.

(** * Exactness is not preserved *)

(** The first part: three states in a line, one move.  Stepping from 0 to 1
    certifies; the window shows only whether the state is at least 2, so the
    certification is invisible. *)
Definition cmpz_ex_M : amachine bool two_pre :=
  mk_am bool two_pre nat unit
    (fun s _ => match s with 0 => 1 | _ => 2 end)
    (fun _ => 1)
    (fun s => Nat.leb 1 s).

Definition cmpz_ex_obs1 (s : am_state cmpz_ex_M) : bool := Nat.leb 2 s.

(** The second part: one state, one move that does nothing.  The window shows
    nothing. *)
Definition cmpz_ex_N : amachine bool two_pre :=
  mk_am bool two_pre unit unit (fun s _ => s) (fun _ => 0) (fun _ => false).

Definition cmpz_ex_obs2 (s : am_state cmpz_ex_N) : unit := tt.

Lemma cmpz_ex_M_exits : forall s : nat,
  ax_exits (X := am_axsys cmpz_ex_M) s tt <-> s = 0.
Proof.
  intro s. unfold ax_exits. cbn. rewrite two_le. destruct s as [| s]; cbn.
  - split; [intros _; reflexivity | intros _ H; discriminate (H eq_refl)].
  - split; [intro H; exfalso; apply H; intro; reflexivity | intro H; discriminate H].
Qed.

Lemma cmpz_ex_M_no_collision : ~ ax_window_collision (am_axsys cmpz_ex_M) cmpz_ex_obs1.
Proof.
  intros [s1 [i1 [s2 [i2 [Hpre [Hpost [Hx1 Hx2]]]]]]].
  destruct i1, i2.
  apply cmpz_ex_M_exits in Hx1. subst s1.
  apply Hx2. apply cmpz_ex_M_exits.
  unfold cmpz_ex_obs1 in *. cbn in *.
  destruct s2 as [| [| s2]]; cbn in *; [reflexivity | | ]; discriminate.
Qed.

Lemma cmpz_ex_N_no_collision : ~ ax_window_collision (am_axsys cmpz_ex_N) cmpz_ex_obs2.
Proof.
  intros [s1 [i1 [s2 [i2 [Hpre [Hpost [Hx1 Hx2]]]]]]].
  apply Hx1. cbn. apply bp_le_refl.
Qed.

Lemma cmpz_ex_M_price :
  exists price, ax_meets_floor (am_axsys cmpz_ex_M) (ax_shadow_cost (X := am_axsys cmpz_ex_M) cmpz_ex_obs1 price) /\
                ax_never_overcharges (am_axsys cmpz_ex_M) (ax_shadow_cost (X := am_axsys cmpz_ex_M) cmpz_ex_obs1 price).
Proof.
  exists (fun o o' => if orb o o' then 0 else 1). split.
  - intros s [] H. apply cmpz_ex_M_exits in H. subst s. cbn. lia.
  - intros s [] H. unfold ax_shadow_cost. unfold cmpz_ex_obs1.
    assert (Hs : s <> 0) by (intro E; apply H; apply cmpz_ex_M_exits; exact E).
    destruct s as [| [| s]]; [exfalso; apply Hs; reflexivity | cbn; reflexivity | cbn; reflexivity].
Qed.

Lemma cmpz_ex_N_price :
  exists price, ax_meets_floor (am_axsys cmpz_ex_N) (ax_shadow_cost (X := am_axsys cmpz_ex_N) cmpz_ex_obs2 price) /\
                ax_never_overcharges (am_axsys cmpz_ex_N) (ax_shadow_cost (X := am_axsys cmpz_ex_N) cmpz_ex_obs2 price).
Proof.
  exists (fun _ _ => 0). split.
  - intros s i H. exfalso. apply H. cbn. apply bp_le_refl.
  - intros s i H. reflexivity.
Qed.

Theorem cmpz_exactness_not_preserved :
  ~ ax_window_collision (am_axsys cmpz_ex_M) cmpz_ex_obs1 /\
  ~ ax_window_collision (am_axsys cmpz_ex_N) cmpz_ex_obs2 /\
  ax_window_collision (am_axsys (cmpz_prod cmpz_ex_M cmpz_ex_N))
    (cmpz_obs cmpz_ex_M cmpz_ex_N cmpz_ex_obs1 cmpz_ex_obs2).
Proof.
  split; [exact cmpz_ex_M_no_collision |]. split; [exact cmpz_ex_N_no_collision |].
  apply (proj2 (cmpz_win_collision_iff cmpz_ex_M cmpz_ex_N cmpz_ex_obs1 cmpz_ex_obs2 0 tt)).
  right. right. left. split.
  - exists 0, tt. split; [| reflexivity].
    apply cmpz_ex_M_exits. reflexivity.
  - exists tt, tt. split; [| reflexivity].
    unfold ax_exits. cbn. intro H. apply H. apply bp_le_refl.
Qed.

(** Each part has an exact shadow price through its own window, and the
    product has none through the pair of windows. *)
Corollary cmpz_exactness_not_preserved_price :
  (exists price, ax_meets_floor (am_axsys cmpz_ex_M) (ax_shadow_cost (X := am_axsys cmpz_ex_M) cmpz_ex_obs1 price) /\
                 ax_never_overcharges (am_axsys cmpz_ex_M) (ax_shadow_cost (X := am_axsys cmpz_ex_M) cmpz_ex_obs1 price)) /\
  (exists price, ax_meets_floor (am_axsys cmpz_ex_N) (ax_shadow_cost (X := am_axsys cmpz_ex_N) cmpz_ex_obs2 price) /\
                 ax_never_overcharges (am_axsys cmpz_ex_N) (ax_shadow_cost (X := am_axsys cmpz_ex_N) cmpz_ex_obs2 price)) /\
  forall price, ~ (ax_meets_floor (am_axsys (cmpz_prod cmpz_ex_M cmpz_ex_N))
                      (ax_shadow_cost (X := am_axsys (cmpz_prod cmpz_ex_M cmpz_ex_N))
                         (cmpz_obs cmpz_ex_M cmpz_ex_N cmpz_ex_obs1 cmpz_ex_obs2) price) /\
                   ax_never_overcharges (am_axsys (cmpz_prod cmpz_ex_M cmpz_ex_N))
                      (ax_shadow_cost (X := am_axsys (cmpz_prod cmpz_ex_M cmpz_ex_N))
                         (cmpz_obs cmpz_ex_M cmpz_ex_N cmpz_ex_obs1 cmpz_ex_obs2) price)).
Proof.
  destruct cmpz_exactness_not_preserved as [_ [_ HP]].
  split; [exact cmpz_ex_M_price | split; [exact cmpz_ex_N_price |]].
  intro price. exact (ax_window_no_exact_price (bool * bool) (cmpz_pair_pre two_pre two_pre)
        (am_axsys (cmpz_prod cmpz_ex_M cmpz_ex_N)) (bool * unit) _ HP price).
Qed.

Print Assumptions cmpz_win_collision_iff.
Print Assumptions cmpz_win_blind_left.
Print Assumptions cmpz_window_sees_record.
Print Assumptions cmpz_exactness_not_preserved.
Print Assumptions cmpz_exactness_not_preserved_price.
