(** Tc2Pow.v: Schroeppel's theorem in the setting of Tc2Chain.v. No tame
    machine with a finite control started on x in counter A and nothing in B
    stops with 2^x in A, for every x ([am_no_power_of_two]).

    The chain of stages of Tc2Chain.v, from an input whose run never comes
    back near the bottom, gives outputs that grow by a fixed amount along an
    arithmetic progression of inputs. Powers of two don't. The only facts
    about the outputs the chain needs are that the runs stop and that
    different inputs give different outputs, so the good-input lemma is
    restated here for any injective output function ([good_exists_f]).
    Through the embedding of Tc2Embed.v the same holds for every program of
    the small machine ([tc2_no_pow]).

    Dependencies: Tc2Am.v, Tc2Forced.v, Tc2Stage.v, Tc2Chain.v, Tc2Embed.v,
    Tc2Mult.v. No axioms and
    no unfinished proofs. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is about abstract two-counter machines with a finite control, the shape
   the two-counter machine of EarnedCore.v takes once its finite part is the
   control (Tc2Embed.v). The machine's link to the abstract record (a
   CertificationSystem with the trace cost floor, and a Thiele-complete
   machine) lives in EarnedCoreLinks.v and ThieleComplete.v. *)

From Coq Require Import List Arith Lia Bool ZArith.
Import ListNotations.
Require Minimal.EarnedCore.
Require Import Minimal.Tc2Am Minimal.Tc2Forced Minimal.Tc2Stage Minimal.Tc2Chain Minimal.Tc2Embed Minimal.Tc2Mult.
Set Default Goal Selector "!".

Section GoodF.
Variable M : tc2_am.
Variable q0 : am_Q M.
Variable f : nat -> nat.
Hypothesis f_inj : forall x x', f x = f x' -> x = x'.
Hypothesis htot : forall x, exists n, am_hlt M (am_run M n (q0, x, 0)) /\ am_a M (am_run M n (q0, x, 0)) = f x.

Lemma ch_outs_start_f : forall x, ch_outs M (q0, x, 0) (f x).
Proof. intro x. destruct (htot x) as (n & H1 & H2). exists n. split; assumption. Qed.

Lemma ch_collision_f : forall x x' n m, am_run M n (q0, x, 0) = am_run M m (q0, x', 0) -> x = x'.
Proof.
  intros x x' n m H.
  pose proof (ch_outs_fwd M n _ _ (ch_outs_start_f x)) as H1.
  pose proof (ch_outs_fwd M m _ _ (ch_outs_start_f x')) as H2.
  rewrite H in H1. apply f_inj. exact (ch_outs_unique M _ _ _ H1 H2).
Qed.

Lemma good_exists_f : forall th x0, exists x, x0 <= x /\ ch_good M th (q0, x, 0).
Proof.
  intros th x0.
  set (Fl := ch_Flist M th).
  assert (Claim : forall n, (exists r, r < n /\ ch_good M th (q0, x0 + r, 0)) \/
    (exists l : list (tc2_cfg M), length l = n /\ NoDup l /\ incl l Fl /\
       forall k, In k l -> exists r t, r < n /\ am_run M t (q0, x0 + r, 0) = k)).
  { intro n. induction n as [| n IH].
    - right. exists []. refine (conj eq_refl (conj (NoDup_nil _) (conj (incl_nil_l _) _))). intros k Hk. contradiction.
    - destruct IH as [(r & Hr & Hg) | (l & Hl1 & Hl2 & Hl3 & Hl4)].
      + left. exists r. split; [lia | exact Hg].
      + destruct (htot (x0 + n)) as (H & Hh & _).
        destruct (tc2_bex_dec (fun t => ch_F M th (am_run M t (q0, x0 + n, 0)))
                    (fun t => ch_F_dec M th _) H) as [Hbad | Hok].
        * right. destruct Hbad as (t & _ & Ht). set (cc := am_run M t (q0, x0 + n, 0)) in *.
          assert (Hnot : ~ In cc l).
          { intro Hin. destruct (Hl4 cc Hin) as (r & t' & Hr & Heq).
            pose proof (ch_collision_f (x0 + r) (x0 + n) t' t Heq) as Hx. lia. }
          exists (cc :: l). repeat split.
          -- simpl. lia.
          -- constructor; assumption.
          -- intros k [<- | Hk]; [apply ch_F_in; exact Ht | apply Hl3; exact Hk].
          -- intros k [<- | Hk]; [exists n, t; split; [lia | reflexivity] |].
             destruct (Hl4 k Hk) as (r & t' & Hr & Heq). exists r, t'. split; [lia | exact Heq].
        * left. exists n. split; [lia |]. intros t Ht.
          destruct (le_lt_dec t H) as [Hle | Hlt]; [exact (Hok t Hle Ht) |].
          rewrite (am_run_after M H t _ ltac:(lia) Hh) in Ht. exact (Hok H (le_n H) Ht). }
  destruct (Claim (S (length Fl))) as [(r & Hr & Hg) | (l & Hl1 & Hl2 & Hl3 & _)].
  - exists (x0 + r). split; [lia | exact Hg].
  - exfalso. pose proof (NoDup_incl_length Hl2 Hl3). lia.
Qed.

End GoodF.

Lemma ch_prod_pos : forall ms, (forall m, In m ms -> 1 <= m) -> 1 <= ch_prod ms.
Proof.
  intros ms H. induction ms as [| m ms IH]; cbn [ch_prod]; [lia |].
  pose proof (H m (or_introl eq_refl)). assert (1 <= ch_prod ms) by (apply IH; intros; apply H; right; auto).
  nia.
Qed.

(** No tame machine computes 2^x from x. *)
Theorem am_no_power_of_two : forall M q0,
  In q0 (am_lq M) ->
  (forall x, exists n, am_hlt M (am_run M n (q0, x, 0)) /\ am_a M (am_run M n (q0, x, 0)) = 2 ^ x) ->
  False.
Proof.
  intros M q0 Hq Htot.
  assert (Hinj : forall x x', 2 ^ x = 2 ^ x' -> x = x') by (intros x x' H; apply (Nat.pow_inj_r 2); [lia | exact H]).
  destruct (sl_both M) as (th & Xl & HB & Hany1 & Hany2).
  destruct (good_exists_f M q0 (fun x => 2 ^ x) Hinj Htot th (Xl + 1)) as (x & Hx & Hgood).
  pose proof (am_B1 M) as HB1.
  destruct (Htot x) as (n & Hhlt & Hy).
  assert (Hout : ch_outs M (q0, x, 0) (2 ^ x)) by (exists n; split; assumption).
  assert (Hbig : Xl < 2 ^ x).
  { assert (x < 2 ^ x) by (apply Nat.pow_gt_lin_r; lia). lia. }
  destruct (chain M th Xl (length (fs_lA M)) HB Hany1 Hany2 n (q0, x, 0) (2 ^ x) Hhlt Hout Hbig
              ltac:(cbn; lia) Hq Hgood) as (ms & ns & mD & Hms & Hns & HmD & Hsh).
  set (D := ch_prod ms * mD). set (E := ch_prod ns * mD).
  assert (HD : 1 <= D) by (unfold D; pose proof (ch_prod_pos ms (fun m Hm => proj1 (Hms m Hm))); nia).
  assert (Hj : forall j, 2 ^ (x + j * D) = 2 ^ x + j * E).
  { intro j. specialize (Hsh j).
    assert (Hshift : am_shA M (j * ch_prod ms * mD) (q0, x, 0) = (q0, x + j * D, 0)).
    { unfold D. cbn. f_equal. f_equal. lia. }
    rewrite Hshift in Hsh.
    pose proof (ch_outs_start_f M q0 (fun x => 2 ^ x) Htot (x + j * D)) as Hout2.
    pose proof (ch_outs_unique M _ _ _ Hsh Hout2) as Heq. unfold E. rewrite <- Heq. lia. }
  pose proof (Hj 1) as H1. pose proof (Hj 2) as H2.
  rewrite Nat.pow_add_r in H1, H2.
  replace (2 * D) with (D + D) in H2 by lia. rewrite Nat.mul_1_l in H1. rewrite Nat.pow_add_r in H2.
  assert (Ha : 1 <= 2 ^ x) by (pose proof (Nat.pow_le_mono_r 2 0 x ltac:(lia) ltac:(lia)); simpl in *; lia).
  assert (Hb : 2 <= 2 ^ D) by (apply (Nat.pow_le_mono_r 2 1 D); lia).
  set (a := 2 ^ x) in *. set (b := 2 ^ D) in *.
  assert (Hsq : a * ((b - 1) * (b - 1)) = 0) by nia.
  assert (0 < a * ((b - 1) * (b - 1))) by (apply Nat.mul_pos_pos; [lia | nia]). lia.
Qed.

Print Assumptions am_no_power_of_two.

(** * The small machine's programs *)


(** No program of the small machine, started on x in counter A and nothing
    in B, stops with 2^x in A for every x. *)
Theorem tc2_no_pow : forall P : list E.instr, ~ (forall x, tc2_pf P x (2 ^ x)).
Proof.
  intros P H.
  apply (am_no_power_of_two (tc2_am_of P) (tc2_q0 P) (tc2_q0_in P)).
  intro x. destruct (proj1 (tc2_pf_iff P x _) (H x)) as (n & Hh & Hy). exists n. split; assumption.
Qed.

Print Assumptions tc2_no_pow.
