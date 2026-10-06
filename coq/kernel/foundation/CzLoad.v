(** CzLoad: a machine whose input can be chosen until it first moves.

    Sequential composition needs a second machine whose start state is the
    output of the first.  A machine cannot read another machine's state, so
    the wire is a move: the loadable form of N has a move LOAD(a, b) that
    sets its input to (a, b) while it has not yet taken a step of its own,
    and does nothing afterwards.  A state is either pristine (the loaded
    state of N for some (a, b)) or running (a state of N), and carries a
    count of what N's own moves have cost.

    The loadable form of a Thiele-complete machine is Thiele-complete
    ([cmpz_ld_tc]).  LOAD is a base move that costs nothing and leaves the
    record at the floor, which is exactly where every pristine state stands;
    the chain in front of a certification lies in the stretch after the last
    LOAD that comes before the first move of N, and lifts through the
    projection onto N's own moves.

    The sequential composite of M and N is the product of M with the
    loadable form of N ([CzSeq.v]). *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import AxCore.
From Kernel Require Import AxLatch.
From Kernel Require Import AxComplete.
From Kernel Require Import AxComplete2.
From Kernel Require Import CzProd CzProdTC.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.

Section Ld.

Context {B : Type} {Q : BPre B} {N : amachine B Q}.
Variable I2 : ax_interface N.

Local Notation u := (axi_base I2).

Definition cmpz_view (s : (nat * nat) + am_state N) : am_state N :=
  match s with inl ab => T.ub_load u (fst ab) (snd ab) | inr t => t end.

Definition cmpz_ld : amachine B Q :=
  mk_am B Q (((nat * nat) + am_state N) * nat) ((nat * nat) + am_move N)
    (fun s m => match m with
                | inl ab => (match fst s with inl _ => inl ab | inr t => inr t end, snd s)
                | inr y => (inr (am_step N (cmpz_view (fst s)) y), snd s + am_cost N y)
                end)
    (fun m => match m with inl _ => 0 | inr y => am_cost N y end)
    (fun s => am_rec N (cmpz_view (fst s))).

Definition cmpz_vw (s : am_state cmpz_ld) : am_state N := cmpz_view (fst s).

Definition cmpz_ld_base : T.universal_base (am_bare cmpz_ld) :=
  T.mk_ub (am_bare cmpz_ld)
    (fun s => T.ub_window u (cmpz_vw s))
    (fun s => T.ub_live u (cmpz_vw s))
    (fun i => inr (T.ub_compile u i))
    (fun a b => (inl (a, b), 0))
    (fun a b => T.ub_load_window u a b)
    (fun a b => T.ub_load_live u a b)
    (fun s i H => T.ub_sim u (cmpz_vw s) i H).

Definition cmpz_ld_iface : ax_interface cmpz_ld :=
  mk_axi B Q cmpz_ld cmpz_ld_base
    (axi_claim I2)
    (fun m => match m with inl _ => T.KBase | inr y => axi_kind I2 y end)
    (fun c s => axi_meaning I2 c (cmpz_vw s))
    (fun s c => axi_check I2 (cmpz_vw s) c)
    (fun c s s' => axi_same I2 c (cmpz_vw s) (cmpz_vw s'))
    (fun s => axi_clean I2 (cmpz_vw s))
    (fun s => snd s)
    (axi_floor I2)
    (axi_point I2).

Lemma cmpz_ld_load : forall a b, ax_load cmpz_ld_iface a b = (inl (a, b), 0).
Proof. reflexivity. Qed.

Hypothesis H2 : ax_tc_with I2.

Local Ltac unpack :=
  destruct H2 as [[Hk2 [Hcl2 [Hb2 Hg2]]] [[Hfl2 [Hex2 [Hs2 Hr2]]] [[Hco2 Hle2] Hnv2]]].

(** A pristine state stands at the floor. *)
Lemma cmpz_load_floor : forall a b, am_rec N (T.ub_load u a b) = axi_floor I2.
Proof. intros a b. unpack. apply Hfl2. apply Hcl2. Qed.

(** A running state: a LOAD does nothing, an N move moves N. *)
Lemma cmpz_ld_running : forall tr (t : am_state N) n,
  cmpz_vw (am_run cmpz_ld tr (inr t, n)) = am_run N (cmpz_rights tr) t.
Proof.
  induction tr as [| [ab | y] tr IH]; intros t n; [reflexivity | |].
  - rewrite am_run_cons. cbn. exact (IH t n).
  - rewrite am_run_cons. cbn. exact (IH _ _).
Qed.

(** From a running state the first-component of any state is running again. *)
Lemma cmpz_ld_running_stays : forall tr (t : am_state N) n,
  exists t' n', am_run cmpz_ld tr (inr t, n) = (inr t', n').
Proof.
  induction tr as [| [ab | y] tr IH]; intros t n.
  - exists t, n. reflexivity.
  - rewrite am_run_cons. cbn. apply IH.
  - rewrite am_run_cons. cbn. apply IH.
Qed.

(** A trace that is empty or starts with a move of N acts on the view as N
    does. *)
Lemma cmpz_ld_view_run : forall tr s,
  (tr = [] \/ exists y rest, tr = inr y :: rest) ->
  cmpz_vw (am_run cmpz_ld tr s) = am_run N (cmpz_rights tr) (cmpz_vw s).
Proof.
  intros tr s [-> | [y [rest ->]]]; [reflexivity |].
  exact (cmpz_ld_running rest (am_step N (cmpz_view (fst s)) y) (snd s + am_cost N y)).
Qed.

(** The part of a trace before its first move of N is a run of LOADs. *)
Lemma cmpz_ld_split : forall (tr : list ((nat * nat) + am_move N)),
  exists G rest, tr = G ++ rest /\ cmpz_rights G = [] /\
    (rest = [] \/ exists y rest', rest = inr y :: rest').
Proof.
  induction tr as [| [ab | y] tr IH].
  - exists [], []. auto.
  - destruct IH as [G [rest [E [Hr Hs]]]]. exists (inl ab :: G), rest.
    split; [rewrite E; reflexivity |]. split; [cbn; exact Hr | exact Hs].
  - exists [], (inr y :: tr). split; [reflexivity |]. split; [reflexivity |].
    right. exists y, tr. reflexivity.
Qed.

Lemma cmpz_ld_clean_run : forall tr s,
  axi_clean cmpz_ld_iface s -> cmpz_rights tr = [] ->
  axi_clean cmpz_ld_iface (am_run cmpz_ld tr s).
Proof.
  unpack.
  induction tr as [| [ab | y] tr IH]; intros s Hc Hr; [exact Hc | |].
  - rewrite am_run_cons. apply IH; [| exact Hr].
    destruct s as [[ab' | t] n]; cbn in *; [apply Hcl2 | exact Hc].
  - cbn in Hr. discriminate Hr.
Qed.

(** The record of a pristine state is the floor, so a LOAD never leaves the
    down-set. *)
Lemma cmpz_ld_inl_no_exit : forall (s : am_state cmpz_ld) (ab : nat * nat),
  ~ ax_exit_step (AM := cmpz_ld) s (inl ab).
Proof.
  intros s ab Hex. apply Hex. destruct s as [[ab' | t] n]; cbn.
  - rewrite !cmpz_load_floor. apply bp_le_refl.
  - apply bp_le_refl.
Qed.

(** A prefix of a trace that is empty or starts with a move of N is empty or
    starts with a move of N. *)
Lemma cmpz_ld_prefix : forall (rest P1 P2 : list ((nat * nat) + am_move N)),
  (rest = [] \/ exists y r, rest = inr y :: r) -> rest = P1 ++ P2 ->
  P1 = [] \/ exists y r, P1 = inr y :: r.
Proof.
  intros rest P1 P2 [-> | [y [r ->]]] E.
  - destruct P1; [left; reflexivity | discriminate E].
  - destruct P1 as [| a P1']; [left; reflexivity |].
    simpl in E. injection E as <- _. right. exists y, P1'. reflexivity.
Qed.

Lemma cmpz_ld_earned : forall s0 (tr : list (am_move cmpz_ld)) y,
  axi_clean cmpz_ld_iface s0 ->
  ax_exit_step (am_run cmpz_ld tr s0) (inr y) ->
  axc_earned_exit cmpz_ld_iface s0 tr (inr y).
Proof.
  intros s0 tr y Hcl Hex.
  pose proof H2 as HH2. unpack.
  destruct (cmpz_ld_split tr) as [G [rest [E [HG Hrest]]]].
  assert (Hc1 : axi_clean I2 (cmpz_vw (am_run cmpz_ld G s0)))
    by exact (cmpz_ld_clean_run G s0 Hcl HG).
  set (s1 := am_run cmpz_ld G s0) in *.
  assert (Hrun : forall T0 : list ((nat * nat) + am_move N),
            (T0 = [] \/ exists y0 r, T0 = inr y0 :: r) ->
            cmpz_vw (am_run cmpz_ld (G ++ T0) s0) = am_run N (cmpz_rights T0) (cmpz_vw s1)).
  { intros T0 HT0. rewrite am_run_app. apply cmpz_ld_view_run. exact HT0. }
  assert (HS : cmpz_vw (am_run cmpz_ld tr s0) = am_run N (cmpz_rights rest) (cmpz_vw s1)).
  { rewrite E. apply Hrun. exact Hrest. }
  assert (Hexit : ax_exit_step (am_run N (cmpz_rights rest) (cmpz_vw s1)) y).
  { unfold ax_exit_step in *. intro Hle. apply Hex.
    change (bp_le Q (am_rec N (am_step N (cmpz_vw (am_run cmpz_ld tr s0)) y))
                    (am_rec N (cmpz_vw (am_run cmpz_ld tr s0)))).
    rewrite HS. exact Hle. }
  destruct (Hex2 (cmpz_vw s1) (cmpz_rights rest) y Hc1 Hexit)
    as [pre [c [chk [mid1 [cmt [mid2 [Htr [Kc [Km [Kx [Hck [Hsame Hlub]]]]]]]]]]]].
  destruct (cmpz_rights_split rest pre chk (mid1 ++ cmt :: mid2) Htr) as [T1 [T2 [E1 [L1 L2]]]].
  destruct (cmpz_rights_split T2 mid1 cmt mid2 L2) as [T21 [T22 [E2 [L21 L22]]]].
  assert (Hrest' : rest = T1 ++ inr chk :: T21 ++ inr cmt :: T22) by (rewrite E1, E2; reflexivity).
  exists (G ++ T1), c, (inr chk), T21, (inr cmt), T22.
  split.
  - rewrite E, Hrest'. rewrite <- app_assoc. reflexivity.
  - split; [exact Kc |]. split; [exact Km |]. split; [exact Kx |].
    split.
    + change (axi_check I2 (cmpz_vw (am_run cmpz_ld (G ++ T1) s0)) c = true).
      rewrite (Hrun T1 (cmpz_ld_prefix rest T1 _ Hrest E1)), L1. exact Hck.
    + split.
      * intros t1 t2 Hm.
        change (axi_same I2 c (cmpz_vw (am_run cmpz_ld (G ++ T1) s0))
                  (cmpz_vw (am_run cmpz_ld ((G ++ T1) ++ inr chk :: t1) s0))).
        assert (Hpre1 : rest = (T1 ++ inr chk :: t1) ++ (t2 ++ inr cmt :: T22)).
        { rewrite Hrest', Hm. rewrite <- !app_assoc. reflexivity. }
        rewrite <- app_assoc.
        rewrite (Hrun T1 (cmpz_ld_prefix rest T1 _ Hrest E1)).
        rewrite (Hrun (T1 ++ inr chk :: t1) (cmpz_ld_prefix rest _ _ Hrest Hpre1)).
        rewrite cmpz_rights_app. cbn [cmpz_rights]. rewrite L1.
        apply (Hsame (cmpz_rights t1) (cmpz_rights t2)).
        rewrite <- L21, Hm. exact (cmpz_rights_app t1 t2).
      * change (ax_is_lub Q (am_rec N (cmpz_vw (am_run cmpz_ld tr s0))) (axi_point I2 c)
                  (am_rec N (am_step N (cmpz_vw (am_run cmpz_ld tr s0)) y))).
        rewrite HS. exact Hlub.
Qed.

Theorem cmpz_ld_tc : ax_tc_with cmpz_ld_iface.
Proof.
  pose proof H2 as HH2. unpack.
  split; [| split; [| split]].
  - (* universal base *)
    split; [| split; [| split]].
    + intro i. cbn. apply Hk2.
    + intros a b. cbn. apply Hcl2.
    + intros s [ab | y] Hk; cbn in Hk.
      * destruct s as [[ab' | t] n]; cbn; [rewrite !cmpz_load_floor; reflexivity | reflexivity].
      * cbn. apply Hb2. exact Hk.
    + intros s [ab | y]; cbn.
      * destruct s as [[ab' | t] n]; cbn; [rewrite !cmpz_load_floor; apply bp_le_refl | apply bp_le_refl].
      * apply Hg2.
  - (* earned record *)
    split; [| split; [| split]].
    + intros s Hc. cbn. apply Hfl2. exact Hc.
    + intros s0 tr [ab | y] Hcl Hex.
      * exfalso. exact (cmpz_ld_inl_no_exit _ ab Hex).
      * exact (cmpz_ld_earned s0 tr y Hcl Hex).
    + intros s c Hc. cbn in *. apply Hs2. exact Hc.
    + intros c s s' Hs Hm. cbn in *. exact (Hr2 _ _ _ Hs Hm).
  - (* exact toll *)
    split.
    + intros [ab | y]; cbn; [reflexivity | apply Hco2].
    + intros s [ab | y]; cbn; lia.
  - (* non-vacuity *)
    destruct Hnv2 as [c [chk [cmt [crt [Kc [Km [Kx [Hiff [Hyes Hno]]]]]]]]].
    exists c, (inr chk), (inr cmt), (inr crt).
    split; [cbn; exact Kc |]. split; [cbn; exact Km |]. split; [cbn; exact Kx |].
    split.
    + intros a b.
      assert (Hv : cmpz_vw (am_run cmpz_ld [inr chk; inr cmt; inr crt] (inl (a, b), 0))
                   = am_run N [chk; cmt; crt] (T.ub_load u a b))
        by (apply (cmpz_ld_view_run [inr chk; inr cmt; inr crt] (inl (a, b), 0));
            right; exists chk, [inr cmt; inr crt]; reflexivity).
      change (bp_le Q (axi_point I2 c)
                (am_rec N (cmpz_vw (am_run cmpz_ld [inr chk; inr cmt; inr crt] (inl (a, b), 0))))
              <-> axi_meaning I2 c (T.ub_load u a b)).
      rewrite Hv. exact (Hiff a b).
    + split; [destruct Hyes as [a [b Hm]]; exists a, b; exact Hm |
              destruct Hno as [a [b Hm]]; exists a, b; exact Hm].
Qed.

End Ld.

(** The order of a LOAD and a move of N matters, unlike the order of moves of
    independent machines: a LOAD after N has moved is ignored, so the same two
    moves in the other order give a different state whenever the input
    matters. *)
Lemma cmpz_ld_late_load_ignored : forall {B Q} {N : amachine B Q} (I2 : ax_interface N)
    (s : am_state (cmpz_ld I2)) y ab,
  am_step (cmpz_ld I2) (am_step (cmpz_ld I2) s (inr y)) (inl ab) = am_step (cmpz_ld I2) s (inr y).
Proof. intros B Q N I2 s y ab. reflexivity. Qed.

Theorem cmpz_ld_order_matters : forall {B Q} {N : amachine B Q} (I2 : ax_interface N) a b a' b' y,
  am_step N (T.ub_load (axi_base I2) a b) y <> am_step N (T.ub_load (axi_base I2) a' b') y ->
  am_run (cmpz_ld I2) [inl (a, b); inr y] ((inl (a', b') : (nat * nat) + am_state N), 0)
  <> am_run (cmpz_ld I2) [inr y; inl (a, b)] ((inl (a', b') : (nat * nat) + am_state N), 0).
Proof.
  intros B Q N I2 a b a' b' y Hne H. apply Hne.
  apply (f_equal fst) in H. cbn in H. injection H as H. exact H.
Qed.

Print Assumptions cmpz_ld_tc.
Print Assumptions cmpz_ld_order_matters.
