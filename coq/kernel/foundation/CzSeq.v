(** CzSeq: sequential composition, "run M, then run N on M's output".

    The sequential composite of M and N is the product of M with the loadable
    form of N ([CzLoad.v]): the two machines side by side, with N's input
    left open until N first moves.  A trace that runs M and then N is the
    schedule

        (moves of M)*  LOAD(a, b)  (moves of N)*

    in which (a, b) are the two counters in the window of M at the moment of
    the LOAD.  Such a trace is called wired ([cmpz_wired]).

    Everything proved for the product holds for the sequential composite at
    once: it is Thiele-complete when both parts are, the record of the
    composite is the pair of the two records, tolls add exactly, and the
    toll on the pair is the toll on each part.  What the wire adds:

      cmpz_seq_tc              the sequential composite is Thiele-complete;
      cmpz_seq_composes        a wired schedule runs M's counter program on
                               (a, b) and then N's counter program on the
                               two counters M left in its window: the window
                               of N after the schedule is N's program run on
                               M's output;
      cmpz_seq_composes_halting  if M's program halts and N's program halts
                               on M's output, the composite's two windows
                               are the two halting configurations;
      cmpz_seq_cost            the cost of a wired schedule is the cost of the
                               M part plus the cost of the N part: the wire
                               costs nothing;
      cmpz_seq_joint_certificate  a certificate of each part, one after the
                               other, costs 6 and no less;
      cmpz_ld_a2_iff           the wire keeps the toll exactly when the
                               loaded states of N all stand at the same
                               record: a hand-off that lands N above the
                               floor is a free certification;
      cmpz_ld_unclean          so a hand-off that can land N above its floor
                               breaks the toll of the composite. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import AxCore.
From Kernel Require Import AxLatch.
From Kernel Require Import AxComplete.
From Kernel Require Import AxComplete2.
From Kernel Require Import CzProd CzProdTC CzLoad.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.

Section Seq.

Context {A B : Type} {P : BPre A} {Q : BPre B} {M : amachine A P} {N : amachine B Q}.
Variable I1 : ax_interface M.
Variable I2 : ax_interface N.

Definition cmpz_seq : amachine (A * B) (cmpz_pair_pre P Q) := cmpz_prod M (cmpz_ld I2).

Definition cmpz_seq_iface : ax_interface cmpz_seq := cmpz_iface I1 (cmpz_ld_iface I2).

Theorem cmpz_seq_tc : ax_tc_with I1 -> ax_tc_with I2 -> ax_tc_with cmpz_seq_iface.
Proof.
  intros H1 H2. exact (cmpz_prod_tc I1 (cmpz_ld_iface I2) H1 (cmpz_ld_tc I2 H2)).
Qed.

(** The two counters in the window of M. *)
Definition cmpz_out (s : am_state M) : nat * nat :=
  snd (T.ub_window (axi_base I1) s).

(** A trace is wired when every LOAD carries the counters of M at that moment. *)
Fixpoint cmpz_wired (tr : list (am_move cmpz_seq)) (s : am_state cmpz_seq) : Prop :=
  match tr with
  | [] => True
  | m :: r => (match m with inr (inl ab) => ab = cmpz_out (fst s) | _ => True end)
              /\ cmpz_wired r (am_step cmpz_seq s m)
  end.

(** The cost of a wired schedule is the cost of its two parts; the wire is free. *)
Theorem cmpz_seq_cost : forall (tr : list (am_move cmpz_seq)),
  cmpz_cost cmpz_seq tr
    = cmpz_cost M (cmpz_lefts tr) + cmpz_cost (cmpz_ld I2) (cmpz_rights tr).
Proof. intro tr. exact (cmpz_cost_prod M (cmpz_ld I2) tr). Qed.

(** A certificate of each part, one after the other, costs 6 and no less. *)
Theorem cmpz_seq_joint_certificate : ax_tc_with I1 -> ax_tc_with I2 ->
  forall p q s0 tr,
  axi_clean cmpz_seq_iface s0 ->
  ~ bp_le P p (axi_floor I1) -> ~ bp_le Q q (axi_floor I2) ->
  bp_le (cmpz_pair_pre P Q) (p, q) (am_rec cmpz_seq (am_run cmpz_seq tr s0)) ->
  ax_record_moves cmpz_seq_iface tr >= 6 /\
  axi_ledger cmpz_seq_iface (am_run cmpz_seq tr s0) >= axi_ledger cmpz_seq_iface s0 + 6.
Proof.
  intros H1 H2 p q s0 tr Hc Hp Hq Hle.
  exact (cmpz_prod_joint_certificate I1 (cmpz_ld_iface I2) H1 (cmpz_ld_tc I2 H2) p q s0 tr Hc Hp Hq Hle).
Qed.

(** ** Running M's program and then N's on M's output *)

Lemma cmpz_wired_moves_inl : forall (tr1 : list (am_move M)) rest s,
  cmpz_wired rest (am_run cmpz_seq (map inl tr1) s) ->
  cmpz_wired (map inl tr1 ++ rest) s.
Proof.
  induction tr1 as [| x tr1 IH]; intros rest s H; [exact H |].
  split; [exact I | apply IH; exact H].
Qed.

Lemma cmpz_wired_moves_n : forall (l : list (am_move N)) (s : am_state cmpz_seq),
  cmpz_wired (map (fun z : (nat * nat) + am_move N => (inr z : am_move cmpz_seq))
                (map (fun y => (inr y : (nat * nat) + am_move N)) l)) s.
Proof.
  induction l as [| y l IH]; intro s; [exact I |].
  split; [exact I | apply IH].
Qed.

Theorem cmpz_seq_composes :
  forall P1 P2 n1 n2 a b,
  exists tr : list (am_move cmpz_seq),
    cmpz_wired tr (ax_load cmpz_seq_iface a b) /\
    T.ub_window (axi_base I1) (fst (am_run cmpz_seq tr (ax_load cmpz_seq_iface a b)))
      = T.cm_run n1 P1 (1, (a, b)) /\
    T.ub_window (axi_base I2)
      (cmpz_vw I2 (snd (am_run cmpz_seq tr (ax_load cmpz_seq_iface a b))))
      = T.cm_run n2 P2 (1, snd (T.cm_run n1 P1 (1, (a, b)))) /\
    T.ub_live (axi_base I1) (fst (am_run cmpz_seq tr (ax_load cmpz_seq_iface a b))) /\
    T.ub_live (axi_base I2)
      (cmpz_vw I2 (snd (am_run cmpz_seq tr (ax_load cmpz_seq_iface a b)))).
Proof.
  intros P1 P2 n1 n2 a b.
  set (u1 := axi_base I1). set (u2 := axi_base I2).
  destruct (cmpz_prog_trace u1 n1 P1 (T.ub_load u1 a b)) as [tr1 H1].
  pose proof (T.base_runs_every_program (am_bare M) u1 n1 P1 (T.ub_load u1 a b)
                (T.ub_load_live u1 a b)) as [W1 L1].
  rewrite (T.ub_load_window u1) in W1.
  set (s1 := am_run M tr1 (T.ub_load u1 a b)).
  assert (Hs1 : s1 = T.prog_run u1 n1 P1 (T.ub_load u1 a b)) by exact H1.
  set (ab := cmpz_out s1).
  assert (Hab : ab = snd (T.cm_run n1 P1 (1, (a, b)))).
  { unfold ab, cmpz_out. rewrite Hs1. exact (f_equal snd W1). }
  destruct (cmpz_prog_trace u2 n2 P2 (T.ub_load u2 (fst ab) (snd ab))) as [tr2 H2].
  pose proof (T.base_runs_every_program (am_bare N) u2 n2 P2 (T.ub_load u2 (fst ab) (snd ab))
                (T.ub_load_live u2 (fst ab) (snd ab))) as [W2 L2].
  rewrite (T.ub_load_window u2) in W2.
  set (tr := map inl tr1 ++ map inr (inl ab :: map inr tr2) : list (am_move cmpz_seq)).
  exists tr.
  assert (Hl : cmpz_lefts tr = tr1).
  { unfold tr. rewrite cmpz_lefts_app. rewrite (cmpz_lefts_map_inl (Y := am_move (cmpz_ld I2))).
    rewrite (cmpz_lefts_map_inr (X := am_move M)). apply app_nil_r. }
  assert (Hr : cmpz_rights tr = inl ab :: map inr tr2).
  { unfold tr. rewrite cmpz_rights_app. rewrite (cmpz_rights_map_inl (Y := am_move (cmpz_ld I2))).
    rewrite (cmpz_rights_map_inr (X := am_move M)). reflexivity. }
  assert (HF : fst (am_run cmpz_seq tr (ax_load cmpz_seq_iface a b)) = s1).
  { change (fst (am_run (cmpz_prod M (cmpz_ld I2)) tr (ax_load cmpz_seq_iface a b)) = s1).
    rewrite cmpz_run_prod_fst, Hl. reflexivity. }
  assert (HV : cmpz_vw I2 (snd (am_run cmpz_seq tr (ax_load cmpz_seq_iface a b)))
               = am_run N tr2 (T.ub_load u2 (fst ab) (snd ab))).
  { change (cmpz_vw I2 (snd (am_run (cmpz_prod M (cmpz_ld I2)) tr (ax_load cmpz_seq_iface a b)))
            = am_run N tr2 (T.ub_load u2 (fst ab) (snd ab))).
    rewrite cmpz_run_prod_snd, Hr.
    rewrite am_run_cons.
    change (cmpz_vw I2 (am_run (cmpz_ld I2) (map inr tr2) ((inl ab : (nat * nat) + am_state N), 0))
            = am_run N tr2 (T.ub_load u2 (fst ab) (snd ab))).
    rewrite (cmpz_ld_view_run I2 (map inr tr2) ((inl ab : (nat * nat) + am_state N), 0)).
    - rewrite (cmpz_rights_map_inr (X := nat * nat)). reflexivity.
    - destruct tr2 as [| y r]; [left; reflexivity | right; exists y, (map inr r); reflexivity]. }
  split; [| split; [| split; [| split]]].
  - (* wired *)
    unfold tr. apply cmpz_wired_moves_inl.
    change (cmpz_wired (inr (inl ab) :: map (fun z : (nat * nat) + am_move N => (inr z : am_move cmpz_seq))
                (map (fun y => (inr y : (nat * nat) + am_move N)) tr2))
              (am_run cmpz_seq (map inl tr1) (ax_load cmpz_seq_iface a b))).
    split.
    + change (ab = cmpz_out (fst (am_run (cmpz_prod M (cmpz_ld I2)) (map inl tr1)
                                  (ax_load cmpz_seq_iface a b)))).
      rewrite cmpz_run_prod_fst, (cmpz_lefts_map_inl (Y := am_move (cmpz_ld I2))). reflexivity.
    + apply cmpz_wired_moves_n.
  - rewrite HF. rewrite Hs1. exact W1.
  - rewrite HV. rewrite H2. refine (eq_trans W2 _).
    rewrite <- (surjective_pairing ab). rewrite Hab. reflexivity.
  - rewrite HF. rewrite Hs1. exact L1.
  - rewrite HV. rewrite H2. exact L2.
Qed.

(** If both programs halt, the composite's two windows are the two halting
    configurations: the sequential composite computes the composite of the
    two counter computations. *)
Corollary cmpz_seq_composes_halting :
  forall P1 P2 n1 n2 a b,
  T.cm_step P1 (T.cm_run n1 P1 (1, (a, b))) = None ->
  T.cm_step P2 (T.cm_run n2 P2 (1, snd (T.cm_run n1 P1 (1, (a, b))))) = None ->
  exists tr : list (am_move cmpz_seq),
    cmpz_wired tr (ax_load cmpz_seq_iface a b) /\
    T.cm_fetch P1 (fst (T.ub_window (axi_base I1)
        (fst (am_run cmpz_seq tr (ax_load cmpz_seq_iface a b))))) = None /\
    T.cm_fetch P2 (fst (T.ub_window (axi_base I2)
        (cmpz_vw I2 (snd (am_run cmpz_seq tr (ax_load cmpz_seq_iface a b)))))) = None.
Proof.
  intros P1 P2 n1 n2 a b Hh1 Hh2.
  destruct (cmpz_seq_composes P1 P2 n1 n2 a b) as [tr [Hw [W1 [W2 _]]]].
  exists tr. split; [exact Hw |]. split.
  - rewrite W1. unfold T.cm_step in Hh1.
    destruct (T.cm_fetch P1 (fst (T.cm_run n1 P1 (1, (a, b))))); [discriminate | reflexivity].
  - rewrite W2. unfold T.cm_step in Hh2.
    destruct (T.cm_fetch P2 (fst (T.cm_run n2 P2 (1, snd (T.cm_run n1 P1 (1, (a, b))))))); [discriminate | reflexivity].
Qed.

End Seq.

(** * The wire keeps the toll exactly when every loaded state stands at one record *)

Section LdToll.

Context {B : Type} {Q : BPre B} {N : amachine B Q}.
Variable I2 : ax_interface N.

Theorem cmpz_ld_a2_if :
  ax_a2 (X := am_axsys N) ->
  (forall a b a' b', bp_le Q (am_rec N (T.ub_load (axi_base I2) a b))
                             (am_rec N (T.ub_load (axi_base I2) a' b'))) ->
  ax_a2 (X := am_axsys (cmpz_ld I2)).
Proof.
  intros HN Hl s [ab | y] Hex.
  - exfalso. apply Hex. cbn. destruct s as [[ab' | t] n]; cbn.
    + apply Hl.
    + apply bp_le_refl.
  - cbn. apply (HN (cmpz_view I2 (fst s)) y). unfold ax_exits in *. cbn in *. exact Hex.
Qed.

Theorem cmpz_ld_a2_only_if :
  ax_a2 (X := am_axsys (cmpz_ld I2)) ->
  forall a b a' b', bp_le Q (am_rec N (T.ub_load (axi_base I2) a b))
                            (am_rec N (T.ub_load (axi_base I2) a' b')).
Proof.
  intros H a b a' b'.
  destruct (bp_leb B Q (am_rec N (T.ub_load (axi_base I2) a b))
                       (am_rec N (T.ub_load (axi_base I2) a' b'))) eqn:E; [exact E |].
  exfalso.
  assert (Hex : ax_exits (X := am_axsys (cmpz_ld I2))
                  ((inl (a', b'), 0) : am_state (cmpz_ld I2)) (inl (a, b))).
  { unfold ax_exits. cbn. intro Hle. unfold bp_le in Hle. rewrite E in Hle. discriminate. }
  pose proof (H _ _ Hex) as Hc. cbn in Hc. lia.
Qed.

(** A hand-off that can land N above its floor is a free certification:
    the loaded form has a move of cost 0 that leaves the down-set. *)
Theorem cmpz_ld_unclean : forall a b a' b',
  ~ bp_le Q (am_rec N (T.ub_load (axi_base I2) a b))
            (am_rec N (T.ub_load (axi_base I2) a' b')) ->
  ~ ax_a2 (X := am_axsys (cmpz_ld I2)).
Proof.
  intros a b a' b' Hn H. apply Hn. apply (cmpz_ld_a2_only_if H).
Qed.

End LdToll.

Print Assumptions cmpz_seq_tc.
Print Assumptions cmpz_seq_cost.
Print Assumptions cmpz_seq_joint_certificate.
Print Assumptions cmpz_seq_composes.
Print Assumptions cmpz_seq_composes_halting.
Print Assumptions cmpz_ld_a2_if.
Print Assumptions cmpz_ld_a2_only_if.
Print Assumptions cmpz_ld_unclean.
