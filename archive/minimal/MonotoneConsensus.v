(** MonotoneConsensus: with everything growing, the small machine's object
    drops to the bottom of Herlihy's ranking.

    - A general impossibility theorem in Herlihy's valency style. Take any
      shared object whose updates return nothing, together with reads of its
      whole state. Suppose that at every state, of any two updates, one
      leaves the state as it is, or the two commute, or one overwrites the
      other. Then no protocol brings two processes to wait-free agreement on
      a bit ([mc_no_consensus]).
    - The monotone variant of the small machine: no versions, a failed
      instruction changes nothing, the property language keeps only
      "the counter is at least n" (so a checked property never turns
      false), no decrement, and the fact table, the commitments and the flag
      are sets and latches that only grow. With registers beside it, its
      updates meet the condition ([mc_mono_interfere]), so it cannot bring
      two processes to agreement ([mc_mono_no_consensus]): it sits on the
      bottom rung, with plain memory. *)

From Coq Require Import List Arith Lia Bool FunctionalExtensionality.
Import ListNotations.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.

Section Generic.

Variables (Obj Op : Type).
Variable apply : Op -> Obj -> Obj.

(** Of two updates at a state: one leaves it alone, they commute, or one
    overwrites the other. *)
Hypothesis interfere : forall s a b,
  apply a s = s \/ apply b s = s \/ apply a (apply b s) = apply b (apply a s) \/
  apply a (apply b s) = apply a s \/ apply b (apply a s) = apply b s.

(** A protocol: each process has a local state; from it the next action is
    an update with the next local state, a read whose result picks the next
    local state, or a decision. *)
Variable L : Type.
Inductive mc_action : Type := AUpd (u : Op) (n : L) | ARead (k : Obj -> L) | ADec (b : bool).
Variable act : L -> mc_action.
Variable init_obj : Obj.
Variable init_loc : bool -> bool -> L.   (* process name, input *)

Record mc_cfg : Type := mkc { c_obj : Obj; c_l0 : L; c_l1 : L }.

Definition mc_loc (c : mc_cfg) (i : bool) : L := if i then c_l1 c else c_l0 c.

Definition mc_set (o : Obj) (c : mc_cfg) (i : bool) (l : L) : mc_cfg :=
  if i then mkc o (c_l0 c) l else mkc o l (c_l1 c).

Definition mc_step (c : mc_cfg) (i : bool) : mc_cfg :=
  match act (mc_loc c i) with
  | AUpd u n => mc_set (apply u (c_obj c)) c i n
  | ARead k => mc_set (c_obj c) c i (k (c_obj c))
  | ADec _ => c
  end.

Definition mc_run (c : mc_cfg) (s : list bool) : mc_cfg := fold_left mc_step s c.

Definition mc_decided (c : mc_cfg) (i : bool) : option bool :=
  match act (mc_loc c i) with ADec b => Some b | _ => None end.

Definition mc_init (x0 x1 : bool) : mc_cfg := mkc init_obj (init_loc false x0) (init_loc true x1).

Fixpoint mc_count (i : bool) (s : list bool) : nat :=
  match s with [] => 0 | j :: r => (if Bool.eqb i j then 1 else 0) + mc_count i r end.

(** What a wait-free binary consensus protocol for the two processes owes. *)
Definition mc_wait_free (K : nat) : Prop :=
  forall x0 x1 s i, mc_count i s >= K -> mc_decided (mc_run (mc_init x0 x1) s) i <> None.
Definition mc_agreement : Prop :=
  forall x0 x1 s b0 b1, mc_decided (mc_run (mc_init x0 x1) s) false = Some b0 ->
    mc_decided (mc_run (mc_init x0 x1) s) true = Some b1 -> b0 = b1.
Definition mc_validity : Prop :=
  forall x0 x1 s i b, mc_decided (mc_run (mc_init x0 x1) s) i = Some b -> b = x0 \/ b = x1.

(** ** Steps *)

Lemma mc_run_app : forall c s t, mc_run c (s ++ t) = mc_run (mc_run c s) t.
Proof. intros. unfold mc_run. apply fold_left_app. Qed.

Lemma mc_loc_set_same : forall o c i l, mc_loc (mc_set o c i l) i = l.
Proof. intros o c [] l; reflexivity. Qed.

Lemma mc_loc_set_other : forall o c i l, mc_loc (mc_set o c i l) (negb i) = mc_loc c (negb i).
Proof. intros o c [] l; reflexivity. Qed.

Lemma mc_obj_set : forall o c i l, c_obj (mc_set o c i l) = o.
Proof. intros o c [] l; reflexivity. Qed.

Lemma mc_step_other : forall c i, mc_loc (mc_step c i) (negb i) = mc_loc c (negb i).
Proof.
  intros c i. unfold mc_step. destruct (act (mc_loc c i)); try apply mc_loc_set_other; reflexivity.
Qed.

(** A process's step reads only the object and its own local state. *)
Lemma mc_step_local : forall c c' i, c_obj c = c_obj c' -> mc_loc c i = mc_loc c' i ->
  c_obj (mc_step c i) = c_obj (mc_step c' i) /\ mc_loc (mc_step c i) i = mc_loc (mc_step c' i) i.
Proof.
  intros c c' i Ho Hl. unfold mc_step. rewrite <- Hl, <- Ho.
  destruct (act (mc_loc c i)); rewrite ?mc_obj_set, ?mc_loc_set_same; auto.
Qed.

Lemma mc_solo_local : forall n c c' i, c_obj c = c_obj c' -> mc_loc c i = mc_loc c' i ->
  c_obj (mc_run c (repeat i n)) = c_obj (mc_run c' (repeat i n)) /\
  mc_loc (mc_run c (repeat i n)) i = mc_loc (mc_run c' (repeat i n)) i.
Proof.
  induction n as [| n IH]; intros c c' i Ho Hl; [split; assumption |].
  simpl. destruct (mc_step_local c c' i Ho Hl) as [Ho' Hl']. apply IH; assumption.
Qed.

Lemma mc_decided_step_same : forall c i b, mc_decided c i = Some b -> mc_step c i = c.
Proof.
  intros c i b H. unfold mc_decided in H. unfold mc_step.
  destruct (act (mc_loc c i)); [discriminate | discriminate | reflexivity].
Qed.

Lemma mc_negb_neq : forall i j, i <> j -> j = negb i.
Proof. intros [] [] H; try reflexivity; contradiction. Qed.

Lemma mc_decided_keep_step : forall c i j b, mc_decided c i = Some b -> mc_decided (mc_step c j) i = Some b.
Proof.
  intros c i j b H. destruct (Bool.bool_dec j i) as [-> | Hne].
  - rewrite (mc_decided_step_same c i b H). exact H.
  - unfold mc_decided in *. assert (E : i = negb j) by (apply mc_negb_neq; congruence).
    rewrite E in *. rewrite mc_step_other. exact H.
Qed.

Lemma mc_decided_keep : forall s c i b, mc_decided c i = Some b -> mc_decided (mc_run c s) i = Some b.
Proof.
  induction s as [| j s IH]; intros c i b H; [exact H |].
  simpl. apply IH. apply mc_decided_keep_step. exact H.
Qed.

Lemma mc_count_app : forall i s t, mc_count i (s ++ t) = mc_count i s + mc_count i t.
Proof. induction s as [| j s IH]; intros t; simpl; [reflexivity | rewrite IH; lia]. Qed.

Lemma mc_count_repeat : forall i n, mc_count i (repeat i n) = n.
Proof. intros i n. induction n as [| n IH]; simpl; [reflexivity | rewrite eqb_reflx, IH; reflexivity]. Qed.

Lemma mc_count_one : forall i j, mc_count i [j] = if Bool.eqb i j then 1 else 0.
Proof. intros. simpl. lia. Qed.

(** ** The valency argument *)

Section Valency.

Variable K : nat.
Hypothesis WF : mc_wait_free K.
Hypothesis AG : mc_agreement.
Hypothesis VA : mc_validity.

Let I := mc_init false true.

Definition mc_vals (s : list bool) (b : bool) : Prop :=
  exists t i, mc_decided (mc_run I (s ++ t)) i = Some b.

Definition mc_biv (s : list bool) : Prop := mc_vals s false /\ mc_vals s true.

Lemma mc_solo_decides : forall s i, exists d,
  mc_decided (mc_run I (s ++ repeat i K)) i = Some d.
Proof.
  intros s i. pose proof (WF false true (s ++ repeat i K) i) as H.
  rewrite mc_count_app, mc_count_repeat in H.
  destruct (mc_decided (mc_run I (s ++ repeat i K)) i) as [d |] eqn:Hd; [exists d; reflexivity |].
  exfalso. apply H; [lia | exact Hd].
Qed.

Lemma mc_biv_undecided : forall s i, mc_biv s -> mc_decided (mc_run I s) i = None.
Proof.
  intros s i [H0 H1]. destruct (mc_decided (mc_run I s) i) as [d |] eqn:Hd; [| reflexivity].
  exfalso.
  assert (Hall : forall b, mc_vals s b -> b = d).
  { intros b [t [j Hj]]. rewrite mc_run_app in Hj.
    pose proof (mc_decided_keep t _ i d Hd) as Hi. rewrite <- mc_run_app in Hi, Hj.
    destruct (Bool.bool_dec j i) as [-> | Hne].
    - congruence.
    - destruct i, j; try contradiction.
      + exact (AG false true (s ++ t) b d Hj Hi).
      + symmetry. exact (AG false true (s ++ t) d b Hi Hj). }
  pose proof (Hall false H0). pose proof (Hall true H1). congruence.
Qed.

Lemma mc_undecided_count : forall s i, mc_decided (mc_run I s) i = None -> mc_count i s < K.
Proof.
  intros s i H. destruct (Nat.lt_ge_cases (mc_count i s) K) as [Hl | Hge]; [exact Hl |].
  exfalso. exact (WF false true s i Hge H).
Qed.

Definition mc_crit (s : list bool) : Prop :=
  mc_biv s /\ ~ mc_biv (s ++ [false]) /\ ~ mc_biv (s ++ [true]).

Lemma mc_vals_cases : forall s b, mc_biv s -> mc_vals s b ->
  mc_vals (s ++ [false]) b \/ mc_vals (s ++ [true]) b.
Proof.
  intros s b Hb [t [i Hi]]. destruct t as [| j t].
  - rewrite app_nil_r, (mc_biv_undecided s i Hb) in Hi. discriminate.
  - assert (E : s ++ j :: t = (s ++ [j]) ++ t) by (rewrite <- app_assoc; reflexivity).
    rewrite E in Hi. destruct j; [right | left]; exists t, i; exact Hi.
Qed.

(** Some bivalent schedule has no bivalent one-step extension. The search
    is constructive: it ends because every step by an undecided process
    uses up some of that process's budget. *)
Lemma mc_find_crit : forall m s, (K - mc_count false s) + (K - mc_count true s) <= m ->
  mc_biv s -> ~ ~ exists s', mc_crit s'.
Proof.
  induction m as [| m IH]; intros s Hm Hb Hno.
  - pose proof (mc_undecided_count s false (mc_biv_undecided s false Hb)). lia.
  - assert (Hnot : ~ (~ mc_biv (s ++ [false]) /\ ~ mc_biv (s ++ [true]))).
    { intros [H0 H1]. apply Hno. exists s. split; [exact Hb | split; assumption]. }
    apply Hnot. split.
    + intro H0. apply (IH (s ++ [false])); [| exact H0 | exact Hno].
      pose proof (mc_undecided_count s false (mc_biv_undecided s false Hb)).
      rewrite !mc_count_app. simpl. lia.
    + intro H1. apply (IH (s ++ [true])); [| exact H1 | exact Hno].
      pose proof (mc_undecided_count s true (mc_biv_undecided s true Hb)).
      rewrite !mc_count_app. simpl. lia.
Qed.

Lemma mc_decided_loc : forall c c' i, mc_loc c i = mc_loc c' i -> mc_decided c i = mc_decided c' i.
Proof. intros c c' i H. unfold mc_decided. rewrite H. reflexivity. Qed.

(** Two configurations, one after each first step, that one process cannot
    tell apart: its solo run decides the same bit from both, and one of the
    two extensions is then bivalent. *)
Lemma mc_clash : forall s, mc_crit s -> forall t t' i,
  c_obj (mc_run I (s ++ false :: t)) = c_obj (mc_run I (s ++ true :: t')) ->
  mc_loc (mc_run I (s ++ false :: t)) i = mc_loc (mc_run I (s ++ true :: t')) i -> False.
Proof.
  intros s [Hb [Hn0 Hn1]] t t' i Ho Hl.
  destruct (mc_solo_local K _ _ i Ho Hl) as [_ Hl'].
  destruct (mc_solo_decides (s ++ false :: t) i) as [d Hd].
  assert (Hd' : mc_decided (mc_run I ((s ++ true :: t') ++ repeat i K)) i = Some d).
  { rewrite (mc_run_app I (s ++ true :: t') (repeat i K)).
    rewrite <- (mc_decided_loc _ _ i Hl'). rewrite <- mc_run_app. exact Hd. }
  assert (V0 : mc_vals (s ++ [false]) d).
  { exists (t ++ repeat i K), i. rewrite <- app_assoc in Hd. simpl in Hd.
    rewrite <- !app_assoc. simpl. exact Hd. }
  assert (V1 : mc_vals (s ++ [true]) d).
  { exists (t' ++ repeat i K), i. rewrite <- app_assoc in Hd'. simpl in Hd'.
    rewrite <- !app_assoc. simpl. exact Hd'. }
  assert (Hother : mc_vals s (negb d)) by (destruct Hb as [B0 B1]; destruct d; assumption).
  destruct (mc_vals_cases s (negb d) Hb Hother) as [W | W].
  - apply Hn0. destruct d; split; assumption.
  - apply Hn1. destruct d; split; assumption.
Qed.

Lemma mc_step_upd : forall c i u n, act (mc_loc c i) = AUpd u n ->
  c_obj (mc_step c i) = apply u (c_obj c) /\ mc_loc (mc_step c i) i = n.
Proof.
  intros c i u n H. unfold mc_step. rewrite H. rewrite mc_obj_set, mc_loc_set_same. split; reflexivity.
Qed.

Lemma mc_step_read : forall c i k, act (mc_loc c i) = ARead k -> c_obj (mc_step c i) = c_obj c.
Proof. intros c i k H. unfold mc_step. rewrite H. apply mc_obj_set. Qed.

Lemma mc_run_snoc : forall s j t, mc_run I (s ++ j :: t) = mc_run (mc_step (mc_run I s) j) t.
Proof. intros. rewrite mc_run_app. reflexivity. Qed.

Lemma mc_crit_false : forall s, mc_crit s -> False.
Proof.
  intros s Hc. pose proof Hc as [Hb _].
  set (C := mc_run I s).
  pose proof (mc_biv_undecided s false Hb) as U0. pose proof (mc_biv_undecided s true Hb) as U1.
  fold C in U0, U1.
  (* the configurations used below, written through C *)
  assert (Rf : forall t, mc_run I (s ++ false :: t) = mc_run (mc_step C false) t) by (intro; apply mc_run_snoc).
  assert (Rt : forall t, mc_run I (s ++ true :: t) = mc_run (mc_step C true) t) by (intro; apply mc_run_snoc).
  (* P0 moves without changing the object: P1 cannot tell *)
  assert (Same0 : c_obj (mc_step C false) = c_obj C -> False).
  { intro Ho. apply (mc_clash s Hc [true] [] true); rewrite Rf, Rt; cbn [mc_run fold_left];
      destruct (mc_step_local (mc_step C false) C true Ho (mc_step_other C false)); assumption. }
  assert (Same1 : c_obj (mc_step C true) = c_obj C -> False).
  { intro Ho. apply (mc_clash s Hc [] [false] false); rewrite Rf, Rt; cbn [mc_run fold_left];
      destruct (mc_step_local C (mc_step C true) false (eq_sym Ho) (eq_sym (mc_step_other C true)));
      assumption. }
  unfold mc_decided in U0, U1.
  destruct (act (mc_loc C false)) as [u0 n0 | k0 | b0] eqn:A0; [| | discriminate].
  2: { apply Same0. exact (mc_step_read C false k0 A0). }
  destruct (act (mc_loc C true)) as [u1 n1 | k1 | b1] eqn:A1; [| | discriminate].
  2: { apply Same1. exact (mc_step_read C true k1 A1). }
  destruct (mc_step_upd C false u0 n0 A0) as [O0 L0].
  destruct (mc_step_upd C true u1 n1 A1) as [O1 L1].
  (* after both first steps, in either order *)
  assert (A0' : act (mc_loc (mc_step C true) false) = AUpd u0 n0).
  { change (act (mc_loc (mc_step C true) (negb true)) = AUpd u0 n0). rewrite mc_step_other. exact A0. }
  assert (A1' : act (mc_loc (mc_step C false) true) = AUpd u1 n1).
  { change (act (mc_loc (mc_step C false) (negb false)) = AUpd u1 n1). rewrite mc_step_other. exact A1. }
  destruct (mc_step_upd (mc_step C true) false u0 n0 A0') as [O10 L10].
  destruct (mc_step_upd (mc_step C false) true u1 n1 A1') as [O01 L01].
  assert (K01 : mc_loc (mc_step (mc_step C false) true) false = n0).
  { change (mc_loc (mc_step (mc_step C false) true) (negb true) = n0). rewrite mc_step_other. exact L0. }
  assert (K10 : mc_loc (mc_step (mc_step C true) false) true = n1).
  { change (mc_loc (mc_step (mc_step C true) false) (negb false) = n1). rewrite mc_step_other. exact L1. }
  destruct (interfere (c_obj C) u0 u1) as [I0 | [I1 | [Ic | [Iw0 | Iw1]]]].
  - apply Same0. rewrite O0. exact I0.
  - apply Same1. rewrite O1. exact I1.
  - (* they commute: the two orders end in the same configuration *)
    apply (mc_clash s Hc [true] [false] false); rewrite Rf, Rt; cbn [mc_run fold_left].
    + rewrite O01, O10, O0, O1. symmetry. exact Ic.
    + rewrite K01, L10. reflexivity.
  - (* P0's update overwrites P1's: P0 cannot tell *)
    apply (mc_clash s Hc [] [false] false); rewrite Rf, Rt; cbn [mc_run fold_left].
    + rewrite O0, O10, O1. symmetry. exact Iw0.
    + rewrite L0, L10. reflexivity.
  - (* P1's update overwrites P0's: P1 cannot tell *)
    apply (mc_clash s Hc [true] [] true); rewrite Rf, Rt; cbn [mc_run fold_left].
    + rewrite O01, O0, O1. exact Iw1.
    + rewrite L01, L1. reflexivity.
Qed.

(** The run from inputs (0, 1) is bivalent at the start: each process, run
    alone, cannot tell it from the run where both proposed its own bit. *)
Lemma mc_init_biv : mc_biv [].
Proof.
  split.
  - destruct (mc_solo_local K I (mc_init false false) false eq_refl eq_refl) as [_ Hl].
    pose proof (WF false false (repeat false K) false) as W. rewrite mc_count_repeat in W.
    destruct (mc_decided (mc_run (mc_init false false) (repeat false K)) false) as [d |] eqn:Hd;
      [| exfalso; apply W; [lia | reflexivity]].
    destruct (VA false false (repeat false K) false d Hd) as [-> | ->];
    exists (repeat false K), false; simpl; rewrite (mc_decided_loc _ _ false Hl); exact Hd.
  - destruct (mc_solo_local K I (mc_init true true) true eq_refl eq_refl) as [_ Hl].
    pose proof (WF true true (repeat true K) true) as W. rewrite mc_count_repeat in W.
    destruct (mc_decided (mc_run (mc_init true true) (repeat true K)) true) as [d |] eqn:Hd;
      [| exfalso; apply W; [lia | reflexivity]].
    destruct (VA true true (repeat true K) true d Hd) as [-> | ->];
    exists (repeat true K), true; simpl; rewrite (mc_decided_loc _ _ true Hl); exact Hd.
Qed.

Lemma mc_contradiction : False.
Proof.
  apply (mc_find_crit ((K - mc_count false []) + (K - mc_count true [])) [] (le_n _) mc_init_biv).
  intros (s & Hs). apply (mc_crit_false s). assumption.
Qed.

End Valency.

(** No wait-free protocol for two processes agrees on a bit. *)
Theorem mc_no_consensus : forall K, ~ (mc_wait_free K /\ mc_agreement /\ mc_validity).
Proof. intros K [WF [AG VA]]. exact (mc_contradiction K WF AG VA). Qed.

End Generic.

(** * The monotone variant of the small machine, with registers *)

(** Counters, the facts "counter c is at least n" established so far, the
    commitments made, a latch for "some commitment exists", the certified
    flag, and a bank of registers. *)
Record mc_mono : Type := mkm {
  m_ca : nat; m_cb : nat;
  m_facts : nat -> E.ctr -> bool;
  m_commits : nat -> E.ctr -> bool;
  m_any : bool;
  m_cert : bool;
  m_regs : nat -> nat
}.

Inductive mc_mop : Type :=
| MInc (c : E.ctr)
| MCheck (n : nat) (c : E.ctr)
| MCommit (n : nat) (c : E.ctr)
| MCertify
| MWrite (r v : nat).

Definition mc_val (s : mc_mono) (c : E.ctr) : nat := match c with E.CA => m_ca s | E.CB => m_cb s end.

Definition mc_ctr_eqb (c d : E.ctr) : bool :=
  match c, d with E.CA, E.CA | E.CB, E.CB => true | _, _ => false end.

Definition mc_upd2 (f : nat -> E.ctr -> bool) (n : nat) (c : E.ctr) : nat -> E.ctr -> bool :=
  fun n' c' => if Nat.eqb n' n && mc_ctr_eqb c' c then true else f n' c'.

Definition mc_updr (g : nat -> nat) (r v : nat) : nat -> nat :=
  fun r' => if Nat.eqb r' r then v else g r'.

(** When an instruction succeeds; a failed one changes nothing. The checked
    property is the small machine's own "counter >= n". *)
Definition mc_guard (a : mc_mop) (s : mc_mono) : bool :=
  match a with
  | MInc _ => true
  | MCheck n c => E.eval (E.PGe n) (mc_val s c)
  | MCommit n c => m_facts s n c
  | MCertify => m_any s
  | MWrite _ _ => true
  end.

(** What a successful instruction does. *)
Definition mc_eff (a : mc_mop) (s : mc_mono) : mc_mono :=
  match a with
  | MInc E.CA => mkm (S (m_ca s)) (m_cb s) (m_facts s) (m_commits s) (m_any s) (m_cert s) (m_regs s)
  | MInc E.CB => mkm (m_ca s) (S (m_cb s)) (m_facts s) (m_commits s) (m_any s) (m_cert s) (m_regs s)
  | MCheck n c => mkm (m_ca s) (m_cb s) (mc_upd2 (m_facts s) n c) (m_commits s) (m_any s) (m_cert s) (m_regs s)
  | MCommit n c => mkm (m_ca s) (m_cb s) (m_facts s) (mc_upd2 (m_commits s) n c) true (m_cert s) (m_regs s)
  | MCertify => mkm (m_ca s) (m_cb s) (m_facts s) (m_commits s) (m_any s) true (m_regs s)
  | MWrite r v => mkm (m_ca s) (m_cb s) (m_facts s) (m_commits s) (m_any s) (m_cert s) (mc_updr (m_regs s) r v)
  end.

Definition mc_apply (a : mc_mop) (s : mc_mono) : mc_mono := if mc_guard a s then mc_eff a s else s.

Lemma mc_upd2_comm : forall f n c n' c', mc_upd2 (mc_upd2 f n c) n' c' = mc_upd2 (mc_upd2 f n' c') n c.
Proof.
  intros. apply functional_extensionality. intro m. apply functional_extensionality. intro d.
  unfold mc_upd2. destruct (Nat.eqb m n && mc_ctr_eqb d c), (Nat.eqb m n' && mc_ctr_eqb d c'); reflexivity.
Qed.

Lemma mc_updr_comm : forall g r v r' v', r <> r' -> mc_updr (mc_updr g r v) r' v' = mc_updr (mc_updr g r' v') r v.
Proof.
  intros g r v r' v' H. apply functional_extensionality. intro m. unfold mc_updr.
  destruct (Nat.eqb_spec m r'), (Nat.eqb_spec m r); subst; try contradiction; reflexivity.
Qed.

Lemma mc_updr_over : forall g r v v', mc_updr (mc_updr g r v') r v = mc_updr g r v.
Proof.
  intros. apply functional_extensionality. intro m. unfold mc_updr. destruct (Nat.eqb m r); reflexivity.
Qed.

(** A succeeding instruction keeps succeeding after any other one has
    acted: everything it looks at only grows. *)
Lemma mc_guard_mono : forall a b s, mc_guard a s = true -> mc_guard a (mc_eff b s) = true.
Proof.
  intros a b s H. destruct a as [c | n c | n c | | r v]; [reflexivity | | | | reflexivity].
  - simpl in *. apply Nat.leb_le in H. apply Nat.leb_le.
    destruct b as [[] | | | | ]; destruct c; simpl in *; lia.
  - simpl in *. destruct b as [[] | n' c' | | | ]; simpl; try exact H.
    unfold mc_upd2. rewrite H. destruct (Nat.eqb n n' && mc_ctr_eqb c c'); reflexivity.
  - simpl in *. destruct b as [[] | | | | ]; simpl; try exact H. reflexivity.
Qed.

(** Two effects commute, or one overwrites the other. *)
Lemma mc_eff_rel : forall a b s,
  mc_eff a (mc_eff b s) = mc_eff b (mc_eff a s) \/
  mc_eff a (mc_eff b s) = mc_eff a s \/ mc_eff b (mc_eff a s) = mc_eff b s.
Proof.
  intros a b [ca cb fa co an ce rg].
  destruct a as [[] | n c | n c | | r v]; destruct b as [[] | n' c' | n' c' | | r' v'];
    try (left; reflexivity); try (left; simpl; rewrite mc_upd2_comm; reflexivity).
  destruct (Nat.eq_dec r r') as [<- | Hne].
  - right. left. simpl. rewrite mc_updr_over. reflexivity.
  - left. simpl. rewrite mc_updr_comm by (intro E; apply Hne; symmetry; exact E). reflexivity.
Qed.

Theorem mc_mono_interfere : forall s a b,
  mc_apply a s = s \/ mc_apply b s = s \/ mc_apply a (mc_apply b s) = mc_apply b (mc_apply a s) \/
  mc_apply a (mc_apply b s) = mc_apply a s \/ mc_apply b (mc_apply a s) = mc_apply b s.
Proof.
  intros s a b. unfold mc_apply at 1 3 4 5 6 7 8.
  destruct (mc_guard a s) eqn:Ga; [| left; reflexivity].
  destruct (mc_guard b s) eqn:Gb; [| right; left; unfold mc_apply; rewrite Gb; reflexivity].
  unfold mc_apply. rewrite Ga, Gb, (mc_guard_mono a b s Ga), (mc_guard_mono b a s Gb).
  right. right. exact (mc_eff_rel a b s).
Qed.

(** The monotone variant, with registers beside it, brings no two processes
    to wait-free agreement on a bit, whatever the protocol. *)
Theorem mc_mono_no_consensus : forall (L : Type) (act : L -> mc_action mc_mono mc_mop L)
  (init_obj : mc_mono) (init_loc : bool -> bool -> L) (K : nat),
  ~ (mc_wait_free mc_mono mc_mop mc_apply L act init_obj init_loc K /\
     mc_agreement mc_mono mc_mop mc_apply L act init_obj init_loc /\
     mc_validity mc_mono mc_mop mc_apply L act init_obj init_loc).
Proof.
  intros L act init_obj init_loc K.
  exact (mc_no_consensus mc_mono mc_mop mc_apply mc_mono_interfere L act init_obj init_loc K).
Qed.

Print Assumptions mc_no_consensus.
Print Assumptions mc_mono_interfere.
Print Assumptions mc_mono_no_consensus.
