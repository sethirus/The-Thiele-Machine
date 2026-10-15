(** NeutralComplete.v: the event-neutral completeness notion
    [neutral_complete] (Thiele-complete over any event, with no checker,
    claim or certification), and what transfers to it from the certified
    notion [thiele_complete].

    Built on minimal/ThieleComplete.v (machine, run, universal_base,
    cm_conf, thiele_complete_with, ...) and minimal/ThieleCompleteWindow.v
    (cm_reach, cm_runl). *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete.
Require Import Minimal.ThieleCompleteWindow.

(* ================================================================= *)
(* 0. The definition.                                                 *)
(* ================================================================= *)

(* A neutral interface: a universal base, a split of the moves into base
   moves and the rest ("marks"), and a ledger. No claims, no checker, no
   clean set, no kinds CHECK/COMMIT/CERTIFY. *)
Record neutral_interface (M : machine) : Type := mk_ni {
  ni_base : universal_base M;
  ni_isbase : m_move M -> bool;
  ni_ledger : m_state M -> nat
}.
Arguments ni_base {M} _.
Arguments ni_isbase {M} _ _.
Arguments ni_ledger {M} _ _.

Section Neutral.
Variable M : machine.
Variable J : neutral_interface M.

Definition nload (a b : nat) : m_state M := ub_load (ni_base J) a b.
Definition nwin (s : m_state M) : cm_conf := ub_window (ni_base J) s.

(* (A) Universal base that cannot touch the record; the record permanent.
   (Clause (a) of Thiele-complete minus "loaded states are clean".) *)
Definition n_base_clause : Prop :=
  (forall i, ni_isbase J (ub_compile (ni_base J) i) = true) /\
  (forall s m, ni_isbase J m = true -> m_record M (m_step M s m) = m_record M s) /\
  (forall s m, m_record M s = true -> m_record M (m_step M s m) = true).

(* (B) Loaded starts have the record down. *)
Definition n_start_clause : Prop := forall a b, m_record M (nload a b) = false.

(* (C) Unit prices: base moves 0, every other move exactly 1, ledger adds. *)
Definition n_price (m : m_move M) : nat := if ni_isbase J m then 0 else 1.
Definition n_price_clause : Prop :=
  (forall m, m_cost M m = n_price m) /\
  (forall s m, ni_ledger J (m_step M s m) = ni_ledger J s + m_cost M m).

(* (D) Distinction: one fixed run raises the record from one loaded start
   and not from another. *)
Definition n_distinction_clause : Prop :=
  exists tr a b a' b',
    m_record M (run M tr (nload a b)) = true /\
    m_record M (run M tr (nload a' b')) = false.

Definition neutral_complete_with : Prop :=
  n_base_clause /\ n_start_clause /\ n_price_clause /\ n_distinction_clause.

End Neutral.

Arguments nload {M} J a b.
Arguments nwin {M} J s.
Arguments n_base_clause {M} J.
Arguments n_start_clause {M} J.
Arguments n_price {M} J m.
Arguments n_price_clause {M} J.
Arguments n_distinction_clause {M} J.
Arguments neutral_complete_with {M} J.

Definition neutral_complete (M : machine) : Prop :=
  exists J : neutral_interface M, neutral_complete_with J.

(* ================================================================= *)
(* 1. Naming an event adds nothing unless the event is fixed first.   *)
(* ================================================================= *)

(* Any permanent record is, step by step, the latch of the event "this
   step raises it". So "the record rises exactly at the first occurrence
   of an event E", with E chosen by the interface, is no constraint. *)
Theorem every_permanent_record_is_a_latch : forall M : machine,
  (forall s m, m_record M s = true -> m_record M (m_step M s m) = true) ->
  exists E : m_state M -> m_move M -> bool,
    forall s m, m_record M (m_step M s m) = m_record M s || E s m.
Proof.
  intros M Hp. exists (fun s m => m_record M (m_step M s m)). intros s m.
  destruct (m_record M s) eqn:Hs; simpl; [apply Hp, Hs | reflexivity].
Qed.

(* The same on runs: every record is the latch of the run-event "the
   record is up at the end". *)
Theorem every_record_latches_itself : forall (M : machine) (start : m_state M -> Prop),
  exists E : m_state M -> list (m_move M) -> Prop,
    forall s0 tr, start s0 -> (m_record M (run M tr s0) = true <-> E s0 tr).
Proof.
  intros M start. exists (fun s0 tr => m_record M (run M tr s0) = true). tauto.
Qed.

(* ================================================================= *)
(* 2. Consequences for every neutral-complete machine.                *)
(* ================================================================= *)

Fixpoint nmarks {M} (J : neutral_interface M) (tr : list (m_move M)) : nat :=
  match tr with [] => 0 | m :: r => n_price J m + nmarks J r end.

Lemma nledger_counts : forall M (J : neutral_interface M), n_price_clause J ->
  forall tr s, ni_ledger J (run M tr s) = ni_ledger J s + nmarks J tr.
Proof.
  intros M J [Hc Hl] tr. induction tr as [| m tr IH]; intro s; simpl; [lia |].
  rewrite IH, Hl, Hc. lia.
Qed.

(* The raising move is never a base move (only base-blindness used). *)
Theorem nc_raise_is_mark : forall M (J : neutral_interface M),
  (forall s m, ni_isbase J m = true -> m_record M (m_step M s m) = m_record M s) ->
  forall s m, m_record M s = false -> m_record M (m_step M s m) = true ->
    ni_isbase J m = false.
Proof.
  intros M J Hb s m H0 H1. destruct (ni_isbase J m) eqn:E; [| reflexivity].
  rewrite (Hb s m E), H0 in H1. discriminate.
Qed.

(* Neutral-complete implies the toll and a universal base. *)
Theorem nc_is_weak : forall M, neutral_complete M -> weakly_thiele_complete M.
Proof.
  intros M [J [[_ [Hb _]] [_ [[Hc _] _]]]]. split; [| exact (inhabits (ni_base J))].
  intros s m H0 H1. rewrite Hc. unfold n_price.
  rewrite (nc_raise_is_mark M J Hb s m H0 H1). lia.
Qed.

Definition nc_cert_system (M : machine) (H : neutral_complete M) : CertificationSystem :=
  as_cert_system M (proj1 (nc_is_weak M H)).

(* The floor of one: from ANY state with the record down (no clean-start
   notion needed), a run that ends with it up contains a mark and raises
   the ledger by at least 1. Uses base-blindness and prices only. *)
Theorem nc_floor_one : forall M (J : neutral_interface M),
  (forall s m, ni_isbase J m = true -> m_record M (m_step M s m) = m_record M s) ->
  n_price_clause J ->
  forall tr s, m_record M s = false -> m_record M (run M tr s) = true ->
    (exists m, In m tr /\ ni_isbase J m = false) /\
    nmarks J tr >= 1 /\ ni_ledger J (run M tr s) >= ni_ledger J s + 1.
Proof.
  intros M J Hb Hp tr. induction tr as [| m tr IH]; intros s H0 H1.
  - simpl in H1. congruence.
  - simpl in H1. destruct (m_record M (m_step M s m)) eqn:Hs.
    + pose proof (nc_raise_is_mark M J Hb s m H0 Hs) as Hm.
      split; [exists m; split; [left; reflexivity | exact Hm] |].
      assert (Hk : nmarks J (m :: tr) >= 1) by (simpl; unfold n_price; rewrite Hm; lia).
      split; [exact Hk |]. rewrite (nledger_counts M J Hp). lia.
    + destruct (IH _ Hs H1) as [[m' [Hin Hm']] [Hk _]].
      split; [exists m'; split; [right; exact Hin | exact Hm'] |].
      assert (Hk' : nmarks J (m :: tr) >= 1) by (simpl; lia).
      split; [exact Hk' |]. rewrite (nledger_counts M J Hp). lia.
Qed.

(* Every move costs 0 or 1, and some move costs 0. *)
Theorem nc_costs : forall M, neutral_complete M ->
  (forall m, m_cost M m <= 1) /\ exists m, m_cost M m = 0.
Proof.
  intros M [J [[Hk _] [_ [[Hc _] _]]]]. split.
  - intro m. rewrite Hc. unfold n_price. destruct (ni_isbase J m); lia.
  - exists (ub_compile (ni_base J) (CINC RA)). rewrite Hc. unfold n_price. rewrite Hk.
    reflexivity.
Qed.

(* Some run from a loaded start raises the record. *)
Theorem nc_some_run_raises : forall M (J : neutral_interface M),
  n_distinction_clause J -> exists a b tr, m_record M (run M tr (nload J a b)) = true.
Proof. intros M J [tr [a [b [_ [_ [H _]]]]]]. exists a, b, tr. exact H. Qed.

(* The base reduct is a universal base (as lift_reduct_universal). *)
Definition nc_reduct (M : machine) (J : neutral_interface M) : machine :=
  mk_machine (m_state M) {m : m_move M | ni_isbase J m = true}
    (fun s m => m_step M s (proj1_sig m)) (fun _ => 0) (fun _ => false).

Theorem nc_reduct_universal : forall M (J : neutral_interface M),
  n_base_clause J -> inhabited (universal_base (nc_reduct M J)).
Proof.
  intros M J [Hk _]. constructor.
  exact (mk_ub (nc_reduct M J) (ub_window (ni_base J)) (ub_live (ni_base J))
    (fun i => exist _ (ub_compile (ni_base J) i) (Hk i))
    (ub_load (ni_base J)) (ub_load_window (ni_base J)) (ub_load_live (ni_base J))
    (fun s i Hl => ub_sim (ni_base J) s i Hl)).
Qed.

(* ================================================================= *)
(* 3. Window blindness, with the minimal hypotheses.                  *)
(* ================================================================= *)

Section WindowCore.
Variable M : machine.
Variable U : universal_base M.
Variable isb : m_move M -> bool.
Hypothesis Hcomp : forall i, isb (ub_compile U i) = true.
Hypothesis Hblind : forall s m, isb m = true -> m_record M (m_step M s m) = m_record M s.

Lemma core_base_run_window : forall is s, ub_live U s ->
  ub_window U (run M (map (ub_compile U) is) s) = cm_runl is (ub_window U s) /\
  ub_live U (run M (map (ub_compile U) is) s).
Proof.
  induction is as [| i is IH]; intros s Hl; simpl; [auto |].
  destruct (ub_sim U s i Hl) as [Hw Hl'].
  destruct (IH _ Hl') as [Hw2 Hl2]. split; [| exact Hl2].
  rewrite Hw2, Hw. reflexivity.
Qed.

Lemma core_base_run_record : forall is s,
  m_record M (run M (map (ub_compile U) is) s) = m_record M s.
Proof.
  induction is as [| i is IH]; intro s; simpl; [reflexivity |].
  rewrite IH. apply Hblind, Hcomp.
Qed.

(* Every window is reachable from every loaded start by base moves. *)
Lemma core_reach : forall a b w, exists is,
  ub_window U (run M (map (ub_compile U) is) (ub_load U a b)) = w.
Proof.
  intros a b [pc [x y]]. destruct (cm_reach (1, (a, b)) pc x y) as [is His].
  exists is. destruct (core_base_run_window is (ub_load U a b) (ub_load_live U a b)) as [Hw _].
  rewrite Hw, ub_load_window. exact His.
Qed.

(* RECORD HIDING needs only: a universal base, compiled moves blind to the
   record, and one loaded start with the record down from which some run
   raises it. No permanence, no prices, no chain, no checker. *)
Theorem core_hides_record : forall a b tr,
  m_record M (ub_load U a b) = false ->
  m_record M (run M tr (ub_load U a b)) = true ->
  exists tr2,
    ub_window U (run M tr2 (ub_load U a b)) = ub_window U (run M tr (ub_load U a b)) /\
    m_record M (run M tr2 (ub_load U a b)) = false.
Proof.
  intros a b tr H0 H1.
  destruct (core_reach a b (ub_window U (run M tr (ub_load U a b)))) as [is Hw].
  exists (map (ub_compile U) is). split; [exact Hw |].
  rewrite core_base_run_record. exact H0.
Qed.

Theorem core_no_record_oracle :
  (exists a b tr, m_record M (ub_load U a b) = false /\
                  m_record M (run M tr (ub_load U a b)) = true) ->
  ~ exists f : cm_conf -> bool, forall a b tr,
      f (ub_window U (run M tr (ub_load U a b))) = m_record M (run M tr (ub_load U a b)).
Proof.
  intros [a [b [tr [H0 H1]]]] [f Hf].
  destruct (core_hides_record a b tr H0 H1) as [tr2 [Hw Hr]].
  pose proof (Hf a b tr) as E1. pose proof (Hf a b tr2) as E2.
  rewrite Hw, E1, H1 in E2. congruence.
Qed.

(* LEDGER HIDING needs: compiled moves free and an additive ledger, and
   some run from a loaded start whose ledger grows. *)
Variable led : m_state M -> nat.
Hypothesis Hfree : forall i s, led (m_step M s (ub_compile U i)) = led s.

Lemma core_base_run_ledger : forall is s,
  led (run M (map (ub_compile U) is) s) = led s.
Proof.
  induction is as [| i is IH]; intro s; simpl; [reflexivity |]. rewrite IH. apply Hfree.
Qed.

Theorem core_hides_ledger : forall a b tr k,
  led (run M tr (ub_load U a b)) >= led (ub_load U a b) + k ->
  exists tr2,
    ub_window U (run M tr2 (ub_load U a b)) = ub_window U (run M tr (ub_load U a b)) /\
    led (run M tr2 (ub_load U a b)) + k <= led (run M tr (ub_load U a b)).
Proof.
  intros a b tr k Hk.
  destruct (core_reach a b (ub_window U (run M tr (ub_load U a b)))) as [is Hw].
  exists (map (ub_compile U) is). split; [exact Hw |].
  rewrite core_base_run_ledger. lia.
Qed.

End WindowCore.

(* The neutral versions: the record hides as before; the ledger gap is 1
   (not 3). *)
Theorem nc_hides_record : forall M (J : neutral_interface M),
  neutral_complete_with J ->
  exists a b tr1 tr2,
    nwin J (run M tr1 (nload J a b)) = nwin J (run M tr2 (nload J a b)) /\
    m_record M (run M tr1 (nload J a b)) = true /\
    m_record M (run M tr2 (nload J a b)) = false.
Proof.
  intros M J [[Hk [Hb _]] [Hs [_ Hd]]].
  destruct (nc_some_run_raises M J Hd) as [a [b [tr H1]]].
  destruct (core_hides_record M (ni_base J) (ni_isbase J) Hk Hb a b tr (Hs a b) H1)
    as [tr2 [Hw Hr]].
  exists a, b, tr, tr2. unfold nwin. auto.
Qed.

Theorem nc_hides_ledger : forall M (J : neutral_interface M),
  neutral_complete_with J ->
  exists a b tr1 tr2,
    nwin J (run M tr1 (nload J a b)) = nwin J (run M tr2 (nload J a b)) /\
    ni_ledger J (run M tr2 (nload J a b)) + 1 <= ni_ledger J (run M tr1 (nload J a b)).
Proof.
  intros M J [[Hk [Hb _]] [Hs [Hp Hd]]].
  destruct (nc_some_run_raises M J Hd) as [a [b [tr H1]]].
  destruct (nc_floor_one M J Hb Hp tr (nload J a b) (Hs a b) H1) as [_ [_ Hl]].
  assert (Hfree : forall i s, ni_ledger J (m_step M s (ub_compile (ni_base J) i)) = ni_ledger J s).
  { intros i s. destruct Hp as [Hc Hl']. rewrite Hl', Hc. unfold n_price. rewrite Hk. lia. }
  destruct (core_hides_ledger M (ni_base J) (ni_ledger J) Hfree a b tr 1 Hl) as [tr2 [Hw Hl2]].
  exists a, b, tr, tr2. unfold nwin. split; [symmetry; exact Hw | exact Hl2].
Qed.

Theorem nc_no_oracles : forall M (J : neutral_interface M),
  neutral_complete_with J ->
  (~ exists f : cm_conf -> bool, forall a b tr,
      f (nwin J (run M tr (nload J a b))) = m_record M (run M tr (nload J a b))) /\
  (~ exists f : cm_conf -> nat, forall a b tr,
      f (nwin J (run M tr (nload J a b))) = ni_ledger J (run M tr (nload J a b))).
Proof.
  intros M J HN. split.
  - intros [f Hf]. destruct (nc_hides_record M J HN) as [a [b [t1 [t2 [Hw [H1 H2]]]]]].
    pose proof (Hf a b t1) as E1. pose proof (Hf a b t2) as E2. rewrite Hw in E1. congruence.
  - intros [f Hf]. destruct (nc_hides_ledger M J HN) as [a [b [t1 [t2 [Hw H]]]]].
    pose proof (Hf a b t1) as E1. pose proof (Hf a b t2) as E2. rewrite Hw in E1. lia.
Qed.

(* Thiele-complete window blindness follows from the cores too, with the
   chain needed only for the gap of 3. *)

(* ================================================================= *)
(* 4. Thiele-complete is neutral-complete plus a certification layer. *)
(* ================================================================= *)

Definition kind_is_base {C} (k : kind C) : bool := match k with KBase => true | _ => false end.

Definition neutralize {M} (I : thiele_interface M) : neutral_interface M :=
  mk_ni M (ti_base I) (fun m => kind_is_base (ti_kind I m)) (ti_ledger I).

Lemma price_is_record_move : forall M (I : thiele_interface M) m,
  n_price (neutralize I) m = record_move I m.
Proof. intros M I m. unfold n_price, record_move. simpl. destruct (ti_kind I m); reflexivity. Qed.

Theorem tc_to_nc : forall M (I : thiele_interface M),
  thiele_complete_with I -> neutral_complete_with (neutralize I).
Proof.
  intros M I [[Hk [Hcl [Hb Hp]]] [[Hc0 _] [[Hc Hl] Hd]]].
  split; [| split; [| split]].
  - split; [intro i; simpl; rewrite Hk; reflexivity |]. split; [| exact Hp].
    intros s m H. simpl in H. apply Hb. destruct (ti_kind I m); simpl in H; congruence.
  - intros a b. apply Hc0, Hcl.
  - split; [intro m; rewrite price_is_record_move; apply Hc | exact Hl].
  - destruct Hd as [c [chk [cmt [crt [_ [_ [_ [Hiff [[a [b Hy]] [a' [b' Hn]]]]]]]]]]].
    exists [chk; cmt; crt], a, b, a', b'. split.
    + apply Hiff, Hy.
    + destruct (m_record M (run M [chk; cmt; crt] (load I a' b'))) eqn:E; [| exact E].
      exfalso. apply Hn, Hiff, E.
Qed.

Corollary thiele_complete_neutral : forall M, thiele_complete M -> neutral_complete M.
Proof. intros M [I HI]. exists (neutralize I). apply tc_to_nc, HI. Qed.

(* Exactly what the certification layer adds: clean loaded states, the
   earned-record clause (chain + soundness + keeping), and non-vacuity
   about a claim. Everything else of Thiele-complete is neutral. *)
Theorem tc_iff_nc_plus_certification : forall M (I : thiele_interface M),
  thiele_complete_with I <->
  neutral_complete_with (neutralize I) /\
  (forall a b, ti_clean I (load I a b)) /\
  earned_record_clause I /\ non_vacuity_clause I.
Proof.
  intros M I. split.
  - intro H. split; [apply tc_to_nc, H |].
    destruct H as [[_ [Hcl _]] [Hb [_ Hd]]]. auto.
  - intros [[[Hk [Hb Hp]] [_ [[Hc Hl] _]]] [Hcl [Hbr Hd]]].
    split; [| split; [exact Hbr | split; [| exact Hd]]].
    + split; [intro i; pose proof (Hk i) as K; simpl in K;
              destruct (ti_kind I (ub_compile (ti_base I) i)); simpl in K; congruence |].
      split; [exact Hcl |]. split; [| exact Hp].
      intros s m Hm. apply Hb. simpl. rewrite Hm. reflexivity.
    + split; [| exact Hl]. intro m. rewrite <- price_is_record_move. apply Hc.
Qed.

(* On a Thiele-complete machine the record, from a clean start, is EXACTLY
   the latch of the run-event "an earned chain has been completed". *)
Theorem tc_record_iff_chain : forall M (I : thiele_interface M),
  thiele_complete_with I ->
  forall s0 tr, ti_clean I s0 ->
    (m_record M (run M tr s0) = true <-> earned_chain I s0 tr).
Proof.
  intros M I [[_ [_ [_ Hp]]] [[_ [Hch _]] _]] s0 tr H0. split; [apply Hch, H0 |].
  intros [pre [c [chk [mid1 [cmt [mid2 [crt [post [Htr [_ [_ [_ [_ [_ [_ Hup]]]]]]]]]]]]]]].
  assert (Hstay : forall l s, m_record M s = true -> m_record M (run M l s) = true)
    by (induction l; intros; simpl; auto).
  rewrite Htr.
  replace (pre ++ chk :: mid1 ++ cmt :: mid2 ++ crt :: post)
    with ((pre ++ chk :: mid1 ++ cmt :: mid2 ++ [crt]) ++ post) by list_eq.
  rewrite run_app. apply Hstay, Hup.
Qed.

(* ================================================================= *)
(* 5. The neutral lift: any universal base, any family of events.     *)
(* ================================================================= *)

Section NLift.
Variable M0 : machine.
Variable K : Type.                      (* names of mark moves *)
Variable E : K -> m_state M0 -> bool.   (* the event each mark registers *)

Inductive nmove : Type := NBase (m : m_move M0) | NMark (k : K).

Definition nstate : Type := (m_state M0 * bool * nat)%type.

Definition nstep (s : nstate) (m : nmove) : nstate :=
  match s with
  | (x, r, l) =>
      match m with
      | NBase b => (m_step M0 x b, r, l)
      | NMark k => (x, r || E k x, S l)
      end
  end.

Definition ncost (m : nmove) : nat := match m with NBase _ => 0 | NMark _ => 1 end.

Definition nlift : machine := mk_machine nstate nmove nstep ncost (fun s => snd (fst s)).

Variable U : universal_base M0.

Definition nlift_base : universal_base nlift.
Proof.
  refine (mk_ub nlift (fun s => ub_window U (fst (fst s))) (fun s => ub_live U (fst (fst s)))
            (fun i => NBase (ub_compile U i)) (fun a b => (ub_load U a b, false, 0)) _ _ _).
  - intros a b. apply ub_load_window.
  - intros a b. apply ub_load_live.
  - intros [[x r] l] i Hl. simpl in *. exact (ub_sim U x i Hl).
Defined.

Definition nlift_interface : neutral_interface nlift :=
  mk_ni nlift nlift_base (fun m => match m with NBase _ => true | NMark _ => false end)
    (fun s => snd s).

Definition nbases (tr : list nmove) : list (m_move M0) :=
  flat_map (fun m => match m with NBase b => [b] | NMark _ => [] end) tr.

Lemma nbases_map : forall w, nbases (map NBase w) = w.
Proof. induction w as [| x w IH]; [reflexivity | simpl; rewrite IH; reflexivity]. Qed.

Lemma nlift_run_base : forall tr x r l,
  fst (fst (run nlift tr (x, r, l))) = run M0 (nbases tr) x.
Proof.
  induction tr as [| m tr IH]; intros x r l; [reflexivity |].
  destruct m as [b | k]; simpl; rewrite IH; reflexivity.
Qed.

(* The record after a run: the start value, or some mark at a state where
   its event holds. *)
Lemma nlift_run_record : forall tr x r l,
  snd (fst (run nlift tr (x, r, l))) = true <->
  r = true \/ exists pre k post, tr = pre ++ NMark k :: post /\
                                 E k (run M0 (nbases pre) x) = true.
Proof.
  induction tr as [| m tr IH]; intros x r l.
  - simpl. split; [tauto |]. intros [H | [pre [k [post [H _]]]]]; [exact H |].
    destruct pre; discriminate H.
  - destruct m as [b | k]; simpl; rewrite IH; split.
    + intros [H | [pre [k [post [Ht He]]]]]; [left; exact H |].
      right. exists (NBase b :: pre), k, post. split; [rewrite Ht; reflexivity | exact He].
    + intros [H | [pre [k [post [Ht He]]]]]; [left; exact H |].
      destruct pre as [| p pre]; [discriminate Ht |].
      injection Ht as Hp Ht. subst p. right. exists pre, k, post. split; [exact Ht | exact He].
    + intros [H | [pre [k' [post [Ht He]]]]].
      * apply orb_true_iff in H as [H | H]; [left; exact H |].
        right. exists [], k, tr. split; [reflexivity | exact H].
      * right. exists (NMark k :: pre), k', post. split; [rewrite Ht; reflexivity | exact He].
    + intros [H | [pre [k' [post [Ht He]]]]]; [left; rewrite H; reflexivity |].
      destruct pre as [| p pre].
      * injection Ht as -> ->. left. simpl in He. rewrite He, orb_true_r. reflexivity.
      * injection Ht as Hp Ht. subst p. right. exists pre, k', post. split; [exact Ht | exact He].
Qed.

Lemma nlift_base_clause : n_base_clause nlift_interface.
Proof.
  split; [intro i; reflexivity |]. split.
  - intros [[x r] l] [b | k] H; simpl in *; [reflexivity | discriminate].
  - intros [[x r] l] [b | k] H; simpl in *; [exact H | rewrite H; reflexivity].
Qed.

Lemma nlift_start_clause : n_start_clause nlift_interface.
Proof. intros a b. reflexivity. Qed.

Lemma nlift_price_clause : n_price_clause nlift_interface.
Proof.
  split; [intros [b | k]; reflexivity |].
  intros [[x r] l] [b | k]; simpl; lia.
Qed.

(* Distinction for the canonical interface holds exactly when some fixed
   list of base moves leads two loaded starts to states that some event
   tells apart. *)
Theorem nlift_distinction_iff :
  n_distinction_clause nlift_interface <->
  exists w k a b a' b', E k (run M0 w (ub_load U a b)) = true /\
                        E k (run M0 w (ub_load U a' b')) = false.
Proof.
  split.
  - intros [tr [a [b [a' [b' [H1 H2]]]]]].
    unfold nload in H1, H2. simpl in H1, H2.
    apply nlift_run_record in H1 as [H1 | [pre [k [post [Ht He]]]]]; [discriminate |].
    exists (nbases pre), k, a, b, a', b'. split; [exact He |].
    destruct (E k (run M0 (nbases pre) (ub_load U a' b'))) eqn:E2; [| reflexivity].
    exfalso. assert (H : snd (fst (run nlift tr (ub_load U a' b', false, 0))) = true).
    { apply nlift_run_record. right. exists pre, k, post. auto. }
    simpl in H2. rewrite H in H2. discriminate.
  - intros [w [k [a [b [a' [b' [H1 H2]]]]]]].
    exists (map NBase w ++ [NMark k]), a, b, a', b'.
    assert (Hnb : nbases (map NBase w) = w) by apply nbases_map.
    unfold nload. simpl. split.
    + apply nlift_run_record. right. exists (map NBase w), k, []. rewrite Hnb. auto.
    + destruct (snd (fst (run nlift (map NBase w ++ [NMark k]) (ub_load U a' b', false, 0))))
        eqn:H; [| reflexivity].
      apply nlift_run_record in H as [H | [pre [k' [post [Ht He]]]]]; [discriminate |].
      exfalso.
      (* the only mark is the last move *)
      assert (Hgen : forall w' pre', map NBase w' ++ [NMark k] = pre' ++ NMark k' :: post ->
                       pre' = map NBase w' /\ k' = k /\ post = []).
      { clear. induction w' as [| x w IH]; intros pre' Ht.
        - destruct pre' as [| p pre']; simpl in Ht.
          + injection Ht as Hk Hpost. subst. auto.
          + injection Ht as Hp Ht. destruct pre'; discriminate Ht.
        - destruct pre' as [| p pre']; simpl in Ht; [discriminate Ht |].
          injection Ht as Hp Ht. subst p. destruct (IH _ Ht) as [-> [Hk Hpost]].
          auto. }
      pose proof (Hgen w pre Ht) as Hpre.
      destruct Hpre as [-> [-> ->]]. rewrite Hnb in He. congruence.
Qed.

Theorem nlift_neutral_complete :
  (exists w k a b a' b', E k (run M0 w (ub_load U a b)) = true /\
                         E k (run M0 w (ub_load U a' b')) = false) ->
  neutral_complete_with nlift_interface.
Proof.
  intro H. split; [exact nlift_base_clause |]. split; [exact nlift_start_clause |].
  split; [exact nlift_price_clause |]. apply nlift_distinction_iff, H.
Qed.

(* The floor of one is attained: one mark from a loaded start where the
   event holds raises the record for exactly 1. *)
Theorem nlift_floor_tight : forall k a b, E k (ub_load U a b) = true ->
  m_record nlift (run nlift [NMark k] (nload nlift_interface a b)) = true /\
  ni_ledger nlift_interface (run nlift [NMark k] (nload nlift_interface a b)) = 1.
Proof. intros k a b H. unfold nload. simpl. rewrite H. auto. Qed.

(* The panel leaves the box alone. *)
Theorem nlift_projection : forall w x r l,
  fst (fst (run nlift (map NBase w) (x, r, l))) = run M0 w x.
Proof.
  intros w x r l. rewrite nlift_run_base, nbases_map. reflexivity.
Qed.

End NLift.

Arguments NBase {M0 K} m.
Arguments NMark {M0 K} k.

(* Every universal base lifts with the window event "A is at least 1":
   no capacity, no claim language, no checker premise. *)
Definition win_event (M0 : machine) (U : universal_base M0) (_ : unit) (x : m_state M0) : bool :=
  Nat.leb 1 (fst (snd (ub_window U x))).

Theorem every_base_lifts_neutrally : forall M0 (U : universal_base M0),
  neutral_complete (nlift M0 unit (win_event M0 U)).
Proof.
  intros M0 U. exists (nlift_interface M0 unit (win_event M0 U) U).
  apply nlift_neutral_complete. exists [], tt, 1, 0, 0, 0. simpl.
  unfold win_event. rewrite !ub_load_window. simpl. auto.
Qed.

(* ================================================================= *)
(* 6. Separations.                                                    *)
(* ================================================================= *)

(* The paid test: the two-counter machine (free) plus marks. Mark true
   registers "A is 0"; mark false raises unconditionally (a TICK). *)
Definition pt_event (k : bool) (x : cm_conf) : bool :=
  if k then Nat.eqb (fst (snd x)) 0 else true.

Definition paid_test : machine := nlift silent bool pt_event.
Definition paid_test_interface : neutral_interface paid_test :=
  nlift_interface silent bool pt_event silent_base.

Theorem paid_test_neutral_complete : neutral_complete_with paid_test_interface.
Proof.
  apply nlift_neutral_complete. exists [], true, 0, 0, 1, 0. simpl. auto.
Qed.

(* It has a move that raises the record from every state, which no
   Thiele-complete machine has; neutral-completeness does not exclude it. *)
Theorem paid_test_has_tick : forall s : m_state paid_test,
  m_record paid_test (m_step paid_test s (NMark false)) = true.
Proof. intros [[x r] l]. simpl. apply orb_true_r. Qed.

Lemma run_silent_cm : forall is x, run silent is x = cm_runl is x.
Proof.
  induction is as [| i is IH]; intro x; [reflexivity |]. simpl. rewrite IH. reflexivity.
Qed.

Fixpoint tc_cost_sum {M} (tr : list (m_move M)) : nat :=
  match tr with [] => 0 | m :: r => m_cost M m + tc_cost_sum r end.

Lemma record_moves_cost : forall M (I : thiele_interface M),
  (forall m, m_cost M m = record_move I m) -> forall tr, record_moves I tr = tc_cost_sum tr.
Proof.
  intros M I Hc tr. induction tr as [| m tr IH]; [reflexivity |]. simpl. rewrite IH, Hc. reflexivity.
Qed.

(* Not Thiele-complete through ANY interface: from any clean start, count
   A down for free, then mark: the record rises for a total cost of 1 < 3. *)
Theorem paid_test_not_thiele_complete : ~ thiele_complete paid_test.
Proof.
  intros [I HI].
  pose proof HI as [[_ [Hcl _]] [[Hc0 _] [[Hc _] _]]].
  pose proof (Hc0 _ (Hcl 0 0)) as Hr0.
  destruct (load I 0 0) as [[x r] l] eqn:Hs0.
  simpl in Hr0.
  set (reps := repeat (CDEC RA 1) (fst (snd x))).
  set (tr := map (@NBase silent bool) reps ++ [@NMark silent bool true]).
  assert (Hup : m_record paid_test (run paid_test tr (load I 0 0)) = true).
  { rewrite Hs0. apply (nlift_run_record silent bool pt_event). right.
    exists (map (@NBase silent bool) reps), true, []. split; [reflexivity |].
    rewrite nbases_map, run_silent_cm. unfold reps.
    destruct x as [p [u v]]. destruct (cm_dec_a_to_zero u p v) as [p' Hz].
    simpl. rewrite Hz. reflexivity. }
  destruct (certificate_costs_three paid_test I HI (load I 0 0) tr (Hcl 0 0) Hup) as [H3 _].
  rewrite (record_moves_cost paid_test I Hc) in H3.
  assert (Hsum : forall n, tc_cost_sum (M := paid_test)
             (map (@NBase silent bool) (repeat (CDEC RA 1) n) ++ [@NMark silent bool true]) = 1).
  { induction n as [| n IH]; [reflexivity |]. simpl. exact IH. }
  unfold tr, reps in H3. rewrite Hsum in H3. lia.
Qed.

Theorem nc_strictly_weaker : exists M, neutral_complete M /\ ~ thiele_complete M.
Proof.
  exists paid_test. split; [exists paid_test_interface; exact paid_test_neutral_complete |].
  exact paid_test_not_thiele_complete.
Qed.

(* The clock and the latch clock are not neutral-complete: neutral-complete
   machines have a free move. Any machine whose every move costs >= 1 is out. *)
Theorem all_paid_not_nc : forall M, (forall m, m_cost M m >= 1) -> ~ neutral_complete M.
Proof.
  intros M H HN. destruct (nc_costs M HN) as [_ [m Hm]]. specialize (H m). lia.
Qed.

Corollary clock_not_nc : forall rd, ~ neutral_complete (clock rd).
Proof. intro rd. apply all_paid_not_nc. intro m. simpl. lia. Qed.

Corollary latch_clock_not_nc : forall lt, ~ neutral_complete (latch_clock lt).
Proof. intro lt. apply all_paid_not_nc. intro m. simpl. lia. Qed.

(* The paid latch (TICK only) is not neutral-complete through any
   interface: after a fixed run the record does not depend on the start. *)
Definition is_tick (m : pl_move) : bool := match m with PL_TICK => true | _ => false end.

Lemma paid_latch_record_run : forall tr x f l,
  snd (fst (run paid_latch tr (x, f, l))) = f || existsb is_tick tr.
Proof.
  induction tr as [| m tr IH]; intros x f l; simpl; [rewrite orb_false_r; reflexivity |].
  destruct m as [i |]; simpl; rewrite IH; [reflexivity | rewrite orb_true_r; reflexivity].
Qed.

Theorem paid_latch_not_nc : ~ neutral_complete paid_latch.
Proof.
  intros [J [_ [Hs [_ [tr [a [b [a' [b' [H1 H2]]]]]]]]]].
  pose proof (Hs a b) as S1. pose proof (Hs a' b') as S2.
  destruct (nload J a b) as [[x f] l] eqn:E1.
  destruct (nload J a' b') as [[x' f'] l'] eqn:E2.
  try rewrite E1 in H1. try rewrite E1 in S1. try rewrite E2 in H2. try rewrite E2 in S2.
  simpl in S1, S2. subst f f'.
  change (snd (fst (run paid_latch tr (x, false, l))) = true) in H1.
  change (snd (fst (run paid_latch tr (x', false, l'))) = false) in H2.
  rewrite paid_latch_record_run in H1, H2. simpl in H1, H2. congruence.
Qed.

Theorem silent_not_nc : ~ neutral_complete silent.
Proof. intros [J [_ [_ [_ [tr [a [b [_ [_ [H _]]]]]]]]]]. simpl in H. discriminate. Qed.

(* The record-merge content, for any latch-shaped record. If the record is
   a separate bit and a move acts on the rest without reading it, then a
   move that raises the record from some state merges that state with its
   copy whose record is already up: two different states, same rest. *)
Theorem latch_raise_merges : forall (X Mv : Type) (g : X -> Mv -> X) (e : X -> Mv -> bool),
  forall x m, e x m = true ->
    let step := fun (s : X * bool) (m : Mv) => (g (fst s) m, snd s || e (fst s) m) in
    (x, false) <> (x, true) /\ step (x, false) m = step (x, true) m.
Proof.
  intros X Mv g e x m H step. split; [intro Hc; discriminate Hc |].
  unfold step. simpl. rewrite H. reflexivity.
Qed.

(* ================================================================= *)
(* Audit.                                                             *)
(* ================================================================= *)
Print Assumptions every_permanent_record_is_a_latch.
Print Assumptions nc_is_weak.
Print Assumptions nc_floor_one.
Print Assumptions nc_costs.
Print Assumptions nc_reduct_universal.
Print Assumptions core_hides_record.
Print Assumptions core_no_record_oracle.
Print Assumptions core_hides_ledger.
Print Assumptions nc_hides_record.
Print Assumptions nc_hides_ledger.
Print Assumptions nc_no_oracles.
Print Assumptions tc_to_nc.
Print Assumptions thiele_complete_neutral.
Print Assumptions tc_iff_nc_plus_certification.
Print Assumptions tc_record_iff_chain.
Print Assumptions nlift_distinction_iff.
Print Assumptions nlift_neutral_complete.
Print Assumptions nlift_floor_tight.
Print Assumptions every_base_lifts_neutrally.
Print Assumptions paid_test_neutral_complete.
Print Assumptions paid_test_has_tick.
Print Assumptions paid_test_not_thiele_complete.
Print Assumptions nc_strictly_weaker.
Print Assumptions clock_not_nc.
Print Assumptions latch_clock_not_nc.
Print Assumptions paid_latch_not_nc.
Print Assumptions silent_not_nc.
Print Assumptions latch_raise_merges.
