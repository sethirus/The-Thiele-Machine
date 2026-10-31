(** NeutralMore.v: independence of the neutral clauses, and the
    "what doesn't lift" results in neutral form. *)
From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete.
Require Import Minimal.ThieleCompleteWindow.
Require Import Minimal.LiftPigeon.
Require Import Minimal.NeutralComplete.

(* ================================================================= *)
(* Independence: for each clause a machine meeting the other three    *)
(* through an interface and neutral-complete through NO interface.    *)
(* ================================================================= *)

(* (A) fails: the paid test with one more base move DROP that lowers the
   record. *)
Inductive dmove : Type := DB (m : nmove silent bool) | DROP.
Definition dstep (s : nstate silent) (m : dmove) : nstate silent :=
  match m with DB m' => nstep silent bool pt_event s m' | DROP => match s with (x, _, l) => (x, false, l) end end.
Definition dcost (m : dmove) : nat := match m with DB m' => ncost silent bool m' | DROP => 0 end.
Definition drop_m : machine := mk_machine (nstate silent) dmove dstep dcost (fun s => snd (fst s)).

Definition drop_base : universal_base drop_m.
Proof.
  refine (mk_ub drop_m (fun s => fst (fst s)) (fun _ => True) (fun i => DB (@NBase silent bool i))
            (fun a b => ((1, (a, b)), false, 0)) _ _ _).
  - reflexivity.
  - intros; exact I.
  - intros [[x r] l] i _. simpl. split; [reflexivity | exact I].
Defined.

Definition drop_if : neutral_interface drop_m :=
  mk_ni drop_m drop_base (fun m => match m with DB (NBase _) => true | DB (NMark _) => false | DROP => true end)
    (fun s => snd s).

Theorem drop_meets_BCD : n_start_clause drop_if /\ n_price_clause drop_if /\ n_distinction_clause drop_if.
Proof.
  split; [intros a b; reflexivity |]. split.
  - split; [intros [[b | k] |]; reflexivity |]. intros [[x r] l] [[b | k] |]; simpl; lia.
  - exists [DB (@NMark silent bool true)], 0, 0, 1, 0. simpl. auto.
Qed.

Theorem drop_not_nc : ~ neutral_complete drop_m.
Proof.
  intros [J [[_ [_ Hp]] _]].
  specialize (Hp ((1, (0, 0)), true, 0) DROP eq_refl). simpl in Hp. discriminate.
Qed.

(* (B) fails: no move ever changes the record, but loaded starts disagree
   on it. *)
Definition frozen : machine :=
  mk_machine (cm_conf * bool) cm_instr (fun s i => (cm_exec i (fst s), snd s)) (fun _ => 0) snd.

Definition frozen_base : universal_base frozen.
Proof.
  refine (mk_ub frozen fst (fun _ => True) (fun i => i) (fun a b => ((1, (a, b)), Nat.eqb a 0)) _ _ _).
  - reflexivity.
  - intros; exact I.
  - intros [x r] i _. split; [reflexivity | exact I].
Defined.

Definition frozen_if : neutral_interface frozen := mk_ni frozen frozen_base (fun _ => true) (fun _ => 0).

Theorem frozen_meets_ACD : n_base_clause frozen_if /\ n_price_clause frozen_if /\
  n_distinction_clause frozen_if.
Proof.
  split; [split; [reflexivity | split; [intros [x r] m _; reflexivity | intros [x r] m H; exact H]] |].
  split; [split; [reflexivity | intros; simpl; lia] |].
  exists [], 0, 0, 1, 0. simpl. auto.
Qed.

Theorem frozen_not_nc : ~ neutral_complete frozen.
Proof.
  intros [J [[_ [Hb _]] [Hs [[Hc _] [tr [a [b [_ [_ [H1 _]]]]]]]]]].
  assert (Hall : forall m, ni_isbase J m = true).
  { intro m. specialize (Hc m). unfold n_price in Hc. simpl in Hc.
    destruct (ni_isbase J m); [reflexivity | discriminate]. }
  assert (Hrun : forall l s, m_record frozen (run frozen l s) = m_record frozen s).
  { induction l as [| m l IH]; intro s; [reflexivity |]. cbn [run]. rewrite IH. apply Hb, Hall. }
  rewrite Hrun, Hs in H1. discriminate.
Qed.

(* (C) fails: the paid test with every move priced 1. *)
Definition paid_all : machine :=
  mk_machine (nstate silent) (nmove silent bool) (nstep silent bool pt_event) (fun _ => 1)
    (fun s => snd (fst s)).

Definition paid_all_base : universal_base paid_all.
Proof.
  refine (mk_ub paid_all (fun s => fst (fst s)) (fun _ => True) (fun i => @NBase silent bool i)
            (fun a b => ((1, (a, b)), false, 0)) _ _ _).
  - reflexivity.
  - intros; exact I.
  - intros [[x r] l] i _. simpl. split; [reflexivity | exact I].
Defined.

Definition paid_all_if : neutral_interface paid_all :=
  mk_ni paid_all paid_all_base (fun m => match m with NBase _ => true | NMark _ => false end)
    (fun s => snd s).

Theorem paid_all_meets_ABD : n_base_clause paid_all_if /\ n_start_clause paid_all_if /\
  n_distinction_clause paid_all_if.
Proof.
  split; [split; [reflexivity | split] |].
  - intros [[x r] l] [b | k] H; simpl in *; [reflexivity | discriminate].
  - intros [[x r] l] [b | k] H; simpl in *; [exact H | rewrite H; reflexivity].
  - split; [intros a b; reflexivity |]. exists [@NMark silent bool true], 0, 0, 1, 0. simpl. auto.
Qed.

Theorem paid_all_not_nc : ~ neutral_complete paid_all.
Proof. apply all_paid_not_nc. intro m. simpl. lia. Qed.

(* (D) fails: the silent machine (no move raises), with its own interface. *)
Definition silent_nif : neutral_interface silent := mk_ni silent silent_base (fun _ => true) (fun _ => 0).

Theorem silent_meets_ABC : n_base_clause silent_nif /\ n_start_clause silent_nif /\
  n_price_clause silent_nif.
Proof.
  unfold n_base_clause, n_start_clause, n_price_clause, n_price. simpl.
  split; [split; [intro; reflexivity | split; intros; reflexivity || discriminate] |].
  split; [intros; reflexivity |]. split; [intro; reflexivity | intros; simpl; lia].
Qed.

(* ================================================================= *)
(* What doesn't lift, neutrally.                                      *)
(* ================================================================= *)

(* The unpaid moves of a neutral-complete machine are never finitely
   branching: uses only the base clause's compiled moves and prices. *)
Definition free_finitely_branching (M : machine) : Prop :=
  forall s, exists N (idx : m_move M -> nat),
    (forall m, m_cost M m = 0 -> idx m < N) /\
    (forall m m', m_cost M m = 0 -> m_cost M m' = 0 -> idx m = idx m' ->
       m_step M s m = m_step M s m').

Theorem nc_free_not_finitely_branching : forall M (J : neutral_interface M),
  n_base_clause J -> n_price_clause J -> ~ free_finitely_branching M.
Proof.
  intros M J [Hk _] [Hc _] Hfb.
  set (U := ni_base J). set (s0 := ub_load U 1 0).
  pose proof (ub_load_live U 1 0) as Hl0. pose proof (ub_load_window U 1 0) as Hw0.
  fold s0 in Hl0, Hw0.
  destruct (Hfb s0) as [N [idx [Hidx Hfac]]].
  set (mv := fun j => ub_compile U (CDEC RA j)).
  assert (Hfree : forall j, m_cost M (mv j) = 0).
  { intro j. unfold mv. rewrite Hc. unfold n_price. fold U. rewrite Hk. reflexivity. }
  assert (Hwin : forall j, ub_window U (m_step M s0 (mv j)) = (j, (0, 0))).
  { intro j. destruct (ub_sim U s0 (CDEC RA j) Hl0) as [Hw _]. unfold mv. rewrite Hw, Hw0. reflexivity. }
  destruct (lift_pigeon N (fun j => idx (mv j))) as [i [j [Hij [Hj Hf]]]].
  - intros j _. apply Hidx, Hfree.
  - pose proof (Hfac _ _ (Hfree i) (Hfree j) Hf) as Hs.
    pose proof (Hwin i) as Wi. pose proof (Hwin j) as Wj.
    rewrite Hs in Wi. rewrite Wi in Wj. injection Wj as Hij'. lia.
Qed.

Corollary tc_free_not_finitely_branching : forall M, thiele_complete M -> ~ free_finitely_branching M.
Proof.
  intros M [I HI]. destruct (tc_to_nc M I HI) as [Hb [_ [Hp _]]].
  exact (nc_free_not_finitely_branching M (neutralize I) Hb Hp).
Qed.

Definition finitely_branching (M0 : machine) : Prop :=
  forall s, exists N (idx : m_move M0 -> nat),
    (forall m, idx m < N) /\ forall m m', idx m = idx m' -> m_step M0 s m = m_step M0 s m'.

(* The neutral lift of a finitely branching base is never neutral-complete,
   for any events. *)
Theorem nlift_finitely_branching_not_nc : forall M0 K E,
  finitely_branching M0 -> ~ neutral_complete (nlift M0 K E).
Proof.
  intros M0 K E Hfb [J [Hb [_ [Hp _]]]].
  apply (nc_free_not_finitely_branching _ J Hb Hp).
  intros [[x r] l]. destruct (Hfb x) as [N [idx [Hidx Hfac]]].
  exists N, (fun m => match m with NBase b => idx b | NMark _ => 0 end). split.
  - intros [b | k] Hc; [apply Hidx | discriminate Hc].
  - intros [b | k] [b' | k'] Hc Hc' Hi; try discriminate.
    simpl. rewrite (Hfac b b' Hi). reflexivity.
Qed.

(* And the neutral lift of a stateless base is never neutral-complete. *)
Theorem nlift_stateless_not_nc : forall M0 K E,
  (forall x x' m, m_step M0 x m = m_step M0 x' m) -> ~ neutral_complete (nlift M0 K E).
Proof.
  intros M0 K E Hst [J [[Hk _] [_ [[Hc _] _]]]].
  set (U := ni_base J). set (s0 := ub_load U 0 0).
  pose proof (ub_load_live U 0 0) as Hl0. pose proof (ub_load_window U 0 0) as Hw0.
  fold s0 in Hl0, Hw0.
  assert (Hform : forall i, exists b, ub_compile U i = NBase b).
  { intro i. pose proof (Hc (ub_compile U i)) as C. unfold n_price in C. fold U in C.
    rewrite Hk in C. destruct (ub_compile U i) as [b | k]; [exists b; reflexivity | discriminate C]. }
  destruct (Hform (CINC RA)) as [bA HA]. destruct (Hform (CINC RB)) as [bB HB].
  set (sA := m_step (nlift M0 K E) s0 (ub_compile U (CINC RA))).
  set (sB := m_step (nlift M0 K E) s0 (ub_compile U (CINC RB))).
  destruct (ub_sim U s0 (CINC RA) Hl0) as [W1 L1].
  destruct (ub_sim U s0 (CINC RB) Hl0) as [V1 M1].
  destruct (ub_sim U sA (CINC RA) L1) as [W2 _].
  destruct (ub_sim U sB (CINC RA) M1) as [V2 _].
  assert (Heq : m_step (nlift M0 K E) sA (ub_compile U (CINC RA)) =
                m_step (nlift M0 K E) sB (ub_compile U (CINC RA))).
  { unfold sA, sB. rewrite HA, HB. destruct s0 as [[x r] l]. simpl. f_equal. f_equal. apply Hst. }
  fold sA in W1. fold sB in V1.
  rewrite Heq, V2, V1, Hw0 in W2. rewrite W1, Hw0 in W2. simpl in W2. discriminate W2.
Qed.

Print Assumptions drop_meets_BCD.
Print Assumptions drop_not_nc.
Print Assumptions frozen_meets_ACD.
Print Assumptions frozen_not_nc.
Print Assumptions paid_all_meets_ABD.
Print Assumptions paid_all_not_nc.
Print Assumptions silent_meets_ABC.
Print Assumptions silent_not_nc.
Print Assumptions nc_free_not_finitely_branching.
Print Assumptions tc_free_not_finitely_branching.
Print Assumptions nlift_finitely_branching_not_nc.
Print Assumptions nlift_stateless_not_nc.

(* ================================================================= *)
(* Window: every window printed at no cost (tc-window (1)), and the   *)
(* ledger gap of the neutral class is exactly 1, not 3.               *)
(* ================================================================= *)

Theorem nc_every_window_printed : forall M (J : neutral_interface M),
  n_base_clause J -> n_start_clause J -> n_price_clause J ->
  forall s : m_state M, exists a b m,
    ni_isbase J m = true /\ m_cost M m = 0 /\
    nwin J (m_step M (nload J a b) m) = nwin J s /\
    m_record M (m_step M (nload J a b) m) = false /\
    ni_ledger J (m_step M (nload J a b) m) = ni_ledger J (nload J a b).
Proof.
  intros M J [Hk [Hb _]] Hs [Hc Hl] s.
  destruct (nwin J s) as [pc [x y]] eqn:Hw.
  exists (S x), y, (ub_compile (ni_base J) (CDEC RA pc)).
  assert (Hc0 : m_cost M (ub_compile (ni_base J) (CDEC RA pc)) = 0)
    by (rewrite Hc; unfold n_price; rewrite Hk; reflexivity).
  split; [apply Hk |]. split; [exact Hc0 |]. split.
  - unfold nwin, nload.
    destruct (ub_sim (ni_base J) (ub_load (ni_base J) (S x) y) (CDEC RA pc)
                (ub_load_live (ni_base J) (S x) y)) as [Hsim _].
    rewrite Hsim, ub_load_window. reflexivity.
  - split; [rewrite (Hb _ _ (Hk _)); apply Hs |]. rewrite Hl, Hc0. lia.
Qed.

(* On the paid test, from one loaded start, [MARK (A is 0)] and [] end on
   the same window with ledgers 1 and 0: the TC gap of 3 does not survive. *)
Theorem paid_test_gap_one :
  nwin paid_test_interface (run paid_test [@NMark silent bool true] (nload paid_test_interface 0 0)) =
  nwin paid_test_interface (run paid_test [] (nload paid_test_interface 0 0)) /\
  m_record paid_test (run paid_test [@NMark silent bool true] (nload paid_test_interface 0 0)) = true /\
  m_record paid_test (run paid_test [] (nload paid_test_interface 0 0)) = false /\
  ni_ledger paid_test_interface (run paid_test [@NMark silent bool true] (nload paid_test_interface 0 0)) = 1 /\
  ni_ledger paid_test_interface (run paid_test [] (nload paid_test_interface 0 0)) = 0.
Proof. repeat split. Qed.

Print Assumptions nc_every_window_printed.
Print Assumptions paid_test_gap_one.
