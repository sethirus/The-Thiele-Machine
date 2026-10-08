(** LiftCore: the earned layer over ANY base.

    ThieleComplete.v defines a universal base as a machine with a window onto
    two-counter configurations (universal_base).  EarnedGeneric.v builds one
    earned machine, whose base is the two-counter machine itself.  This file
    builds the earned layer once for every base: the layer reads only the
    base's state type, its move type and its step function.

    The layer adds, on top of a base machine M0:

      versions   a version number of the base state, raised by every base
                 move (so equal versions mean no base move in between);
      facts      a table of claims, each with the version it was checked at,
                 holding at most [cap] entries;
      channel    at most one committed fact;
      latch      the certified flag, raised only by CERTIFY and never lowered;
      trap       the error latch: a CHECK that fails, a COMMIT of a claim not
                 in the table at the current version, or a CERTIFY with an empty
                 channel traps the machine, and a trapped machine only pays;
      toll       base moves cost 0, CHECK, COMMIT and CERTIFY cost 1 each.

    The claims are a language over base states: an exact decidable checker
    for a meaning.  The window language [lift_window_lang] needs nothing but
    the base's own window, so every universal base has one.

    Results (all closed under the global context):

      lift_thiele_complete       for every universal base of every machine M0,
                                 every claim language with a claim true at one
                                 loaded start and false at another, and every
                                 cap of at least 1, the lifted machine is
                                 Thiele-complete in the sense of
                                 ThieleComplete.v.
      lift_window_thiele_complete  the same with the window language: nothing
                                 beyond the universal base is needed.

    The base's own cost and record fields are not used.                      *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.

(** * Claim languages over base states *)

Record lift_lang (S : Type) : Type := lift_mk_ll {
  lift_ll_claim : Type;
  lift_ll_eqb : lift_ll_claim -> lift_ll_claim -> bool;
  lift_ll_eqb_eq : forall c d, lift_ll_eqb c d = true <-> c = d;
  lift_ll_mean : lift_ll_claim -> S -> Prop;
  lift_ll_eval : lift_ll_claim -> S -> bool;
  lift_ll_eval_iff : forall c s, lift_ll_eval c s = true <-> lift_ll_mean c s
}.

Arguments lift_ll_claim {S} l.
Arguments lift_ll_eqb {S} l c d.
Arguments lift_ll_eqb_eq {S} l c d.
Arguments lift_ll_mean {S} l c s.
Arguments lift_ll_eval {S} l c s.
Arguments lift_ll_eval_iff {S} l c s.

(** A claim language has a witness when some claim is true at one loaded
    start and false at another. *)
Definition lift_nonvacuous {M0 : T.machine} (U : T.universal_base M0)
    (l : lift_lang (T.m_state M0)) : Prop :=
  exists c, (exists a b, lift_ll_mean l c (T.ub_load U a b)) /\
            (exists a b, ~ lift_ll_mean l c (T.ub_load U a b)).

Section Lift.

Variable M0 : T.machine.
Variable LG : lift_lang (T.m_state M0).
Variable cap : nat.

Local Notation S0 := (T.m_state M0).
Local Notation C := (lift_ll_claim LG).

(** * The lifted machine *)

Record lift_lfact : Type := lift_mk_lfact { lift_lf_claim : C; lift_lf_ver : nat }.

Definition lift_lfact_eqb (f g : lift_lfact) : bool :=
  lift_ll_eqb LG (lift_lf_claim f) (lift_lf_claim g) && Nat.eqb (lift_lf_ver f) (lift_lf_ver g).

Lemma lift_lfact_eqb_eq : forall f g, lift_lfact_eqb f g = true <-> f = g.
Proof.
  intros [c v] [d w]. unfold lift_lfact_eqb. simpl. rewrite andb_true_iff, Nat.eqb_eq,
    lift_ll_eqb_eq. split.
  - intros [-> ->]. reflexivity.
  - intros H. inversion H. auto.
Qed.

Record lift_lstate : Type := lift_mk_ls {
  lift_ls_base : S0;
  lift_ls_ver : nat;
  lift_ls_facts : list lift_lfact;
  lift_ls_chan : option lift_lfact;
  lift_ls_err : bool;
  lift_ls_mu : nat;
  lift_ls_cert : bool
}.

Inductive lift_lmove : Type :=
| lift_LBase (m : T.m_move M0)
| lift_LCheck (c : C)
| lift_LCommit (c : C)
| lift_LCertify.

Definition lift_cost (m : lift_lmove) : nat :=
  match m with lift_LBase _ => 0 | _ => 1 end.

Definition lift_check_ok (s : lift_lstate) (c : C) : bool :=
  negb (lift_ls_err s) && lift_ll_eval LG c (lift_ls_base s) && Nat.ltb (length (lift_ls_facts s)) cap.

Definition lift_commit_ok (s : lift_lstate) (c : C) : bool :=
  negb (lift_ls_err s) && existsb (lift_lfact_eqb (lift_mk_lfact c (lift_ls_ver s))) (lift_ls_facts s).

Definition lift_certify_ok (s : lift_lstate) : bool :=
  negb (lift_ls_err s) && match lift_ls_chan s with Some _ => true | None => false end.

Definition lift_step (s : lift_lstate) (m : lift_lmove) : lift_lstate :=
  let mu' := lift_ls_mu s + lift_cost m in
  if lift_ls_err s then
    lift_mk_ls (lift_ls_base s) (lift_ls_ver s) (lift_ls_facts s) (lift_ls_chan s) true mu' (lift_ls_cert s)
  else
    match m with
    | lift_LBase b =>
        lift_mk_ls (T.m_step M0 (lift_ls_base s) b) (S (lift_ls_ver s)) (lift_ls_facts s) (lift_ls_chan s)
              false mu' (lift_ls_cert s)
    | lift_LCheck c =>
        if lift_check_ok s c then
          lift_mk_ls (lift_ls_base s) (lift_ls_ver s) (lift_mk_lfact c (lift_ls_ver s) :: lift_ls_facts s)
                (lift_ls_chan s) false mu' (lift_ls_cert s)
        else
          lift_mk_ls (lift_ls_base s) (lift_ls_ver s) (lift_ls_facts s) (lift_ls_chan s) true mu' (lift_ls_cert s)
    | lift_LCommit c =>
        if lift_commit_ok s c then
          lift_mk_ls (lift_ls_base s) (lift_ls_ver s) (lift_ls_facts s)
                (Some (lift_mk_lfact c (lift_ls_ver s))) false mu' (lift_ls_cert s)
        else
          lift_mk_ls (lift_ls_base s) (lift_ls_ver s) (lift_ls_facts s) (lift_ls_chan s) true mu' (lift_ls_cert s)
    | lift_LCertify =>
        if lift_certify_ok s then
          lift_mk_ls (lift_ls_base s) (lift_ls_ver s) (lift_ls_facts s) (lift_ls_chan s) false mu' true
        else
          lift_mk_ls (lift_ls_base s) (lift_ls_ver s) (lift_ls_facts s) (lift_ls_chan s) true mu' (lift_ls_cert s)
    end.

(** The lifted machine: its record is the certified flag. *)
Definition lift_machine : T.machine :=
  T.mk_machine lift_lstate lift_lmove lift_step lift_cost lift_ls_cert.

Definition lift_lrun (tr : list lift_lmove) (s : lift_lstate) : lift_lstate := T.run lift_machine tr s.

Lemma lift_lrun_nil : forall s, lift_lrun [] s = s.
Proof. reflexivity. Qed.

Lemma lift_lrun_cons : forall m tr s, lift_lrun (m :: tr) s = lift_lrun tr (lift_step s m).
Proof. reflexivity. Qed.

Lemma lift_lrun_app : forall l1 l2 s, lift_lrun (l1 ++ l2) s = lift_lrun l2 (lift_lrun l1 s).
Proof. intros. exact (T.run_app lift_machine l1 l2 s). Qed.

Lemma lift_lrun_snoc : forall tr m s, lift_lrun (tr ++ [m]) s = lift_step (lift_lrun tr s) m.
Proof. intros. rewrite lift_lrun_app. reflexivity. Qed.

(** * Facts about one step *)

Lemma lift_mu_step : forall s m, lift_ls_mu (lift_step s m) = lift_ls_mu s + lift_cost m.
Proof.
  intros s m. unfold lift_step. destruct (lift_ls_err s); [reflexivity |].
  destruct m; simpl; try reflexivity;
    [ destruct (lift_check_ok s c) | destruct (lift_commit_ok s c)
    | destruct (lift_certify_ok s) ]; reflexivity.
Qed.

Lemma lift_cert_permanent : forall s m,
  lift_ls_cert s = true -> lift_ls_cert (lift_step s m) = true.
Proof.
  intros s m H. unfold lift_step. destruct (lift_ls_err s); [exact H |].
  destruct m; simpl; try exact H;
    [ destruct (lift_check_ok s c) | destruct (lift_commit_ok s c)
    | destruct (lift_certify_ok s) ]; try exact H; reflexivity.
Qed.

Lemma lift_base_blind : forall s b, lift_ls_cert (lift_step s (lift_LBase b)) = lift_ls_cert s.
Proof.
  intros s b. unfold lift_step. destruct (lift_ls_err s); reflexivity.
Qed.

Lemma lift_cert_raise : forall s m,
  lift_ls_cert s = false -> lift_ls_cert (lift_step s m) = true ->
  m = lift_LCertify /\ lift_certify_ok s = true.
Proof.
  intros s m H0 H1. unfold lift_step in H1. destruct (lift_ls_err s) eqn:Ee;
    [simpl in H1; congruence |].
  destruct m; simpl in H1; try congruence.
  - destruct (lift_check_ok s c); simpl in H1; congruence.
  - destruct (lift_commit_ok s c); simpl in H1; congruence.
  - destruct (lift_certify_ok s) eqn:Eo; [| simpl in H1; congruence]. auto.
Qed.

Lemma lift_ver_mono : forall s m, lift_ls_ver s <= lift_ls_ver (lift_step s m).
Proof.
  intros s m. unfold lift_step. destruct (lift_ls_err s); [simpl; lia |].
  destruct m; simpl; try lia;
    [ destruct (lift_check_ok s c) | destruct (lift_commit_ok s c)
    | destruct (lift_certify_ok s) ]; simpl; lia.
Qed.

(** A step that leaves the version alone leaves the base state alone. *)
Lemma lift_ver_eq_base : forall s m,
  lift_ls_ver (lift_step s m) = lift_ls_ver s -> lift_ls_base (lift_step s m) = lift_ls_base s.
Proof.
  intros s m H. unfold lift_step in *. destruct (lift_ls_err s); [reflexivity |].
  destruct m; simpl in *; try lia;
    [ destruct (lift_check_ok s c) | destruct (lift_commit_ok s c)
    | destruct (lift_certify_ok s) ]; simpl in *; reflexivity.
Qed.

Lemma lift_ver_mono_run : forall tr s, lift_ls_ver s <= lift_ls_ver (lift_lrun tr s).
Proof.
  induction tr as [| m tr IH]; intro s; [rewrite lift_lrun_nil; lia |].
  rewrite lift_lrun_cons. pose proof (lift_ver_mono s m). pose proof (IH (lift_step s m)).
  lia.
Qed.

Lemma lift_ver_eq_base_run : forall tr s,
  lift_ls_ver (lift_lrun tr s) = lift_ls_ver s -> lift_ls_base (lift_lrun tr s) = lift_ls_base s.
Proof.
  induction tr as [| m tr IH]; intros s H; [reflexivity |].
  rewrite lift_lrun_cons in *. pose proof (lift_ver_mono s m).
  pose proof (lift_ver_mono_run tr (lift_step s m)).
  assert (Hv : lift_ls_ver (lift_step s m) = lift_ls_ver s) by lia.
  rewrite (IH (lift_step s m)); [| lia]. apply lift_ver_eq_base. exact Hv.
Qed.

Lemma lift_facts_step : forall s m f,
  In f (lift_ls_facts (lift_step s m)) ->
  In f (lift_ls_facts s) \/
  exists c, m = lift_LCheck c /\ lift_check_ok s c = true /\ f = lift_mk_lfact c (lift_ls_ver s).
Proof.
  intros s m f H. unfold lift_step in H. destruct (lift_ls_err s); [left; exact H |].
  destruct m; simpl in H; try (left; exact H).
  - destruct (lift_check_ok s c) eqn:E; simpl in H.
    + destruct H as [<- | H]; [right; exists c; auto | left; exact H].
    + left; exact H.
  - destruct (lift_commit_ok s c); left; exact H.
  - destruct (lift_certify_ok s); left; exact H.
Qed.

Lemma lift_chan_step : forall s m f,
  lift_ls_chan (lift_step s m) = Some f ->
  lift_ls_chan s = Some f \/
  exists c, m = lift_LCommit c /\ lift_commit_ok s c = true /\ f = lift_mk_lfact c (lift_ls_ver s)
            /\ In f (lift_ls_facts s).
Proof.
  intros s m f H. unfold lift_step in H. destruct (lift_ls_err s); [left; exact H |].
  destruct m; simpl in H; try (left; exact H).
  - destruct (lift_check_ok s c); left; exact H.
  - destruct (lift_commit_ok s c) eqn:E; simpl in H.
    + injection H as <-. right. exists c. split; [reflexivity |].
      split; [exact E |]. split; [reflexivity |].
      unfold lift_commit_ok in E. apply andb_true_iff in E as [_ E].
      apply existsb_exists in E as [g [Hg Hgb]].
      apply lift_lfact_eqb_eq in Hgb. rewrite <- Hgb in Hg. exact Hg.
    + left; exact H.
  - destruct (lift_certify_ok s); left; exact H.
Qed.

(** * Provenance of a run from a start with an empty table *)

Lemma lift_facts_prov : forall s0, lift_ls_facts s0 = [] -> forall tr f,
  In f (lift_ls_facts (lift_lrun tr s0)) ->
  exists pre c post, tr = pre ++ lift_LCheck c :: post /\
    f = lift_mk_lfact c (lift_ls_ver (lift_lrun pre s0)) /\ lift_check_ok (lift_lrun pre s0) c = true.
Proof.
  intros s0 H0 tr. induction tr as [| m tr IH] using rev_ind; intros f Hin.
  - rewrite lift_lrun_nil in Hin. rewrite H0 in Hin. contradiction.
  - rewrite lift_lrun_snoc in Hin. destruct (lift_facts_step _ _ _ Hin) as [H | [c [Hm [Hok Hf]]]].
    + destruct (IH f H) as [pre [c [post [-> [Hf Hok]]]]].
      exists pre, c, (post ++ [m]). split; [| split; assumption].
      rewrite <- app_assoc. reflexivity.
    + subst m. exists tr, c, []. split; [reflexivity |]. split; assumption.
Qed.

Lemma lift_chan_prov : forall s0, lift_ls_chan s0 = None -> forall tr f,
  lift_ls_chan (lift_lrun tr s0) = Some f ->
  exists pre c mid2, tr = pre ++ lift_LCommit c :: mid2 /\
    f = lift_mk_lfact c (lift_ls_ver (lift_lrun pre s0)) /\ In f (lift_ls_facts (lift_lrun pre s0)).
Proof.
  intros s0 H0 tr. induction tr as [| m tr IH] using rev_ind; intros f Hch.
  - rewrite lift_lrun_nil in Hch. rewrite H0 in Hch. discriminate.
  - rewrite lift_lrun_snoc in Hch. destruct (lift_chan_step _ _ _ Hch)
      as [H | [c [Hm [Hok [Hf Hin]]]]].
    + destruct (IH f H) as [pre [c [mid2 [-> [Hf Hin]]]]].
      exists pre, c, (mid2 ++ [m]). split; [| split; assumption].
      rewrite <- app_assoc. reflexivity.
    + subst m. exists tr, c, []. split; [reflexivity |]. split; assumption.
Qed.

(** The first step that raises the certified flag is a CERTIFY. *)
Lemma lift_cert_first : forall tr s0,
  lift_ls_cert s0 = false -> lift_ls_cert (lift_lrun tr s0) = true ->
  exists pre post, tr = pre ++ lift_LCertify :: post /\
    lift_ls_cert (lift_lrun pre s0) = false /\ lift_certify_ok (lift_lrun pre s0) = true /\
    lift_ls_cert (lift_lrun (pre ++ [lift_LCertify]) s0) = true.
Proof.
  induction tr as [| m tr IH]; intros s0 H0 H1.
  - rewrite lift_lrun_nil in H1. congruence.
  - rewrite lift_lrun_cons in H1. destruct (lift_ls_cert (lift_step s0 m)) eqn:E.
    + destruct (lift_cert_raise _ _ H0 E) as [-> Hok]. exists [], tr.
      simpl. split; [reflexivity |]. split; [exact H0 |]. split; [exact Hok |].
      exact E.
    + destruct (IH _ E H1) as [pre [post [-> [Hc [Hok Hup]]]]].
      exists (m :: pre), post. rewrite !lift_lrun_cons in *. simpl.
      repeat split; try reflexivity; assumption.
Qed.

(** * The interface *)

Definition lift_kind (m : lift_lmove) : T.kind C :=
  match m with
  | lift_LBase _ => T.KBase
  | lift_LCheck c => T.KCheck c
  | lift_LCommit c => T.KCommit c
  | lift_LCertify => T.KCertify
  end.

Definition lift_clean (s : lift_lstate) : Prop :=
  lift_ls_facts s = [] /\ lift_ls_chan s = None /\ lift_ls_cert s = false.

Section Interface.

Variable U : T.universal_base M0.

Definition lift_load (a b : nat) : lift_lstate :=
  lift_mk_ls (T.ub_load U a b) 0 [] None false 0 false.

Definition lift_live (s : lift_lstate) : Prop :=
  lift_ls_err s = false /\ T.ub_live U (lift_ls_base s).

Lemma lift_sim : forall s i, lift_live s ->
  T.ub_window U (lift_ls_base (lift_step s (lift_LBase (T.ub_compile U i))))
    = T.cm_exec i (T.ub_window U (lift_ls_base s)) /\
  lift_live (lift_step s (lift_LBase (T.ub_compile U i))).
Proof.
  intros s i [He Hb]. unfold lift_step. rewrite He. simpl.
  destruct (T.ub_sim U (lift_ls_base s) i Hb) as [Hw Hb']. split; [exact Hw |].
  split; [reflexivity | exact Hb'].
Qed.

Definition lift_ubase : T.universal_base lift_machine :=
  T.mk_ub lift_machine (fun s => T.ub_window U (lift_ls_base s)) lift_live
    (fun i => lift_LBase (T.ub_compile U i)) lift_load
    (fun a b => T.ub_load_window U a b)
    (fun a b => conj eq_refl (T.ub_load_live U a b))
    lift_sim.

(** The one-step equations, by cases on the latch and the checks. *)
Lemma lift_step_err : forall s m, lift_ls_err s = true ->
  lift_step s m = lift_mk_ls (lift_ls_base s) (lift_ls_ver s) (lift_ls_facts s) (lift_ls_chan s) true
                        (lift_ls_mu s + lift_cost m) (lift_ls_cert s).
Proof. intros s m H. unfold lift_step. rewrite H. reflexivity. Qed.

Lemma lift_step_check_ok : forall s c, lift_ls_err s = false -> lift_check_ok s c = true ->
  lift_step s (lift_LCheck c) =
  lift_mk_ls (lift_ls_base s) (lift_ls_ver s) (lift_mk_lfact c (lift_ls_ver s) :: lift_ls_facts s) (lift_ls_chan s)
        false (lift_ls_mu s + 1) (lift_ls_cert s).
Proof. intros s c He Hk. unfold lift_step. rewrite He, Hk. reflexivity. Qed.

Lemma lift_step_check_fail : forall s c, lift_ls_err s = false -> lift_check_ok s c = false ->
  lift_step s (lift_LCheck c) =
  lift_mk_ls (lift_ls_base s) (lift_ls_ver s) (lift_ls_facts s) (lift_ls_chan s) true (lift_ls_mu s + 1) (lift_ls_cert s).
Proof. intros s c He Hk. unfold lift_step. rewrite He, Hk. reflexivity. Qed.

Lemma lift_step_commit_ok : forall s c, lift_ls_err s = false -> lift_commit_ok s c = true ->
  lift_step s (lift_LCommit c) =
  lift_mk_ls (lift_ls_base s) (lift_ls_ver s) (lift_ls_facts s) (Some (lift_mk_lfact c (lift_ls_ver s)))
        false (lift_ls_mu s + 1) (lift_ls_cert s).
Proof. intros s c He Hk. unfold lift_step. rewrite He, Hk. reflexivity. Qed.

Lemma lift_step_certify_ok : forall s, lift_ls_err s = false -> lift_certify_ok s = true ->
  lift_step s lift_LCertify =
  lift_mk_ls (lift_ls_base s) (lift_ls_ver s) (lift_ls_facts s) (lift_ls_chan s) false (lift_ls_mu s + 1) true.
Proof. intros s He Hk. unfold lift_step. rewrite He, Hk. reflexivity. Qed.

(** The interface of ThieleComplete.v for the lifted machine. *)
Definition lift_interface : T.thiele_interface lift_machine :=
  T.mk_ti lift_machine lift_ubase C lift_kind
    (fun c s => lift_ll_mean LG c (lift_ls_base s))
    (fun s c => lift_check_ok s c)
    (fun c s s' => lift_ls_base s = lift_ls_base s')
    lift_clean lift_ls_mu.

Ltac lift_leq := repeat first [rewrite <- app_assoc | progress simpl]; reflexivity.

(** (a) The base is universal and leaves the record alone. *)
Lemma lift_base_clause : T.universal_base_clause lift_interface.
Proof.
  split; [| split; [| split]].
  - intro i. reflexivity.
  - intros a b. unfold T.load. simpl. unfold lift_clean. simpl. repeat split; reflexivity.
  - intros s m Hk. destruct m; simpl in Hk; try discriminate. apply lift_base_blind.
  - intros s m H. apply lift_cert_permanent, H.
Qed.

(** (b) The record is earned: the chain of ThieleComplete.v in front of every raise. *)
Lemma lift_earned_chain : forall s0 tr, lift_clean s0 -> lift_ls_cert (lift_lrun tr s0) = true ->
  T.earned_chain lift_interface s0 tr.
Proof.
  intros s0 tr [Hf [Hc H0]] H1.
  destruct (lift_cert_first tr s0 H0 H1) as [pre [post [Htr [Hpre [Hok Hup]]]]].
  unfold lift_certify_ok in Hok. apply andb_true_iff in Hok as [_ Hok].
  destruct (lift_ls_chan (lift_lrun pre s0)) as [f |] eqn:Hch; [| discriminate].
  destruct (lift_chan_prov s0 Hc pre f Hch) as [pre' [c [mid2 [Hpre' [Hfc Hin]]]]].
  destruct (lift_facts_prov s0 Hf pre' f Hin) as [pre1 [c1 [mid1 [Hpre1 [Hfc1 Hck]]]]].
  rewrite Hfc in Hfc1. injection Hfc1 as Hc1 Hv. subst c1.
  assert (Hall : tr = pre1 ++ lift_LCheck c :: mid1 ++ lift_LCommit c :: mid2 ++ lift_LCertify :: post)
    by (rewrite Htr, Hpre', Hpre1; lift_leq).
  assert (Hpre_eq : pre = pre1 ++ lift_LCheck c :: mid1 ++ lift_LCommit c :: mid2)
    by (rewrite Hpre', Hpre1; lift_leq).
  exists pre1, c, (lift_LCheck c), mid1, (lift_LCommit c), mid2, lift_LCertify, post.
  split; [exact Hall |]. split; [reflexivity |]. split; [reflexivity |].
  split; [reflexivity |]. split; [exact Hck |]. split.
  - intros t1 t2 Hm. simpl.
    set (s := lift_lrun pre1 s0) in *.
    assert (Hrun : lift_lrun pre' s0 = lift_lrun t2 (lift_lrun (lift_LCheck c :: t1) s)).
    { rewrite Hpre1, lift_lrun_app, Hm.
      replace (lift_LCheck c :: (t1 ++ t2)) with ((lift_LCheck c :: t1) ++ t2) by reflexivity.
      rewrite lift_lrun_app. reflexivity. }
    assert (Hlo : lift_ls_ver s <= lift_ls_ver (lift_lrun (lift_LCheck c :: t1) s))
      by apply lift_ver_mono_run.
    assert (Hhi : lift_ls_ver (lift_lrun (lift_LCheck c :: t1) s) <= lift_ls_ver (lift_lrun pre' s0)).
    { rewrite Hrun. apply lift_ver_mono_run. }
    assert (Heq : lift_ls_ver (lift_lrun (lift_LCheck c :: t1) s) = lift_ls_ver s) by lia.
    unfold s in *.
    rewrite lift_lrun_app.
    rewrite (lift_ver_eq_base_run (lift_LCheck c :: t1) (lift_lrun pre1 s0) Heq). reflexivity.
  - assert (Hl2 : pre1 ++ lift_LCheck c :: mid1 ++ lift_LCommit c :: mid2 = pre)
      by (symmetry; exact Hpre_eq).
    assert (Hl3 : pre1 ++ lift_LCheck c :: mid1 ++ lift_LCommit c :: mid2 ++ [lift_LCertify]
                  = pre ++ [lift_LCertify]) by (rewrite Hpre_eq; lift_leq).
    change (lift_ls_cert (lift_lrun (pre1 ++ lift_LCheck c :: mid1 ++ lift_LCommit c :: mid2) s0) = false /\
            lift_ls_cert (lift_lrun (pre1 ++ lift_LCheck c :: mid1 ++ lift_LCommit c :: mid2 ++ [lift_LCertify]) s0)
              = true).
    rewrite Hl2, Hl3. split; [exact Hpre | exact Hup].
Qed.

Lemma lift_earned_clause : T.earned_record_clause lift_interface.
Proof.
  split; [intros s [_ [_ H]]; exact H |]. split.
  - intros s0 tr H0 H1. apply lift_earned_chain; assumption.
  - split.
    + intros s c H. simpl in *. unfold lift_check_ok in H.
      apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H].
      apply lift_ll_eval_iff, H.
    + intros c s s' Hs Hm. simpl in *. rewrite <- Hs. exact Hm.
Qed.

(** (c) The toll is exact. *)
Lemma lift_toll_clause : T.exact_toll_clause lift_interface.
Proof.
  split.
  - intro m. destruct m; reflexivity.
  - intros s m. simpl. apply lift_mu_step.
Qed.

(** (d) Non-vacuity of the witness claim. *)
Lemma lift_chain_true : forall s c, 0 < cap -> lift_ls_err s = false -> lift_ls_facts s = [] ->
  lift_ll_mean LG c (lift_ls_base s) ->
  lift_ls_cert (lift_lrun [lift_LCheck c; lift_LCommit c; lift_LCertify] s) = true.
Proof.
  intros s c Hcap He Hf Hm.
  assert (Hk : lift_check_ok s c = true).
  { unfold lift_check_ok. rewrite He, Hf. simpl. apply andb_true_iff. split.
    - apply lift_ll_eval_iff, Hm.
    - apply Nat.ltb_lt. exact Hcap. }
  rewrite !lift_lrun_cons, lift_lrun_nil. rewrite (lift_step_check_ok s c He Hk).
  set (s1 := lift_mk_ls (lift_ls_base s) (lift_ls_ver s) (lift_mk_lfact c (lift_ls_ver s) :: lift_ls_facts s)
                   (lift_ls_chan s) false (lift_ls_mu s + 1) (lift_ls_cert s)).
  assert (Hc : lift_commit_ok s1 c = true).
  { unfold lift_commit_ok, s1. simpl. apply orb_true_iff. left.
    apply lift_lfact_eqb_eq. reflexivity. }
  rewrite (lift_step_commit_ok s1 c eq_refl Hc).
  set (s2 := lift_mk_ls (lift_ls_base s1) (lift_ls_ver s1) (lift_ls_facts s1)
                   (Some (lift_mk_lfact c (lift_ls_ver s1))) false (lift_ls_mu s1 + 1) (lift_ls_cert s1)).
  assert (Hr : lift_certify_ok s2 = true) by reflexivity.
  rewrite (lift_step_certify_ok s2 eq_refl Hr). reflexivity.
Qed.

Lemma lift_run_err : forall tr s, lift_ls_err s = true -> lift_ls_cert (lift_lrun tr s) = lift_ls_cert s.
Proof.
  induction tr as [| m tr IH]; intros s H; [reflexivity |].
  rewrite lift_lrun_cons, (lift_step_err s m H). rewrite IH; reflexivity.
Qed.

Lemma lift_chain_false : forall s c, 0 < cap -> lift_ls_err s = false ->
  ~ lift_ll_mean LG c (lift_ls_base s) -> lift_ls_cert s = false ->
  lift_ls_cert (lift_lrun [lift_LCheck c; lift_LCommit c; lift_LCertify] s) = false.
Proof.
  intros s c Hcap He Hn Hc0.
  assert (Hk : lift_check_ok s c = false).
  { destruct (lift_check_ok s c) eqn:E; [| reflexivity]. exfalso. apply Hn.
    unfold lift_check_ok in E. apply andb_true_iff in E as [E _].
    apply andb_true_iff in E as [_ E]. apply lift_ll_eval_iff, E. }
  rewrite lift_lrun_cons, (lift_step_check_fail s c He Hk).
  rewrite lift_run_err; [simpl; exact Hc0 | reflexivity].
Qed.

Lemma lift_nonvac_clause : 0 < cap -> lift_nonvacuous U LG ->
  T.non_vacuity_clause lift_interface.
Proof.
  intros Hcap [c [Hy Hn]].
  exists c, (lift_LCheck c), (lift_LCommit c), lift_LCertify.
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [| split; [exact Hy | exact Hn]].
  intros a b.
  change (lift_ls_cert (lift_lrun [lift_LCheck c; lift_LCommit c; lift_LCertify] (lift_load a b)) = true
          <-> lift_ll_mean LG c (lift_ls_base (lift_load a b))).
  split.
  - intro H. destruct (lift_ll_eval LG c (lift_ls_base (lift_load a b))) eqn:E.
    + apply lift_ll_eval_iff, E.
    + exfalso.
      assert (Hm : ~ lift_ll_mean LG c (lift_ls_base (lift_load a b))).
      { intro Hm. apply lift_ll_eval_iff in Hm. congruence. }
      pose proof (lift_chain_false (lift_load a b) c Hcap eq_refl Hm eq_refl) as H2.
      congruence.
  - intro H. exact (lift_chain_true (lift_load a b) c Hcap eq_refl eq_refl H).
Qed.


End Interface.

End Lift.

(** The base machine and the claim language are implicit from here on. *)
Arguments lift_mk_lfact {M0 LG} _ _.
Arguments lift_lf_claim {M0 LG} _.
Arguments lift_lf_ver {M0 LG} _.
Arguments lift_lfact_eqb {M0 LG} f g.
Arguments lift_mk_ls {M0 LG} _ _ _ _ _ _ _.
Arguments lift_ls_base {M0 LG} _.
Arguments lift_ls_ver {M0 LG} _.
Arguments lift_ls_facts {M0 LG} _.
Arguments lift_ls_chan {M0 LG} _.
Arguments lift_ls_err {M0 LG} _.
Arguments lift_ls_mu {M0 LG} _.
Arguments lift_ls_cert {M0 LG} _.
Arguments lift_LBase {M0 LG} m.
Arguments lift_LCheck {M0 LG} c.
Arguments lift_LCommit {M0 LG} c.
Arguments lift_LCertify {M0 LG}.
Arguments lift_cost {M0 LG} m.
Arguments lift_check_ok {M0 LG} cap s c.
Arguments lift_commit_ok {M0 LG} s c.
Arguments lift_certify_ok {M0 LG} s.
Arguments lift_step {M0 LG} cap s m.
Arguments lift_lrun {M0 LG} cap tr s.
Arguments lift_clean {M0 LG} s.
Arguments lift_kind {M0 LG} m.
Arguments lift_load {M0 LG} U a b.
Arguments lift_live {M0 LG} U s.
Arguments lift_ubase {M0 LG} cap U.

(** * The lifting theorem *)

Theorem lift_thiele_complete_with : forall M0 (LG : lift_lang (T.m_state M0)) cap
    (U : T.universal_base M0),
  0 < cap -> lift_nonvacuous U LG ->
  T.thiele_complete_with (lift_interface M0 LG cap U).
Proof.
  intros M0 LG cap U Hcap Hnv.
  split; [apply lift_base_clause |]. split; [apply lift_earned_clause |].
  split; [apply lift_toll_clause | apply lift_nonvac_clause; assumption].
Qed.

Theorem lift_thiele_complete : forall M0 (LG : lift_lang (T.m_state M0)) cap
    (U : T.universal_base M0),
  0 < cap -> lift_nonvacuous U LG -> T.thiele_complete (lift_machine M0 LG cap).
Proof.
  intros M0 LG cap U Hcap Hnv. exists (lift_interface M0 LG cap U).
  apply lift_thiele_complete_with; assumption.
Qed.

(** * The window language: nothing beyond the universal base *)

(** A claim is "register r holds at least n" or "the program counter is n",
    read on the two-counter window of the base state. *)
Inductive lift_wclaim : Type :=
| lift_WGe (r : T.reg) (n : nat)
| lift_WPc (n : nat).

Definition lift_wc_eqb (c d : lift_wclaim) : bool :=
  match c, d with
  | lift_WGe T.RA n, lift_WGe T.RA m => Nat.eqb n m
  | lift_WGe T.RB n, lift_WGe T.RB m => Nat.eqb n m
  | lift_WPc n, lift_WPc m => Nat.eqb n m
  | _, _ => false
  end.

Lemma lift_wc_eqb_eq : forall c d, lift_wc_eqb c d = true <-> c = d.
Proof.
  intros [[|] n | n] [[|] m | m]; simpl; split; intro H;
    try discriminate; try (apply Nat.eqb_eq in H; subst; reflexivity);
    try (inversion H; subst; apply Nat.eqb_refl).
Qed.

Definition lift_wc_eval (c : lift_wclaim) (x : T.cm_conf) : bool :=
  match c with
  | lift_WGe r n => Nat.leb n (T.cm_get x r)
  | lift_WPc n => Nat.eqb (fst x) n
  end.

Definition lift_wc_mean (c : lift_wclaim) (x : T.cm_conf) : Prop :=
  match c with
  | lift_WGe r n => n <= T.cm_get x r
  | lift_WPc n => fst x = n
  end.

Lemma lift_wc_eval_iff : forall c x, lift_wc_eval c x = true <-> lift_wc_mean c x.
Proof.
  intros [r n | n] x; simpl; [apply Nat.leb_le | apply Nat.eqb_eq].
Qed.

Definition lift_window_lang (M0 : T.machine) (U : T.universal_base M0)
  : lift_lang (T.m_state M0) :=
  lift_mk_ll (T.m_state M0) lift_wclaim lift_wc_eqb lift_wc_eqb_eq
    (fun c s => lift_wc_mean c (T.ub_window U s))
    (fun c s => lift_wc_eval c (T.ub_window U s))
    (fun c s => lift_wc_eval_iff c (T.ub_window U s)).

Lemma lift_window_nonvacuous : forall M0 (U : T.universal_base M0),
  lift_nonvacuous U (lift_window_lang M0 U).
Proof.
  intros M0 U. exists (lift_WGe T.RA 1). split.
  - exists 1, 0. simpl. rewrite (T.ub_load_window U 1 0). simpl. lia.
  - exists 0, 0. simpl. rewrite (T.ub_load_window U 0 0). simpl. lia.
Qed.

(** Every universal base lifts, with no further hypothesis, for every cap of
    at least 1 (the repository's machine has cap 16). *)
Theorem lift_window_thiele_complete : forall M0 (U : T.universal_base M0) cap,
  0 < cap -> T.thiele_complete (lift_machine M0 (lift_window_lang M0 U) cap).
Proof.
  intros M0 U cap Hcap. apply (lift_thiele_complete M0 _ cap U Hcap).
  apply lift_window_nonvacuous.
Qed.

Print Assumptions lift_thiele_complete.
Print Assumptions lift_window_thiele_complete.
