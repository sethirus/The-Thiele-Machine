(** CzTower: the real nested simulations of the repository as links.

    The fixed host program U_P runs a priced guest program of the small
    machine, and the compiler turns every computably presented machine into
    such a guest.  Each of these is a link in the sense of CzLink:

      cmpz_ds_pres     a presented machine M run from s0, as a driven system
                       whose state carries its ledger and its latch;
      cmpz_ds_guest    the priced small machine running a program Q;
      cmpz_ds_host     the host machine running U_P.

      cmpz_compile_link   M run from s0  ==>  its compiled guest program,
                          with surcharge exactly surcharge M s0 n (at most 2 from a
                          start where the reading is no);
      cmpz_priced_link    a priced guest program Q  ==>  the host running
                          U_P on it, with surcharge 0: the record, the ledger
                          and the halting are the guest's exactly;
      cmpz_host_link      the composite: M run from s0  ==>  U_P loaded with
                          the compiled guest, a tower of two links, with the
                          surcharge of the first and none from the second.

    The surcharge per level.  A presented machine whose first raising move
    costs c, with its reading at no to begin with, is carried at surcharge
    3 - c once its latch is up, and 0 before: at most 2 because the raising
    move pays the toll.  When every move the machine takes costs at most 1,
    and a Thiele-complete machine never charges more than 1 for a move
    ([Minimal.ThieleComplete.complete_costs_at_most_one]), the surcharge is
    exactly 2:

      cmpz_surcharge_exact_two   the bound 2 is attained by every presented
                                 machine all of whose moves cost at most 1,
                                 whenever its latch is up.

    So a machine that is itself a Thiele machine, run on U_P, pays exactly 2
    more than it did on its own, and no run on U_P pays less than 3 for a
    raised flag ([PresentedUniversal.presented_universal_no_exact_below_three]).
    The tower of k such levels pays 2 per level above the first
    ([cmpz_tower_presented_exact]).

    What a tower of depth above 2 needs.  The level above the host would be
    a presented machine whose driven run is the host's run.  The repository
    does not build that machine: the registers of the host are functions from
    numbers to numbers, which have no injective code, so the host machine as
    it stands is not a presented machine.  [cmpz_tower_presented] states
    exactly what a tower of any depth gives, as a theorem about any sequence
    of presented machines each of which presents the host run of the one
    below; its hypothesis is not proved here. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Minimal Require Import CzLink.
From Undecidability.FRACTRAN.Util Require Import prime_seq.
Require Import Kernel.UniversalPCodes Kernel.UniversalPBridge Kernel.UniversalPBlocks
  Kernel.UniversalPLayout Kernel.UniversalPPhases Kernel.UniversalPSim Kernel.UniversalPRun.
Require Minimal.ThieleComplete.
Require Import Minimal.Presented Kernel.Presentation.
Require Import Kernel.CompilerCodes Kernel.CompilerChecker Kernel.CompilerGuest
  Kernel.CompilerGuestRun Kernel.PresentedUniversal.
Module T := Minimal.ThieleComplete.
Require Import Kernel.AxHost.

Local Notation hstate := (@M.pu_state pu_hprop).

(** * A presented machine as a driven system *)

Section Pres.

Variable Mp : presented_machine.

Local Notation st := (T.cs_state (pm_sys Mp)).
Local Notation rd := (T.cs_cert (pm_sys Mp)).
Local Notation cstep := (T.cs_step (pm_sys Mp)).
Local Notation ccost := (T.cs_cost (pm_sys Mp)).

(** The state is the machine's state, the ledger so far, and the latch. *)
Definition cmpz_ds_pres : cmpz_ds :=
  mk_ds (st * nat * bool)
    (fun x => match pm_next Mp (fst (fst x)) with
              | None => None
              | Some i => Some (cstep (fst (fst x)) i, snd (fst x) + ccost i,
                                orb (snd x) (rd (cstep (fst (fst x)) i)))
              end)
    (fun x => snd (fst x)) (fun x => snd x).

Definition cmpz_pres_start (s0 : st) : ds_state cmpz_ds_pres := (s0, 0, rd s0).

Lemma cmpz_mlatch_rd : forall s n, rd s = true -> mlatch Mp s n = true.
Proof. intros s [| n] H; simpl; rewrite H; reflexivity. Qed.

Lemma cmpz_bool_absorb : forall b r m : bool, (r = true -> m = true) -> orb (orb b r) m = orb b m.
Proof. intros [] [] [] H; simpl in *; try reflexivity; try (specialize (H eq_refl); discriminate). Qed.

Lemma cmpz_pres_run : forall n s l b,
  orb b (rd s) = b ->
  ds_run cmpz_ds_pres n (s, l, b)
    = (presented_run Mp s n, l + mledger Mp s n, orb b (mlatch Mp s n)).
Proof.
  induction n as [| n IH]; intros s l b H.
  - simpl. rewrite Nat.add_0_r, orb_false_r, H. reflexivity.
  - simpl. destruct (pm_next Mp s) as [i |] eqn:E.
    + assert (H' : orb (orb b (rd (cstep s i))) (rd (cstep s i)) = orb b (rd (cstep s i))).
      { destruct b, (rd (cstep s i)); reflexivity. }
      rewrite (IH _ _ _ H'). cbn [fst snd].
      rewrite (cmpz_bool_absorb b (rd (cstep s i)) (mlatch Mp (cstep s i) n)
                (fun Hr => cmpz_mlatch_rd _ _ Hr)).
      replace (l + (ccost i + mledger Mp (cstep s i) n)) with (l + ccost i + mledger Mp (cstep s i) n) by lia.
      rewrite <- H. destruct b, (rd s); reflexivity.
    + rewrite Nat.add_0_r, orb_false_r, H. reflexivity.
Qed.

Lemma cmpz_presented_run_halted : forall s0 n,
  pm_next Mp (presented_run Mp s0 n) = None -> presented_run Mp s0 (S n) = presented_run Mp s0 n.
Proof. intros s0 n H. rewrite presented_run_succ, H. reflexivity. Qed.

Lemma cmpz_mledger_halted : forall s0 n,
  pm_next Mp (presented_run Mp s0 n) = None -> mledger Mp s0 (S n) = mledger Mp s0 n.
Proof. intros s0 n H. rewrite mledger_succ, H. lia. Qed.

Lemma cmpz_mlatch_halted : forall s0 n,
  pm_next Mp (presented_run Mp s0 n) = None -> mlatch Mp s0 (S n) = mlatch Mp s0 n.
Proof.
  intros s0 n H. apply eq_true_iff_eq. rewrite !presented_mlatch_iff. split.
  - intros [m [Hm Hr]]. destruct (Nat.eq_dec m (S n)) as [-> | Hne].
    + exists n. split; [lia |]. rewrite <- (cmpz_presented_run_halted s0 n H). exact Hr.
    + exists m. split; [lia | exact Hr].
  - intros [m [Hm Hr]]. exists m. split; [lia | exact Hr].
Qed.

Lemma cmpz_surcharge_halted : forall s0 n,
  pm_next Mp (presented_run Mp s0 n) = None -> surcharge Mp s0 (S n) = surcharge Mp s0 n.
Proof.
  intros s0 n H. unfold surcharge. rewrite (cmpz_mlatch_halted s0 n H).
  destruct (mlatch Mp s0 n) eqn:Hl; [| reflexivity].
  unfold raise_cost. rewrite (presented_first_raise_stable Mp n (S n) s0 Hl (le_S _ _ (le_n n))).
  reflexivity.
Qed.

(** A run that has not halted at step n has not halted at any earlier step. *)
Lemma cmpz_not_halted_before : forall s0 n,
  pm_next Mp (presented_run Mp s0 n) <> None ->
  forall m, m <= n -> pm_next Mp (presented_run Mp s0 m) <> None.
Proof.
  intros s0 n Hn m Hm Hh. apply Hn.
  destruct (presented_halted_stable Mp s0 m n Hh Hm) as [Hr _].
  rewrite Hr. exact Hh.
Qed.

(** The bound 2 is attained by every presented machine whose moves cost at
    most 1. *)
Theorem cmpz_surcharge_exact_two : forall s0 n,
  rd s0 = false ->
  (forall m i, m < n -> pm_next Mp (presented_run Mp s0 m) = Some i -> ccost i <= 1) ->
  mlatch Mp s0 n = true -> surcharge Mp s0 n = 2.
Proof.
  intros s0 n H0 Hc Hl.
  destruct (presented_first_raise_spec Mp n s0 H0 Hl) as [m [i [Hm [Hn [Hall [Hup Hf]]]]]].
  unfold surcharge. rewrite Hl. unfold raise_cost. rewrite Hf.
  pose proof (T.cs_cert_costs (pm_sys Mp) (presented_run Mp s0 m) i (Hall m (le_n m)) Hup) as H1.
  pose proof (Hc m i Hm Hn) as H2. lia.
Qed.

(** A latch up from the start costs 3. *)
Theorem cmpz_surcharge_start_up : forall s0 n,
  rd s0 = true -> surcharge Mp s0 n = 3.
Proof.
  intros s0 n H0. unfold surcharge. rewrite (cmpz_mlatch_rd s0 n H0).
  unfold raise_cost. destruct n; simpl; rewrite H0; reflexivity.
Qed.

End Pres.

(** * A priced guest program as a driven system *)

Definition cmpz_ds_guest (Q : list E.instr) : cmpz_ds :=
  mk_ds E.state
    (fun g => match E.next_instr Q (E.core_of g) with
              | None => None
              | Some i => Some (E.exec g i)
              end)
    (fun g => E.mu g) (fun g => E.cert g).

Lemma cmpz_guest_run_eq : forall Q n g, ds_run (cmpz_ds_guest Q) n g = E.run_prog n Q g.
Proof.
  intros Q n. induction n as [| n IH]; intro g; [reflexivity |].
  cbn [ds_run ds_next cmpz_ds_guest].
  change (E.run_prog (S n) Q g) with (E.run_prog n Q (E.step Q g)).
  unfold E.step. destruct (E.next_instr Q (E.core_of g)) as [i |] eqn:Hn.
  - apply IH.
  - symmetry. apply (E.run_prog_halted n Q g). exact Hn.
Qed.

(** * The host as a driven system *)

Definition cmpz_ds_host : cmpz_ds :=
  mk_ds hstate
    (fun h => match M.pu_next_instr U_P (M.core_of h) with
              | None => None
              | Some i => Some (M.pu_exec pu_hprop_eqb pu_heval h i)
              end)
    (fun h => M.mu h) (fun h => M.cert h).

Lemma cmpz_host_run_eq : forall n h,
  ds_run cmpz_ds_host n h = M.pu_run_prog pu_hprop_eqb pu_heval n U_P h.
Proof.
  induction n as [| n IH]; intro h; [reflexivity |].
  cbn [ds_run ds_next cmpz_ds_host].
  change (M.pu_run_prog pu_hprop_eqb pu_heval (S n) U_P h)
    with (M.pu_run_prog pu_hprop_eqb pu_heval n U_P (M.pu_step pu_hprop_eqb pu_heval U_P h)).
  unfold M.pu_step. destruct (M.pu_next_instr U_P (M.core_of h)) as [i |] eqn:Hn.
  - apply IH.
  - symmetry. apply (M.pu_multi_run_prog_halted pu_hprop_eqb pu_heval n U_P h). exact Hn.
Qed.

Lemma cmpz_guest_halted_iff : forall Q g,
  ds_halted (cmpz_ds_guest Q) g <-> E.halted Q (E.core_of g).
Proof.
  intros Q g. unfold ds_halted, E.halted. cbn [ds_next cmpz_ds_guest].
  destruct (E.next_instr Q (E.core_of g)); split; intro H; try reflexivity; discriminate.
Qed.

Lemma cmpz_host_halted_iff : forall h,
  ds_halted cmpz_ds_host h <-> M.pu_halted U_P (M.core_of h).
Proof.
  intro h. unfold ds_halted, M.pu_halted. cbn [ds_next cmpz_ds_host].
  destruct (M.pu_next_instr U_P (M.core_of h)); split; intro H; try reflexivity; discriminate.
Qed.

(** * The priced link: a guest program run by U_P, nothing added *)

Theorem cmpz_priced_link : forall Q x y,
  cmpz_link (cmpz_ds_guest Q) cmpz_ds_host (E.start x y) (pu_hload Q x y) 0 0
    (fun g h => pu_rel Q g h \/ pu_rel_halt Q g h).
Proof.
  intros Q x y. split.
  - intro n. destruct (ax_universal_record Q x y n) as [t [Hrel [Hrec Hmu]]].
    exists t, 0. rewrite cmpz_guest_run_eq, cmpz_host_run_eq.
    change (E.run_prog n Q (E.start x y)) with (pu_grun Q x y n).
    change (M.pu_run_prog pu_hprop_eqb pu_heval t U_P (pu_hload Q x y)) with (pu_hrun Q x y t).
    split; [destruct Hrel as [[R _] | RH]; [left; exact R | right; exact RH] |].
    split; [exact (f_equal fst Hrec) |].
    split; [cbn; lia |].
    split; [intros _; reflexivity | intros _; split; lia].
  - destruct (pu_universal_halting Q x y) as [F B]. split.
    + intros [n Hn]. rewrite cmpz_guest_run_eq in Hn.
      apply cmpz_guest_halted_iff in Hn.
      destruct (F (ex_intro _ n Hn)) as [t Ht]. exists t.
      rewrite cmpz_host_run_eq. apply cmpz_host_halted_iff. exact Ht.
    + intros [t Ht]. rewrite cmpz_host_run_eq in Ht.
      apply cmpz_host_halted_iff in Ht.
      destruct (B (ex_intro _ t Ht)) as [n Hn]. exists n.
      rewrite cmpz_guest_run_eq. apply cmpz_guest_halted_iff. exact Hn.
  - destruct (pu_universal_flag_iff Q x y) as [F B]. split.
    + intros [t Ht]. rewrite cmpz_host_run_eq in Ht.
      destruct (B (ex_intro _ t Ht)) as [n Hn]. exists n.
      rewrite cmpz_guest_run_eq. exact Hn.
    + intros [n Hn]. rewrite cmpz_guest_run_eq in Hn.
      destruct (F (ex_intro _ n Hn)) as [t Ht]. exists t.
      rewrite cmpz_host_run_eq. exact Ht.
Qed.

Print Assumptions cmpz_priced_link.
Print Assumptions cmpz_surcharge_exact_two.

(** * The compile link: a presented machine run as its compiled guest *)

Section Compile.

Variable Mp : presented_machine.
Variable pc : cg_presentation Mp.
Variable s0 : T.cs_state (pm_sys Mp).

Local Notation rd := (T.cs_cert (pm_sys Mp)).
Local Notation ccost := (T.cs_cost (pm_sys Mp)).

Local Notation Q := (cg_guest Mp pc).

(** The guest's start: counter A is 0, counter B is the code of the start. *)
Definition cmpz_gstart : E.state := E.start 0 (pu_guest_b Mp pc s0).

Definition cmpz_rel_compile : ds_state (cmpz_ds_pres Mp) -> ds_state (cmpz_ds_guest Q) -> Prop :=
  fun x g => pm_sdec Mp (cg_expo (qs 0) (E.cb (E.core_of g))) = Some (fst (fst x)).

Lemma cmpz_compile_points : forall n, exists N,
  pm_sdec Mp (cg_expo (qs 0) (E.cb (E.core_of (E.run_prog N Q cmpz_gstart))))
    = Some (presented_run Mp s0 n) /\
  E.mu (E.run_prog N Q cmpz_gstart) = mledger Mp s0 n + surcharge Mp s0 n /\
  E.cert (E.run_prog N Q cmpz_gstart) = mlatch Mp s0 n.
Proof.
  induction n as [| n IH].
  - destruct (cg_guest_matching_points Mp pc s0 0
                (fun m Hm => False_ind _ (Nat.nlt_0_r m Hm)))
      as (N & _ & _ & _ & _ & Hd & Hm & Hc).
    exists N. auto.
  - destruct (pm_next Mp (presented_run Mp s0 n)) eqn:E.
    + assert (Hn : forall m, m < S n -> pm_next Mp (presented_run Mp s0 m) <> None).
      { intros m Hm. apply (cmpz_not_halted_before Mp s0 n); [rewrite E; discriminate | lia]. }
      destruct (cg_guest_matching_points Mp pc s0 (S n) Hn)
        as (N & _ & _ & _ & _ & Hd & Hm & Hc).
      exists N. auto.
    + destruct IH as [N [Hd [Hm Hc]]]. exists N.
      rewrite (cmpz_presented_run_halted Mp s0 n E), (cmpz_mledger_halted Mp s0 n E),
              (cmpz_surcharge_halted Mp s0 n E), (cmpz_mlatch_halted Mp s0 n E).
      auto.
Qed.

Lemma cmpz_pres_halted_iff : forall x : ds_state (cmpz_ds_pres Mp),
  ds_halted (cmpz_ds_pres Mp) x <-> pm_next Mp (fst (fst x)) = None.
Proof.
  intros [[s l] b]. unfold ds_halted. cbn [ds_next cmpz_ds_pres fst snd].
  destruct (pm_next Mp s); split; intro H; try reflexivity; discriminate.
Qed.

Lemma cmpz_pres_rec : forall n,
  ds_rec (cmpz_ds_pres Mp) (ds_run (cmpz_ds_pres Mp) n (cmpz_pres_start Mp s0)) = mlatch Mp s0 n.
Proof.
  intro n. unfold cmpz_pres_start.
  rewrite (cmpz_pres_run Mp n s0 0 (rd s0)) by (destruct (rd s0); reflexivity).
  cbn [ds_rec cmpz_ds_pres snd]. destruct (rd s0) eqn:H0.
  - symmetry. exact (cmpz_mlatch_rd Mp s0 n H0).
  - reflexivity.
Qed.

Lemma cmpz_pres_led : forall n,
  ds_led (cmpz_ds_pres Mp) (ds_run (cmpz_ds_pres Mp) n (cmpz_pres_start Mp s0)) = mledger Mp s0 n.
Proof.
  intro n. unfold cmpz_pres_start.
  rewrite (cmpz_pres_run Mp n s0 0 (rd s0)) by (destruct (rd s0); reflexivity).
  cbn [ds_led cmpz_ds_pres fst snd]. reflexivity.
Qed.

Lemma cmpz_pres_state : forall n,
  fst (fst (ds_run (cmpz_ds_pres Mp) n (cmpz_pres_start Mp s0))) = presented_run Mp s0 n.
Proof.
  intro n. unfold cmpz_pres_start.
  rewrite (cmpz_pres_run Mp n s0 0 (rd s0)) by (destruct (rd s0); reflexivity).
  reflexivity.
Qed.

Theorem cmpz_compile_link : forall lo hi,
  (forall n, mlatch Mp s0 n = true -> lo <= surcharge Mp s0 n /\ surcharge Mp s0 n <= hi) ->
  cmpz_link (cmpz_ds_pres Mp) (cmpz_ds_guest Q) (cmpz_pres_start Mp s0) cmpz_gstart lo hi
    cmpz_rel_compile.
Proof.
  intros lo hi Hb. split.
  - intro n. destruct (cmpz_compile_points n) as [N [Hd [Hm Hc]]].
    exists N, (surcharge Mp s0 n).
    rewrite cmpz_guest_run_eq.
    split; [unfold cmpz_rel_compile; rewrite cmpz_pres_state; exact Hd |].
    split; [cbn [ds_rec cmpz_ds_guest]; rewrite Hc, cmpz_pres_rec; reflexivity |].
    split; [cbn [ds_led cmpz_ds_guest]; rewrite Hm, cmpz_pres_led; lia |].
    rewrite cmpz_pres_rec. split.
    + intro Hl. unfold surcharge. rewrite Hl. reflexivity.
    + exact (Hb n).
  - destruct (cg_guest_halting_iff Mp pc s0) as [F B]. split.
    + intros [n Hn]. apply cmpz_pres_halted_iff in Hn. rewrite cmpz_pres_state in Hn.
      destruct (B (ex_intro _ n Hn)) as [N HN]. exists N.
      rewrite cmpz_guest_run_eq. apply cmpz_guest_halted_iff. exact HN.
    + intros [N HN]. rewrite cmpz_guest_run_eq in HN. apply cmpz_guest_halted_iff in HN.
      destruct (F (ex_intro _ N HN)) as [n Hn]. exists n.
      apply cmpz_pres_halted_iff. rewrite cmpz_pres_state. exact Hn.
  - destruct (cg_guest_flag_iff Mp pc s0) as [F B]. split.
    + intros [N HN]. rewrite cmpz_guest_run_eq in HN.
      destruct (F (ex_intro _ N HN)) as [n Hn]. exists n.
      rewrite cmpz_pres_rec. apply presented_mlatch_iff. exists n. split; [lia | exact Hn].
    + intros [n Hn]. rewrite cmpz_pres_rec in Hn. apply presented_mlatch_iff in Hn.
      destruct Hn as [m [_ Hm]].
      destruct (B (ex_intro _ m Hm)) as [N HN]. exists N.
      rewrite cmpz_guest_run_eq. exact HN.
Qed.

End Compile.

(** * The composite: a presented machine run by U_P, a tower of two links *)

Section HostLink.

Variable Mp : presented_machine.
Variable pc : cg_presentation Mp.
Variable s0 : T.cs_state (pm_sys Mp).

Local Notation rd := (T.cs_cert (pm_sys Mp)).
Local Notation ccost := (T.cs_cost (pm_sys Mp)).

Definition cmpz_rel_host : ds_state (cmpz_ds_pres Mp) -> ds_state cmpz_ds_host -> Prop :=
  cmpz_rel_comp (cmpz_rel_compile Mp pc)
    (fun (g : ds_state (cmpz_ds_guest (cg_guest Mp pc))) (h : ds_state cmpz_ds_host) =>
       pu_rel (cg_guest Mp pc) g h \/ pu_rel_halt (cg_guest Mp pc) g h).

Theorem cmpz_host_link : forall lo hi,
  (forall n, mlatch Mp s0 n = true -> lo <= surcharge Mp s0 n /\ surcharge Mp s0 n <= hi) ->
  cmpz_link (cmpz_ds_pres Mp) cmpz_ds_host (cmpz_pres_start Mp s0) (pu_host_start Mp pc s0)
    lo hi cmpz_rel_host.
Proof.
  intros lo hi Hb.
  pose proof (cmpz_link_compose (cmpz_compile_link Mp pc s0 lo hi Hb)
                (cmpz_priced_link (cg_guest Mp pc) 0 (pu_guest_b Mp pc s0))) as L.
  refine (cmpz_link_weaken L _ _); lia.
Qed.

(** From a start where the reading is no: surcharge at most 2. *)
Theorem cmpz_host_link_le_two : rd s0 = false ->
  cmpz_link (cmpz_ds_pres Mp) cmpz_ds_host (cmpz_pres_start Mp s0) (pu_host_start Mp pc s0)
    0 2 cmpz_rel_host.
Proof.
  intro H0. apply cmpz_host_link. intros n _. split; [lia |].
  exact (presented_surcharge_le_two Mp s0 n H0).
Qed.

(** When every move the machine takes costs at most 1: exactly 2. *)
Theorem cmpz_host_link_exact : rd s0 = false ->
  (forall m i, pm_next Mp (presented_run Mp s0 m) = Some i -> ccost i <= 1) ->
  cmpz_link (cmpz_ds_pres Mp) cmpz_ds_host (cmpz_pres_start Mp s0) (pu_host_start Mp pc s0)
    2 2 cmpz_rel_host.
Proof.
  intros H0 Hc. apply cmpz_host_link. intros n Hl.
  assert (Hs : surcharge Mp s0 n = 2).
  { apply cmpz_surcharge_exact_two; [exact H0 | | exact Hl].
    intros m i _ Hm. exact (Hc m i Hm). }
  split; lia.
Qed.

(** A reading that is already yes at the start costs 3. *)
Theorem cmpz_host_link_start_up : rd s0 = true ->
  cmpz_link (cmpz_ds_pres Mp) cmpz_ds_host (cmpz_pres_start Mp s0) (pu_host_start Mp pc s0)
    3 3 cmpz_rel_host.
Proof.
  intro H0. apply cmpz_host_link. intros n Hl.
  rewrite (cmpz_surcharge_start_up Mp s0 n H0). split; lia.
Qed.

End HostLink.

(** * Towers of any depth, given the machine that presents the host *)

(** A presented machine presents a driven system when a map from the system
    onto the machine's driven system carries the run to the run, the record
    bit to the latch, the ledger to the ledger and halting to halting. *)
Definition cmpz_presents_by (Mp : presented_machine) (s0 : T.cs_state (pm_sys Mp))
    (D : cmpz_ds) (d0 : ds_state D) (f : ds_state D -> ds_state (cmpz_ds_pres Mp)) : Prop :=
  (forall n, f (ds_run D n d0) = ds_run (cmpz_ds_pres Mp) n (cmpz_pres_start Mp s0)) /\
  (forall d, ds_rec (cmpz_ds_pres Mp) (f d) = ds_rec D d) /\
  (forall d, ds_led (cmpz_ds_pres Mp) (f d) = ds_led D d) /\
  (forall d, ds_halted (cmpz_ds_pres Mp) (f d) <-> ds_halted D d).

(** A presentation is a link that costs nothing. *)
Theorem cmpz_presents_link : forall Mp s0 D d0 f,
  cmpz_presents_by Mp s0 D d0 f ->
  cmpz_link D (cmpz_ds_pres Mp) d0 (cmpz_pres_start Mp s0) 0 0 (fun d x => f d = x).
Proof.
  intros Mp s0 D d0 f (H1 & H2 & H3 & H4). split.
  - intro n. exists n, 0. split; [exact (H1 n) |].
    split; [rewrite <- (H1 n), H2; reflexivity |].
    split; [rewrite <- (H1 n), H3; lia |].
    split; [intros _; reflexivity | intros _; split; lia].
  - split; intros [n Hn]; exists n.
    + rewrite <- (H1 n). apply H4. exact Hn.
    + apply H4. rewrite (H1 n). exact Hn.
  - split; intros [n Hn]; exists n.
    + rewrite <- (H1 n) in Hn. rewrite H2 in Hn. exact Hn.
    + rewrite <- (H1 n). rewrite H2. exact Hn.
Qed.

(** A host that starts at no and whose every instruction costs at most 1. *)
Lemma cmpz_host_cost_le_one : forall (i : @M.pu_instr pu_hprop), M.pu_cost i <= 1.
Proof. intro i. destruct i; simpl; lia. Qed.

Theorem cmpz_presents_host_start : forall Mp s0 d0 f,
  cmpz_presents_by Mp s0 cmpz_ds_host d0 f -> M.cert d0 = false ->
  T.cs_cert (pm_sys Mp) s0 = false.
Proof.
  intros Mp s0 d0 f (H1 & H2 & _) H0.
  pose proof (H2 d0) as E. pose proof (H1 0) as E0. simpl in E0. rewrite E0 in E.
  unfold cmpz_pres_start in E. cbn [ds_rec cmpz_ds_pres snd] in E.
  cbn [ds_rec cmpz_ds_host] in E. rewrite H0 in E. exact E.
Qed.

Theorem cmpz_presents_host_cost : forall Mp s0 d0 f,
  cmpz_presents_by Mp s0 cmpz_ds_host d0 f ->
  forall m j, pm_next Mp (presented_run Mp s0 m) = Some j ->
    T.cs_cost (pm_sys Mp) j <= 1.
Proof.
  intros Mp s0 d0 f (H1 & H2 & H3 & H4) m j Hj.
  assert (Lm : M.mu (ds_run cmpz_ds_host m d0) = mledger Mp s0 m).
  { pose proof (H3 (ds_run cmpz_ds_host m d0)) as E. rewrite (H1 m) in E.
    rewrite (cmpz_pres_led Mp s0 m) in E. cbn [ds_led cmpz_ds_host] in E. symmetry. exact E. }
  assert (Lsm : M.mu (ds_run cmpz_ds_host (S m) d0) = mledger Mp s0 (S m)).
  { pose proof (H3 (ds_run cmpz_ds_host (S m) d0)) as E. rewrite (H1 (S m)) in E.
    rewrite (cmpz_pres_led Mp s0 (S m)) in E. cbn [ds_led cmpz_ds_host] in E. symmetry. exact E. }
  rewrite mledger_succ, Hj in Lsm.
  replace (S m) with (m + 1) in Lsm by lia. rewrite ds_run_add in Lsm.
  set (h := ds_run cmpz_ds_host m d0) in *.
  cbn [ds_run ds_next cmpz_ds_host] in Lsm.
  destruct (M.pu_next_instr U_P (M.core_of h)) as [i |] eqn:E.
  - cbn in Lsm. unfold M.pu_exec in Lsm. cbn in Lsm.
    pose proof (cmpz_host_cost_le_one i). lia.
  - cbn in Lsm. lia.
Qed.

Section TowerPresented.

Variable Mp : nat -> presented_machine.
Variable pc : forall i, cg_presentation (Mp i).
Variable s0 : forall i, T.cs_state (pm_sys (Mp i)).
Variable f : forall i, ds_state cmpz_ds_host -> ds_state (cmpz_ds_pres (Mp (S i))).
Variable lo hi : nat -> nat.

(** Level i+1 presents the host run of level i. *)
Hypothesis Hpres : forall i,
  cmpz_presents_by (Mp (S i)) (s0 (S i)) cmpz_ds_host (pu_host_start (Mp i) (pc i) (s0 i)) (f i).

(** The bounds on the surcharge of each level's own run. *)
Hypothesis Hb : forall i n, mlatch (Mp i) (s0 i) n = true ->
  lo i <= surcharge (Mp i) (s0 i) n /\ surcharge (Mp i) (s0 i) n <= hi i.

Local Notation Rel i :=
  (cmpz_rel_comp (cmpz_rel_host (Mp i) (pc i)) (fun h x => f i h = x)).

Lemma cmpz_level_link : forall i,
  cmpz_link (cmpz_ds_pres (Mp i)) (cmpz_ds_pres (Mp (S i)))
    (cmpz_pres_start (Mp i) (s0 i)) (cmpz_pres_start (Mp (S i)) (s0 (S i)))
    (lo i) (hi i) (Rel i).
Proof.
  intro i.
  pose proof (cmpz_link_compose (cmpz_host_link (Mp i) (pc i) (s0 i) (lo i) (hi i) (Hb i))
                (cmpz_presents_link _ _ _ _ _ (Hpres i))) as Lk.
  refine (cmpz_link_weaken Lk _ _); lia.
Qed.

(** A tower of k nested runs, each level the host run of the one below, keeps
    the record bit exactly, adds nothing while it is down, and once it is up
    adds between the sum of the lower bounds and the sum of the upper
    bounds. *)
Theorem cmpz_tower_presented : forall k,
  cmpz_link (cmpz_ds_pres (Mp 0)) (cmpz_ds_pres (Mp k))
    (cmpz_pres_start (Mp 0) (s0 0)) (cmpz_pres_start (Mp k) (s0 k))
    (cmpz_sum lo k) (cmpz_sum hi k)
    (cmpz_tower_rel (fun i => cmpz_ds_pres (Mp i)) (fun i => Rel i) k).
Proof.
  intro k.
  exact (cmpz_tower (fun i => cmpz_ds_pres (Mp i)) (fun i => cmpz_pres_start (Mp i) (s0 i))
           lo hi (fun i => Rel i) cmpz_level_link k).
Qed.

End TowerPresented.

(** In the exact case every level above the first is a presented machine
    whose moves are the host's, which cost at most 1, so each of those levels
    pays exactly 2. *)
Section TowerExact.

Variable Mp : nat -> presented_machine.
Variable pc : forall i, cg_presentation (Mp i).
Variable s0 : forall i, T.cs_state (pm_sys (Mp i)).
Variable f : forall i, ds_state cmpz_ds_host -> ds_state (cmpz_ds_pres (Mp (S i))).
Variable lo0 hi0 : nat.

Hypothesis Hpres : forall i,
  cmpz_presents_by (Mp (S i)) (s0 (S i)) cmpz_ds_host (pu_host_start (Mp i) (pc i) (s0 i)) (f i).
Hypothesis H0 : forall n, mlatch (Mp 0) (s0 0) n = true ->
  lo0 <= surcharge (Mp 0) (s0 0) n /\ surcharge (Mp 0) (s0 0) n <= hi0.

Definition cmpz_exact_lo (i : nat) : nat := match i with 0 => lo0 | _ => 2 end.
Definition cmpz_exact_hi (i : nat) : nat := match i with 0 => hi0 | _ => 2 end.

Lemma cmpz_exact_sum : forall (c : nat -> nat) (c0 : nat),
  (forall i, c (S i) = 2) -> c 0 = c0 -> forall k, cmpz_sum c (S k) = c0 + 2 * k.
Proof.
  intros c c0 H1 H2 k. induction k as [| k IH]; simpl.
  - rewrite H2. lia.
  - rewrite H1. simpl in IH. lia.
Qed.

Theorem cmpz_tower_presented_exact : forall k,
  cmpz_link (cmpz_ds_pres (Mp 0)) (cmpz_ds_pres (Mp (S k)))
    (cmpz_pres_start (Mp 0) (s0 0)) (cmpz_pres_start (Mp (S k)) (s0 (S k)))
    (lo0 + 2 * k) (hi0 + 2 * k)
    (cmpz_tower_rel (fun i => cmpz_ds_pres (Mp i))
       (fun i => cmpz_rel_comp (cmpz_rel_host (Mp i) (pc i)) (fun h x => f i h = x)) (S k)).
Proof.
  intro k.
  assert (Hb : forall i n, mlatch (Mp i) (s0 i) n = true ->
            cmpz_exact_lo i <= surcharge (Mp i) (s0 i) n /\
            surcharge (Mp i) (s0 i) n <= cmpz_exact_hi i).
  { intros [| i] n Hl.
    - exact (H0 n Hl).
    - assert (Hs : surcharge (Mp (S i)) (s0 (S i)) n = 2).
      { apply cmpz_surcharge_exact_two; [| | exact Hl].
        - apply (cmpz_presents_host_start (Mp (S i)) (s0 (S i)) _ (f i) (Hpres i)). reflexivity.
        - intros m j _ Hj. exact (cmpz_presents_host_cost _ _ _ _ (Hpres i) m j Hj). }
      simpl. lia. }
  pose proof (cmpz_tower_presented Mp pc s0 f cmpz_exact_lo cmpz_exact_hi Hpres Hb (S k)) as T.
  rewrite (cmpz_exact_sum cmpz_exact_lo lo0 (fun i => eq_refl) eq_refl k) in T.
  rewrite (cmpz_exact_sum cmpz_exact_hi hi0 (fun i => eq_refl) eq_refl k) in T.
  exact T.
Qed.

End TowerExact.

Print Assumptions cmpz_compile_link.
Print Assumptions cmpz_host_link.
Print Assumptions cmpz_host_link_le_two.
Print Assumptions cmpz_host_link_exact.
Print Assumptions cmpz_host_link_start_up.
Print Assumptions cmpz_presents_link.
Print Assumptions cmpz_presents_host_cost.
Print Assumptions cmpz_tower_presented.
Print Assumptions cmpz_tower_presented_exact.
