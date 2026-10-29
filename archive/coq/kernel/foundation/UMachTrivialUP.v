(** UMachTrivialUP.v: the "trivial-claim" variant of U_P.

    V = U_P with every CHECK p r and COMMIT p r retargeted to one register
    TR = 100, which U_P never mentions (U_P's registers are 0..80), on the
    same host machine (EarnedMultiPriced over PSlot, U_P's checker), from
    U_P's load with TR preset to CV = 1, a value PSlot holds of
    (pu_heval PSlot 1 = true).  So every CHECK and COMMIT of V is on the
    same constant claim, true of every guest.

    Why V still runs every computably presented machine: on U_P's class
    the compiled guest never traps (guest_noerr), so U_P never traps
    (UP_noerr), so every CHECK and COMMIT that U_P executes passes; V's
    retargeted ones pass at exactly the same times (lockstep: same
    registers except TR, same versions, line, trap, number of facts,
    channel emptiness, ledger and flag).

      V_meets_strong   V meets UMachDef.universal_thiele (in order, K = 3).
      V_meets_d        the host is a register host (UP_host_RH) and V's
                       load is clean and given by a fixed formula.
      V_fails_c        every CHECK and COMMIT of V is on TR, TR holds the
                       constant 1 at every time of every run, and every
                       rise of V's flag stands on CHECK p TR, COMMIT p TR,
                       CERTIFY in V's own trace; and V's flag does rise
                       (on PresentedDemo's machine).  So no flag rise of V
                       stands on a check of the guest's justification.

    Note what this shows about U_P: its own CHECKs never fail on its class,
    because the compiled guest only checks once it has computed that the
    claim holds.                                                           *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.UMachPresented.
Require Import Kernel.UMachMeetsUP.
Require Import Kernel.UMachRegHost.
Require Import Kernel.UMachInOrderUP.
Require Import Kernel.UniversalPCodes.
Require Import Kernel.UniversalPBridge.
Require Import Kernel.UniversalPLayout.
Require Import Kernel.UniversalPPhases.
Require Import Kernel.UniversalPSim.
Require Import Kernel.UniversalPRun.
Require Import Kernel.PresentedUniversal.
Require Import Kernel.CompilerGuest.
Require Import Kernel.CompilerGuestRun.
Require Import Kernel.CompilerChecker.
Require Import Minimal.Presented.
Require Import Kernel.Presentation.
Require Kernel.PresentedDemo.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.

Local Notation hstate := (@M.pu_state pu_hprop).
Local Notation hcore := (@M.pu_core pu_hprop).
Local Notation hinstr := (@M.pu_instr pu_hprop).
Local Notation run := (M.pu_run_prog pu_hprop_eqb pu_heval).

Definition TR : nat := 100.
Definition CV : nat := 1.

Lemma CV_true : pu_heval PSlot CV = true.
Proof. vm_compute. reflexivity. Qed.

Definition mentions (i : hinstr) : nat :=
  match i with M.INC r => r | M.DEC r _ => r | M.CHECK _ r => r | M.COMMIT _ r => r | _ => 0 end.

Lemma U_P_avoids : forallb (fun i => negb (Nat.eqb (mentions i) TR)) U_P = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fetch_avoids : forall n i, M.pu_fetch U_P n = Some i -> mentions i <> TR.
Proof.
  intros [| n] i H; [discriminate |]. simpl in H. apply nth_error_In in H.
  pose proof U_P_avoids as A. rewrite forallb_forall in A. specialize (A i H).
  apply negb_true_iff, Nat.eqb_neq in A. exact A.
Qed.

Definition retarget (i : hinstr) : hinstr :=
  match i with M.CHECK p _ => M.CHECK p TR | M.COMMIT p _ => M.COMMIT p TR | _ => i end.

Definition V : list hinstr := map retarget U_P.

Lemma fetch_map : forall (f : hinstr -> hinstr) l n, M.pu_fetch (map f l) n = option_map f (M.pu_fetch l n).
Proof. intros f l [| n]; [reflexivity |]. simpl. apply nth_error_map. Qed.

Lemma next_V : forall k k', M.err k' = M.err k -> M.pc k' = M.pc k ->
  M.pu_next_instr V k' = option_map retarget (M.pu_next_instr U_P k).
Proof.
  intros k k' He Hp. unfold M.pu_next_instr. rewrite He, Hp.
  destruct (M.err k); [reflexivity |]. unfold V. rewrite fetch_map.
  destruct (M.pu_fetch U_P (M.pc k)) as [[] |]; reflexivity.
Qed.

(* ================================================================= *)
(* Lockstep.                                                          *)
(* ================================================================= *)

Definition TF : @M.pu_fact pu_hprop := M.mkfact PSlot TR 0.

Definition Rlc (k k' : hcore) : Prop :=
  (forall r, r <> TR -> M.vals k' r = M.vals k r) /\ M.vals k' TR = CV /\
  (forall r, M.vers k' r = M.vers k r) /\ M.vers k TR = 0 /\
  M.pc k' = M.pc k /\ M.err k' = M.err k /\
  M.facts k' = repeat TF (length (M.facts k)) /\
  (M.chan k = None <-> M.chan k' = None).

Definition Rl (s s' : hstate) : Prop :=
  Rlc (M.core_of s) (M.core_of s') /\ M.mu s' = M.mu s /\ M.cert s' = M.cert s.

Lemma upd_ne : forall (f : nat -> nat) r v x, x <> r -> M.pu_upd f r v x = f x.
Proof. intros f r v x H. unfold M.pu_upd. apply Nat.eqb_neq in H. rewrite H. reflexivity. Qed.

Lemma Rlc_write : forall k k' r n j, Rlc k k' -> r <> TR ->
  Rlc (M.pu_write k r n j) (M.pu_write k' r n j).
Proof.
  intros k k' r n j (V1 & V2 & W1 & W2 & P1 & E1 & F1 & C1) Hr.
  assert (Ht : Nat.eqb TR r = false) by (apply Nat.eqb_neq; congruence).
  unfold Rlc, M.pu_write. simpl.
  split. { intros x Hx. unfold M.pu_upd. destruct (Nat.eqb x r); [reflexivity | apply V1, Hx]. }
  split. { unfold M.pu_upd. rewrite Ht. exact V2. }
  split. { intros x. unfold M.pu_upd. rewrite !W1. reflexivity. }
  split. { unfold M.pu_upd. rewrite Ht. exact W2. }
  split; [reflexivity |]. split; [exact E1 |]. split; [exact F1 | exact C1].
Qed.

Lemma Rlc_goto : forall k k' j, Rlc k k' -> Rlc (M.pu_goto k j) (M.pu_goto k' j).
Proof. intros k k' j (V1 & V2 & W1 & W2 & P1 & E1 & F1 & C1). unfold M.pu_goto. repeat split; simpl; auto; apply C1. Qed.

Lemma step_lock : forall k k' i, Rlc k k' -> M.err k = false -> mentions i <> TR ->
  M.err (M.pu_cexec pu_hprop_eqb pu_heval k i) = false ->
  Rlc (M.pu_cexec pu_hprop_eqb pu_heval k i) (M.pu_cexec pu_hprop_eqb pu_heval k' (retarget i)) /\
  M.pu_fires k i = M.pu_fires k' (retarget i).
Proof.
  intros k k' i R He Hm Hn. pose proof R as (V1 & V2 & W1 & W2 & P1 & E1 & F1 & C1).
  unfold M.pu_cexec in *. rewrite He in Hn. rewrite E1, He.
  destruct i as [r | r j | | p r | p r | |]; simpl in Hm |- *.
  - split; [| reflexivity]. rewrite (V1 r Hm), P1. apply Rlc_write; assumption.
  - split; [| reflexivity]. rewrite (V1 r Hm). destruct (M.vals k r) as [| n].
    + rewrite P1. apply Rlc_goto, R.
    + apply Rlc_write; assumption.
  - split; [exact R | reflexivity].
  - (* CHECK: the original passes, so the retargeted one passes *)
    destruct (M.pu_check_ok pu_heval k p r) eqn:Ck; [| simpl in Hn; discriminate].
    assert (Ck' : M.pu_check_ok pu_heval k' p TR = true).
    { unfold M.pu_check_ok in *. rewrite E1, He, V2, F1, repeat_length. destruct p.
      rewrite CV_true. simpl. apply andb_true_iff in Ck as [_ Ck]. exact Ck. }
    rewrite Ck'. split; [| reflexivity].
    unfold M.pu_record_fact, M.pu_claim. repeat split; simpl; auto.
    + rewrite F1. destruct p. unfold TF. rewrite W1, W2. reflexivity.
    + apply C1.
    + apply C1.
  - (* COMMIT *)
    destruct (M.pu_commit_ok pu_hprop_eqb k p r) eqn:Cm; [| simpl in Hn; discriminate].
    assert (Hne : M.facts k <> []).
    { intros X. unfold M.pu_commit_ok in Cm. rewrite X in Cm. simpl in Cm.
      rewrite andb_false_r in Cm. discriminate. }
    assert (Cm' : M.pu_commit_ok pu_hprop_eqb k' p TR = true).
    { unfold M.pu_commit_ok. rewrite E1, He, F1. simpl.
      destruct (M.facts k) as [| f fs]; [contradiction |]. simpl.
      unfold M.pu_claim. rewrite W1, W2. destruct p. unfold TF.
      rewrite (proj2 (M.pu_multi_fact_eqb_eq pu_hprop_eqb pu_hprop_eqb_eq _ _) eq_refl). reflexivity. }
    rewrite Cm'. split; [| reflexivity].
    unfold M.pu_commit_to. repeat split; simpl; auto; discriminate.
  - (* CERTIFY *)
    assert (Co : M.pu_certify_ok k' = M.pu_certify_ok k).
    { unfold M.pu_certify_ok. rewrite E1. destruct (M.chan k) eqn:Ch.
      - destruct (M.chan k') eqn:Ch'; [reflexivity |]. exfalso.
        pose proof (proj2 C1 eq_refl) as X. discriminate X.
      - pose proof (proj1 C1 eq_refl) as X. rewrite X. reflexivity. }
    rewrite Co. destruct (M.pu_certify_ok k) eqn:Ok; [| simpl in Hn; discriminate].
    split; [rewrite P1; apply Rlc_goto, R | simpl; rewrite ?Co, ?Ok; reflexivity].
  - split; [rewrite P1; apply Rlc_goto, R | reflexivity].
Qed.

Lemma cost_retarget : forall i, M.pu_cost (retarget i) = M.pu_cost i.
Proof. intros []; reflexivity. Qed.

Theorem lockstep : forall n s s', Rl s s' ->
  (forall t, M.err (M.core_of (run t U_P s)) = false) ->
  Rl (run n U_P s) (run n V s').
Proof.
  induction n as [| n IH]; intros s s' R Hn; [exact R |].
  change (run (S n) U_P s) with (run n U_P (M.pu_step pu_hprop_eqb pu_heval U_P s)).
  change (run (S n) V s') with (run n V (M.pu_step pu_hprop_eqb pu_heval V s')).
  apply IH.
  - destruct R as [Rc [Hmu Hc]]. pose proof Rc as (V1 & V2 & W1 & W2 & P1 & E1 & F1 & C1).
    unfold M.pu_step. rewrite (next_V _ _ E1 P1).
    destruct (M.pu_next_instr U_P (M.core_of s)) as [i |] eqn:Ni; simpl; [| split; auto].
    assert (He : M.err (M.core_of s) = false).
    { unfold M.pu_next_instr in Ni. destruct (M.err (M.core_of s)); [discriminate | reflexivity]. }
    assert (Hm : mentions i <> TR).
    { apply (fetch_avoids (M.pc (M.core_of s))). unfold M.pu_next_instr in Ni. rewrite He in Ni.
      destruct (M.pu_fetch U_P (M.pc (M.core_of s))) as [[] |]; congruence. }
    assert (Hn1 : M.err (M.pu_cexec pu_hprop_eqb pu_heval (M.core_of s) i) = false).
    { specialize (Hn 1). simpl in Hn. unfold M.pu_step in Hn. rewrite Ni in Hn. exact Hn. }
    destruct (step_lock _ _ i Rc He Hm Hn1) as [Rc' Hf].
    split; [exact Rc' |]. simpl. rewrite cost_retarget, Hmu, Hc, Hf. split; reflexivity.
  - intros t. specialize (Hn (S t)). exact Hn.
Qed.

(* ================================================================= *)
(* On U_P's class, the guest never traps and U_P never traps.         *)
(* ================================================================= *)

Section Class.
Variable Mp : presented_machine.
Variable pc : cg_presentation Mp.
Variable s0 : T.cs_state (pm_sys Mp).

Local Notation Q := (cg_guest Mp pc).
Local Notation b := (pu_guest_b Mp pc s0).

Lemma guest_noerr : forall N, E.err (E.core_of (pu_grun Q 0 b N)) = false.
Proof.
  intros N. destruct (cg_cover Mp pc s0 N) as (N' & n & x & HN & _ & Hsim).
  assert (E' : E.err (E.core_of (pu_grun Q 0 b N')) = false).
  { destruct x as [e a]. destruct Hsim as (_ & _ & _ & _ & _ & H6 & _). exact H6. }
  destruct (E.err (E.core_of (pu_grun Q 0 b N))) eqn:E; [| reflexivity].
  exfalso. assert (Hh : E.halted Q (E.core_of (pu_grun Q 0 b N))) by (apply pu_ghalted_trap, E).
  assert (St : pu_grun Q 0 b N' = pu_grun Q 0 b N).
  { unfold pu_grun. apply cg_run_prog_stay; [exact Hh | exact HN]. }
  rewrite St, E in E'. discriminate.
Qed.

Lemma UP_noerr : forall t, herr (pu_hrun Q 0 b t) = false.
Proof.
  intros t.
  assert (Stay : forall a c, a <= c -> herr (pu_hrun Q 0 b a) = true -> herr (pu_hrun Q 0 b c) = true).
  { intros a c Hac Ha. unfold pu_hrun in *.
    rewrite (pu_hhalted_stay a c _ Hac); [exact Ha |]. apply M.pu_multi_trapped_halted, Ha. }
  destruct (pu_sim_points Q 0 b t) as (N & sg & rho & [[R Hle] | RH] & _).
  - destruct (pu_rw_head _ _ _ _ _ R) as (_ & HeN & _).
    destruct (herr (pu_hrun Q 0 b t)) eqn:E; [| reflexivity].
    rewrite (Stay t N Hle E) in HeN. discriminate.
  - destruct RH as (_ & Hh & _ & _ & He & _).
    rewrite (guest_noerr t) in He.
    destruct (le_lt_dec t N) as [Hle | Hlt].
    + destruct (herr (pu_hrun Q 0 b t)) eqn:E; [| reflexivity].
      rewrite (Stay t N Hle E) in He. discriminate.
    + unfold pu_hrun in *. rewrite (pu_hhalted_stay N t _ ltac:(lia) Hh). exact He.
Qed.

Definition vload : hstate :=
  M.pu_start (fun r => if Nat.eqb r TR then CV else pu_hregs Q 0 b r).

Lemma pu_hregs_TR : pu_hregs Q 0 b TR = 0.
Proof. reflexivity. Qed.

Lemma load_rel : Rl (pu_host_start Mp pc s0) vload.
Proof.
  unfold pu_host_start, pu_hload, vload, M.pu_start, M.pu_start_core.
  split; [| split; reflexivity]. repeat split; simpl; auto.
  intros r Hr. apply Nat.eqb_neq in Hr. rewrite Hr. reflexivity.
Qed.

Theorem V_lock : forall t, Rl (pu_host_at Mp pc s0 t) (run t V vload).
Proof.
  intros t. unfold pu_host_at, pu_hrun. apply lockstep; [exact load_rel |].
  intros t'. exact (UP_noerr t').
Qed.

End Class.

(* ================================================================= *)
(* V meets clauses (1)-(3), in order, K = 3.                          *)
(* ================================================================= *)

Theorem V_meets_strong :
  universal_thiele presented_class UP_host
    (fun i => option (T.cs_state (pm_sys (projT1 i)))) pobs 3.
Proof.
  exists V, (fun i => vload (projT1 i) (fst (projT2 i)) (snd (projT2 i))),
         (fun i h => pu_decode (projT1 i) (hv h pu_RB)).
  intros [Mp [pc s0]]. simpl fst; simpl snd; simpl projT1.
  destruct (UP_meets_strong) as (P0 & ld & dc & _). clear P0 ld dc.
  assert (Halt : forall t, hnext UP_host V (hr (H:=UP_host) V (vload Mp pc s0) t) = None <->
                           M.pu_halted U_P (M.core_of (pu_host_at Mp pc s0 t))).
  { intros t. simpl. rewrite UP_hr. destruct (V_lock Mp pc s0 t) as [(V1 & V2 & W1 & W2 & P1 & E1 & _) _].
    rewrite (next_V _ _ E1 P1). unfold M.pu_halted.
    destruct (M.pu_next_instr U_P _); simpl; split; congruence. }
  split; [| split].
  - unfold clause1. split.
    + intros [n Hn]. apply Halt in Hn.
      destruct (proj1 (presented_universal_halting Mp pc s0) (ex_intro _ n Hn)) as [m Hm].
      exists m. unfold UMachDef.grun. simpl. rewrite pgr. exact Hm.
    + intros [m Hm]. unfold UMachDef.grun in Hm. simpl in Hm.
      rewrite (pgr (existT _ Mp (pc, s0))) in Hm.
      destruct (proj2 (presented_universal_halting Mp pc s0) (ex_intro _ m Hm)) as [n Hn].
      exists n. apply Halt. exact Hn.
  - destruct (UP_in_order Mp pc s0) as (f & Hinc & Hpts).
    exists f. split; [intros m _; apply Hinc |].
    intros m Hl.
    assert (Hl' : forall k, k < m -> pm_next Mp (presented_run Mp s0 k) <> None).
    { intros k Hk. pose proof (Hl k Hk) as X. unfold UMachDef.grun in X. simpl in X.
      rewrite (pgr (existT _ Mp (pc, s0))) in X. exact X. }
    destruct (Hpts m Hl') as (Hd & Hmu & Hc).
    destruct (V_lock Mp pc s0 (f m)) as [(V1 & _) [Lmu Lc]].
    unfold match_at. simpl hP in *. rewrite UP_hr.
    pose proof (UP_hl V (f m) (vload Mp pc s0)) as Hh.
    split; [| split].
    + simpl. rewrite (V1 pu_RB) by (unfold pu_RB, TR; lia). rewrite Hd. unfold pobs, UMachDef.grun. simpl.
      rewrite (pgr (existT _ Mp (pc, s0))). reflexivity.
    + simpl. rewrite Lc, Hc. symmetry. apply (pglat (existT _ Mp (pc, s0))).
    + exists (surcharge Mp s0 m). split.
      * unfold surcharge. destruct (mlatch Mp s0 m); lia.
      * unfold gledger. simpl gstart. rewrite (pgl (existT _ Mp (pc, s0))).
        assert (H0 : M.mu (vload Mp pc s0) = 0) by reflexivity. simpl in *. lia.
  - intros n. apply clause3_free.
Qed.

(* ================================================================= *)
(* (d): register host, clean load.                                    *)
(* ================================================================= *)

Theorem V_meets_d : inhabited (reg_host UP_host) /\
  forall Mp pc s0, M.pu_clean_start (vload Mp pc s0) /\ M.mu (vload Mp pc s0) = 0.
Proof.
  split; [constructor; exact UP_host_RH |]. intros. split; [apply M.pu_multi_start_clean | reflexivity].
Qed.

(* ================================================================= *)
(* (c) fails: every flag rise stands on the constant claim on TR.     *)
(* ================================================================= *)

Lemma V_record_on_TR : forall n i, M.pu_fetch V n = Some i ->
  (forall p r, i = M.CHECK p r -> r = TR) /\ (forall p r, i = M.COMMIT p r -> r = TR).
Proof.
  intros n i H. unfold V in H. rewrite fetch_map in H.
  destruct (M.pu_fetch U_P n) as [j |]; [| discriminate]. simpl in H. injection H as <-.
  destruct j; simpl; split; intros p' r' E; inversion E; reflexivity.
Qed.

Lemma trace_from_prog : forall n P s i, In i (M.pu_trace_of pu_hprop_eqb pu_heval n P s) ->
  exists m, M.pu_fetch P m = Some i.
Proof.
  induction n as [| n IH]; intros P s i H; simpl in H; [contradiction |].
  destruct (M.pu_next_instr P (M.core_of s)) as [j |] eqn:N; [| contradiction].
  destruct H as [<- | H]; [| exact (IH _ _ _ H)].
  unfold M.pu_next_instr in N. destruct (M.err (M.core_of s)); [discriminate |].
  exists (M.pc (M.core_of s)). destruct (M.pu_fetch P (M.pc (M.core_of s))) as [[] |]; congruence.
Qed.

Theorem V_TR_const : forall Mp pc s0 t, hv (run t V (vload Mp pc s0)) TR = CV.
Proof. intros. destruct (V_lock Mp pc s0 t) as [(_ & V2 & _) _]. exact V2. Qed.

Theorem V_flag_chain : forall Mp pc s0 t,
  M.cert (run t V (vload Mp pc s0)) = true ->
  exists pre1 p mid1 mid2 post,
    M.pu_trace_of pu_hprop_eqb pu_heval t V (vload Mp pc s0) =
      pre1 ++ M.CHECK p TR :: mid1 ++ M.COMMIT p TR :: mid2 ++ M.CERTIFY :: post.
Proof.
  intros Mp pc s0 t Hc.
  set (tr := M.pu_trace_of pu_hprop_eqb pu_heval t V (vload Mp pc s0)).
  assert (Hc' : M.cert (M.pu_run pu_hprop_eqb pu_heval tr (vload Mp pc s0)) = true).
  { unfold tr. rewrite <- M.pu_multi_run_prog_trace. exact Hc. }
  destruct (pu_host_chain_holds (vload Mp pc s0) tr (M.pu_multi_start_clean _) Hc')
    as (pre & c & chk & mid1 & cmt & mid2 & crt & post & Htr & Kk & Km & Kc & Ck & _).
  destruct c as [[p r] |]; [| simpl in Ck; discriminate].
  destruct chk; simpl in Kk; try discriminate. inversion Kk; subst.
  destruct cmt; simpl in Km; try discriminate. inversion Km; subst.
  destruct crt; simpl in Kc; try discriminate.
  repeat match goal with q : pu_hprop |- _ => destruct q end.
  assert (Hin : In (M.CHECK PSlot r) tr) by (rewrite Htr; apply in_or_app; right; left; reflexivity).
  destruct (trace_from_prog _ _ _ _ Hin) as [m Hm].
  pose proof (proj1 (V_record_on_TR m _ Hm) PSlot r eq_refl) as ->.
  exists pre, PSlot, mid1, mid2, post. exact Htr.
Qed.

(* V's flag does rise: on PresentedDemo's machine from state 0. *)
Theorem V_flag_rises :
  exists t, M.cert (run t V (vload PresentedDemo.pu_demo PresentedDemo.pu_demo_pc 0)) = true.
Proof.
  destruct PresentedDemo.pu_demo_flag_rises as [t Ht]. exists t.
  destruct (V_lock PresentedDemo.pu_demo PresentedDemo.pu_demo_pc 0 t) as [_ [_ Hc]].
  rewrite Hc. exact Ht.
Qed.

Print Assumptions guest_noerr.
Print Assumptions UP_noerr.
Print Assumptions V_lock.
Print Assumptions V_meets_strong.
Print Assumptions V_meets_d.
Print Assumptions V_TR_const.
Print Assumptions V_flag_chain.
Print Assumptions V_flag_rises.
