(** UMachHybrid.v: the hybrid host (U's host machine + three price-0 moves that
    fetch, decode and execute a guest instruction), and more generally ANY
    extension of U's host machine (EarnedMulti over PSlot) by extra moves
    of price 0 that only write registers (each write bumps the register's
    version) and leave the fact table, channel, trap, ledger and flag alone.

    1. ext_thiele_complete / ext_thiele_complete_over: every such extension
       is Thiele-complete (minimal/ThieleComplete.v), over the same claim
       language as U's host.  hybrid_thiele_complete is the instance.

    2. ext_not_reg_host: an extension with a price-0 extra move that, at a
       live state at line 1 and at a live state at line 3, turns one
       register from 0 to positive and another from positive to 0 in one
       move, is not a register host (UMachRegHost.reg_host), under ANY choice of
       line, registers and trap bit.  No trap is used: the argument goes
       through the host's own INC 0 and DEC r 100, whose zero tests tie the
       register view to the real registers.  hybrid_not_reg_host is the
       instance (GOP on a guest INC A turns OPR 0 -> 1 and CR 1 -> 0).    *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.UMachRegHost.
Require Import Minimal.UniversalCodes.
Require Import Kernel.UniversalBridge.
Require Import Kernel.UniversalLayout.
Require Import Kernel.UniversalRun.
Require Minimal.ThieleComplete.
Module TC := Minimal.ThieleComplete.

Local Notation core := (@M.core hprop).
Local Notation state := (@M.state hprop).
Local Notation instr := (@M.instr hprop).

(* ================================================================= *)
(* Register-only core maps.                                           *)
(* ================================================================= *)

Definition grows (k k' : core) : Prop :=
  M.facts k' = M.facts k /\ M.chan k' = M.chan k /\ M.err k' = M.err k /\
  (forall r, M.vers k r <= M.vers k' r) /\
  (forall r, M.vers k' r = M.vers k r -> M.vals k' r = M.vals k r).

Lemma grows_refl : forall k, grows k k.
Proof. intros k. repeat split; intros; lia || reflexivity. Qed.

Lemma grows_trans : forall k1 k2 k3, grows k1 k2 -> grows k2 k3 -> grows k1 k3.
Proof.
  intros k1 k2 k3 (F1 & C1 & E1 & V1 & W1) (F2 & C2 & E2 & V2 & W2).
  split; [congruence |]. split; [congruence |]. split; [congruence |].
  split; [intros r; specialize (V1 r); specialize (V2 r); lia |].
  intros r H. assert (A : M.vers k2 r = M.vers k1 r) by (specialize (V1 r); specialize (V2 r); lia).
  rewrite W2 by congruence. apply W1, A.
Qed.

Definition wr (k : core) (r v : nat) : core := M.write k r v (M.pc k).
Definition step_pc (k : core) : core := M.goto k (S (M.pc k)).

Lemma grows_wr : forall k r v, grows k (wr k r v).
Proof.
  intros k r v. unfold wr, M.write, M.upd. repeat split; simpl.
  - intros x. destruct (Nat.eqb_spec x r); [subst; lia | lia].
  - intros x. destruct (Nat.eqb_spec x r); [subst; lia | auto].
Qed.

Lemma grows_goto : forall k j, grows k (M.goto k j).
Proof. intros k j. unfold M.goto. repeat split; simpl; intros; lia || reflexivity. Qed.

(* ================================================================= *)
(* The extension of U's host machine by extra moves.                  *)
(* ================================================================= *)

Section Ext.
Variable X : Type.
Variable xcore : X -> core -> core.
Hypothesis xgrows : forall x k, grows k (xcore x k).

Definition emove : Type := (instr + X)%type.

Definition eexec (s : state) (m : emove) : state :=
  match m with
  | inl i => M.exec hprop_eqb heval s i
  | inr x => M.mkst (xcore x (M.core_of s)) (M.mu s) (M.cert s)
  end.

Definition ecost (m : emove) : nat := match m with inl i => M.cost i | inr _ => 0 end.

Definition emachine : TC.machine := TC.mk_machine state emove eexec ecost (@M.cert hprop).

(* One step: what can change. *)
Lemma estep_facts : forall s m,
  M.facts (M.core_of (eexec s m)) = M.facts (M.core_of s) \/
  exists p r, m = inl (M.CHECK p r) /\ M.check_ok heval (M.core_of s) p r = true /\
    M.facts (M.core_of (eexec s m)) = M.claim (M.core_of s) p r :: M.facts (M.core_of s).
Proof.
  intros [k mu c] [i | x]; simpl; [| left; apply xgrows].
  unfold M.cexec. destruct (M.err k); [left; reflexivity |].
  destruct i as [r | r j | | p r | p r |]; simpl; try (left; reflexivity).
  - destruct (M.vals k r); left; reflexivity.
  - destruct (M.check_ok heval k p r) eqn:E; [right; exists p, r; auto | left; reflexivity].
  - destruct (M.commit_ok hprop_eqb k p r); left; reflexivity.
  - destruct (M.certify_ok k); left; reflexivity.
Qed.

Lemma estep_chan : forall s m,
  M.chan (M.core_of (eexec s m)) = M.chan (M.core_of s) \/
  exists p r, m = inl (M.COMMIT p r) /\ M.commit_ok hprop_eqb (M.core_of s) p r = true /\
    M.chan (M.core_of (eexec s m)) = Some (M.claim (M.core_of s) p r).
Proof.
  intros [k mu c] [i | x]; simpl; [| left; apply xgrows].
  unfold M.cexec. destruct (M.err k); [left; reflexivity |].
  destruct i as [r | r j | | p r | p r |]; simpl; try (left; reflexivity).
  - destruct (M.vals k r); left; reflexivity.
  - destruct (M.check_ok heval k p r); left; reflexivity.
  - destruct (M.commit_ok hprop_eqb k p r) eqn:E; [right; exists p, r; auto | left; reflexivity].
  - destruct (M.certify_ok k); left; reflexivity.
Qed.

Lemma estep_grows_regs : forall s m,
  (forall r, M.vers (M.core_of s) r <= M.vers (M.core_of (eexec s m)) r) /\
  (forall r, M.vers (M.core_of (eexec s m)) r = M.vers (M.core_of s) r ->
             M.vals (M.core_of (eexec s m)) r = M.vals (M.core_of s) r).
Proof.
  intros [k mu c] [i | x]; simpl; [| destruct (xgrows x k) as (_ & _ & _ & V & W); auto].
  unfold M.cexec. destruct (M.err k); [split; intros; lia || reflexivity |].
  destruct i as [r | r j | | p r | p r |]; simpl.
  - apply (grows_wr k r (S (M.vals k r))).
  - destruct (M.vals k r) as [| n]; [apply (grows_goto k) | apply (grows_wr k r n)].
  - split; intros; lia || reflexivity.
  - destruct (M.check_ok heval k p r); simpl; split; intros; lia || reflexivity.
  - destruct (M.commit_ok hprop_eqb k p r); simpl; split; intros; lia || reflexivity.
  - destruct (M.certify_ok k); simpl; split; intros; lia || reflexivity.
Qed.

Lemma estep_cert : forall s m,
  M.cert (eexec s m) = true -> M.cert s = false ->
  m = inl M.CERTIFY /\ M.certify_ok (M.core_of s) = true.
Proof.
  intros [k mu c] [i | x] H1 H0; simpl in *; [| congruence].
  subst c. simpl in H1. destruct i; simpl in H1; try discriminate. auto.
Qed.

Local Notation run := (TC.run emachine).

Lemma run_snoc : forall l m s, run (l ++ [m]) s = eexec (run l s) m.
Proof. intros l m s. rewrite TC.run_app. reflexivity. Qed.

Lemma run_vers_mono : forall l s r, M.vers (M.core_of s) r <= M.vers (M.core_of (run l s)) r.
Proof.
  induction l as [| m l IH]; intros s r; simpl; [lia |].
  pose proof (proj1 (estep_grows_regs s m) r). specialize (IH (eexec s m) r). lia.
Qed.

Lemma run_same_val : forall l s r,
  M.vers (M.core_of (run l s)) r = M.vers (M.core_of s) r ->
  M.vals (M.core_of (run l s)) r = M.vals (M.core_of s) r.
Proof.
  induction l as [| m l IH]; intros s r H; simpl in *; [reflexivity |].
  destruct (estep_grows_regs s m) as [V W].
  pose proof (V r). pose proof (run_vers_mono l (eexec s m) r).
  rewrite IH by lia. apply W. lia.
Qed.

Lemma cert_first : forall tr s0, M.cert s0 = false -> M.cert (run tr s0) = true ->
  exists pre post, tr = pre ++ inl M.CERTIFY :: post /\ M.cert (run pre s0) = false /\
    M.certify_ok (M.core_of (run pre s0)) = true.
Proof.
  induction tr as [| m tr IH] using rev_ind; intros s0 H0 H1; [simpl in H1; congruence |].
  rewrite run_snoc in H1. destruct (M.cert (run tr s0)) eqn:E.
  - destruct (IH s0 H0 E) as (pre & post & -> & A & B).
    exists pre, (post ++ [m]). split; [rewrite <- app_assoc; reflexivity | auto].
  - destruct (estep_cert _ _ H1 E) as [-> Hok]. exists tr, []. auto.
Qed.

Lemma chan_origin : forall l s0 f, M.chan (M.core_of s0) = None ->
  M.chan (M.core_of (run l s0)) = Some f ->
  exists l1 p r l2, l = l1 ++ inl (M.COMMIT p r) :: l2 /\
    M.commit_ok hprop_eqb (M.core_of (run l1 s0)) p r = true /\
    f = M.claim (M.core_of (run l1 s0)) p r.
Proof.
  induction l as [| m l IH] using rev_ind; intros s0 f H0 H1; [simpl in H1; congruence |].
  rewrite run_snoc in H1. destruct (estep_chan (run l s0) m) as [E | (p & r & -> & Hok & E)].
  - rewrite E in H1. destruct (IH s0 f H0 H1) as (l1 & p & r & l2 & -> & A & B).
    exists l1, p, r, (l2 ++ [m]). split; [rewrite <- app_assoc; reflexivity | auto].
  - rewrite E in H1. injection H1 as <-. exists l, p, r, []. auto.
Qed.

Lemma fact_origin : forall l s0 f, M.facts (M.core_of s0) = [] ->
  In f (M.facts (M.core_of (run l s0))) ->
  exists l1 p r l2, l = l1 ++ inl (M.CHECK p r) :: l2 /\
    M.check_ok heval (M.core_of (run l1 s0)) p r = true /\
    f = M.claim (M.core_of (run l1 s0)) p r.
Proof.
  induction l as [| m l IH] using rev_ind; intros s0 f H0 H1; [simpl in H1; rewrite H0 in H1; contradiction |].
  rewrite run_snoc in H1. destruct (estep_facts (run l s0) m) as [E | (p & r & -> & Hok & E)].
  - rewrite E in H1. destruct (IH s0 f H0 H1) as (l1 & p & r & l2 & -> & A & B).
    exists l1, p, r, (l2 ++ [m]). split; [rewrite <- app_assoc; reflexivity | auto].
  - rewrite E in H1. destruct H1 as [<- | Hin].
    + exists l, p, r, []. auto.
    + destruct (IH s0 f H0 Hin) as (l1 & p' & r' & l2 & -> & A & B).
      exists l1, p', r', (l2 ++ [inl (M.CHECK p r)]). split; [rewrite <- app_assoc; reflexivity | auto].
Qed.

(* ---------------------------------------------------------------- *)
(* The interface: U's host interface, the extra moves read as base.  *)
(* ---------------------------------------------------------------- *)

Lemma ehost_sim : forall (s : state) i, herr s = false ->
  host_window (eexec s (inl (host_compile i))) = TC.cm_exec i (host_window s) /\
  herr (eexec s (inl (host_compile i))) = false.
Proof. intros s i H. exact (host_sim s i H). Qed.

Definition ebase : TC.universal_base emachine :=
  TC.mk_ub emachine host_window (fun s => herr s = false) (fun i => inl (host_compile i)) host_load
    (fun a b => eq_refl) (fun a b => eq_refl) ehost_sim.

Definition ekind (m : emove) : TC.kind (hprop * nat) :=
  match m with inl i => host_kind i | inr _ => TC.KBase end.

Definition emeaning (pr : hprop * nat) (s : state) : Prop := hholds (fst pr) (hv s (snd pr)).
Definition echeck (s : state) (pr : hprop * nat) : bool := M.check_ok heval (M.core_of s) (fst pr) (snd pr).
Definition esame (pr : hprop * nat) (s t : state) : Prop :=
  hver s (snd pr) = hver t (snd pr) /\ hv s (snd pr) = hv t (snd pr).

Definition eI : TC.thiele_interface emachine :=
  TC.mk_ti emachine ebase (hprop * nat) ekind emeaning echeck esame M.clean_start (@M.mu hprop).

Lemma commit_in_facts : forall k p r, M.commit_ok hprop_eqb k p r = true ->
  In (M.claim k p r) (M.facts k).
Proof.
  intros k p r H. unfold M.commit_ok in H. apply andb_true_iff in H as [_ H].
  apply existsb_exists in H as [g [Hin Hg]].
  apply (M.multi_fact_eqb_eq hprop_eqb hprop_eqb_eq) in Hg. subst. exact Hin.
Qed.

Lemma ext_chain : forall s0 tr, M.clean_start s0 -> M.cert (run tr s0) = true ->
  TC.earned_chain eI s0 tr.
Proof.
  intros s0 tr (Hf0 & Hc0 & Hr0) H1.
  destruct (cert_first tr s0 Hr0 H1) as (pre & post & -> & Hpre & Hok).
  assert (Hch : exists f, M.chan (M.core_of (run pre s0)) = Some f).
  { unfold M.certify_ok in Hok. apply andb_true_iff in Hok as [_ Hok].
    destruct (M.chan (M.core_of (run pre s0))) as [f |]; [exists f; reflexivity | discriminate]. }
  destruct Hch as [f Hf].
  destruct (chan_origin pre s0 f Hc0 Hf) as (l1 & p & r & mid2 & -> & Hcm & Hfeq).
  pose proof (commit_in_facts _ _ _ Hcm) as Hin.
  destruct (fact_origin l1 s0 _ Hf0 Hin) as (pre1 & p' & r' & mid1 & -> & Hck & Heq).
  unfold M.claim in Heq.
  assert (Hp : p' = p) by congruence. assert (Hr : r' = r) by congruence. subst p' r'.
  assert (Hv : M.vers (M.core_of (run (pre1 ++ inl (M.CHECK p r) :: mid1) s0)) r =
               M.vers (M.core_of (run pre1 s0)) r) by congruence.
  exists pre1, (p, r), (inl (M.CHECK p r)), mid1, (inl (M.COMMIT p r)), mid2,
    (inl M.CERTIFY), post.
  split; [rewrite <- !app_assoc; reflexivity |].
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [exact Hck |].
  split.
  - intros t1 t2 Hm. subst mid1. unfold esame. simpl snd.
    assert (A : M.vers (M.core_of (run pre1 s0)) r <= M.vers (M.core_of (run (pre1 ++ inl (M.CHECK p r) :: t1) s0)) r).
    { rewrite TC.run_app. apply run_vers_mono. }
    assert (B : M.vers (M.core_of (run (pre1 ++ inl (M.CHECK p r) :: t1) s0)) r <=
                M.vers (M.core_of (run (pre1 ++ inl (M.CHECK p r) :: t1 ++ t2) s0)) r).
    { replace (pre1 ++ inl (M.CHECK p r) :: t1 ++ t2) with ((pre1 ++ inl (M.CHECK p r) :: t1) ++ t2)
        by (rewrite <- app_assoc; reflexivity).
      rewrite (TC.run_app emachine _ t2). apply run_vers_mono. }
    assert (Eq : M.vers (M.core_of (run (pre1 ++ inl (M.CHECK p r) :: t1) s0)) r =
                 M.vers (M.core_of (run pre1 s0)) r) by lia.
    split; [symmetry; exact Eq |].
    symmetry. rewrite TC.run_app. apply run_same_val. rewrite TC.run_app in Eq. exact Eq.
  - split.
    + rewrite <- app_assoc in Hpre. exact Hpre.
    + change (M.cert (run (pre1 ++ inl (M.CHECK p r) :: mid1 ++ inl (M.COMMIT p r) :: mid2 ++ [inl M.CERTIFY]) s0) = true).
      replace (pre1 ++ inl (M.CHECK p r) :: mid1 ++ inl (M.COMMIT p r) :: mid2 ++ [inl M.CERTIFY])
        with (((pre1 ++ inl (M.CHECK p r) :: mid1) ++ inl (M.COMMIT p r) :: mid2) ++ [inl M.CERTIFY])
        by (rewrite <- !app_assoc; reflexivity).
      rewrite run_snoc. simpl. rewrite Hok. apply orb_true_r.
Qed.

Theorem ext_thiele_complete_with : TC.thiele_complete_with eI.
Proof.
  split; [| split; [| split]].
  - split; [intros [[|] | [|] j]; reflexivity |].
    split; [intros a b; apply M.multi_start_clean |]. split.
    + intros s [i | x] Hk; simpl; [| reflexivity].
      destruct i; simpl in Hk; try discriminate; simpl; apply orb_false_r.
    + intros s [i | x] H; simpl in *; [rewrite H; reflexivity | exact H].
  - split; [intros s (_ & _ & H); exact H |]. split.
    + intros s0 tr H0 H1. apply ext_chain; assumption.
    + split.
      * intros s [p r] H. simpl in *. unfold echeck, M.check_ok in H.
        apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H].
        apply heval_iff, H.
      * intros [p r] s t [_ Hsame] H. simpl in *. unfold emeaning in *. simpl in *. rewrite <- Hsame. exact H.
  - split; [intros [[] | x]; reflexivity | intros s [i | x]; [reflexivity | simpl; lia]].
  - exists (PSlot, 0), (inl (M.CHECK PSlot 0)), (inl (M.COMMIT PSlot 0)), (inl M.CERTIFY).
    split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    split; [| split; [exists 1, 0; exact hholds_one | exists 0, 0; exact hholds_zero]].
    intros a b. unfold TC.load. simpl TC.ti_meaning. unfold emeaning.
    change (TC.run emachine [inl (M.CHECK PSlot 0); inl (M.COMMIT PSlot 0); inl M.CERTIFY]
              (host_load a b))
      with (M.run hprop_eqb heval [M.CHECK PSlot 0; M.COMMIT PSlot 0; M.CERTIFY] (host_load a b)).
    apply host_chain_iff.
Qed.

Theorem ext_thiele_complete : TC.thiele_complete emachine.
Proof. exists eI. exact ext_thiele_complete_with. Qed.

(* Over the same claim language as U's host, written before the interface. *)
Definition elanguage : TC.claim_language emachine :=
  TC.mk_cl emachine (hprop * nat) host_claim_eqb host_claim_eqb_spec emeaning esame
    (fun pr s t H => host_same_keeps pr s t H).

Definition eli : TC.lang_interface emachine elanguage :=
  TC.mk_lang emachine elanguage ebase ekind echeck (fun s pr H => host_check_sound s pr H)
    M.clean_start (@M.mu hprop).

Theorem ext_thiele_complete_over : TC.thiele_complete_over emachine elanguage.
Proof. exists eli. exact ext_thiele_complete_with. Qed.

(* ---------------------------------------------------------------- *)
(* The extension as a UMachDef host (stored programs over emove).       *)
(* ---------------------------------------------------------------- *)

Lemma etoll : forall s m, M.cert s = false -> M.cert (eexec s m) = true -> ecost m >= 1.
Proof. intros s m H0 H1. destruct (estep_cert s m H1 H0) as [-> _]. simpl. lia. Qed.

Definition enext (P : list emove) (s : state) : option emove :=
  if M.err (M.core_of s) then None else
  match M.fetch P (M.pc (M.core_of s)) with Some (inl M.HALT) => None | o => o end.

Definition ehost : host := mk_host state emove eexec ecost (@M.cert hprop) etoll (list emove) enext.

(* ================================================================= *)
(* Not a register host.                                               *)
(* ================================================================= *)

Definition live (s : state) : Prop := M.err (M.core_of s) = false /\ 1 <= M.pc (M.core_of s).

Definition I0 : emove := inl (M.INC 0).
Definition DJ (r : nat) : emove := inl (M.DEC r 100).

Lemma fetch_rep : forall p q, 1 <= q -> q <= p -> M.fetch (repeat I0 p) q = Some I0.
Proof.
  intros p q H1 H2. destruct q as [| q]; [lia |]. unfold M.fetch.
  apply nth_error_repeat. lia.
Qed.

Lemma fetch_rep_none : forall p q, p < q -> M.fetch (repeat I0 p) q = None.
Proof.
  intros p q H. destruct q as [| q]; [lia |]. unfold M.fetch.
  apply nth_error_None. rewrite repeat_length. lia.
Qed.

Section NotReg.
Variable R : reg_host ehost.

Lemma live_berr : forall s, live s -> b_err R s = false.
Proof.
  intros s [He Hp]. destruct (b_err R s) eqn:E; [| reflexivity]. exfalso.
  pose proof (b_next_err ehost R (repeat I0 (M.pc (M.core_of s))) s E) as N.
  simpl in N. unfold enext in N. rewrite He, fetch_rep in N by lia. discriminate.
Qed.

Lemma same_bpc : forall s t, live s -> live t -> b_pc R s = b_pc R t ->
  M.pc (M.core_of s) = M.pc (M.core_of t).
Proof.
  intros s t Ls Lt Hb.
  assert (N : forall P, enext P s = enext P t).
  { intros P. apply (b_next ehost R P s t); [rewrite !live_berr by assumption; reflexivity | exact Hb]. }
  destruct Ls as [Es Ps]. destruct Lt as [Et Pt].
  destruct (lt_eq_lt_dec (M.pc (M.core_of s)) (M.pc (M.core_of t))) as [[H | H] | H]; [| exact H |].
  - specialize (N (repeat I0 (M.pc (M.core_of s)))). unfold enext in N.
    rewrite Es, Et, fetch_rep, fetch_rep_none in N by lia. discriminate.
  - specialize (N (repeat I0 (M.pc (M.core_of t)))). unfold enext in N.
    rewrite Es, Et, fetch_rep_none, fetch_rep in N by lia. discriminate.
Qed.

Lemma kind0 : forall m, ecost m = 0 -> b_kind R m <> RRec.
Proof. intros m H K. pose proof (b_cost ehost R m) as C. simpl in C. rewrite K in C. simpl in H. lia. Qed.

(* The real effect of INC 0 and DEC r 100 on a live state. *)
Lemma I0_live : forall s, live s -> live (eexec s I0) /\
  M.pc (M.core_of (eexec s I0)) = S (M.pc (M.core_of s)).
Proof.
  intros [k mu c] [He Hp]. unfold live, I0. simpl in *. unfold M.cexec. rewrite He. simpl.
  split; [split; [exact He | lia] | reflexivity].
Qed.

Lemma DJ_live : forall s r, live s -> live (eexec s (DJ r)) /\
  M.pc (M.core_of (eexec s (DJ r))) =
    (if Nat.eqb (M.vals (M.core_of s) r) 0 then S (M.pc (M.core_of s)) else 100).
Proof.
  intros [k mu c] r [He Hp]. unfold live, DJ. simpl in *. unfold M.cexec. rewrite He. simpl.
  destruct (M.vals k r); simpl; (split; [split; [exact He | lia] | reflexivity]).
Qed.

Definition Srouted (s : state) : Prop := b_pc R (eexec s I0) = S (b_pc R s).

Lemma I0_route : forall s, live s ->
  Srouted s \/ exists x j, b_kind R I0 = RDec x j /\ b_reg R s x > 0 /\ b_pc R (eexec s I0) = j.
Proof.
  intros s Ls. pose proof (live_berr s Ls) as Eb. destruct (I0_live s Ls) as [Li Pi].
  destruct (b_kind R I0) as [x | x j | |] eqn:K.
  - left. destruct (b_inc ehost R s I0 x Eb K) as (_ & H & _). exact H.
  - destruct (b_dec ehost R s I0 x j Eb K) as (_ & D).
    destruct (b_reg R s x) as [| n] eqn:V.
    + left. exact (proj1 D).
    + right. exists x, j. split; [reflexivity |]. split; [lia | exact (proj1 D)].
  - exfalso. destruct (b_halt ehost R s I0 K) as (_ & H & _).
    pose proof (same_bpc _ _ Li Ls H). lia.
  - exfalso. exact (kind0 I0 eq_refl K).
Qed.

Lemma nonS_same_pc : forall s t, live s -> live t -> ~ Srouted s -> ~ Srouted t ->
  M.pc (M.core_of s) = M.pc (M.core_of t).
Proof.
  intros s t Ls Lt Ns Nt.
  destruct (I0_route s Ls) as [H | (x & j & K & _ & Hs)]; [contradiction |].
  destruct (I0_route t Lt) as [H | (x' & j' & K' & _ & Ht)]; [contradiction |].
  rewrite K in K'. injection K' as <- <-.
  destruct (I0_live s Ls) as [Li Pi]. destruct (I0_live t Lt) as [Lj Pj].
  pose proof (same_bpc _ _ Li Lj (eq_trans Hs (eq_sym Ht))). lia.
Qed.

Lemma tie : forall r u v, live u -> live v ->
  M.vals (M.core_of u) r > 0 -> M.vals (M.core_of v) r = 0 -> Srouted u ->
  M.pc (M.core_of u) <> 100 -> S (M.pc (M.core_of u)) <> 100 -> S (M.pc (M.core_of v)) <> 100 ->
  exists x j, b_kind R (DJ r) = RDec x j /\ b_reg R u x > 0 /\ b_reg R v x = 0.
Proof.
  intros r u v Lu Lv Hu Hv Su N1 N2 N3.
  destruct (DJ_live u r Lu) as [Ldu Pdu]. destruct (DJ_live v r Lv) as [Ldv Pdv].
  destruct (I0_live u Lu) as [Liu Piu].
  assert (Eu : Nat.eqb (M.vals (M.core_of u) r) 0 = false) by (apply Nat.eqb_neq; lia).
  assert (Ev : Nat.eqb (M.vals (M.core_of v) r) 0 = true) by (apply Nat.eqb_eq; lia).
  rewrite Eu in Pdu. rewrite Ev in Pdv.
  pose proof (live_berr u Lu) as Bu. pose proof (live_berr v Lv) as Bv.
  destruct (b_kind R (DJ r)) as [x | x j | |] eqn:K.
  - exfalso. destruct (b_inc ehost R u (DJ r) x Bu K) as (_ & H & _).
    unfold Srouted in Su. rewrite <- Su in H.
    pose proof (same_bpc _ _ Ldu Liu H). lia.
  - destruct (b_dec ehost R u (DJ r) x j Bu K) as (_ & Du).
    destruct (b_reg R u x) as [| n] eqn:Vu.
    + exfalso. destruct Du as [H _]. unfold Srouted in Su. rewrite <- Su in H.
      pose proof (same_bpc _ _ Ldu Liu H). lia.
    + destruct Du as [Hj _]. exists x, j. split; [reflexivity |]. split; [lia |].
      destruct (b_dec ehost R v (DJ r) x j Bv K) as (_ & Dv).
      destruct (b_reg R v x) as [| n'] eqn:Vv; [reflexivity |].
      exfalso. destruct Dv as [Hj' _]. rewrite <- Hj in Hj'.
      pose proof (same_bpc _ _ Ldv Ldu Hj'). lia.
  - exfalso. destruct (b_halt ehost R u (DJ r) K) as (_ & H & _).
    pose proof (same_bpc _ _ Ldu Lu H). lia.
  - exfalso. exact (kind0 (DJ r) eq_refl K).
Qed.

End NotReg.

Definition st (k : core) : state := M.mkst k 0 false.

(* The hypothesis on one extra move x0: at a live state at line p (p = 1
   and p = 3), it turns register a from 0 to positive and register b from
   positive to 0, and goes to line p + 1 untrapped. *)
Definition flips (x0 : X) (a b p : nat) : Prop :=
  exists k, M.err k = false /\ M.pc k = p /\ M.vals k a = 0 /\ M.vals k b > 0 /\
    M.vals (xcore x0 k) a > 0 /\ M.vals (xcore x0 k) b = 0 /\
    M.pc (xcore x0 k) = S p /\ M.err (xcore x0 k) = false.

Theorem ext_not_reg_host : forall x0 a b, flips x0 a b 1 -> flips x0 a b 3 -> reg_host ehost -> False.
Proof.
  intros x0 a b F1 F3 R.
  (* finishing argument at one line p where INC 0 is S-routed before and after x0 *)
  assert (Finish : forall p k, p = 1 \/ p = 3 ->
            M.err k = false -> M.pc k = p -> M.vals k a = 0 -> M.vals k b > 0 ->
            M.vals (xcore x0 k) a > 0 -> M.vals (xcore x0 k) b = 0 ->
            M.pc (xcore x0 k) = S p -> M.err (xcore x0 k) = false ->
            Srouted R (st k) -> Srouted R (st (xcore x0 k)) -> False).
  { intros p k Hp Ek Pk Ak Bk Ak' Bk' Pk' Ek' Su Sw.
    set (u := st k). set (w := st (xcore x0 k)).
    assert (Lu : live u) by (unfold live; simpl; split; [exact Ek | lia]).
    assert (Lw : live w) by (unfold live; simpl; split; [exact Ek' | lia]).
    destruct (tie R a w u Lw Lu Ak' Ak Sw) as (xa & ja & Ka & Wa & Ua);
      simpl; try lia.
    destruct (tie R b u w Lu Lw Bk Bk' Su) as (xb & jb & Kb & Ub & Wb);
      simpl; try lia.
    assert (Hw : hstep ehost u (inr x0) = w) by reflexivity.
    pose proof (live_berr R u Lu) as Bu.
    destruct (b_kind R (inr x0)) as [z | z j | |] eqn:K.
    - destruct (b_inc ehost R u (inr x0) z Bu K) as (_ & _ & Hr).
      rewrite Hw in Hr. specialize (Hr xb). unfold upd in Hr.
      destruct (Nat.eqb xb z); lia.
    - destruct (b_dec ehost R u (inr x0) z j Bu K) as (_ & D). rewrite Hw in D.
      destruct (b_reg R u z) as [| n] eqn:Vz.
      + destruct D as [_ Hr]. specialize (Hr xa). lia.
      + destruct D as [_ Hr]. specialize (Hr xa). unfold upd in Hr.
        destruct (Nat.eqb_spec xa z) as [-> | Hne]; lia.
    - destruct (b_halt ehost R u (inr x0) K) as (_ & _ & Hr). rewrite Hw in Hr.
      specialize (Hr xa). lia.
    - exact (kind0 R (inr x0) eq_refl K). }
  destruct F1 as (k1 & E1 & P1 & A1 & B1 & A1' & B1' & P1' & E1').
  destruct F3 as (k3 & E3 & P3 & A3 & B3 & A3' & B3' & P3' & E3').
  assert (L1 : live (st k1)) by (unfold live; simpl; split; [exact E1 | lia]).
  assert (L1' : live (st (xcore x0 k1))) by (unfold live; simpl; split; [exact E1' | lia]).
  assert (L3 : live (st k3)) by (unfold live; simpl; split; [exact E3 | lia]).
  assert (L3' : live (st (xcore x0 k3))) by (unfold live; simpl; split; [exact E3' | lia]).
  assert (Case : forall k p, M.err k = false -> M.pc k = p -> 1 <= p ->
            M.pc (xcore x0 k) = S p -> M.err (xcore x0 k) = false ->
            (Srouted R (st k) /\ Srouted R (st (xcore x0 k))) \/
            exists s, live s /\ ~ Srouted R s /\ (M.pc (M.core_of s) = p \/ M.pc (M.core_of s) = S p)).
  { intros k p Ek Pk Hp Pk' Ek'.
    destruct (Nat.eq_dec (b_pc R (eexec (st k) I0)) (S (b_pc R (st k)))) as [Sa | Na].
    - destruct (Nat.eq_dec (b_pc R (eexec (st (xcore x0 k)) I0)) (S (b_pc R (st (xcore x0 k)))))
        as [Sb | Nb].
      + left. split; assumption.
      + right. exists (st (xcore x0 k)). split; [unfold live; simpl; split; [exact Ek' | lia] |].
        split; [exact Nb | right; exact Pk'].
    - right. exists (st k). split; [unfold live; simpl; split; [exact Ek | lia] |].
      split; [exact Na | left; exact Pk]. }
  destruct (Case k1 1 E1 P1 ltac:(lia) P1' E1') as [[S1 S1'] | (s1 & Ls1 & Ns1 & Ps1)];
    [exact (Finish 1 k1 (or_introl eq_refl) E1 P1 A1 B1 A1' B1' P1' E1' S1 S1') |].
  destruct (Case k3 3 E3 P3 ltac:(lia) P3' E3') as [[S3 S3'] | (s3 & Ls3 & Ns3 & Ps3)];
    [exact (Finish 3 k3 (or_intror eq_refl) E3 P3 A3 B3 A3' B3' P3' E3' S3 S3') |].
  pose proof (nonS_same_pc R s1 s3 Ls1 Ls3 Ns1 Ns3). lia.
Qed.

End Ext.


(* ================================================================= *)
(* The hybrid's three primitives (as in universal/hybrid_model.py).   *)
(* ================================================================= *)

Definition OPR : nat := 4.
Definition CR : nat := 5.
Definition KR : nat := 7.

(* The guest instruction at line GPC of the program coded in PROG
   (None: line 0, past the end, undecodable, or HALT). *)
Definition guest_instr (k : core) : option E.instr :=
  match M.vals k GPC with
  | 0 => None
  | S l => match fetch_code (M.vals k PROG) l with
           | Some c => match idecode c with Some E.HALT => None | o => o end
           | None => None
           end
  end.

Fixpoint firstj (f : nat -> bool) (j fuel : nat) : nat :=
  match fuel with 0 => j | S fu => if f j then j else firstj f (S j) fu end.

Definition first_mp (k : core) (c : E.ctr) (p : E.prop) : nat :=
  firstj (fun j => Nat.eqb (M.vals k (MP c j)) (S (pcode p))) 0 16.

(* Nudge: value kept, version + 2; and zero the mirror if it is not 0. *)
Definition nudge1 (k : core) (r : nat) : core := wr (wr k r (S (M.vals k r))) r (M.vals k r).

Fixpoint nudge_all (c : E.ctr) (n : nat) (k : core) : core :=
  match n with
  | 0 => k
  | S j => let k1 := nudge1 (nudge_all c j k) (SLOT c j) in
           if Nat.eqb (M.vals k1 (MP c j)) 0 then k1 else wr k1 (MP c j) 0
  end.

Definition gop (k : core) : core :=
  if M.err k then k else step_pc
  match guest_instr k with
  | None | Some E.HALT => wr k OPR 0
  | Some (E.INC c) => wr (wr k OPR 1) CR (ccode c)
  | Some (E.DEC c _) => wr (wr k OPR 2) CR (ccode c)
  | Some (E.CHECK p c) =>
      let kk := M.vals k (NC c) in
      let k1 := wr (wr (wr k OPR 4) CR (ccode c)) KR kk in
      if Nat.ltb kk 16 then wr k1 (SLOT c kk) (pair (pcode p) (M.vals k (greg c))) else k1
  | Some (E.COMMIT p c) => wr (wr (wr k OPR 5) CR (ccode c)) KR (first_mp k c p)
  | Some E.CERTIFY => wr k OPR 6
  end.

Definition gbase (k : core) : core :=
  if M.err k then k else step_pc
  match guest_instr k with
  | Some (E.INC c) =>
      nudge_all c 16 (wr (wr k (greg c) (S (M.vals k (greg c)))) GPC (S (M.vals k GPC)))
  | Some (E.DEC c j) =>
      match M.vals k (greg c) with
      | 0 => wr k GPC (S (M.vals k GPC))
      | S n => nudge_all c 16 (wr (wr k (greg c) n) GPC j)
      end
  | _ => k
  end.

Definition gadv (k : core) : core :=
  if M.err k then k else step_pc
  match guest_instr k with
  | Some (E.CHECK p c) =>
      let kk := M.vals k (NC c) in
      wr (wr (wr k (MP c kk) (S (pcode p))) (NC c) (S kk)) GPC (S (M.vals k GPC))
  | _ => wr k GPC (S (M.vals k GPC))
  end.

Inductive hprim : Type := GOP | GBASE | GADV.

Definition hcore (x : hprim) : core -> core :=
  match x with GOP => gop | GBASE => gbase | GADV => gadv end.

Lemma grows_nudge1 : forall k r, grows k (nudge1 k r).
Proof. intros k r. unfold nudge1. eapply grows_trans; apply grows_wr. Qed.

Lemma grows_nudge_all : forall c n k, grows k (nudge_all c n k).
Proof.
  intros c n. induction n as [| j IH]; intros k; simpl; [apply grows_refl |].
  destruct (Nat.eqb _ 0).
  - eapply grows_trans; [apply IH | apply grows_nudge1].
  - eapply grows_trans; [apply IH |]. eapply grows_trans; [apply grows_nudge1 | apply grows_wr].
Qed.

Ltac gw := repeat (eapply grows_trans; [apply grows_wr |]); try apply grows_wr; try apply grows_refl.

Lemma hgrows : forall x k, grows k (hcore x k).
Proof.
  intros [] k; simpl.
  - unfold gop. destruct (M.err k); [apply grows_refl |].
    eapply grows_trans; [| apply grows_goto].
    destruct (guest_instr k) as [[c | c j | | p c | p c |] |].
    + eapply grows_trans; apply grows_wr.
    + eapply grows_trans; apply grows_wr.
    + apply grows_wr.
    + destruct (Nat.ltb _ 16).
      * eapply grows_trans; [| apply grows_wr]. eapply grows_trans; [| apply grows_wr].
        eapply grows_trans; apply grows_wr.
      * eapply grows_trans; [| apply grows_wr]. eapply grows_trans; apply grows_wr.
    + eapply grows_trans; [| apply grows_wr]. eapply grows_trans; apply grows_wr.
    + apply grows_wr.
    + apply grows_wr.
  - unfold gbase. destruct (M.err k); [apply grows_refl |].
    eapply grows_trans; [| apply grows_goto].
    destruct (guest_instr k) as [[c | c j | | p c | p c |] |]; try apply grows_refl.
    + eapply grows_trans; [| apply grows_nudge_all]. eapply grows_trans; apply grows_wr.
    + destruct (M.vals k (greg c)).
      * apply grows_wr.
      * eapply grows_trans; [| apply grows_nudge_all]. eapply grows_trans; apply grows_wr.
  - unfold gadv. destruct (M.err k); [apply grows_refl |].
    eapply grows_trans; [| apply grows_goto].
    destruct (guest_instr k) as [[c | c j | | p c | p c |] |]; try apply grows_wr.
    eapply grows_trans; [| apply grows_wr]. eapply grows_trans; apply grows_wr.
Qed.

(* The hybrid machine and host. *)
Definition hybrid_machine : TC.machine := emachine hprim hcore.
Definition hybrid_host : host := ehost hprim hcore.

Theorem hybrid_thiele_complete : TC.thiele_complete hybrid_machine.
Proof. exact (ext_thiele_complete hprim hcore hgrows). Qed.

Theorem hybrid_thiele_complete_over :
  TC.thiele_complete_over hybrid_machine (elanguage hprim hcore).
Proof. exact (ext_thiele_complete_over hprim hcore hgrows). Qed.

(* GOP on a guest INC A, at line p: OPR 0 -> 1, CR 1 -> 0. *)
Definition kflip (p : nat) : core :=
  M.mkcore (fun r => if Nat.eqb r PROG then prog_code [E.INC E.CA] else
                     if Nat.eqb r GPC then 1 else if Nat.eqb r CR then 1 else 0)
           (fun _ => 0) p [] None false.

Lemma hybrid_flips : forall p, flips hprim hcore GOP OPR CR p.
Proof.
  intros p. exists (kflip p). vm_compute. repeat split; lia || reflexivity.
Qed.

Theorem hybrid_not_reg_host : reg_host hybrid_host -> False.
Proof.
  exact (ext_not_reg_host hprim hcore GOP OPR CR (hybrid_flips 1) (hybrid_flips 3)).
Qed.

Print Assumptions ext_thiele_complete.
Print Assumptions ext_thiele_complete_over.
Print Assumptions ext_not_reg_host.
Print Assumptions hybrid_thiele_complete.
Print Assumptions hybrid_thiele_complete_over.
Print Assumptions hybrid_not_reg_host.
