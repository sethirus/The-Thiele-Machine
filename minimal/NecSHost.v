(** NecSHost.v: the host of "The host runs any guest" (UniversalThiele.v)
    pushed to its limit.

    - The host must be untrapped for GSTEP to run the guest.
    - The stored program U need not start at line 1: it keeps pace with its
      guest from line 1, from line 2, and from line 3 when counter A is
      positive, and from nowhere else; that condition is exact.
    - The mirror's agreement is needed: a disagreeing mirror can stay wrong
      forever.
    - The host's step collects the guest's toll only when it is untrapped,
      and the ledger inequality is attained (equality on a whole
      certifying run) and can be strict.
    - The two "rises only by" theorems are in fact "if and only if".
    - The guestless converse fails: a GSTEP can leave guest and mirror
      alone.
    - The earned mirror needs the loaded (clean) guest start.
    - The host toll's bound 1 is attained.                               *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedCore.
Require Import Minimal.UniversalThiele.
Module E := Minimal.EarnedCore.

Definition nec_s_trapped_hcore : E.core := E.mkcore 0 0 0 0 1 [] None true.

(* ================================================================= *)
(* 1. The host runs any guest: the untrapped hypothesis.              *)
(* ================================================================= *)

Definition nec_s_trapped_host : hstate :=
  mkh nec_s_trapped_hcore 0 false [E.INC E.CA] (E.start 0 0) false.

Theorem nec_s_universal_needs_untrapped :
  ~ (forall n h, gst (hrun (repeat (GSTEP 1) n) h) = E.run_prog n (gprog h) (gst h)).
Proof.
  intro H. pose proof (H 1 nec_s_trapped_host) as H1. vm_compute in H1. discriminate.
Qed.

(* ================================================================= *)
(* 2. The phase of U: exact condition for keeping pace.               *)
(* ================================================================= *)

Definition nec_s_phase (h : hstate) : Prop :=
  E.pc (hcore h) = 1 \/ E.pc (hcore h) = 2 \/ (E.pc (hcore h) = 3 /\ 0 < E.ca (hcore h)).

Lemma nec_s_U_round_phase : forall h,
  E.err (hcore h) = false -> nec_s_phase h ->
  nec_s_phase (hrun_prog 3 U h) /\ E.err (hcore (hrun_prog 3 U h)) = false /\
  gst (hrun_prog 3 U h) = E.step (gprog h) (gst h) /\
  gprog (hrun_prog 3 U h) = gprog h.
Proof.
  intros [[ca cb va vb pc fs ch er] m c P g r] He Hp. simpl in He. subst er.
  unfold nec_s_phase in *. simpl in Hp.
  destruct Hp as [-> | [-> | [-> Hca]]].
  - cbn. rewrite gnext_one. auto.
  - cbn. rewrite gnext_one. auto.
  - destruct ca as [| ca]; [lia |]. cbn. rewrite gnext_one.
    split; [right; right; split; [reflexivity | simpl; lia] |]. auto.
Qed.

Theorem nec_s_U_any_phase : forall n h,
  E.err (hcore h) = false -> nec_s_phase h ->
  gst (hrun_prog (3 * n) U h) = E.run_prog n (gprog h) (gst h).
Proof.
  induction n as [| n IH]; intros h He Hp; [reflexivity |].
  replace (3 * S n) with (3 + 3 * n) by lia. rewrite hrun_prog_add.
  destruct (nec_s_U_round_phase h He Hp) as [Hp' [He' [Hg Hq]]].
  rewrite (IH _ He' Hp'), Hg, Hq. reflexivity.
Qed.

(* The repository's line-1 theorem is the first case. *)
Corollary nec_s_U_line_one : forall n h,
  E.pc (hcore h) = 1 -> E.err (hcore h) = false ->
  gst (hrun_prog (3 * n) U h) = E.run_prog n (gprog h) (gst h).
Proof. intros n h Hp He. apply nec_s_U_any_phase; [exact He | left; exact Hp]. Qed.

(* Outside the phase condition U halts before its first GSTEP, so a guest
   that would move does not. *)
Lemma nec_s_U_off_phase_stuck : forall h,
  E.err (hcore h) = false -> ~ nec_s_phase h ->
  gst (hrun_prog 3 U h) = gst h.
Proof.
  intros [[ca cb va vb pc fs ch er] m c P g r] He Hp. simpl in He. subst er.
  unfold nec_s_phase in Hp. simpl in Hp.
  destruct pc as [| [| [| [| pc]]]].
  - reflexivity.
  - exfalso. apply Hp. left. reflexivity.
  - exfalso. apply Hp. right. left. reflexivity.
  - destruct ca as [| ca]; [reflexivity |].
    exfalso. apply Hp. right. right. split; [reflexivity | lia].
  - destruct pc; reflexivity.
Qed.

Lemma nec_s_phase_dec : forall h, nec_s_phase h \/ ~ nec_s_phase h.
Proof.
  intro h. unfold nec_s_phase.
  destruct (Nat.eq_dec (E.pc (hcore h)) 1) as [H1 | H1]; [left; auto |].
  destruct (Nat.eq_dec (E.pc (hcore h)) 2) as [H2 | H2]; [left; auto |].
  destruct (Nat.eq_dec (E.pc (hcore h)) 3) as [H3 | H3].
  - destruct (lt_dec 0 (E.ca (hcore h))) as [H | H]; [left; auto |].
    right. intros [H' | [H' | [_ H']]]; [congruence | congruence | lia].
  - right. intros [H' | [H' | [H' _]]]; congruence.
Qed.

Theorem nec_s_U_phase_iff : forall h,
  E.err (hcore h) = false -> gprog h = [E.INC E.CA] -> gst h = E.start 0 0 ->
  ((forall n, gst (hrun_prog (3 * n) U h) = E.run_prog n (gprog h) (gst h)) <->
   nec_s_phase h).
Proof.
  intros h He HP Hg. split.
  - intro H. destruct (nec_s_phase_dec h) as [Hp | Hp]; [exact Hp |].
    exfalso. pose proof (H 1) as H1. change (3 * 1) with 3 in H1.
    rewrite (nec_s_U_off_phase_stuck h He Hp), HP, Hg in H1.
    vm_compute in H1. discriminate.
  - intros Hp n. apply nec_s_U_any_phase; assumption.
Qed.

(* ================================================================= *)
(* 3. The mirror: agreement is needed, and can fail for good.         *)
(* ================================================================= *)

Lemma nec_s_hexec_guest_cert : forall h i,
  E.cert (gst h) = true -> E.cert (gst (hexec h i)) = true.
Proof.
  intros h [j | b] H; simpl; [exact H |].
  destruct (E.err (hcore h)); simpl; [exact H |].
  unfold gnext. destruct (gmove (gprog h) (gst h) b); [| exact H].
  apply E.cert_permanent. exact H.
Qed.

(* A mirror that is down while the guest's flag is up stays wrong after
   every host trace. *)
Theorem nec_s_disagreement_persists : forall tr h,
  mrec h = false -> E.cert (gst h) = true ->
  mrec (hrun tr h) = false /\ E.cert (gst (hrun tr h)) = true.
Proof.
  induction tr as [| i tr IH]; intros h H0 H1; simpl; [auto |].
  apply IH; [| apply nec_s_hexec_guest_cert; exact H1].
  destruct i as [j | b]; simpl; [exact H0 |].
  destruct (E.err (hcore h)); simpl; [exact H0 |].
  unfold crossing. rewrite H0, H1. reflexivity.
Qed.

Definition nec_s_wrong_mirror : hstate :=
  mkh (E.start_core 0 0) 0 false [] (E.mkst (E.start_core 0 0) 0 true) false.

Theorem nec_s_mirror_needs_agreement :
  ~ agrees nec_s_wrong_mirror /\
  (forall tr, ~ agrees (hrun tr nec_s_wrong_mirror)).
Proof.
  split; [unfold agrees; simpl; discriminate |].
  intros tr Ha. destruct (nec_s_disagreement_persists tr nec_s_wrong_mirror eq_refl eq_refl)
    as [H0 H1]. unfold agrees in Ha. congruence.
Qed.

(* The simulated record needs the host untrapped. *)
Definition nec_s_trapped_demo : hstate :=
  mkh nec_s_trapped_hcore 0 false demo_guest (E.start 0 0) false.

Theorem nec_s_simulated_record_needs_untrapped :
  agrees nec_s_trapped_demo /\
  mrec (hrun (repeat (GSTEP 1) 3) nec_s_trapped_demo) = false /\
  E.cert (E.run_prog 3 (gprog nec_s_trapped_demo) (gst nec_s_trapped_demo)) = true.
Proof. vm_compute. auto. Qed.

(* ================================================================= *)
(* 4. The host toll.                                                  *)
(* ================================================================= *)

(* Untrapped is needed: a trapped host whose guest stands at a passing
   CERTIFY does not raise its mirror. *)
Definition nec_s_trapped_at_certify : hstate :=
  mkh nec_s_trapped_hcore 0 false demo_guest (E.run_prog 2 demo_guest (E.start 0 0)) false.

Theorem nec_s_host_toll_needs_untrapped :
  agrees nec_s_trapped_at_certify /\
  crossing (gst nec_s_trapped_at_certify)
           (gnext (gprog nec_s_trapped_at_certify) (gst nec_s_trapped_at_certify) 1) = true /\
  mrec (hexec nec_s_trapped_at_certify (GSTEP 1)) = false.
Proof. vm_compute. auto. Qed.

(* The ledger inequality is attained with equality on the whole demo run,
   and is strict on a GSTEP that runs a free guest instruction. *)
Theorem nec_s_host_cost_cover_tight :
  (let tr := repeat (GSTEP 1) 3 in
   E.mu (gst (hrun tr demo_host)) + hmu demo_host = hmu (hrun tr demo_host) + E.mu (gst demo_host)
   /\ mrec (hrun tr demo_host) = true) /\
  (let h := hload 0 0 [E.INC E.CA] 0 0 in
   E.mu (gst (hexec h (GSTEP 1))) + hmu h < hmu (hexec h (GSTEP 1)) + E.mu (gst h)).
Proof. vm_compute. split; [auto | lia]. Qed.

(* The bound "costs at least 1" of the host toll is attained. *)
Theorem nec_s_host_toll_attained :
  let h := hrun (repeat (GSTEP 1) 2) demo_host in
  hread h = false /\ hread (hexec h (GSTEP 1)) = true /\ hcost (GSTEP 1) = 1.
Proof. vm_compute. auto. Qed.

(* ================================================================= *)
(* 5. "Only by" is "exactly when".                                    *)
(* ================================================================= *)

Theorem nec_s_mirror_rise_iff : forall h i,
  mrec h = false ->
  (mrec (hexec h i) = true <->
   exists b, i = GSTEP b /\ E.err (hcore h) = false /\
             crossing (gst h) (gnext (gprog h) (gst h) b) = true).
Proof.
  intros h i H0. split.
  - intro H1. destruct i as [j | b]; simpl in H1; [congruence |].
    destruct (E.err (hcore h)) eqn:He; simpl in H1; [congruence |].
    rewrite H0 in H1. exists b. auto.
  - intros [b [-> [He Hx]]]. simpl. rewrite He. simpl. rewrite Hx. apply orb_true_r.
Qed.

Theorem nec_s_own_rise_iff : forall h i,
  hcert h = false ->
  (hcert (hexec h i) = true <-> i = OWN E.CERTIFY /\ E.certify_ok (hcore h) = true).
Proof.
  intros h i H0. split; [apply own_record_only_by_certify; exact H0 |].
  intros [-> Hok]. simpl. rewrite H0, Hok. reflexivity.
Qed.

(* The converse of the guestless theorem fails: a trace with a GSTEP can
   leave the guest and the mirror where they were. *)
Theorem nec_s_guestless_converse_false :
  gst (hrun [GSTEP 1] nec_s_trapped_host) = gst nec_s_trapped_host /\
  mrec (hrun [GSTEP 1] nec_s_trapped_host) = mrec nec_s_trapped_host /\
  ~ (forall i, In i [GSTEP 1] -> exists j, i = OWN j).
Proof.
  split; [reflexivity |]. split; [reflexivity |].
  intro H. destruct (H (GSTEP 1) (or_introl eq_refl)) as [j Hj]. discriminate.
Qed.

(* ================================================================= *)
(* 6. The earned mirror needs the loaded clean guest.                 *)
(* ================================================================= *)

Theorem nec_s_mirror_earned_needs_load :
  let h := mkh (E.start_core 0 0) 0 false [] (E.mkst (E.start_core 0 0) 0 true) true in
  agrees h /\ mrec (hrun [] h) = true /\
  forall n, E.trace_of n (gprog h) (gst h) = [].
Proof.
  intro h. split; [reflexivity |]. split; [reflexivity |].
  intros [| n]; reflexivity.
Qed.

Print Assumptions nec_s_universal_needs_untrapped.
Print Assumptions nec_s_U_any_phase.
Print Assumptions nec_s_U_phase_iff.
Print Assumptions nec_s_disagreement_persists.
Print Assumptions nec_s_mirror_needs_agreement.
Print Assumptions nec_s_simulated_record_needs_untrapped.
Print Assumptions nec_s_host_toll_needs_untrapped.
Print Assumptions nec_s_host_cost_cover_tight.
Print Assumptions nec_s_host_toll_attained.
Print Assumptions nec_s_mirror_rise_iff.
Print Assumptions nec_s_own_rise_iff.
Print Assumptions nec_s_guestless_converse_false.
Print Assumptions nec_s_mirror_earned_needs_load.
