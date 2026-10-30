(** NeutralUnivU.v: U is a neutral universal machine (all of N0-N5, IN ORDER) with
    surcharge 0 for every small-machine program from every clean start.

    The small machine is Thiele-complete, hence neutral-complete
    (NeutralUnivGstep.small_guests_nc), so this is a Turing-complete class of
    neutral-complete guests run by one fixed program on one fixed register
    host with the ledger exact.  (Each of these guests itself pays 3 to
    raise its record; the guests that raise for 1 are not in this class.)  *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.NeutralUnivBase.
Require Import Kernel.NeutralUnivDef.
Require Import Kernel.UMachCheatSmall.
Require Import Kernel.UMachMeetsU.
Require Import Minimal.UniversalCodes.
Require Import Kernel.UniversalBridge.
Require Import Kernel.UniversalLayout.
Require Import Kernel.UniversalSim.
Require Import Kernel.UniversalRun.
Require Minimal.NeutralComplete.

Definition ukind (i : @M.instr hprop) : rkind :=
  match i with M.INC r => RInc r | M.DEC r j => RDec r j | M.HALT => RHalt | _ => RRec end.

Definition U_reg : reg_host U_host.
Proof.
  refine (mk_rh U_host (fun s => M.pc (M.core_of s)) (fun s => M.vals (M.core_of s))
            (fun s => M.err (M.core_of s)) ukind _ _ _ _ _ _ _ _).
  - intros [r | r j | | p r | p r |]; reflexivity.
  - intros s m E. simpl. unfold M.cexec. rewrite E. auto.
  - intros s m r E K. destruct m; simpl in K; try discriminate. injection K as ->.
    simpl. unfold M.cexec. rewrite E. simpl. auto.
  - intros s m r j E K. destruct m; simpl in K; try discriminate. injection K as -> ->.
    simpl. unfold M.cexec. rewrite E. destruct (M.vals (M.core_of s) r); simpl; auto.
  - intros s m K. destruct m; simpl in K; try discriminate.
    simpl. unfold M.cexec. destruct (M.err (M.core_of s)) eqn:E; simpl; repeat split; auto.
  - intros s m E K. simpl. unfold M.cexec. rewrite E.
    destruct m; simpl in K; try discriminate.
    + destruct (M.check_ok heval (M.core_of s) p r); simpl; auto.
    + destruct (M.commit_ok hprop_eqb (M.core_of s) p r); simpl; auto.
    + destruct (M.certify_ok (M.core_of s)); simpl; auto.
  - intros P s1 s2 E Pc. simpl. unfold M.next_instr. rewrite E, Pc. reflexivity.
  - intros P s E. simpl. unfold M.next_instr. rewrite E. reflexivity.
Defined.

Definition U_iface : NeutralComplete.neutral_interface (hmach U_host) :=
  NeutralComplete.neutralize host_interface.

Theorem U_host_nc : host_nc U_host U_reg.
Proof.
  exists U_iface. split.
  - exact (NeutralComplete.tc_to_nc host_machine host_interface host_thiele_complete_with).
  - intros [r | r j | | p r | p r |]; reflexivity.
Qed.

Definition U_raise (l : nat) : bool := match M.fetch U l with Some M.CERTIFY => true | _ => false end.

Theorem U_line_raise : line_raise U_host U_reg U U_raise.
Proof.
  intros s m E Hn K. simpl in *. unfold M.next_instr in Hn. rewrite E in Hn.
  unfold U_raise. destruct (M.fetch U (M.pc (M.core_of s))) as [o |] eqn:F; [| discriminate].
  destruct o; try (injection Hn as <-); try discriminate; simpl in K; try discriminate.
  - right. simpl. rewrite orb_false_r. reflexivity.
  - right. simpl. rewrite orb_false_r. reflexivity.
  - unfold M.cexec. rewrite E. simpl. destruct (M.certify_ok (M.core_of s)) eqn:C.
    + right. rewrite orb_true_r. reflexivity.
    + left. reflexivity.
Qed.

Lemma U_clean : clean_template U_host U_reg M.start.
Proof. repeat split. Qed.

Definition U_code (i : sinst) : nat -> nat := hregs (fst (fst i)) (snd (fst i)) (snd i).
Definition U_dec (i : sinst) (rho : nat -> nat) : nat * nat := (rho RA, rho RB).

(* ================================================================= *)
(* (N1).                                                              *)
(* ================================================================= *)

Theorem U_halt : forall i,
  halt_clause small_class U_host (fun _ => (nat * nat)%type) cobs 0 U (M.start (U_code i)) i
    (fun h => U_dec i (b_reg U_reg h)).
Proof.
  intros [[P x] y]. change (M.start (U_code (P, x, y))) with (hload P x y). split.
  - unfold clause1. split.
    + intros [n Hn]. simpl in Hn. rewrite U_hr in Hn.
      destruct (proj2 (universal_halting P x y) (ex_intro _ n Hn)) as [m Hm].
      exists m. simpl. rewrite (small_gr (P, x, y)). exact Hm.
    + intros [m Hm]. simpl in Hm. rewrite (small_gr (P, x, y)) in Hm.
      destruct (proj1 (universal_halting P x y) (ex_intro _ m Hm)) as [n Hn].
      exists n. simpl. rewrite U_hr. exact Hn.
  - intros m0 _ Hs. simpl in Hs. rewrite (small_gr (P, x, y)) in Hs.
    destruct (proj1 (universal_halting P x y) (ex_intro _ m0 Hs)) as [n Hn].
    destruct (universal_output P x y m0 n Hs Hn) as (Ha & Hb & _ & Hmu & Hc).
    exists n. split; [simpl; rewrite U_hr; exact Hn |].
    pose proof (U_hl U n (hload P x y)) as Hl. fold (UniversalRun.hrun P x y n) in Hl.
    pose proof (glat_cert (P, x, y) m0) as Hlat. rewrite (small_gr (P, x, y)) in Hlat. simpl in Hlat.
    split; [| split].
    + unfold U_dec, cobs. simpl. rewrite U_hr. fold (UniversalRun.hrun P x y n).
      rewrite (small_gr (P, x, y)). simpl. rewrite Ha, Hb. reflexivity.
    + simpl. rewrite U_hr. fold (UniversalRun.hrun P x y n). rewrite Hlat. exact Hc.
    + exists 0. split; [lia |]. rewrite <- small_gl. simpl.
      assert (Hm0 : M.mu (hload P x y) = 0) by reflexivity. fold (UniversalRun.hrun P x y n) in Hl. lia.
Qed.

(* ================================================================= *)
(* (N2), in order.                                                    *)
(* ================================================================= *)

Lemma hchainU : forall P x y N0,
  (forall k, k < N0 -> ~ E.halted P (E.core_of (UniversalRun.grun P x y k))) ->
  exists lh : nat -> nat, (forall k, k < N0 -> lh k < lh (S k)) /\
    forall k, k <= N0 ->
      (exists sg rho, rel_with P sg rho (UniversalRun.grun P x y k) (UniversalRun.hrun P x y (lh k))) \/
      rel_halt P (UniversalRun.grun P x y k) (UniversalRun.hrun P x y (lh k)).
Proof.
  intros P x y N0. induction N0 as [| N IH]; intros Hl.
  (* SAFE: a chain over the single step 0 has nothing to increase;
     time 0 is the load, which is related to the guest's start. *)
  - exists (fun _ => 0). split; [intros; lia |]. intros k Hk. replace k with 0 by lia.
    left. exists [], None. exact (hload_rel P x y).
  - destruct (IH (fun k Hk => Hl k ltac:(lia))) as (lh & Hinc & Hrel).
    assert (HnN : ~ E.halted P (E.core_of (UniversalRun.grun P x y N))) by (apply Hl; lia).
    destruct (Hrel N (le_n N)) as [(sg & rho & R) | RH]; [| exfalso; exact (HnN (proj1 RH))].
    assert (Hg : UniversalRun.grun P x y (S N) = E.step P (UniversalRun.grun P x y N))
      by (unfold UniversalRun.grun; apply grun_succ).
    destruct (U_step_with P sg rho _ _ R) as [[Hh _] | [_ (d & h' & Hd & Hres)]];
      [exfalso; exact (HnN Hh) |].
    assert (Hhh : UniversalRun.hrun P x y (lh N + S d) = h') by (rewrite hrun_add; exact Hd).
    exists (fun k => if Nat.leb k N then lh k else lh N + S d). split.
    + intros k Hk. destruct (Nat.leb k N) eqn:E1; destruct (Nat.leb (S k) N) eqn:E2;
        apply Nat.leb_le in E1 || apply Nat.leb_gt in E1;
        apply Nat.leb_le in E2 || apply Nat.leb_gt in E2; try lia.
      * apply Hinc. lia.
      * replace k with N by lia. lia.
    + intros k Hk. destruct (Nat.leb k N) eqn:E1.
      * apply Nat.leb_le in E1. apply Hrel, E1.
      * apply Nat.leb_gt in E1. replace k with (S N) by lia. rewrite Hg, Hhh.
        destruct Hres as [(sg' & rho' & R' & _) | (_ & RH')]; [left; exists sg', rho'; exact R' | right; exact RH'].
Qed.

Section Order.
Variable P : list E.instr.
Variables x y : nat.

Definition DU (m n : nat) : Prop :=
  hv (UniversalRun.hrun P x y n) RA = E.ca (E.core_of (UniversalRun.grun P x y m)) /\
  hv (UniversalRun.hrun P x y n) RB = E.cb (E.core_of (UniversalRun.grun P x y m)) /\
  M.mu (UniversalRun.hrun P x y n) = E.mu (UniversalRun.grun P x y m) /\
  M.cert (UniversalRun.hrun P x y n) = E.cert (UniversalRun.grun P x y m).

Lemma DU_dec : forall m n, {DU m n} + {~ DU m n}.
Proof.
  intros m n. unfold DU.
  destruct (Nat.eq_dec (hv (UniversalRun.hrun P x y n) RA) (E.ca (E.core_of (UniversalRun.grun P x y m))));
    [| right; tauto].
  destruct (Nat.eq_dec (hv (UniversalRun.hrun P x y n) RB) (E.cb (E.core_of (UniversalRun.grun P x y m))));
    [| right; tauto].
  destruct (Nat.eq_dec (M.mu (UniversalRun.hrun P x y n)) (E.mu (UniversalRun.grun P x y m))); [| right; tauto].
  destruct (Bool.bool_dec (M.cert (UniversalRun.hrun P x y n)) (E.cert (UniversalRun.grun P x y m)));
    [left; auto | right; tauto].
Defined.

Definition LU (m : nat) : Prop := forall k, k < m -> ~ E.halted P (E.core_of (UniversalRun.grun P x y k)).

Lemma LU_dec : forall m, {LU m} + {~ LU m}.
Proof.
  intros m. induction m as [| m IH].
  - left. intros k Hk. lia.
  - destruct IH as [Hl | Hl].
    + destruct (E.next_instr P (E.core_of (UniversalRun.grun P x y m))) eqn:E.
      * left. intros k Hk. destruct (Nat.eq_dec k m) as [-> | Hne].
        -- unfold E.halted. rewrite E. discriminate.
        -- apply Hl. lia.
      * right. intros Hl'. exact (Hl' m ltac:(lia) E).
    + right. intros Hl'. apply Hl. intros k Hk. apply Hl'. lia.
Defined.

Lemma uchains : forall M0, LU M0 -> exists l : nat -> nat,
  (forall k, k < M0 -> l k < l (S k)) /\ (forall k, k <= M0 -> DU k (l k)).
Proof.
  intros M0 Hl. destruct (hchainU P x y M0 Hl) as (lh & Hinc & Hrel). exists lh. split; [exact Hinc |].
  intros k Hk. destruct (Hrel k Hk) as [(sg & rho & R) | RH].
  - split; [exact (R_ra P sg rho _ _ R) |]. split; [exact (R_rb P sg rho _ _ R) |].
    split; [exact (rw_mu _ _ _ _ _ R) | exact (rw_cert _ _ _ _ _ R)].
  - destruct RH as (_ & _ & Ha & Hb & _ & Hm & Hc & _). unfold DU. auto.
Qed.

Theorem U_order : exists f : nat -> nat,
  (forall m, LU (S m) -> f m < f (S m)) /\ (forall m, LU m -> DU m (f m)).
Proof.
  apply (chains_to_fun DU DU_dec LU LU_dec).
  - intros m Hl k Hk. apply Hl. lia.
  - exact uchains.
Qed.

End Order.

Theorem U_in_order : forall i, exists f,
  in_order small_class U_host (fun _ => (nat * nat)%type) cobs 0 U (M.start (U_code i)) i
    (fun h => U_dec i (b_reg U_reg h)) f.
Proof.
  intros [[P x] y]. change (M.start (U_code (P, x, y))) with (hload P x y).
  destruct (U_order P x y) as (f & Hinc & HD).
  assert (Hl : forall m, live_before (C:=small_class) (P, x, y) m -> LU P x y m).
  { intros m Hm k Hk. pose proof (Hm k Hk) as X.
    change (gnext small_class (P, x, y) (UMachDef.grun (C:=small_class) (P, x, y) k) <> None) in X.
    rewrite (small_gr (P, x, y)) in X. exact X. }
  exists f. split; [intros m Hm; apply Hinc, Hl, Hm |].
  intros m Hm. destruct (HD m (Hl m Hm)) as (Ha & Hb & Hmu & Hc).
  pose proof (U_hl U (f m) (hload P x y)) as Hh. fold (UniversalRun.hrun P x y (f m)) in Hh.
  pose proof (glat_cert (P, x, y) m) as Hlat. rewrite (small_gr (P, x, y)) in Hlat. simpl in Hlat.
  split; [| split].
  - unfold U_dec, cobs. simpl. rewrite U_hr. fold (UniversalRun.hrun P x y (f m)).
    rewrite (small_gr (P, x, y)). simpl. rewrite Ha, Hb. reflexivity.
  - simpl. rewrite U_hr. fold (UniversalRun.hrun P x y (f m)). rewrite Hlat. exact Hc.
  - exists 0. split; [lia |]. rewrite <- small_gl. simpl.
    assert (Hm0 : M.mu (hload P x y) = 0) by reflexivity. lia.
Qed.

Theorem U_neutral_universal :
  neutral_universal small_class U_host (fun _ => (nat * nat)%type) cobs 0.
Proof.
  exists U, U_reg, U_raise, M.start, U_code, U_dec.
  split; [exact U_host_nc |]. split; [exact U_line_raise |]. split; [exact U_clean |].
  intros i. split; [apply U_halt | apply U_in_order].
Qed.

Print Assumptions U_host_nc.
Print Assumptions U_line_raise.
Print Assumptions U_halt.
Print Assumptions U_in_order.
Print Assumptions U_neutral_universal.
