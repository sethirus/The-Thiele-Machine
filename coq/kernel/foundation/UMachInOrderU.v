(** UMachInOrderU.v: the IN-ORDER form of clause (2) for U.

    U_in_order: for every guest program P and start (x, y) there is ONE
    function f with f m < f (S m) for every m, such that at host time f m
    (for every m the guest reaches without having stopped before) the host
    shows the guest after m steps: RA, RB hold its counters, the host trap
    equals its trap, the host ledger equals its ledger, the host flag
    equals its flag, and, when the guest has not trapped, GPC holds its
    line and the host is at the head of U's loop (line L_HEAD, trap down).

    U_meets_strong: U meets UMachDef.universal_thiele (the in-order rendering
    of the plain definition) with surcharge 0, observation = the two
    counters (and U_meets_strong_full with observation = counters, trap,
    and line when untrapped).                                              *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.UMachCheatSmall.
Require Import Kernel.UMachMeetsU.
Require Import Kernel.UMachInOrderGen.
Require Import Minimal.UniversalCodes.
Require Import Kernel.UniversalBridge.
Require Import Kernel.UniversalLayout.
Require Import Kernel.UniversalPhases.
Require Import Kernel.UniversalSim.
Require Import Kernel.UniversalRun.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.

(* live_before is decidable, for any guest class. *)
Lemma live_dec : forall (C : gclass) (i : gi C) m, {live_before i m} + {~ live_before i m}.
Proof.
  intros C i m. induction m as [| m IH].
  - left. intros k Hk. lia.
  - destruct IH as [H | H].
    + destruct (gnext C i (UMachDef.grun i m)) eqn:E.
      * left. intros k Hk. destruct (Nat.eq_dec k m) as [-> | Hne]; [unfold UMachDef.grun in E; rewrite E; discriminate |].
        apply H. lia.
      * right. intros X. apply (X m); [lia | unfold UMachDef.grun in E; exact E].
    + right. intros X. apply H. intros k Hk. apply X. lia.
Defined.

Lemma live_prev : forall (C : gclass) (i : gi C) m, live_before i (S m) -> live_before i m.
Proof. intros C i m H k Hk. apply H. lia. Qed.

Section U.
Variables (P : list E.instr) (x y : nat).

Local Notation g m := (UniversalRun.grun P x y m).
Local Notation h t := (UniversalRun.hrun P x y t).

Definition Lu (m : nat) : Prop := live_before (C:=small_class) (P, x, y) m.

Definition Du (m t : nat) : Prop :=
  hv (h t) RA = E.ca (E.core_of (g m)) /\
  hv (h t) RB = E.cb (E.core_of (g m)) /\
  herr (h t) = E.err (E.core_of (g m)) /\
  M.mu (h t) = E.mu (g m) /\
  M.cert (h t) = E.cert (g m) /\
  (E.err (E.core_of (g m)) = false -> hv (h t) GPC = E.pc (E.core_of (g m)) /\ hpc (h t) = L_HEAD).

Definition Ru (m t : nat) : Prop :=
  rel P (g m) (h t) \/ (E.err (E.core_of (g m)) = true /\ rel_halt P (g m) (h t)).

Lemma Du_dec : forall m t, {Du m t} + {~ Du m t}.
Proof.
  intros m t. unfold Du.
  repeat match goal with
  | |- {?A /\ ?B} + {~ (?A /\ ?B)} =>
      let a := fresh in let b := fresh in
      assert (a : {A} + {~ A}); [| assert (b : {B} + {~ B});
        [| destruct a, b; [left; split; assumption | right; tauto | right; tauto | right; tauto]]]
  | |- {?u = ?v :> nat} + {_} => apply Nat.eq_dec
  | |- {?u = ?v :> bool} + {_} => apply Bool.bool_dec
  | |- {?A -> ?B} + {~ (?A -> ?B)} =>
      let a := fresh in let b := fresh in
      assert (a : {A} + {~ A}); [| assert (b : {B} + {~ B});
        [| destruct a, b; [left; auto | right; auto | left; tauto | left; tauto]]]
  end.
Defined.

Lemma live_not_halted : forall m, Lu (S m) -> ~ E.halted P (E.core_of (g m)).
Proof.
  intros m Hl Hh. apply (Hl m); [lia |].
  change (E.next_instr P (E.core_of (UMachDef.grun (C:=small_class) (P, x, y) m)) = None).
  rewrite (small_gr (P, x, y) m). exact Hh.
Qed.

Lemma Ru_D : forall m t, Lu m -> Ru m t -> Du m t.
Proof.
  intros m t _ [[sg [rho R]] | [He RH]].
  - pose proof (rw_greg _ _ _ _ _ R E.CA) as HA. pose proof (rw_greg _ _ _ _ _ R E.CB) as HB.
    simpl in HA, HB. pose proof (rw_err _ _ _ _ _ R) as Herr.
    destruct (rw_head _ _ _ _ _ R) as (Hpc & Hhe & _).
    unfold Du. split; [exact HA |]. split; [exact HB |].
    split; [rewrite Hhe, Herr; reflexivity |].
    split; [exact (rw_mu _ _ _ _ _ R) |]. split; [exact (rw_cert _ _ _ _ _ R) |].
    intros _. split; [exact (rw_gpc _ _ _ _ _ R) | exact Hpc].
  - destruct RH as (_ & _ & HA & HB & Hhe & Hmu & Hc & _).
    unfold Du. split; [exact HA |]. split; [exact HB |]. split; [exact Hhe |].
    split; [exact Hmu |]. split; [exact Hc |]. intros X. congruence.
Qed.

Lemma Ru_0 : Lu 0 -> exists t, Ru 0 t.
Proof. intros _. exists 0. left. exists [], None. apply hload_rel. Qed.

Lemma Ru_S : forall m t, Lu (S m) -> Ru m t -> exists t', t < t' /\ Ru (S m) t'.
Proof.
  intros m t Hl [[sg [rho R]] | [He RH]].
  - destruct (U_step_with P sg rho _ _ R) as [[Hh _] | [_ (n & h' & Hr & Hres)]].
    + exfalso. exact (live_not_halted m Hl Hh).
    + exists (t + S n). split; [lia |].
      assert (Ht : h (t + S n) = h') by (rewrite hrun_add; exact Hr).
      assert (Hg : g (S m) = E.step P (g m)) by (unfold UniversalRun.grun; apply grun_succ).
      unfold Ru. rewrite Ht, Hg. destruct Hres as [(sg' & rho' & R' & _) | [He' RH']].
      * left. exists sg', rho'. exact R'.
      * right. split; assumption.
  - exfalso. apply (live_not_halted m Hl). apply ghalted_trap. exact He.
Qed.

Theorem U_in_order :
  exists f : nat -> nat, (forall m, f m < f (S m)) /\ (forall m, Lu m -> Du m (f m)).
Proof.
  apply (in_order Lu (fun m => live_dec small_class (P, x, y) m)
           (fun m => live_prev small_class (P, x, y) m) Du Du_dec Ru Ru_D Ru_0 Ru_S).
Qed.

End U.

(* ================================================================= *)
(* U meets the in-order rendering of the plain definition.            *)
(* ================================================================= *)

Lemma U_clause1 : forall P x y,
  clause1 small_class U_host U (hload P x y) (P, x, y).
Proof.
  intros P x y. unfold clause1. split.
  + intros [n Hn]. simpl in Hn. rewrite U_hr in Hn.
    destruct (proj2 (universal_halting P x y) (ex_intro _ n Hn)) as [m Hm].
    exists m. simpl. rewrite (small_gr (P, x, y)). exact Hm.
  + intros [m Hm]. simpl in Hm. rewrite (small_gr (P, x, y)) in Hm.
    destruct (proj1 (universal_halting P x y) (ex_intro _ m Hm)) as [n Hn].
    exists n. simpl. rewrite U_hr. exact Hn.
Qed.

Lemma U_ledger_at : forall P x y t,
  hl (H:=U_host) U (hload P x y) t = M.mu (UniversalRun.hrun P x y t).
Proof.
  intros P x y t. pose proof (U_hl U t (hload P x y)) as Hl.
  fold (UniversalRun.hrun P x y t) in Hl. assert (M.mu (hload P x y) = 0) by reflexivity. lia.
Qed.

Theorem U_meets_strong :
  universal_thiele small_class U_host (fun _ => (nat * nat)%type) cobs 0.
Proof.
  exists U, (fun i => hload (fst (fst i)) (snd (fst i)) (snd i)),
         (fun _ h => (hv h RA, hv h RB)).
  intros [[P x] y]. simpl fst; simpl snd. split; [apply U_clause1 |]. split; [| intros n; apply clause3_free].
  destruct (U_in_order P x y) as (f & Hinc & Hd). exists f. split; [intros m _; apply Hinc |].
  intros m Hl. destruct (Hd m Hl) as (HA & HB & _ & Hmu & Hc & _).
  unfold match_at. simpl hP in *. rewrite !U_hr. fold (UniversalRun.hrun P x y (f m)).
  split; [| split].
  - unfold cobs. rewrite (small_gr (P, x, y)). simpl. rewrite HA, HB. reflexivity.
  - simpl. rewrite Hc. pose proof (glat_cert (P, x, y) m) as Hlat.
    rewrite (small_gr (P, x, y)) in Hlat. simpl in Hlat. rewrite Hlat. reflexivity.
  - exists 0. split; [lia |]. rewrite U_ledger_at, <- small_gl. simpl. lia.
Qed.

(* The richer observation: counters, trap, and the line while untrapped. *)
Definition fobs (i : sinst) (s : E.state) : nat * nat * bool * option nat :=
  (E.ca (E.core_of s), E.cb (E.core_of s), E.err (E.core_of s),
   if E.err (E.core_of s) then None else Some (E.pc (E.core_of s))).

Definition fdecode (h : @M.state hprop) : nat * nat * bool * option nat :=
  (hv h RA, hv h RB, herr h, if herr h then None else Some (hv h GPC)).

Theorem U_meets_strong_full :
  universal_thiele small_class U_host (fun _ => (nat * nat * bool * option nat)%type) fobs 0.
Proof.
  exists U, (fun i => hload (fst (fst i)) (snd (fst i)) (snd i)), (fun _ => fdecode).
  intros [[P x] y]. simpl fst; simpl snd. split; [apply U_clause1 |]. split; [| intros n; apply clause3_free].
  destruct (U_in_order P x y) as (f & Hinc & Hd). exists f. split; [intros m _; apply Hinc |].
  intros m Hl. destruct (Hd m Hl) as (HA & HB & He & Hmu & Hc & Hpc).
  unfold match_at. simpl hP in *. rewrite !U_hr. fold (UniversalRun.hrun P x y (f m)).
  split; [| split].
  - unfold fobs, fdecode. rewrite (small_gr (P, x, y)). simpl. rewrite HA, HB, He.
    destruct (E.err _) eqn:Ee; [reflexivity |]. rewrite (proj1 (Hpc eq_refl)). reflexivity.
  - simpl. rewrite Hc. pose proof (glat_cert (P, x, y) m) as Hlat.
    rewrite (small_gr (P, x, y)) in Hlat. simpl in Hlat. rewrite Hlat. reflexivity.
  - exists 0. split; [lia |]. rewrite U_ledger_at, <- small_gl. simpl. lia.
Qed.

Print Assumptions U_in_order.
Print Assumptions U_meets_strong.
Print Assumptions U_meets_strong_full.
