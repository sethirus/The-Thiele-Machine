(** UMachMeetsU.v: U and U_P meet the (weak, order-free) rendering of
    the plain definition in UMachDef.v, from the theorems already proved
    about them.
    This checks that the rendering is not stronger than what the book's
    machines satisfy, so that the cheat of UMachCheatSmall.v
    meeting the (stronger, in-order) rendering is a statement about the
    book's definition and not about an over-weak formalisation.          *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.UMachCheatSmall.
Require Import Minimal.UniversalCodes.
Require Import Kernel.UniversalBridge.
Require Import Kernel.UniversalLayout.
Require Import Kernel.UniversalSim.
Require Import Kernel.UniversalRun.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.

(* ================================================================= *)
(* U's host machine as a UMachDef host.                                  *)
(* ================================================================= *)

Definition U_host : host :=
  mk_host (@M.state hprop) (@M.instr hprop) (M.exec hprop_eqb heval) (@M.cost hprop)
    (@M.cert hprop) (fun s i => M.multi_a2 hprop_eqb heval s i)
    (list (@M.instr hprop)) (fun P s => M.next_instr P (M.core_of s)).

Lemma U_hr : forall (Q : list (@M.instr hprop)) n s,
  hr (H:=U_host) Q s n = M.run_prog hprop_eqb heval n Q s.
Proof.
  intros Q n. induction n as [| n IH]; intros s; [reflexivity |].
  simpl. unfold M.step. destruct (M.next_instr Q (M.core_of s)) eqn:E.
  - apply IH.
  - symmetry. apply M.multi_run_prog_halted. exact E.
Qed.

Lemma U_hl : forall (Q : list (@M.instr hprop)) n s,
  M.mu (M.run_prog hprop_eqb heval n Q s) = M.mu s + hl (H:=U_host) Q s n.
Proof.
  intros Q n. induction n as [| n IH]; intros s; [simpl; lia |].
  simpl. unfold M.step. destruct (M.next_instr Q (M.core_of s)) eqn:E.
  - rewrite IH. simpl. lia.
  - rewrite M.multi_run_prog_halted by exact E. lia.
Qed.

Lemma small_gr : forall (i : sinst) m,
  UMachDef.grun (C:=small_class) i m = UniversalRun.grun (fst (fst i)) (snd (fst i)) (snd i) m.
Proof.
  intros [[P x] y] m. unfold UMachDef.grun, UniversalRun.grun. simpl.
  generalize (E.start x y). induction m as [| m IH]; intros s; [reflexivity |].
  simpl. unfold E.step. destruct (E.next_instr P (E.core_of s)) eqn:E.
  - apply IH.
  - symmetry. clear IH. induction m; simpl; [reflexivity |]. unfold E.step. rewrite E. exact IHm.
Qed.

Lemma small_gl_gen : forall P x y m (s : E.state),
  E.mu (E.run_prog m P s) = E.mu s + gl (C:=small_class) (i:=(P, x, y)) s m.
Proof.
  intros P x y m. induction m as [| m IH]; intros s; [simpl; lia |].
  simpl. unfold E.step. destruct (E.next_instr P (E.core_of s)) eqn:E.
  - rewrite IH. simpl. lia.
  - assert (Hs : E.run_prog m P s = s).
    { clear IH. induction m; simpl; [reflexivity |]. unfold E.step. rewrite E. exact IHm. }
    rewrite Hs. lia.
Qed.

Lemma small_gl : forall (i : sinst) m,
  E.mu (UniversalRun.grun (fst (fst i)) (snd (fst i)) (snd i) m) = gledger (C:=small_class) i m.
Proof.
  intros [[P x] y] m. unfold gledger, UniversalRun.grun. simpl.
  rewrite (small_gl_gen P x y m). reflexivity.
Qed.

(* Observation: the guest's two counters (what U's theorems decode at
   every matching point, running or halted). *)
Definition cobs (i : sinst) (g : E.state) : nat * nat := (E.ca (E.core_of g), E.cb (E.core_of g)).

Theorem U_meets_weak :
  universal_thiele_weak small_class U_host (fun _ => (nat * nat)%type) cobs 0.
Proof.
  exists U, (fun i => hload (fst (fst i)) (snd (fst i)) (snd i)),
         (fun _ h => (hv h RA, hv h RB)).
  intros [[P x] y]. simpl fst; simpl snd. split; [| split].
  - unfold clause1. split.
    + intros [n Hn]. simpl in Hn. rewrite U_hr in Hn.
      destruct (proj2 (universal_halting P x y) (ex_intro _ n Hn)) as [m Hm].
      exists m. simpl. rewrite (small_gr (P, x, y)). exact Hm.
    + intros [m Hm]. simpl in Hm. rewrite (small_gr (P, x, y)) in Hm.
      destruct (proj1 (universal_halting P x y) (ex_intro _ m Hm)) as [n Hn].
      exists n. simpl. rewrite U_hr. exact Hn.
  - intros m _. destruct (proj1 (universal_ledger_exact P x y) m) as [n [Hr Hmu]].
    exists n. unfold match_at. simpl hP in *. rewrite !U_hr.
    pose proof (U_hl U n (hload P x y)) as Hl. fold (UniversalRun.hrun P x y n) in Hl.
    pose proof (glat_cert (P, x, y) m) as Hlat.
    rewrite (small_gr (P, x, y)) in Hlat. simpl in Hlat.
    fold (UniversalRun.hrun P x y n).
    assert (Hm0 : M.mu (hload P x y) = 0) by reflexivity.
    destruct Hr as [[[sg [rho R]] _] | RH].
    + split; [| split].
      * unfold cobs. rewrite (small_gr (P, x, y)). simpl.
        pose proof (rw_greg _ _ _ _ _ R E.CA) as HA. pose proof (rw_greg _ _ _ _ _ R E.CB) as HB.
        simpl in HA, HB. unfold RA, RB. rewrite HA, HB. reflexivity.
      * simpl. rewrite Hlat. exact (rw_cert _ _ _ _ _ R).
      * exists 0. split; [lia |]. rewrite <- small_gl. simpl. lia.
    + destruct RH as (_ & _ & HA & HB & _ & _ & Hc & _).
      split; [| split].
      * unfold cobs. rewrite (small_gr (P, x, y)). simpl. rewrite HA, HB. reflexivity.
      * simpl. rewrite Hlat. exact Hc.
      * exists 0. split; [lia |]. rewrite <- small_gl. simpl. lia.
  - intros n. apply clause3_free.
Qed.

Print Assumptions U_meets_weak.
