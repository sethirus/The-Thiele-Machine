(** UMachShadowU.v: UMachRegHost.reg_host is about a VIEW of the state (line,
    register file, trap bit).  It says nothing about the rest of the state.

    prod_reg_host: for any register host H and ANY extra component Z with
    ANY update zstep : state -> move -> Z -> Z, the product host (same
    moves, prices, flag and program fetch; the extra component updated by
    zstep at every move) is again a register host.

    prod_universal: if H meets the in-order rendering of
    the plain definition for a class, so does the product, with the same
    surcharge bound (load the extra component with anything, decode from
    H's part).

    Instance shadowU: U's host machine with a hidden copy of the guest,
    where every INC on register 0 ALSO takes one step of the guest program
    on the hidden copy: a guest step built into a counter move.  shadowU
    meets the in-order definition with surcharge 0 (shadow_meets), is a
    register host (shadow_reg_host), is loaded clean (shadow_clean), and its
    runs execute exactly U's moves (shadow_trace), so universal_earned (U's
    form of (c)) holds of it verbatim; and its hidden copy really is
    stepped by the host (shadow_steps).                                     *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.UMachCheatSmall.
Require Import Kernel.UMachMeetsU.
Require Import Kernel.UMachRegHost.
Require Import Kernel.UMachInOrderU.
Require Import Minimal.UniversalCodes.
Require Import Kernel.UniversalBridge.
Require Import Kernel.UniversalLayout.
Require Import Kernel.UniversalSim.
Require Import Kernel.UniversalRun.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.

Section Prod.
Variable H : host.
Variable Z : Type.
Variable zstep : hS H -> hI H -> Z -> Z.

Definition pstep (s : hS H * Z) (m : hI H) : hS H * Z := (hstep H (fst s) m, zstep (fst s) m (snd s)).

Lemma ptoll : forall s m, hflag H (fst s) = false -> hflag H (fst (pstep s m)) = true -> hcost H m >= 1.
Proof. intros [s z] m H0 H1. exact (htoll H s m H0 H1). Qed.

Definition prod_host : host :=
  mk_host (hS H * Z) (hI H) pstep (hcost H) (fun s => hflag H (fst s)) ptoll (hP H)
    (fun P s => hnext H P (fst s)).

Lemma prod_hr : forall P s z n, fst (hr (H:=prod_host) P (s, z) n) = hr (H:=H) P s n.
Proof.
  intros P s z n. revert s z. induction n as [| n IH]; intros s z; [reflexivity |].
  simpl. destruct (hnext H P s); [apply IH | reflexivity].
Qed.

Lemma prod_hl : forall P s z n, hl (H:=prod_host) P (s, z) n = hl (H:=H) P s n.
Proof.
  intros P s z n. revert s z. induction n as [| n IH]; intros s z; [reflexivity |].
  simpl. destruct (hnext H P s); [unfold pstep; rewrite IH; reflexivity | reflexivity].
Qed.

Definition prod_reg_host (R : reg_host H) : reg_host prod_host.
Proof.
  refine (mk_rh prod_host (fun s => b_pc R (fst s)) (fun s => b_reg R (fst s)) (fun s => b_err R (fst s))
            (b_kind R) _ _ _ _ _ _ _ _).
  - exact (b_cost H R).
  - intros s m E. exact (b_stuck H R (fst s) m E).
  - intros s m r E K. exact (b_inc H R (fst s) m r E K).
  - intros s m r j E K. exact (b_dec H R (fst s) m r j E K).
  - intros s m K. exact (b_halt H R (fst s) m K).
  - intros s m E K. exact (b_rec H R (fst s) m E K).
  - intros P s1 s2 E Pc. exact (b_next H R P (fst s1) (fst s2) E Pc).
  - intros P s E. exact (b_next_err H R P (fst s) E).
Defined.

Theorem prod_universal : forall (C : gclass) Obs obs K (z0 : gi C -> Z),
  universal_thiele C H Obs obs K -> universal_thiele C prod_host Obs obs K.
Proof.
  intros C Obs obs K z0 (P & load & decode & Hall).
  exists P, (fun i => (load i, z0 i)), (fun i s => decode i (fst s)). intros i.
  destruct (Hall i) as (H1 & (f & Hinc & Hm) & _). split; [| split].
  - unfold clause1 in *. simpl. rewrite <- H1. split; intros [n Hn]; exists n;
      rewrite ?prod_hr in *; rewrite <- ?prod_hr in Hn; simpl in *; rewrite ?prod_hr in *; exact Hn.
  - exists f. split; [exact Hinc |]. intros m Hl. destruct (Hm m Hl) as (A & B & s & Hs & Hle).
    unfold match_at. simpl hflag. rewrite prod_hr, prod_hl. split; [exact A |]. split; [exact B |].
    exists s. auto.
  - intros n. apply clause3_free.
Qed.

End Prod.

(* ================================================================= *)
(* U with a hidden guest stepped by INC 0.                            *)
(* ================================================================= *)

Definition gz : Type := (list E.instr * E.state)%type.

Definition zU (s : hS U_host) (m : hI U_host) (z : gz) : gz :=
  match m with M.INC 0 => (fst z, E.step (fst z) (snd z)) | _ => z end.

Definition shadowU : host := prod_host U_host gz zU.

Theorem shadow_meets :
  universal_thiele small_class shadowU (fun _ => (nat * nat)%type) cobs 0.
Proof.
  apply (prod_universal U_host gz zU small_class _ cobs 0
           (fun i => (fst (fst i), E.start (snd (fst i)) (snd i)))).
  exact U_meets_strong.
Qed.

Definition shadow_reg_host : reg_host shadowU := prod_reg_host U_host gz zU U_host_RH.

Theorem shadow_clean : forall P x y,
  M.clean_start (fst (hload P x y, (P, E.start x y))) /\ M.mu (fst (hload P x y, (P, E.start x y))) = 0.
Proof. intros. split; [apply M.multi_start_clean | reflexivity]. Qed.

(* The moves the shadow host's program takes are U's. *)
Fixpoint ptrace {H : host} (P : hP H) (h : hS H) (n : nat) : list (hI H) :=
  match n with
  | 0 => []
  | S n' => match hnext H P h with None => [] | Some m => m :: ptrace P (hstep H h m) n' end
  end.

Theorem shadow_trace : forall (P : hP U_host) s z n,
  ptrace (H:=shadowU) P (s, z) n = ptrace (H:=U_host) P s n.
Proof.
  intros P s z n. revert s z. induction n as [| n IH]; intros s z; [reflexivity |].
  simpl. destruct (M.next_instr P (M.core_of s)); [| reflexivity]. f_equal. apply IH.
Qed.

(* The hidden copy is stepped by the host: after a host move INC 0, the
   hidden guest has taken one more step of its program. *)
Theorem shadow_steps : forall s Pg g,
  snd (hstep shadowU (s, (Pg, g)) (M.INC 0)) = (Pg, E.step Pg g).
Proof. reflexivity. Qed.

Print Assumptions prod_universal.
Print Assumptions shadow_meets.
Print Assumptions shadow_reg_host.
Print Assumptions shadow_trace.
