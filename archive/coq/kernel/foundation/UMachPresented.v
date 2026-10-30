(** UMachPresented.v: U_P's class of guests, computably presented
    machines with a start, as a guest class of UMachDef.v, with two generic
    lemmas about guest runs and the observation of a presented guest. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Minimal.Presented.
Require Import Kernel.Presentation.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.

(* ================================================================= *)
(* Generic: a guest is live up to n, or it stopped at a first m0 < n. *)
(* ================================================================= *)

Lemma live_or_stop_gen : forall (C : gclass) (i : gi C) n,
  live_before i n \/
  exists m0, m0 < n /\ gnext C i (grun i m0) = None /\ live_before i m0.
Proof.
  intros C i n. induction n as [| n IH].
  - left. intros k Hk. lia.
  - destruct IH as [Hl | (m0 & Hm & Hs & Hl)].
    + destruct (gnext C i (grun i n)) eqn:E.
      * left. intros k Hk. destruct (Nat.eq_dec k n) as [-> | Hne].
        { unfold grun in E. rewrite E. discriminate. }
        apply Hl. lia.
      * right. exists n. auto.
    + right. exists m0. split; [lia | auto].
Qed.

Lemma glatch_read : forall (C : gclass) (i : gi C) s n, gread C i (gr s n) = true -> glatch s n = true.
Proof.
  intros C i s [| n] H; [exact H |].
  change (glatch s (S n)) with (glatch s n || gread C i (gr s (S n))).
  rewrite H. apply orb_true_r.
Qed.

(* ================================================================= *)
(* U_P's class: computably presented machines with a start.           *)
(* ================================================================= *)

Definition pinst : Type :=
  { Mp : presented_machine & (cg_presentation Mp * T.cs_state (pm_sys Mp))%type }.

Definition presented_class : gclass :=
  mk_gclass pinst
    (fun i => T.cs_state (pm_sys (projT1 i)))
    (fun i => T.cs_instr (pm_sys (projT1 i)))
    (fun i => pm_next (projT1 i))
    (fun i => T.cs_step (pm_sys (projT1 i)))
    (fun i => T.cs_cost (pm_sys (projT1 i)))
    (fun i => T.cs_cert (pm_sys (projT1 i)))
    (fun i => T.cs_cert_costs (pm_sys (projT1 i)))
    (fun i => snd (projT2 i)).


(* The observation of a presented guest: its whole state. *)
Definition pobs (i : pinst) (s : T.cs_state (pm_sys (projT1 i))) : option (T.cs_state (pm_sys (projT1 i))) :=
  Some s.
