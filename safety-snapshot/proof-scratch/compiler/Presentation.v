(** Presentation.v: computably presented machines.

    A presented machine M (Presented.v) is computably presented when four
    recursive algorithms (the vendored recalg of coq-undecidability, with
    its relational semantics ra_rel) compute, on the number codes of M:

      next   from the code of a state s, the number 0 when the driver halts
             at s, and 1 + the code of the move when the driver takes a move
             [cg_next_val];
      step   from the codes of a state s and a move i, the code of the state
             the move leads to;
      cost   from the code of a move, its cost;
      read   from any number v, 1 when v is the code of a state whose
             reading is yes, and 0 otherwise: 0 when the reading is no, and
             0 on every number that is not the code of a state (junk 0)
             [cg_read_val, cg_read_val_code].

    The record cg_presentation M holds the four algorithms with these four
    specifications, and cg_computably_presented M says such a record
    exists.

    The file also proves how one driven step changes the latch, the ledger
    and the surcharge of Presented.v [cg_mlatch_succ, cg_first_raise_succ,
    cg_account_step, cg_account_start]: for a move of cost c from the state
    after n steps, the ledger plus surcharge grows by c, except at the first
    raise, where it grows by 3 + (c - 3).

    Dependencies: Coq standard library, the vendored coq-undecidability
    library (recursive algorithms), EarnedGeneric.v, EarnedPriced.v,
    ThieleComplete.v and Presented.v. No axioms, no Admitted. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec.
From Undecidability.MuRec.Util Require Import recalg.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.
Require Import Minimal.Presented.

Section Presentation.

Variable M : presented_machine.

Local Notation st := (T.cs_state (pm_sys M)).
Local Notation mv := (T.cs_instr (pm_sys M)).
Local Notation cstep := (T.cs_step (pm_sys M)).
Local Notation ccost := (T.cs_cost (pm_sys M)).
Local Notation rd := (T.cs_cert (pm_sys M)).
Local Notation next := (pm_next M).

(* The driver's answer as a number: 0 to halt, 1 + the move's code. *)
Definition cg_next_val (s : st) : nat :=
  match next s with None => 0 | Some i => S (pm_icode M i) end.

(* The reading as a number on every input: 1 or 0 on the code of a state,
   0 on every number that is not the code of a state. *)
Definition cg_read_val (v : nat) : nat :=
  match pm_sdec M v with
  | Some s => if Nat.eqb (pm_scode M s) v then (if rd s then 1 else 0) else 0
  | None => 0
  end.

Lemma cg_read_val_code : forall s, cg_read_val (pm_scode M s) = if rd s then 1 else 0.
Proof.
  intros s. unfold cg_read_val. rewrite pm_sdec_scode, Nat.eqb_refl. reflexivity.
Qed.

Lemma cg_read_val_junk : forall v, (forall s, pm_scode M s <> v) -> cg_read_val v = 0.
Proof.
  intros v H. unfold cg_read_val. destruct (pm_sdec M v) as [s |]; [| reflexivity].
  destruct (Nat.eqb_spec (pm_scode M s) v); [exfalso; exact (H s e) | reflexivity].
Qed.

Record cg_presentation : Type := cg_mk_presentation {
  cg_next_ra : recalg 1;
  cg_step_ra : recalg 2;
  cg_cost_ra : recalg 1;
  cg_read_ra : recalg 1;
  cg_next_spec : forall s, ra_rel cg_next_ra (pm_scode M s ## vec_nil) (cg_next_val s);
  cg_step_spec : forall s i,
    ra_rel cg_step_ra (pm_scode M s ## pm_icode M i ## vec_nil) (pm_scode M (cstep s i));
  cg_cost_spec : forall i, ra_rel cg_cost_ra (pm_icode M i ## vec_nil) (ccost i);
  cg_read_spec : forall v, ra_rel cg_read_ra (v ## vec_nil) (cg_read_val v)
}.

Definition cg_computably_presented : Prop := inhabited cg_presentation.

(* ================================================================= *)
(* One driven step and the account of Presented.v.                    *)
(* ================================================================= *)

Lemma cg_mlatch_succ : forall s0 n,
  mlatch M s0 (S n) = mlatch M s0 n || rd (presented_run M s0 (S n)).
Proof.
  intros s0 n. apply eq_true_iff_eq. rewrite orb_true_iff, !presented_mlatch_iff.
  split.
  - intros [m [Hm H]]. destruct (Nat.eq_dec m (S n)) as [-> | Hne].
    + right. exact H.
    + left. exists m. split; [lia | exact H].
  - intros [[m [Hm H]] | H].
    + exists m. split; [lia | exact H].
    + exists (S n). split; [lia | exact H].
Qed.

Lemma cg_mlatch_false_rd : forall s0 n, mlatch M s0 n = false -> rd s0 = false.
Proof. intros s0 [| n] H; simpl in H; apply orb_false_iff in H; apply H. Qed.

(* The first raise, when it happens at step n + 1. *)
Lemma cg_first_raise_succ : forall n s0 i,
  mlatch M s0 n = false ->
  next (presented_run M s0 n) = Some i ->
  rd (cstep (presented_run M s0 n) i) = true ->
  first_raise M s0 (S n) = Some i.
Proof.
  induction n as [| n IH]; intros s0 i Hl Hn Hr.
  - simpl in Hl. rewrite orb_false_r in Hl. simpl in Hn, Hr.
    simpl. rewrite Hl, Hn, Hr. reflexivity.
  - simpl in Hl. apply orb_false_iff in Hl as [H0 Hl].
    simpl in Hn, Hr. destruct (next s0) as [j |] eqn:E; rewrite ?E in Hl, Hn, Hr.
    + assert (Hj : rd (cstep s0 j) = false) by (apply (cg_mlatch_false_rd _ n Hl)).
      change (first_raise M s0 (S (S n))) with
        (if rd s0 then None else
         match next s0 with
         | None => None
         | Some i => if rd (cstep s0 i) then Some i else first_raise M (cstep s0 i) (S n)
         end).
      rewrite H0, E, Hj. apply IH; assumption.
    + congruence.
Qed.

(* What the guest pays at the check that follows a move of cost c: c,
   except at the first raise (latch down, reading now yes), where it pays
   3 for the earned record and then c - 3. *)
Definition cg_chk_pay (l b : bool) (c : nat) : nat :=
  if negb l && b then 3 + (c - 3) else c.

Theorem cg_account_step : forall s0 n i,
  next (presented_run M s0 n) = Some i ->
  presented_run M s0 (S n) = cstep (presented_run M s0 n) i /\
  mlatch M s0 (S n) = mlatch M s0 n || rd (cstep (presented_run M s0 n) i) /\
  mledger M s0 (S n) + surcharge M s0 (S n) =
    mledger M s0 n + surcharge M s0 n +
    cg_chk_pay (mlatch M s0 n) (rd (cstep (presented_run M s0 n) i)) (ccost i).
Proof.
  intros s0 n i Hn.
  assert (Hr : presented_run M s0 (S n) = cstep (presented_run M s0 n) i)
    by (rewrite presented_run_succ, Hn; reflexivity).
  assert (Hl : mlatch M s0 (S n) = mlatch M s0 n || rd (cstep (presented_run M s0 n) i))
    by (rewrite cg_mlatch_succ, Hr; reflexivity).
  split; [exact Hr |]. split; [exact Hl |].
  rewrite mledger_succ, Hn. unfold cg_chk_pay.
  destruct (mlatch M s0 n) eqn:Ln.
  - rewrite (presented_surcharge_stable M s0 n (S n)) by (lia || exact Ln). simpl. lia.
  - assert (S0 : surcharge M s0 n = 0) by (unfold surcharge; rewrite Ln; reflexivity).
    rewrite S0.
    destruct (rd (cstep (presented_run M s0 n) i)) eqn:Rd; simpl.
    + assert (S1 : surcharge M s0 (S n) = 3 - ccost i).
      { unfold surcharge, raise_cost. rewrite (cg_first_raise_succ n s0 i Ln Hn Rd).
        rewrite Hl, ?Ln, ?Rd. reflexivity. }
      rewrite S1. lia.
    + assert (S1 : surcharge M s0 (S n) = 0)
        by (unfold surcharge; rewrite Hl, ?Ln, ?Rd; reflexivity).
      rewrite S1. lia.
Qed.

Theorem cg_account_start : forall s0,
  mlatch M s0 0 = rd s0 /\
  mledger M s0 0 + surcharge M s0 0 = cg_chk_pay false (rd s0) 0.
Proof.
  intros s0. simpl. rewrite orb_false_r. split; [reflexivity |].
  unfold surcharge, raise_cost, cg_chk_pay. simpl.
  destruct (rd s0); reflexivity.
Qed.

End Presentation.

Arguments cg_next_ra {M}.
Arguments cg_step_ra {M}.
Arguments cg_cost_ra {M}.
Arguments cg_read_ra {M}.
Arguments cg_next_spec {M}.
Arguments cg_step_spec {M}.
Arguments cg_cost_spec {M}.
Arguments cg_read_spec {M}.
