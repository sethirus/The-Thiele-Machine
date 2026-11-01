(** AxChain: a machine with a driver, number codes and a HEIGHT, and what its
    runs, ledger and latched height are.

    A chain machine has states, moves, a step, a cost per move, a driver (the
    move to take, or none to halt), number codes for states and moves, and a
    height h : state -> nat.  The height is the number of levels of a chain of
    thresholds that the record of the state has reached: level j is reached
    when j <= h s.  A record that grows along the run has a height that does
    not fall; the machine here does not need that, because what the guest
    keeps is the LATCHED height, the largest height seen so far.

    For a start state s0 and n driven steps:

      ax_cm_run s0 n         the state after n steps (a halted machine stays);
      ax_cm_ledger s0 n      the total cost of the moves taken;
      ax_cm_lat s0 n         the latched height: the largest height among the
                          states of the first n + 1;
      ax_cm_gledger s0 n     the ledger of the compiled guest: the start state
                          pays 3 for each of its levels, and each step pays
                          max (cost of the move, 3 * (levels newly latched by
                          that step)), because the guest pays 3 for each new
                          level out of the cost of the move first, and the
                          rest of the move after;
      ax_cm_surcharge s0 n   ax_cm_gledger - ax_cm_ledger, the extra the guest pays.

    A chain presentation is the four recursive algorithms that compute the
    driver, the step, the cost and the reading on number codes, where the
    reading takes a state code v and a level j and answers 1 when j <= h of
    the state coded by v, and 0 on every other pair.

    Results (all closed):

      ax_cm_lat_succ              the latched height after n + 1 steps is the
                               larger of the latched height after n steps and
                               the height of the state after n + 1;
      ax_cm_surcharge_le          the surcharge is at most 3 times the latched
                               height;
      ax_cm_gledger_ge            the guest's ledger is at least the machine's. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   defines chain machines (a machine with a height, so that level j is
   reached when j is at most the height) and their presentations. The
   statements that connect them to the axis and to the host that runs the
   chain are AxCgkAxis.v and AxCgkHost.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec.
From Undecidability.MuRec.Util Require Import recalg.

Record ax_chain_mach : Type := ax_mk_chain {
  ax_cm_st : Type;
  ax_cm_mv : Type;
  ax_cm_step : ax_cm_st -> ax_cm_mv -> ax_cm_st;
  ax_cm_cost : ax_cm_mv -> nat;
  ax_cm_h : ax_cm_st -> nat;
  ax_cm_next : ax_cm_st -> option ax_cm_mv;
  ax_cm_scode : ax_cm_st -> nat;
  ax_cm_sdec : nat -> option ax_cm_st;
  ax_cm_icode : ax_cm_mv -> nat;
  ax_cm_idec : nat -> option ax_cm_mv;
  ax_cm_sdec_scode : forall s, ax_cm_sdec (ax_cm_scode s) = Some s;
  ax_cm_idec_icode : forall i, ax_cm_idec (ax_cm_icode i) = Some i
}.

Section Chain.

Variable C : ax_chain_mach.

Local Notation st := (ax_cm_st C).
Local Notation mv := (ax_cm_mv C).
Local Notation cstep := (ax_cm_step C).
Local Notation ccost := (ax_cm_cost C).
Local Notation hh := (ax_cm_h C).
Local Notation next := (ax_cm_next C).

(** The driver's answer as a number: 0 to halt, 1 + the move's code. *)
Definition ax_cm_next_val (s : st) : nat :=
  match next s with None => 0 | Some i => S (ax_cm_icode C i) end.

(** The reading as a number on every pair: 1 when the first number codes a
    state s and the level is at most the height of s, else 0. *)
Definition ax_cm_read_val (v j : nat) : nat :=
  match ax_cm_sdec C v with
  | Some s => if Nat.eqb (ax_cm_scode C s) v then (if Nat.leb j (hh s) then 1 else 0) else 0
  | None => 0
  end.

Lemma ax_cm_read_val_code : forall s j,
  ax_cm_read_val (ax_cm_scode C s) j = if Nat.leb j (hh s) then 1 else 0.
Proof.
  intros s j. unfold ax_cm_read_val. rewrite ax_cm_sdec_scode, Nat.eqb_refl. reflexivity.
Qed.

Record ax_chain_pres : Type := ax_mk_chain_pres {
  ax_cp_next_ra : recalg 1;
  ax_cp_step_ra : recalg 2;
  ax_cp_cost_ra : recalg 1;
  ax_cp_read_ra : recalg 2;
  ax_cp_next_spec : forall s, ra_rel ax_cp_next_ra (ax_cm_scode C s ## vec_nil) (ax_cm_next_val s);
  ax_cp_step_spec : forall s i,
    ra_rel ax_cp_step_ra (ax_cm_scode C s ## ax_cm_icode C i ## vec_nil) (ax_cm_scode C (cstep s i));
  ax_cp_cost_spec : forall i, ra_rel ax_cp_cost_ra (ax_cm_icode C i ## vec_nil) (ccost i);
  ax_cp_read_spec : forall v j, ra_rel ax_cp_read_ra (v ## j ## vec_nil) (ax_cm_read_val v j)
}.

(** The chains fit the fact table of the machine. *)
Definition ax_cm_bounded : Prop := forall s : st, hh s <= 16.

(** Runs. *)
Fixpoint ax_cm_run (s : st) (n : nat) : st :=
  match n with
  | 0 => s
  | S n' => match next s with None => s | Some i => ax_cm_run (cstep s i) n' end
  end.

Fixpoint ax_cm_ledger (s : st) (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match next s with None => 0 | Some i => ccost i + ax_cm_ledger (cstep s i) n' end
  end.

(** The latched height. *)
Fixpoint ax_cm_lat (s : st) (n : nat) : nat :=
  match n with
  | 0 => hh s
  | S n' => max (hh s) (match next s with None => 0 | Some i => ax_cm_lat (cstep s i) n' end)
  end.

Lemma ax_cm_run_halted : forall s n, next s = None -> ax_cm_run s n = s.
Proof. intros s [| n] H; simpl; [reflexivity | rewrite H; reflexivity]. Qed.

Lemma ax_cm_run_add : forall m n s, ax_cm_run s (m + n) = ax_cm_run (ax_cm_run s m) n.
Proof.
  induction m as [| m IH]; intros n s; simpl; [reflexivity |].
  destruct (next s) as [i |] eqn:E; [apply IH |].
  symmetry. apply ax_cm_run_halted. exact E.
Qed.

Lemma ax_cm_run_succ : forall n s,
  ax_cm_run s (S n) =
  match next (ax_cm_run s n) with None => ax_cm_run s n | Some i => cstep (ax_cm_run s n) i end.
Proof.
  intros n s. replace (S n) with (n + 1) by lia. rewrite ax_cm_run_add.
  simpl. destruct (next (ax_cm_run s n)); reflexivity.
Qed.

Lemma ax_cm_ledger_succ : forall n s,
  ax_cm_ledger s (S n) = ax_cm_ledger s n +
  match next (ax_cm_run s n) with None => 0 | Some i => ccost i end.
Proof.
  induction n as [| n IH]; intros s.
  - simpl. destruct (next s); lia.
  - change (ax_cm_ledger s (S (S n))) with
      (match next s with None => 0 | Some i => ccost i + ax_cm_ledger (cstep s i) (S n) end).
    change (ax_cm_ledger s (S n)) with
      (match next s with None => 0 | Some i => ccost i + ax_cm_ledger (cstep s i) n end).
    change (ax_cm_run s (S n)) with
      (match next s with None => s | Some i => ax_cm_run (cstep s i) n end).
    destruct (next s) as [i |] eqn:E.
    + rewrite IH. lia.
    + simpl. rewrite E. lia.
Qed.

Lemma ax_cm_lat_ge_h : forall n s, hh (ax_cm_run s n) <= ax_cm_lat s n.
Proof.
  induction n as [| n IH]; intros s; simpl; [lia |].
  destruct (next s) as [i |] eqn:E.
  - pose proof (IH (cstep s i)). lia.
  - lia.
Qed.

Lemma ax_cm_lat_ge_start : forall n s, hh s <= ax_cm_lat s n.
Proof. intros [| n] s; simpl; lia. Qed.

Lemma ax_cm_lat_succ : forall n s,
  ax_cm_lat s (S n) = max (ax_cm_lat s n) (hh (ax_cm_run s (S n))).
Proof.
  induction n as [| n IH]; intros s.
  - simpl. destruct (next s) as [i |]; simpl; lia.
  - change (ax_cm_lat s (S (S n))) with
      (max (hh s) (match next s with None => 0 | Some i => ax_cm_lat (cstep s i) (S n) end)).
    change (ax_cm_lat s (S n)) with
      (max (hh s) (match next s with None => 0 | Some i => ax_cm_lat (cstep s i) n end)).
    change (ax_cm_run s (S (S n))) with
      (match next s with None => s | Some i => ax_cm_run (cstep s i) (S n) end).
    destruct (next s) as [i |] eqn:E.
    + rewrite IH. lia.
    + pose proof (ax_cm_lat_ge_start n s). pose proof (ax_cm_lat_ge_start (S n) s).
      simpl in *. lia.
Qed.

Lemma ax_cm_lat_le : ax_cm_bounded -> forall n s, ax_cm_lat s n <= 16.
Proof.
  intros Hb n. induction n as [| n IH]; intros s; simpl; [apply Hb |].
  destruct (next s) as [i |]; [pose proof (IH (cstep s i)); pose proof (Hb s); lia | pose proof (Hb s); lia].
Qed.

Lemma ax_cm_run_some : forall s i n, next s = Some i -> ax_cm_run s (S n) = ax_cm_run (cstep s i) n.
Proof. intros s i n E. simpl. rewrite E. reflexivity. Qed.

(** Level j is latched after n steps exactly when some state of the first
    n + 1 reaches it. *)
Lemma ax_cm_lat_iff : forall n s j,
  j <= ax_cm_lat s n <-> exists i, i <= n /\ j <= hh (ax_cm_run s i).
Proof.
  induction n as [| n IH]; intros s j.
  - simpl. split; [intros H; exists 0; split; [lia | exact H] |].
    intros [i [Hi H]]. assert (i = 0) by lia. subst i. exact H.
  - change (ax_cm_lat s (S n)) with
      (max (hh s) (match next s with None => 0 | Some i => ax_cm_lat (cstep s i) n end)).
    destruct (next s) as [i |] eqn:E.
    + split.
      * intros H. destruct (le_lt_dec j (hh s)) as [Hj | Hj].
        -- exists 0. split; [lia | exact Hj].
        -- assert (Hj' : j <= ax_cm_lat (cstep s i) n) by lia.
           destruct (proj1 (IH (cstep s i) j) Hj') as [i' [Hi' Hh]].
           exists (S i'). split; [lia |]. rewrite (ax_cm_run_some s i i' E). exact Hh.
      * intros [i' [Hi' Hh]]. destruct i' as [| i'].
        -- simpl in Hh. lia.
        -- rewrite (ax_cm_run_some s i i' E) in Hh.
           assert (Hc : j <= ax_cm_lat (cstep s i) n) by (apply IH; exists i'; split; [lia | exact Hh]).
           lia.
    + split.
      * intros H. exists 0. split; [lia | simpl; lia].
      * intros [i' [Hi' Hh]]. rewrite (ax_cm_run_halted s i' E) in Hh. lia.
Qed.

(** The heights along the run from s0 are at most 16. *)
Definition ax_cm_bounded_from (s0 : st) : Prop := forall n, hh (ax_cm_run s0 n) <= 16.

Lemma ax_cm_bounded_of : ax_cm_bounded -> forall s0, ax_cm_bounded_from s0.
Proof. intros H s0 n. apply H. Qed.

Lemma ax_cm_lat_le_from : forall s0, ax_cm_bounded_from s0 -> forall n, ax_cm_lat s0 n <= 16.
Proof.
  intros s0 H n. destruct (le_lt_dec (ax_cm_lat s0 n) 16) as [Hle | Hgt]; [exact Hle |].
  exfalso. destruct (proj1 (ax_cm_lat_iff n s0 17) ltac:(lia)) as [i [_ Hi]].
  pose proof (H i). lia.
Qed.

Lemma ax_cm_lat_mono : forall n s, ax_cm_lat s n <= ax_cm_lat s (S n).
Proof. intros n s. rewrite ax_cm_lat_succ. lia. Qed.

(** The guest's ledger. *)
Definition ax_cm_step_cost (s : st) : nat :=
  match next s with None => 0 | Some i => ccost i end.

Fixpoint ax_cm_gledger (s0 : st) (n : nat) : nat :=
  match n with
  | 0 => 3 * hh s0
  | S n' => ax_cm_gledger s0 n' +
            max (ax_cm_step_cost (ax_cm_run s0 n')) (3 * (ax_cm_lat s0 (S n') - ax_cm_lat s0 n'))
  end.

Definition ax_cm_surcharge (s0 : st) (n : nat) : nat := ax_cm_gledger s0 n - ax_cm_ledger s0 n.

Lemma ax_cm_gledger_ge : forall s0 n, ax_cm_ledger s0 n <= ax_cm_gledger s0 n.
Proof.
  intros s0 n. induction n as [| n IH]; [simpl; lia |].
  cbn [ax_cm_gledger]. rewrite ax_cm_ledger_succ. unfold ax_cm_step_cost. lia.
Qed.

Lemma ax_cm_gledger_le : forall s0 n, ax_cm_gledger s0 n <= ax_cm_ledger s0 n + 3 * ax_cm_lat s0 n.
Proof.
  intros s0 n. induction n as [| n IH]; [simpl; lia |].
  cbn [ax_cm_gledger]. rewrite ax_cm_ledger_succ. unfold ax_cm_step_cost.
  pose proof (ax_cm_lat_mono n s0).
  destruct (next (ax_cm_run s0 n)) as [i |]; lia.
Qed.

Theorem ax_cm_surcharge_le : forall s0 n, ax_cm_surcharge s0 n <= 3 * ax_cm_lat s0 n.
Proof.
  intros s0 n. unfold ax_cm_surcharge. pose proof (ax_cm_gledger_le s0 n). lia.
Qed.

End Chain.

Print Assumptions ax_cm_lat_succ.
Print Assumptions ax_cm_ledger_succ.
Print Assumptions ax_cm_gledger_ge.
Print Assumptions ax_cm_surcharge_le.
