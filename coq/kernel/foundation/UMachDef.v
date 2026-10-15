(** UMachDef.v: the plain definition of a universal Thiele machine, over
    arbitrary guest classes and arbitrary hosts.  It asks for halting,
    matching and the host's own raise, and puts no condition on how the host
    computes.  The cheat of UMachCheatSmall.v meets it; NeutralUnivDef.v
    states the definition with the clauses that exclude it
    ([neutral_universal]).

    The plain definition:
      Fix a class C of Thiele machines, each with its runs from given start
      states. A universal Thiele machine for C is a Thiele machine H, the
      host, with one program P fixed for the whole class and a way to load
      any guest M in C with any start s0 into a start state of H, such that
      the run of P from that loaded state
      (1) halts exactly when M's run from s0 stops;
      (2) passes, in order, through host states that decode to M's states
          along its run, at which the host's flag equals M's reading kept as
          a latch and the host's ledger equals M's ledger plus a surcharge
          bounded by a number fixed for the class;
      (3) raises the host's flag only by the host's own moves, under the
          host's own toll.

    Rendering choices (each one as GENEROUS TO THE DEFINITION'S STRENGTH as
    the words allow, so that a cheat meeting it meets every reading):
      - "Thiele machine": the book's Definition def:certsys (states, moves,
        step, cost, reading, toll).  A "program" is not part of def:certsys;
        a host comes with a type of programs and a fetch [hnext] (None =
        stopped), as the book's machines do.
      - "M's states along its run": the driven run of the guest.  A guest
        class is a family of driven Thiele machines with starts.
      - "decode to M's states": a decode map per instance into an
        observation type [Obs i] of the guest's states, given with the
        class (obs = identity is the strongest reading).
      - "in order": strictly increasing matching times f m (strong form);
        the weak form drops the order (that is all the Coq theorems about
        U and U_P state).
      - surcharge: a natural number <= K.                                    *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   states the plain definition of a universal machine over arbitrary hosts
   and guest classes and imports only the Coq standard library. The files
   that connect it to the small machine and to U and U_P are UMachMeetsU.v,
   UMachCheatSmall.v and NeutralUnivDef.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.

(* ================================================================= *)
(* Guest classes.                                                     *)
(* ================================================================= *)

Record gclass : Type := mk_gclass {
  gi : Type;                                   (* instances: guest + start *)
  gS : gi -> Type;                             (* guest states            *)
  gI : gi -> Type;                             (* guest moves             *)
  gnext : forall i, gS i -> option (gI i);     (* the driver / program    *)
  gstep : forall i, gS i -> gI i -> gS i;
  gcost : forall i, gI i -> nat;
  gread : forall i, gS i -> bool;
  gtoll : forall i s m, gread i s = false -> gread i (gstep i s m) = true -> gcost i m >= 1;
  gstart : forall i, gS i
}.

Section GuestRuns.
Variable C : gclass.
Variable i : gi C.

Fixpoint gr (s : gS C i) (n : nat) : gS C i :=
  match n with
  | 0 => s
  | S n' => match gnext C i s with None => s | Some m => gr (gstep C i s m) n' end
  end.

Fixpoint gl (s : gS C i) (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match gnext C i s with None => 0 | Some m => gcost C i m + gl (gstep C i s m) n' end
  end.

(* M's reading kept as a latch: yes at some state among the first n+1. *)
Fixpoint glatch (s : gS C i) (n : nat) : bool :=
  match n with
  | 0 => gread C i s
  | S n' => glatch s n' || gread C i (gr s (S n'))
  end.

Lemma gr_stop : forall s n, gnext C i s = None -> gr s n = s.
Proof. intros s [| n] H; simpl; [reflexivity | rewrite H; reflexivity]. Qed.

Lemma gl_stop : forall s n, gnext C i s = None -> gl s n = 0.
Proof. intros s [| n] H; simpl; [reflexivity | rewrite H; reflexivity]. Qed.

Lemma gr_add : forall a b s, gr s (a + b) = gr (gr s a) b.
Proof.
  induction a; intros b s; simpl; [reflexivity |].
  destruct (gnext C i s) eqn:E; [apply IHa | symmetry; apply gr_stop; exact E].
Qed.

Lemma gl_add : forall a b s, gl s (a + b) = gl s a + gl (gr s a) b.
Proof.
  induction a; intros b s; simpl; [reflexivity |].
  destruct (gnext C i s) eqn:E; [rewrite IHa; lia | rewrite gl_stop by exact E; reflexivity].
Qed.

Lemma gr_succ : forall n s, gr s (S n) =
  match gnext C i (gr s n) with None => gr s n | Some m => gstep C i (gr s n) m end.
Proof.
  intros n s. replace (S n) with (n + 1) by lia. rewrite gr_add. simpl.
  destruct (gnext C i (gr s n)); reflexivity.
Qed.

Lemma gl_succ : forall n s, gl s (S n) =
  gl s n + match gnext C i (gr s n) with None => 0 | Some m => gcost C i m end.
Proof.
  intros n s. replace (S n) with (n + 1) by lia. rewrite gl_add. simpl.
  destruct (gnext C i (gr s n)); lia.
Qed.

(* The guest has not stopped before step m. *)
Definition live_before (m : nat) : Prop :=
  forall k, k < m -> gnext C i (gr (gstart C i) k) <> None.

Definition grun (m : nat) := gr (gstart C i) m.
Definition gledger (m : nat) := gl (gstart C i) m.
Definition glat (m : nat) := glatch (gstart C i) m.

End GuestRuns.

Arguments gr {C i} s n.
Arguments gl {C i} s n.
Arguments glatch {C i} s n.
Arguments live_before {C} i m.
Arguments grun {C} i m.
Arguments gledger {C} i m.
Arguments glat {C} i m.

(* ================================================================= *)
(* Hosts: Thiele machines with stored programs.                       *)
(* ================================================================= *)

Record host : Type := mk_host {
  hS : Type;
  hI : Type;
  hstep : hS -> hI -> hS;
  hcost : hI -> nat;
  hflag : hS -> bool;
  htoll : forall s m, hflag s = false -> hflag (hstep s m) = true -> hcost m >= 1;
  hP : Type;
  hnext : hP -> hS -> option hI
}.

Section HostRuns.
Variable H : host.
Variable P : hP H.

Fixpoint hr (h : hS H) (n : nat) : hS H :=
  match n with
  | 0 => h
  | S n' => match hnext H P h with None => h | Some m => hr (hstep H h m) n' end
  end.

Fixpoint hl (h : hS H) (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match hnext H P h with None => 0 | Some m => hcost H m + hl (hstep H h m) n' end
  end.

Lemma hr_stop : forall h n, hnext H P h = None -> hr h n = h.
Proof. intros h [| n] E; simpl; [reflexivity | rewrite E; reflexivity]. Qed.

Lemma hl_stop : forall h n, hnext H P h = None -> hl h n = 0.
Proof. intros h [| n] E; simpl; [reflexivity | rewrite E; reflexivity]. Qed.

Lemma hr_add : forall a b h, hr h (a + b) = hr (hr h a) b.
Proof.
  induction a; intros b h; simpl; [reflexivity |].
  destruct (hnext H P h) eqn:E; [apply IHa | symmetry; apply hr_stop; exact E].
Qed.

Lemma hl_add : forall a b h, hl h (a + b) = hl h a + hl (hr h a) b.
Proof.
  induction a; intros b h; simpl; [reflexivity |].
  destruct (hnext H P h) eqn:E; [rewrite IHa; lia | rewrite hl_stop by exact E; reflexivity].
Qed.

Lemma hr_succ : forall n h, hr h (S n) =
  match hnext H P (hr h n) with None => hr h n | Some m => hstep H (hr h n) m end.
Proof.
  intros n h. replace (S n) with (n + 1) by lia. rewrite hr_add. simpl.
  destruct (hnext H P (hr h n)); reflexivity.
Qed.

(* A stopped host stays stopped. *)
Lemma hr_stopped_stays : forall h a b, a <= b -> hnext H P (hr h a) = None -> hr h b = hr h a.
Proof.
  intros h a b Hab E. replace b with (a + (b - a)) by lia. rewrite hr_add.
  apply hr_stop. exact E.
Qed.

(* Clause (3) costs nothing: it follows from the host's toll alone. *)
Theorem clause3_free : forall h n,
  hflag H (hr h n) = false -> hflag H (hr h (S n)) = true ->
  exists m, hnext H P (hr h n) = Some m /\ hcost H m >= 1.
Proof.
  intros h n H0 H1. rewrite hr_succ in H1.
  destruct (hnext H P (hr h n)) as [m |] eqn:E; [| congruence].
  exists m. split; [reflexivity | exact (htoll H _ _ H0 H1)].
Qed.

End HostRuns.

Arguments hr {H} P h n.
Arguments hl {H} P h n.

(* ================================================================= *)
(* The definition.                                                    *)
(* ================================================================= *)

Section Def.
Variable C : gclass.
Variable H : host.
Variable Obs : gi C -> Type.
Variable obs : forall i, gS C i -> Obs i.

Definition clause1 (P : hP H) (h0 : hS H) (i : gi C) : Prop :=
  (exists n, hnext H P (hr P h0 n) = None) <-> (exists m, gnext C i (grun i m) = None).

Definition match_at (K : nat) (P : hP H) (h0 : hS H) (i : gi C)
  (decode : hS H -> Obs i) (n m : nat) : Prop :=
  decode (hr P h0 n) = obs i (grun i m) /\
  hflag H (hr P h0 n) = glat i m /\
  exists s, s <= K /\ hl P h0 n = gledger i m + s.

Definition clause3 (P : hP H) (h0 : hS H) : Prop :=
  forall n, hflag H (hr P h0 n) = false -> hflag H (hr P h0 (S n)) = true ->
    exists m, hnext H P (hr P h0 n) = Some m /\ hcost H m >= 1.

(* Strong form: "passes, in order". *)
Definition universal_thiele (K : nat) : Prop :=
  exists (P : hP H) (load : gi C -> hS H) (decode : forall i, hS H -> Obs i),
  forall i,
    clause1 P (load i) i /\
    (exists f : nat -> nat,
       (forall m, live_before i (S m) -> f m < f (S m)) /\
       (forall m, live_before i m -> match_at K P (load i) i (decode i) (f m) m)) /\
    clause3 P (load i).

(* Weak form: a matching host time for every guest step, no order. *)
Definition universal_thiele_weak (K : nat) : Prop :=
  exists (P : hP H) (load : gi C -> hS H) (decode : forall i, hS H -> Obs i),
  forall i,
    clause1 P (load i) i /\
    (forall m, live_before i m -> exists n, match_at K P (load i) i (decode i) n m) /\
    clause3 P (load i).

Theorem strong_weak : forall K, universal_thiele K -> universal_thiele_weak K.
Proof.
  intros K (P & load & decode & Hall). exists P, load, decode. intros i.
  destruct (Hall i) as (H1 & (f & _ & Hm) & H3). split; [exact H1 |]. split; [| exact H3].
  intros m Hl. exists (f m). apply Hm, Hl.
Qed.

End Def.
