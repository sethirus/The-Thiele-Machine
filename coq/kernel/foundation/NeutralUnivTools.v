(** NeutralUnivTools.v: helpers for testing the clauses on small classes of CNH
    guests: CNH guest classes, line_raise for mark-free programs, the
    impossibility of line_raise for programs that use MARK, and the
    general "a free move with a fixed point that moves the line elsewhere is
    no counter move, under any register reading" lemma.                  *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   holds helpers about the neutral universal machine of NeutralUnivDef.v on
   the canonical host of NeutralUnivCanon.v. Those two files connect it to
   ThieleComplete.v and NeutralComplete.v; it uses no name of the foundation
   chain directly. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.NeutralUnivBase.
Require Import Kernel.NeutralUnivDef.
Require Import Kernel.NeutralUnivCanon.

(* ================================================================= *)
(* CNH guest classes.                                                 *)
(* ================================================================= *)

Definition cnh_class (I : Type) (Q : I -> list cmove) (st : I -> cst) : gclass :=
  mk_gclass I (fun _ => cst) (fun _ => cmove) (fun i => cnext (Q i)) (fun _ => cstep)
    (fun _ => ccost) (fun _ => cflag) (fun _ => ctoll) st.

Lemma cnh_perm : forall s m, cflag s = true -> cflag (cstep s m) = true.
Proof.
  intros [p r f l] m H. simpl in H. subst f. destruct m as [x | x j | | x | |]; simpl; auto.
  destruct (r x); reflexivity.
Qed.

Definition tick_at (o : option cmove) : bool := match o with Some CTick => true | _ => false end.

Lemma cnh_line_raise_nomark : forall P,
  (forall l r, cfetch P l <> Some (CMark r)) ->
  line_raise CNH cnh_reg P (fun l => tick_at (cfetch P l)).
Proof.
  intros P Hm s m _ Hn K. right. simpl in *. unfold cnext in Hn.
  destruct (cfetch P (cpc s)) as [o |] eqn:E; [| discriminate].
  destruct o as [x | x j | | x | |]; try (injection Hn as <-); try discriminate; simpl in *.
  - exfalso. exact (Hm _ x E).
  - rewrite orb_true_r. reflexivity.
  - rewrite orb_false_r. reflexivity.
Qed.

(* A program that executes MARK r has no line_raise at all. *)
Lemma cnh_mark_not_line : forall P l r, cfetch P l = Some (CMark r) ->
  ~ exists raise, line_raise CNH cnh_reg P raise.
Proof.
  intros P l r E [ra Hra].
  set (s0 := mkcs l (fun _ => 0) false 0). set (s1 := mkcs l (fun _ => 1) false 0).
  assert (N0 : hnext CNH P s0 = Some (CMark r)) by (simpl; unfold cnext; simpl; rewrite E; reflexivity).
  assert (N1 : hnext CNH P s1 = Some (CMark r)) by (simpl; unfold cnext; simpl; rewrite E; reflexivity).
  destruct (Hra s0 _ eq_refl N0 eq_refl) as [T | A0]; [discriminate T |].
  destruct (Hra s1 _ eq_refl N1 eq_refl) as [T | A1]; [discriminate T |].
  simpl in A0, A1. rewrite <- A0 in A1. discriminate A1.
Qed.

(* ================================================================= *)
(* A free move with a fixed point that elsewhere changes what the      *)
(* program does next is no counter move, whatever the register reading.*)
(* ================================================================= *)

Theorem not_counter : forall (H : host) (R : reg_host H) (m : hI H),
  hcost H m = 0 ->
  (exists s0 P0, hstep H s0 m = s0 /\ hnext H P0 s0 <> None) ->
  (exists s1 P1, hnext H P1 (hstep H s1 m) <> hnext H P1 s1 /\ hnext H P1 s1 <> None) ->
  False.
Proof.
  intros H R m Hc (s0 & P0 & F & N0) (s1 & P1 & D & N1).
  assert (E0 : b_err R s0 = false).
  { destruct (b_err R s0) eqn:E; [| reflexivity]. exfalso. apply N0, (b_next_err H R), E. }
  assert (E1 : b_err R s1 = false).
  { destruct (b_err R s1) eqn:E; [| reflexivity]. exfalso. apply N1, (b_next_err H R), E. }
  pose proof (b_cost H R m) as Bc. rewrite Hc in Bc.
  destruct (b_kind R m) as [r | r j | |] eqn:K; [| | | discriminate Bc].
  - destruct (b_inc H R s0 m r E0 K) as (_ & Hp & _). rewrite F in Hp. lia.
  - destruct (b_dec H R s0 m r j E0 K) as (_ & D0). rewrite F in D0.
    destruct (b_reg R s0 r) as [| n] eqn:V.
    + destruct D0 as [Hp _]. lia.
    + destruct D0 as [_ Hr]. specialize (Hr r). unfold upd in Hr. rewrite Nat.eqb_refl, V in Hr. lia.
  - destruct (b_halt H R s1 m K) as (He & Hp & _).
    apply D. apply (b_next H R); assumption.
Qed.


(* A free move that, read through R, increments register x (and leaves y)
   from one untrapped state and increments y (and leaves x) from another, has
   no counter kind: a built-in "execute the guest's next instruction" that
   is INC A here and INC B there is no INC, no DEC and no HALT. *)
Theorem not_counter2 : forall (H : host) (R : reg_host H) (m : hI H) s1 s2 x y,
  hcost H m = 0 -> x <> y -> b_err R s1 = false -> b_err R s2 = false ->
  b_reg R (hstep H s1 m) x = S (b_reg R s1 x) -> b_reg R (hstep H s1 m) y = b_reg R s1 y ->
  b_reg R (hstep H s2 m) y = S (b_reg R s2 y) -> b_reg R (hstep H s2 m) x = b_reg R s2 x ->
  False.
Proof.
  intros H R m s1 s2 x y Hc Hxy E1 E2 A1 B1 A2 B2.
  pose proof (b_cost H R m) as Bc. rewrite Hc in Bc.
  destruct (b_kind R m) as [r | r j | |] eqn:K; [| | | discriminate Bc].
  - destruct (b_inc H R s1 m r E1 K) as (_ & _ & R1). destruct (b_inc H R s2 m r E2 K) as (_ & _ & R2).
    specialize (R1 x). specialize (R2 y). unfold upd in R1, R2.
    destruct (Nat.eqb x r) eqn:Q1; [| lia]. destruct (Nat.eqb y r) eqn:Q2; [| lia].
    apply Nat.eqb_eq in Q1, Q2. congruence.
  - destruct (b_dec H R s1 m r j E1 K) as (_ & D1).
    destruct (b_reg R s1 r) as [| n] eqn:V.
    + destruct D1 as [_ R1]. specialize (R1 x). lia.
    + destruct D1 as [_ R1]. specialize (R1 x). unfold upd in R1.
      destruct (Nat.eqb x r) eqn:Q; [apply Nat.eqb_eq in Q; subst x; lia | lia].
  - destruct (b_halt H R s1 m K) as (_ & _ & R1). specialize (R1 x). lia.
Qed.

(* ================================================================= *)
(* Finite runs.                                                       *)
(* ================================================================= *)

Lemma live_bound : forall (C : gclass) (i : gi C) k m,
  gnext C i (grun i k) = None -> live_before i m -> m <= k.
Proof.
  intros C i k m Hs Hl. destruct (le_lt_dec m k) as [H | H]; [exact H |].
  exfalso. exact (Hl k H Hs).
Qed.

Lemma grun_stop_stays : forall (C : gclass) (i : gi C) k m, k <= m ->
  gnext C i (grun i k) = None -> grun i m = grun i k.
Proof.
  intros C i k m Hkm Hs. unfold grun in *. replace m with (k + (m - k)) by lia.
  rewrite gr_add. apply gr_stop. exact Hs.
Qed.

Print Assumptions cnh_line_raise_nomark.
Print Assumptions cnh_mark_not_line.
Print Assumptions not_counter.
Print Assumptions not_counter2.
