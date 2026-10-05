(** UniversalNoCopy.v: a host that only checks an exact copy of the guest
    counter cannot carry every claim of the small machine.

    The guest is the small machine of EarnedCore.v. The host is any machine
    of EarnedMulti.v, with any property language that has a boolean
    equality and a checker. A fixed host program names finitely many
    properties in its CHECK and COMMIT instructions; put them in a list Q.
    Suppose the host turns each guest property p into a host property
    tr p taken from Q, and that the host check of tr p passes whenever the
    guest check of p passes on the same number. The guest has a property
    PGe n for every n, so two different ones, PGe n and PGe m, go to the
    same host property. Then the guest run

      CHECK (PGe n) A; COMMIT (PGe m) A

    traps on every start, because the guest table holds a fact about
    PGe n and the commit asks for PGe m. The host run

      CHECK (tr (PGe n)) R; COMMIT (tr (PGe m)) R

    on a register R holding exactly the guest's value of A succeeds,
    because both instructions name the same host property. So the facts
    the host commits to cannot sit on a register that only copies the
    guest counter.

    The counting step is proved on its own, twice: a function from nat into
    a finite list is not injective (pigeonhole_not_injective, for any type),
    and when equality is decidable two different numbers have the same
    image (pigeonhole_collision).

    Dependencies: Coq standard library, EarnedCore.v, EarnedMulti.v.
    No axioms, no Admitted.                                                 *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose, as in
   EarnedCore.v: this file imports nothing but the Coq standard library,
   EarnedCore.v and EarnedMulti.v, so anyone can re-check it from a clean
   checkout. Its link to the abstract record, and its reading for the
   interpreter host's property language, live in
   coq/kernel/foundation/UniversalInterpreterLinks.v. *)

From Coq Require Import List Arith Lia Bool.
From Coq Require Import FinFun.
Import ListNotations.
Require Minimal.EarnedCore Minimal.EarnedMulti.

Module C := Minimal.EarnedCore.
Module M := Minimal.EarnedMulti.

(* ================================================================= *)
(* The counting step.                                                 *)
(* ================================================================= *)

(* A function from nat into a finite list is not injective. *)
Theorem pigeonhole_not_injective :
  forall (A : Type) (Q : list A) (f : nat -> A),
  (forall n, In (f n) Q) -> ~ (forall n m, f n = f m -> n = m).
Proof.
  intros A Q f HQ Hinj.
  set (L := map f (seq 0 (S (length Q)))).
  assert (Hnd : NoDup L).
  { apply Injective_map_NoDup; [exact Hinj | apply seq_NoDup]. }
  assert (Hinc : incl L Q).
  { intros x Hx. apply in_map_iff in Hx as [n [<- _]]. apply HQ. }
  pose proof (NoDup_incl_length Hnd Hinc) as Hle.
  unfold L in Hle. rewrite map_length, seq_length in Hle. lia.
Qed.

Lemma collide :
  forall (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y})
         (f : nat -> A) (ns : list nat) (Q : list A),
  NoDup ns -> (forall n, In n ns -> In (f n) Q) -> length Q < length ns ->
  exists n m, n <> m /\ f n = f m.
Proof.
  intros A eq_dec f ns. induction ns as [| a ns IH]; intros Q Hnd Hin Hlen.
  - simpl in Hlen. lia.
  - inversion Hnd as [| ? ? Hna Hnd']; subst.
    destruct (in_dec eq_dec (f a) (map f ns)) as [Hy | Hn].
    + apply in_map_iff in Hy as [m [Hfm Hm]].
      exists a, m. split; [intros <-; contradiction | symmetry; exact Hfm].
    + apply (IH (remove eq_dec (f a) Q) Hnd').
      * intros m Hm. apply in_in_remove.
        -- intros E. apply Hn. rewrite <- E. apply in_map. exact Hm.
        -- apply Hin. right. exact Hm.
      * pose proof (remove_length_lt eq_dec Q (f a) (Hin a (or_introl eq_refl))).
        simpl in Hlen. lia.
Qed.

(* With decidable equality, two different numbers have the same image. *)
Theorem pigeonhole_collision :
  forall (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y})
         (Q : list A) (f : nat -> A),
  (forall n, In (f n) Q) -> exists n m, n <> m /\ f n = f m.
Proof.
  intros A eq_dec Q f HQ.
  apply (collide A eq_dec f (seq 0 (S (length Q))) Q).
  - apply seq_NoDup.
  - intros n _. apply HQ.
  - rewrite seq_length. lia.
Qed.

(* ================================================================= *)
(* The guest run traps on every start.                                *)
(* ================================================================= *)

Definition guest (n m : nat) : list C.instr :=
  [C.CHECK (C.PGe n) C.CA; C.COMMIT (C.PGe m) C.CA].

(* The check passes when A >= n: the trap, if any, is at the commit. *)
Lemma guest_check_passes : forall n m a b, n <= a ->
  C.err (C.core_of (C.run_prog 1 (guest n m) (C.start a b))) = false.
Proof.
  intros n m a b Hle. apply Nat.leb_le in Hle.
  cbn. unfold C.check_ok. cbn. rewrite Hle. reflexivity.
Qed.

(* The commit asks for PGe m, the table holds only PGe n: a trap on every
   start, whether or not the check passed. *)
Lemma guest_traps : forall n m a b, n <> m ->
  C.err (C.core_of (C.run_prog 2 (guest n m) (C.start a b))) = true.
Proof.
  intros n m a b Hnm.
  assert (Hmn : Nat.eqb m n = false) by (apply Nat.eqb_neq; auto).
  unfold C.run_prog, C.step, C.next_instr, C.exec, C.cexec. cbn.
  unfold C.check_ok. cbn. destruct (Nat.leb n a); cbn.
  - unfold C.commit_ok, C.fact_eqb. cbn. rewrite Hmn. reflexivity.
  - reflexivity.
Qed.

(* ================================================================= *)
(* The host run on an exact copy succeeds.                            *)
(* ================================================================= *)

Section Host.

Context {hprop : Type}.
Variable hprop_eqb : hprop -> hprop -> bool.
Hypothesis hprop_eqb_eq : forall p q, hprop_eqb p q = true <-> p = q.
Variable heval : hprop -> nat -> bool.

Definition hprop_dec : forall p q : hprop, {p = q} + {p <> q}.
Proof.
  intros p q. destruct (hprop_eqb p q) eqn:E.
  - left. apply hprop_eqb_eq. exact E.
  - right. intros H. apply hprop_eqb_eq in H. congruence.
Defined.

(* CHECK q R then COMMIT q R, from an untrapped state with room in the
   table, where q passes on R's value: no trap, and the channel names
   the claim q about R's current version. *)
Lemma host_same_prop_succeeds : forall (s : @M.state hprop) q R,
  M.err (M.core_of s) = false ->
  length (M.facts (M.core_of s)) < M.fact_cap ->
  heval q (M.vals (M.core_of s) R) = true ->
  let s' := M.run hprop_eqb heval [M.CHECK q R; M.COMMIT q R] s in
  M.err (M.core_of s') = false /\
  M.chan (M.core_of s') = Some (M.mkfact q R (M.vers (M.core_of s) R)).
Proof.
  intros s q R Herr Hcap Hq.
  assert (Hck : M.check_ok heval (M.core_of s) q R = true).
  { unfold M.check_ok. rewrite Herr, Hq. apply Nat.ltb_lt in Hcap.
    rewrite Hcap. reflexivity. }
  assert (Hf : M.fact_eqb hprop_eqb (M.claim (M.record_fact (M.core_of s)
             (M.claim (M.core_of s) q R)) q R) (M.claim (M.core_of s) q R) = true).
  { apply (M.multi_fact_eqb_eq hprop_eqb hprop_eqb_eq). reflexivity. }
  set (k1 := M.record_fact (M.core_of s) (M.claim (M.core_of s) q R)).
  assert (H1 : M.cexec hprop_eqb heval (M.core_of s) (M.CHECK q R) = k1).
  { unfold M.cexec. rewrite Herr, Hck. reflexivity. }
  assert (H2 : M.cexec hprop_eqb heval k1 (M.COMMIT q R)
               = M.commit_to k1 (M.claim k1 q R)).
  { unfold M.cexec, k1. cbn [M.err M.record_fact]. rewrite Herr.
    unfold M.commit_ok. cbn [M.err M.record_fact M.facts existsb].
    rewrite Hf, Herr. reflexivity. }
  cbn [M.run M.exec M.core_of]. rewrite H1, H2.
  split; [exact Herr | reflexivity].
Qed.

(* The N2 fact. Any fixed host program names a finite list Q of host
   properties. If guest properties go to host properties in Q by a
   function tr, and the host check of tr p passes whenever the guest
   check of p passes, then there are two different guest properties
   PGe n and PGe m with the same image, the guest run
   CHECK (PGe n) A; COMMIT (PGe m) A traps on every start, and on every
   start with A >= n the guest check passes while the host run
   CHECK (tr (PGe n)) R; COMMIT (tr (PGe m)) R, on any untrapped host
   state with room in its table whose register R holds exactly the
   guest's value of A, succeeds. *)
Theorem no_exact_copy_host :
  forall (Q : list hprop) (tr : C.prop -> hprop),
  (forall p, In (tr p) Q) ->
  (forall p v, C.eval p v = true -> heval (tr p) v = true) ->
  exists n m,
    n <> m /\ C.PGe n <> C.PGe m /\ tr (C.PGe n) = tr (C.PGe m) /\
    (forall a b,
       C.err (C.core_of (C.run_prog 2 (guest n m) (C.start a b))) = true) /\
    (forall a b (R : nat) (s : @M.state hprop),
       n <= a ->
       M.vals (M.core_of s) R = a ->
       M.err (M.core_of s) = false ->
       length (M.facts (M.core_of s)) < M.fact_cap ->
       C.err (C.core_of (C.run_prog 1 (guest n m) (C.start a b))) = false /\
       C.err (C.core_of (C.run_prog 2 (guest n m) (C.start a b))) = true /\
       let s' := M.run hprop_eqb heval
                   [M.CHECK (tr (C.PGe n)) R; M.COMMIT (tr (C.PGe m)) R] s in
       M.err (M.core_of s') = false /\
       M.chan (M.core_of s') =
         Some (M.mkfact (tr (C.PGe m)) R (M.vers (M.core_of s) R))).
Proof.
  intros Q tr HQ Hsound.
  destruct (pigeonhole_collision hprop hprop_dec Q (fun n => tr (C.PGe n))
              (fun n => HQ (C.PGe n))) as [n [m [Hnm Heq]]].
  cbn beta in Heq.
  exists n, m. split; [exact Hnm |]. split; [congruence |].
  split; [exact Heq |]. split.
  - intros a b. apply guest_traps. exact Hnm.
  - intros a b R s Hle Hval Herr Hcap.
    split; [apply guest_check_passes; exact Hle |].
    split; [apply guest_traps; exact Hnm |].
    rewrite <- Heq. apply host_same_prop_succeeds; [exact Herr | exact Hcap |].
    rewrite Hval. apply Hsound. cbn. apply Nat.leb_le. exact Hle.
Qed.

End Host.

Print Assumptions pigeonhole_not_injective.
Print Assumptions pigeonhole_collision.
Print Assumptions guest_check_passes.
Print Assumptions guest_traps.
Print Assumptions host_same_prop_succeeds.
Print Assumptions no_exact_copy_host.
