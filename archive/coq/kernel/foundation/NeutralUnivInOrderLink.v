(** NeutralUnivInOrderLink.v: NeutralUnivDef.chains_to_fun and
    UMachInOrderGen.in_order build the same kind of increasing matching function
    (both by ConstructiveEpsilon.epsilon_smallest).  UMachInOrderGen's hypotheses
    (a stepping relation Rel) give chains_to_fun's (finite increasing chains),
    so every use of UMachInOrderGen.in_order is also a use of chains_to_fun
    (gen_to_chains, gen_via_chains), and UMachInOrderGen.in_order itself is
    reused here unchanged (gen_direct).  chains_to_fun is the more general:
    it needs only that each finite prefix has SOME increasing chain, which is
    what the two-level composition for U_P (NeutralUnivUP.pchains) provides. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   relates two lemmas about natural numbers, NeutralUnivDef.chains_to_fun
   and UMachInOrderGen.in_order. NeutralUnivDef.v connects it to
   ThieleComplete.v and NeutralComplete.v; it uses no name of the
   foundation chain directly. *)

From Coq Require Import Arith Lia.
Require Import Kernel.UMachInOrderGen.
Require Import Kernel.NeutralUnivDef.

Section Link.
Variable L : nat -> Prop.
Hypothesis Ldec : forall m, {L m} + {~ L m}.
Hypothesis Lprev : forall m, L (S m) -> L m.
Variable D : nat -> nat -> Prop.
Hypothesis Ddec : forall m t, {D m t} + {~ D m t}.
Variable Rel : nat -> nat -> Prop.
Hypothesis RelD : forall m t, L m -> Rel m t -> D m t.
Hypothesis Rel0 : L 0 -> exists t, Rel 0 t.
Hypothesis RelS : forall m t, L (S m) -> Rel m t -> exists t', t < t' /\ Rel (S m) t'.

Lemma gen_to_chains : forall M, L M -> exists l : nat -> nat,
  (forall k, k < M -> l k < l (S k)) /\ (forall k, k <= M -> D k (l k)).
Proof.
  assert (G : forall M, L M -> exists l : nat -> nat,
            (forall k, k < M -> l k < l (S k)) /\ (forall k, k <= M -> Rel k (l k))).
  { induction M as [| M IH]; intros HL.
    - destruct (Rel0 HL) as [t Ht]. exists (fun _ => t). split; [intros; lia |].
      intros k Hk. replace k with 0 by lia. exact Ht.
    - destruct (IH (Lprev M HL)) as (l & Hi & Hr).
      destruct (RelS M (l M) HL (Hr M (le_n M))) as (t & Ht & R).
      exists (fun k => if Nat.leb k M then l k else t). split.
      + intros k Hk. destruct (Nat.leb k M) eqn:E1; destruct (Nat.leb (S k) M) eqn:E2;
          apply Nat.leb_le in E1 || apply Nat.leb_gt in E1;
          apply Nat.leb_le in E2 || apply Nat.leb_gt in E2; try lia.
        * apply Hi. lia.
        * replace k with M by lia. exact Ht.
      + intros k Hk. destruct (Nat.leb k M) eqn:E1.
        * apply Nat.leb_le in E1. apply Hr, E1.
        * apply Nat.leb_gt in E1. replace k with (S M) by lia. exact R. }
  intros M HL. destruct (G M HL) as (l & Hi & Hr). exists l. split; [exact Hi |].
  intros k Hk. apply RelD; [| apply Hr, Hk].
  clear -Lprev HL Hk. induction M as [| M IH]; [replace k with 0 by lia; exact HL |].
  destruct (Nat.eq_dec k (S M)) as [-> | Hne]; [exact HL | apply IH; [apply Lprev, HL | lia]].
Qed.

Theorem gen_via_chains : exists f : nat -> nat,
  (forall m, L (S m) -> f m < f (S m)) /\ (forall m, L m -> D m (f m)).
Proof. exact (chains_to_fun D Ddec L Ldec Lprev gen_to_chains). Qed.

Theorem gen_direct : exists f : nat -> nat,
  (forall m, f m < f (S m)) /\ (forall m, L m -> D m (f m)).
Proof. exact (UMachInOrderGen.in_order L Ldec Lprev D Ddec Rel RelD Rel0 RelS). Qed.

End Link.

Print Assumptions gen_to_chains.
Print Assumptions gen_via_chains.
Print Assumptions gen_direct.
