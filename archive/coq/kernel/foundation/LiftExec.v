(** LiftExec: the two-counter step as a function on numbers, a universal base
    on numbers, and its computability in the lambda calculus L.

    A configuration (pc, (a, b)) is the number pair pc (pair a b), where pair
    is the pairing of UniversalCodes.v.  An instruction CINC r or CDEC r j is
    the number pair 0 (pair r 0) or pair 1 (pair r j).  [lift_ex_f i s] is the
    number of the configuration reached by executing the instruction numbered
    i on the configuration numbered s, and s itself when either number is not
    a code.

    [lift_ex_machine] is the machine on numbers: its states are numbers, its moves
    are numbers, its step is [lift_ex_f].  It has a universal base in the sense of
    ThieleComplete.v ([lift_ex_base]).  Its step function is L-computable
    ([lift_ex_L_computable]), by the extraction tactic of the vendored library, so
    by the vendored equivalence of models it is computable in each of the
    models of LiftModels.v.

    No axioms and no unfinished proofs.                                                  *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.L Require Import L Tactics.LTactics Datatypes.LNat Datatypes.LOptions
  Datatypes.LProd Datatypes.LBool Datatypes.Lists.
From Kernel Require Import SmFuel SmEvalL.
Require Minimal.ThieleComplete.
Require Minimal.UniversalCodes.
Require Import Minimal.SmCodes.
Module T := Minimal.ThieleComplete.
Module UC := Minimal.UniversalCodes.

(** * Codes *)

Definition lift_ex_rcode (r : T.reg) : nat := match r with T.RA => 0 | T.RB => 1 end.

Definition lift_ex_icode (i : T.cm_instr) : nat :=
  match i with
  | T.CINC r => UC.pair 0 (UC.pair (lift_ex_rcode r) 0)
  | T.CDEC r j => UC.pair 1 (UC.pair (lift_ex_rcode r) j)
  end.

Definition lift_ex_scode (x : T.cm_conf) : nat :=
  UC.pair (fst x) (UC.pair (fst (snd x)) (snd (snd x))).

(** The step on numbers, written with numbers and pairs only. *)
Definition lift_ex_f (i s : nat) : nat :=
  match sm_unpair i with
  | None => s
  | Some (k, w) =>
    match sm_unpair w with
    | None => s
    | Some (r, j) =>
      match sm_unpair s with
      | None => s
      | Some (pc, w2) =>
        match sm_unpair w2 with
        | None => s
        | Some (a, b) =>
          match k with
          | 0 => UC.pair (S pc) (UC.pair (if Nat.eqb r 0 then S a else a)
                                         (if Nat.eqb r 0 then b else S b))
          | _ =>
            match r with
            | 0 => match a with
                   | 0 => UC.pair (S pc) (UC.pair 0 b)
                   | S a' => UC.pair j (UC.pair a' b)
                   end
            | _ => match b with
                   | 0 => UC.pair (S pc) (UC.pair a 0)
                   | S b' => UC.pair j (UC.pair a b')
                   end
            end
          end
        end
      end
    end
  end.

(** The window: read a number back as a configuration. *)
Definition lift_ex_sdec (s : nat) : T.cm_conf :=
  match sm_unpair s with
  | None => (0, (0, 0))
  | Some (pc, w) =>
    match sm_unpair w with
    | None => (pc, (0, 0))
    | Some (a, b) => (pc, (a, b))
    end
  end.

Lemma lift_ex_sdec_scode : forall x, lift_ex_sdec (lift_ex_scode x) = x.
Proof.
  intros [pc [a b]]. unfold lift_ex_sdec, lift_ex_scode. simpl.
  rewrite sm_unpair_pair, sm_unpair_pair. reflexivity.
Qed.

Lemma lift_ex_f_exec : forall i x, lift_ex_f (lift_ex_icode i) (lift_ex_scode x) = lift_ex_scode (T.cm_exec i x).
Proof.
  intros i [pc [a b]]. unfold lift_ex_f, lift_ex_icode, lift_ex_scode. simpl.
  destruct i as [r | r j]; simpl;
    rewrite !sm_unpair_pair; destruct r; simpl; rewrite ?sm_unpair_pair.
  - reflexivity.
  - reflexivity.
  - destruct a; simpl; reflexivity.
  - destruct b; simpl; reflexivity.
Qed.

(** * The machine on numbers and its universal base *)

Definition lift_ex_g (s i : nat) : nat := lift_ex_f i s.

Definition lift_ex_machine : T.machine :=
  T.mk_machine nat nat lift_ex_g (fun _ => 0) (fun _ => false).

Definition lift_ex_live (s : nat) : Prop := exists x, s = lift_ex_scode x.

Lemma lift_ex_sim : forall s i, lift_ex_live s ->
  lift_ex_sdec (lift_ex_g s (lift_ex_icode i)) = T.cm_exec i (lift_ex_sdec s) /\ lift_ex_live (lift_ex_g s (lift_ex_icode i)).
Proof.
  intros s i [x ->]. unfold lift_ex_g. rewrite lift_ex_f_exec, !lift_ex_sdec_scode.
  split; [reflexivity | exists (T.cm_exec i x); reflexivity].
Qed.

Definition lift_ex_base : T.universal_base lift_ex_machine :=
  T.mk_ub lift_ex_machine lift_ex_sdec lift_ex_live lift_ex_icode (fun a b => lift_ex_scode (1, (a, b)))
    (fun a b => lift_ex_sdec_scode (1, (a, b)))
    (fun a b => ex_intro _ (1, (a, b)) eq_refl)
    lift_ex_sim.

(** * Computability in L *)

Instance lift_term_ex_f : computable lift_ex_f. Proof. extract. Qed.
Instance lift_term_ex_g : computable lift_ex_g. Proof. extract. Qed.

Definition lift_ex_ff (d n s i : nat) : option nat := Some (lift_ex_g s i).
Instance lift_term_ex_ff : computable lift_ex_ff. Proof. extract. Qed.

(** The step relation of the machine: the number s of a configuration, the
    number i of an instruction, and the number of the next configuration. *)
Definition lift_ex_rel (v : Vector.t nat 2) (m : nat) : Prop :=
  m = T.m_step lift_ex_machine (Vector.hd v) (Vector.hd (Vector.tl v)).

Theorem lift_ex_L_computable : L_computable lift_ex_rel.
Proof.
  assert (H := @sm_L_computable_fuel2 nat _ lift_ex_ff _ 0
                 (fun n n' x c m H _ => H)).
  destruct H as [s Hs]. exists s. intro v. destruct (Hs v) as [H1 H2]. split; [| exact H2].
  intro m. rewrite <- (H1 m). unfold lift_ex_rel, lift_ex_ff. split.
  - intro H. exists 0. rewrite H. reflexivity.
  - intros [n Hn]. injection Hn as <-. reflexivity.
Qed.

Print Assumptions lift_ex_L_computable.
Print Assumptions lift_ex_base.
