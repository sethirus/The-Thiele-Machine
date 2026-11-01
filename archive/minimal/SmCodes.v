(** SmCodes.v: numbers for the programs of the host machine.

    The host machine is EarnedMulti.v with the property language of
    UniversalCodes.v: one property, PSlot. Its instructions are written here
    as a plain inductive type [sm_ki] (no type parameter), with a translation
    [sm_of_ki] to the host's own instructions and back [sm_to_ki].

    Numbers. pair m n is (2n + 1) * 2^m, as in UniversalCodes.v.
      sm_kcode i       the number of an instruction: INC r is pair 0 r,
                       DEC r j is pair 1 (pair r j), HALT pair 2 0,
                       CHECK r pair 3 r, COMMIT r pair 4 r, CERTIFY
                       pair 5 0.
      sm_kdec x        reads any number back as an instruction; a number
                       that is no instruction's code reads as HALT.
      sm_lencode l     a list of numbers as one number: [] is 0 and
                       x :: t is pair x (sm_lencode t). sm_ldecode reads
                       any number back as a list.
      sm_hcode P       the number of a host program; sm_hdecode reads any
                       number back as a host program, and
                       sm_hdecode (sm_hcode P) = P  [sm_hdecode_hcode].

    Every function here is a plain recursion over numbers, booleans, pairs,
    options and lists, so it can be turned into a term of the lambda
    calculus L in SmEvalL.v. Each is proved equal to the matching function
    of UniversalCodes.v where one exists.

    Dependencies: Coq standard library, EarnedCore.v, EarnedGeneric.v,
    EarnedMulti.v, UniversalCodes.v and SmHostBlocks.v. No axioms and no
    unfinished proofs.                                                              *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the host machine, here the numbers that write a program of the host machine of EarnedMulti.v.
   The host machine's link to the abstract record (a CertificationSystem
   with the trace floor, a Thiele-complete machine, and the halting problem
   of U) lives in UniversalInterpreterLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedMulti Minimal.UniversalCodes.
Require Import Minimal.SmHostBlocks.
Module M := Minimal.EarnedMulti.
Module UC := Minimal.UniversalCodes.
Unset Implicit Arguments.

Local Notation hinstr := (@M.instr UC.hprop).

(* ================================================================= *)
(* Halving, and pairs read back.                                      *)
(* ================================================================= *)

Fixpoint sm_hb (n : nat) : nat * bool :=
  match n with
  | 0 => (0, false)
  | S k => let (h, b) := sm_hb k in if b then (S h, false) else (h, true)
  end.

Definition sm_bit (b : bool) : nat := if b then 1 else 0.

Lemma sm_hb_correct : forall n, n = 2 * fst (sm_hb n) + sm_bit (snd (sm_hb n)).
Proof.
  induction n as [| k IH]; [reflexivity |].
  simpl. destruct (sm_hb k) as [h b]. simpl in *.
  destruct b; simpl in *; lia.
Qed.

Lemma sm_hb_unique : forall h b, sm_hb (sm_bit b + 2 * h) = (h, b).
Proof.
  intros h b. pose proof (sm_hb_correct (sm_bit b + 2 * h)) as E.
  destruct (sm_hb (sm_bit b + 2 * h)) as [h' b'] eqn:Ehb. simpl in E.
  destruct b, b'; unfold sm_bit in E; simpl in E; f_equal; lia.
Qed.

Lemma sm_hb_spec : forall n, sm_hb n = (Nat.div2 n, Nat.odd n).
Proof.
  intro n. pose proof (Nat.div2_odd n) as E.
  rewrite E at 1. replace (Nat.b2n (Nat.odd n)) with (sm_bit (Nat.odd n))
    by (destruct (Nat.odd n); reflexivity).
  rewrite Nat.add_comm. apply sm_hb_unique.
Qed.

Fixpoint sm_unp (fuel x m : nat) : option (nat * nat) :=
  match fuel with
  | 0 => None
  | S f =>
      match x with
      | 0 => None
      | S _ =>
          match sm_hb x with
          | (h, true) => Some (m, h)
          | (h, false) => sm_unp f h (S m)
          end
      end
  end.

Lemma sm_unp_eq : forall f x m, sm_unp f x m = UC.unp f x m.
Proof.
  induction f as [| f IH]; intros x m; [reflexivity |].
  destruct x as [| x']; [reflexivity |].
  change (UC.unp (S f) (S x') m) with
    (if Nat.odd (S x') then Some (m, Nat.div2 (S x'))
     else UC.unp f (Nat.div2 (S x')) (S m)).
  change (sm_unp (S f) (S x') m) with
    (match sm_hb (S x') with (h, true) => Some (m, h) | (h, false) => sm_unp f h (S m) end).
  rewrite sm_hb_spec.
  destruct (Nat.odd (S x')); [reflexivity | apply IH].
Qed.

Definition sm_unpair (x : nat) : option (nat * nat) := sm_unp x x 0.

Lemma sm_unpair_eq : forall x, sm_unpair x = UC.unpair x.
Proof. intro x. apply sm_unp_eq. Qed.

Lemma sm_unpair_pair : forall m n, sm_unpair (UC.pair m n) = Some (m, n).
Proof. intros. rewrite sm_unpair_eq. apply UC.unpair_pair. Qed.

Lemma sm_unpair_zero : sm_unpair 0 = None.
Proof. reflexivity. Qed.

Lemma sm_pair_ge : forall m n, S n <= UC.pair m n.
Proof.
  intros m n. unfold UC.pair. pose proof (UC.pow2_pos m). nia.
Qed.

(* ================================================================= *)
(* Lists of numbers as one number.                                    *)
(* ================================================================= *)

Fixpoint sm_lencode (l : list nat) : nat :=
  match l with [] => 0 | x :: t => UC.pair x (sm_lencode t) end.

Fixpoint sm_ldec (fuel v : nat) : list nat :=
  match fuel with
  | 0 => []
  | S f => match sm_unpair v with None => [] | Some (x, t) => x :: sm_ldec f t end
  end.

Definition sm_ldecode (v : nat) : list nat := sm_ldec v v.

Lemma sm_lencode_ge : forall l, length l <= sm_lencode l.
Proof.
  induction l as [| x t IH]; simpl; [lia |]. pose proof (sm_pair_ge x (sm_lencode t)). lia.
Qed.

Lemma sm_ldec_encode : forall l f, length l <= f -> sm_ldec f (sm_lencode l) = l.
Proof.
  induction l as [| x t IH]; intros f Hf.
  - destruct f; reflexivity.
  - destruct f as [| f]; [simpl in Hf; lia |]. simpl.
    rewrite sm_unpair_pair. rewrite IH by (simpl in Hf; lia). reflexivity.
Qed.

Theorem sm_ldecode_encode : forall l, sm_ldecode (sm_lencode l) = l.
Proof. intro l. apply sm_ldec_encode, sm_lencode_ge. Qed.

(* ================================================================= *)
(* Instructions.                                                      *)
(* ================================================================= *)

Inductive sm_ki : Type :=
| sm_KInc (r : nat)
| sm_KDec (r j : nat)
| sm_KHalt
| sm_KCheck (r : nat)
| sm_KCommit (r : nat)
| sm_KCertify.

Definition sm_kcode (i : sm_ki) : nat :=
  match i with
  | sm_KInc r => UC.pair 0 r
  | sm_KDec r j => UC.pair 1 (UC.pair r j)
  | sm_KHalt => UC.pair 2 0
  | sm_KCheck r => UC.pair 3 r
  | sm_KCommit r => UC.pair 4 r
  | sm_KCertify => UC.pair 5 0
  end.

Definition sm_kdec2 (a : nat) : sm_ki :=
  match sm_unpair a with Some (r, j) => sm_KDec r j | None => sm_KHalt end.

Definition sm_kdec_op (o a : nat) : sm_ki :=
  match o with
  | 0 => sm_KInc a
  | S o1 =>
      match o1 with
      | 0 => sm_kdec2 a
      | S o2 =>
          match o2 with
          | 0 => sm_KHalt
          | S o3 =>
              match o3 with
              | 0 => sm_KCheck a
              | S o4 => match o4 with 0 => sm_KCommit a | S o5 => match o5 with 0 => sm_KCertify | S _ => sm_KHalt end end
              end
          end
      end
  end.

Definition sm_kdec (x : nat) : sm_ki :=
  match sm_unpair x with Some (o, a) => sm_kdec_op o a | None => sm_KHalt end.

Theorem sm_kdec_kcode : forall i, sm_kdec (sm_kcode i) = i.
Proof.
  intros []; unfold sm_kdec, sm_kcode; rewrite sm_unpair_pair; try reflexivity.
  simpl. unfold sm_kdec2. rewrite sm_unpair_pair. reflexivity.
Qed.

(* ================================================================= *)
(* Programs.                                                          *)
(* ================================================================= *)

Definition sm_kpcode (P : list sm_ki) : nat := sm_lencode (map sm_kcode P).

Definition sm_kpdec (n : nat) : list sm_ki := map sm_kdec (sm_ldecode n).

Theorem sm_kpdec_kpcode : forall P, sm_kpdec (sm_kpcode P) = P.
Proof.
  intro P. unfold sm_kpdec, sm_kpcode. rewrite sm_ldecode_encode, map_map.
  rewrite (map_ext _ (fun i => i)) by apply sm_kdec_kcode. apply map_id.
Qed.

(* ================================================================= *)
(* The host's own instructions.                                       *)
(* ================================================================= *)

Definition sm_of_ki (i : sm_ki) : hinstr :=
  match i with
  | sm_KInc r => M.INC r
  | sm_KDec r j => M.DEC r j
  | sm_KHalt => M.HALT
  | sm_KCheck r => M.CHECK UC.PSlot r
  | sm_KCommit r => M.COMMIT UC.PSlot r
  | sm_KCertify => M.CERTIFY
  end.

Definition sm_to_ki (i : hinstr) : sm_ki :=
  match i with
  | M.INC r => sm_KInc r
  | M.DEC r j => sm_KDec r j
  | M.HALT => sm_KHalt
  | M.CHECK _ r => sm_KCheck r
  | M.COMMIT _ r => sm_KCommit r
  | M.CERTIFY => sm_KCertify
  end.

Lemma sm_of_to_ki : forall i, sm_of_ki (sm_to_ki i) = i.
Proof. intros [r | r j | | [] r | [] r |]; reflexivity. Qed.

Lemma sm_to_of_ki : forall i, sm_to_ki (sm_of_ki i) = i.
Proof. intros []; reflexivity. Qed.

Lemma sm_map_of_to : forall P, map sm_of_ki (map sm_to_ki P) = P.
Proof.
  intro P. rewrite map_map. rewrite (map_ext _ (fun i => i)) by apply sm_of_to_ki. apply map_id.
Qed.

Lemma sm_map_to_of : forall P, map sm_to_ki (map sm_of_ki P) = P.
Proof.
  intro P. rewrite map_map. rewrite (map_ext _ (fun i => i)) by apply sm_to_of_ki. apply map_id.
Qed.

(* The number of a host program, and any number read back as one. *)
Definition sm_hcode (P : list hinstr) : nat := sm_kpcode (map sm_to_ki P).

Definition sm_hdecode (n : nat) : list hinstr := map sm_of_ki (sm_kpdec n).

Theorem sm_hdecode_hcode : forall P, sm_hdecode (sm_hcode P) = P.
Proof. intro P. unfold sm_hdecode, sm_hcode. rewrite sm_kpdec_kpcode. apply sm_map_of_to. Qed.

Lemma sm_hcode_of : forall P, sm_hcode (map sm_of_ki P) = sm_kpcode P.
Proof. intro P. unfold sm_hcode. rewrite sm_map_to_of. reflexivity. Qed.

Theorem sm_hcode_inj : forall P Q, sm_hcode P = sm_hcode Q -> P = Q.
Proof.
  intros P Q H. rewrite <- (sm_hdecode_hcode P), <- (sm_hdecode_hcode Q), H. reflexivity.
Qed.

(* ================================================================= *)
(* Relocation, on sm_ki programs.                                        *)
(* ================================================================= *)

Definition sm_kri (off len : nat) (i : sm_ki) : sm_ki :=
  match i with sm_KDec r j => sm_KDec r (sm_rj off len j) | _ => i end.

Definition sm_kreloc (off : nat) (B : list sm_ki) : list sm_ki := map (sm_kri off (length B)) B.

Lemma sm_kreloc_of : forall off B,
  map sm_of_ki (sm_kreloc off B) = sm_reloc off (map sm_of_ki B).
Proof.
  intros off B. unfold sm_kreloc, sm_reloc. rewrite !map_map, map_length.
  apply map_ext. intros []; reflexivity.
Qed.

(* ================================================================= *)
(* Specialisation: fix register 2 to c.                               *)
(* ================================================================= *)

(* c copies of INC 2, then the program numbered c, moved down by c lines.
   Started on x, it runs the program numbered c with x in register 1 and
   c in register 2. *)
Definition sm_spec (c : nat) (V : list hinstr) : list hinstr := sm_incs 2 c ++ sm_reloc c V.

Definition sm_kspec_prog (c : nat) : list sm_ki := repeat (sm_KInc 2) c ++ sm_kreloc c (sm_kpdec c).

Definition sm_kspec (c : nat) : nat := sm_kpcode (sm_kspec_prog c).

Lemma sm_kspec_prog_of : forall c, map sm_of_ki (sm_kspec_prog c) = sm_spec c (sm_hdecode c).
Proof.
  intro c. unfold sm_kspec_prog, sm_spec, sm_hdecode. rewrite map_app, sm_kreloc_of.
  f_equal. unfold sm_incs. rewrite map_repeat. reflexivity.
Qed.

Theorem sm_kspec_code : forall c, sm_kspec c = sm_hcode (sm_spec c (sm_hdecode c)).
Proof.
  intro c. rewrite <- sm_kspec_prog_of, sm_hcode_of. reflexivity.
Qed.

Print Assumptions sm_hdecode_hcode.
Print Assumptions sm_kspec_code.
