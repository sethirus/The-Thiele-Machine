(** UniversalCodes.v: numbers for the guest machine's parts, and the one
    property the host machine checks.

    The guest is the small machine of EarnedCore.v. The host is the machine
    of EarnedMulti.v, with a counter for every natural number. This file
    fixes how a guest program, a guest property and a guest claim are
    written as numbers the host can hold in its counters.

      pair m n      the number (2n + 1) * 2^m. Every positive number is
                    pair m n for exactly one m and n; 0 is pair of nothing.
      unpair x      the inverse: Some (m, n) when x = pair m n, None at 0.
      pcode p       the number of a guest property: PZero 0, PEven 1,
                    PGe n is n + 2. pdec is its inverse.
      ccode c       the number of a guest counter: A 0, B 1.
      icode i       the number of a guest instruction, a pair of an opcode
                    (0 INC, 1 DEC, 2 HALT, 3 CHECK, 4 COMMIT, 5 CERTIFY)
                    and its operands. idecode reads it back, and reads
                    every number that is no instruction's code as None.
      prog_code P   the list of instruction codes of P as one number, by
                    the list code of EarnedGeneric.v: encode [] = 0 and
                    encode (x :: t) = pair x (encode t).
      fetch_code    unpacks a program code k times and reads the head:
                    fetch_code (prog_code P) k is the code of the k-th
                    instruction of P, counting from 0.

    The host checks one property, PSlot. A host counter holding
    pair (pcode p) v satisfies PSlot exactly when the guest property p
    holds of v. So a host fact on PSlot about a slot counter carries a
    guest claim together with the value it was checked on.

    Dependencies: Coq standard library, EarnedCore.v, EarnedGeneric.v and
    EarnedMulti.v. No axioms, no Admitted.                                  *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose, as in
   EarnedCore.v: this file imports nothing but the Coq standard library and
   the three small machines beside it, so anyone can re-check it from a
   clean checkout. Its link to the abstract record (the host machine with
   the property PSlot as a CertificationSystem, and the undecidability of
   its halting problem on U) lives in
   coq/kernel/foundation/UniversalInterpreterLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedCore Minimal.EarnedGeneric Minimal.EarnedMulti.

Module E := Minimal.EarnedCore.
Module G := Minimal.EarnedGeneric.
Module M := Minimal.EarnedMulti.

(* ================================================================= *)
(* Pairs of numbers as one number.                                    *)
(* ================================================================= *)

Definition pair (m n : nat) : nat := (n + n + 1) * 2 ^ m.

(* Strip factors of 2, counting them in m, until the number is odd. The
   fuel argument is the number itself, which is always enough. *)
Fixpoint unp (fuel x m : nat) : option (nat * nat) :=
  match fuel with
  | 0 => None
  | S f =>
      match x with
      | 0 => None
      | S _ => if Nat.odd x then Some (m, Nat.div2 x) else unp f (Nat.div2 x) (S m)
      end
  end.

Definition unpair (x : nat) : option (nat * nat) := unp x x 0.

Lemma unpair_zero : unpair 0 = None.
Proof. reflexivity. Qed.

Lemma pow2_pos : forall m, 0 < 2 ^ m.
Proof. intro m. apply Nat.neq_0_lt_0, Nat.pow_nonzero. lia. Qed.

Lemma pair_pos : forall m n, 0 < pair m n.
Proof. intros m n. unfold pair. pose proof (pow2_pos m). nia. Qed.

Lemma pair_S : forall m n, pair (S m) n = 2 * pair m n.
Proof. intros m n. unfold pair. rewrite Nat.pow_succ_r'. lia. Qed.

Lemma pair_0 : forall n, pair 0 n = S (2 * n).
Proof. intro n. unfold pair. simpl. lia. Qed.

Lemma unp_fuel : forall f1 f2 x m, x <= f1 -> x <= f2 -> unp f1 x m = unp f2 x m.
Proof.
  induction f1 as [| f1 IH]; intros f2 x m H1 H2.
  - assert (x = 0) as -> by lia. destruct f2; reflexivity.
  - destruct x as [| x']; [destruct f2; reflexivity |].
    destruct f2 as [| f2]; [lia |].
    assert (Hd : Nat.div2 (S x') < S x') by (apply Nat.lt_div2; lia).
    change (unp (S f1) (S x') m) with
      (if Nat.odd (S x') then Some (m, Nat.div2 (S x'))
       else unp f1 (Nat.div2 (S x')) (S m)).
    change (unp (S f2) (S x') m) with
      (if Nat.odd (S x') then Some (m, Nat.div2 (S x'))
       else unp f2 (Nat.div2 (S x')) (S m)).
    destruct (Nat.odd (S x')); [reflexivity |].
    apply IH; lia.
Qed.

Lemma unp_odd : forall y m, unp (S (2 * y)) (S (2 * y)) m = Some (m, y).
Proof.
  intros y m.
  change (unp (S (2 * y)) (S (2 * y)) m) with
    (if Nat.odd (S (2 * y)) then Some (m, Nat.div2 (S (2 * y)))
     else unp (2 * y) (Nat.div2 (S (2 * y))) (S m)).
  replace (Nat.odd (S (2 * y))) with true
    by (replace (S (2 * y)) with (1 + 2 * y) by lia;
        rewrite Nat.odd_add_mul_2; reflexivity).
  rewrite Nat.div2_succ_double. reflexivity.
Qed.

Lemma unp_even : forall v m, 0 < v -> unp (2 * v) (2 * v) m = unp v v (S m).
Proof.
  intros v m Hv. destruct (2 * v) as [| w] eqn:E; [lia |].
  change (unp (S w) (S w) m) with
    (if Nat.odd (S w) then Some (m, Nat.div2 (S w))
     else unp w (Nat.div2 (S w)) (S m)).
  rewrite <- E.
  replace (Nat.odd (2 * v)) with false
    by (replace (2 * v) with (0 + 2 * v) by lia;
        rewrite Nat.odd_add_mul_2; reflexivity).
  rewrite Nat.div2_double. apply unp_fuel; lia.
Qed.

Lemma unp_pair : forall m n acc, unp (pair m n) (pair m n) acc = Some (m + acc, n).
Proof.
  induction m as [| m IH]; intros n acc.
  - rewrite pair_0. rewrite unp_odd. reflexivity.
  - rewrite pair_S. rewrite unp_even by apply pair_pos.
    rewrite IH. f_equal. f_equal. lia.
Qed.

Theorem unpair_pair : forall m n, unpair (pair m n) = Some (m, n).
Proof.
  intros m n. unfold unpair. rewrite unp_pair. rewrite Nat.add_0_r. reflexivity.
Qed.

Theorem pair_inj : forall m n m' n', pair m n = pair m' n' -> m = m' /\ n = n'.
Proof.
  intros m n m' n' H. apply (f_equal unpair) in H.
  rewrite !unpair_pair in H. injection H as -> ->. auto.
Qed.

(* Every positive number is a pair. *)
Lemma pair_onto : forall x, 0 < x -> exists m n, x = pair m n.
Proof.
  induction x as [x IH] using (well_founded_induction lt_wf). intros Hx.
  pose proof (Nat.div2_odd x) as Hd.
  destruct (Nat.odd x) eqn:Ho; simpl in Hd.
  - exists 0, (Nat.div2 x). rewrite pair_0. lia.
  - assert (Hlt : Nat.div2 x < x) by (apply Nat.lt_div2; lia).
    assert (Hpos : 0 < Nat.div2 x) by lia.
    destruct (IH _ Hlt Hpos) as [m [n Hmn]].
    exists (S m), n. rewrite pair_S, <- Hmn. lia.
Qed.

Theorem unpair_some : forall x, 0 < x ->
  exists m n, unpair x = Some (m, n) /\ x = pair m n.
Proof.
  intros x Hx. destruct (pair_onto x Hx) as [m [n ->]].
  exists m, n. split; [apply unpair_pair | reflexivity].
Qed.

Theorem unpair_none : forall x, unpair x = None <-> x = 0.
Proof.
  intro x. split.
  - intro H. destruct x as [| x]; [reflexivity | exfalso].
    destruct (unpair_some (S x)) as [m [n [Hs _]]]; [lia | congruence].
  - intros ->. reflexivity.
Qed.

Theorem unpair_sound : forall x m n, unpair x = Some (m, n) -> x = pair m n.
Proof.
  intros x m n H. destruct x as [| x]; [discriminate |].
  destruct (unpair_some (S x)) as [m' [n' [Hs Hx]]]; [lia |].
  rewrite H in Hs. injection Hs as -> ->. exact Hx.
Qed.

(* The list code of EarnedGeneric.v is built from pair. *)
Lemma pair_encode : forall x t, G.encode (x :: t) = pair x (G.encode t).
Proof. intros x t. simpl. unfold pair. lia. Qed.

Lemma unpair_encode_nil : unpair (G.encode []) = None.
Proof. reflexivity. Qed.

Lemma unpair_encode_cons : forall x t,
  unpair (G.encode (x :: t)) = Some (x, G.encode t).
Proof. intros x t. rewrite pair_encode. apply unpair_pair. Qed.

(* ================================================================= *)
(* Guest properties and counters as numbers.                          *)
(* ================================================================= *)

Definition pcode (p : E.prop) : nat :=
  match p with E.PZero => 0 | E.PEven => 1 | E.PGe n => n + 2 end.

Definition pdec (n : nat) : E.prop :=
  match n with 0 => E.PZero | 1 => E.PEven | S (S m) => E.PGe m end.

Theorem pdec_pcode : forall p, pdec (pcode p) = p.
Proof.
  intros [| | n]; [reflexivity | reflexivity |].
  simpl. replace (n + 2) with (S (S n)) by lia. reflexivity.
Qed.

Theorem pcode_pdec : forall n, pcode (pdec n) = n.
Proof. intros [| [| n]]; simpl; [reflexivity | reflexivity | lia]. Qed.

Theorem pcode_inj : forall p q, pcode p = pcode q -> p = q.
Proof.
  intros p q H. rewrite <- (pdec_pcode p), <- (pdec_pcode q), H. reflexivity.
Qed.

Definition ccode (c : E.ctr) : nat := match c with E.CA => 0 | E.CB => 1 end.

Definition cdec (n : nat) : option E.ctr :=
  match n with 0 => Some E.CA | 1 => Some E.CB | _ => None end.

Theorem cdec_ccode : forall c, cdec (ccode c) = Some c.
Proof. intros []; reflexivity. Qed.

Theorem cdec_sound : forall n c, cdec n = Some c -> ccode c = n.
Proof.
  intros [| [| n]] c H; simpl in H; try discriminate; injection H as <-; reflexivity.
Qed.

Theorem ccode_inj : forall c d, ccode c = ccode d -> c = d.
Proof. intros [] [] H; simpl in H; try discriminate; reflexivity. Qed.

Lemma ccode_lt : forall c, ccode c < 2.
Proof. intros []; simpl; lia. Qed.

(* ================================================================= *)
(* The host property language: one property, PSlot.                   *)
(* ================================================================= *)

Inductive hprop : Type := PSlot.

(* The one property equals itself; with one constructor the match has one
   case. *)
Definition hprop_eqb (p q : hprop) : bool :=
  match p, q with PSlot, PSlot => true end.

Lemma hprop_eqb_eq : forall p q, hprop_eqb p q = true <-> p = q.
Proof. intros [] []. split; reflexivity. Qed.

(* A counter holding pair m v satisfies PSlot when guest property pdec m
   holds of v. A counter holding 0 holds no pair and never satisfies it. *)
Definition heval (p : hprop) (x : nat) : bool :=
  match unpair x with Some (m, v) => E.eval (pdec m) v | None => false end.

Definition hholds (p : hprop) (x : nat) : Prop :=
  match unpair x with Some (m, v) => E.holds (pdec m) v | None => False end.

Theorem heval_iff : forall p x, heval p x = true <-> hholds p x.
Proof.
  intros p x. unfold heval, hholds.
  destruct (unpair x) as [[m v] |]; [apply E.eval_iff | split; [discriminate | tauto]].
Qed.

Theorem heval_pair : forall p v, heval PSlot (pair (pcode p) v) = E.eval p v.
Proof. intros p v. unfold heval. rewrite unpair_pair, pdec_pcode. reflexivity. Qed.

Theorem hholds_pair : forall p v, hholds PSlot (pair (pcode p) v) <-> E.holds p v.
Proof. intros p v. unfold hholds. rewrite unpair_pair, pdec_pcode. tauto. Qed.

Theorem heval_zero : heval PSlot 0 = false.
Proof. reflexivity. Qed.

(* A counter satisfies PSlot exactly when it holds the code of a guest
   claim together with a value the claim holds of. *)
Theorem hholds_iff : forall x,
  hholds PSlot x <-> exists p v, x = pair (pcode p) v /\ E.holds p v.
Proof.
  intro x. split.
  - intro H. unfold hholds in H.
    destruct (unpair x) as [[m v] |] eqn:Hu; [| destruct H].
    exists (pdec m), v. rewrite pcode_pdec. split; [| exact H].
    apply unpair_sound, Hu.
  - intros [p [v [-> Hh]]]. apply hholds_pair, Hh.
Qed.

(* ================================================================= *)
(* Guest instructions as numbers.                                     *)
(* ================================================================= *)

Definition icode (i : E.instr) : nat :=
  match i with
  | E.INC c => pair 0 (ccode c)
  | E.DEC c j => pair 1 (pair (ccode c) j)
  | E.HALT => pair 2 0
  | E.CHECK p c => pair 3 (pair (ccode c) (pcode p))
  | E.COMMIT p c => pair 4 (pair (ccode c) (pcode p))
  | E.CERTIFY => pair 5 0
  end.

Definition idecode (x : nat) : option E.instr :=
  match unpair x with
  | Some (0, a) => option_map E.INC (cdec a)
  | Some (1, a) =>
      match unpair a with
      | Some (c, j) => option_map (fun c => E.DEC c j) (cdec c)
      | None => None
      end
  | Some (2, 0) => Some E.HALT
  | Some (3, a) =>
      match unpair a with
      | Some (c, q) => option_map (fun c => E.CHECK (pdec q) c) (cdec c)
      | None => None
      end
  | Some (4, a) =>
      match unpair a with
      | Some (c, q) => option_map (fun c => E.COMMIT (pdec q) c) (cdec c)
      | None => None
      end
  | Some (5, 0) => Some E.CERTIFY
  | _ => None
  end.

Theorem idecode_icode : forall i, idecode (icode i) = Some i.
Proof.
  intros [c | c j | | p c | p c |]; unfold idecode, icode;
    rewrite ?unpair_pair, ?cdec_ccode, ?pdec_pcode; reflexivity.
Qed.

(* idecode reads back only codes: whatever it decodes was that code. *)
Theorem idecode_sound : forall x i, idecode x = Some i -> icode i = x.
Proof.
  intros x i H. unfold idecode in H.
  destruct (unpair x) as [[o a] |] eqn:Hx; [| discriminate].
  apply unpair_sound in Hx. subst x.
  destruct o as [| [| [| [| [| [| o]]]]]].
  - destruct (cdec a) as [c |] eqn:Hc; simpl in H; [| discriminate].
    injection H as <-. simpl. apply cdec_sound in Hc. subst. reflexivity.
  - destruct (unpair a) as [[c j] |] eqn:Ha; [| discriminate].
    destruct (cdec c) as [d |] eqn:Hc; simpl in H; [| discriminate].
    injection H as <-. simpl. apply cdec_sound in Hc. apply unpair_sound in Ha.
    subst. reflexivity.
  - destruct a; [| discriminate]. injection H as <-. reflexivity.
  - destruct (unpair a) as [[c q] |] eqn:Ha; [| discriminate].
    destruct (cdec c) as [d |] eqn:Hc; simpl in H; [| discriminate].
    injection H as <-. simpl. apply cdec_sound in Hc. apply unpair_sound in Ha.
    rewrite pcode_pdec. subst. reflexivity.
  - destruct (unpair a) as [[c q] |] eqn:Ha; [| discriminate].
    destruct (cdec c) as [d |] eqn:Hc; simpl in H; [| discriminate].
    injection H as <-. simpl. apply cdec_sound in Hc. apply unpair_sound in Ha.
    rewrite pcode_pdec. subst. reflexivity.
  - destruct a; [| discriminate]. injection H as <-. reflexivity.
  - discriminate.
Qed.

Theorem icode_inj : forall i j, icode i = icode j -> i = j.
Proof.
  intros i j H. apply (f_equal idecode) in H. rewrite !idecode_icode in H.
  injection H as ->. reflexivity.
Qed.

Lemma icode_pos : forall i, 0 < icode i.
Proof. intros []; apply pair_pos. Qed.

(* The opcode and operand of each instruction code. *)
Lemma unpair_icode : forall i, exists o a, unpair (icode i) = Some (o, a) /\ o <= 5.
Proof.
  intros []; simpl; eexists; eexists; (split; [apply unpair_pair | lia]).
Qed.

(* ================================================================= *)
(* Programs as numbers, and the fetch the host performs.              *)
(* ================================================================= *)

Definition prog_code (P : list E.instr) : nat := G.encode (map icode P).

Theorem prog_code_decode : forall P, G.decode (prog_code P) = map icode P.
Proof. intro P. unfold prog_code. apply G.decode_encode. Qed.

Lemma prog_code_nil : prog_code [] = 0.
Proof. reflexivity. Qed.

Lemma prog_code_cons : forall i P, prog_code (i :: P) = pair (icode i) (prog_code P).
Proof. intros i P. unfold prog_code. simpl map. apply pair_encode. Qed.

Theorem prog_code_inj : forall P Q, prog_code P = prog_code Q -> P = Q.
Proof.
  induction P as [| i P IH]; intros [| j Q] H.
  - reflexivity.
  - rewrite prog_code_nil, prog_code_cons in H. pose proof (pair_pos (icode j) (prog_code Q)).
    lia.
  - rewrite prog_code_nil, prog_code_cons in H. pose proof (pair_pos (icode i) (prog_code P)).
    lia.
  - rewrite !prog_code_cons in H. apply pair_inj in H as [Hi HP].
    apply icode_inj in Hi. apply IH in HP. subst. reflexivity.
Qed.

(* Strip k elements from a list code: the number left after k unpackings.
   A code that runs out first leaves 0. *)
Fixpoint skip_code (code k : nat) : nat :=
  match k with
  | 0 => code
  | S k' => match unpair code with Some (_, t) => skip_code t k' | None => 0 end
  end.

(* The head of a list code after k unpackings: the k-th element. *)
Fixpoint fetch_code (code : nat) (k : nat) : option nat :=
  match k with
  | 0 => option_map fst (unpair code)
  | S k' => match unpair code with Some (_, t) => fetch_code t k' | None => None end
  end.

Lemma skip_code_S : forall code k,
  skip_code code (S k) =
  match unpair code with Some (_, t) => skip_code t k | None => 0 end.
Proof. reflexivity. Qed.

Lemma fetch_code_S : forall code k,
  fetch_code code (S k) =
  match unpair code with Some (_, t) => fetch_code t k | None => None end.
Proof. reflexivity. Qed.

(* fetch_code is skip_code followed by one more unpacking. *)
Theorem fetch_code_skip : forall k code,
  fetch_code code k = option_map fst (unpair (skip_code code k)).
Proof.
  induction k as [| k IH]; intro code; simpl; [reflexivity |].
  destruct (unpair code) as [[h t] |]; [apply IH | reflexivity].
Qed.

Theorem skip_code_encode : forall k l, skip_code (G.encode l) k = G.encode (skipn k l).
Proof.
  induction k as [| k IH]; intro l; [reflexivity |].
  destruct l as [| x t].
  - reflexivity.
  - rewrite skip_code_S, unpair_encode_cons. apply IH.
Qed.

Theorem fetch_code_encode : forall k l, fetch_code (G.encode l) k = nth_error l k.
Proof.
  induction k as [| k IH]; intros [| x t].
  - reflexivity.
  - unfold fetch_code. rewrite unpair_encode_cons. reflexivity.
  - reflexivity.
  - rewrite fetch_code_S, unpair_encode_cons. apply IH.
Qed.

Lemma nth_error_map_opt : forall (A B : Type) (f : A -> B) (l : list A) k,
  nth_error (map f l) k = option_map f (nth_error l k).
Proof.
  intros A B f l. induction l as [| x l IH]; intros [| k]; simpl; auto.
Qed.

Lemma skipn_map_comm : forall (A B : Type) (f : A -> B) (l : list A) k,
  skipn k (map f l) = map f (skipn k l).
Proof.
  intros A B f l. induction l as [| x l IH]; intros [| k]; simpl; auto.
Qed.

(* What the host's fetch computes: the k-th unpacking of a program code is
   the code of the k-th instruction of the program (counting from 0), and
   None past the end. *)
Theorem fetch_code_prog : forall P k,
  fetch_code (prog_code P) k = option_map icode (nth_error P k).
Proof.
  intros P k. unfold prog_code. rewrite fetch_code_encode. apply nth_error_map_opt.
Qed.

(* After k unpackings the program code is the code of the rest of the
   program. *)
Theorem skip_code_prog : forall P k, skip_code (prog_code P) k = prog_code (skipn k P).
Proof.
  intros P k. unfold prog_code. rewrite skip_code_encode. f_equal.
  apply skipn_map_comm.
Qed.

(* One unpacking of the rest of the program: the head is the code of the
   k-th instruction and the tail is the code of the program after it. *)
Theorem unpair_skip_prog : forall P k i,
  nth_error P k = Some i ->
  unpair (skip_code (prog_code P) k) = Some (icode i, prog_code (skipn (S k) P)).
Proof.
  induction P as [| x P IH]; intros [| k] i H; simpl in H; try discriminate.
  - injection H as <-. change (skip_code (prog_code (x :: P)) 0) with (prog_code (x :: P)).
    change (skipn 1 (x :: P)) with P.
    rewrite prog_code_cons. apply unpair_pair.
  - rewrite skip_code_S, prog_code_cons, unpair_pair.
    change (skipn (S (S k)) (x :: P)) with (skipn (S k) P). apply IH, H.
Qed.

(* Past the end of the program, the unpacking finds 0. *)
Theorem skip_prog_past_end : forall P k,
  nth_error P k = None -> skip_code (prog_code P) k = 0.
Proof.
  intros P k H. rewrite skip_code_prog.
  apply nth_error_None in H. rewrite skipn_all2 by exact H. reflexivity.
Qed.

(* Fetch and decode together give back the guest's instruction fetch. *)
Theorem fetch_decode_prog : forall P k,
  match fetch_code (prog_code P) k with Some x => idecode x | None => None end
  = nth_error P k.
Proof.
  intros P k. rewrite fetch_code_prog.
  destruct (nth_error P k); simpl; [apply idecode_icode | reflexivity].
Qed.

(* The guest fetches at a 1-based pc: pc 0 fetches nothing, pc S k fetches
   the k-th instruction. *)
Theorem guest_fetch_code : forall P k,
  option_map icode (E.fetch P (S k)) = fetch_code (prog_code P) k.
Proof. intros P k. rewrite fetch_code_prog. reflexivity. Qed.

(* ================================================================= *)
(* The host machine on PSlot.                                         *)
(* ================================================================= *)

(* A host run that raises the flag earned it on a PSlot claim about one
   register, by CHECK, COMMIT at the same version, CERTIFY. *)
Corollary host_earned_certification_provenance :
  forall (s0 : @M.state hprop) (tr : list (@M.instr hprop)),
  M.clean_start s0 -> M.cert (M.run hprop_eqb heval tr s0) = true ->
  exists pre1 p c mid1 mid2 post,
    tr = pre1 ++ M.CHECK p c :: mid1 ++ M.COMMIT p c :: mid2 ++ M.CERTIFY :: post /\
    M.check_ok heval (M.core_of (M.run hprop_eqb heval pre1 s0)) p c = true /\
    M.commit_ok hprop_eqb
      (M.core_of (M.run hprop_eqb heval (pre1 ++ M.CHECK p c :: mid1) s0)) p c = true /\
    M.certify_ok (M.core_of (M.run hprop_eqb heval
      (pre1 ++ M.CHECK p c :: mid1 ++ M.COMMIT p c :: mid2) s0)) = true /\
    M.vers (M.core_of (M.run hprop_eqb heval pre1 s0)) c
      = M.vers (M.core_of (M.run hprop_eqb heval (pre1 ++ M.CHECK p c :: mid1) s0)) c /\
    M.untouched hprop_eqb heval
      (M.run hprop_eqb heval (pre1 ++ [M.CHECK p c]) s0) mid1 c.
Proof. exact (M.multi_earned_certification_provenance hprop_eqb hprop_eqb_eq heval). Qed.

(* A live host fact on PSlot about register r means r holds the code of a
   guest claim p together with a value v, and p holds of v. *)
Corollary host_slot_soundness :
  forall (s0 : @M.state hprop) (tr : list (@M.instr hprop)) (f : @M.fact hprop),
  M.clean_start s0 ->
  let k := M.core_of (M.run hprop_eqb heval tr s0) in
  In f (M.facts k) -> M.f_ver f = M.vers k (M.f_reg f) ->
  exists p v, M.vals k (M.f_reg f) = pair (pcode p) v /\ E.holds p v.
Proof.
  intros s0 tr f H0 k Hin Hv.
  pose proof (M.multi_checker_soundness hprop_eqb heval hholds heval_iff
                s0 tr f H0 Hin Hv) as Hh.
  destruct (M.f_prop f). apply hholds_iff, Hh.
Qed.

(* A COMMIT of PSlot on register r that would succeed means r holds a
   guest claim code and a value the claim holds of. *)
Corollary host_committed_slot_holds :
  forall (s0 : @M.state hprop) (tr : list (@M.instr hprop)) r,
  M.clean_start s0 ->
  M.commit_ok hprop_eqb (M.core_of (M.run hprop_eqb heval tr s0)) PSlot r = true ->
  exists p v, M.vals (M.core_of (M.run hprop_eqb heval tr s0)) r = pair (pcode p) v
              /\ E.holds p v.
Proof.
  intros s0 tr r H0 H.
  apply hholds_iff.
  exact (M.multi_committed_claim_holds hprop_eqb hprop_eqb_eq heval hholds heval_iff
           s0 tr PSlot r H0 H).
Qed.

(* ================================================================= *)
(* Assumption audit. Every line must print                            *)
(* "Closed under the global context".                                 *)
(* ================================================================= *)

Print Assumptions unpair_pair.
Print Assumptions pair_inj.
Print Assumptions unpair_some.
Print Assumptions unpair_none.
Print Assumptions unpair_sound.
Print Assumptions pair_encode.
Print Assumptions pdec_pcode.
Print Assumptions pcode_pdec.
Print Assumptions cdec_ccode.
Print Assumptions heval_iff.
Print Assumptions heval_pair.
Print Assumptions hholds_iff.
Print Assumptions idecode_icode.
Print Assumptions idecode_sound.
Print Assumptions icode_inj.
Print Assumptions prog_code_decode.
Print Assumptions prog_code_inj.
Print Assumptions fetch_code_skip.
Print Assumptions fetch_code_prog.
Print Assumptions skip_code_prog.
Print Assumptions unpair_skip_prog.
Print Assumptions skip_prog_past_end.
Print Assumptions fetch_decode_prog.
Print Assumptions guest_fetch_code.
Print Assumptions host_earned_certification_provenance.
Print Assumptions host_slot_soundness.
Print Assumptions host_committed_slot_holds.
