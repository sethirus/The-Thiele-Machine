(** TcPlain.v: what the packed theorems say about plain inputs, and where
    the recursion theorem for plain inputs stands.

    A program computes y from x in the plain reading, [tc_plain_fun P x y],
    when started with x in counter A and 0 in counter B it stops with y in
    counter A. This is the reading where the input is the number itself.

    Proved here:

      [tc_rice_packed_fun]   Rice's theorem for properties of the packed
                             function of a program (a corollary of
                             TcRice.v)
      [tc_plain_is_packed]   on inputs 2^x the plain reading and the packed
                             reading are the same machine run; a program
                             computes y from 2^x in the plain reading when
                             its A ends as 2^y
      [tc_kleene_plain_powers]  Kleene's recursion theorem for the plain
                             reading restricted to the inputs 2^x: the fixed
                             point e and F e stop together on every input
                             2^x and then leave the same number in counter A
                             exactly when that number is a power of 2
                             (this is TcPacked.tc_kleene, restated)

    And the precise place where recursion on all plain inputs stops. Take a
    transformation of programs F(p) = "add t(p) to the input", for a
    function t that grows faster than any bound L on the constant a program
    of a given length can add. A fixed point of F, for the plain reading
    on all inputs, is a program e that computes x + t(e) on every x
    ([tc_plain_fixed_point_additive]); and no such program exists when
    [tc_LL L] holds ([tc_plain_recursion_needs_LL]). [tc_LL L] says that a
    program of s lines that adds a constant t to every input has t <= L(s).
    It is a statement of the kind Schroeppel (1972) and Barzdin (1963)
    proved for their functions; it is the content of "two counters keep one
    number and cannot also compute a constant larger than their control
    while keeping that number".

    Dependencies: TcRice.v, TcPacked.v. No axioms and no unfinished proofs. tc_LL is a
    definition, not an assumption: the two theorems that mention it have it
    as a hypothesis.                                                       *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the two-counter machine of EarnedCore.v (its
   programs, runs and the numbering of programs). The machine's link to the
   abstract record (a CertificationSystem with the trace cost floor, and a
   Thiele-complete machine) lives in EarnedCoreLinks.v and ThieleComplete.v. *)


From Coq Require Import List Arith Lia.
Import ListNotations.
From Undecidability.Synthetic Require Import Undecidability.
Require Import Minimal.TcBlocks Kernel.TcRice Kernel.TcCodes Kernel.TcInterp Kernel.TcPacked.
Module E := Minimal.EarnedCore.
Set Default Goal Selector "!".

Definition tc_plain_fun (P : list E.instr) (x y : nat) : Prop :=
  exists s, tc_ends x P s /\ E.ca (E.core_of s) = y.

Lemma tc_plain_is_packed : forall P x y, tc_pk P x y <-> tc_plain_fun P (2 ^ x) (2 ^ y).
Proof. intros P x y. reflexivity. Qed.

(* Rice's theorem for properties of the packed function *)
Corollary tc_rice_packed_fun : forall (Pi : list E.instr -> Prop) y n,
  (forall p q, (forall x z, tc_pk p x z <-> tc_pk q x z) -> Pi p -> Pi q) ->
  Pi y -> ~ Pi n -> undecidable Pi.
Proof.
  intros Pi y n Hext Hy Hn.
  apply (tc_rice tc_packed Pi y n); [| exact Hy | exact Hn].
  intros p q Hpq Hp. apply (Hext p q); [| exact Hp].
  intros x z. split.
  - intros [s [Hs Hz]]. destruct (Hpq (2 ^ x) (ex_intro _ x eq_refl)) as [H1 _].
    destruct (H1 s Hs) as [t [Ht Ha]]. exists t. split; [exact Ht |].
    destruct Ha as (Ha & _). rewrite <- Ha. exact Hz.
  - intros [t [Ht Hz]]. destruct (Hpq (2 ^ x) (ex_intro _ x eq_refl)) as [_ H2].
    destruct (H2 t Ht) as [s [Hs Ha]]. exists s. split; [exact Hs |].
    destruct Ha as (Ha & _). rewrite Ha. exact Hz.
Qed.

(* ------------------------------------------------------------------ *)
(* Plain recursion and the growth of an added constant                *)
(* ------------------------------------------------------------------ *)

Definition tc_adds (P : list E.instr) (t : nat) : Prop :=
  forall x, tc_plain_fun P x (x + t).

Definition tc_LL (L : nat -> nat) : Prop :=
  forall P t, tc_adds P t -> t <= L (length P).

(* the program that adds k to its input *)
Definition tc_adder (k : nat) : list E.instr := repeat (E.INC E.CA) k.

Lemma tc_adder_run : forall K j x, j <= K ->
  let s := E.run_prog j (tc_adder K) (E.start x 0) in
  E.ca (E.core_of s) = x + j /\ E.cb (E.core_of s) = 0 /\ E.err (E.core_of s) = false /\ E.pc (E.core_of s) = S j.
Proof.
  intros K j. induction j as [| j IH]; intros x Hj s; subst s.
  - simpl. repeat split; try reflexivity; lia.
  - assert (Hj' : j <= K) by lia.
    destruct (IH x Hj') as (Ha & Hb & He & Hp).
    set (s0 := E.run_prog j (tc_adder K) (E.start x 0)) in *.
    replace (S j) with (j + 1) by lia. rewrite tc_grun_add.
    fold s0. change (E.run_prog 1 (tc_adder K) s0) with (E.step (tc_adder K) s0).
    assert (Hn : E.next_instr (tc_adder K) (E.core_of s0) = Some (E.INC E.CA)).
    { unfold E.next_instr. rewrite He, Hp. simpl. unfold tc_adder.
      assert (Hr : nth_error (repeat (E.INC E.CA) K) j = Some (E.INC E.CA)) by (apply nth_error_repeat; lia).
      rewrite Hr. reflexivity. }
    assert (Hst : E.step (tc_adder K) s0 = E.exec s0 (E.INC E.CA)) by (unfold E.step; rewrite Hn; reflexivity).
    rewrite Hst. unfold E.exec. simpl. unfold E.cexec. rewrite He. simpl.
    rewrite Hp. unfold E.write. simpl. repeat split; try lia; assumption.
Qed.

Lemma tc_adder_ends : forall k x, exists s, tc_ends x (tc_adder k) s /\ E.ca (E.core_of s) = x + k.
Proof.
  intros k x. destruct (@tc_adder_run k k x (le_n k)) as (Ha & Hb & He & Hp).
  exists (E.run_prog k (tc_adder k) (E.start x 0)). split; [| exact Ha].
  exists k. split; [reflexivity |].
  unfold E.halted, E.next_instr. rewrite He, Hp. simpl. unfold tc_adder.
  assert (Hn : nth_error (repeat (E.INC E.CA) k) k = None) by (apply nth_error_None; rewrite repeat_length; lia).
  rewrite Hn. reflexivity.
Qed.

(* plain recursion for the transformations "add t(p) to the input" *)
Definition tc_PlainRecursion : Prop :=
  forall F : list E.instr -> list E.instr,
    exists e, forall x y, tc_plain_fun e x y <-> tc_plain_fun (F e) x y.

Theorem tc_plain_fixed_point_additive : tc_PlainRecursion ->
  forall t : list E.instr -> nat, exists e, tc_adds e (t e).
Proof.
  intros HR t. destruct (HR (fun p => tc_adder (t p))) as [e He]. exists e. intro x.
  apply He. simpl. apply tc_adder_ends.
Qed.

Theorem tc_plain_recursion_needs_LL : forall L, tc_LL L -> ~ tc_PlainRecursion.
Proof.
  intros L HL HR.
  destruct (tc_plain_fixed_point_additive HR (fun p => L (length p) + 1)) as [e He].
  pose proof (HL e _ He). lia.
Qed.

(* the plainest consequence: a program that adds its own number to its input *)
Corollary tc_plain_recursion_self_adder : tc_PlainRecursion -> exists e, tc_adds e (tc_pcode e).
Proof. intro HR. apply (tc_plain_fixed_point_additive HR tc_pcode). Qed.

Print Assumptions tc_rice_packed_fun.
Print Assumptions tc_plain_fixed_point_additive.
Print Assumptions tc_plain_recursion_needs_LL.
