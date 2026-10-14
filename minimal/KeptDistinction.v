(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file holds the exact instances behind the toll chapter: the write of a 0 on a blank cell is a merge, the finite remembering escape fails, the endless tape and the bilateral shift are the only escapes, no state space holds its own readings (Cantor), and the regress has a price; it stands alone from the certification-system kernel. *)
(* The exact examples, machine-checked. *)
Require Import Arith Lia.

(* 1. A blank cell becomes a 0. States: blank, zero, one. The write keeps written values.
      The reading "definite" never comes down. The write is a merge: blank and zero land on zero. *)
Inductive Cell := Blank | Zero | One.
Definition write0 (c : Cell) : Cell := match c with Blank => Zero | Zero => Zero | One => One end.
Definition definite (c : Cell) : bool := match c with Blank => false | _ => true end.

Theorem write_is_permanent : forall c, definite c = true -> definite (write0 c) = true.
Proof. destruct c; simpl; auto. Qed.
Theorem write_raises : definite Blank = false /\ definite (write0 Blank) = true.
Proof. auto. Qed.
Theorem write_is_a_merge : write0 Blank = write0 Zero /\ Blank <> Zero.
Proof. split. reflexivity. discriminate. Qed.

(* 2. The supposed escape: a fourth state that remembers it was blank. It does NOT escape.
      The remembering state has to go somewhere on the next write; on a finite set it lands on a
      chair already taken (here: itself), and the blank and the remembering state merge.
      This is the chairs theorem biting the escape: no finite extension of the cell avoids the merge. *)
Inductive Cell4 := B4 | Z4 | O4 | ZfromB.
Definition write0' (c : Cell4) : Cell4 := match c with B4 => ZfromB | Z4 => Z4 | O4 => O4 | ZfromB => ZfromB end.
Theorem four_state_escape_fails : write0' B4 = write0' ZfromB /\ B4 <> ZfromB.
Proof. split. reflexivity. discriminate. Qed.
(* and in general: any finite set of states with a reading that only goes up and is raised somewhere
   has a merge: that is run_merges_or_fresh / retention_bound in HeatOrRoom.v and the step law in StepLaw.v. *)

(* 3. On an endless tape the same write is injective forever: blank_n -> written_n, each cell its own. *)
Definition tape_write (n : nat) : nat := S n.   (* n = "n cells written"; the write adds one *)
Theorem tape_write_injective : forall a b, a <> b -> tape_write a <> tape_write b.
Proof. unfold tape_write. intros. lia. Qed.
Theorem tape_write_never_returns : forall n, tape_write n <> 0.
Proof. unfold tape_write. lia. Qed.

(* 4. No state space codes all its own readings: there is no surjection from X onto X -> bool,
      so the questions you can ask of a chair always outnumber the chairs. This is Cantor's diagonal.
      The machine does contain itself by running itself (the universal program, Minimal.UniversalThiele);
      what no level does is hold every question about itself, which is why the regress is forced. *)
Theorem no_space_holds_its_own_readings : forall (X : Type) (code : X -> (X -> bool)),
  ~ (forall r : X -> bool, exists x, code x = r).
Proof.
  intros X code Hsurj.
  destruct (Hsurj (fun x => negb (code x x))) as [d Hd].
  pose proof (f_equal (fun r => r d) Hd) as E. simpl in E.
  destruct (code d d); simpl in E; discriminate.
Qed.

(* 5. The regress has a price. The entitlement count in the repo (ent_cs_run_entitlement, ent_run_entitlement)
      says: with each passed test keeping at least half the candidates, the rounded-up log2 drop from the
      prior to the posterior is at most the number of tests passed, each costing at least one.
      Instance: to be entitled to "this cell is blank" among N possibilities costs at least log2_up N marks,
      and that price is unbounded as the possibilities grow. *)
Theorem regress_price_unbounded : forall m, exists N, m <= Nat.log2_up N.
Proof. intro m. exists (2 ^ m). rewrite Nat.log2_up_pow2 by lia. lia. Qed.

(* 6. Infinite room: the bilateral shift on the integers. Every state has a successor and a
      predecessor (it is a bijection, the discrete unitary), the reading "at least one" is raised
      from 0 on the first step and never comes down, and nothing ever merges. Fresh chair forever. *)
Require Import ZArith.
Open Scope Z_scope.
Definition shift (z : Z) : Z := z + 1.
Definition atleast1 (z : Z) : bool := Z.leb 1 z.
Theorem shift_bijective : (forall a b, shift a = shift b -> a = b) /\ (forall b, exists a, shift a = b).
Proof. split. unfold shift; intros; lia. intro b. exists (b - 1). unfold shift. lia. Qed.
Theorem shift_raises_and_keeps :
  atleast1 0 = false /\ atleast1 (shift 0) = true /\ (forall z, atleast1 z = true -> atleast1 (shift z) = true).
Proof. unfold atleast1, shift. repeat split. intros z H. apply Z.leb_le in H. apply Z.leb_le. lia. Qed.
Fixpoint iter_shift (k : nat) (z : Z) : Z := match k with O => z | S k' => shift (iter_shift k' z) end.
Lemma iter_shift_val : forall k z, iter_shift k z = z + Z.of_nat k.
Proof. induction k; intro z; simpl. lia. rewrite IHk. unfold shift. lia. Qed.
Theorem shift_never_returns : forall z k, (0 < k)%nat -> iter_shift k z <> z.
Proof. intros z k Hk. rewrite iter_shift_val. lia. Qed.
Close Scope Z_scope.
