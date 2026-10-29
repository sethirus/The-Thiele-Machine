(** CmpRun.v: a fast runner for the host programs of the compiler, proved
    against the register semantics of CmpHost.v, and the end-to-end theorems
    about it.

    The host program of CmpHost.v is a list of instructions of two kinds,
    INC r and DEC r j. Running it with the host machine of EarnedMulti.v
    (run_prog) is correct but slow once extracted, because the program is a
    list and a register file is a function. This file gives the runner that
    is extracted: the program and the registers are kept in binary tries
    indexed by numbers (cr_tr), a lookup or an update takes a number of
    steps proportional to the number of bits of the index, and the runner
    cr_run is a loop on a fuel that counts the steps.

      cr_get_set_f / cr_rget_rset   a trie behaves as the finite map it
                                    stands for
      cr_ptab_get                   the trie of a program holds instruction
                                    a at address a (the first at address 1)
      cr_run_steps                  a run of cmp_hstep from a state, as many
                                    steps as the fuel allows, is what
                                    cr_run does
      cr_run_sound                  what cr_run returns is a run of cmp_hstep
                                    (halted: out of the program; not halted:
                                    inside it, all the fuel used)

    The end-to-end statements, for a source program p that takes nin inputs
    and answers in variable out, started on xs with the fuel given:

      cmp_exec_machine    when the runner halts after k steps, the host
                          machine of EarnedMulti.v (over any property
                          language), run for k steps from the same registers,
                          is halted at the end of the program with the
                          registers the runner holds and every other field
                          as at the start
      cmp_exec_sound      when the runner halts, the source program has a
                          derivation (CmpLang.v) from xs whose final
                          variables are the registers 1 .. nv0 of the runner
      cmp_exec_complete   when the source program has a derivation, there is
                          a step count k such that every fuel at least k
                          makes the runner halt after exactly k steps, with
                          the final source variables in its registers
      cmp_exec_unhalted   when the runner did not halt, the host machine is
                          still running after all the fuel, and every
                          derivation of the source program needs more steps
                          than the fuel

    The boolean cmp_wf_b is the check of the shape of programs the compiler
    accepts (cmp_wf), proved to agree with it.

    Dependencies: Coq standard library, the vendored coq-undecidability
    library, minimal/EarnedMulti.v and the Cmp files before this one. No
    axioms and no unfinished proofs.                                                    *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is the runner stage of the verified compiler of CmpPipeline.v and imports
   the Coq standard library, the vendored coq-undecidability library,
   minimal/EarnedMulti.v and the Cmp files. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss.
From Undecidability.MinskyMachines Require Import MM.
From Undecidability.MinskyMachines.MMenv Require Import env mme_defs.
Require Minimal.EarnedMulti.
Require Import Kernel.CmpLang Kernel.CmpBlocks Kernel.CmpCompile Kernel.CmpHost.

(* ================================================================= *)
(* Binary tries indexed by numbers.                                   *)
(* ================================================================= *)

(* Index 0 is the root; index 1 + 2m is index m of the left subtrie and
   index 2 + 2m is index m of the right one. *)
Inductive cr_tr (A : Type) : Type :=
| TLeaf : cr_tr A
| TNode : cr_tr A -> option A -> cr_tr A -> cr_tr A.
Arguments TLeaf {A}.
Arguments TNode {A}.

Fixpoint cr_get {A : Type} (t : cr_tr A) (k : nat) : option A :=
  match t with
  | TLeaf => None
  | TNode l v r =>
    match k with
    | 0 => v
    | S a => if Nat.eqb (a mod 2) 0 then cr_get l (a / 2) else cr_get r (a / 2)
    end
  end.

Definition cr_l {A : Type} (t : cr_tr A) : cr_tr A := match t with TLeaf => TLeaf | TNode l _ _ => l end.
Definition cr_v {A : Type} (t : cr_tr A) : option A := match t with TLeaf => None | TNode _ v _ => v end.
Definition cr_r {A : Type} (t : cr_tr A) : cr_tr A := match t with TLeaf => TLeaf | TNode _ _ r => r end.

Lemma cr_get_0 : forall (A : Type) (t : cr_tr A), cr_get t 0 = cr_v t.
Proof. intros A [| l v r]; reflexivity. Qed.

Lemma cr_get_S : forall (A : Type) (t : cr_tr A) a,
  cr_get t (S a) = if Nat.eqb (a mod 2) 0 then cr_get (cr_l t) (a / 2) else cr_get (cr_r t) (a / 2).
Proof. intros A [| l v r] a; [destruct (Nat.eqb (a mod 2) 0); reflexivity | reflexivity]. Qed.

(* The fuel only has to exceed the index: every level uses one unit and
   halves the index. *)
Fixpoint cr_set_f {A : Type} (f : nat) (t : cr_tr A) (k : nat) (x : A) : cr_tr A :=
  match f with
  | 0 => t
  | S f' =>
    match k with
    | 0 => TNode (cr_l t) (Some x) (cr_r t)
    | S a =>
      if Nat.eqb (a mod 2) 0
      then TNode (cr_set_f f' (cr_l t) (a / 2) x) (cr_v t) (cr_r t)
      else TNode (cr_l t) (cr_v t) (cr_set_f f' (cr_r t) (a / 2) x)
    end
  end.

Definition cr_set {A : Type} (t : cr_tr A) (k : nat) (x : A) : cr_tr A := cr_set_f (S k) t k x.

(* lia does not unfold division and remainder by a numeral here, so the
   defining equation is given to it. *)
Lemma cr_divmod : forall a, a = 2 * (a / 2) + a mod 2 /\ a mod 2 < 2.
Proof. intros a. split; [apply Nat.div_mod; discriminate | apply Nat.mod_upper_bound; discriminate]. Qed.

Lemma cr_get_set_f : forall (A : Type) f (t : cr_tr A) k x k', k < f ->
  cr_get (cr_set_f f t k x) k' = if Nat.eqb k' k then Some x else cr_get t k'.
Proof.
  intros A f. induction f as [| f IH]; intros t k x k' Hk; [lia |].
  cbn [cr_set_f]. destruct k as [| a].
  - destruct k' as [| b].
    + rewrite cr_get_0. reflexivity.
    + rewrite cr_get_S. cbn [cr_l cr_r cr_v]. rewrite cr_get_S. reflexivity.
  - destruct (Nat.eqb (a mod 2) 0) eqn:Ea.
    + destruct k' as [| b].
      * rewrite cr_get_0. cbn [cr_v Nat.eqb]. rewrite cr_get_0. reflexivity.
      * rewrite cr_get_S. cbn [cr_l cr_r cr_v]. rewrite cr_get_S.
        destruct (Nat.eqb (b mod 2) 0) eqn:Eb.
        -- rewrite IH by (pose proof (cr_divmod a); lia).
           apply Nat.eqb_eq in Ea. apply Nat.eqb_eq in Eb.
           destruct (Nat.eqb_spec (b / 2) (a / 2)) as [E1 | E1];
             destruct (Nat.eqb_spec (S b) (S a)) as [E2 | E2]; try reflexivity; exfalso; pose proof (cr_divmod a); pose proof (cr_divmod b); lia.
        -- apply Nat.eqb_eq in Ea. apply Nat.eqb_neq in Eb.
           destruct (Nat.eqb_spec (S b) (S a)); [exfalso; pose proof (cr_divmod a); pose proof (cr_divmod b); lia | reflexivity].
    + destruct k' as [| b].
      * rewrite cr_get_0. cbn [cr_v Nat.eqb]. rewrite cr_get_0. reflexivity.
      * rewrite cr_get_S. cbn [cr_l cr_r cr_v]. rewrite cr_get_S.
        destruct (Nat.eqb (b mod 2) 0) eqn:Eb.
        -- apply Nat.eqb_neq in Ea. apply Nat.eqb_eq in Eb.
           destruct (Nat.eqb_spec (S b) (S a)); [exfalso; pose proof (cr_divmod a); pose proof (cr_divmod b); lia | reflexivity].
        -- rewrite IH by (pose proof (cr_divmod a); lia).
           apply Nat.eqb_neq in Ea. apply Nat.eqb_neq in Eb.
           destruct (Nat.eqb_spec (b / 2) (a / 2)) as [E1 | E1];
             destruct (Nat.eqb_spec (S b) (S a)) as [E2 | E2]; try reflexivity; exfalso; pose proof (cr_divmod a); pose proof (cr_divmod b); lia.
Qed.

Lemma cr_get_set : forall (A : Type) (t : cr_tr A) k x k',
  cr_get (cr_set t k x) k' = if Nat.eqb k' k then Some x else cr_get t k'.
Proof. intros. unfold cr_set. apply cr_get_set_f. lia. Qed.

(* ================================================================= *)
(* The program table.                                                 *)
(* ================================================================= *)

Fixpoint cr_build (H : list cmp_hi) (a : nat) (t : cr_tr cmp_hi) : cr_tr cmp_hi :=
  match H with
  | [] => t
  | h :: H' => cr_build H' (S a) (cr_set t a h)
  end.

(* The instruction at address a is the (a - 1)-th of the list. *)
Definition cr_ptab (H : list cmp_hi) : cr_tr cmp_hi := cr_build H 1 TLeaf.

Lemma cr_build_out : forall H a t k, (k < a \/ a + length H <= k) ->
  cr_get (cr_build H a t) k = cr_get t k.
Proof.
  induction H as [| h H IH]; intros a t k Hk; simpl; [reflexivity |].
  rewrite IH by (simpl in Hk; lia). rewrite cr_get_set.
  destruct (Nat.eqb_spec k a); [exfalso; simpl in Hk; lia | reflexivity].
Qed.

Lemma cr_build_in : forall H a t k, a <= k -> k < a + length H ->
  cr_get (cr_build H a t) k = nth_error H (k - a).
Proof.
  induction H as [| h H IH]; intros a t k H1 H2; simpl in *; [lia |].
  destruct (Nat.eqb_spec k a) as [-> | Hne].
  - rewrite cr_build_out by lia. rewrite cr_get_set. rewrite Nat.eqb_refl.
    replace (a - a) with 0 by lia. reflexivity.
  - rewrite IH by lia. replace (k - a) with (S (k - S a)) by lia. reflexivity.
Qed.

Lemma cr_ptab_get : forall H a,
  cr_get (cr_ptab H) a = match a with 0 => None | S a' => nth_error H a' end.
Proof.
  intros H a. unfold cr_ptab. destruct a as [| a'].
  - rewrite cr_build_out by lia. reflexivity.
  - destruct (Nat.ltb_spec a' (length H)) as [H2 | H2].
    + rewrite cr_build_in by lia. replace (S a' - 1) with a' by lia. reflexivity.
    + rewrite cr_build_out by lia. simpl. symmetry. apply nth_error_None. lia.
Qed.

Lemma cr_ptab_none : forall H a, cr_get (cr_ptab H) a = None <-> out_code a (1, H).
Proof.
  intros H a. rewrite cr_ptab_get. unfold out_code, code_end, code_start. cbn [fst snd]. destruct a as [| a'].
  - split; [intros _; left; lia | intros _; reflexivity].
  - rewrite nth_error_None. split; intros Hl; [right; lia | destruct Hl; lia].
Qed.

Lemma cr_ptab_some : forall H a h, cr_get (cr_ptab H) a = Some h ->
  exists l r, H = l ++ h :: r /\ a = 1 + length l.
Proof.
  intros H a h E. rewrite cr_ptab_get in E. destruct a as [| a']; [discriminate |].
  destruct (nth_error_split H a' E) as (l & r & HH & Hl). exists l, r. split; [exact HH | lia].
Qed.

(* ================================================================= *)
(* Registers.                                                         *)
(* ================================================================= *)

Definition cr_rget (R : cr_tr nat) (r : nat) : nat := match cr_get R r with Some v => v | None => 0 end.

Lemma cr_rget_rset : forall R r v r', cr_rget (cr_set R r v) r' = if Nat.eqb r' r then v else cr_rget R r'.
Proof.
  intros R r v r'. unfold cr_rget. rewrite cr_get_set. destruct (Nat.eqb r' r); reflexivity.
Qed.

(* The trie R holds the registers e. *)
Definition cr_rel (R : cr_tr nat) (e : nat -> nat) : Prop := forall r, cr_rget R r = e r.

Lemma cr_rel_set : forall R e r v, cr_rel R e -> cr_rel (cr_set R r v) (cmp_upd e r v).
Proof.
  intros R e r v H r'. rewrite cr_rget_rset. unfold cmp_upd. destruct (Nat.eqb r' r); [reflexivity | apply H].
Qed.

(* Registers 1, 2, ... hold the inputs, as many as nv; everything else is 0. *)
Fixpoint cr_loadf (xs : list nat) (nv a : nat) (t : cr_tr nat) : cr_tr nat :=
  match xs, nv with
  | x :: xs', S nv' => cr_loadf xs' nv' (S a) (cr_set t a x)
  | _, _ => t
  end.

Definition cr_load (nv : nat) (xs : list nat) : cr_tr nat := cr_loadf xs nv 1 TLeaf.

Lemma cr_loadf_get : forall xs nv a t k,
  cr_rget (cr_loadf xs nv a t) k =
  if (Nat.leb a k && Nat.ltb (k - a) nv && Nat.ltb (k - a) (length xs))%bool then nth (k - a) xs 0 else cr_rget t k.
Proof.
  induction xs as [| x xs IH]; intros nv a t k.
  - simpl. destruct (Nat.leb a k && Nat.ltb (k - a) nv && Nat.ltb (k - a) 0)%bool eqn:E; [| reflexivity].
    apply andb_true_iff in E. destruct E as [_ E]. apply Nat.ltb_lt in E. lia.
  - destruct nv as [| nv].
    + simpl. destruct (Nat.leb a k && Nat.ltb (k - a) 0 && Nat.ltb (k - a) (S (length xs)))%bool eqn:E; [| reflexivity].
      apply andb_true_iff in E. destruct E as [E _]. apply andb_true_iff in E. destruct E as [_ E].
      apply Nat.ltb_lt in E. lia.
    + simpl. rewrite IH. rewrite cr_rget_rset.
      destruct (Nat.eqb_spec k a) as [-> | Hne].
      * replace (Nat.leb (S a) a) with false by (symmetry; apply Nat.leb_gt; lia).
        replace (Nat.leb a a) with true by (symmetry; apply Nat.leb_le; lia).
        replace (a - a) with 0 by lia. simpl. reflexivity.
      * destruct (Nat.leb_spec (S a) k) as [H1 | H1]; destruct (Nat.leb_spec a k) as [H2 | H2]; simpl;
          try (exfalso; lia).
        -- replace (k - a) with (S (k - S a)) by lia. simpl.
           destruct (Nat.ltb_spec (k - S a) nv) as [H3 | H3]; destruct (Nat.ltb_spec (S (k - S a)) (S nv)) as [H4 | H4];
             try (exfalso; lia).
           ++ destruct (Nat.ltb_spec (k - S a) (length xs)) as [H5 | H5];
                destruct (Nat.ltb_spec (S (k - S a)) (S (length xs))) as [H6 | H6]; try (exfalso; lia); reflexivity.
           ++ reflexivity.
        -- destruct (Nat.eqb_spec k a); [exfalso; lia | reflexivity].
Qed.

Lemma cr_load_rel : forall nv xs, cr_rel (cr_load nv xs) (cmp_mm_load nv xs).
Proof.
  intros nv xs r. unfold cr_load. rewrite cr_loadf_get. unfold cmp_mm_load.
  destruct r as [| x].
  - simpl. reflexivity.
  - replace (S x - 1) with x by lia.
    destruct (Nat.leb_spec 1 (S x)) as [H1 | H1]; [| exfalso; lia]. simpl.
    destruct (Nat.ltb_spec x nv) as [H3 | H3]; simpl.
    + destruct (Nat.ltb_spec x (length xs)) as [H5 | H5]; [reflexivity |].
      unfold cr_rget. simpl. symmetry. apply nth_overflow. lia.
    + unfold cr_rget. reflexivity.
Qed.

(* ================================================================= *)
(* The runner.                                                        *)
(* ================================================================= *)

Record cr_res : Type := mk_cr_res {
  cr_halted : bool;               (* the address is outside the program *)
  cr_pc : nat;                    (* the address reached *)
  cr_regs : cr_tr nat;            (* the registers there *)
  cr_left : nat                   (* the fuel not used *)
}.

(* One instruction, at address pc, on the registers R: the next address
   and registers. *)
Definition cr_next (h : cmp_hi) (pc : nat) (R : cr_tr nat) : nat * cr_tr nat :=
  match h with
  | HInc r => (S pc, cr_set R r (S (cr_rget R r)))
  | HDec r j => match cr_rget R r with
                | 0 => (S pc, R)
                | S u => (j, cr_set R r u)
                end
  end.

Fixpoint cr_run (P : cr_tr cmp_hi) (fuel pc : nat) (R : cr_tr nat) : cr_res :=
  match cr_get P pc with
  | None => mk_cr_res true pc R fuel
  | Some h =>
    match fuel with
    | 0 => mk_cr_res false pc R 0
    | S f => match cr_next h pc R with (pc', R') => cr_run P f pc' R' end
    end
  end.

Lemma cr_run_none : forall P fuel pc R, cr_get P pc = None -> cr_run P fuel pc R = mk_cr_res true pc R fuel.
Proof. intros P fuel pc R E. destruct fuel; simpl; rewrite E; reflexivity. Qed.

Lemma cr_run_zero : forall P pc R h, cr_get P pc = Some h -> cr_run P 0 pc R = mk_cr_res false pc R 0.
Proof. intros P pc R h E. simpl. rewrite E. reflexivity. Qed.

Lemma cr_run_some : forall P f pc R h, cr_get P pc = Some h ->
  cr_run P (S f) pc R = cr_run P f (fst (cr_next h pc R)) (snd (cr_next h pc R)).
Proof. intros P f pc R h E. simpl. rewrite E. destruct (cr_next h pc R). reflexivity. Qed.

Lemma cr_next_spec : forall h pc R e, cr_rel R e ->
  exists e2, cmp_hstep h (pc, e) (fst (cr_next h pc R), e2) /\ cr_rel (snd (cr_next h pc R)) e2.
Proof.
  intros h pc R e Hr. destruct h as [r | r j]; simpl.
  - exists (cmp_upd e r (S (e r))). split; [apply HSInc |].
    rewrite <- (Hr r). apply cr_rel_set. exact Hr.
  - destruct (cr_rget R r) eqn:E.
    + exists e. split; [apply HSDec0; rewrite <- Hr; exact E | exact Hr].
    + exists (cmp_upd e r n). split; [apply HSDecS; rewrite <- Hr; exact E | apply cr_rel_set; exact Hr].
Qed.

(* A step of the register semantics, in the program of the trie. *)
Lemma cr_step_inv : forall H pc e st2, sss_step cmp_hstep (1, H) (pc, e) st2 ->
  exists h, cr_get (cr_ptab H) pc = Some h /\ cmp_hstep h (pc, e) st2.
Proof.
  intros H pc e st2 (k0 & l & h & r & d & HP & Hst & Hh).
  inversion HP; subst k0 H. inversion Hst; subst pc d.
  exists h. split; [| exact Hh].
  rewrite cr_ptab_get. replace (1 + length l) with (S (length l)) by lia.
  rewrite nth_error_app2 by lia. replace (length l - length l) with 0 by lia. reflexivity.
Qed.

Lemma cr_step_of : forall H pc h e st2, cr_get (cr_ptab H) pc = Some h -> cmp_hstep h (pc, e) st2 ->
  sss_step cmp_hstep (1, H) (pc, e) st2.
Proof.
  intros H pc h e st2 Hg Hst.
  destruct (cr_ptab_some H pc h Hg) as (l & r & HH & Hpc). subst H.
  apply in_sss_step with (k := 1) (l := l); [simpl; lia |]. exact Hst.
Qed.

(* A run of the register semantics is what the runner does. *)
Theorem cr_run_steps : forall H k pc e pc2 e2,
  sss_steps cmp_hstep (1, H) k (pc, e) (pc2, e2) ->
  forall fuel R, cr_rel R e -> k <= fuel ->
  exists R2, cr_rel R2 e2 /\ cr_run (cr_ptab H) fuel pc R = cr_run (cr_ptab H) (fuel - k) pc2 R2.
Proof.
  intros H k. induction k as [| k IH]; intros pc e pc2 e2 Hs fuel R Hr Hk.
  - apply sss_steps_0_inv in Hs. inversion Hs; subst. exists R. split; [exact Hr |]. f_equal. lia.
  - destruct (sss_steps_S_inv' Hs) as ((i2 & f2) & H1 & H2).
    destruct (cr_step_inv H pc e (i2, f2) H1) as (h & Hg & Hst).
    destruct fuel as [| fu]; [lia |].
    destruct (cr_next_spec h pc R e Hr) as (e3 & Hs3 & Hr3).
    assert (Hst' : (fst (cr_next h pc R), e3) = (i2, f2)) by (eapply cmp_hstep_fun; [exact Hs3 | exact Hst]).
    injection Hst' as H3 H4; subst i2 f2.
    destruct (IH _ _ _ _ H2 fu (snd (cr_next h pc R)) Hr3 ltac:(lia)) as (R2 & Hr2 & Hrun).
    exists R2. split; [exact Hr2 |].
    rewrite (cr_run_some _ _ _ _ _ Hg). rewrite Hrun. f_equal; try lia.
Qed.

Lemma cr_in_code_of : forall H pc h, cr_get (cr_ptab H) pc = Some h -> in_code pc (1, H).
Proof.
  intros H pc h Eg. destruct (in_out_code_dec pc (1, H)) as [Hi | Ho]; [exact Hi |].
  apply cr_ptab_none in Ho. congruence.
Qed.

(* What the runner returns is a run of the register semantics. *)
Theorem cr_run_sound : forall H fuel pc R e, cr_rel R e ->
  let res := cr_run (cr_ptab H) fuel pc R in
  exists e', cr_rel (cr_regs res) e' /\
    sss_steps cmp_hstep (1, H) (fuel - cr_left res) (pc, e) (cr_pc res, e') /\
    cr_left res <= fuel /\
    (cr_halted res = true -> out_code (cr_pc res) (1, H)) /\
    (cr_halted res = false -> in_code (cr_pc res) (1, H) /\ cr_left res = 0).
Proof.
  intros H fuel. induction fuel as [| fu IH]; intros pc R e Hr; cbv zeta.
  - destruct (cr_get (cr_ptab H) pc) as [h |] eqn:Eg.
    + rewrite (cr_run_zero _ _ _ _ Eg). exists e. refine (conj Hr (conj _ (conj _ (conj _ _)))).
      * apply in_sss_steps_0.
      * simpl. lia.
      * simpl. intros Hd. discriminate.
      * simpl. intros _. split; [eapply cr_in_code_of; exact Eg | reflexivity].
    + rewrite (cr_run_none _ _ _ _ Eg). exists e. refine (conj Hr (conj _ (conj _ (conj _ _)))).
      * apply in_sss_steps_0.
      * simpl. lia.
      * simpl. intros _. apply cr_ptab_none. exact Eg.
      * simpl. intros Hd. discriminate.
  - destruct (cr_get (cr_ptab H) pc) as [h |] eqn:Eg.
    + rewrite (cr_run_some _ _ _ _ _ Eg).
      destruct (cr_next_spec h pc R e Hr) as (e3 & Hs3 & Hr3).
      destruct (IH (fst (cr_next h pc R)) (snd (cr_next h pc R)) e3 Hr3) as (e' & Hr' & Hst & Hl & Hh & Hn).
      exists e'. refine (conj Hr' (conj _ (conj _ (conj Hh Hn)))).
      * replace (S fu - cr_left (cr_run (cr_ptab H) fu (fst (cr_next h pc R)) (snd (cr_next h pc R))))
          with (S (fu - cr_left (cr_run (cr_ptab H) fu (fst (cr_next h pc R)) (snd (cr_next h pc R))))) by lia.
        eapply in_sss_steps_S with (st2 := (fst (cr_next h pc R), e3)).
        -- apply (cr_step_of H pc h e); [exact Eg | exact Hs3].
        -- exact Hst.
      * lia.
    + rewrite (cr_run_none _ _ _ _ Eg). exists e. refine (conj Hr (conj _ (conj _ (conj _ _)))).
      * simpl. rewrite Nat.sub_diag. apply in_sss_steps_0.
      * simpl. lia.
      * simpl. intros _. apply cr_ptab_none. exact Eg.
      * simpl. intros Hd. discriminate.
Qed.


(* ================================================================= *)
(* The check of the shape of programs.                                *)
(* ================================================================= *)

Fixpoint cmp_wfs_b (n : nat) (s : cmp_stmt) : bool :=
  match s with
  | SSkip | SAssign _ _ => true
  | SSeq s t | SIf _ s t => cmp_wfs_b n s && cmp_wfs_b n t
  | SWhile _ s => cmp_wfs_b n s
  | SCall _ p _ => Nat.ltb p n
  end.

Lemma cmp_wfs_b_spec : forall s n, cmp_wfs_b n s = true <-> cmp_wfs n s.
Proof.
  induction s; intros n; simpl.
  - split; auto.
  - split; auto.
  - rewrite andb_true_iff, IHs1, IHs2. tauto.
  - rewrite andb_true_iff, IHs1, IHs2. tauto.
  - apply IHs.
  - apply Nat.ltb_lt.
Qed.

(* Procedure i of the list, counting from i0, may call only those below it. *)
Fixpoint cmp_wfp_from (i : nat) (ps : list cmp_proc) : bool :=
  match ps with
  | [] => true
  | pr :: ps' => cmp_wfs_b i (pr_body pr) && cmp_wfp_from (S i) ps'
  end.

Lemma cmp_wfp_from_spec : forall ps i, cmp_wfp_from i ps = true <->
  forall j pr, nth_error ps j = Some pr -> cmp_wfs (i + j) (pr_body pr).
Proof.
  induction ps as [| pr0 ps IH]; intros i; simpl.
  - split; [intros _ j pr H; destruct j; discriminate | auto].
  - rewrite andb_true_iff, cmp_wfs_b_spec, IH. split.
    + intros [H1 H2] j pr H. destruct j as [| j].
      * simpl in H. injection H as <-. rewrite Nat.add_0_r. exact H1.
      * simpl in H. replace (i + S j) with (S i + j) by lia. exact (H2 j pr H).
    + intros H. split.
      * specialize (H 0 pr0 eq_refl). rewrite Nat.add_0_r in H. exact H.
      * intros j pr Hj. replace (S i + j) with (i + S j) by lia. exact (H (S j) pr Hj).
Qed.

Definition cmp_wf_b (p : cmp_prog) : bool :=
  cmp_wfp_from 0 (cp_procs p) && cmp_wfs_b (length (cp_procs p)) (cp_main p).

Theorem cmp_wf_b_spec : forall p, cmp_wf_b p = true <-> cmp_wf p.
Proof.
  intros p. unfold cmp_wf_b, cmp_wf, cmp_wfp. rewrite andb_true_iff, cmp_wfs_b_spec, cmp_wfp_from_spec.
  split; intros [H1 H2]; split; auto; intros i pr H; specialize (H1 i pr H); simpl in H1; exact H1.
Qed.

(* ================================================================= *)
(* The runner on the host program of a source program.                *)
(* ================================================================= *)

Definition cmp_hostprog (p : cmp_prog) (nin out : nat) : list cmp_hi := cmp_host_prog (cmp_mm_prog p nin out).

(* Run the host program of p from the inputs xs (registers 1, 2, ...) for at
   most fuel steps. *)
Definition cmp_exec (p : cmp_prog) (nin out : nat) (xs : list nat) (fuel : nat) : cr_res :=
  cr_run (cr_ptab (cmp_hostprog p nin out)) fuel 1 (cr_load (cmp_nvF p nin out) xs).

(* The answer: register out + 1. The variables 0 .. n - 1 of the source
   program: registers 1 .. n. *)
Definition cmp_answer (out : nat) (res : cr_res) : nat := cr_rget (cr_regs res) (S out).
Definition cmp_vars (n : nat) (res : cr_res) : list nat := map (fun x => cr_rget (cr_regs res) (S x)) (seq 0 n).

Lemma cmp_hostprog_eq : forall p nin out, cmp_hostprog p nin out = cmp_hcode (1, cmp_mm_prog p nin out) 1.
Proof. reflexivity. Qed.

(* A run of the runner that halts is a halted run of the register semantics
   from the inputs, and the converse theorems of CmpHost.v apply to it. *)
Lemma cmp_exec_run : forall p nin out xs fuel,
  cr_halted (cmp_exec p nin out xs fuel) = true ->
  exists e', cr_rel (cr_regs (cmp_exec p nin out xs fuel)) e' /\
    sss_output cmp_hstep (1, cmp_hcode (1, cmp_mm_prog p nin out) 1)
      (1, cmp_mm_load (cmp_nvF p nin out) xs) (cr_pc (cmp_exec p nin out xs fuel), e') /\
    sss_steps cmp_hstep (1, cmp_hostprog p nin out) (fuel - cr_left (cmp_exec p nin out xs fuel))
      (1, cmp_mm_load (cmp_nvF p nin out) xs) (cr_pc (cmp_exec p nin out xs fuel), e').
Proof.
  intros p nin out xs fuel Hh.
  destruct (cr_run_sound (cmp_hostprog p nin out) fuel 1 (cr_load (cmp_nvF p nin out) xs)
              (cmp_mm_load (cmp_nvF p nin out) xs) (cr_load_rel _ _)) as (e' & Hr & Hs & Hl & Hh1 & Hh2).
  cbv zeta in *. fold (cmp_exec p nin out xs fuel) in *. 
  exists e'. split; [exact Hr |]. split; [| exact Hs].
  split; [exists (fuel - cr_left (cmp_exec p nin out xs fuel)); exact Hs | exact (Hh1 Hh)].
Qed.

Section CmpExecMachine.

Context {prop : Type}.
Variable prop_eqb : prop -> prop -> bool.
Variable eval : prop -> nat -> bool.

(* When the runner halts after k steps, the host machine of EarnedMulti.v run
   for k steps from the same registers is at the end of the program with the
   registers of the runner and everything else as at the start. *)
Theorem cmp_exec_machine : forall p nin out xs fuel,
  cr_halted (cmp_exec p nin out xs fuel) = true ->
  @cmp_host_final prop (cmp_mm_prog p nin out) (cr_rget (cr_regs (cmp_exec p nin out xs fuel)))
    (@cmp_host_at prop prop_eqb eval (cmp_mm_prog p nin out) (cmp_mm_load (cmp_nvF p nin out) xs)
       (fuel - cr_left (cmp_exec p nin out xs fuel))).
Proof.
  intros p nin out xs fuel Hh.
  destruct (cmp_exec_run p nin out xs fuel Hh) as (e' & Hr & Ho & Hs).
  set (res := cmp_exec p nin out xs fuel) in *.
  set (Q := cmp_mm_prog p nin out). set (w := cmp_mm_load (cmp_nvF p nin out) xs).
  destruct (cmp_host_output_conv (1, Q) 1 w (cr_pc res) w e' (fun r => eq_refl) Ho) as (i2 & v2 & Hs2 & Hm & Hj).
  destruct (cmp_host_run_fwd prop_eqb eval (cmp_host_prog Q) (fuel - cr_left res) 1 w (cr_pc res) e'
              (@Minimal.EarnedMulti.start prop w) Hs (cmp_hrel_start w)) as (Hrel & Hsame).
  assert (Hf : cmp_host_final Q e' (cmp_host_at prop_eqb eval Q w (fuel - cr_left res))).
  { eapply cmp_host_final_of with (j := cr_pc res); [exact Hrel | exact Hsame | | exact Hj].
    eapply cmp_hhalted; [exact Hrel |]. exact (proj2 Ho). }
  destruct Hf as (A & B & C & D1 & D2 & D3 & D4 & D5). repeat split; try assumption.
  intros r. rewrite C. symmetry. apply Hr.
Qed.

End CmpExecMachine.

(* When the runner halts, the source program has a derivation whose final
   variables 0 .. nv0 - 1 are in registers 1 .. nv0. *)
Theorem cmp_exec_sound : forall p nin out, cmp_wf p -> forall xs fuel,
  cr_halted (cmp_exec p nin out xs fuel) = true ->
  exists e1 c, cmp_ceval (cp_procs p) (cmp_init xs) (cp_main p) e1 c /\
    (forall x, x < cmp_nv0 p nin out -> cr_rget (cr_regs (cmp_exec p nin out xs fuel)) (S x) = e1 x).
Proof.
  intros p nin out Hwf xs fuel Hh.
  destruct (cmp_exec_run p nin out xs fuel Hh) as (e' & Hr & Ho & Hs).
  destruct (cmp_host_output_conv (1, cmp_mm_prog p nin out) 1 (cmp_mm_load (cmp_nvF p nin out) xs)
              (cr_pc (cmp_exec p nin out xs fuel)) _ e' (fun r => eq_refl) Ho) as (i2 & v2 & Hs2 & Hm & Hj).
  destruct (cmp_stageA_bwd p nin out Hwf xs i2 v2 Hm) as (e1 & c & D & _ & Hv).
  exists e1, c. split; [exact D |].
  intros x Hx. rewrite Hr. rewrite <- (Hv x Hx). symmetry. apply Hs2.
Qed.

(* When the source program has a derivation, the runner halts, with the
   final source variables in its registers, as soon as the fuel reaches the
   number of host steps of the run. *)
Theorem cmp_exec_complete : forall p nin out, cmp_wf p -> forall xs e1 c,
  cmp_ceval (cp_procs p) (cmp_init xs) (cp_main p) e1 c ->
  exists k, forall fuel, k <= fuel ->
    cr_halted (cmp_exec p nin out xs fuel) = true /\
    cr_left (cmp_exec p nin out xs fuel) = fuel - k /\
    (forall x, x < cmp_nv0 p nin out -> cr_rget (cr_regs (cmp_exec p nin out xs fuel)) (S x) = e1 x).
Proof.
  intros p nin out Hwf xs e1 c Hd.
  destruct (cmp_stageA_fwd p nin out Hwf xs e1 c Hd) as (w2 & Hv & Hm).
  destruct (cmp_host_output (1, cmp_mm_prog p nin out) 1 (cmp_mm_load (cmp_nvF p nin out) xs) _ w2
              (cmp_mm_load (cmp_nvF p nin out) xs) (fun r => eq_refl) Hm) as (w3 & Hs3 & (Hc & Hout)).
  destruct Hc as (k & Hk).
  exists k. intros fuel Hf.
  destruct (cr_run_steps (cmp_hostprog p nin out) k 1 _ _ _ Hk fuel (cr_load (cmp_nvF p nin out) xs)
              (cr_load_rel _ _) Hf) as (R2 & Hr2 & Hrun).
  assert (Hnone : cr_get (cr_ptab (cmp_hostprog p nin out)) (1 + length (cmp_hcode (1, cmp_mm_prog p nin out) 1)) = None).
  { apply cr_ptab_none. exact Hout. }
  unfold cmp_exec. rewrite Hrun. rewrite (cr_run_none _ _ _ _ Hnone). simpl.
  repeat split.
  intros x Hx. rewrite Hr2. rewrite <- (Hs3 (S x)). apply Hv. exact Hx.
Qed.

(* When the runner did not halt, the host machine is still running after all
   the fuel, and every derivation of the source program needs more host
   steps than the fuel. *)
Section CmpExecUnhalted.

Context {prop : Type}.
Variable prop_eqb : prop -> prop -> bool.
Variable eval : prop -> nat -> bool.

Theorem cmp_exec_unhalted : forall p nin out, cmp_wf p -> forall xs fuel,
  cr_halted (cmp_exec p nin out xs fuel) = false ->
  cr_left (cmp_exec p nin out xs fuel) = 0 /\
  ~ Minimal.EarnedMulti.halted (cmp_hprog (cmp_hostprog p nin out))
      (Minimal.EarnedMulti.core_of (@cmp_host_at prop prop_eqb eval (cmp_mm_prog p nin out)
         (cmp_mm_load (cmp_nvF p nin out) xs) fuel)) /\
  (forall e1 c, cmp_ceval (cp_procs p) (cmp_init xs) (cp_main p) e1 c ->
     exists k, fuel < k /\ forall fuel', k <= fuel' -> cr_halted (cmp_exec p nin out xs fuel') = true).
Proof.
  intros p nin out Hwf xs fuel Hh.
  destruct (cr_run_sound (cmp_hostprog p nin out) fuel 1 (cr_load (cmp_nvF p nin out) xs)
              (cmp_mm_load (cmp_nvF p nin out) xs) (cr_load_rel _ _)) as (e' & Hr & Hs & Hl & Hh1 & Hh2).
  cbv zeta in *. fold (cmp_exec p nin out xs fuel) in *.
  destruct (Hh2 Hh) as (Hin & Hleft).
  rewrite Hleft in Hs. rewrite Nat.sub_0_r in Hs.
  split; [exact Hleft | split].
  - destruct (cmp_host_run_fwd prop_eqb eval (cmp_hostprog p nin out) fuel 1 (cmp_mm_load (cmp_nvF p nin out) xs)
                (cr_pc (cmp_exec p nin out xs fuel)) e' (@Minimal.EarnedMulti.start prop (cmp_mm_load (cmp_nvF p nin out) xs))
                Hs (cmp_hrel_start _)) as (Hrel & _).
    intros Hhalt. pose proof (cmp_hhalted_out (cmp_hostprog p nin out) _ _ _ Hrel Hhalt) as Hout.
    exact (in_out_code Hin Hout).
  - intros e1 c Hd.
    destruct (cmp_exec_complete p nin out Hwf xs e1 c Hd) as (k & Hk).
    exists k. split; [| intros fuel' Hf; exact (proj1 (Hk fuel' Hf))].
    destruct (Nat.lt_ge_cases fuel k) as [Hlt | Hge]; [exact Hlt |].
    exfalso. pose proof (proj1 (Hk fuel Hge)) as Hh'. congruence.
Qed.

End CmpExecUnhalted.

(* The interpreter of CmpLang.v and the runner agree: when the interpreter
   finishes, the runner halts as soon as it has enough fuel, with the same
   final variables. *)
Theorem cmp_exec_agrees : forall p nin out, cmp_wf p -> forall xs f l k,
  cmp_interp (cp_procs p) f xs (cp_main p) 0 = Some (l, k) ->
  exists k0, forall fuel, k0 <= fuel ->
    cr_halted (cmp_exec p nin out xs fuel) = true /\
    (forall x, x < cmp_nv0 p nin out -> cr_rget (cr_regs (cmp_exec p nin out xs fuel)) (S x) = cmp_lget l x).
Proof.
  intros p nin out Hwf xs f l k Hi.
  destruct (cmp_interp_sound _ _ _ _ _ _ _ Hi) as (e1 & c & D & Q & _).
  destruct (cmp_exec_complete p nin out Hwf xs e1 c D) as (k0 & Hk0).
  exists k0. intros fuel Hf. destruct (Hk0 fuel Hf) as (H1 & _ & H3).
  split; [exact H1 |]. intros x Hx. rewrite (H3 x Hx). apply Q.
Qed.

Print Assumptions cmp_exec_machine.
Print Assumptions cmp_exec_sound.
Print Assumptions cmp_exec_complete.
Print Assumptions cmp_exec_unhalted.
Print Assumptions cmp_exec_agrees.
Print Assumptions cmp_wf_b_spec.

Print Assumptions cr_run_steps.
Print Assumptions cr_run_sound.
Print Assumptions cr_get_set.
Print Assumptions cr_ptab_get.
Print Assumptions cr_load_rel.
