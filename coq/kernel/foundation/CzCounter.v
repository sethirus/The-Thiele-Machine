(** CzCounter: what the product does not do.

    Four facts, each with its proof.

      cmpz_interleaving_invariant   two interleavings of the same pair of
                                    projections end in the same state with
                                    the same cost: the product forgets the
                                    order in which independent parts moved,
                                    in the record, the ledger and the state.
      cmpz_or_weakly_complete       the weak notion composes: the product of
                                    two machines that pay the toll and have a
                                    universal base pays it and has one.
      cmpz_or_clocks_not_complete   and it proves nothing: the product of
                                    two clocks is weakly Thiele-complete and
                                    is not Thiele-complete, because it has
                                    no move that costs nothing.
      cmpz_sum_record_loses         a record that adds the parts, instead of
                                    pairing them, pays the toll on the
                                    product but cannot say which part
                                    certified: two product states with the
                                    same sum differ in the left threshold. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import AxCore.
From Kernel Require Import AxLatch.
From Kernel Require Import AxComplete.
From Kernel Require Import CzProd CzProdTC.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.

(** * The order of independent moves is forgotten *)

Theorem cmpz_interleaving_invariant : forall {A B P Q} (M : amachine A P) (N : amachine B Q)
    (tr tr' : list (am_move (cmpz_prod M N))) s,
  cmpz_lefts tr = cmpz_lefts tr' -> cmpz_rights tr = cmpz_rights tr' ->
  am_run (cmpz_prod M N) tr s = am_run (cmpz_prod M N) tr' s /\
  cmpz_cost (cmpz_prod M N) tr = cmpz_cost (cmpz_prod M N) tr'.
Proof.
  intros A B P Q M N tr tr' s Hl Hr. split.
  - rewrite !cmpz_run_prod, Hl, Hr. reflexivity.
  - rewrite !cmpz_cost_prod, Hl, Hr. reflexivity.
Qed.

(** * The weak notion composes, and means nothing *)

Theorem cmpz_or_weakly_complete : forall M0 N0 : T.machine,
  T.weakly_thiele_complete M0 -> T.weakly_thiele_complete N0 ->
  T.weakly_thiele_complete (cmpz_or M0 N0).
Proof.
  intros M0 N0 [HM [uM]] [HN [uN]]. split.
  - intros s [x | y] H0 H1; cbn in *.
    + apply orb_false_iff in H0 as [H0a H0b]. rewrite H0b in H1. rewrite orb_false_r in H1.
      exact (HM _ _ H0a H1).
    + apply orb_false_iff in H0 as [H0a H0b]. rewrite H0a in H1. 
      exact (HN _ _ H0b H1).
  - constructor.
    refine (T.mk_ub (cmpz_or M0 N0)
      (fun s => T.ub_window uM (fst s)) (fun s => T.ub_live uM (fst s))
      (fun i => inl (T.ub_compile uM i))
      (fun a b => (T.ub_load uM a b, T.ub_load uN a b))
      (fun a b => T.ub_load_window uM a b) (fun a b => T.ub_load_live uM a b)
      (fun s i H => T.ub_sim uM (fst s) i H)).
Qed.

Theorem cmpz_or_clocks_not_complete : forall rd1 rd2,
  T.weakly_thiele_complete (cmpz_or (T.clock rd1) (T.clock rd2)) /\
  ~ T.thiele_complete (cmpz_or (T.clock rd1) (T.clock rd2)).
Proof.
  intros rd1 rd2. split.
  - apply cmpz_or_weakly_complete; apply T.clock_weakly_thiele_complete.
  - intro H. destruct (T.complete_has_free_move _ H) as [m Hm].
    destruct m as [x | y]; cbn in Hm; discriminate Hm.
Qed.

(** * A record that adds the parts forgets which part certified *)

(** The sum record on the product of two certification flags: the number of
    parts that have certified, ordered as the natural numbers. *)
Definition cmpz_sum_rec (s : bool * bool) : nat :=
  (if fst s then 1 else 0) + (if snd s then 1 else 0).

Theorem cmpz_sum_record_loses :
  cmpz_sum_rec (true, false) = cmpz_sum_rec (false, true) /\
  (true, false) <> (false, true) /\
  (* the pair record separates them by a one-bit threshold of the left part *)
  bp_leb (bool * bool) (cmpz_pair_pre two_pre two_pre) (true, false) (true, false) = true /\
  bp_leb (bool * bool) (cmpz_pair_pre two_pre two_pre) (true, false) (false, true) = false.
Proof.
  split; [reflexivity | split; [intro H; discriminate H | split; reflexivity]].
Qed.

Print Assumptions cmpz_interleaving_invariant.
Print Assumptions cmpz_or_weakly_complete.
Print Assumptions cmpz_or_clocks_not_complete.
Print Assumptions cmpz_sum_record_loses.
