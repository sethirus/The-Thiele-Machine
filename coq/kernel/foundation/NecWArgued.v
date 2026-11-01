(** NecWArgued: three claims the book argues in the text, checked.

    - A window that forgets the counter can't recover it: if the counter
      can be set on its own and the window does not change when it is, no
      rule on the window returns the counter; the same for the flag. The
      premise that the counter can be set on its own is needed.
    - Honest records agree up to the schedule: add any surcharge that
      depends on the current state to an honest extension; the result is
      honest, factors through the same latch, and matches the original
      step for step on the record, the halting and the base, while its
      step costs differ by exactly the surcharge.
    - An outside decider gets the nat family right: for every d, the
      decider "yes on 0, not d(2) on 2, no elsewhere" is correct on every
      program of the nat substrate built from d, and its flip is not
      representable there. *)

From Coq Require Import Arith.PeanoNat Lia Bool.
From Kernel Require Import StructuralCore StructuralCoreCover StructuralCoreAnyBase.
From Kernel Require Import Substrate StructuralUndecidability NatSubstrateInstance.

(* ================================================================= *)
(** * 1. A window that forgets the counter                            *)
(* ================================================================= *)

Theorem nec_w_forgetful_window_no_counter :
  forall (S W : Type) (mu : S -> nat) (set : S -> nat -> S) (w : S -> W) (s0 : S),
    (forall s n, mu (set s n) = n) ->
    (forall s n, w (set s n) = w s) ->
    ~ exists r : W -> nat, forall s, r (w s) = mu s.
Proof.
  intros S W mu set w s0 Hset Hforget [r Hr].
  pose proof (Hr (set s0 1)) as H1. pose proof (Hr (set s0 2)) as H2.
  rewrite Hforget, Hset in H1, H2. congruence.
Qed.

Theorem nec_w_forgetful_window_no_flag :
  forall (S W : Type) (flag : S -> bool) (set : S -> bool -> S) (w : S -> W) (s0 : S),
    (forall s b, flag (set s b) = b) ->
    (forall s b, w (set s b) = w s) ->
    ~ exists r : W -> bool, forall s, r (w s) = flag s.
Proof.
  intros S W flag set w s0 Hset Hforget [r Hr].
  pose proof (Hr (set s0 true)) as H1. pose proof (Hr (set s0 false)) as H2.
  rewrite Hforget, Hset in H1, H2. congruence.
Qed.

(** The premise that the counter can be set on its own is needed: with a
    "set" that changes nothing, the identity window forgets it trivially
    and still shows the counter. *)
Theorem nec_w_forget_needs_settable :
  let set := fun (s : nat) (_ : nat) => s in
  (forall s n, (fun x : nat => x) (set s n) = (fun x => x) s) /\
  exists r : nat -> nat, forall s, r ((fun x => x) s) = s.
Proof.
  intros set. split; [intros; reflexivity | exists (fun x => x); reflexivity].
Qed.

(* ================================================================= *)
(** * 2. Honest records agree up to the schedule                      *)
(* ================================================================= *)

Section Billed.

Variable M : RCM.
Variable sur : rc_state M -> nat.

(** The same machine with a surcharge [sur] on every step, carried in a
    second ledger component. *)
Definition nec_w_billed : RCM := {|
  rc_state := rc_state M * nat;
  rc_next := fun x => (rc_next M (fst x), snd x + sur (fst x));
  rc_init := fun x => rc_init M (fst x) /\ snd x = 0;
  rc_cert := fun x => rc_cert M (fst x);
  rc_mu := fun x => rc_mu M (fst x) + snd x;
  rc_halted := fun x => rc_halted M (fst x)
|}.

Variable B : BaseMachine.
Variable C : BaseCover M B.

Definition nec_w_billed_cover : BaseCover nec_w_billed B.
Proof.
  refine (Build_BaseCover nec_w_billed B (fun x => base_state M B C (fst x)) _ _ _ _).
  - intros [m k] [Hm _]. exact (base_initial M B C m Hm).
  - intros b Hb. destruct (base_surjective_initial M B C b Hb) as [m [Hm E]].
    exists (m, 0). split; [split; [exact Hm | reflexivity] | exact E].
  - intros [m k]. exact (base_step M B C m).
  - intros [m k]. exact (base_halted M B C m).
Defined.

Lemma nec_w_billed_run : forall n x,
  fst (rc_run nec_w_billed n x) = rc_run M n (fst x).
Proof.
  induction n as [| n IH]; intros x; [reflexivity |].
  change (fst (rc_next nec_w_billed (rc_run nec_w_billed n x)) =
          rc_next M (rc_run M n (fst x))).
  simpl. rewrite IH. reflexivity.
Qed.

Lemma nec_w_billed_step_cost : ledger_carried M ->
  forall x, step_cost nec_w_billed x = step_cost M (fst x) + sur (fst x).
Proof.
  intros Hl [m k]. unfold step_cost. simpl. specialize (Hl m). lia.
Qed.

Theorem nec_w_billed_honest :
  HonestBaseExtension M B C -> HonestBaseExtension nec_w_billed B nec_w_billed_cover.
Proof.
  intros [[f Hf] [Hl [Ha2 [Hp [s [n [Hs [H0 H1]]]]]]]].
  split; [exists f; intros [m k]; exact (Hf m) |].
  split; [intros [m k]; simpl; specialize (Hl m); lia |].
  split.
  - intros [m k] E0 E1. rewrite (nec_w_billed_step_cost Hl).
    specialize (Ha2 m E0 E1). simpl. lia.
  - split; [intros [m k] E; exact (Hp m E) |].
    exists (s, 0), n. split; [split; [exact Hs | reflexivity] |].
    change (rc_cert M (fst (rc_run nec_w_billed n (s, 0))) = false /\
            rc_cert M (rc_next M (fst (rc_run nec_w_billed n (s, 0)))) = true).
    rewrite nec_w_billed_run. simpl fst. exact (conj H0 H1).
Qed.

Theorem nec_w_billed_same_latch :
  forall h, latch_factorization M B C h -> latch_factorization nec_w_billed B nec_w_billed_cover h.
Proof.
  intros h H [m k]. exact (H m).
Qed.

(** Sameness up to the schedule: the repository's observed bisimulation
    without its two cost clauses. *)
Definition nec_w_schedule_bisim (N1 N2 : RCM) (R : rc_state N1 -> rc_state N2 -> Prop) : Prop :=
  (forall m, rc_init N1 m -> exists n, rc_init N2 n /\ R m n) /\
  (forall n, rc_init N2 n -> exists m, rc_init N1 m /\ R m n) /\
  (forall m n, R m n ->
     rc_cert N1 m = rc_cert N2 n /\
     (rc_halted N1 m <-> rc_halted N2 n) /\
     R (rc_next N1 m) (rc_next N2 n)).

Theorem nec_w_billed_same_up_to_schedule :
  nec_w_schedule_bisim M nec_w_billed (fun m x => fst x = m) /\
  (forall m x, fst x = m -> base_state nec_w_billed B nec_w_billed_cover x = base_state M B C m).
Proof.
  split.
  - split; [intros m Hm; exists (m, 0); split; [split; [exact Hm | reflexivity] | reflexivity] |].
    split; [intros [m k] [Hm _]; exists m; split; [exact Hm | reflexivity] |].
    intros m [m' k] E. simpl in E. subst m'. simpl.
    split; [reflexivity | split; [tauto | reflexivity]].
  - intros m [m' k] E. simpl in E. subst m'. reflexivity.
Qed.

End Billed.

(** The repository's observed bisimulation implies sameness up to the
    schedule. *)
Lemma nec_w_observed_implies_schedule_bisim :
  forall N1 N2 R, observed_core_bisim N1 N2 R -> nec_w_schedule_bisim N1 N2 R.
Proof.
  intros N1 N2 R [H1 [H2 H3]]. split; [exact H1 | split; [exact H2 |]].
  intros m n HR. destruct (H3 m n HR) as [Ec [_ [Eh [_ Hn]]]]. auto.
Qed.

(* ================================================================= *)
(** * 3. An outside decider gets the nat family right                 *)
(* ================================================================= *)

Definition nec_w_outside (d : nat -> bool) (p : nat) : bool :=
  if Nat.eqb p 0 then true else if Nat.eqb p 2 then negb (d 2) else false.

Theorem nec_w_outside_decider :
  forall d : nat -> bool,
    (forall p, nec_w_outside d p = true <-> nat_admits d p) /\
    ~ @Representable (nat_substrate d) (fun p => if nec_w_outside d p then 1 else 0).
Proof.
  intros d. split.
  - intros p. unfold nec_w_outside, nat_admits, nat_run.
    destruct p as [| [| [| p]]]; simpl.
    + split; reflexivity.
    + split; discriminate.
    + destruct (d 2); simpl; split; congruence.
    + split; discriminate.
  - intros H. specialize (H 2). unfold nec_w_outside in H. simpl in H.
    destruct (d 2); discriminate.
Qed.

Print Assumptions nec_w_forgetful_window_no_counter.
Print Assumptions nec_w_forgetful_window_no_flag.
Print Assumptions nec_w_forget_needs_settable.
Print Assumptions nec_w_billed_honest.
Print Assumptions nec_w_billed_same_latch.
Print Assumptions nec_w_billed_same_up_to_schedule.
Print Assumptions nec_w_billed_step_cost.
Print Assumptions nec_w_observed_implies_schedule_bisim.
Print Assumptions nec_w_outside_decider.
