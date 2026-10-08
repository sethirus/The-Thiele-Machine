(** FragmentSmall.v: the finite fragment that pays for its merges, run by
    the small machine.

    The room argument (a permanent flip on a finite machine merges two
    states; charge every merge; the toll follows) needs a finite state
    space. The small machine's counters, versions and ledger are unbounded,
    so it is not finite. This file faces that the same way the book does:
    build a finite machine on which every premise is a theorem, then show a
    small-machine program runs it through a narrow window and pays exactly
    its price.

    The finite machine is the book's: four slots times a flag, eight states,
    three moves.
      stamp     set the flag, go to the next slot     costs 1
      jump a    go to slot a, keep the flag           costs 2
      next      go to the next slot, keep the flag    costs 0

    What is proved (every result closed under the global context):

      1. The room, on any machine. On a finite machine with a permanent
         reading, a move that turns the reading on merges two states
         [frag_flip_merges]; with every merge priced, the toll follows
         [frag_toll_from_merges].
      2. The eight-state machine meets every premise as a theorem: finite
         [frag_fin_finite], permanent [frag_fin_permanent], next forgets
         nothing [frag_next_injective], stamp and jump merge
         [frag_stamp_merges, frag_jump_merges], every merge is priced
         [frag_fin_merges_priced]. So the toll holds on it
         [frag_fin_toll], and it is a CertificationSystem
         [frag_cert_system]. Each move's price is exactly the number of
         halvings in its largest squeeze: no fibre is bigger than 2^cost,
         and some fibre is exactly that big [frag_price_is_squeeze].
      3. The small machine runs it. The window reads the program counter
         modulo 4 as the slot and the certified flag as the flag. On live
         states (trap latch down, the fact "A >= 0" about A's current
         version in the table, a commitment on the channel):
           stamp  is  CERTIFY                                 (pays 1)
           next   is  INC B                                   (pays 0)
           jump a is  COMMIT, COMMIT, INC B, DEC B a          (pays 2)
         For every live state and move, the window of the result is the
         finite machine's step of the window, the result is live
         [frag_runs_finite_machine], and the ledger rises by exactly the
         finite price [frag_pays_finite_price]; the same over every list of
         moves [frag_runs_finite_trace]; and a run from flag down to flag
         up raises the ledger by at least 1, which is the finite toll
         carried through the window [frag_certification_paid].
      4. The whole program from a clean start. Two setup instructions,
         CHECK "A >= 0" and COMMIT "A >= 0", reach a live state with
         ledger 2 [frag_setup_live]. After them, any list of finite moves
         runs exactly as on the finite machine, at ledger 2 plus the finite
         price [frag_program_runs], and a raised flag comes with the earned
         chain of ThieleComplete.v [frag_program_earned].
      5. The small machine as a whole is not merge-priced, and says so.
         CERTIFY merges [frag_small_certify_merges]; every step that raises
         the flag is a CERTIFY, merges and costs at least 1
         [frag_small_certifying_step_priced_merge]; DEC A 2 merges two
         full states and costs 0 [frag_small_dec_free_merge]; so "every
         merge is priced" fails on the small machine
         [frag_small_not_merge_priced]. Its schedule puts the floor on the
         flag, not on forgetting in general.

    Limits. The jump's charge of two is a choice the program makes: two
    COMMITs that change nothing but the program counter and the channel.
    The small machine allows it and does not force it. The window is a
    projection; the full state keeps more than the eight finite states do.
    The setup's claim "A >= 0" is true of every value, so its CHECK can't
    fail; it is there because the small machine won't certify without a
    checked, committed claim.

    Dependencies: Coq standard library, ThieleComplete.v and the files it
    requires. No axioms, no Admitted.                                      *)

From Coq Require Import List Arith Lia Bool.
From Coq Require Import Logic.FinFun.
Import ListNotations.
Require Import Minimal.ThieleComplete.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.

(* ================================================================= *)
(* 1. The room, on any machine.                                       *)
(* ================================================================= *)

Section Room.

Variables (St Mv : Type).
Variable step : St -> Mv -> St.
Variable flag : St -> bool.
Variable cost : Mv -> nat.

(* A duplicate-free list names every state. *)
Definition frag_finite (all : list St) : Prop := NoDup all /\ forall s, In s all.

(* Once up, the reading stays up. *)
Definition frag_permanent : Prop := forall s m, flag s = true -> flag (step s m) = true.

(* The move forgets nothing. A move that is not injective merges. *)
Definition frag_injective (m : Mv) : Prop := forall a b, step a m = step b m -> a = b.

(* Merge pricing: every move that merges costs at least 1. *)
Definition frag_merges_priced : Prop := forall m, ~ frag_injective m -> cost m >= 1.

(* The toll: every move that turns the reading on costs at least 1. *)
Definition frag_toll : Prop :=
  forall s m, flag s = false -> flag (step s m) = true -> cost m >= 1.

Definition frag_up (all : list St) : list St := filter flag all.

Lemma frag_up_spec : forall all, frag_finite all -> forall t, In t (frag_up all) <-> flag t = true.
Proof.
  intros all [_ Hall] t. unfold frag_up. rewrite filter_In. split.
  - intros [_ H]. exact H.
  - intro H. split; [apply Hall | exact H].
Qed.

Theorem frag_flip_merges : forall all s m,
  frag_finite all -> frag_permanent -> flag s = false -> flag (step s m) = true ->
  ~ frag_injective m.
Proof.
  intros all s m Hfin Hperm Hs Hflip Hinj.
  set (L := frag_up all). set (f := fun t => step t m).
  assert (HndL : NoDup L) by (apply NoDup_filter, (proj1 Hfin)).
  assert (HndM : NoDup (map f L)).
  { apply Injective_map_NoDup; [| exact HndL]. intros a b Hab. apply Hinj. exact Hab. }
  assert (Hincl : incl (map f L) L).
  { intros y Hy. apply in_map_iff in Hy as [x [<- Hx]].
    apply (frag_up_spec all Hfin). apply (frag_up_spec all Hfin) in Hx. apply Hperm, Hx. }
  assert (Hback : incl L (map f L)).
  { apply NoDup_length_incl; [exact HndM | rewrite map_length; lia | exact Hincl]. }
  assert (Hfs : In (f s) (map f L)) by (apply Hback, (frag_up_spec all Hfin), Hflip).
  apply in_map_iff in Hfs as [c [Hc HcL]].
  apply Hinj in Hc. subst c. apply (frag_up_spec all Hfin) in HcL. congruence.
Qed.

Theorem frag_toll_from_merges : forall all,
  frag_finite all -> frag_permanent -> frag_merges_priced -> frag_toll.
Proof.
  intros all Hfin Hperm Hprice s m Hs Hflip.
  apply Hprice. eapply frag_flip_merges; eauto.
Qed.

End Room.

(* ================================================================= *)
(* 2. The eight-state machine.                                        *)
(* ================================================================= *)

Inductive frag_slot : Type := FS0 | FS1 | FS2 | FS3.

Definition frag_next_slot (p : frag_slot) : frag_slot :=
  match p with FS0 => FS1 | FS1 => FS2 | FS2 => FS3 | FS3 => FS0 end.

Definition frag_fstate : Type := (frag_slot * bool)%type.

Inductive frag_move : Type := FStamp | FJump (a : frag_slot) | FNext.

Definition frag_step (x : frag_fstate) (m : frag_move) : frag_fstate :=
  match m with
  | FStamp => (frag_next_slot (fst x), true)
  | FJump a => (a, snd x)
  | FNext => (frag_next_slot (fst x), snd x)
  end.

Definition frag_flag (x : frag_fstate) : bool := snd x.

Definition frag_cost (m : frag_move) : nat :=
  match m with FStamp => 1 | FJump _ => 2 | FNext => 0 end.

Definition frag_all : list frag_fstate :=
  [(FS0, false); (FS1, false); (FS2, false); (FS3, false);
   (FS0, true); (FS1, true); (FS2, true); (FS3, true)].

Theorem frag_fin_finite : frag_finite frag_fstate frag_all.
Proof.
  split.
  - repeat constructor; simpl; intuition discriminate.
  - intros [p c]. destruct p, c; simpl; tauto.
Qed.

Theorem frag_fin_permanent : frag_permanent frag_fstate frag_move frag_step frag_flag.
Proof. intros [p c] m Hc. destruct m; simpl in *; auto. Qed.

Theorem frag_next_injective : frag_injective frag_fstate frag_move frag_step FNext.
Proof.
  intros [p c] [q d] H. simpl in H. inversion H as [[Hpq Hcd]].
  destruct p, q; simpl in Hpq; try discriminate; reflexivity.
Qed.

Theorem frag_stamp_merges : ~ frag_injective frag_fstate frag_move frag_step FStamp.
Proof. intro Hinj. specialize (Hinj (FS0, false) (FS0, true) eq_refl). discriminate. Qed.

Theorem frag_jump_merges : forall a, ~ frag_injective frag_fstate frag_move frag_step (FJump a).
Proof. intros a Hinj. specialize (Hinj (FS0, false) (FS1, false) eq_refl). discriminate. Qed.

Theorem frag_fin_merges_priced : frag_merges_priced frag_fstate frag_move frag_step frag_cost.
Proof.
  intros m Hmerge. destruct m; simpl; [lia | lia |].
  exfalso. exact (Hmerge frag_next_injective).
Qed.

(* The toll on eight states, derived from finiteness, permanence and merge
   pricing, not assumed. *)
Theorem frag_fin_toll : frag_toll frag_fstate frag_move frag_step frag_flag frag_cost.
Proof.
  exact (frag_toll_from_merges _ _ frag_step frag_flag frag_cost frag_all
           frag_fin_finite frag_fin_permanent frag_fin_merges_priced).
Qed.

Definition frag_cert_system : CertificationSystem :=
  mk_cert_system frag_fstate frag_move frag_step frag_cost frag_flag frag_fin_toll.

Definition frag_slot_eqb (p q : frag_slot) : bool :=
  match p, q with
  | FS0, FS0 | FS1, FS1 | FS2, FS2 | FS3, FS3 => true
  | _, _ => false
  end.

Definition frag_fstate_eqb (x y : frag_fstate) : bool :=
  frag_slot_eqb (fst x) (fst y) && Bool.eqb (snd x) (snd y).

(* The fibre of y under move m: the states m sends to y. *)
Definition frag_fibre (m : frag_move) (y : frag_fstate) : list frag_fstate :=
  filter (fun x => frag_fstate_eqb (frag_step x m) y) frag_all.

(* Each move's price is exactly the halvings in its largest squeeze. *)
Theorem frag_price_is_squeeze : forall m,
  (forall y, length (frag_fibre m y) <= 2 ^ frag_cost m) /\
  (exists y, length (frag_fibre m y) = 2 ^ frag_cost m).
Proof.
  intro m. split.
  - intros [q d]. destruct m as [| a |]; [| destruct a |]; destruct q, d; vm_compute; lia.
  - destruct m as [| a |].
    + exists (FS1, true). reflexivity.
    + exists (a, false). destruct a; reflexivity.
    + exists (FS0, false). reflexivity.
Qed.

(* Runs and total price on the finite machine. *)
Fixpoint frag_frun (t : list frag_move) (x : frag_fstate) : frag_fstate :=
  match t with [] => x | m :: rest => frag_frun rest (frag_step x m) end.

Fixpoint frag_fcost (t : list frag_move) : nat :=
  match t with [] => 0 | m :: rest => frag_cost m + frag_fcost rest end.

(* A finite run from flag down to flag up costs at least 1, by the toll. *)
Lemma frag_frun_flip_paid : forall t x,
  frag_flag x = false -> frag_flag (frag_frun t x) = true -> frag_fcost t >= 1.
Proof.
  induction t as [| m t IH]; intros x H0 H1; simpl in *; [congruence |].
  destruct (frag_flag (frag_step x m)) eqn:Hm.
  - pose proof (frag_fin_toll x m H0 Hm). lia.
  - pose proof (IH _ Hm H1). lia.
Qed.

(* ================================================================= *)
(* 3. The small machine runs it.                                      *)
(* ================================================================= *)

Fixpoint frag_slot_of (n : nat) : frag_slot :=
  match n with 0 => FS0 | S k => frag_next_slot (frag_slot_of k) end.

Definition frag_nat (a : frag_slot) : nat :=
  match a with FS0 => 0 | FS1 => 1 | FS2 => 2 | FS3 => 3 end.

Lemma frag_slot_of_nat : forall a, frag_slot_of (frag_nat a) = a.
Proof. intros []; reflexivity. Qed.

(* The setup claim: counter A is at least 0. *)
Definition frag_q : E.prop := E.PGe 0.

(* Live: the trap latch is down, the fact "A >= 0" about A's current
   version is in the table, and the channel holds a commitment. *)
Definition frag_live (s : E.state) : Prop :=
  E.err (E.core_of s) = false /\
  In (E.claim (E.core_of s) frag_q E.CA) (E.facts (E.core_of s)) /\
  E.chan (E.core_of s) <> None.

(* The narrow window: program counter modulo 4, and the flag. *)
Definition frag_window (s : E.state) : frag_fstate :=
  (frag_slot_of (E.pc (E.core_of s)), E.cert s).

Definition frag_compile (m : frag_move) : list E.instr :=
  match m with
  | FStamp => [E.CERTIFY]
  | FNext => [E.INC E.CB]
  | FJump a => [E.COMMIT frag_q E.CA; E.COMMIT frag_q E.CA; E.INC E.CB; E.DEC E.CB (frag_nat a)]
  end.

Definition frag_compile_all (t : list frag_move) : list E.instr := flat_map frag_compile t.

Lemma frag_in_existsb : forall f facts,
  In f facts -> existsb (E.fact_eqb f) facts = true.
Proof.
  intros f facts H. apply existsb_exists. exists f.
  split; [exact H | apply E.fact_eqb_eq; reflexivity].
Qed.

(* On a live state, COMMIT "A >= 0" succeeds: it moves the program counter
   on, puts the fact on the channel, and charges 1. *)
Lemma frag_exec_commit : forall s, frag_live s ->
  E.exec s (E.COMMIT frag_q E.CA)
  = E.mkst (E.commit_to (E.core_of s) (E.claim (E.core_of s) frag_q E.CA)) (E.mu s + 1) (E.cert s).
Proof.
  intros [k mu c] [He [Hin _]]. simpl in He, Hin.
  unfold E.exec, E.cexec, E.commit_ok. simpl E.core_of. rewrite He.
  rewrite (frag_in_existsb _ _ Hin). simpl. rewrite orb_false_r. reflexivity.
Qed.

Lemma frag_live_commit : forall s, frag_live s ->
  frag_live (E.mkst (E.commit_to (E.core_of s) (E.claim (E.core_of s) frag_q E.CA))
                    (E.mu s + 1) (E.cert s)).
Proof.
  intros [[ca cb va vb pc facts chan err] mu c] [He [Hin _]].
  unfold frag_live in *. simpl in *. repeat split; auto; discriminate.
Qed.

Theorem frag_runs_finite_machine : forall s m, frag_live s ->
  frag_window (E.run (frag_compile m) s) = frag_step (frag_window s) m /\
  frag_live (E.run (frag_compile m) s).
Proof.
  intros s m Hl. destruct m as [| a |].
  - destruct s as [[ca cb va vb pc facts chan err] mu c]. destruct Hl as [Herr [Hin Hch]].
    simpl in Herr, Hin, Hch. subst err. destruct chan as [f |]; [| congruence].
    unfold frag_window, frag_live; simpl.
    rewrite orb_true_r. repeat split; auto; try discriminate.
  - cbn [frag_compile E.run].
    rewrite (frag_exec_commit s Hl).
    rewrite (frag_exec_commit _ (frag_live_commit s Hl)).
    destruct s as [[ca cb va vb pc facts chan err] mu c]. destruct Hl as [Herr [Hin Hch]].
    simpl in Herr, Hin, Hch. subst err.
    unfold frag_window, frag_live; simpl.
    rewrite frag_slot_of_nat, !orb_false_r. repeat split; auto; try discriminate.
  - destruct s as [[ca cb va vb pc facts chan err] mu c]. destruct Hl as [Herr [Hin Hch]].
    simpl in Herr, Hin, Hch. subst err.
    unfold frag_window, frag_live; simpl.
    rewrite orb_false_r. repeat split; auto; try discriminate.
Qed.

Theorem frag_pays_finite_price : forall s m,
  E.mu (E.run (frag_compile m) s) = E.mu s + frag_cost m.
Proof. intros s m. rewrite E.mu_conservation_trace. destruct m; reflexivity. Qed.

Theorem frag_runs_finite_trace : forall t s, frag_live s ->
  frag_window (E.run (frag_compile_all t) s) = frag_frun t (frag_window s) /\
  frag_live (E.run (frag_compile_all t) s) /\
  E.mu (E.run (frag_compile_all t) s) = E.mu s + frag_fcost t.
Proof.
  induction t as [| m t IH]; intros s Hl; simpl; [auto |].
  unfold frag_compile_all in *. simpl. rewrite E.run_app.
  destruct (frag_runs_finite_machine s m Hl) as [Hw Hl'].
  destruct (IH _ Hl') as [Hw2 [Hl2 Hm2]].
  rewrite Hw2, Hw, Hm2, frag_pays_finite_price. split; [reflexivity |]. split; [exact Hl2 | lia].
Qed.

(* A run of the fragment from flag down to flag up pays at least 1: the
   finite toll, proved from finiteness, permanence and merge pricing,
   carried through the window. *)
Theorem frag_certification_paid : forall t s, frag_live s ->
  E.cert s = false -> E.cert (E.run (frag_compile_all t) s) = true ->
  E.mu (E.run (frag_compile_all t) s) >= E.mu s + 1.
Proof.
  intros t s Hl H0 H1.
  destruct (frag_runs_finite_trace t s Hl) as [Hw [_ Hm]].
  assert (Hf : frag_flag (frag_frun t (frag_window s)) = true).
  { rewrite <- Hw. exact H1. }
  pose proof (frag_frun_flip_paid t (frag_window s) H0 Hf). lia.
Qed.

(* ================================================================= *)
(* 4. The whole program from a clean start.                           *)
(* ================================================================= *)

Definition frag_setup : list E.instr := [E.CHECK frag_q E.CA; E.COMMIT frag_q E.CA].

Theorem frag_setup_live : forall a b,
  frag_live (E.run frag_setup (E.start a b)) /\
  frag_window (E.run frag_setup (E.start a b)) = (FS3, false) /\
  E.mu (E.run frag_setup (E.start a b)) = 2.
Proof.
  intros a b. unfold frag_live, frag_window. simpl.
  repeat split; auto; try discriminate.
Qed.

Theorem frag_program_runs : forall a b t,
  frag_window (E.run (frag_setup ++ frag_compile_all t) (E.start a b)) = frag_frun t (FS3, false) /\
  E.mu (E.run (frag_setup ++ frag_compile_all t) (E.start a b)) = 2 + frag_fcost t.
Proof.
  intros a b t. rewrite E.run_app.
  destruct (frag_setup_live a b) as [Hl [Hw Hm]].
  destruct (frag_runs_finite_trace t _ Hl) as [Hw2 [_ Hm2]].
  rewrite Hw2, Hw, Hm2, Hm. split; reflexivity.
Qed.

(* A raised flag on this program stands on a passing CHECK and a COMMIT of
   the same claim: the earned chain of ThieleComplete.v. *)
Theorem frag_program_earned : forall a b t,
  E.cert (E.run (frag_setup ++ frag_compile_all t) (E.start a b)) = true ->
  earned_chain earned_interface (E.start a b) (frag_setup ++ frag_compile_all t).
Proof.
  intros a b t H. apply earned_chain_holds; [apply E.start_clean | exact H].
Qed.

(* ================================================================= *)
(* 5. The small machine as a whole is not merge-priced.               *)
(* ================================================================= *)

Definition frag_f0 : E.fact := E.mkfact E.PZero E.CA 0.
Definition frag_k0 : E.core := E.mkcore 0 0 0 0 1 [] (Some frag_f0) false.

Theorem frag_small_certify_merges : ~ frag_injective E.state E.instr E.exec E.CERTIFY.
Proof.
  intro Hinj.
  assert (H : E.exec (E.mkst frag_k0 0 false) E.CERTIFY = E.exec (E.mkst frag_k0 0 true) E.CERTIFY)
    by reflexivity.
  apply Hinj in H. inversion H.
Qed.

Theorem frag_small_certifying_step_priced_merge : forall s i,
  E.cert s = false -> E.cert (E.exec s i) = true ->
  i = E.CERTIFY /\ ~ frag_injective E.state E.instr E.exec i /\ E.cost i >= 1.
Proof.
  intros s i H0 H1. destruct (E.only_certify_certifies s i H0 H1) as [-> _].
  split; [reflexivity |]. split; [exact frag_small_certify_merges | simpl; lia].
Qed.

Theorem frag_small_dec_free_merge :
  ~ frag_injective E.state E.instr E.exec (E.DEC E.CA 2) /\ E.cost (E.DEC E.CA 2) = 0.
Proof.
  split; [| reflexivity]. intro Hinj.
  assert (H : E.exec (E.mkst (E.mkcore 0 0 1 0 1 [] None false) 0 false) (E.DEC E.CA 2)
            = E.exec (E.mkst (E.mkcore 1 0 0 0 1 [] None false) 0 false) (E.DEC E.CA 2))
    by reflexivity.
  apply Hinj in H. inversion H.
Qed.

Theorem frag_small_not_merge_priced : ~ frag_merges_priced E.state E.instr E.exec E.cost.
Proof.
  intro H. destruct frag_small_dec_free_merge as [Hm Hc].
  pose proof (H _ Hm). lia.
Qed.

(* ================================================================= *)
(* Assumption audit. Every line must print                            *)
(* "Closed under the global context".                                 *)
(* ================================================================= *)

Print Assumptions frag_flip_merges.
Print Assumptions frag_toll_from_merges.
Print Assumptions frag_fin_finite.
Print Assumptions frag_fin_permanent.
Print Assumptions frag_next_injective.
Print Assumptions frag_stamp_merges.
Print Assumptions frag_jump_merges.
Print Assumptions frag_fin_merges_priced.
Print Assumptions frag_fin_toll.
Print Assumptions frag_cert_system.
Print Assumptions frag_price_is_squeeze.
Print Assumptions frag_frun_flip_paid.
Print Assumptions frag_runs_finite_machine.
Print Assumptions frag_pays_finite_price.
Print Assumptions frag_runs_finite_trace.
Print Assumptions frag_certification_paid.
Print Assumptions frag_setup_live.
Print Assumptions frag_program_runs.
Print Assumptions frag_program_earned.
Print Assumptions frag_small_certify_merges.
Print Assumptions frag_small_certifying_step_priced_merge.
Print Assumptions frag_small_dec_free_merge.
Print Assumptions frag_small_not_merge_priced.
