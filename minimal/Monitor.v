(* SCOPE NOTE: standalone proof scope.
   Implements the exact current-edition checking task on a three-state carrier.
   The stated interface supplies the hypotheses; no concrete native-machine
   implementation is assumed. *)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.

Inductive state := Zero | OneUnchecked | OneChecked.
Inductive action := Write (b:bool) | Check | Idle.
Definition step s a := match a with
 | Write false=>Zero | Write true=>OneUnchecked
 | Check=>match s with Zero=>Zero | _=>OneChecked end
 | Idle=>s end.
Definition data s := match s with Zero=>false | _=>true end.
Definition valid s := match s with OneChecked=>true | _=>false end.
Fixpoint run_from s p := match p with []=>s | a::rest=>run_from(step s a) rest end.
Definition run p := run_from Zero p.

(* Independent trace specification: the property being checked is data=true.
   Write, even a same-value write, starts a new edition. Successful Check
   establishes the claim, and Idle preserves it. There is no version number. *)
Definition specification_step (bh:bool*bool) a := let '(b,h):=bh in
 match a with Write x=>(x,false) | Check=>(b,h||b) | Idle=>(b,h) end.
Fixpoint specification_from bh p := match p with
 | []=>bh | a::rest=>specification_from(specification_step bh a) rest end.
Definition specification p := specification_from(false,false) p.
Lemma step_matches_history : forall s a,
 (data(step s a),valid(step s a))=specification_step(data s,valid s) a.
Proof. destruct s; intros [b| |]; try destruct b; reflexivity. Qed.
Theorem every_program_matches_history : forall p s,
 (data(run_from s p),valid(run_from s p))=specification_from(data s,valid s) p.
Proof. induction p; intro s; simpl; [reflexivity|rewrite IHp,step_matches_history; reflexivity]. Qed.
Theorem exact_historical_verdict : forall p,
 valid(run p)=snd(specification p).
Proof. intro p; pose proof(f_equal snd (every_program_matches_history p Zero)) as H; exact H. Qed.
Theorem truth_soundness : forall s,valid s=true -> data s=true.
Proof. destruct s; simpl; intros; discriminate || reflexivity. Qed.
Theorem every_full_state_is_reachable : forall s,exists p,run p=s.
Proof. destruct s.
 - exists []; reflexivity.
 - exists [Write true]; reflexivity.
 - exists [Write true;Check]; reflexivity.
Qed.
Lemma unchecked_steps_keep_verdict_false : forall s p,
 valid s=false -> ~In Check p -> valid(run_from s p)=false.
Proof.
 intros s p; revert s; induction p; intros s Hs Hno; simpl; [exact Hs|].
 apply IHp; [destruct a as [b| |]; try destruct b; simpl; auto; exfalso; apply Hno; left; reflexivity|].
 intro Hin; apply Hno; right; exact Hin.
Qed.
Theorem no_unchecked_forgery : forall p,~In Check p -> valid(run p)=false.
Proof. intros p H; apply unchecked_steps_keep_verdict_false; auto. Qed.
Theorem reachability_does_not_supply_unchecked_reachability :
 (forall s,exists p,run p=s) /\
 ~exists p,~In Check p /\ run p=OneChecked.
Proof.
 split; [apply every_full_state_is_reachable|].
 intros [p [Hno Hrun]]; pose proof(no_unchecked_forgery p Hno); rewrite Hrun in H; discriminate.
Qed.
Theorem two_histories_one_data_two_states :
 data(run [Write true])=data(run [Write true;Check]) /\
 valid(run [Write true])=false /\ valid(run [Write true;Check])=true /\
 run [Write true]<>run [Write true;Check].
Proof. repeat split; reflexivity || discriminate. Qed.
Theorem writes_invalidate_without_versions : forall s b,
 valid(step s (Write b))=false /\ data(step s (Write b))=b.
Proof. destruct b; split; reflexivity. Qed.
Theorem current_verdict_is_not_permanent :
 valid OneChecked=true /\ valid(step OneChecked (Write true))=false.
Proof. split; reflexivity. Qed.
Theorem repeated_check_merges_inside_one_fibre :
 OneUnchecked<>OneChecked /\ data OneUnchecked=data OneChecked /\
 step OneUnchecked Check=step OneChecked Check.
Proof. repeat split; reflexivity || discriminate. Qed.

(* Ordinary programmability is a fixed map once the remaining program is data. *)
Definition autonomous (sp:state*list action) := match sp with
 | (s,[]) => (s,[]) | (s,a::rest)=>(step s a,rest) end.
Theorem single_fixed_map_contains_arbitrary_programs : forall s a rest,
 autonomous(s,a::rest)=(step s a,rest).
Proof. reflexivity. Qed.

(* This rechecks at use, without changing the stored historical record.
   It guarantees truth of a use, not the stronger prior-check provenance task. *)
Definition use_gate (b saved:bool) := saved && b.
Theorem sound_use_does_not_force_saved_record_mutation :
 (forall b saved,use_gate b saved=true -> b=true) /\
 use_gate true true=true /\ use_gate false true=false.
Proof. split; [destruct b,saved; simpl; intros; discriminate || reflexivity|].
 split; reflexivity. Qed.
