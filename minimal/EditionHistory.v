(* SCOPE NOTE: standalone proof scope.
   Relates the edition archive implementation to its separately defined history evaluator.
   The stated interface supplies the hypotheses; no concrete native-machine
   implementation is assumed. *)

From Coq Require Import List Bool.
From Minimal Require Import Task EditionCapacity.
Import ListNotations.
Definition translate(i:EditionCapacity.command):@Task.command bool :=
 match i with
 | EditionCapacity.Write b=>Task.Write b|EditionCapacity.Idle=>Task.Idle
 | EditionCapacity.Check=>Task.Check|EditionCapacity.Commit=>Task.Commit
 | EditionCapacity.Certify=>Task.Certify end.
Definition journal_state := (list bool * @Task.journal bool)%type.
Definition journal_step(i:EditionCapacity.command)(s:journal_state):journal_state :=
 (match i with EditionCapacity.Write _=>fst s++[Task.published(snd s)]|_=>fst s end,
  Task.logstep (fun b=>b)(translate i)(snd s)).
Fixpoint journal_run(word:list EditionCapacity.command)(s:journal_state):journal_state :=
 match word with []=>s|i::rest=>journal_run rest(journal_step i s)end.
Definition abstract_journal(s:journal_state):EditionCapacity.state :=
 EditionCapacity.mkstate (Task.work(snd s))(fst s)
 (if Task.published(snd s) then EditionCapacity.Published
  else if Task.committed(snd s) then EditionCapacity.Committed
  else if Task.checked(snd s) then EditionCapacity.Checked else EditionCapacity.Raw).
Lemma journal_step_consistent : forall i s,
 Task.consistent (fun b=>b)(snd s) -> Task.consistent (fun b=>b)(snd(journal_step i s)).
Proof. intros i [old j] H; simpl; apply Task.journal_consistent; assumption. Qed.
Lemma abstraction_step : forall i s,
 Task.consistent (fun b=>b)(snd s) ->
 abstract_journal(journal_step i s)=EditionCapacity.step i(abstract_journal s).
Proof.
 intros i [old [b c m d e]] H; destruct i;
 unfold Task.consistent,abstract_journal,journal_step,Task.logstep,translate,EditionCapacity.step in *;
 simpl in *; destruct b,c,m,d,e; simpl in *; intuition congruence.
Qed.
Theorem all_program_history_refinement : forall word s,
 Task.consistent (fun b=>b)(snd s) ->
 abstract_journal(journal_run word s)=EditionCapacity.run word(abstract_journal s).
Proof.
 induction word as [|i word IH]; intros; simpl; auto.
 rewrite IH by (apply journal_step_consistent; assumption).
 rewrite abstraction_step by assumption; reflexivity.
Qed.
Lemma abstraction_query : forall s j,
 EditionCapacity.query(abstract_journal s)j=nth j(fst s++[Task.published(snd s)])false.
Proof.
 intros [old [b c m d e]] j; unfold EditionCapacity.query,abstract_journal; simpl.
 destruct d,m,c; reflexivity.
Qed.
Theorem exact_records_every_program : forall word b0 j,
 EditionCapacity.query(EditionCapacity.run word(EditionCapacity.mkstate b0 [] EditionCapacity.Raw))j=
 let s:=journal_run word([],Task.J b0 false false false false) in
 nth j(fst s++[Task.published(snd s)])false.
Proof.
 intros word b0 j.
 assert(H:Task.consistent (fun b=>b)(Task.J b0 false false false false))
 by (unfold Task.consistent; simpl; intuition discriminate).
 pose proof(all_program_history_refinement word ([],Task.J b0 false false false false) H) as E.
 change (abstract_journal(journal_run word ([],Task.J b0 false false false false))=
  EditionCapacity.run word(EditionCapacity.mkstate b0 [] EditionCapacity.Raw)) in E.
 rewrite <-E. apply abstraction_query.
Qed.
