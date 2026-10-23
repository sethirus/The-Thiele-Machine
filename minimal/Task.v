(* SCOPE NOTE: standalone proof scope.
   Defines a certification-history task and compares permanent history with current-workspace truth.
   The stated interface supplies the hypotheses; no concrete native-machine
   implementation is assumed. *)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.

(* The literal demand for permanent certification of CURRENT truth is inconsistent. *)
Theorem permanent_current_truth_impossible {S B : Type}
 (view:S->B) (cert:S->bool) (write:B->S->S) (P:B->bool)
 (accepted:S) (bad:B) :
 cert accepted=true -> P bad=false ->
 (forall s b,view(write b s)=b) ->
 (forall s b,cert s=true -> cert(write b s)=true) ->
 (forall s,cert s=true -> P(view s)=true) -> False.
Proof.
 intros Hy Hbad Hw Hp Hsound.
 specialize (Hsound (write bad accepted) (Hp accepted bad Hy)).
 rewrite Hw,Hbad in Hsound; discriminate.
Qed.

Inductive phase := U | C | M | D.
Section Task.
 Context {B:Type}.
 Variable P:B->bool.
 Variable permanent:bool.
 Inductive command := Write (b:B) | Idle | Check | Commit | Certify.
 Definition state := (B*phase)%type.
 Definition step (i:command) (s:state) : state :=
 let '(b,p):=s in
 match i with
 | Write b' => (b',if permanent then match p with D=>D|_=>U end else U)
 | Idle => s
 | Check => (b,match p with U=>if P b then C else U|_=>p end)
 | Commit => (b,match p with C=>M|_=>p end)
 | Certify => (b,match p with M=>D|_=>p end)
 end.
 Fixpoint run (w:list command) (s:state) : state :=
 match w with []=>s|i::rest=>run rest(step i s) end.
 Definition verdict(s:state):bool := match snd s with D=>true|_=>false end.
 Definition legal(s:state):Prop := snd s=U \/ P(fst s)=true \/ (permanent=true /\ snd s=D).
 Lemma run_app : forall u v s, run(u++v)s=run v(run u s).
 Proof. induction u; intros; simpl; auto. Qed.
 Lemma step_legal : forall i s,legal s -> legal(step i s).
 Proof.
  intros i [b p] H; destruct i,p; unfold legal,step in *; simpl in *;
   repeat match goal with |- context [if ?a then _ else _] => destruct a eqn:? end;
   simpl in *; intuition congruence.
 Qed.
 Lemma run_legal : forall w s,legal s -> legal(run w s).
 Proof. induction w; simpl; auto using step_legal. Qed.
 Definition upper(i:command)(b:B):B:=match i with Write b'=>b'|_=>b end.
 Fixpoint base_run(w:list command)(b:B):B:=
 match w with []=>b|i::rest=>base_run rest(upper i b)end.
 Lemma step_projects : forall i s,fst(step i s)=upper i(fst s).
 Proof. intros [] [x []]; reflexivity. Qed.
 Theorem autonomous_workspace : forall w s,fst(run w s)=base_run w(fst s).
 Proof. induction w; intros; simpl; auto. rewrite IHw,step_projects; reflexivity. Qed.
 Theorem writes_invalidate_before_publication : forall b b' p,p<>D -> step(Write b')(b,p)=(b',U).
 Proof. intros b b' [] H; try contradiction; unfold step; destruct permanent; reflexivity. Qed.
 Theorem historical_certificate_survives : permanent=true -> forall i s,
 verdict s=true -> verdict(step i s)=true.
 Proof. intros Hp [] [x []]; simpl; try discriminate; rewrite ?Hp; auto. Qed.
 Theorem current_certificate_requires_truth : permanent=false -> forall s,
 legal s -> verdict s=true -> P(fst s)=true.
 Proof. intros Hp [b []]; unfold legal,verdict; simpl; intuition congruence. Qed.
 Theorem only_certify_publishes : forall i s,
 verdict s=false -> verdict(step i s)=true -> i=Certify.
 Proof. intros [] [x []]; unfold verdict,step; simpl;
  destruct permanent; try destruct(P x); simpl; intros; congruence. Qed.

 (* Independent chronological journal: records actual check/commit/publication
    events for the current edition, plus whether any publication ever occurred.
    The implementation above does not store this journal. *)
 Record journal := J { work:B; checked:bool; committed:bool; published:bool; ever:bool }.
 Definition logstep(i:command)(j:journal):journal:=
 match i with
 | Write b => J b false false false (ever j)
 | Idle => j
 | Check => J (work j) (checked j || P(work j)) (committed j) (published j) (ever j)
 | Commit => J (work j) (checked j) (committed j || checked j) (published j) (ever j)
 | Certify => J (work j) (checked j) (committed j)
                   (published j || committed j) (ever j || committed j)
 end.
 Fixpoint logrun(w:list command)(j:journal):journal:=
 match w with []=>j|i::rest=>logrun rest(logstep i j)end.
 Definition logverdict(j:journal):bool:=if permanent then ever j else published j.
 Definition consistent(j:journal):Prop :=
 (published j=true -> committed j=true) /\
 (committed j=true -> checked j=true) /\
 (checked j=true -> P(work j)=true) /\
 (published j=true -> ever j=true).
 Definition compress(j:journal):state :=
 (work j,if logverdict j then D else if committed j then M else if checked j then C else U).
 Lemma journal_consistent : forall i j,consistent j -> consistent(logstep i j).
 Proof.
  intros i [b c m d e] H; destruct i; unfold consistent,logstep in *; simpl in *;
   destruct c,m,d,e; simpl in *; try destruct(P b); intuition congruence.
 Qed.
 Lemma compression_step : forall i j,consistent j -> compress(logstep i j)=step i(compress j).
 Proof.
  intros i [b c m d e] H; destruct i; unfold consistent,compress,logverdict,logstep in *;
   simpl in *; destruct permanent,c,m,d,e; simpl in *; destruct(P b); simpl in *;
   intuition congruence.
 Qed.
 Theorem journal_refinement : forall w j,consistent j -> compress(logrun w j)=run w(compress j).
 Proof.
  induction w; intros; simpl; auto.
  rewrite IHw by (apply journal_consistent; assumption).
  rewrite compression_step by assumption; reflexivity.
 Qed.
 Theorem exact_history_all_programs : forall w b0,
 verdict(run w(b0,U))=logverdict(logrun w(J b0 false false false false)).
 Proof.
  intros. assert(Hc:consistent(J b0 false false false false)) by (unfold consistent; simpl; intuition discriminate).
  pose proof(journal_refinement w _ Hc) as H.
  assert(H0:compress(J b0 false false false false)=(b0,U)) by (unfold compress,logverdict; destruct permanent; reflexivity).
  rewrite H0 in H; rewrite <-H.
  unfold compress,verdict; simpl. destruct(logverdict(logrun w(J b0 false false false false))); simpl; auto.
  destruct(committed(logrun w(J b0 false false false false))),
          (checked(logrun w(J b0 false false false false))); reflexivity.
 Qed.

 Variable good:B.
 Hypothesis good_true:P good=true.
 Definition witness(b:B)(p:phase):list command:=
 match p with
 | U => [Write b]
 | C => [Write b;Check]
 | M => [Write b;Check;Commit]
 | D => if P b then [Write b;Check;Commit;Certify]
        else [Write good;Check;Commit;Certify;Write b]
 end.
 Lemma witness_reaches : forall b p b0,legal(b,p) -> run(witness b p)(b0,U)=(b,p).
 Proof.
  intros b p b0 H; destruct p; unfold witness; simpl;
   unfold legal in H; simpl in H; destruct permanent eqn:Ep; simpl in *;
   destruct(P b) eqn:Eb; simpl in *; rewrite ?good_true; simpl; rewrite ?Ep,?Eb; simpl; intuition congruence.
 Qed.
 Definition phases(b:B):list phase:=if P b then [U;C;M;D] else if permanent then [U;D] else [U].
 Lemma phases_legal : forall b p,In p(phases b) <-> legal(b,p).
 Proof. intros b []; unfold phases,legal; simpl; destruct(P b),permanent; simpl; intuition congruence. Qed.
 Lemma phases_distinct : forall b,NoDup(phases b).
 Proof. intro; unfold phases; destruct(P b),permanent; repeat constructor; simpl; intuition discriminate. Qed.
 Definition carrier(bases:list B):list state:=flat_map(fun b=>map(pair b)(phases b))bases.
 Fixpoint positives(bases:list B):nat:=match bases with []=>0|b::rest=>(if P b then 1 else 0)+positives rest end.
 Theorem carrier_size : forall bases,length(carrier bases)=
  if permanent then 2*length bases+2*positives bases else length bases+3*positives bases.
 Proof.
  induction bases as [|b rest IH].
  - destruct permanent; reflexivity.
  - cbn [carrier flat_map].
    rewrite app_length,map_length. fold (carrier rest).
    unfold carrier, phases, state in *; destruct permanent eqn:Ep; cbn [length positives] in *;
      destruct(P b); simpl in *; lia.
 Qed.
 Definition signature(s:state):bool*bool*bool:=
  (verdict(run [Commit;Certify] s),verdict(run [Certify] s),verdict s).
 Lemma signature_separates : forall b p q,signature(b,p)=signature(b,q) -> p=q.
 Proof. intros b [] []; unfold signature,verdict; simpl; intros; congruence. Qed.
End Task.
