From Coq Require Import List Bool Arith Lia.
From Minimal Require Import EarnedCore CertifiedHistory.
Import ListNotations.

Definition channel_backed (s:state) : Prop :=
 forall f, chan(core_of s)=Some f -> In f(facts(core_of s)).

Lemma channel_backed_step : forall s i,
 channel_backed s -> channel_backed(exec s i).
Proof.
 intros s i H f Hch; unfold exec in *; simpl in *.
 destruct(chan_step(core_of s)i) as [Hold|[p [c [Hi [Hok Hnew]]]]].
 - rewrite Hold in Hch; apply facts_keep; apply H; exact Hch.
 - apply facts_keep. apply commit_ok_iff in Hok as [_ Hin].
   rewrite Hnew in Hch; inversion Hch; subst; exact Hin.
Qed.

Lemma record_supported_step : forall s rs i,
 channel_backed s -> incl rs(facts(core_of s)) ->
 incl (update_record s i rs)(facts(core_of(exec s i))).
Proof.
 intros s rs i Hch Hr f Hin; unfold update_record in Hin.
 destruct(emit s i) as [g|] eqn:E.
 - apply insert_membership in Hin as [->|Hin].
   + apply facts_keep; apply Hch. unfold emit in E.
     destruct(fires(core_of s)i); congruence.
   + apply facts_keep; apply Hr; exact Hin.
 - apply facts_keep; apply Hr; exact Hin.
Qed.

Theorem records_supported_by_native_facts : forall word s rs,
 channel_backed s -> incl rs(facts(core_of s)) ->
 incl (snd(recorded_run word(s,rs))) (facts(core_of(run word s))).
Proof.
 induction word as [|i word IH]; intros s rs Hch Hr; simpl; [exact Hr|].
 apply IH; auto using channel_backed_step, record_supported_step.
Qed.

Lemma native_table_cap_run : forall word s,
 length(facts(core_of s))<=fact_cap ->
 length(facts(core_of(run word s)))<=fact_cap.
Proof.
 induction word; intros; simpl; auto.
 apply IHword; apply facts_bounded_step; assumption.
Qed.

Theorem clean_certified_archive_bound : forall word s,
 clean_start s ->
 incl(snd(recorded_run word(s,[])))(facts(core_of(run word s))) /\
 NoDup(snd(recorded_run word(s,[]))) /\
 length(snd(recorded_run word(s,[]))) <= length(facts(core_of(run word s))) /\
 length(snd(recorded_run word(s,[]))) <= 16.
Proof.
 intros word s [Hfacts [Hchan Hcert]].
 assert(Hback:channel_backed s).
 { intros f E; rewrite Hchan in E; discriminate. }
 assert(Hincl:incl(snd(recorded_run word(s,[])))(facts(core_of(run word s)))).
 { apply records_supported_by_native_facts; auto. intros f H; contradiction. }
 assert(Hnd:NoDup(snd(recorded_run word(s,[])))).
 { apply record_remains_a_set; constructor. }
 assert(Hlen:length(snd(recorded_run word(s,[])))<=length(facts(core_of(run word s)))).
 { apply NoDup_incl_length; assumption. }
 assert(Hcap:length(facts(core_of(run word s)))<=fact_cap).
 { apply native_table_cap_run; rewrite Hfacts; simpl; unfold fact_cap; lia. }
 unfold fact_cap in Hcap; repeat split; auto; lia.
Qed.
