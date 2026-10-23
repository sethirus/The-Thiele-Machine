From Coq Require Import List Bool Arith Lia.
From Minimal Require Import EarnedCore CertifiedHistory.
Import ListNotations.

Definition ge_fact(j:nat):fact:=mkfact(PGe j) CA 0.
Definition shape(fs:list fact)(pcn:nat)(ch:option fact)(meter:nat)(flag:bool):state:=
 mkst(mkcore 16 0 0 0 pcn fs ch false) meter flag.
Definition block(j:nat)(publish:bool):list instr:=
 [COMMIT(PGe j)CA; if publish then CERTIFY else COMMIT(PGe j)CA].

Lemma recorded_run_app : forall xs ys s,
 recorded_run(xs++ys)s=recorded_run ys(recorded_run xs s).
Proof. induction xs; intros; simpl; auto. Qed.

Lemma block_effect : forall j pick fs pcn ch meter flag rs,
 In(ge_fact j)fs ->
 recorded_run(block j pick)(shape fs pcn ch meter flag,rs)=
 (shape fs (pcn+2)(Some(ge_fact j))(meter+2)(flag||pick),
  if pick then insert_fact(ge_fact j)rs else rs).
Proof.
 intros j pick fs pcn ch meter flag rs Hin.
 assert(E:existsb(fact_eqb(ge_fact j))fs=true).
 { apply existsb_exists; exists(ge_fact j); split; auto.
   apply fact_eqb_eq; reflexivity. }
 unfold ge_fact in E.
 destruct pick; unfold block,shape,recorded_run,recorded_step,update_record,emit,
 exec,cexec,commit_ok,certify_ok,fires,claim,ver,commit_to,goto,cost;
 cbn -[existsb fact_eqb insert_fact];
 rewrite E; cbn -[existsb fact_eqb insert_fact]; try rewrite E;
 rewrite ?orb_false_r,?orb_true_r;
 replace (S(S pcn)) with (pcn+2) by lia;
 replace (meter+1+1) with (meter+2) by lia; reflexivity.
Qed.

Lemma indexed_mask_member : forall bits start n,n<length bits ->
 (In(start+n,true)(combine(seq start(length bits))bits) <-> nth n bits false=true).
Proof.
 induction bits as [|b bits IH]; intros start n Hn; [simpl in Hn; lia|].
 destruct n as [|n].
 - cbn [length seq combine nth]. rewrite Nat.add_0_r. split.
   + intros [E|Hin]; [inversion E; reflexivity|].
     apply in_combine_l in Hin; apply in_seq in Hin; lia.
   + intro E; subst b; left; reflexivity.
 - cbn [length seq combine nth].
   replace(start+S n) with(S start+n) by lia.
   rewrite <-(IH (S start) n) by (simpl in Hn; lia). split; [|intro H; right; exact H].
   intros [E|Hin]; [inversion E; lia|exact Hin].
Qed.

Fixpoint program(qs:list(nat*bool)):list instr:=
 match qs with []=>[]|(j,b)::rest=>block j b++program rest end.
Fixpoint last_channel(qs:list(nat*bool))(ch:option fact):option fact:=
 match qs with []=>ch|(j,_)::rest=>last_channel rest(Some(ge_fact j)) end.
Fixpoint any_selected(qs:list(nat*bool)):bool:=
 match qs with []=>false|(_,b)::rest=>b||any_selected rest end.
Fixpoint archive(qs:list(nat*bool))(rs:list fact):list fact:=
 match qs with []=>rs|(j,b)::rest=>archive rest(if b then insert_fact(ge_fact j)rs else rs)end.

Theorem program_effect : forall qs fs pcn ch meter flag rs,
 (forall j b,In(j,b)qs -> In(ge_fact j)fs) ->
 recorded_run(program qs)(shape fs pcn ch meter flag,rs)=
 (shape fs (pcn+2*length qs)(last_channel qs ch)
    (meter+2*length qs)(flag||any_selected qs), archive qs rs).
Proof.
 induction qs as [|[j b] qs IH]; intros fs pcn ch meter flag rs H.
 - simpl; rewrite !Nat.add_0_r,orb_false_r; reflexivity.
 - cbn [program]. rewrite recorded_run_app,block_effect by (apply H with b; simpl; auto).
   rewrite IH by (intros; apply H with b0; simpl; auto).
   cbn [length last_channel any_selected archive].
   rewrite orb_assoc. replace(pcn+2+2*length qs) with(pcn+2*S(length qs)) by lia.
   replace(meter+2+2*length qs) with(meter+2*S(length qs)) by lia. reflexivity.
Qed.

Lemma archive_membership : forall qs rs f,
 In f(archive qs rs) <-> In f rs \/ exists j,In(j,true)qs /\ f=ge_fact j.
Proof.
 induction qs as [|[j b] qs IH]; intros; simpl.
 - split; [auto|intros [H|[x [H _]]]; auto; contradiction].
 - rewrite IH; destruct b.
   + rewrite insert_membership; split.
     * intros [[->|H]|[x [H E]]]; [right; exists j; auto|auto|right; exists x; auto].
     * intros [H|[x [[E|H] Ef]]]; [auto|inversion E; subst; auto|right; exists x; auto].
   + split.
     * intros [H|[x [H E]]]; [auto|right; exists x; auto].
     * intros [H|[x [[E|H] Ef]]]; [auto|discriminate|right; exists x; auto].
Qed.

Definition checks:list instr:=map(fun j=>CHECK(PGe j)CA)(seq 0 16).
Definition table:list fact:=rev(map ge_fact(seq 0 16)).

Theorem prepared_table : recorded_run checks(start 16 0,[])=
 (shape table 17 None 16 false,[]).
Proof. vm_compute; reflexivity. Qed.

Lemma table_contains : forall j,j<16 -> In(ge_fact j)table.
Proof.
 intros j Hj; unfold table; rewrite <-in_rev; apply in_map; apply in_seq; lia.
Qed.

Definition selected_program(bits:list bool):list instr:=
 checks++program(combine(seq 0 16)bits).
Definition selected_archive(bits:list bool):list fact:=
 archive(combine(seq 0 16)bits)[].

Theorem every_mask_native_effect : forall bits,length bits=16 ->
 recorded_run(selected_program bits)(start 16 0,[])=
 (shape table 49 (Some(ge_fact 15)) 48 (existsb(fun b=>b)bits),selected_archive bits).
Proof.
 intros bits Hlen; unfold selected_program; rewrite recorded_run_app,prepared_table.
 rewrite program_effect.
 - unfold selected_archive.
   assert(Hlength:length(combine(seq 0 16)bits)=16).
   { rewrite combine_length,seq_length,Hlen; reflexivity. }
   rewrite Hlength.
   assert(Hlast:last_channel(combine(seq 0 16)bits)None=Some(ge_fact 15)).
   { do 16 (destruct bits as [|? bits]; [simpl in Hlen; discriminate|]).
     destruct bits; [reflexivity|simpl in Hlen; discriminate]. }
   assert(Hany:any_selected(combine(seq 0 16)bits)=existsb(fun b=>b)bits).
   { do 16 (destruct bits as [|? bits]; [simpl in Hlen; discriminate|]).
     destruct bits; [reflexivity|simpl in Hlen; discriminate]. }
   rewrite Hlast,Hany; reflexivity.
 - intros j b Hin; apply in_combine_l in Hin. apply in_seq in Hin.
   apply table_contains; lia.
Qed.

Theorem exact_selected_membership : forall bits j,length bits=16 -> j<16 ->
 (In(ge_fact j)(selected_archive bits) <-> nth j bits false=true).
Proof.
 intros bits j Hlen Hj; unfold selected_archive; rewrite archive_membership.
 rewrite <-Hlen in Hj.
 pose proof(indexed_mask_member bits 0 j Hj) as H; simpl in H.
 rewrite Hlen in H. rewrite <-H. split.
 - intros [E|[x [Hin He]]]; [contradiction|].
   unfold ge_fact in He; inversion He; subst; assumption.
 - intro Hin; right; exists j; auto.
Qed.

Theorem distinct_masks_distinct_records : forall xs ys,
 length xs=16 -> length ys=16 ->
 (forall f,In f(selected_archive xs)<->In f(selected_archive ys)) -> xs=ys.
Proof.
 intros xs ys Hx Hy Hmem; apply nth_ext with (d:=false)(d':=false); [lia|].
 intros n Hn; rewrite Hx in Hn.
 pose proof(exact_selected_membership xs n Hx Hn) as A.
 pose proof(exact_selected_membership ys n Hy Hn) as B.
 specialize(Hmem(ge_fact n)).
 destruct(nth n xs false), (nth n ys false); intuition discriminate.
Qed.

Theorem nonempty_masks_identical_native_state : forall xs ys,
 length xs=16 -> length ys=16 ->
 existsb(fun b=>b)xs=true -> existsb(fun b=>b)ys=true ->
 run(selected_program xs)(start 16 0)=run(selected_program ys)(start 16 0).
Proof.
 intros xs ys Hx Hy Ex Ey.
 rewrite <-(native_projection (selected_program xs)(start 16 0)[]),
         <-(native_projection (selected_program ys)(start 16 0)[]).
 rewrite !every_mask_native_effect by assumption.
 rewrite Ex,Ey; reflexivity.
Qed.

Theorem archive_cardinality_bound_attained :
 length(snd(recorded_run(selected_program(repeat true 16))(start 16 0,[])))=16.
Proof. vm_compute; reflexivity. Qed.
