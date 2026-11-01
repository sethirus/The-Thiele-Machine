From Coq Require Import List Bool Arith Lia.
From Minimal Require Import EarnedCore CertifiedHistory Representation ArchiveBound MaskWitness.
Import ListNotations.

Definition chosen(bits:list bool):bool:=existsb(fun b=>b)bits.
Definition positive_profiles(n:nat):list(list bool):=filter chosen(profiles n).

Lemma filter_of_map {A B}(p:B->bool)(f:A->B):forall xs,
 filter p(map f xs)=map f(filter(fun x=>p(f x))xs).
Proof. induction xs; simpl; auto; destruct(p(f a)); simpl; congruence. Qed.

Lemma positive_profiles_count : forall n,length(positive_profiles n)+1=2^n.
Proof.
 induction n as [|n IH]; [reflexivity|].
 unfold positive_profiles in *; cbn [profiles]. rewrite filter_app,!filter_of_map,app_length,!map_length.
 assert(Ef:filter (fun x:list bool=>chosen(false::x))(profiles n)=filter chosen(profiles n)).
 { reflexivity. }
 assert(Et:filter(fun x:list bool=>chosen(true::x))(profiles n)=profiles n).
 { unfold chosen; generalize(profiles n); intro xs; induction xs; simpl in *; congruence. }
 rewrite Ef,Et,profiles_length. cbn [Nat.pow]. lia.
Qed.

Lemma positive_profile_properties : forall n bits,
 In bits(positive_profiles n) -> length bits=n /\ chosen bits=true.
Proof.
 intros n bits H; unfold positive_profiles in H; apply filter_In in H as [H E].
 apply profiles_complete in H; auto.
Qed.

Definition rich_endpoint(bits:list bool):recorded_state:=
 recorded_run(selected_program bits)(start 16 0,[]).
Definition common_endpoint:state:=shape table 49 (Some(ge_fact 15)) 48 true.

Theorem all_positive_profiles_share_native_endpoint : forall bits,
 In bits(positive_profiles 16) -> fst(rich_endpoint bits)=common_endpoint.
Proof.
 intros bits H; apply positive_profile_properties in H as [H E].
 unfold rich_endpoint; rewrite every_mask_native_effect by exact H.
 unfold chosen in E; rewrite E; reflexivity.
Qed.

Theorem rich_endpoints_are_distinct : forall xs ys,
 length xs=16 -> length ys=16 -> rich_endpoint xs=rich_endpoint ys -> xs=ys.
Proof.
 intros xs ys Hx Hy E; unfold rich_endpoint in E.
 rewrite !every_mask_native_effect in E by assumption.
 apply distinct_masks_distinct_records; auto. inversion E; subst; tauto.
Qed.

Theorem native_fibre_contains_65535_history_states :
 NoDup(map rich_endpoint(positive_profiles 16)) /\
 length(map rich_endpoint(positive_profiles 16))=65535 /\
 (forall s,In s(map rich_endpoint(positive_profiles 16)) -> fst s=common_endpoint).
Proof.
 split.
 - apply map_injective_nodup.
   + apply NoDup_filter; apply profiles_nodup.
   + intros xs ys Hx Hy E; apply positive_profile_properties in Hx,Hy.
     apply rich_endpoints_are_distinct; tauto.
 - split.
   + rewrite map_length. apply (proj1 (Nat.add_cancel_r _ _ 1)).
     transitivity(2^16); [apply positive_profiles_count|reflexivity].
   + intros s H; apply in_map_iff in H as [bits [<- H]].
     apply all_positive_profiles_share_native_endpoint; exact H.
Qed.

Definition memberb(f:fact)(rs:list fact):bool:=existsb(fact_eqb f)rs.
Lemma memberb_spec : forall f rs,memberb f rs=true <-> In f rs.
Proof.
 intros f rs; unfold memberb; rewrite existsb_exists; split.
 - intros [g [Hin He]]; apply fact_eqb_eq in He; subst; assumption.
 - intro H; exists f; split; auto; apply fact_eqb_eq; reflexivity.
Qed.
Definition archive_code(fs rs:list fact):list bool:=map(fun f=>memberb f rs)fs.

Lemma maps_equal_at {A B}(f g:A->B):forall xs,
 map f xs=map g xs -> forall x,In x xs -> f x=g x.
Proof.
 induction xs as [|a xs IH]; intros E x H; [contradiction|].
 simpl in E; inversion E. destruct H as [<-|H]; auto.
Qed.

Lemma archive_code_exact : forall fs rs ts,
 incl rs fs -> incl ts fs -> archive_code fs rs=archive_code fs ts ->
 forall f,In f rs <-> In f ts.
Proof.
 intros fs rs ts Hr Ht E f.
 assert(Hpoint:forall g,In g fs -> memberb g rs=memberb g ts).
 { apply maps_equal_at; exact E. }
 split; intro H.
 - apply memberb_spec. rewrite <-(Hpoint f (Hr f H)); apply memberb_spec; exact H.
 - apply memberb_spec. rewrite (Hpoint f (Ht f H)); apply memberb_spec; exact H.
Qed.

Theorem native_history_has_a_sixteen_bit_encoding : forall word s,
 clean_start s ->
 let finish:=run word s in
 let records:=snd(recorded_run word(s,[])) in
 length(archive_code(facts(core_of finish))records)<=16 /\
 (forall ts,incl ts(facts(core_of finish)) ->
   archive_code(facts(core_of finish))records=archive_code(facts(core_of finish))ts ->
   forall f,In f records <-> In f ts).
Proof.
 intros word s H; cbn zeta.
 destruct(clean_certified_archive_bound word s H) as [Hi [_ [_ Hcap]]].
 split.
 - unfold archive_code; rewrite map_length.
   apply native_table_cap_run; destruct H as [H _]; rewrite H; simpl; unfold fact_cap; lia.
 - intros ts Hts E; apply (archive_code_exact (facts(core_of(run word s)))); assumption.
Qed.

Definition padded_code(fs rs:list fact):list bool:=
 archive_code fs rs++repeat false(16-length fs).

Lemma code_nonempty : forall fs rs,incl rs fs ->
 chosen(archive_code fs rs)=coarse rs.
Proof.
 intros fs rs Hi; destruct rs as [|f rs].
 - clear Hi; unfold archive_code,memberb,chosen; induction fs; simpl; auto.
 - change(chosen(archive_code fs(f::rs))=true).
   unfold chosen; apply existsb_exists; exists true; split; [|reflexivity].
   unfold archive_code; apply in_map_iff; exists f; split.
   + apply memberb_spec; simpl; auto.
   + apply Hi; simpl; auto.
Qed.

Theorem clean_native_history_code : forall word s,clean_start s ->
 let fs:=facts(core_of(run word s)) in
 let rs:=snd(recorded_run word(s,[])) in
 length(padded_code fs rs)=16 /\ chosen(padded_code fs rs)=cert(run word s).
Proof.
 intros word s H; cbn zeta.
 destruct(clean_certified_archive_bound word s H) as [Hi [_ [_ _]]].
 assert(Hcap:length(facts(core_of(run word s)))<=16).
 { apply native_table_cap_run; destruct H as [H _]; rewrite H; simpl; unfold fact_cap; lia. }
 unfold padded_code; split.
 - rewrite app_length,repeat_length; unfold archive_code; rewrite map_length; lia.
 - unfold chosen at 1; rewrite existsb_app.
   assert(E:forall n,existsb(fun b:bool=>b)(repeat false n)=false).
   { induction n; simpl; auto. }
   rewrite E,orb_false_r. fold chosen.
   rewrite code_nonempty by exact Hi. apply clean_boolean_shadow; exact H.
Qed.

Theorem at_most_65535_nonempty_native_history_codes : forall s target codes,
 clean_start s -> cert target=true -> NoDup codes ->
 (forall code,In code codes -> exists word,
    run word s=target /\
    code=padded_code(facts(core_of target))(snd(recorded_run word(s,[])))) ->
 length codes<=65535.
Proof.
 intros s target codes Hclean Hcert Hnd Hreal.
 assert(Hi:incl codes(positive_profiles 16)).
 { intros code Hin; destruct(Hreal code Hin) as [word [He Ec]].
   pose proof(clean_native_history_code word s Hclean) as [Hl Hp].
   rewrite He in Hl,Hp. rewrite <-Ec in Hl,Hp.
   unfold positive_profiles; apply filter_In; split.
   - apply profiles_complete; exact Hl.
   - rewrite Hp; exact Hcert. }
 pose proof(NoDup_incl_length Hnd Hi) as Hlen.
 assert(E:length(positive_profiles 16)=65535).
 { apply(proj1(Nat.add_cancel_r _ _ 1)); transitivity(2^16);
   [apply positive_profiles_count|reflexivity]. }
 rewrite E in Hlen; exact Hlen.
Qed.
