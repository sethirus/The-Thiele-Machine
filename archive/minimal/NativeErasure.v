From Coq Require Import List Bool Arith Lia.
From Minimal Require Import EarnedCore.
Import ListNotations.

Definition inspect_then_erase:list instr:=
 [CHECK(PGe 1)CA; COMMIT(PGe 1)CA; CERTIFY; DEC CA 5].
Definition counters(s:state):nat*nat:=(ca(core_of s),cb(core_of s)).

Theorem native_rebar_witness :
 counters(run inspect_then_erase(start 1 0))=(0,0) /\
 counters(run inspect_then_erase(start 0 0))=(0,0) /\
 cert(run inspect_then_erase(start 1 0))=true /\
 cert(run inspect_then_erase(start 0 0))=false /\
 err(core_of(run inspect_then_erase(start 1 0)))=false /\
 err(core_of(run inspect_then_erase(start 0 0)))=true.
Proof. repeat split; reflexivity. Qed.

Theorem native_exact_for_boolean_candidates : forall candidate:bool,
 let x:=if candidate then 1 else 0 in
 counters(run inspect_then_erase(start x 0))=(0,0) /\
 cert(run inspect_then_erase(start x 0))=candidate /\
 mu(run inspect_then_erase(start x 0))=3.
Proof. intros []; repeat split; reflexivity. Qed.

Theorem native_post_counter_checker_impossible :
 ~exists verify:(nat*nat)->bool,forall candidate:bool,
 let x:=if candidate then 1 else 0 in
 verify(counters(run inspect_then_erase(start x 0)))=candidate.
Proof. intros [v H]; pose proof(H true) as A; pose proof(H false) as B;
 change(v(0,0)=true) in A; change(v(0,0)=false) in B; congruence. Qed.

Theorem free_native_dec_can_erase_the_counter_distinction :
 cost(DEC CA 5)=0 /\
 counters(exec(start 1 0)(DEC CA 5))=counters(exec(start 0 0)(DEC CA 5)).
Proof. split; reflexivity. Qed.

Theorem trapped_invalid_execution_does_not_perform_later_erasure :
 pc(core_of(run inspect_then_erase(start 0 0)))=1 /\
 va(core_of(run inspect_then_erase(start 0 0)))=0 /\
 pc(core_of(run inspect_then_erase(start 1 0)))=5 /\
 va(core_of(run inspect_then_erase(start 1 0)))=1.
Proof. repeat split; reflexivity. Qed.

Theorem native_cert_does_not_mean_all_later_checks_passed :
 let s:=run(inspect_then_erase++[CHECK(PGe 1)CA])(start 1 0) in
 cert s=true /\ err(core_of s)=true.
Proof. split; reflexivity. Qed.

Theorem two_native_good_states_need_not_collapse_at_every_write :
 counters(exec(start 0 0)(INC CA))<>(counters(exec(start 1 0)(INC CA))).
Proof. discriminate. Qed.
