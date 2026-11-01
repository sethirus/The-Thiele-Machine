(* SCOPE NOTE: standalone proof scope. the geometry limits are stated over bare
   state functions, not over the record system itself. *)
From Coq Require Import List Bool Arith Lia.
Import ListNotations.

(* Idempotence on the full state, not merely on the record, gives the exact
   collision. A ledger can make the full step non-idempotent. *)
Theorem idempotent_changed_state_collides {S R:Type}
 (F:S->S)(record:S->R)(s:S) :
 F(F s)=F s -> record(F s)<>record s ->
 s<>F s /\ F s=F(F s).
Proof. intros Hid Hchange; split; [intro He; rewrite <-He in Hchange; contradiction|symmetry; assumption]. Qed.

(* Protected record updates do not, by themselves, imply an autonomous working
   projection. This countermodel is excluded when Option 2 is imposed. *)
Definition steering(s:bool*bool):bool*bool:=(xorb(fst s)(snd s),snd s).
Theorem preserving_record_does_not_force_shadow_independence :
 snd(steering(false,false))=false /\ snd(steering(false,true))=true /\
 fst(false,false)=fst(false,true) /\
 fst(steering(false,false))<>fst(steering(false,true)).
Proof. repeat split; discriminate. Qed.

(* An ordinary variable with constrained updates can hold a protected record.
   No arbitrary raw write to that variable is included in this interface. *)
Definition ordinary_write(b:bool)(s:bool*bool):bool*bool:=(b,snd s).
Definition ordinary_establish(s:bool*bool):bool*bool:=(fst s,snd s || fst s).
Theorem ordinary_record_variable_is_protected :
 (forall b s,snd(ordinary_write b s)=snd s) /\
 snd(ordinary_establish(true,false))=true /\
 (forall s,snd s=true -> snd(ordinary_establish s)=true).
Proof. repeat split; try reflexivity. intros [b r] Hr; simpl in *; rewrite Hr; reflexivity. Qed.
Theorem including_protected_record_in_view_need_not_be_noninjective :
 (forall s t:bool*bool,(fun x=>x)s=(fun x=>x)t -> s=t) /\
 ordinary_establish(true,false)<>(true,false).
Proof. split; [auto|discriminate]. Qed.
