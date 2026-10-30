(* SCOPE NOTE: standalone proof scope. the verifier corollary is stated over an
   abstract explanation relation, not over the record system itself. *)
(** VerifierSmall.v: the verifier corollary, stated abstractly.

    The setting. A verifier reads a transcript and says accept or reject.
    An explanation relation says which states can stand behind which
    transcripts. A verifier is sound for a claim when every state behind an
    accepted transcript satisfies the claim, and complete when every
    transcript behind which a state satisfying the claim can stand is
    accepted.

    What is proved (every result closed under the global context):

      1. The collision, on any states and transcripts. If one transcript is
         explained by a state that satisfies the claim and by one that does
         not, no verifier is both sound and complete
         [ver_collision_blocks]; a sound verifier must reject that
         transcript [ver_sound_rejects]. A verifier on a richer transcript
         that only looks at a projection cannot be sound and complete when
         two transcripts with the same projection are explained by such a
         pair [ver_no_factor].
      2. Three escapes, on any states. A full-state transcript (the
         verifier reads the last state) [ver_full_state_escape]; a
         commitment bit under the binding-and-honesty contract
         [ver_commitment_escape], with the honest relation meeting the
         contract [ver_honest_meets_contract] and an unchecked bit
         breaking it whenever the bare relation has a collision
         [ver_unchecked_breaks_contract]; a response read off the state
         [ver_response_escape].

    What is not proved. The collision is a hypothesis of ver_no_factor, not
    a conclusion: a transcript type that separates the two states does not
    meet it, and the theorem says nothing there. Nothing shows the three
    escapes are the only ones. The commitment contract is assumed; it is
    what a signature and a hardness assumption would have to supply, and no
    hardness is proved. The response relation only allows a truthful
    response, so it buys no resistance to a cheating prover.

    Dependencies: the Coq standard library. No axioms, no Admitted. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.

(* ================================================================= *)
(* 1. The collision, on any states and transcripts.                   *)
(* ================================================================= *)

Section Collision.

Context {St Tr : Type}.
Variable claim : St -> Prop.
Variable explains : St -> Tr -> Prop.

Definition ver_sound (V : Tr -> bool) : Prop :=
  forall t, V t = true -> forall s, explains s t -> claim s.

Definition ver_complete (V : Tr -> bool) : Prop :=
  forall s t, claim s -> explains s t -> V t = true.

Theorem ver_collision_blocks : forall t A B,
  explains A t -> explains B t -> claim A -> ~ claim B ->
  ~ exists V, ver_sound V /\ ver_complete V.
Proof.
  intros t A B HA HB HcA HcB [V [Hs Hc]].
  apply HcB. apply (Hs t (Hc A t HcA HA) B HB).
Qed.

Theorem ver_sound_rejects : forall t B,
  explains B t -> ~ claim B -> forall V, ver_sound V -> V t = false.
Proof.
  intros t B HB HcB V Hs. destruct (V t) eqn:E; [| reflexivity].
  exfalso. apply HcB, (Hs t E B HB).
Qed.

End Collision.

(* A verifier factors through a projection when transcripts with the same
   projection always get the same answer. *)
Definition ver_factors {T P : Type} (proj : T -> P) (V : T -> bool) : Prop :=
  forall t1 t2, proj t1 = proj t2 -> V t1 = V t2.

Theorem ver_no_factor :
  forall (St T P : Type) (claim : St -> Prop) (explains : St -> T -> Prop)
         (proj : T -> P) (tA tB : T) (A B : St) (V : T -> bool),
    proj tA = proj tB ->
    explains A tA -> explains B tB ->
    claim A -> ~ claim B ->
    ver_sound claim explains V -> ver_complete claim explains V ->
    ~ ver_factors proj V.
Proof.
  intros St T P claim explains proj tA tB A B V Hp HA HB HcA HcB Hs Hc Hf.
  assert (HVA : V tA = true) by (apply (Hc A tA HcA HA)).
  rewrite (Hf tA tB Hp) in HVA.
  apply HcB, (Hs tB HVA B HB).
Qed.

(* ================================================================= *)
(* 2. Three escapes, on any states.                                   *)
(* ================================================================= *)

Section Escapes.

Context {St : Type}.
Variable claim_b : St -> bool.

(* The claim, decided by claim_b. *)
Definition ver_claim (s : St) : Prop := claim_b s = true.

(* Full-state transcript: a list of states; the state behind it is its
   last entry. The verifier reads that entry. *)
Fixpoint ver_last (t : list St) : option St :=
  match t with
  | [] => None
  | [x] => Some x
  | _ :: rest => ver_last rest
  end.

Definition ver_full_explains (s : St) (t : list St) : Prop := ver_last t = Some s.

Definition ver_full_verifier (t : list St) : bool :=
  match ver_last t with Some s => claim_b s | None => false end.

Theorem ver_full_state_escape :
  ver_sound ver_claim ver_full_explains ver_full_verifier /\
  ver_complete ver_claim ver_full_explains ver_full_verifier.
Proof.
  split.
  - intros t Hv s He. unfold ver_full_verifier, ver_full_explains in *.
    rewrite He in Hv. exact Hv.
  - intros s t Hc He. unfold ver_full_verifier, ver_full_explains in *.
    rewrite He. exact Hc.
Qed.

(* Commitment transcript: a bare transcript and a bit. The contract on an
   explanation relation: binding (a set bit means the claim holds of every
   state behind it) and honesty (a state satisfying the claim only stands
   behind a set bit). *)
Definition ver_contract {B : Type} (EC : St -> B * bool -> Prop) : Prop :=
  (forall s t b, EC s (t, b) -> b = true -> ver_claim s) /\
  (forall s t b, EC s (t, b) -> ver_claim s -> b = true).

Definition ver_bit_verifier {B : Type} (t : B * bool) : bool := snd t.

Theorem ver_commitment_escape : forall {B : Type} (EC : St -> B * bool -> Prop),
  ver_contract EC ->
  ver_sound ver_claim EC ver_bit_verifier /\ ver_complete ver_claim EC ver_bit_verifier.
Proof.
  intros B EC [Hbind Hhon]. split.
  - intros [t b] Hv s He. exact (Hbind s t b He Hv).
  - intros s [t b] Hc He. exact (Hhon s t b He Hc).
Qed.

(* The honest relation: the bare relation, with the bit equal to the
   claim. *)
Definition ver_honest {B : Type} (E0 : St -> B -> Prop) (s : St) (tb : B * bool) : Prop :=
  E0 s (fst tb) /\ snd tb = claim_b s.

Theorem ver_honest_meets_contract : forall {B : Type} (E0 : St -> B -> Prop),
  ver_contract (ver_honest E0).
Proof.
  intros B E0. split.
  - intros s t b [_ Hb] H. unfold ver_claim. simpl in Hb. congruence.
  - intros s t b [_ Hb] H. unfold ver_claim in H. simpl in Hb. congruence.
Qed.

(* The unchecked relation: the bare relation, any bit. *)
Definition ver_unchecked {B : Type} (E0 : St -> B -> Prop) (s : St) (tb : B * bool) : Prop :=
  E0 s (fst tb).

Theorem ver_unchecked_breaks_contract : forall {B : Type} (E0 : St -> B -> Prop) t S,
  E0 S t -> ~ ver_claim S -> ~ ver_contract (ver_unchecked E0).
Proof.
  intros B E0 t S HS HcS [Hbind _]. apply HcS. apply (Hbind S t true HS eq_refl).
Qed.

(* Response transcript: a bare transcript and a response. The state behind
   it is one whose response it is; the verifier accepts by a test on the
   response that is exact for the claim. *)
Theorem ver_response_escape :
  forall {B R : Type} (resp : St -> R) (acc : R -> bool),
    (forall s, acc (resp s) = claim_b s) ->
    ver_sound ver_claim (fun s (tr : B * R) => snd tr = resp s) (fun tr => acc (snd tr)) /\
    ver_complete ver_claim (fun s (tr : B * R) => snd tr = resp s) (fun tr => acc (snd tr)).
Proof.
  intros B R resp acc Hacc. split.
  - intros [t r] Hv s He. simpl in *. subst r. unfold ver_claim. rewrite <- Hacc. exact Hv.
  - intros s [t r] Hc He. simpl in *. subst r. rewrite Hacc. exact Hc.
Qed.

End Escapes.

Print Assumptions ver_collision_blocks.
Print Assumptions ver_sound_rejects.
Print Assumptions ver_no_factor.
Print Assumptions ver_full_state_escape.
Print Assumptions ver_commitment_escape.
Print Assumptions ver_honest_meets_contract.
Print Assumptions ver_unchecked_breaks_contract.
Print Assumptions ver_response_escape.
