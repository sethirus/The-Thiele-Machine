(** VerifierSmall.v: the verifier corollary, stated abstractly and proved
    for every Thiele-complete machine, the small machine included.

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
      3. Every Thiele-complete machine has the collision. The bare
         transcript is the clean start's two counters and the end's base
         window; a state explains it when some run from that start ends
         there showing that window. No verifier on bare transcripts is
         sound and complete for "the record is up"
         [ver_complete_no_record_verifier], and for some clean start none
         is for "the ledger rose by at least 3"
         [ver_complete_no_ledger_verifier]. No sound and complete verifier
         on any richer transcript type factors through the bare part when
         the collision survives into it [ver_complete_no_factor]. The three
         escapes work for the record claim [ver_complete_escapes]. All of
         it in one statement [ver_corollary].
      4. The small machine. The pair of EarnedCore.v (CHECK, COMMIT,
         CERTIFY versus three idle decrements, both from (0, 0)) ends with
         the same window, ledger 3 against 0. No verifier on the bare window
         is sound and complete for "the ledger reads 3"
         [ver_small_no_ledger_verifier]; the whole corollary holds for the
         small machine through its own interface [ver_small_corollary].

    What is not proved. The collision is a hypothesis of ver_no_factor, not
    a conclusion: a transcript type that separates the two states does not
    meet it, and the theorem says nothing there. Nothing shows the three
    escapes are the only ones. The commitment contract is assumed; it is
    what a signature and a hardness assumption would have to supply, and no
    hardness is proved. The response relation only allows a truthful
    response, so it buys no resistance to a cheating prover.

    Dependencies: Coq standard library, ThieleComplete.v,
    ThieleCompleteWindow.v, EntitlementSmall.v (for the small machine's
    interface lemma) and the files they require. No axioms, no Admitted.        *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete.
Require Import Minimal.ThieleCompleteWindow.
Require Import Minimal.EntitlementSmall.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.

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

(* ================================================================= *)
(* 3. Every Thiele-complete machine has the collision.                *)
(* ================================================================= *)

(* The bare transcript: the clean start's two counters and the end's base
   window. *)
Definition ver_bare : Type := (nat * nat * cm_conf)%type.

Definition ver_bare_explains {M : machine} (I : thiele_interface M)
    (s : m_state M) (t : ver_bare) : Prop :=
  let '(a, b, w) := t in
  exists tr, s = run M tr (load I a b) /\ base_window I s = w.

Definition ver_record {M : machine} (s : m_state M) : Prop := m_record M s = true.

Theorem ver_complete_no_record_verifier : forall (M : machine) (I : thiele_interface M),
  thiele_complete_with I ->
  ~ exists V : ver_bare -> bool,
      ver_sound ver_record (ver_bare_explains I) V /\
      ver_complete ver_record (ver_bare_explains I) V.
Proof.
  intros M I HC.
  destruct (complete_hides_record M I HC) as [a [b [tr1 [tr2 [_ [Hw [H1 H2]]]]]]].
  apply (ver_collision_blocks ver_record (ver_bare_explains I)
           (a, b, base_window I (run M tr1 (load I a b)))
           (run M tr1 (load I a b)) (run M tr2 (load I a b))).
  - exists tr1. split; reflexivity.
  - exists tr2. split; [reflexivity | symmetry; exact Hw].
  - exact H1.
  - unfold ver_record. rewrite H2. discriminate.
Qed.

Theorem ver_complete_no_ledger_verifier : forall (M : machine) (I : thiele_interface M),
  thiele_complete_with I ->
  exists a b, ti_clean I (load I a b) /\
  ~ exists V : ver_bare -> bool,
      ver_sound (fun s => ti_ledger I (load I a b) + 3 <= ti_ledger I s) (ver_bare_explains I) V /\
      ver_complete (fun s => ti_ledger I (load I a b) + 3 <= ti_ledger I s) (ver_bare_explains I) V.
Proof.
  intros M I HC.
  destruct (complete_two_runs M I HC)
    as [a [b [tr1 [tr2 [Hc [_ [Hw [_ [_ [Hl2 Hl1]]]]]]]]]].
  exists a, b. split; [exact Hc |].
  apply (ver_collision_blocks _ (ver_bare_explains I)
           (a, b, base_window I (run M tr1 (load I a b)))
           (run M tr1 (load I a b)) (run M tr2 (load I a b))).
  - exists tr1. split; reflexivity.
  - exists tr2. split; [reflexivity | symmetry; exact Hw].
  - exact Hl1.
  - rewrite Hl2. lia.
Qed.

(* The colliding pair, named: one clean start, two runs, the same window,
   the record up after one and down after the other. *)
Theorem ver_complete_pair : forall (M : machine) (I : thiele_interface M),
  thiele_complete_with I ->
  exists (t : ver_bare) (A B : m_state M),
    ver_bare_explains I A t /\ ver_bare_explains I B t /\ ver_record A /\ ~ ver_record B.
Proof.
  intros M I HC.
  destruct (complete_hides_record M I HC) as [a [b [tr1 [tr2 [_ [Hw [H1 H2]]]]]]].
  exists (a, b, base_window I (run M tr1 (load I a b))),
         (run M tr1 (load I a b)), (run M tr2 (load I a b)).
  split; [exists tr1; split; reflexivity |].
  split; [exists tr2; split; [reflexivity | symmetry; exact Hw] |].
  split; [exact H1 | unfold ver_record; rewrite H2; discriminate].
Qed.

(* A richer transcript that keeps the collision cannot be read through
   its bare part. *)
Theorem ver_complete_no_factor : forall (M : machine) (I : thiele_interface M),
  thiele_complete_with I ->
  exists A B : m_state M, ver_record A /\ ~ ver_record B /\
  forall (T : Type) (proj : T -> ver_bare) (explains : m_state M -> T -> Prop)
         (tA tB : T) (V : T -> bool),
    proj tA = proj tB -> explains A tA -> explains B tB ->
    ver_sound ver_record explains V -> ver_complete ver_record explains V ->
    ~ ver_factors proj V.
Proof.
  intros M I HC.
  destruct (ver_complete_pair M I HC) as [t [A [B [_ [_ [HA HB]]]]]].
  exists A, B. split; [exact HA |]. split; [exact HB |].
  intros T proj explains tA tB V Hp HeA HeB Hs Hc.
  exact (ver_no_factor (m_state M) T ver_bare ver_record explains proj tA tB A B V
           Hp HeA HeB HA HB Hs Hc).
Qed.

Lemma ver_record_claim : forall (M : machine) (s : m_state M),
  ver_record s <-> ver_claim (m_record M) s.
Proof. intros. reflexivity. Qed.

(* The three escapes, for the record claim, on any machine. *)
Theorem ver_complete_escapes : forall (M : machine) (I : thiele_interface M),
  (ver_sound ver_record ver_full_explains (ver_full_verifier (m_record M)) /\
   ver_complete ver_record ver_full_explains (ver_full_verifier (m_record M))) /\
  (ver_sound ver_record (ver_honest (m_record M) (ver_bare_explains I)) ver_bit_verifier /\
   ver_complete ver_record (ver_honest (m_record M) (ver_bare_explains I)) ver_bit_verifier) /\
  (ver_sound ver_record (fun s (tr : ver_bare * bool) => snd tr = m_record M s)
             (fun tr => snd tr) /\
   ver_complete ver_record (fun s (tr : ver_bare * bool) => snd tr = m_record M s)
             (fun tr => snd tr)).
Proof.
  intros M I. split; [| split].
  - exact (ver_full_state_escape (m_record M)).
  - apply ver_commitment_escape, ver_honest_meets_contract.
  - exact (@ver_response_escape _ (m_record M) ver_bare bool (m_record M) (fun b => b) (fun s => eq_refl)).
Qed.

(* The unchecked bit fails on every Thiele-complete machine. *)
Theorem ver_complete_unchecked_fails : forall (M : machine) (I : thiele_interface M),
  thiele_complete_with I ->
  ~ ver_contract (m_record M) (ver_unchecked (ver_bare_explains I)).
Proof.
  intros M I HC.
  destruct (ver_complete_pair M I HC) as [t [A [B [_ [HB [_ HnB]]]]]].
  exact (ver_unchecked_breaks_contract (m_record M) (ver_bare_explains I) t B HB HnB).
Qed.

(* THE VERIFIER COROLLARY, on every Thiele-complete machine. *)
Theorem ver_corollary : forall (M : machine) (I : thiele_interface M),
  thiele_complete_with I ->
  (~ exists V : ver_bare -> bool,
       ver_sound ver_record (ver_bare_explains I) V /\
       ver_complete ver_record (ver_bare_explains I) V) /\
  (exists A B : m_state M, ver_record A /\ ~ ver_record B /\
     forall (T : Type) (proj : T -> ver_bare) (explains : m_state M -> T -> Prop)
            (tA tB : T) (V : T -> bool),
       proj tA = proj tB -> explains A tA -> explains B tB ->
       ver_sound ver_record explains V -> ver_complete ver_record explains V ->
       ~ ver_factors proj V) /\
  (exists V : list (m_state M) -> bool,
     ver_sound ver_record ver_full_explains V /\ ver_complete ver_record ver_full_explains V) /\
  (exists V : ver_bare * bool -> bool,
     ver_sound ver_record (ver_honest (m_record M) (ver_bare_explains I)) V /\
     ver_complete ver_record (ver_honest (m_record M) (ver_bare_explains I)) V) /\
  ~ ver_contract (m_record M) (ver_unchecked (ver_bare_explains I)) /\
  (exists V : ver_bare * bool -> bool,
     ver_sound ver_record (fun s (tr : ver_bare * bool) => snd tr = m_record M s) V /\
     ver_complete ver_record (fun s (tr : ver_bare * bool) => snd tr = m_record M s) V).
Proof.
  intros M I HC.
  destruct (ver_complete_escapes M I) as [Hf [Hh Hr]].
  split; [apply ver_complete_no_record_verifier, HC |].
  split; [exact (ver_complete_no_factor M I HC) |].
  split; [eexists; exact Hf |].
  split; [eexists; exact Hh |].
  split; [apply ver_complete_unchecked_fails, HC |].
  eexists; exact Hr.
Qed.

(* ================================================================= *)
(* 4. The small machine.                                              *)
(* ================================================================= *)

(* The small machine's two runs from (0, 0): CHECK, COMMIT, CERTIFY, and
   three idle decrements. A state explains a window when some run from
   (0, 0) ends there showing it. *)
Definition ver_small_explains (s : E.state) (w : E.mconf) : Prop :=
  exists tr, s = E.run tr (E.start 0 0) /\ E.window (E.core_of s) = w.

Theorem ver_small_no_ledger_verifier :
  ~ exists V : E.mconf -> bool,
      ver_sound (fun s => E.mu s = 3) ver_small_explains V /\
      ver_complete (fun s => E.mu s = 3) ver_small_explains V.
Proof.
  destruct E.receipt_separation as [Hw _].
  apply (ver_collision_blocks (fun s => E.mu s = 3) ver_small_explains
           (E.window (E.core_of E.state_A)) E.state_A E.state_B).
  - exists E.earned_run. split; reflexivity.
  - exists E.idle_run. split; [reflexivity | symmetry; exact Hw].
  - reflexivity.
  - vm_compute. discriminate.
Qed.

(* The whole corollary for the small machine through its own interface
   (thiele_complete_with earned_interface is ent_earned_complete_with, in
   EntitlementSmall.v). *)
Definition ver_small_corollary := ver_corollary earned_machine earned_interface
                                    ent_earned_complete_with.

(* ================================================================= *)
(* Assumption audit. Every line must print                            *)
(* "Closed under the global context".                                 *)
(* ================================================================= *)

Print Assumptions ver_collision_blocks.
Print Assumptions ver_sound_rejects.
Print Assumptions ver_no_factor.
Print Assumptions ver_full_state_escape.
Print Assumptions ver_commitment_escape.
Print Assumptions ver_honest_meets_contract.
Print Assumptions ver_unchecked_breaks_contract.
Print Assumptions ver_response_escape.
Print Assumptions ver_complete_no_record_verifier.
Print Assumptions ver_complete_no_ledger_verifier.
Print Assumptions ver_complete_pair.
Print Assumptions ver_complete_no_factor.
Print Assumptions ver_complete_escapes.
Print Assumptions ver_complete_unchecked_fails.
Print Assumptions ver_corollary.
Print Assumptions ver_small_no_ledger_verifier.
Print Assumptions ver_small_corollary.
