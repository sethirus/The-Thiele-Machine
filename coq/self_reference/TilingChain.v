(** TilingChain: trust certificates composed along an arbitrary chain.

   InductiveTrust proves a single constructive expansion step. This file shows
   that the same story composes along an arbitrary finite chain. Expansions
   compose, their insights add exactly, and the source safety predicate keeps
   lifting through the whole chain.

   The result is a concrete model of recursive self-improvement without a free
   lunch theorem hiding underneath it. Every link still pays its μ-cost, and
   the endpoint certificate is just the composed witness.
 *)

From Coq Require Import Arith List Lia.
Import ListNotations.

(** Foundation imports for connectivity. *)
From Kernel Require Import VMState VMStep MuCostModel.

Require Import InductiveTrust.

(* *)
(** ** 1. Composition of Expansions *)

Definition compose_embed
    {A B C : StateSpace}
    (eAB : Expansion A B)
    (eBC : Expansion B C) : nat -> nat :=
  fun x => eBC.(embed B C) (eAB.(embed A B) x).

Lemma compose_embed_lt :
  forall {A B C : StateSpace} (eAB : Expansion A B) (eBC : Expansion B C),
    forall x, x < A.(ss_size) ->
    compose_embed eAB eBC x < C.(ss_size).
Proof.
  intros A B C eAB eBC x Hx.
  unfold compose_embed.
  apply (eBC.(embed_lt B C)).
  apply (eAB.(embed_lt A B)).
  exact Hx.
Qed.

Lemma compose_embed_inj :
  forall {A B C : StateSpace} (eAB : Expansion A B) (eBC : Expansion B C),
    forall x y,
      x < A.(ss_size) -> y < A.(ss_size) ->
      compose_embed eAB eBC x = compose_embed eAB eBC y ->
      x = y.
Proof.
  intros A B C eAB eBC x y Hx Hy Heq.
  apply (eAB.(embed_inj A B) x y Hx Hy).
  apply (eBC.(embed_inj B C)
    (eAB.(embed A B) x) (eAB.(embed A B) y)
    (eAB.(embed_lt A B) x Hx)
    (eAB.(embed_lt A B) y Hy)).
  exact Heq.
Qed.

Lemma compose_size_strict :
  forall {A B C : StateSpace} (eAB : Expansion A B) (eBC : Expansion B C),
    A.(ss_size) < C.(ss_size).
Proof.
  intros A B C eAB eBC.
  exact (Nat.lt_trans _ _ _
    (eAB.(size_strict A B))
    (eBC.(size_strict B C))).
Qed.

(** [compose_expansion]: sequential composition of two Expansions.
    The result is an Expansion A ↪ C with insight = insight(A↪B) + insight(B↪C). *)
Definition compose_expansion
    {A B C : StateSpace}
    (eAB : Expansion A B)
    (eBC : Expansion B C) : Expansion A C :=
  {| embed       := compose_embed eAB eBC;
     embed_lt    := compose_embed_lt eAB eBC;
     embed_inj   := compose_embed_inj eAB eBC;
     size_strict := compose_size_strict eAB eBC |}.

(* *)
(** ** 2. Insight of the composed expansion *)

(** Insight is EXACTLY additive — no overhead, no synergy. *)
Lemma compose_insight_eq :
  forall {A B C : StateSpace} (eAB : Expansion A B) (eBC : Expansion B C),
    expansion_insight eAB + expansion_insight eBC =
    expansion_insight (compose_expansion eAB eBC).
Proof.
  intros A B C eAB eBC.
  unfold expansion_insight, compose_expansion; simpl.
  pose proof (eAB.(size_strict A B)).
  pose proof (eBC.(size_strict B C)).
  lia.
Qed.

(* *)
(** ** 3. TilingChain: n-step trust chains *)

(** A [TilingChain Src Tgt] is either:
    - A single TrustCertificate Src ↪ Tgt, or
    - A chain Src ↪ Mid followed by a TrustCertificate Mid ↪ Tgt. *)
Inductive TilingChain : StateSpace -> StateSpace -> Type :=
| TilingBase : forall (A B : StateSpace),
    TrustCertificate A B ->
    TilingChain A B
| TilingStep : forall (A B C : StateSpace),
    TilingChain A B ->
    TrustCertificate B C ->
    TilingChain A C.

(* *)
(** ** 4. Global Expansion from a TilingChain *)

(** Every TilingChain Src Tgt yields an Expansion Src ↪ Tgt
    by composing the individual steps. *)
Fixpoint chain_expansion {Src Tgt : StateSpace} (ch : TilingChain Src Tgt)
    : Expansion Src Tgt :=
  match ch with
  | TilingBase A B tc       => tc.(tc_expansion A B)
  | TilingStep A B C ch' tc =>
      compose_expansion (chain_expansion ch') (tc.(tc_expansion B C))
  end.

(* *)
(** ** 5. Total insight along a TilingChain *)

(** The total insight is the sum of individual insights along the chain. *)
Fixpoint chain_total_insight {Src Tgt : StateSpace} (ch : TilingChain Src Tgt)
    : nat :=
  match ch with
  | TilingBase A B tc       => expansion_insight (tc.(tc_expansion A B))
  | TilingStep A B C ch' tc =>
      chain_total_insight ch' + expansion_insight (tc.(tc_expansion B C))
  end.

(** THE ADDITIVE total insight = insight of the composed expansion.
    No information is lost or created by the chain structure. *)
Theorem chain_insight_additive :
  forall {Src Tgt : StateSpace} (ch : TilingChain Src Tgt),
    chain_total_insight ch = expansion_insight (chain_expansion ch).
Proof.
  intros Src Tgt ch.
  induction ch as [A B tc | A B C ch' IH tc].
  - reflexivity.
  - simpl. rewrite IH. apply compose_insight_eq.
Qed.

(* *)
(** ** 6. Safety lifts through any TilingChain *)

(** The composed embedding faithfully carries Src's safe states into Tgt. *)
Theorem chain_safety_sound :
  forall {Src Tgt : StateSpace} (ch : TilingChain Src Tgt),
  forall s, s < Src.(ss_size) -> Src.(ss_safe) s ->
    (lift_safety Src (chain_expansion ch).(embed Src Tgt) Tgt.(ss_size)).(ss_safe)
      ((chain_expansion ch).(embed Src Tgt) s).
Proof.
  intros Src Tgt ch s Hs Hsafe.
  apply safety_functor_sound.
  - exact (chain_expansion ch).(size_strict Src Tgt).
  - exact (chain_expansion ch).(embed_lt Src Tgt).
  - exact Hs.
  - exact Hsafe.
Qed.

(* *)
(** ** 7. Terminal space is strictly larger *)

Theorem chain_strictly_grows :
  forall {Src Tgt : StateSpace} (ch : TilingChain Src Tgt),
    Src.(ss_size) < Tgt.(ss_size).
Proof.
  intros Src Tgt ch.
  exact (chain_expansion ch).(size_strict Src Tgt).
Qed.

(* *)
(** ** 8. Scale invariance: safety holds at every depth *)

(** THE SCALE INVARIANCE No matter how long the chain Src ↪ A₁ ↪ … ↪ Tgt, Src's originally
    certified states remain faithfully embedded in Tgt.
    Safety is NEVER weakened by recursive self-improvement. *)
Theorem scale_invariance :
  forall {Src Tgt : StateSpace} (ch : TilingChain Src Tgt),
  forall s, s < Src.(ss_size) -> Src.(ss_safe) s ->
    (lift_safety Src (chain_expansion ch).(embed Src Tgt) Tgt.(ss_size)).(ss_safe)
      ((chain_expansion ch).(embed Src Tgt) s).
Proof.
  intros Src Tgt ch s Hs Hsafe.
  exact (chain_safety_sound ch s Hs Hsafe).
Qed.

(** Every chain carries a constructive TrustCertificate at the endpoints. *)
Theorem chain_trust_certificate :
  forall {Src Tgt : StateSpace} (ch : TilingChain Src Tgt) (cSrc : VerifyCost Src),
    TrustCertificate Src Tgt.
Proof.
  intros Src Tgt ch cSrc.
  exact (mk_trust_certificate Src Tgt (chain_expansion ch) cSrc).
Qed.

(* *)
(** ** 9. No free trust *)

(** Every link costs positive μ.  The tiling is never a free lunch. *)
Theorem chain_no_free_trust :
  forall {Src Tgt : StateSpace} (ch : TilingChain Src Tgt),
    0 < chain_total_insight ch.
Proof.
  intros Src Tgt ch.
  induction ch as [A B tc | A B C ch' IH tc].
  - simpl. exact (tc.(tc_insight_pos A B)).
  - simpl. pose proof (tc.(tc_insight_pos B C)). lia.
Qed.

Corollary chain_insight_positive :
  forall {Src Tgt : StateSpace} (ch : TilingChain Src Tgt),
    0 < expansion_insight (chain_expansion ch).
Proof.
  intros Src Tgt ch.
  rewrite <- chain_insight_additive.
  exact (chain_no_free_trust ch).
Qed.
