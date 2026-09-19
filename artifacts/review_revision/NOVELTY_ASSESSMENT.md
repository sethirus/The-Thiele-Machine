# Novelty and mathematical payoff: initial comparison

This is a research note supporting targets N1–N3 in STATUS.md, not a novelty certificate or a completed literature review. The research specification is in NOVELTY_RESEARCH_REQUEST.md. Source inspection and the primary-source checks below were made on 2026-09-12. Existing interpreter and physical refinement obligations continue independently.

The question is whether a precise result contributes a new characterization, restriction, or useful transfer method. These are alternative routes. Correct Coq proofs, an executable interpreter, and working hardware establish their stated properties; their completion alone does not establish mathematical significance or predict recognition.

## Exact baseline: what the present initiality results determine

Two source theorems are especially relevant to a uniqueness claim.

`Kernel.ThieleInitiality.thiele_trace_fold_initial` quantifies over a `CertCostMachine` M and a starting state z. Its canonical map is

    F(t) = fold_left (ccm_step M) t z.

It proves F([])=z, F(t++[i])=step(F(t),i), and uniqueness among maps satisfying these two equations. The source of F is the free instruction-list type, not VM states modulo execution. The proof uses only the target state, step and basepoint. Certification and pricing fields do no work in this proof.

This statement has an immediate generic derivation: for arbitrary types I and S, z:S and step:S→I→S, reverse-list induction forces any such map g to equal fold_left step. The empty case is g([])=z; the extension case substitutes the induction hypothesis into g(t++[i])=step(g(t),i). Taking I=vm_instruction and S=ccm_state M gives exactly the theorem's conclusion. This is an explicit reduction of this particular claim to the generic list-fold property, not a reduction of the whole framework to existing work.

`Kernel.MuInitiality.mu_is_initial_monotone` fixes instruction_cost, initial ledger zero, and the exact equation M(vm_apply(s,i))=M(s)+instruction_cost(i). For every state reachable by a finite instruction fold from init_state, it concludes M(s)=vm_mu(s). Iterating the premise gives

    M(exec(s0,t)) = M(s0) + sum(map instruction_cost t).

The VM ledger satisfies the same equation and initial value. Substitution gives equality. Thus this theorem selects an accumulated measure after the price schedule is fixed; it does not derive the schedule or force a structural state object. Its local exact-update hypothesis is stronger than mere monotonicity or a positive event floor.

Assessment of these two statements: their abstract conclusions follow from generic fold/accumulation arguments. An independently motivated account of why the premises are necessary, or a further consequence using them, could still contribute. These two proofs alone do not establish whole-substrate uniqueness.

## Closest checked comparison for a characterization or transfer claim

Green, Karvounarakis and Tannen supply a useful concrete comparison. Proposition 3.4 relates the specified positive relational-algebra identities to commutative-semiring laws. Proposition 3.5 characterizes annotation maps commuting with those queries as semiring homomorphisms. Proposition 4.2 gives the polynomial evaluation universal property; Theorem 4.3 uses it to evaluate annotated queries through polynomial provenance. [Provenance Semirings, §§3–4](https://www.cs.ucdavis.edu/~green/papers/pods07.pdf).

The comparison does not identify Thiele states with K-relations: no such translation has been constructed. It identifies the missing obligation in a proposed comparable contribution. A Thiele characterization must state independently justified operations and equations, derive the claimed structure, and show what reusable analysis follows. Merely giving each system a natural-valued running charge does not supply the query algebra, a provenance representation, or the transfer theorem above. Conversely, a relational annotation theorem cannot be assumed to cover state mutation, traps, or evidence reuse without a translation preserving those operations.

## Checked comparison: operations and equations determine a state monad

Plotkin and Power's Theorem 1 identifies the monad induced by their global-state algebra as `(S ⊗ -)^S`. Its domain fixes finite locations L, countable values V, S=V^L, and a category with countable products and coproducts. The algebra uses lookup and update with specified equations. Theorem 2 treats their local-state algebra on a presheaf category, with additional block structure. [Notions of Computation Determine Monads, §§3–4](https://era.ed.ac.uk/bitstreams/1308e672-4651-4df2-ab48-426328db59b8/download).

The resulting comparison is specific: an operations-and-equations characterization of state already exists. The Thiele list-fold theorem does not supply an additional characterization merely by instantiating a state type. A further result would need independently justified structural operations, an exact relation to these algebras, and a consequence not supplied by that relation alone. No translation preserving Thiele graph observations, evidence reuse, and charging has been constructed here; neither equivalence nor separation from this account is established.

## A stronger existing candidate to examine next

`Kernel.HonestNoFI_TheoremsWithoutAssumptions.structural_entitlement_representation` combines strict predicate strengthening, structure addition, and a logarithmic ledger bound. This is a better candidate for inspecting interaction between structural and quantitative reasoning than the fold theorem alone.

Its actual domain is a bounded run_vm execution, feasible lists, an observation comparator, a receipt decoder, two observation functions, and a supplied decision tree. Premises include strict subset reduction with a distinguishing eliminated witness, initially inactive CSR certification, final Certified evidence, decision_tree_realized_by_trace, nonempty posterior, and PosteriorRepresentativeReduction. The conclusion includes

    log2_up(|prior|) - log2_up(|posterior|) <= final_mu - initial_mu

with natural subtraction and the source's feasible-size convention. The theorem uses separate distinguishing and representative observations. Its neighboring lemma shows that conflating them can make the witness requirements inconsistent.

The load-bearing definitions have now been inspected directly. In `NoFreeInsight.v`, Certified expands to an error-free final state, truth of the receipt predicate on the supplied decoder output, and final supra-certification. In `MuShannonBridge.v`, decision_tree_realized_by_trace is precisely `depth(tree) <= cert_setter_executions`; it does not extract or execute an observation tree. PosteriorRepresentativeReduction supplies an observation-preserving assignment into posterior fibers, the numerical prior-length bound by their summed lengths, and a leaf-count bound on each fiber. Feasible size is list length.

The numerical argument consequently has the shape

    |prior| <= sum(fiber lengths) <= leaves(tree) * |posterior|,
    log2_up(leaves(tree)) <= depth(tree)
      <= cert_setter_executions <= delta_mu.

The second line uses the binary-tree bound and the VM's proved setter-cost bound. Setter executions are not interchangeable with actual false-to-true flips. This identifies which bridge is supplied as a premise: the tree's depth is already constrained by the charged execution count. The conclusion is a valid composition of these contracts; it does not yet establish that arbitrary semantic narrowing forces that payment contract.

The next comparison must identify whether the *combined use* of these premises yields an independently useful consequence beyond this numerical composition. It must establish whether composing these contracts adds a useful theorem or is an application of already available arguments. In particular, a payment inequality supplied by a record is not a newly derived necessity of payment. A distinct contribution would require an explicit consequence beyond those inputs, with an applicable instance. This note does not yet judge that candidate novel or covered.

## Comparison queue and source-read scope

| Account | Relevance and source checked | Remaining comparison |
| --- | --- | --- |
| Algebraic effects/monads | Theorems 1–2 and their global/local-state definitions inspected; exact scope recorded above. | Compare independently specified operations/equations and their induced semantic structure before claiming an additional characterization. |
| Abstract state machines | The supplied Gurevich publication locator was opened, but its accessible page supplied no paper body. [Publication locator](https://www.microsoft.com/en-us/research/publication/sequential-abstract-state-machines-capture-sequential-algorithms/). | Obtain and inspect exact postulates and characterization theorem before asserting a translation or difference. |
| Abstract interpretation | The authors' page describes deriving information about concrete computations through abstract execution. [Cousot and Cousot, POPL 1977](https://www.di.ens.fr/~cousot/COUSOTpapers/POPL77.shtml). | Compare the chosen observations and transfer conditions with exact soundness/completeness statements in the paper. The landing-page summary is not enough to claim subsumption. |
| Game semantics | The abstract reports definability and an observationally fully abstract quotient for PCF, including effective universality. [Abramsky, Jagadeesan and Malacaria](https://arxiv.org/abs/1311.6125v2). | Inspect theorem premises and whether any claimed Thiele contextual equivalence has an actual analogous definability result. No model translation yet. |
| Provenance semirings | Exact statements of Propositions 3.4, 3.5, 4.2 and Theorem 4.3 inspected above. | Test a concrete structural-operation/evidence interpretation; distinguish sequential order and mutation from commutative annotations. |
| Amortized resource analysis | Author-hosted paper describes multivariate potential analysis, a type system, soundness and automated inference. [Hoffmann, Aehlig and Hofmann](https://www.cs.cmu.edu/~janh/assets/pdf/HoffmannAH10.pdf). | Compare expanded entitlement/payment contracts with exact operational potential inequalities; do not equate an exact ledger identity with an inferred resource bound. |

## Required short account and review

The eventual account must name the closest prior theorem and finish this claim with evidence: compared with that theorem, the specified Thiele result establishes a particular additional conclusion under listed premises, resolving a named question. The evidence must include a complete argument and an applicable nontrivial instance, or an explicit translation showing that the result is already covered.

For a proposed evidence-reuse result, specify the evidence's proposition, dependency state, allowed mutations, composition operation, and later observation first. A counterexample to preserving a deleted field is a useful sanity check, but not by itself the intended contribution. For a proposed uniqueness result, show descent through VM trace identifications and preservation of every promised operation; merely defining an observational quotient is insufficient to characterize what it contains.

A specialist should be able to identify the exact new step, give a covering prior theorem and translation, expose an invalid inference, or request a specific missing premise. No external reviewer has yet been contacted. An unfavorable result should guide the research honestly. At this stage neither a significant new foundational theorem nor a reduction of the entire Thiele framework has been established.
