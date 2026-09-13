# Group: `local-lemma` — Chapter 6

What the chapter establishes: the Lovász local lemma, which avoids a family of bad events
when each is unlikely *and* each depends on few others — the regime between full
independence and a union bound.

**Measure-theoretic, necessarily.** The independence in play (Definition 6.1.1) is
independence from a whole *family* of events, meaning independence of every signed
intersection of them. That is strictly stronger than pairwise independence, and Remark
6.1.4 gives the standard three-event counterexample showing the difference is real. It does
not reduce to counting, so this group is stated over `MeasureTheory.Measure`, as Chapter 4 is.

Mathlib has no local lemma in any form.

## `pattern`, `indep_from`, `is_dependency_graph`

`pattern B s f = ⋂ j ∈ s, if f j then B j else (B j)ᶜ` is the event that each `B j`, `j ∈ s`,
occurs or fails according to the sign vector `f`.

`IndepFrom μ A B s` (Definition 6.1.1) says `μ (A ∩ pattern B s f) = μ A * μ (pattern B s f)`
for every `f` — `A` is independent of the whole family, not merely of each member.

`IsDependencyGraph μ A N` (Definition 6.1.2) says each `A i` is `IndepFrom` every set of
events avoiding `i` and its neighbours `N i`. Note the direction: the definition constrains
the *non-neighbours*, so the complete graph is always a valid dependency graph and `N` is
not determined by `A`. Applications supply `N` from the structure of the problem (Setup
6.1.5: events depending on disjoint sets of independent variables are independent), never by
testing pairs for independence.

## `measure_inter_biInter_compl_le` — the induction step

Equation (6.1) of Theorem 6.1.9, contributed as its own declaration with the general form
(PR #41): for `i ∉ S`,

    ℙ(A i ∩ ⋂_{j ∈ S} (A j)ᶜ) ≤ x i · ℙ(⋂_{j ∈ S} (A j)ᶜ).

Note the **product form** rather than `ℙ(A i | ⋂_{j ∈ S} (A j)ᶜ) ≤ x i`.  The two agree when
the conditioning event has positive measure, and the product form is automatically true when
it is null — which removes the positivity side conditions that make the conditional statement
awkward to carry through the induction.  Worth imitating elsewhere in this group.

## `lovasz_local_lemma` — general form

Theorem 6.1.9. With weights `x i ∈ [0,1)` satisfying `ℙ(A i) ≤ x i ∏_{j ∈ N i} (1 - x j)`,
the probability that no `A i` occurs is at least `∏ i (1 - x i)`.

The chapter's one real theorem; everything else in the group follows from it. The proof is
an induction on `|S|` establishing `ℙ(A i | ⋂_{j ∈ S} A_jᶜ) ≤ x i`, splitting `S` into
`S₁ = S ∩ N i` and `S₂ = S \ S₁`, bounding the numerator by independence from `S₂` and the
denominator by the induction hypothesis applied along a chain. Conditional probability is
`ProbabilityTheory.cond` (`μ[·|·]`); the chain rule and the positivity side conditions
(every conditioning event must have non-zero measure, which the induction itself supplies)
are where the formalization work lives.

Expect a reduction. The induction statement (6.1) is the natural sub-node.

## `lovasz_local_lemma_symmetric`

Theorem 6.1.7. `ℙ(A i) ≤ p`, `|N i| ≤ d`, `e p (d+1) ≤ 1` ⟹ positive probability none occur.
The form used in practice. Follows from the general form with `x i = 1/(d+1)`, using
`(1 - 1/(d+1))^d > 1/e`. The constant `e` is optimal (Shearer 1985).

## `lovasz_local_lemma_of_sum_le`

Corollary 6.1.10. `ℙ(A i) < 1/2` and `∑_{j ∈ N i} ℙ(A j) ≤ 1/4` ⟹ positive probability none
occur. From the general form with `x i = 2 ℙ(A i)` and a union bound on the product. The
right tool when the bad events have genuinely different probabilities.

## `two_colorable_local` — `twoColorable_of_inter_card_le`

Theorem 6.2.1: a `k`-uniform hypergraph whose every edge meets at most `d` others is
2-colourable when `e (d+1) ≤ 2^{k-1}`.

The contrast with Theorem 1.3.1 (group `introduction`) is the point of the chapter: that
result caps the *total* number of edges, this one caps only local overlap, so arbitrarily
large hypergraphs qualify. Apply the symmetric form to the events "edge `f` is
monochromatic", each of probability `2^{1-k}`.

## `two_colorable_regular` — `twoColorable_of_regular`

Corollary 6.2.2: every `k`-uniform `k`-regular hypergraph with `k ≥ 9` is 2-colourable.
Each edge meets at most `k(k-1)` others, and `e(k(k-1)+1)2^{1-k} < 1` for `k ≥ 9`. Short
given the previous node; the arithmetic at `k = 9` is the only fiddly part. (True for all
`k ≥ 4` by Thomassen 1992, and false for `k = 2, 3` — do not try to strengthen it.)

## `ramsey_spencer` — `lt_ramseyNumber_of_local_lemma`

Theorem 1.1.9 (Spencer 1977), which the book states in Chapter 1 but proves with the local
lemma, so it lives here. Applied to the events "`S` spans a monochromatic `K k`", with two
such events dependent only when their vertex sets share an edge, it gives
`R(k,k) > (√2/e + o(1)) k 2^{k/2}` — **the best lower bound on the diagonal Ramsey number
known to date**, a factor `√2` above `lt_ramseyNumber` (task #7).

Depends on `ramseyNumber` and `RamseyProperty` from `Ramsey.lean`, and on
`RamseyProperty.mono` and `exists_ramseyProperty` for the same reason task #7 does: `sInf` of
the empty set is `0`.

## Not stated

§6.3 (independent transversals), §6.4 (directed cycles of length divisible by `k`),
§6.5 (the lopsided local lemma) and §6.6 (the algorithmic local lemma, Moser–Tardos) are
planned. §6.5 needs the general form's proof refactored so that step (6.3) uses a
correlation inequality rather than independence — worth doing only once the general form is
proved. §6.6 is an algorithmic result whose statement needs a model of the resampling
process; it is the largest single item in the chapter.

Also not stated: Theorem 6.2.4 (non-uniform hypergraphs, via Corollary 6.1.10), Theorem
6.2.6 and Lemma 6.2.7 (the compactness argument extending the lemma to infinite vertex
sets, via Tychonoff), and Theorems 6.2.10–6.2.11 (multicoloured translates; Beck's colouring
of arithmetic progressions). All are reachable once the three local-lemma forms land, and
6.2.4 in particular is a short follow-on.
