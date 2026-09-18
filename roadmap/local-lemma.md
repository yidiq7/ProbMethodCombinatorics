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

## `one_sub_sum_le_prod_one_sub` — Weierstrass product inequality

`1 - ∑_{j ∈ s} y j ≤ ∏_{j ∈ s} (1 - y j)` for weights in `[0,1]`, contributed with
`lll_sum` (PR #45).  Mathlib has no equivalent — checked — and the statement is general
(any `Finset κ`, real-valued), so it is reusable rather than bespoke to the local lemma.

## `lovasz_local_lemma_of_sum_le`

Corollary 6.1.10. `ℙ(A i) < 1/2` and `∑_{j ∈ N i} ℙ(A j) ≤ 1/4` ⟹ positive probability none
occur. From the general form with `x i = 2 ℙ(A i)` and a union bound on the product. The
right tool when the bad events have genuinely different probabilities.

## The uniform random two-colouring — `fairCoin`, `uniformColoring` and friends

Authored centrally on 2026-09-13, after #49, #50 and #53 each rebuilt it from scratch.

`uniformColoring κ = Measure.pi fun _ => fairCoin` — each coordinate an independent fair
coin — with two working facts:

- `uniformColoring_const T b` : a colouring is constant `b` on `T` with probability `2⁻¹ ^ |T|`;
- `uniformColoring_inter_eq_mul` : events determined by **disjoint** sets of coordinates are
  independent.  This is Setup 6.1.5 in the form the applications need.

The index type is arbitrary, which is the point: the hypergraph applications colour vertices
(`α`), Spencer's Ramsey bound colours edges (`Finset (Fin n)`).  **Every new application in
this chapter should use these rather than rebuilding `Measure.pi` over `Bool`.**

The lesson for the plan, not just this file: the need for this layer was visible when #28 was
written, and the prose said so while leaving it to contributors.  A definition several tasks
depend on is an interface, and interfaces are authored centrally *before* the tasks that need
them are published.

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

**§6.3 is stated** as `exists_independent_transversal` (#185), and **Theorem 6.2.4** as
`twoColorable_of_sum_inv_two_pow_le` (#190) — the short follow-on this section predicted.  What
remains:

§6.4 (directed cycles of length divisible by `k`),
§6.5 (the lopsided local lemma) and §6.6 (the algorithmic local lemma, Moser–Tardos). §6.5 needs the general form's proof refactored so that step (6.3) uses a
correlation inequality rather than independence — worth doing only once the general form is
proved. §6.6 is an algorithmic result whose statement needs a model of the resampling
process; it is the largest single item in the chapter.

Also not stated: Theorem 6.2.6 and Lemma 6.2.7 (the compactness argument extending the lemma
to infinite vertex sets, via Tychonoff), and Theorems 6.2.10–6.2.11 (multicoloured translates;
Beck's colouring of arithmetic progressions).  The three general local-lemma forms
(`lovasz_local_lemma`, `lovasz_local_lemma_symmetric`, `lovasz_local_lemma_of_sum_le`) have all
landed, so these are reachable now rather than blocked.

**Corrected 2026-09-17**: this list used to also name Theorem 6.2.4, which contradicted the
paragraph above it — 6.2.4 *is* `twoColorable_of_sum_inv_two_pow_le` (#190) and has been proved
since 2026-09-16.

**§6.4 assessed 2026-09-17.**  Theorem 6.4.3 (Alon–Linial): a digraph with min out-degree `δ`
and max in-degree `Δ` has a cycle of length divisible by `k` whenever
`k ≤ δ / (1 + log (1 + δΔ))`.  The probabilistic half is a routine symmetric-local-lemma
application (label each vertex by `x v ∈ ZMod k`, let `A v` be the event that no out-neighbour
carries `x v + 1`, so `ℙ(A v) = (1 - 1/k) ^ δ`).  The blocker is vocabulary, not probability:
Mathlib's `Combinatorics/Digraph/` has only `Basic.lean` and `Orientation.lean` — **no directed
walk, no directed cycle** — so the closing step, extracting a cycle from the functional graph
of "successor with label `+1`", has nothing to be stated against.  This is the same shape of
obstacle §5.3 had, and it was resolved there by authoring the vocabulary and validating it by
exhaustive small-case search before any theorem was stated.  The same discipline applies here.


## §6.2's infinite-vertex-set material, stated 2026-09-17/18

**Lemma 6.2.7 (compactness)** is `exists_forall_notMem_of_forall_finset`, proved in #275.  It
is pure Tychonoff — no probability, no local lemma: give each variable type the discrete
topology, observe that `hdet` makes every bad event a union of basic open boxes, and run
`elim_finite_subfamily_closed` against the finite-intersection property supplied by the
hypothesis.  The index type of the *events* is unrestricted (it is `ℝ` in both applications);
what must be finite is the set of values each *variable* can take, which is Remark 6.2.8's
point.

It lives in a new `Compactness` section rather than `Applications`, because that section's
`variable` line fixes `[Fintype α]` and the whole purpose here is an infinite vertex set.  The
same constraint forced `twoColorable_of_le_card_inter_card_le`, which is
`twoColorable_of_inter_card_le` with two restrictions lifted: edges may have *at least* `k`
vertices, and `α` need not be a `Fintype`.  Neither lift needs the local lemma re-derived —
non-uniform reduces to uniform by shrinking each edge to a `k`-subset (neighbour counts only
shrink), and an arbitrary vertex type reduces to `H.sup id`.

**Theorem 6.2.10 (multicoloured translates)** is stated in `Coloring.lean`, again a separate
file so that nothing is added to `LocalLemma.lean` while tasks are pinned to it.

The reason this was cheap: Chapter 6's existing colouring machinery is `Bool`-valued
(`fairCoin`, `uniformColoring`), and more than two colours looked like it would need the whole
independence layer rebuilt.  It does not.  Mathlib's `uniformOn_pi` already proves that the
uniform measure on `κ → β` *is* `Measure.pi`, and this project's `measure_pi_inter_eq_mul` was
written index-generically rather than for `Bool`, so it applies unchanged.
`instIsProbabilityMeasure_uniformOn_univ` comes free as well.  The lesson is the mirror of the
stale-blocker one: a piece of infrastructure written generically once pays out at a distance,
and it is worth checking how general the existing lemma actually is before generalising it.

The hypothesis was checked non-vacuous before stating: the least admissible `m` is `9, 20, 33,
46, 123` for `k = 2, 3, 4, 5, 10`.  The degenerate corner needs no guard — `m = 0` would force
`e·k ≤ 1`, impossible for `k ≥ 1`.

**This also unblocks half of §6.4.**  Alon–Linial labels vertices by `ZMod k`, and the
non-`Bool` uniform colouring was one of its two obstacles.  The other — no directed walk or
cycle anywhere in Mathlib's `Combinatorics/Digraph/` — stands, and is an authoring job of the
same shape as `IsKSubdivision`.
