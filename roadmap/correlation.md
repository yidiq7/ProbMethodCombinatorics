# Group: `correlation` — Chapter 7

What the chapter establishes: **increasing events of independent variables are positively
correlated.** The slogan does the work in Chapter 8, where the matching upper bounds come from
Janson's inequality.

## Already upstream, not tasks

- **`IsUpperSet.le_card_inter_finset`** (`Mathlib/Combinatorics/SetFamily/HarrisKleitman.lean`)
  — Harris–Kleitman: for up-sets `𝒜, ℬ` of `Finset α`,
  `#𝒜 * #ℬ ≤ 2 ^ |α| * #(𝒜 ∩ ℬ)`. This is Theorem 7.1.1 for the **uniform** measure, in
  counting form, together with the mixed and lower-set variants.
- **`fkg`** (`Mathlib/Combinatorics/SetFamily/FourFunctions.lean`) — the
  Fortuin–Kasteleyn–Ginibre inequality for a log-supermodular measure on a distributive
  lattice, with `holley` and the four functions theorem beside it.

So the *uniform* case of this chapter is done. What is missing is the case the applications
need: an arbitrary edge probability.

## `harris_binomial` — `binomialRandom_mul_le_inter`

Theorem 7.1.1 for `G(V, p)`: two increasing graph properties are positively correlated.
`SimpleGraph V` is a `CompleteAtomicBooleanAlgebra`, so `IsUpperSet` applies directly, and
`SimpleGraph.binomialRandom` is Mathlib's `G(V, p)`.

**Proved (PR #80) by reduction to `fkg`.** The step that makes it work: `G(V, p)` is not
merely log-*super*modular but log-**modular**. `binomialRandom_singleton` gives each graph mass
`p^|E(G)| · σp^(C(n,2) - |E(G)|)`, and `|E(a ⊓ b)| + |E(a ⊔ b)| = |E(a)| + |E(b)|` by
inclusion–exclusion on edge sets, so `fkg`'s hypothesis holds with equality.

The PR also settles a question left open when the task was written: **every set of graphs is
measurable for a `Fintype V`.** `MeasurableSingletonClass (SimpleGraph V)` follows from
`measurable_adj`, so the `MeasurableSet` hypotheses on this statement are redundant — callers
can discharge them with `measurableSet_discrete` or similar. They are left in place rather than
churned, but a future golf could drop them.

The content beyond upstream is precisely that `p` is arbitrary — Harris–Kleitman is the
`p = 1/2` case. The natural route is to transport the four functions theorem along
`SimpleGraph.edgeSet`, whose measurable-embedding property Mathlib already provides
(`measurableEmbedding_edgeSet`), turning the statement into one about a product of Bernoulli
measures on edge indicators.

## `harris_lower_family` — `prod_le_binomialRandom_iInter`

Corollary 7.1.6 in the form the applications use: finitely many *decreasing* properties, all
holding, with probability at least the product. Follows from the pairwise increasing case by
complementation and induction on the family — the induction is the real work, since each step
must re-establish that a finite intersection of lower sets is a lower set.

## `triangle_free_lower` — `le_binomialRandom_cliqueFree_three`

Theorem 7.2.2: `ℙ(G(n,p) triangle-free) ≥ (1 - p³)^{n choose 3}`.

For each triple, "does not span a triangle" is decreasing with probability exactly `1 - p³`;
the triples overlap, so independence fails, but `harris_lower_family` bounds the intersection
below by the product.

Remark 7.2.3 is worth knowing when judging this bound: it is the better of the two easy lower
bounds only when `p ≪ n^{-1/2}`; for larger `p` the bound
`ℙ(triangle-free) ≥ ℙ(empty) = (1-p)^{n choose 2}` wins. **Chapter 8 supplies the matching
upper bounds**, which is the point of the pairing.

## Not stated

**Theorem 7.1.5**, the monotone-*function* form `𝔼[fg] ≥ 𝔼[f]𝔼[g]`, which implies the event
form by taking indicators. Stating it needs a product measure over arbitrary linearly ordered
factors and integrability side conditions; the event form covers every application in the
book, so this waits until something needs it.

**Theorem 7.2.5** (Riordan–Selby, `ℙ(maxdeg G(n,1/2) ≤ n/2) = (0.6102… + o(1))ⁿ`) and
**Proposition 7.2.6** are not stated: the first is quoted without proof in the source, and the
second needs Gaussian random variables and a Laplace-method estimate.

## The `setBernoulli` forms, for Chapter 8

Chapter 8 lives on `setBernoulli` — a random *subset* of an index type — not on
`binomialRandom`, and it needs the **mixed** pairing rather than the increasing/increasing one.
Both facts were requested by the contributor who proved `janson_prob_none_le`, after
establishing that the step genuinely cannot be done by subadditivity: the union bound gives
`ℙ(Aᵢ)ℙ(B) − ∑ ℙ(AᵢAⱼ)` where the argument needs `(ℙ(Aᵢ) − ∑) ℙ(B)`, and `ℙ(B) ≤ 1` points the
wrong way. They are stated here rather than left to a task to invent, per the shared-layer rule.

- `harris_setbernoulli` — `A` increasing and `B` decreasing are *negatively* correlated. The
  `setBernoulli` analogue of `binomialRandom_mul_le_inter`, in the shape the Boppana–Spencer
  conditioning step pairs them.
- `setbernoulli_block_indep` — events determined by disjoint coordinate blocks multiply.
  "Determined by the block" is stated as invariance under changes outside it, which is what a
  caller can actually establish.

**Neither takes `MeasurableSpace ι` or `MeasurableSingletonClass ι`.** `setBernoulli` needs
neither, and requiring them would have made both lemmas unusable from `Janson.lean`, where `ι`
carries no measurable structure. That was checked by applying them in that context before the
tasks went out — a signature that type-checks in isolation is not the same as one that can be
used.

## What did *not* work for `harris_setbernoulli`, and why

Recorded because it cost real time and the failure is not obvious from the type signatures.

**`fkg` does not apply.** Mathlib's `fkg` requires `[Fintype α]`, and `Set ι` for merely
`Countable ι` is infinite, so there is no finite sum over singletons to build the
log-supermodular density from. This is the central obstruction and no amount of massaging the
lattice gets around it. The proof instead goes by **transport through complementation** from an
increasing/increasing form, done additively in the `ENNReal` `CommSemiring` exactly as the
conventions note prescribes.

**`ℝ≥0∞` is not a `CommSemiring` with `IsStrictOrderedRing`**, so the four-functions step has to
go through `ℝ≥0` and be transported back.

`setBernoulli_mul_le_inter`, the increasing/increasing companion, is public and sits beside
`binomialRandom_mul_le_inter`; it is the direct analogue and the two belong together.

## A non-uniform Bernoulli on subsets

`setBernoulliPi f` keeps coordinate `i` with probability `f i`, independently. It exists because
Warnke's proof of the Janson lower tail thins the index set by an independent Bernoulli `q`, so
the thinned space has per-coordinate probabilities that `setBernoulli` — uniform-`p` only —
cannot express. The contributor who proved `janson_lower_tail` identified the gap and **stopped
at it** rather than inventing a primitive inside `Janson.lean`; authoring it centrally is the
rule, and this is the second time that rule has paid for itself.

`setBernoulli_eq_setBernoulliPi` recovers `setBernoulli` exactly. **That lemma is the point**: a
new definition that merely elaborates proves nothing, and the specialisation is what shows the
generalisation is faithful. It is stated with hypotheses rather than
`f = fun i ↦ if i ∈ u then p else 0`, since that spelling needs `Decidable (i ∈ u)`.

The `IsProbabilityMeasure` instance is registered immediately and the docstring says why:
`Measure.infinitePi` is `if h : ∀ i, IsProbabilityMeasure (μ i) then … else 0`, so without it the
definition is silently the zero measure and every `infinitePi` lemma fails to fire with no error.


## `setBernoulli_cylinder` — the lemma to reach for

Found by the contributor who proved `prob_mem_monotone` (#158), and not known to me when that
task was written: Mathlib's `setBernoulli_cylinder` computes the measure of a cylinder event
directly, which gives "misses every element of a finite `J`" as `(1 - s) ^ #J` in one step.

**Reach for it before building cylinder computations by hand.** It is the natural tool for
anything in Chapters 7–8 that needs the probability of a prescribed pattern on finitely many
coordinates, and this project has written that kind of computation out longhand more than once.

The proof of `prob_mem_monotone` is also worth reading as a model: it takes Zhao's **Proof 2**
(two-round exposure) rather than the monotone coupling, constructing `p'` with
`(1-p)(1-p') = 1-q` and matching the two distributions on the avoidance events, which generate
the σ-algebra. That stays inside `setBernoulli` throughout; the coupling route would have needed
an auxiliary `[0,1]`-valued field. The `p = 1` branch has to be split out — `1 - p = 0` forces
`q = 1`, available only because `p ≤ q ≤ 1` — and for `p < 1` the witness `(q-p)/(1-p)` needs
*both* endpoints of `I` to be placed.
