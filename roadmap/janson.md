# Group: `janson` — Chapter 8

What the chapter establishes: exponential bounds on the probability that a random subset
contains **none** of a prescribed family of sets, and on the lower tail of the count. Where the
second moment method (Chapter 4) gives polynomial decay, these give exponential decay — which
is what makes the chromatic-number application of §8.3 possible.

**Nothing in this chapter is in Mathlib.**

## Setup

Setup 8.1.1 throughout: `R` is a random subset of `ι`, each element kept independently with
probability `p`. That is Mathlib's `setBernoulli`, which already carries an
`IsProbabilityMeasure` instance and is the same primitive `SimpleGraph.binomialRandom` is built
from — so Chapters 7 and 8 sit on a common foundation.

Three definitions are authored here rather than inlined, because all three theorems share them
and a task's statement mentioning them makes them interface:

- `jansonMu p S` — `μ = ∑ ℙ(S i ⊆ R)`;
- `jansonDelta p S D` — `Δ = ∑_{(i,j) ∈ D} ℙ(S i ∪ S j ⊆ R)`;
- `jansonCount S R` — the random variable `X`, as `Set.ncard {i | S i ⊆ R}`. Not a
  `Finset.filter`: set inclusion on `Set ι` is undecidable and the project does not add
  `Decidable` instances.

**`D` is a parameter, not derived from `S`** — the same decision as `variance_sum_indicator_le`
in Chapter 4, and for the same reason. The hypothesis constrains only pairs *outside* `D`
(they must be disjoint, hence independent), so any `D` containing every dependent ordered pair
is admissible and a larger `D` merely weakens the bound. Note the book counts `(i,j)` and
`(j,i)` separately in `Δ`.

## `janson_one` — `janson_prob_none_le`

Theorem 8.1.2: `ℙ(X = 0) ≤ exp(-μ + Δ/2)`.

Useful when `Δ = o(μ)`. Remark 8.1.3 is the reason this chapter is paired with Chapter 7:
Harris' inequality gives the matching *lower* bound `exp(-(1+o(1))μ)` in the same regime, so
the two together determine the probability rather than merely bounding it.

The proof conditions the events one at a time and bounds each conditional probability below by
`ℙ(A i) - ∑_{j < i, j ~ i} ℙ(A i A j)`; that step is itself an application of Harris'
inequality (Corollary 7.1.6), so **`janson_one` genuinely depends on Chapter 7**.

## `janson_two` — `janson_prob_none_le_of_mu_le`

Theorem 8.1.8: when `Δ ≥ μ`, `ℙ(X = 0) ≤ exp(-μ²/(2Δ))`.

Covers the regime where the first inequality says nothing. Proved *from* the first by applying
it to a random subsample of the events — include each index with probability `q`, note
`𝔼μ_T = qμ` and `𝔼Δ_T = q²Δ`, and optimise at `q = μ/Δ ∈ [0,1]`.

## `janson_three` — `janson_lower_tail`

Theorem 8.2.2: for `0 ≤ t ≤ μ`, `ℙ(X ≤ μ - t) ≤ exp(-t²/(2(μ+Δ)))`.

The strongest of the three — taking `t = μ` recovers the other two up to a constant in the
exponent. The proof is a moment-generating-function argument in the style of the Chernoff
bound, using the first inequality on an auxiliary family.

**There is deliberately no upper-tail companion.** Example 8.2.4 shows the analogous bound is
*false*: planting a clique of size `Θ(np)` forces an excess of triangles with probability
`p^{Θ(n²p²)}`, far above `exp(-Θ(n²p))`. Anyone tempted to state the symmetric version should
read that example first.

## Not stated

The asymptotic consequences — Theorem 8.1.6, Corollary 8.1.7, Theorem 8.1.10 (the two-regime
triangle-free estimate), Theorem 8.2.5 (Harel–Mousset–Samotij) and §8.3's chromatic number of
`G(n,1/2)` (Theorem 8.3.2, Bollobás) — are planned rather than stated. The `whp` convention they
need is now settled (see `README.md`), which leaves one blocker, and it is not the one recorded
here before: **the ground set, not the `G(n,p)` API.** Mathlib's `binomialRandom` is

    G(V, p) = setBer(Sym2.diagSetᶜ, p).comap edgeSet

so `G(n,p)` *is* a `setBernoulli`, and the API around it is adequate. But every theorem in this
chapter is fixed at `setBernoulli Set.univ p`, and those statements are frozen. Transferring
them to a ground set that omits the diagonal is `map_inter_setBernoulli` (#193), which is
therefore the single shared prerequisite for all five.

Theorem 8.3.2 additionally needs Lemma 8.3.3 and the iterated-extraction colouring argument,
which is a substantial development of its own.

**The lesson in the correction:** the old note said these needed "a worked `G(n,p)` API", which
sounded like a large build-out and priced the whole group out of reach. The actual obstruction
was a one-lemma impedance mismatch between two ground sets. A blocker recorded at the wrong
level of abstraction is worse than no note, because it stops anyone from looking again.

## `[Countable ι]`, and how it was found

The three Chapter 8 statements originally had no countability hypothesis and **were false
without one**. The defect was found by the contributor proving `janson_one`, who filed it on
the issue instead of working around it.

The measurable space on `Set ι` is the product σ-algebra: a set is measurable only if it depends
on countably many coordinates. For uncountable `S i` the event `{R | S i ⊆ R}` is therefore not
measurable, and `setBernoulli` does not fail — it silently returns an *outer* measure. At `p = 1`
that breaks the inequality. With `ι` uncountable, `κ = Unit`, `S 0 = univ` and `D = ∅`, the event
`{R | R ≠ univ}` has no measurable superset excluding `univ`, because a measurable set depends on
countably many coordinates `J` and containing any `R ≠ univ` forces it to contain `univ` as well.
So the left side is `1` while `μ = 1` and `Δ = 0` put the bound at `exp(-1)`.

Mathlib's own `SetBernoulli` API draws the line in the same place — everything substantive in
`SetBernoulli.lean` sits inside `section Countable`. **That is the tell worth remembering: when
upstream gates part of an API behind a hypothesis, a statement built on the ungated part is
suspect.**

## `janson_step` — `janson_prob_none_step_le`

The Boppana–Spencer conditioning step, left behind as a declared reduction when `janson_one`
landed. Stated multiplicatively over a `Finset`, so that no ordering, no conditional
probability and no positivity side condition appear in the statement — which is what makes it a
reusable node rather than a private step. Its inputs are `harris_setbernoulli` and
`setbernoulli_block_indep` in `Correlation.lean`.

## `janson_two` — the diagonal of `D`, and the route that works

The route originally published for `janson_prob_none_le_of_mu_le` was wrong, and a contributor
caught it. It prescribed independent `q`-sampling of the index set with `𝔼 Δ_T = q² Δ`. But `D`
is an arbitrary `Finset (κ × κ)` and may contain diagonal pairs `(i, i)`, which survive sampling
with probability `q`, not `q²`. So `𝔼 Δ_T = q² Λ + q δ`, and the averaging genuinely breaks
rather than merely getting messier — with `δ = sμ` the required inequality fails once `Λ ≫ μ`,
which is exactly the regime this theorem is for.

**The statement was never wrong**: a larger `Δ` only weakens `exp(-μ²/(2Δ))`. Only the route was.

The fix is to run the argument on `E := D.filter (fun z => z.1 ≠ z.2)` with `Λ := jansonDelta p S E`.
Then `hD` transfers unchanged — for `i ≠ j`, `(i,j) ∈ E ↔ (i,j) ∈ D` — and `Λ ≤ Δ`. **No case
split is needed**, which is the nice part: with `q = μ/Δ`,

    −qμ + q²Λ/2 = −μ²/Δ + μ²Λ/(2Δ²) ≤ −μ²/(2Δ)   ⟺   Λ ≤ Δ,

true by construction, so the hypothesis `Λ ≥ μ` that the naive route needs never arises. And
`q = μ/Δ ≤ 1` is precisely this theorem's own hypothesis.

## `janson_three` — and the one primitive it still needs

`janson_lower_tail` is proved modulo `janson_lower_tail_step_le`, the Chernoff/thinning step of
Warnke's argument. `exp_neg_le_one_sub_add_sq_div_two` — `exp (-x) ≤ 1 - x + x²/2` for `x ≥ 0`,
proved **without calculus** from `Real.quadratic_le_exp_of_nonneg` — is the analytic input and is
already closed.

The obstacle in the remaining step is structural rather than analytic. Thinning by an independent
Bernoulli `q` leaves the index set carrying **per-coordinate** inclusion probabilities (`p` on
`ι`, `q` on `κ`), and `setBernoulli` is uniform-`p` only, so `janson_prob_none_le` cannot be
applied literally even though Janson I is true for arbitrary independent probabilities.
`setBernoulliPi` in `Correlation.lean` now supplies the missing measure.

**What is deliberately still unstated** is a non-uniform Janson I. Stating it means choosing
whether `jansonMu`/`jansonDelta` are generalised in place — they are consumed by three
already-proved theorems whose proofs must not break — or whether a parallel pair is better. That
choice is better made by someone holding the proof, so the task asks for a proposal instead of
handing down an interface. If the thinning turns out to route through a *product* of two uniform
`setBernoulli`s, no non-uniform Janson I is needed at all.

## `janson_three` is proved, and the thinning needed no new measure

`janson_lower_tail` (Janson III) is **unconditional**. The interesting part is that the route I
predicted was wrong, and in an instructive direction.

I expected the Chernoff/thinning step to need a **non-uniform** Bernoulli, because Warnke's
argument thins the index set by an independent Bernoulli `q` and `setBernoulli` is uniform-`p`
only. I authored `setBernoulliPi` for it. **It turned out not to be needed at all**: `κ` is a
`Fintype`, so a thinned family is a `Finset κ` and the `q`-average is a *finite sum* against
weights `q^#T (1-q)^#(U\T)`, carried entirely inside the existing `p`-space. What would have been
Fubini is finite additivity.

Three things from that proof worth keeping:

- **The finite-sum `Φ` really is the MGF**, and the check that it is not a weaker surrogate is
  that *both* bounds meet: it is lower-bounded by `e^{-lam s} ℙ(X ≤ s)` and upper-bounded by
  `exp(-qμ + q²Δ/2)`. A degenerate quantity could satisfy one, not both.
- **The `q²` needs no FKG.** The increasing function is a single coordinate indicator, so pairing
  `T` with `insert j T` reduces the correlation step to termwise `P (insert j T) ≤ P T`. This is
  the one-coordinate case of Harris done by hand.
- **Markov as a finite partition does not trip the outer-measure hazard.** `{X ≤ s} = ⋃ EV J` with
  each `EV J` measurable and `measure_biUnion_finset` giving an equality. `[Countable ι]` is
  load-bearing a second time here, because Mathlib's `Measurable.subset` sits under
  `[Countable α]`.

**The negative result, recorded so it is not re-derived:** routing the thinning through a
*product* of two uniform `setBernoulli`s does not work. `janson_prob_none_le` requires its measure
to be literally `setBernoulli Set.univ p'` on some `Set ι'`, and a product on `Set ι × Set κ` is
not of that form; re-indexing does not fix it, because `lam` is universally quantified so
`q = 1 - e^{-lam}` ranges over all of `[0,1)` independently of `p`.

`setBernoulliPi` stays in `Correlation.lean`. It is correct, proved, and a faithful
generalisation — it is simply not what this chapter needed. **Authoring a primitive on a
predicted need rather than a demonstrated one is the mistake to avoid repeating.**

## Chapter 8 is complete

All three Janson inequalities are proved and `Janson.lean` has **zero `sorry`s**, verified with
`#print axioms` on each rather than inferred from green merges.

## Resolved: the duplicated `Δ`-bookkeeping

Roughly 75–80 lines inside `janson_lower_tail_step_le` duplicate `janson_prob_none_le`'s
`E`-bookkeeping near-verbatim, plus ~18 more around the conditioning step. The contributor
offered to extract it and was right not to: extraction means a new top-level declaration, which
is orchestrator work under this project's own rule.

**Done**, once Janson II landed and the file had no open task against it — which was the point of
waiting rather than doing the surgery twice or invalidating work in flight.

`sum_filter_insert_le` now states the step over an explicit `b` and `D` rather than over the local
`E` abbreviation each proof introduces. That is what makes one lemma serve all the call sites: `E`
and `b` are introduced by `⟨_, fun _ => rfl⟩` definitional abbreviations, so a top-level lemma can
talk about the underlying sums directly and each caller discharges with `rw [hE, hE]`. Both
55-line blocks collapse to three lines each; net **−40 lines** across the file, with all three
inequalities still axiom-clean.

The `K = ∅` case of `sum_powerset_weight_eq` — contributed with Janson II — also subsumed a local
`hbinom` inside the lower-tail proof, now rewritten as a one-liner. **Three separate contributors
each wrote a copy of the same binomial-weight-over-powerset identity before anyone had a top-level
lemma to reach for**; that is the recurring cost of statements landing in parallel against a
pinned base, and the orchestrator is the only party positioned to fix it.

Still open, recorded rather than acted on: `prob_none_le_subfamily` re-derives by subtype
instantiation what the internal `key` of `janson_prob_none_le` already proves for every
`Finset κ`. The right shape is for Janson I to expose a `Finset` companion instead of being
stated only at `univ`. **Not built, because nothing currently needs it** — the same discipline
`setBernoulliPi` violated.
