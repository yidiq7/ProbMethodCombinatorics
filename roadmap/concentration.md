# Group: `concentration` — Chapter 9

What the chapter establishes: **a Lipschitz function of many independent random variables is
concentrated.** Chapter 5's Chernoff bound is the case where the function is a sum; the point
here is that no sum structure is needed.

This is the longest chapter in the book (44 pages) and the frontier stated for it is
deliberately one node. The rest is planned, for reasons given below.

## Already upstream

- **`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`** — Hoeffding's lemma (Lemma 9.2.12):
  a mean-zero variable in an interval of length `ℓ` has `𝔼[e^{tX}] ≤ e^{t²ℓ²/8}`. This is the
  analytic engine of the whole chapter.
- **`measure_sum_ge_le_of_iIndepFun`** — Hoeffding's inequality for sums of independent
  sub-Gaussian variables, plus the surrounding `ProbabilityTheory.HasSubgaussianMGF` API.

Mathlib has **no** Azuma inequality and **no** bounded differences inequality; a search for
`azuma` and `mcdiarmid` returns nothing.

## `bounded_differences` — `measure_sub_integral_ge_le`

Theorem 9.1.3: if changing coordinate `i` alone moves `f` by at most `c i`, then

    ℙ(f - 𝔼f ≥ λ) ≤ exp(-2λ² / ∑ᵢ cᵢ²).

Stated over `Measure.pi`, so independence is structural rather than hypothesised, and with no
martingale in the statement — the martingale is an artefact of the *proof*, not of the claim.
That matters for formalisation: a contributor may take the source's route (Doob martingale plus
Azuma) or go directly through Mathlib's sub-Gaussian machinery, and the statement does not
prejudge it.

Note the constant: `exp(-2λ²/∑cᵢ²)`, not `exp(-λ²/(2∑cᵢ²))`. The source is careful about this
— Theorem 9.2.8's form of Azuma gives the weaker constant, and recovering the sharp one needs
Theorem 9.2.9, the Doob-martingale refinement. Remark 9.2.13 explains why 9.2.9 is genuinely
more versatile: the `cᵢ` there can be smaller than a worst-case Lipschitz bound.

## Planned, not stated

- ~~**Azuma's inequality** (Theorems 9.2.7–9.2.9)~~ — **proved**, as
  `measure_martingale_sub_ge_le`; this bullet was stale from 2026-09-15 to 2026-09-17.  Original
  note kept below for its reasoning. Stating it needs martingales with filtrations,
  which Mathlib has (`MeasureTheory.Martingale`) but which is a heavier commitment than the
  applications require. Worth stating if a contributor wants the source's route to the node
  above; ask first.
- ~~**Theorem 9.3.1** (Shamir–Spencer)~~ — **stated 2026-09-17** as
  `measure_abs_sub_integral_chromaticNumber_ge_le` (#209), on the back of three pieces landed the
  same day: `binomialRandom_eq_map_graphOfExposure` (#201), `abs_sub_chromaticNumber_le_one`
  (#207), and the already-proved `measure_sub_integral_ge_le`.  The "small amount of interface"
  the old note asked for turned out to be the **vertex-exposure product**, and which exposure is
  chosen is not a detail: `n - 1` nonempty vertex blocks give `exp (-2 λ²)`, where `C(n,2)` edge
  coordinates would give only `exp (-2 λ² / C(n,2))`.  That gap is the content of the theorem.

  **It needs `2 ≤ n`, which the source does not state.**  At `n = 1` the radius `λ √(n-1)` is
  zero, the event is everything and the left side is `1`, while the right side falls below `1`
  from `λ = 1` (about `0.0007` at `λ = 2`).  Zhao's interest is asymptotic; the finite form needs
  the hypothesis, and it is also what makes `0 < ∑ cᵢ²` true.
- **Lemma 9.3.3** and the clique-number route to Bollobás' theorem, which the source gives as
  an alternative to the Janson route of §8.3.
- **§9.4 isoperimetry, §9.5 Talagrand's inequality, §9.6 the Euclidean travelling salesman
  problem.** These are research-level and each needs substantial machinery Mathlib lacks —
  a concentration function on the Hamming cube, Talagrand's convex distance, and a
  subadditive-Euclidean-functional framework respectively. They are listed so the plan is
  honest about the chapter's extent, not because they are close.


## Mathlib audit for the unstated remainder (2026-09-15)

Checked what each blocked item's *proof* needs, not just its statement's vocabulary — the
distinction that has now produced two wrong roadmap notes elsewhere in this project.

- **Azuma (9.2.7–9.2.9).** **Stated 2026-09-15** as `measure_martingale_sub_ge_le` (Theorem
  9.2.8), task in the board.  9.2.7 is the `cᵢ = 1` case and is not stated separately.
  Mathlib **has** `Martingale` with `Filtration`
  (`Probability/Martingale/Basic.lean:53`) and conditional expectation, and it **has** Hoeffding
  for sums of *independent* sub-Gaussians (`measure_sum_ge_le_of_iIndepFun`,
  `Moments/SubGaussian.lean:780`) — which is what this project's already-proved
  `measure_sub_integral_ge_le` runs on. What it does **not** have is Azuma itself: the
  martingale-difference version. So this is **real work on existing infrastructure**, not a
  missing-infrastructure block like §4.5's Mertens. Statable whenever someone wants it.

  *Search warning:* grepping Mathlib for "Azuma" returns `Mathlib/Algebra/Azumaya/*` — Azumaya
  algebras, entirely unrelated. A name-substring hit is not evidence the result exists.

- **9.3.1 Shamir–Spencer, §9.4 isoperimetry, §9.5 Talagrand, §9.6 Euclidean TSP.** ~~All still
  research-level, and all downstream of Azuma.~~ **Corrected 2026-09-17: this was wrong twice
  over.**  Azuma has been proved here since 2026-09-15 (`measure_martingale_sub_ge_le`,
  sorry-free), so nothing was downstream of a gap; and 9.3.1 does not go through Azuma at all —
  it runs on the bounded differences inequality, which was proved even earlier.  9.3.1 is now
  stated (#209).  §9.4–§9.6 remain genuinely out of reach, but for their own reasons, not this
  one.

Note the project already has the chapter's headline result — the bounded differences inequality
— proved via the *independent* route rather than through martingales, so nothing here blocks
Chapter 9's existing content.
