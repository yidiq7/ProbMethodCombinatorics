# Group: `alterations` — Chapter 3

What the chapter establishes: the alteration (or deletion) method — make a random
construction, then repair its blemishes. The repair is what lets the construction be
*wasteful*, which is why the bounds beat what a single clean random choice gives.

Section 3.3 is Markov's inequality, which Mathlib already has measure-theoretically
(`MeasureTheory.mul_meas_ge_le_lintegral₀`). This project uses it in counting form, so
`card_filter_le_sum_div` restates it over a `Finset`; that is a project lemma, not a
restatement of an upstream theorem.

## `markov_counting` — `card_filter_le_sum_div`

Zhao, Theorem 3.3.1, in the form the rest of the project needs: for `f ≥ 0` on `s`,

    #{i ∈ s | a ≤ f i} ≤ (∑ i ∈ s, f i) / a.

Every "with positive probability" step in Chapters 1–3 is an instance of this once the
probability is rewritten as a count, so it is worth having as a named lemma rather than
re-derived inline. The easiest node in the group, and the one to prove first.

## `is_dominating`, `dominating_set_bound` — `IsDominating`, `exists_isDominating_card_le`

Theorem 3.1.1. A graph on `n` vertices with minimum degree `δ > 1` has a dominating set of
size at most `((log (δ+1) + 1) / (δ+1)) · n`.

`IsDominating G U` says every vertex is in `U` or adjacent to something in `U`. Mathlib has
no dominating sets at all, so the definition is ours.

The proof is the chapter's opening illustration, and it is the first result in the project
that genuinely needs real analysis: pick each vertex independently with probability `p`,
add a repair set `Y = V \ (X ∪ N(X))` whose expected size is at most `(1-p)^{1+δ} n`, and
optimize `p = log(δ+1)/(δ+1)` using `1 + x ≤ e^x`. The optimization is where `Real.log`
and `Real.exp` enter; `Real.add_one_le_exp` is the inequality.

## `twice_area`, `heilbronn` — `twiceArea`, `exists_heilbronn_configuration`

Theorem 3.2.3. For some absolute `c > 0` and every `n`, there are `n` points in the unit
square with every triple spanning a triangle of area at least `c / n²`.

`twiceArea p q r` is the absolute value of the cross product `(q-p) × (r-p)`, i.e. twice the
unsigned area; the factor of two is absorbed into `c`. Working in `ℝ × ℝ` with the
determinant keeps this elementary algebra rather than measure theory.

**Proved (PR #47) by the algebraic route.**  Bertrand supplies a prime `P ∈ (n, 2n]`; the
points are `(x, x² mod P)/P`.  Modulo `P` the determinant collapses to `(b-a)(c-a)(c-b)`,
non-zero because `ZMod P` is a field and the residues are distinct — so the *integer*
determinant is non-zero, hence at least 1 in absolute value, and twice-area is at least
`1/P² ≥ 1/(4n²)`.  `c = 1/4`.  No Pick's theorem and no analysis.  The record of both routes
is kept below because the comparison is the lesson.

**Two routes, and the book's is not the easier one.** The probabilistic proof needs the
annulus estimate `ℙ(area(pqr) ≤ ε) ≲ ε`, which is a genuine integral computation.
The algebraic construction in the same section — Erdős, via Roth 1951 — is far more
formalizable: take a prime `p`, the points `(x, x² mod p)` for `x ∈ [p]`, scaled into the
unit square. No three lie on a line (a parabola meets a line in at most two points over a
field), so by Pick's theorem every triangle has area at least `1/2` before scaling.
Mathlib has Bertrand's postulate (`Nat.exists_prime_lt_and_le_two_mul`) to get a prime
between `n` and `2n`, which is what makes the construction work for every `n` rather than
just for primes. Pick's theorem is **not** in Mathlib, but the weaker fact needed here — a
triangle with distinct integer vertices and non-zero determinant has twice-area at least 1
— is immediate from integrality of the determinant, and avoids Pick entirely.

## `girth_chromatic` — `exists_girth_gt_and_chromaticNumber_gt`

Theorem 3.4.1 (Erdős 1959): graphs of arbitrarily large girth and arbitrarily large
chromatic number exist, so high chromatic number cannot be certified from local structure.

The hardest node in the group, and the first that needs `G(n, p)`. The proof takes
`p = (log n)² / n`, bounds the expected number of short cycles by `o(n)`, uses Markov to
delete a vertex from each, and bounds the independence number by `3n / log n` to force
`χ ≥ |V| / α ≥ log n / 6`. Both `SimpleGraph.girth` (as `ℕ∞`) and
`SimpleGraph.chromaticNumber` (as `ℕ∞`) are Mathlib's; the chromatic bound
`χ(G) ≥ |V| / α(G)` may or may not be there and is worth stating separately if not.

Expect a reduction rather than a single PR.

## `property_b_sharp` — `exists_twoColorable_of_card_le`

Theorem 3.5.1 (Radhakrishnan–Srinivasan 2000): for some `c > 0`, every `k`-uniform
hypergraph with at most `c √(k / log k) 2^k` edges is 2-colourable — the best known lower
bound on `m k`, strengthening `twoColorable_of_card_lt` (Theorem 1.3.1, group
`introduction`).

Random greedy colouring: order the vertices by independent uniform points of `[0,1]`,
colour greedily blue-unless-forced, and split `[0,1] = L ∪ M ∪ R` to bound the chance of a
conflicting pair. The `∫ x^{k-1}(1-x)^{k-1} dx ≤ p 4^{-k+1}` estimate is the analytic
heart and has no Mathlib counterpart. Very hard; stated so the chapter's true frontier is
visible, not because it is expected to close soon.
