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

**Came back as a reduction (PR #48), which is what was expected.** Two new nodes:

`card_le_mul_indepNum_of_colorable` — `|V| ≤ m * α(G)` for an `m`-colourable graph, the
`χ ≥ |V|/α` step in division-free form. Proved. Mathlib relates neither `chromaticNumber` nor
`Colorable` to `indepNum`, so this is ours.

`exists_girth_gt_and_mul_indepNum_lt` — the random-graph half: for every `l, m` a graph with
girth `> l` and `m * α < n`. Still open; this is the analytic heart of the chapter.

One property of the published statement, found in review: `SimpleGraph.girth` is `egirth.toNat`,
**`ℕ`-valued with junk value `0` on acyclic graphs**, so `(l : ℕ∞) < G.girth` also asserts the
graph has a cycle. That was not deliberate when the statement was authored. It is harmless —
a graph with `χ > k ≥ 1` cannot be acyclic — but any future statement mentioning `girth` should
account for it.

## The Erdős 1959 random-graph step

Reduced twice (PR #48, then PR #57).  What is proved: the alteration step
(`exists_girth_gt_and_indepNum_le_of_shortCycleCover` — delete `S`, keep the independence
number, gain girth), the union bound combining the two halves, and the packaging into the
published theorem.  What is open: the two probabilistic estimates, tasks #59 and #60.

**Two definitions came in with #57 and are now the project's to maintain**, since both open
statements mention them:

- `girthEdgeCount n = ⌈n (log n)²⌉₊` — the edge count, giving density `p ≈ 2 (log n)²/n`,
  twice the book's.  Still inside the window `log n / n ≪ p ≪ n^(-1+1/l)` the argument needs.
- `graphFamily n M = Finset.powersetCard M Finset.univ` over `Sym2 (Fin n)` — the uniform
  `M`-subset model, which keeps the whole argument a `Finset` count rather than a measure and
  so stays in Chapter 3's idiom.

**A wart in `graphFamily`, verified rather than assumed:** `univ : Finset (Sym2 (Fin n))`
includes the diagonal, so this samples `M` pairs from `n(n+1)/2` *including loops*, which
`fromEdgeSet` then discards.  It is not exactly `G(n, M)` — the realised edge count is `M`
minus about `2M/(n+1)` loops.  Harmless at `M ≈ n log² n`, and both open statements remain
true, but a prover must not assume exactly `M` edges.  If either estimate turns out to want a
cleaner model, changing these definitions is the centralized layer's job, not a contributor's.

### Three reusable lemmas from the expectation computation (PR #67)

- `sum_shortCycleSupport_card_le_cycleBound` — the double count: `∑_E #shortCycleSupport l E`
  is at most `∑_{i=3}^{l} i · nⁱ · C(N - i, M - i)`, since `C(N-i, M-i)` of the `M`-subsets
  contain `i` prescribed pairs.
- `choose_mul_pow_le_choose_add_mul_pow` — `C(a,b)·aⁱ ≤ C(a+i, b+i)·(b+i)ⁱ`.  This is the
  `G(n,M)`-to-`G(n,p)` bridge: it turns `C(N-i, M-i) / C(N,M)` into `(M/(N-i))ⁱ` **entirely in
  ℕ**, with no real division.  General-purpose; worth reaching for elsewhere.
- `exists_mul_pow_log_lt` — `c (log n)^k < n` eventually, from Mathlib's
  `Real.isLittleO_pow_log_id_atTop`.

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
