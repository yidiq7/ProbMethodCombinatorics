# Group: `introduction` — Chapter 1

What the chapter establishes: the probabilistic method in its simplest form — build a
random object, compute one expectation or one union bound, conclude that a good object
exists.

## `cut_edges` — `ProbMethodCombinatorics.cutEdges`

The edges of `G` separated by a two-colouring `f : V → Bool`, defined as
`G.edgeFinset.filter fun e => Sym2.map f e = s(true, false)`.  An edge `s(u, v)` is
counted exactly when `f u ≠ f v`, and `Sym2.map` makes that decidable without a bespoke
instance.  These are the edges of the bipartite subgraph induced by `f`.

## `large_bipartite_subgraph` — `exists_cutEdges_two_mul_card_le`

Theorem 1.0.1.  Every graph with `m` edges has a bipartite subgraph with at least `m / 2`
edges; stated over ℕ as `G.edgeFinset.card ≤ 2 * (cutEdges G f).card` for some `f`.

The book colours each vertex independently; the formalized route is to average
`(cutEdges G f).card` over all `f : V → Bool` — every non-loop edge is cut by exactly
half of them — and take an `f` at least as good as the average.

## `is_monochromatic`, `ramsey_property`, `ramsey_number`

An edge colouring of `K n` is a symmetric `c : Fin n → Fin n → Bool`; its value on the
diagonal is never used.  `IsMonochromatic c S` says every edge inside `S` gets one colour.
`RamseyProperty n k` says every such colouring has a monochromatic `k`-clique, and
`ramseyNumber k = sInf {n | RamseyProperty n k}` is the diagonal Ramsey number `R(k, k)`.

Mathlib has no Ramsey numbers, so these definitions are the project's own interface.

## `ramsey_property_mono` — `RamseyProperty.mono`

If `m ≤ n` and every colouring of `K m` has a monochromatic `k`-clique, so does every
colouring of `K n`: restrict a colouring of `K n` along `Fin m ↪ Fin n` and push the
clique forward.  Needed to turn "no good colouring of `K n`" into a bound on the `sInf`.

## `ramsey_lower_erdos` — `exists_coloring_no_isMonochromatic`

Theorem 1.1.2 (Erdős 1947).  If `2 * (n.choose k) < 2 ^ (k.choose 2)` then some symmetric
colouring of `K n` has no monochromatic `k`-clique.  The hypothesis is the book's
`(n.choose k) · 2 ^ (1 - k.choose 2) < 1` with denominators cleared, which keeps the whole
statement in ℕ.

The union bound becomes a counting argument: over all `2 ^ (n.choose 2)` symmetric
colourings, each `k`-set is monochromatic in `2 ^ (1 + (n.choose 2) - (k.choose 2))` of
them, so fewer than all of them are spoiled by some `k`-set.

## `exists_monochromatic_of_choose_le` — Erdős–Szekeres

The off-diagonal statement the Ramsey induction needs, contributed with `ramsey_finite`
(PR #43): any `Finset` of at least `(k + l).choose k` vertices carries, under every symmetric
colouring, a `true`-clique on `k` vertices or a `false`-clique on `l`.

Two deliberate choices.  The vertex set is an arbitrary `Finset α` rather than `Fin n`, so the
inductive step — fix a vertex, recurse into the two colour classes of its neighbourhood —
stays inside the statement.  And the bound is `(k+l).choose k`, looser than the sharp
`(k+l-2).choose (k-1)`; the task asked for whatever falls out of a clean induction, and it
gives `R(k,k) ≤ (2k).choose k`, which is the classical Erdős–Szekeres diagonal bound.

## `ramsey_finite` — `exists_ramseyProperty`

Ramsey's theorem (Ramsey 1929), in the weakest form this project needs: `∃ n,
RamseyProperty n k`.

`ramseyNumber k` is `sInf {n | RamseyProperty n k}`, and `Nat.sInf ∅ = 0`, so without
finiteness the infimum is `0` and every lower bound on `R(k, k)` is false.  Mathlib has no
Ramsey theorem, so the obligation is ours.  Only existence is stated; the quantitative
Erdős–Szekeres bound `R(k+1, ℓ+1) ≤ (k+ℓ).choose k` (Remark 1.1.5) is a later refinement,
not a prerequisite.

## `lt_ramsey_number` — `lt_ramseyNumber`

Theorem 1.1.2 restated: the same hypothesis gives `n < ramseyNumber k`.  Immediate from
the previous three nodes — the colouring shows `¬ RamseyProperty n k`, monotonicity extends
that to every `m ≤ n`, and so the infimum exceeds `n`.

## `bollobas_two_families` — `bollobas_two_families`

Theorem 1.2.6 (Bollobás 1965).  For finite sets with `A i ∩ B i = ∅` and `A i ∩ B j ≠ ∅`
for `i ≠ j`,

    ∑ i, (|A i| + |B i|).choose |A i| ⁻¹ ≤ 1.

The book's proof takes a uniform random ordering of `⋃ (A i ∪ B i)` and observes that the
events "all of `A i` precedes all of `B i`" are disjoint.  Formalizing means counting
orderings, not sampling them.

Sperner, LYM and Erdős–Ko–Rado — the rest of §1.2 — are already in Mathlib and are
recorded as upstream nodes.

## `two_colorable`, `two_colorable_of_card_lt`

Theorem 1.3.1 (Erdős 1964).  `TwoColorable H` says the vertices can be two-coloured with
no edge of `H` monochromatic (property B).  Every `k`-uniform hypergraph with fewer than
`2 ^ (k - 1)` edges is 2-colourable, i.e. `m k ≥ 2 ^ (k - 1)`.

Again a counting union bound: of the `2 ^ |α|` colourings, each edge is monochromatic
under `2 ^ (|α| - k + 1)` of them, and `|H| < 2 ^ (k - 1)` makes the spoiled colourings a
strict minority.

§1.4 (list chromatic number of `K n n`) is not yet stated.
