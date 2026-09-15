# Group: `containers` — Chapter 11

What the chapter establishes: the **container method**. A union bound over all independent sets
of a hypergraph is hopeless — for triangle-free graphs there are `2^(n²/8 + o(n²))` maximal ones
alone — but independent sets cluster, and the container theorems make that precise: there is a
small family of *containers*, each barely larger than a maximum independent set, that between
them cover every independent set. The union bound then runs over containers.

**Nothing here is in Mathlib**, and — unlike Chapters 7–10 — **the source does not prove the
main theorems.** Theorems 11.2.1 and 11.3.1 are given as an algorithm plus a proof idea, with
details deferred to Morris' 2016 lecture notes. These are research-level obligations and the
honest expectation is reductions, not single-PR proofs. The tasks say so explicitly and invite
decomposition proposals on the issue.

## Two decisions about how the statements are written

Both are recorded in the module docstring of `Containers.lean` as well, because they will recur
if anyone extends the chapter.

**Vertex sets are `Fin n`, not an arbitrary finite type.** Every theorem here has the shape "for
every `c` there is a `δ` that works for *all* graphs", so `δ` is chosen before the graph and
therefore before its vertex type. `∃ δ, ∀ {V : Type*} …` is not expressible — the universe
cannot be bound under the existential. `Fin n` costs no generality, since every finite graph is
isomorphic to one on `Fin n`, and it keeps the cardinality arithmetic in `ℕ`.

**Asymptotics are written out, never as `o(1)`.** `2^(n²/4 + o(n²))` becomes "for every `ε > 0`
there is an `N` such that for all `n ≥ N`, …". This is the idiom `exists_nearly_equiangular`
established in Chapter 5, and it is what the `≫` of Theorem 11.1.5 would need too.

Graphs are edge sets in `Finset (Sym2 (Fin n))`, as in Chapter 10, and `triangleEdges` is
imported from `Entropy.lean` rather than restated. `IsTriangleFreeEdgeSet` is an `abbrev` so
that `Decidable` resolution sees through it — **the project declares no `Decidable` instances**,
and making the predicate reducible means it does not have to.

## §11.2 Graph containers

- `graph_container` — Theorem 11.2.1. The foundation: everything else in the chapter is
  downstream. Marked high priority for that reason.
- `graph_container_fingerprint` — Theorem 11.2.3. The refinement the applications need: the
  container is `S I ∪ A (S I)` for an explicit fingerprint function, and **`A` depends only on
  `S I`**. That is what lets a union bound range over fingerprints, and it is what would push
  Theorem 11.1.5 from `p ≫ n^{-1/2} log n` down to `p ≫ n^{-1/2}`.

  **The dependency has been flipped, and the file reordered to match.** It was published in the
  book's order with 11.2.1 first, and a contributor working that task found the consequence:
  11.2.1 is a counting corollary of 11.2.3, so under the book's order it cannot be proved
  without a forward reference, which Lean does not have. They reported it and released the claim
  rather than duplicating 11.2.3's statement above the target — the right call, and the reason
  this was a five-minute fix instead of a near-duplicate in the file.

  `exists_containers_fingerprint` now precedes `exists_containers`, and `graph_container`
  depends on `graph_container_fingerprint` in the graph. **The lesson is general: publishing a
  chapter in the source's presentation order can encode a dependency backwards**, because a
  textbook is free to state a weaker result first and strengthen it later, and a Lean file is
  not. §11.1 has the same shape — 11.0.2 leans on 11.1.1 — and happens to be ordered correctly,
  but it is worth checking whenever a chapter is stated from a linear reading.

## §11.3 The hypergraph container theorem

- `hypergraph_container` — Theorem 11.3.1, Balogh–Morris–Samotij and Saxton–Thomason (2015).
  The hardest statement in the project. Its algorithm **calls** the graph container algorithm,
  so `graph_container` is a genuine dependency rather than an analogue, and the proof turns on a
  case split at termination: either many vertices have left, or the accumulated graph of
  forbidden pairs is dense enough and regular enough for the graph container lemma to apply.

`maxCodegree k H` is the `Δ_k(H)` of the section, defined in the file.

## §11.1 Containers for triangle-free graphs

- `container_triangle_free` — Theorem 11.1.1. Apply `hypergraph_container` to the hypergraph of
  triangles on the pairs from `[n]`. **One application is not enough**: it shrinks a container by
  a factor `1 - δ`, and the conclusion needs Mantel's bound up to `ε`, so the theorem has to be
  *iterated* (Remark 11.2.2) against a **supersaturation** input — every set of pairs much larger
  than `n²/4` spans many triangles. **Supersaturation for triangles is not in this repository and
  not in Mathlib.** The task tells the contributor to ask for it as its own task rather than bury
  it.
- `ekr_upper` — Theorem 11.0.2, upper half. Short given the containers: each of the
  `n^(C n^{3/2})` containers has at most `(1/4 + ε) n²` edges and hence `2^((1/4+ε)n²)`
  subgraphs, and `n^(C n^{3/2}) = 2^(o(n²))` absorbs the factor.
- `ekr_lower` — Theorem 11.0.2, lower half, and the half that fixes the constant `1/4`: the
  `2^(⌊n/2⌋⌈n/2⌉)` subgraphs of `K_{⌊n/2⌋,⌈n/2⌉}` are all triangle-free. A direct injection, no
  containers. Brute-forced for `n ≤ 4` before publishing: the bound reads `1, 1, 2, 4, 16`
  against actual counts `1, 1, 2, 7, 41`. `n = 0` and `n = 1` are not degenerate, so the
  statement carries no hypothesis on `n` and should not acquire one.

## Planned, not stated

- **Theorem 11.1.5 (Mantel in `G(n, p)`)**: for `p ≫ n^{-1/2}`, whp every triangle-free subgraph
  of `G(n, p)` has at most `(1/4 + o(1)) p n²` edges. Statable — it would combine
  `container_triangle_free` with the Chapter 5 Chernoff bound and the `binomialRandom` of
  Chapter 7 — but it needs a settled idiom for "whp" on top of the `ε`–`N` one, and the source
  proves only the weaker `p ≫ n^{-1/2} log n`. Revisit once something else in the project needs
  a whp idiom.
- **Theorem 11.1.2 (Erdős–Stone–Simonovits)** and **Theorem 11.1.3 (counting `H`-free graphs as
  `2^((1+o(1)) ex(n,H))`)**: both are quoted by the source rather than proved, and both need
  `ex(n, H)` as a definition, which the project does not have. Conjecture 11.1.4 is **open
  mathematics** and must not be stated as a theorem.
- **Triangle supersaturation**, the missing input to `container_triangle_free`. The most useful
  thing anyone could add to this group.
