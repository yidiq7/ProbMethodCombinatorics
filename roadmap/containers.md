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
- **Triangle supersaturation**, the missing input to `container_triangle_free` — **and it is
  reachable from Mathlib**, contrary to what this file said until 2026-09-15. PR #146 found the
  route: `SimpleGraph.CliqueFree.card_edgeFinset_le` at `r = 2` is Mantel, which makes an
  over-dense graph `ε`-far from triangle-free via `SimpleGraph.farFromTriangleFree_iff`, and the
  triangle removal lemma `SimpleGraph.FarFromTriangleFree.le_card_cliqueFinset` then supplies the
  triangle count with `c = SimpleGraph.triangleRemovalBound ε`. So this is a transcription
  exercise, not new mathematics.


## The `d ≤ 2δn` proviso — and how three statements came to be false

`exists_containers_fingerprint` and `exists_containers` were published **false**, for every
`c ≥ 3/2`, and PR #143 inherited the defect into two further public statements before anyone
noticed. All are now fixed. The cause is worth stating exactly, because it is a transcription
failure of a kind that will recur.

**Zhao states the theorem and the proviso in different places.** Theorem 11.2.1 on printed
p. 206 carries no upper bound on `d`; the bound appears one page later, inside the proof idea:
*"at least `≥ d/2` new vertices are added to `X` (provided that `d ≤ 2δ|V|`)"*. I transcribed the
boxed theorem and not the parenthetical. **A textbook's theorem box is not always the whole
hypothesis list** — when a proof sketch introduces a side condition, check whether the statement
depends on it.

The two refuting families, which between them killed three statements this week and are now the
project's standard test pair for Chapter 11:

* **`Kₙ`** — `d = n - 1`, only `∅` and singletons independent. For `δ < 1/2` the budget
  `2δn/d < 1` forces every fingerprint empty, so one container must hold every vertex:
  `n ≤ (1-δ)n` fails. **Forces `δ ≥ 1/2`.**
* **`m` disjoint paths on three vertices** — `d = 4/3`, max degree `2 ≤ c·d` once `c ≥ 3/2`, and
  the `2m` leaves are independent of size `2n/3`. **Forces `δ ≤ 1/3`.**

`d ≤ 2δn` excludes the first and keeps the second, which is precisely its content: the
fingerprint budget is at least `1`, so a fingerprint can be nonempty at all.

**`exists_containers_three_uniform` needs no analogue** and did not acquire one: `3|H| ≤ 3·C(n,3)`
gives `d < n²/2`, so its budget `n/√d` always exceeds `√2`.

**`exists_containers` had already merged** as a declared reduction onto the fingerprint form, so
it was proved-modulo-a-false-lemma rather than unsound — the kernel was never deceived. Threading
the new hypothesis through its body was one extra binder.

## §11.2 is reduced: PR #166, and the three obligations it created

`exists_containers_fingerprint` (Theorem 11.2.3) is **proved** as of 2026-09-16, as a three-way
reduction merged in [PR #166](https://github.com/yidiq7/ProbMethodCombinatorics/pull/166).  The
parent's body is not glue-only: it chooses `δ := 1/(100 * max c 1)` (rather than `1/(100c)`, so
that `δ ≤ 1/100` holds even for `c < 1`, where `c ≥ 1` is only derivable once `n ≥ 1`), splits on
`d ≤ δn` versus `δn < d`, and repackages the dense corner's `(s, K)` into the `(S, A)` shape with
`I = ∅` handled separately.  The three obligations are nodes `exists_greedy_rule`,
`exists_fingerprint_of_greedy_rule` and `exists_dense_fingerprint`, all in `Containers.lean`,
all published as tasks.

**`IsGreedyRule` is orchestrator-owned vocabulary, and stays `private`.**  It is a `private def`
the contributor added, and it appears in the *statements* of two published tasks, which makes it
mine in substance even though a worker wrote it.  I have reviewed its four clauses and adopt them:
they are jointly satisfiable (decreasing `deg_{G[A]}` order, ties by index, `pick` = the
`≺`-least element, `kill A v = {u ∈ A | u ≺ v} ∪ (N(v) ∩ A)`), and they are *dimensioned to the
assembly* — the `2δn` threshold in the retirement clause is exactly what `|Aᶜ| = |X| + |S|`
reaches during the run.  `private` is right because both consumers live in this file (Lean 4
`private` is module-scoped) and §11.3 will need a *hypergraph* analogue rather than this
predicate, so making it public would freeze eight clauses of vocabulary nobody else reuses.
**Neither obligation's prover may edit it** — doing so changes both children's statements, and
`statement-immutability` will block it.

**Zhao's `d/2` retirement guarantee is not sufficient as stated**, and PR #166's author found why.
With a `d/2` guarantee, `(m-1)·(d/2) < δn` only gives `m < 1 + B` for `B = 2δn/d`, i.e. `m ≤ ⌈B⌉`,
not the `m ≤ B` the fingerprint budget needs.  Getting `m ≤ B` needs a guarantee of
`(d/2)·(B/⌊B⌋)`, which `B ≥ 2` caps at `3d/4` — and `3d/4` is available exactly because `d ≤ δn`
makes `cd` negligible against `n`.  **That is what forces the two-regime split**, and it is a
genuine correction to the source's proof sketch, not a formalization artifact.

## §11.2's dense corner is closed — it was never open

**Not to be confused with §11.3's dense corner**, `√d ≳ n` on task #99, which is a different
theorem and is still open (last paragraph of this file).  This section is about `δn < d ≤ 2δn` in
the *graph* container theorem.

**PR #166 flagged `exists_dense_fingerprint` as neither provable nor refutable, with an open
window of relative width `(c-1)δ` above `δn`, and asked that it not be published.  That was
wrong.**  The obligation is true, the proof is short, and the window is an artifact of one choice
in the construction.

The route, now recorded in the declaration's own docstring: the statement is equivalent to
producing an order in which every vertex has `|N(v) ∪ Pred(v)| ≥ δn`.  The window appears only if
the order is taken by **degree** — the sharpened count `dn ≤ t(cd + n - t)` is a bound on what the
largest-degree vertex can guarantee, and in the window a small high-degree set can leave the
chosen vertex one short.  Nothing forces that order.  Build it **greedily** instead: for every
`j < δn` and every `P` with `|P| = j` there is `v ∉ P` with `|N(v) \ P| ≥ δn - j`, since otherwise
summing degrees and bounding the `P`–`Pᶜ` edges twice from the `P` side gives
`n(d - δn) < j(2cd + j - n - δn)`, whose left side is positive by `δn < d` while `c ≥ 1` forces
`cd ≤ n/50` and hence the right side `≤ 0`.  Iterate for `j = 0 … ⌈δn⌉ - 1`.

**No lower bound on `d - δn` is used beyond positivity**, which is precisely why the width of the
supposed window is irrelevant.

The lesson is the mirror image of the `d ≤ 2δn` failure recorded below, and worth holding next to
it: **that one was a statement published false and believed true; this one was a statement
published true and believed false.**  Both came from reasoning about a particular construction
rather than about the statement.  When an obligation resists, ask whether what is stuck is the
*statement* or the *one construction tried so far* — the author had probed clique unions,
clique-plus-matching and Hi/Lo degree sequences for a counterexample and found none, which was
evidence the statement was true, not evidence the corner was hard.

## Stability is needed, and is now stated on the obligation

PR #143 established, in the course of reducing 11.3.1, that a two-phase fingerprint needs

    S I ⊆ J ⊆ I → S J = S I

for *both* phases, so that the composite `F = S I ∪ S' (S I) I` satisfies `S F = S I`. This is the
book's "two maximal independent sets with the same fingerprint produce the same partition" bullet,
which the book states for one phase only. **It is true of the greedy algorithm and free inside any
honest proof of it, but it cannot be recovered from the statement of 11.2.3**, whose `S` is an
arbitrary function. Raised on #98; if the proof there produces it, it should be stated rather than
re-derived.

**Done, 2026-09-16.** It is now a conjunct of `exists_fingerprint_of_greedy_rule`'s conclusion:

    ∀ J : Finset (Fin n), S I ⊆ J → J ⊆ I → S J = S I

I verified it is genuinely free from the `IsGreedyRule` interface before stating it, rather than
taking the reduction author's word: for `k < m` the pick `v_{k+1}` lies in `S I ⊆ J` and in `A_k`,
so `J ∩ A_k` is nonempty and the stability clause of `pick` (`T' ⊆ T` with `pick A T ∈ T'`) forces
the same choice; and if `I ∩ A_m = ∅` then `J ∩ A_m = ∅`, so the two runs halt together.  The
parent drops the conjunct at its one call site and still composes.

**It was stated now rather than when the obligation is discharged, which is the opposite of what
PR #166 proposed.**  The author suggested adding it once obligation 2 lands; that would be a
statement change to an already-published task, and `skills/orchestrator-notes.md` records what
that does — in-flight branches built on the older pin silently revert the statement, and
`statement-immutability` is the only thing that catches it.  **Author the interface before
publishing, not after.**  This project has paid for that lesson once already, in the duplicated
measure layer of #28–#30.

The open design question on **#99** is its own **dense corner**: `√d ≳ n`. Relaxing the sub-obligations'
budgets does not fix it, because the parent's own budget `⌊n/√d⌋₊` is only guaranteed `≥ 1`, so a
size-2 composite fingerprint does not fit. Either the assembly arithmetic changes or that corner
gets its own argument.
