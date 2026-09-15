import ProbMethodCombinatorics.Entropy
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Chapter 11: Containers

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Chapter 11.

The container method replaces a hopeless union bound over all independent sets of a hypergraph
with an efficient one over a small family of **containers**: sets that are not much larger than a
maximum independent set, few in number, and between them covering every independent set.

**Nothing in this chapter is in Mathlib**, and unlike Chapters 7–10 the source does not supply
complete proofs: Theorems 11.2.1 and 11.3.1 are given as algorithms plus a proof *idea*, with the
details delegated to Morris' lecture notes. So the obligations here are genuinely research-level,
and the honest expectation is reductions rather than single-PR proofs.

## Two decisions about how the statements are written

**Vertex sets are `Fin n`, not an arbitrary finite type.** Every theorem in the chapter has the
shape "for every `c` there is a `δ` that works for *all* graphs", so the `δ` must be chosen before
the graph — and hence before its vertex type. Quantifying over a universe-polymorphic `V` inside
an `∃ δ` is not expressible; `Fin n` costs no generality, since every finite graph is isomorphic
to one on `Fin n`, and keeps the cardinality arithmetic in `ℕ` where it belongs.

**Asymptotics are written out, never as `o(1)`.** `2^(n²/4 + o(n²))` becomes "for every `ε > 0`
there is an `N` such that for all `n ≥ N`, …", the idiom already used by
`exists_nearly_equiangular` in Chapter 5. The `≫` of Theorem 11.1.5 would need the same
treatment.

Graphs are recorded as edge sets in `Finset (Sym2 (Fin n))`, as in Chapter 10's
`card_lt_of_triangleIntersecting`, and `triangleEdges` is imported from `Entropy.lean` rather
than restated.
-/

namespace ProbMethodCombinatorics

open Finset

/-- A set of unordered pairs is the edge set of a triangle-free simple graph: no pair is
degenerate, and no three vertices have all three of their pairs present.

An `abbrev` rather than a `def` so that `Decidable` resolution sees through it: the project does
not declare `Decidable` instances, and the predicate is decidable componentwise. -/
abbrev IsTriangleFreeEdgeSet {n : ℕ} (G : Finset (Sym2 (Fin n))) : Prop :=
  (∀ e ∈ G, ¬ e.IsDiag) ∧ ∀ a b c : Fin n, ¬ triangleEdges a b c ⊆ G

/-- `maxCodegree k H` is `Δ_k(H)` of §11.3: the largest number of edges of the hypergraph `H`
containing a fixed set of `k` vertices. -/
def maxCodegree {α : Type*} [Fintype α] [DecidableEq α] (k : ℕ) (H : Finset (Finset α)) : ℕ :=
  (univ.filter fun A : Finset α => A.card = k).sup fun A => (H.filter fun e => A ⊆ e).card

/-- The `n`-vertex triangle-free graphs, as a finset of edge sets. -/
noncomputable def triangleFreeGraphs (n : ℕ) : Finset (Finset (Sym2 (Fin n))) :=
  univ.filter IsTriangleFreeEdgeSet

/-! ### 11.2 Graph containers -/

/-- The interface the greedy step of the container algorithm is asked to satisfy on a graph `G`
of average degree `d`, with shrinking parameter `δ`.

`pick A T` is the vertex selected out of a candidate set `T` while `A` is the set of still-alive
vertices, and `kill A v` is the set of vertices retired from `A` when `v` is selected.

* `pick A T ∈ T` for nonempty `T`, and `pick A` is **stable**: shrinking `T` to a subset that still
  contains the selected vertex does not change the selection.  This is what lets the run be
  replayed from the fingerprint alone, because the fingerprint records exactly the vertices that
  are still to be selected.
* `kill A v ⊆ A` and `v ∉ kill A v`, so the selected vertex is retired separately from the
  vertices its selection retires.
* As long as fewer than `2 * δ * n` vertices have been retired, selecting from an independent set
  `I` retires at least `3 * d / 4` vertices, none of them in `I`. -/
private def IsGreedyRule {n : ℕ} (G : SimpleGraph (Fin n)) (d δ : ℝ)
    (pick : Finset (Fin n) → Finset (Fin n) → Fin n)
    (kill : Finset (Fin n) → Fin n → Finset (Fin n)) : Prop :=
  (∀ A T : Finset (Fin n), T.Nonempty → pick A T ∈ T) ∧
  (∀ A T T' : Finset (Fin n), T' ⊆ T → pick A T ∈ T' → pick A T' = pick A T) ∧
  (∀ (A : Finset (Fin n)) (v : Fin n), kill A v ⊆ A ∧ v ∉ kill A v) ∧
  (∀ A : Finset (Fin n), ((Aᶜ).card : ℝ) ≤ 2 * δ * n →
    ∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) → (I ∩ A).Nonempty →
      Disjoint (kill A (pick A (I ∩ A))) I ∧
      3 * d / 4 ≤ ((kill A (pick A (I ∩ A))).card : ℝ))

/-- **The greedy step of the container algorithm** (Zhao, the algorithm on printed p. 206).  On a
graph whose average degree `d` is small compared with `δ * n`, selecting from the alive set `A`
the vertex of `I ∩ A` that comes first in the order of decreasing degree in `G[A]` retires at
least `3 * d / 4` vertices of `A` outside `I`: its predecessors in that order, which cannot lie
in `I`, together with its neighbours, which cannot lie in `I` either.

The count is the degree count of the proof idea.  Writing `v` for the selected vertex, `P` for
its predecessors and `t` for the number of vertices retired, every vertex of `A` outside
`P ∪ {v}` has degree in `G[A]` at most that of `v`, so

    d * n - 4 * c * d * (δ * n) ≤ ∑ u ∈ A, degree_{G[A]} u ≤ t * (c * d) + n * t,

and `d ≤ δ * n` with `δ ≤ 1 / (100 * c)` turns this into `t ≥ 0.9 * d`.  It is the hypothesis
`d ≤ δ * n` that makes `c * d` negligible against `n`; Zhao's `d / 2` is what the same count
gives without it. -/
theorem exists_greedy_rule (c d δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) (hδc : δ ≤ 1 / (100 * c))
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hd : 0 < d) (hdn : d ≤ δ * n)
    (hsum : (∑ v, (G.degree v : ℝ)) = d * n) (hdeg : ∀ v, (G.degree v : ℝ) ≤ c * d) :
    ∃ (pick : Finset (Fin n) → Finset (Fin n) → Fin n)
      (kill : Finset (Fin n) → Fin n → Finset (Fin n)), IsGreedyRule G d δ pick kill := by
  sorry

/-- **The container algorithm assembled from its greedy step.**  Running a greedy rule from the
alive set `Finset.univ` and the empty fingerprint produces the fingerprint function `S` and the
container function `A` of Theorem 11.2.3 in the regime `d ≤ δ * n`.

The run selects vertices `v₁, …, v_m` out of `I`, retiring `kill` sets into a set `X` of retired
vertices, and stops when either `δ * n` vertices have been retired or nothing of `I` is left
alive.  Three facts make it work.

* `X` never meets `I`, so `I ⊆ S ∪ A` with `S = {v₁, …, v_m}` the vertices selected and `A` the
  alive set at the halt: the selected vertex is first in `I ∩ A`, so its predecessors miss `I`,
  and its neighbours miss `I` by independence.
* **`A` is recovered from `S` alone.**  Replaying the run with `I` replaced by the *set* `S`
  selects the same vertices, because at step `k` the fingerprint restricted to the alive set is
  `{v_{k+1}, …, v_m} ⊆ I ∩ A_k` and still contains `v_{k+1}`, so stability of `pick` gives the
  same selection.  Halting for want of alive vertices is also visible from `S`, and there `I` is
  forced to equal `S`, which is what makes `A := ∅` consistent on that branch.
* The budget.  Each of the first `m - 1` steps retires at least `3 * d / 4` vertices while fewer
  than `δ * n` are retired, so `m - 1 < 4 * δ * n / (3 * d) = (2 / 3) * (2 * δ * n / d)`, and
  `d ≤ δ * n` makes `2 * δ * n / d ≥ 2`, which is exactly enough for the integer `m` to satisfy
  `m ≤ 2 * δ * n / d`.  On the branch that halts for want of alive vertices the container is `S`
  itself, and `∑ v, degree v = d * n` with `degree ≤ c * d` bounds every independent set by
  `(1 - 1 / (2 * c)) * n ≤ (1 - δ) * n`. -/
theorem exists_fingerprint_of_greedy_rule (c d δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (hδc : δ ≤ 1 / (100 * c)) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hd : 0 < d) (hdn : d ≤ δ * n) (hsum : (∑ v, (G.degree v : ℝ)) = d * n)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ c * d)
    (pick : Finset (Fin n) → Finset (Fin n) → Fin n)
    (kill : Finset (Fin n) → Fin n → Finset (Fin n)) (hrule : IsGreedyRule G d δ pick kill) :
    ∃ S A : Finset (Fin n) → Finset (Fin n),
      ∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) →
        S I ⊆ I ∧ I ⊆ S I ∪ A (S I) ∧
        ((S I).card : ℝ) ≤ 2 * δ * n / d ∧
        ((S I ∪ A (S I)).card : ℝ) ≤ (1 - δ) * n := by
  sorry

/-- **Containers from a single-vertex fingerprint, in the dense corner `δ * n < d`.**  When the
average degree exceeds `δ * n` the fingerprint budget `2 * δ * n / d` of Theorem 11.2.3 is below
`2`, so a fingerprint may hold at most one vertex, and the conclusion takes the form: a selection
`s I ∈ I` and a set `K v` depending only on the selected vertex, with `I ⊆ insert (s I) (K (s I))`
and that container missing at least `δ * n` vertices.

Selecting from `I` the vertex `v` of largest degree (ties by index) and taking
`K v = (V \ ({u | v ≺ u} ∪ N(v)))` works whenever the count

    d * n ≤ |{u | u ≺ v}| * (c * d) + n * (G.degree v)

forces `|{u | u ≺ v} ∪ N(v)| ≥ δ * n`, which it does for `d ≥ δ * n * (1 + 2 * c * δ)`.  Between
`δ * n` and that, the count is short of `δ * n` by a second-order amount and the corner needs its
own argument; `d ≤ 2 * δ * n` is what keeps the budget at least `1`, so that a one-vertex
fingerprint is permitted at all. -/
theorem exists_dense_fingerprint (c d δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) (hδc : δ ≤ 1 / (100 * c))
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hd : 0 < d) (hlo : δ * n < d)
    (hhi : d ≤ 2 * δ * n) (hsum : (∑ v, (G.degree v : ℝ)) = d * n)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ c * d) :
    ∃ (s : Finset (Fin n) → Fin n) (K : Fin n → Finset (Fin n)),
      ∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) → I.Nonempty →
        s I ∈ I ∧ I ⊆ insert (s I) (K (s I)) ∧
        ((insert (s I) (K (s I))).card : ℝ) ≤ (1 - δ) * n := by
  sorry

/-- **The graph container theorem, with fingerprints** (Zhao, Theorem 11.2.3).  The refinement of
Theorem 11.2.1 that the applications actually need, and — despite the numbering — **the
statement the container algorithm actually produces.**  The container assigned to an independent
set `I` is not merely *some* member of a small family, but `S I ∪ A (S I)`, a function of a
fingerprint `S I ⊆ I`.  That `A` depends only on `S I` — and not otherwise on `I` — is the whole
content; it is what lets a union bound range over fingerprints.

It is stated **before** `exists_containers` because that is the direction the dependency runs:
11.2.1 is a counting corollary of this, obtained by taking `𝒞` to be the image of `A ∘ S` over
the small fingerprints.  The file originally had them in the book's order, which made the
corollary unprovable without a forward reference; a contributor working 11.2.1 found that and
reported it rather than duplicating the statement.

**`d ≤ 2 * δ * n` is load-bearing and was missing.**  It is Zhao's own proviso — stated on
printed p. 207 inside the proof idea ("provided that `d ≤ 2δ|V|`") and omitted from the theorem —
and without it the statement is **false** for every `c ≥ 3/2`.  Two instances refute it together:

* `G = Kₙ`, where `d = n - 1` and the only independent sets are `∅` and singletons.  If
  `δ < 1/2` then `2δn/d < 1`, so every fingerprint is forced empty, so the single container
  `A ∅` must contain every vertex and `n ≤ (1 - δ) n` fails.  Hence `δ ≥ 1/2`.
* `G` a disjoint union of `m` paths on three vertices, where `d = 4/3`, the maximum degree is
  `2 ≤ c d`, and the `2m` leaves are independent of size `2n/3`.  Any container holding them
  needs `(1 - δ) n ≥ 2n/3`.  Hence `δ ≤ 1/3`.

The hypothesis excludes the first family (`n - 1 ≤ 2δn` fails for `δ < 1/2`) while keeping the
second (`4/3 ≤ 2δn` for `n` large), which is exactly its role: it says the fingerprint budget
`2δn/d` is at least `1`, so that a fingerprint can be nonempty at all. -/
theorem exists_containers_fingerprint (c : ℝ) (hc : 0 < c) :
    ∃ δ > 0, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (d : ℝ), 0 < d →
      d ≤ 2 * δ * n →
      (∑ v, (G.degree v : ℝ)) = d * n → (∀ v, (G.degree v : ℝ) ≤ c * d) →
      ∃ S A : Finset (Fin n) → Finset (Fin n),
        ∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) →
          S I ⊆ I ∧ I ⊆ S I ∪ A (S I) ∧
          ((S I).card : ℝ) ≤ 2 * δ * n / d ∧
          ((S I ∪ A (S I)).card : ℝ) ≤ (1 - δ) * n := by
  have hm1 : (1 : ℝ) ≤ max c 1 := le_max_right _ _
  have hmc : c ≤ max c 1 := le_max_left _ _
  have hmpos : (0 : ℝ) < 100 * max c 1 := by linarith
  refine ⟨1 / (100 * max c 1), by positivity, fun n G _ d hd hdn hsum hdeg => ?_⟩
  set δ : ℝ := 1 / (100 * max c 1) with hδdef
  have hδ : (0 : ℝ) < δ := by rw [hδdef]; positivity
  have hδc : δ ≤ 1 / (100 * c) := by
    rw [hδdef]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hδ1 : δ ≤ 1 / 100 := by
    rw [hδdef]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  by_cases hcase : d ≤ δ * n
  · obtain ⟨pick, kill, hrule⟩ := exists_greedy_rule c d δ hc hδ hδc n G hd hcase hsum hdeg
    exact exists_fingerprint_of_greedy_rule c d δ hc hδ hδc n G hd hcase hsum hdeg pick kill hrule
  · obtain ⟨s, K, hsK⟩ :=
      exists_dense_fingerprint c d δ hc hδ hδc n G hd (lt_of_not_ge hcase) hdn hsum hdeg
    refine ⟨fun I => if I = ∅ then ∅ else {s I}, fun T => T.biUnion K, fun I hI => ?_⟩
    by_cases hIe : I = ∅
    · subst hIe
      have hn : (0 : ℝ) ≤ (n : ℕ) := Nat.cast_nonneg n
      simp only [reduceIte, Finset.biUnion_empty, Finset.union_empty, Finset.card_empty,
        Nat.cast_zero, Finset.Subset.refl, true_and]
      exact ⟨by positivity, mul_nonneg (by linarith) hn⟩
    · have hne : I.Nonempty := Finset.nonempty_iff_ne_empty.mpr hIe
      obtain ⟨hsI, hcov, hcard⟩ := hsK I hI hne
      simp only [if_neg hIe, Finset.singleton_biUnion, Finset.singleton_union]
      refine ⟨Finset.singleton_subset_iff.mpr hsI, hcov, ?_, hcard⟩
      rw [Finset.card_singleton, Nat.cast_one, le_div_iff₀ hd]
      linarith

/-- **The graph container theorem** (Zhao, Theorem 11.2.1).  In a graph whose maximum degree is
within a constant factor of its average degree `d`, the independent sets are covered by a family
of containers indexed by "fingerprints" of size `≤ 2δ|V|/d`, each container missing at least a
`δ` fraction of the vertices.

The bound on `|𝒞|` is the book's `binom(|V|, ≤ 2δ|V|/d)`, written as the partial sum of binomial
coefficients it abbreviates.

**A corollary of `exists_containers_fingerprint` above**, not an independent theorem: take `𝒞`
to be the image of `T ↦ T ∪ A T` over the fingerprints `T` small enough and with `T ∪ A T` small
enough.  The second condition is load-bearing — without it the fingerprint theorem says nothing
about a `T` that is not some `S I`.

Carries the same `d ≤ 2 * δ * n` proviso as `exists_containers_fingerprint`, and for the same
reason — see the counterexamples in that docstring. -/
theorem exists_containers (c : ℝ) (hc : 0 < c) :
    ∃ δ > 0, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (d : ℝ), 0 < d →
      d ≤ 2 * δ * n →
      (∑ v, (G.degree v : ℝ)) = d * n → (∀ v, (G.degree v : ℝ) ≤ c * d) →
      ∃ 𝒞 : Finset (Finset (Fin n)),
        (𝒞.card : ℝ) ≤ ∑ i ∈ range (⌊2 * δ * n / d⌋₊ + 1), (n.choose i : ℝ) ∧
        (∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) → ∃ C ∈ 𝒞, I ⊆ C) ∧
        (∀ C ∈ 𝒞, (C.card : ℝ) ≤ (1 - δ) * n) := by
  obtain ⟨δ, hδ, hfp⟩ := exists_containers_fingerprint c hc
  refine ⟨δ, hδ, fun n G _ d hd hdn hsum hdeg => ?_⟩
  obtain ⟨S, A, hSA⟩ := hfp n G d hd hdn hsum hdeg
  -- The fingerprints that are both small and have a small container.  The second condition is
  -- needed because the fingerprint theorem says nothing about a `T` that is not some `S I`.
  set F : Finset (Finset (Fin n)) :=
    univ.powerset.filter fun T : Finset (Fin n) =>
      (T.card : ℝ) ≤ 2 * δ * n / d ∧ ((T ∪ A T).card : ℝ) ≤ (1 - δ) * n with hF
  refine ⟨F.image fun T => T ∪ A T, ?_, ?_, ?_⟩
  · have hsub : F ⊆ (range (⌊2 * δ * n / d⌋₊ + 1)).biUnion
        fun i => powersetCard i (univ : Finset (Fin n)) := by
      intro T hT
      rw [hF, mem_filter] at hT
      exact mem_biUnion.mpr ⟨T.card, mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hT.2.1)),
        mem_powersetCard.mpr ⟨subset_univ _, rfl⟩⟩
    have hcount : ((range (⌊2 * δ * n / d⌋₊ + 1)).biUnion
        fun i => powersetCard i (univ : Finset (Fin n))).card
        = ∑ i ∈ range (⌊2 * δ * n / d⌋₊ + 1), n.choose i := by
      rw [card_biUnion ((pairwise_disjoint_powersetCard (univ : Finset (Fin n))).set_pairwise _)]
      simp
    have hnat : (F.image fun T => T ∪ A T).card
        ≤ ∑ i ∈ range (⌊2 * δ * n / d⌋₊ + 1), n.choose i :=
      card_image_le.trans (hcount ▸ card_le_card hsub)
    calc ((F.image fun T => T ∪ A T).card : ℝ)
        ≤ ((∑ i ∈ range (⌊2 * δ * n / d⌋₊ + 1), n.choose i : ℕ) : ℝ) := Nat.cast_le.mpr hnat
      _ = ∑ i ∈ range (⌊2 * δ * n / d⌋₊ + 1), (n.choose i : ℝ) := by push_cast; ring
  · intro I hI
    obtain ⟨-, hcov, hsmall, hcont⟩ := hSA I hI
    exact ⟨S I ∪ A (S I), mem_image_of_mem _
      (mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), hsmall, hcont⟩), hcov⟩
  · intro C hC
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hC
    exact (mem_filter.mp hT).2.2

/-! ### 11.3 The hypergraph container theorem -/

/-- **The container theorem for 3-uniform hypergraphs** (Zhao, Theorem 11.3.1; Balogh–Morris–
Samotij and Saxton–Thomason, independently, 2015).  The degree conditions are on `Δ₁ ≤ cd` and
`Δ₂ ≤ c√d`, and the fingerprints now have size `≤ v(H)/√d`.

The source's proof calls the graph container algorithm as a subroutine, so `exists_containers` is
a genuine dependency rather than merely an analogue. -/
theorem exists_containers_three_uniform (c : ℝ) (hc : 0 < c) :
    ∃ δ > 0, ∀ (n : ℕ) (H : Finset (Finset (Fin n))) (d : ℝ),
      (∀ e ∈ H, e.card = 3) → δ⁻¹ ≤ d → 3 * (H.card : ℝ) = d * n →
      (maxCodegree 1 H : ℝ) ≤ c * d → (maxCodegree 2 H : ℝ) ≤ c * Real.sqrt d →
      ∃ 𝒞 : Finset (Finset (Fin n)),
        (𝒞.card : ℝ) ≤ ∑ i ∈ range (⌊(n : ℝ) / Real.sqrt d⌋₊ + 1), (n.choose i : ℝ) ∧
        (∀ I : Finset (Fin n), (∀ e ∈ H, ¬ e ⊆ I) → ∃ C ∈ 𝒞, I ⊆ C) ∧
        (∀ C ∈ 𝒞, (C.card : ℝ) ≤ (1 - δ) * n) := by
  sorry

/-! ### 11.1 Containers for triangle-free graphs -/

/-- **Containers for triangle-free graphs** (Zhao, Theorem 11.1.1).  Every triangle-free graph on
`n` vertices sits inside one of at most `n ^ (C n^{3/2})` graphs, each with at most
`(1/4 + ε) n²` edges — Mantel's bound, up to `ε`.

Obtained from `exists_containers_three_uniform` applied to the hypergraph whose vertices are the
pairs from `[n]` and whose edges are the triangles, then iterated: one application only shrinks a
container by a factor `1 - δ`, so the theorem's near-optimal `1/4 + ε` needs the iteration of
Remark 11.2.2 together with a supersaturation input. -/
theorem exists_containers_triangleFree (ε : ℝ) (hε : 0 < ε) :
    ∃ C > 0, ∀ n : ℕ, ∃ 𝒞 : Finset (Finset (Sym2 (Fin n))),
      (𝒞.card : ℝ) ≤ (n : ℝ) ^ (C * (n : ℝ) ^ ((3 : ℝ) / 2)) ∧
      (∀ F ∈ 𝒞, (F.card : ℝ) ≤ (1 / 4 + ε) * (n : ℝ) ^ 2) ∧
      (∀ G ∈ triangleFreeGraphs n, ∃ F ∈ 𝒞, G ⊆ F) := by
  sorry

/-- **Erdős–Kleitman–Rothschild** (Zhao, Theorem 11.0.2), upper bound: there are at most
`2 ^ ((1/4 + ε) n²)` triangle-free graphs on `n` vertices, for every `ε > 0` and `n` large.

Together with `le_card_triangleFreeGraphs` this is the asymptotic `2^(n²/4 + o(n²))`.  The union
bound is over the containers: each of the `n^(C n^{3/2})` of them has at most `(1/4 + ε) n²`
edges and so at most `2^((1/4+ε)n²)` subgraphs, and `n^(C n^{3/2}) = 2^(o(n²))` absorbs the
factor. -/
theorem card_triangleFreeGraphs_le (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N,
      ((triangleFreeGraphs n).card : ℝ) ≤ (2 : ℝ) ^ ((1 / 4 + ε) * (n : ℝ) ^ 2) := by
  obtain ⟨C, hC, hcont⟩ := exists_containers_triangleFree (ε / 2) (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hscale : 0 < Real.log 2 * (ε / 2) := mul_pos hlog2 (by linarith)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 4 * C / (Real.log 2 * (ε / 2)) := ⟨_, rfl⟩
  have hK : 0 < K := hKdef ▸ div_pos (by linarith) hscale
  have hLK : Real.log 2 * (ε / 2) * K = 4 * C := by
    rw [hKdef]
    field_simp
  refine ⟨⌈K ^ 4⌉₊ + 1, fun n hn => ?_⟩
  obtain ⟨𝒞, hcard, hsize, hcover⟩ := hcont n
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have h : 1 ≤ n := le_trans (Nat.le_add_left 1 _) hn
    exact_mod_cast h
  have hpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  have h32 : (0 : ℝ) < (n : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hpos _
  have h14 : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hpos _
  have h74 : (0 : ℝ) < (n : ℝ) ^ ((7 : ℝ) / 4) := Real.rpow_pos_of_pos hpos _
  have e1 : (n : ℝ) ^ ((3 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 4) = (n : ℝ) ^ ((7 : ℝ) / 4) := by
    rw [← Real.rpow_add hpos]
    norm_num
  have e2 : (n : ℝ) ^ ((7 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4) = (n : ℝ) ^ 2 := by
    rw [← Real.rpow_add hpos, ← Real.rpow_natCast (n : ℝ) 2]
    norm_num
  -- `log t ≤ t - 1` applied at `t = n ^ (1/4)` gives `log n ≤ 4 n ^ (1/4)`.
  have hlogn : Real.log (n : ℝ) ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
    have h := Real.log_le_sub_one_of_pos h14
    rw [Real.log_rpow hpos] at h
    linarith
  have hKn : K ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := by
    have hce : K ^ 4 ≤ (n : ℝ) := by
      refine le_trans (Nat.le_ceil _) ?_
      have h : (⌈K ^ 4⌉₊ : ℕ) ≤ n := le_trans (Nat.le_add_right _ 1) hn
      exact_mod_cast h
    have hrw : K = (K ^ 4) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_natCast K 4, ← Real.rpow_mul hK.le]
      norm_num
    rw [hrw]
    exact Real.rpow_le_rpow (by positivity) hce (by norm_num)
  -- The container count `n ^ (C n ^ (3/2))` is at most `2 ^ ((ε/2) n²)`.
  have hanal : (n : ℝ) ^ (C * (n : ℝ) ^ ((3 : ℝ) / 2)) ≤ (2 : ℝ) ^ (ε / 2 * (n : ℝ) ^ 2) := by
    have hCm : (0 : ℝ) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2) := mul_nonneg hC.le h32.le
    have hineq : Real.log (n : ℝ) * (C * (n : ℝ) ^ ((3 : ℝ) / 2))
        ≤ Real.log 2 * (ε / 2 * (n : ℝ) ^ 2) := by
      calc Real.log (n : ℝ) * (C * (n : ℝ) ^ ((3 : ℝ) / 2))
          ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 4) * (C * (n : ℝ) ^ ((3 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_right hlogn hCm
        _ = 4 * C * ((n : ℝ) ^ ((3 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 4)) := by ring
        _ = Real.log 2 * (ε / 2) * K * (n : ℝ) ^ ((7 : ℝ) / 4) := by rw [hLK, e1]
        _ ≤ Real.log 2 * (ε / 2) * (n : ℝ) ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((7 : ℝ) / 4) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hKn hscale.le) h74.le
        _ = Real.log 2 * (ε / 2 * ((n : ℝ) ^ ((7 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4))) := by
            ring
        _ = Real.log 2 * (ε / 2 * (n : ℝ) ^ 2) := by rw [e2]
    have hl : (n : ℝ) ^ (C * (n : ℝ) ^ ((3 : ℝ) / 2))
        = Real.exp (Real.log (n : ℝ) * (C * (n : ℝ) ^ ((3 : ℝ) / 2))) :=
      Real.rpow_def_of_pos hpos _
    have hr : (2 : ℝ) ^ (ε / 2 * (n : ℝ) ^ 2)
        = Real.exp (Real.log 2 * (ε / 2 * (n : ℝ) ^ 2)) :=
      Real.rpow_def_of_pos (by norm_num) _
    rw [hl, hr]
    exact Real.exp_le_exp.mpr hineq
  -- Every triangle-free graph is a subgraph of a container, and a container with `m` edges has
  -- `2 ^ m` subgraphs.
  have hsub : triangleFreeGraphs n ⊆ 𝒞.biUnion fun F => F.powerset := by
    intro G hG
    obtain ⟨F, hF, hGF⟩ := hcover G hG
    exact Finset.mem_biUnion.mpr ⟨F, hF, Finset.mem_powerset.mpr hGF⟩
  have hnat : (triangleFreeGraphs n).card ≤ ∑ F ∈ 𝒞, 2 ^ F.card :=
    calc (triangleFreeGraphs n).card ≤ (𝒞.biUnion fun F => F.powerset).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ F ∈ 𝒞, F.powerset.card := Finset.card_biUnion_le
      _ = ∑ F ∈ 𝒞, 2 ^ F.card := by simp [Finset.card_powerset]
  have hterm : ∀ F ∈ 𝒞, (2 : ℝ) ^ F.card ≤ (2 : ℝ) ^ ((1 / 4 + ε / 2) * (n : ℝ) ^ 2) := by
    intro F hF
    rw [← Real.rpow_natCast (2 : ℝ) F.card]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two (hsize F hF)
  calc ((triangleFreeGraphs n).card : ℝ)
      ≤ ((∑ F ∈ 𝒞, 2 ^ F.card : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = ∑ F ∈ 𝒞, (2 : ℝ) ^ F.card := by push_cast; ring
    _ ≤ 𝒞.card • (2 : ℝ) ^ ((1 / 4 + ε / 2) * (n : ℝ) ^ 2) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = (𝒞.card : ℝ) * (2 : ℝ) ^ ((1 / 4 + ε / 2) * (n : ℝ) ^ 2) := by
        rw [nsmul_eq_mul]
    _ ≤ (n : ℝ) ^ (C * (n : ℝ) ^ ((3 : ℝ) / 2)) * (2 : ℝ) ^ ((1 / 4 + ε / 2) * (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg (by norm_num) _)
    _ ≤ (2 : ℝ) ^ (ε / 2 * (n : ℝ) ^ 2) * (2 : ℝ) ^ ((1 / 4 + ε / 2) * (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hanal (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ ((1 / 4 + ε) * (n : ℝ) ^ 2) := by
        rw [← Real.rpow_add (by norm_num)]
        ring_nf

/-- **Erdős–Kleitman–Rothschild**, lower bound: every subgraph of the complete bipartite graph
`K_{⌊n/2⌋, ⌈n/2⌉}` is triangle-free, and there are `2 ^ (⌊n/2⌋⌈n/2⌉)` of them.

The easy half, and the one that fixes the constant `1/4`.  No containers involved. -/
theorem le_card_triangleFreeGraphs (n : ℕ) :
    2 ^ (n / 2 * ((n + 1) / 2)) ≤ (triangleFreeGraphs n).card := by
  set L : Finset (Fin n) := univ.map (Fin.castLEEmb (Nat.div_le_self n 2)) with hLdef
  set f : Fin n × Fin n → Sym2 (Fin n) := fun p => s(p.1, p.2) with hfdef
  have hLcard : L.card = n / 2 := by simp [hLdef]
  have hLccard : Lᶜ.card = (n + 1) / 2 := by
    have h : Lᶜ.card = n - n / 2 := by rw [Finset.card_compl, hLcard, Fintype.card_fin]
    omega
  have hsides : ∀ F : Finset (Fin n × Fin n), F ⊆ L ×ˢ Lᶜ → ∀ x y : Fin n,
      s(x, y) ∈ F.image f → (x ∈ L ↔ y ∉ L) := by
    intro F hF x y hxy
    obtain ⟨⟨a, b⟩, hab, hE⟩ := Finset.mem_image.mp hxy
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp (hF hab)
    rw [Finset.mem_compl] at hb
    rcases Sym2.eq_iff.mp hE with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [ha, hb]
    · simp [ha, hb]
  have hmaps : ∀ F ∈ (L ×ˢ Lᶜ).powerset, F.image f ∈ triangleFreeGraphs n := by
    intro F hF
    rw [Finset.mem_powerset] at hF
    rw [triangleFreeGraphs, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro e he
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp (hF hab)
      rw [Finset.mem_compl] at hb
      simp only [hfdef, Sym2.mk_isDiag_iff]
      rintro rfl
      exact hb ha
    · intro a b c hsub
      have hab := hsides F hF a b (hsub (by simp [triangleEdges]))
      have hac := hsides F hF a c (hsub (by simp [triangleEdges]))
      have hbc := hsides F hF b c (hsub (by simp [triangleEdges]))
      tauto
  have hsub : ∀ A B : Finset (Fin n × Fin n), A ⊆ L ×ˢ Lᶜ → B ⊆ L ×ˢ Lᶜ →
      A.image f = B.image f → A ⊆ B := by
    intro A B hA hB h p hp
    have hpB : f p ∈ B.image f := by rw [← h]; exact Finset.mem_image_of_mem f hp
    obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hpB
    obtain ⟨hq1, -⟩ := Finset.mem_product.mp (hB hq)
    obtain ⟨-, hp2⟩ := Finset.mem_product.mp (hA hp)
    rw [Finset.mem_compl] at hp2
    rcases Sym2.eq_iff.mp hqp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rwa [show p = q from Prod.ext h1.symm h2.symm]
    · exact absurd (h1 ▸ hq1) hp2
  have hcard : ((L ×ˢ Lᶜ).powerset).card ≤ (triangleFreeGraphs n).card := by
    refine Finset.card_le_card_of_injOn (fun F => F.image f) (fun F hF => hmaps F hF) ?_
    intro A hA B hB h
    rw [Finset.mem_coe, Finset.mem_powerset] at hA hB
    exact Finset.Subset.antisymm (hsub A B hA hB h) (hsub B A hB hA h.symm)
  rwa [Finset.card_powerset, Finset.card_product, hLcard, hLccard] at hcard

end ProbMethodCombinatorics
