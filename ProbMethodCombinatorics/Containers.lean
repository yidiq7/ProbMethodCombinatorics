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
reported it rather than duplicating the statement. -/
theorem exists_containers_fingerprint (c : ℝ) (hc : 0 < c) :
    ∃ δ > 0, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (d : ℝ), 0 < d →
      (∑ v, (G.degree v : ℝ)) = d * n → (∀ v, (G.degree v : ℝ) ≤ c * d) →
      ∃ S A : Finset (Fin n) → Finset (Fin n),
        ∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) →
          S I ⊆ I ∧ I ⊆ S I ∪ A (S I) ∧
          ((S I).card : ℝ) ≤ 2 * δ * n / d ∧
          ((S I ∪ A (S I)).card : ℝ) ≤ (1 - δ) * n := by
  sorry

/-- **The graph container theorem** (Zhao, Theorem 11.2.1).  In a graph whose maximum degree is
within a constant factor of its average degree `d`, the independent sets are covered by a family
of containers indexed by "fingerprints" of size `≤ 2δ|V|/d`, each container missing at least a
`δ` fraction of the vertices.

The bound on `|𝒞|` is the book's `binom(|V|, ≤ 2δ|V|/d)`, written as the partial sum of binomial
coefficients it abbreviates.

**A corollary of `exists_containers_fingerprint` above**, not an independent theorem: take `𝒞`
to be the image of `T ↦ T ∪ A T` over the fingerprints `T` small enough and with `T ∪ A T` small
enough.  The second condition is load-bearing — without it the fingerprint theorem says nothing
about a `T` that is not some `S I`. -/
theorem exists_containers (c : ℝ) (hc : 0 < c) :
    ∃ δ > 0, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (d : ℝ), 0 < d →
      (∑ v, (G.degree v : ℝ)) = d * n → (∀ v, (G.degree v : ℝ) ≤ c * d) →
      ∃ 𝒞 : Finset (Finset (Fin n)),
        (𝒞.card : ℝ) ≤ ∑ i ∈ range (⌊2 * δ * n / d⌋₊ + 1), (n.choose i : ℝ) ∧
        (∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) → ∃ C ∈ 𝒞, I ⊆ C) ∧
        (∀ C ∈ 𝒞, (C.card : ℝ) ≤ (1 - δ) * n) := by
  obtain ⟨δ, hδ, hfp⟩ := exists_containers_fingerprint c hc
  refine ⟨δ, hδ, fun n G _ d hd hsum hdeg => ?_⟩
  obtain ⟨S, A, hSA⟩ := hfp n G d hd hsum hdeg
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

/-- **The graph container theorem with an arbitrarily small constant and stable fingerprints**
(Zhao, Theorem 11.2.3, in the form the hypergraph container algorithm consumes).  Two
strengthenings of `exists_containers_fingerprint`, both properties of the fingerprint the graph
container algorithm actually computes:

* `δ` may be taken below any prescribed `η`.  The conclusion is not monotone in `δ` — shrinking it
  sharpens the bound on the fingerprint and weakens the bound on the container — so this is a
  genuine strengthening, but only of the bookkeeping: the hypotheses for a constant `c` imply
  those for any larger constant, and a graph container theorem for a large enough constant already
  has a small `δ`, as the disjoint union of `⌊2c - 1⌋`-leaf stars witnesses.
* the fingerprint map is **stable** — `S J = S I` whenever `S I ⊆ J ⊆ I` — because the greedy
  choices of the algorithm on input `J` are exactly its choices on input `I` as soon as `J`
  retains all of them.

Stability is what lets a two-phase algorithm have a single set as its fingerprint: the second
phase enlarges the fingerprint inside `I`, and stability says that replaying the first phase on
the enlarged set recovers the first-phase fingerprint. -/
theorem exists_containers_fingerprint_stable (c : ℝ) (hc : 0 < c) (η : ℝ) (hη : 0 < η) :
    ∃ δ, 0 < δ ∧ δ ≤ η ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (d : ℝ), 0 < d →
        (∑ v, (G.degree v : ℝ)) = d * n → (∀ v, (G.degree v : ℝ) ≤ c * d) →
        ∃ S A : Finset (Fin n) → Finset (Fin n),
          (∀ I J : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) → S I ⊆ J → J ⊆ I →
            S J = S I) ∧
          ∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) →
            S I ⊆ I ∧ I ⊆ S I ∪ A (S I) ∧
            ((S I).card : ℝ) ≤ 2 * δ * n / d ∧
            ((S I ∪ A (S I)).card : ℝ) ≤ (1 - δ) * n := by
  sorry

/-! ### 11.3 The hypergraph container theorem -/

/-- The graph on `Fin n` with the given symmetric, irreflexive neighbourhoods. -/
private def neighborGraph {n : ℕ} (M : Fin n → Finset (Fin n))
    (hs : ∀ x y : Fin n, x ∈ M y ↔ y ∈ M x) (hl : ∀ x : Fin n, x ∉ M x) :
    SimpleGraph (Fin n) where
  Adj x y := y ∈ M x
  symm := ⟨fun a b h => (hs a b).mpr h⟩
  loopless := ⟨fun a h => hl a h⟩

/-- The degree in `neighborGraph M hs hl` is the size of the given neighbourhood. -/
private theorem degree_neighborGraph {n : ℕ} (M : Fin n → Finset (Fin n))
    (hs : ∀ x y : Fin n, x ∈ M y ↔ y ∈ M x) (hl : ∀ x : Fin n, x ∉ M x)
    [DecidableRel (neighborGraph M hs hl).Adj] (x : Fin n) :
    (neighborGraph M hs hl).degree x = (M x).card := by
  have h : (neighborGraph M hs hl).neighborFinset x = M x := by
    ext w
    rw [SimpleGraph.mem_neighborFinset]
    exact Iff.rfl
  rw [SimpleGraph.degree, h]

/-- The degree sum of `neighborGraph M hs hl` is the sum of the sizes of the neighbourhoods. -/
private theorem sum_degree_neighborGraph {n : ℕ} (M : Fin n → Finset (Fin n))
    (hs : ∀ x y : Fin n, x ∈ M y ↔ y ∈ M x) (hl : ∀ x : Fin n, x ∉ M x)
    [DecidableRel (neighborGraph M hs hl).Adj] :
    (∑ v : Fin n, ((neighborGraph M hs hl).degree v : ℝ))
      = ∑ v : Fin n, ((M v).card : ℝ) :=
  Finset.sum_congr rfl fun v _ => by rw [degree_neighborGraph]

/-- The graph container theorem, fed a graph presented by its neighbourhoods. -/
private theorem graphContainer_of_neighbors {n : ℕ} (δ₁ c' : ℝ)
    (hgc : ∀ (m : ℕ) (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] (e : ℝ), 0 < e →
      (∑ v, (G.degree v : ℝ)) = e * m → (∀ v, (G.degree v : ℝ) ≤ c' * e) →
      ∃ S A : Finset (Fin m) → Finset (Fin m),
        (∀ I J : Finset (Fin m), G.IsIndepSet (I : Set (Fin m)) → S I ⊆ J → J ⊆ I →
          S J = S I) ∧
        ∀ I : Finset (Fin m), G.IsIndepSet (I : Set (Fin m)) →
          S I ⊆ I ∧ I ⊆ S I ∪ A (S I) ∧
          ((S I).card : ℝ) ≤ 2 * δ₁ * m / e ∧
          ((S I ∪ A (S I)).card : ℝ) ≤ (1 - δ₁) * m)
    (M : Fin n → Finset (Fin n)) (hs : ∀ x y : Fin n, x ∈ M y ↔ y ∈ M x)
    (hl : ∀ x : Fin n, x ∉ M x) (e : ℝ) (he : 0 < e)
    (hsum : (∑ v : Fin n, ((M v).card : ℝ)) = e * n)
    (hdeg : ∀ v : Fin n, ((M v).card : ℝ) ≤ c' * e) :
    ∃ S A : Finset (Fin n) → Finset (Fin n),
      (∀ I J : Finset (Fin n), (neighborGraph M hs hl).IsIndepSet (I : Set (Fin n)) →
        S I ⊆ J → J ⊆ I → S J = S I) ∧
      ∀ I : Finset (Fin n), (neighborGraph M hs hl).IsIndepSet (I : Set (Fin n)) →
        S I ⊆ I ∧ I ⊆ S I ∪ A (S I) ∧
        ((S I).card : ℝ) ≤ 2 * δ₁ * n / e ∧
        ((S I ∪ A (S I)).card : ℝ) ≤ (1 - δ₁) * n := by
  let inst : DecidableRel (neighborGraph M hs hl).Adj :=
    fun a b => inferInstanceAs (Decidable (b ∈ M a))
  exact @hgc n (neighborGraph M hs hl) inst e he
    (by rw [sum_degree_neighborGraph]; exact hsum)
    (fun v => by rw [degree_neighborGraph]; exact hdeg v)

/-- The counting form of a container theorem, read off from its fingerprint form: the containers
are the values of `T ↦ T ∪ A T` on the fingerprints that are small and have a small container,
and there are at most as many of those as there are subsets of size at most `b`. -/
private theorem containers_of_fingerprint {n : ℕ} (b m : ℝ)
    (S A : Finset (Fin n) → Finset (Fin n)) (P : Finset (Fin n) → Prop)
    (h : ∀ I : Finset (Fin n), P I → S I ⊆ I ∧ I ⊆ S I ∪ A (S I) ∧
      ((S I).card : ℝ) ≤ b ∧ ((S I ∪ A (S I)).card : ℝ) ≤ m) :
    ∃ 𝒞 : Finset (Finset (Fin n)),
      (𝒞.card : ℝ) ≤ ∑ i ∈ range (⌊b⌋₊ + 1), (n.choose i : ℝ) ∧
      (∀ I : Finset (Fin n), P I → ∃ C ∈ 𝒞, I ⊆ C) ∧
      (∀ C ∈ 𝒞, (C.card : ℝ) ≤ m) := by
  set F : Finset (Finset (Fin n)) :=
    univ.powerset.filter fun T : Finset (Fin n) =>
      (T.card : ℝ) ≤ b ∧ ((T ∪ A T).card : ℝ) ≤ m with hF
  refine ⟨F.image fun T => T ∪ A T, ?_, ?_, ?_⟩
  · have hsub : F ⊆ (range (⌊b⌋₊ + 1)).biUnion
        fun i => powersetCard i (univ : Finset (Fin n)) := by
      intro T hT
      rw [hF, mem_filter] at hT
      exact mem_biUnion.mpr ⟨T.card, mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hT.2.1)),
        mem_powersetCard.mpr ⟨subset_univ _, rfl⟩⟩
    have hcount : ((range (⌊b⌋₊ + 1)).biUnion
        fun i => powersetCard i (univ : Finset (Fin n))).card
        = ∑ i ∈ range (⌊b⌋₊ + 1), n.choose i := by
      rw [card_biUnion ((pairwise_disjoint_powersetCard (univ : Finset (Fin n))).set_pairwise _)]
      simp
    have hnat : (F.image fun T => T ∪ A T).card ≤ ∑ i ∈ range (⌊b⌋₊ + 1), n.choose i :=
      card_image_le.trans (hcount ▸ card_le_card hsub)
    calc ((F.image fun T => T ∪ A T).card : ℝ)
        ≤ ((∑ i ∈ range (⌊b⌋₊ + 1), n.choose i : ℕ) : ℝ) := Nat.cast_le.mpr hnat
      _ = ∑ i ∈ range (⌊b⌋₊ + 1), (n.choose i : ℝ) := by push_cast; ring
  · intro I hI
    obtain ⟨-, hcov, hsmall, hcont⟩ := h I hI
    exact ⟨S I ∪ A (S I), mem_image_of_mem _
      (mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), hsmall, hcont⟩), hcov⟩
  · intro C hC
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hC
    exact (mem_filter.mp hT).2.2

/-- **The first phase of the 3-uniform container algorithm and its forbidden-pair graph**
(Zhao, §11.3, the algorithm sketched on printed p. 209).

Run for `ε · v(H) / √d` steps, the phase returns a fingerprint `S I ⊆ I`, the set `X T` of
vertices it has certified to lie outside `I`, and the neighbourhoods `N T` of the graph `G` of
forbidden pairs — `X` and `N` functions of the fingerprint alone, which is what lets the container
be one too.  `G` is the union of the links of the vertices of `S`, with the vertices of `G`-degree
above `c√d` stripped of their edges, as in the algorithm's fifth step; that is why its maximum
degree is `O(√d)` unconditionally.  A pair inside `I` is never forbidden, because `uxy ∈ E(H)` for
`u ∈ S ⊆ I` would put an edge of `H` inside `I`.

The final disjunct is the dichotomy at termination: either the phase has certified a constant
fraction of the vertices to lie outside `I`, or `G` has `Ω(√d · n)` edges — in which case its
average degree and its maximum degree agree up to a constant and the graph container theorem
applies to it.  Both thresholds are the single constant `δ`, which the statement is free to choose
as small as the proof needs; `exists_containers_three_uniform` picks the constant of
`exists_containers_fingerprint_stable` afterwards, so nothing here has to anticipate it. -/
theorem exists_forbiddenPairs_three_uniform (c : ℝ) (hc : 0 < c) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (n : ℕ) (H : Finset (Finset (Fin n))) (d : ℝ),
      (∀ e ∈ H, e.card = 3) → δ⁻¹ ≤ d → 3 * (H.card : ℝ) = d * n →
      (maxCodegree 1 H : ℝ) ≤ c * d → (maxCodegree 2 H : ℝ) ≤ c * Real.sqrt d →
      ∃ (S X : Finset (Fin n) → Finset (Fin n)) (N : Finset (Fin n) → Fin n → Finset (Fin n)),
        (∀ (T : Finset (Fin n)) (x y : Fin n), x ∈ N T y ↔ y ∈ N T x) ∧
        (∀ (T : Finset (Fin n)) (x : Fin n), x ∉ N T x) ∧
        (∀ I J : Finset (Fin n), (∀ e ∈ H, ¬ e ⊆ I) → S I ⊆ J → J ⊆ I → S J = S I) ∧
        ∀ I : Finset (Fin n), (∀ e ∈ H, ¬ e ⊆ I) →
          S I ⊆ I ∧
          ((S I).card : ℝ) ≤ ε * n / Real.sqrt d ∧
          Disjoint I (X (S I)) ∧
          (∀ x ∈ I, ∀ y ∈ I, y ∉ N (S I) x) ∧
          (∀ x : Fin n, ((N (S I) x).card : ℝ) ≤ c * Real.sqrt d) ∧
          (δ * n ≤ ((X (S I)).card : ℝ) ∨
            δ * Real.sqrt d * n ≤ ∑ x : Fin n, ((N (S I) x).card : ℝ)) := by
  sorry

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
  obtain ⟨δ₀, hδ₀, halg⟩ := exists_forbiddenPairs_three_uniform c hc (1 / 2) (by norm_num)
  obtain ⟨δ₁, hδ₁, hδ₁η, hgc⟩ :=
    exists_containers_fingerprint_stable (c / δ₀) (div_pos hc hδ₀) (δ₀ / 4) (by positivity)
  -- The fingerprint is built in two phases: the first is the one
  -- `exists_forbiddenPairs_three_uniform` computes, and on the dense branch the graph container
  -- theorem applied to the forbidden-pair graph supplies the second.  Each gets half of the
  -- budget `v(H)/√d`, which is what `δ₁ ≤ δ₀ / 4` buys: the forbidden-pair graph has average
  -- degree at least `δ₀√d`, so its fingerprint has size at most `2δ₁ v(H)/(δ₀√d)`.
  refine ⟨min δ₀ (min (δ₁ / 2) (δ₁ ^ 2 / 4)),
    lt_min hδ₀ (lt_min (by positivity) (by positivity)), ?_⟩
  intro n H d h3 hd hsum hΔ₁ hΔ₂
  set δ := min δ₀ (min (δ₁ / 2) (δ₁ ^ 2 / 4)) with hδdef
  have hδpos : 0 < δ := lt_min hδ₀ (lt_min (by positivity) (by positivity))
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδhalf : δ ≤ δ₁ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδsq : δ ≤ δ₁ ^ 2 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hdpos : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdpos
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨{∅}, ?_, ?_, ?_⟩
    · simp
    · exact fun I _ => ⟨∅, mem_singleton_self _, fun x _ => x.elim0⟩
    · intro C hC
      rw [mem_singleton] at hC
      simp [hC]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd₀ : δ₀⁻¹ ≤ d := le_trans (by gcongr) hd
  obtain ⟨S, X, N, hsymm, hloop, hstab, hmain⟩ := halg n H d h3 hd₀ hsum hΔ₁ hΔ₂
  obtain ⟨dG, hdG⟩ : ∃ f : Finset (Fin n) → ℝ,
      ∀ T, f T = (∑ v : Fin n, ((N T v).card : ℝ)) / n := ⟨_, fun _ => rfl⟩
  have hgraph : ∀ T : Finset (Fin n), ∃ S' A' : Finset (Fin n) → Finset (Fin n),
      0 < dG T → (∀ v : Fin n, ((N T v).card : ℝ) ≤ c / δ₀ * dG T) →
      ((∀ I J : Finset (Fin n),
            (neighborGraph (N T) (hsymm T) (hloop T)).IsIndepSet (I : Set (Fin n)) →
            S' I ⊆ J → J ⊆ I → S' J = S' I) ∧
        ∀ I : Finset (Fin n),
          (neighborGraph (N T) (hsymm T) (hloop T)).IsIndepSet (I : Set (Fin n)) →
            S' I ⊆ I ∧ I ⊆ S' I ∪ A' (S' I) ∧
            ((S' I).card : ℝ) ≤ 2 * δ₁ * n / dG T ∧
            ((S' I ∪ A' (S' I)).card : ℝ) ≤ (1 - δ₁) * n) := by
    intro T
    by_cases hgood : 0 < dG T ∧ ∀ v : Fin n, ((N T v).card : ℝ) ≤ c / δ₀ * dG T
    · obtain ⟨S', A', hst, hmn⟩ := graphContainer_of_neighbors δ₁ (c / δ₀) hgc
        (N T) (hsymm T) (hloop T) (dG T) hgood.1
        (by rw [hdG, div_mul_cancel₀ _ hn'.ne']) hgood.2
      exact ⟨S', A', fun _ _ => ⟨hst, hmn⟩⟩
    · exact ⟨fun _ => ∅, fun _ => ∅, fun h1 h2 => absurd ⟨h1, h2⟩ hgood⟩
  choose S' A' hS' using hgraph
  obtain ⟨Sfin, hSfin⟩ : ∃ f : Finset (Fin n) → Finset (Fin n),
      ∀ I, f I = if δ₀ * n ≤ ((X (S I)).card : ℝ) then S I else S I ∪ S' (S I) I :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Afin, hAfin⟩ : ∃ f : Finset (Fin n) → Finset (Fin n),
      ∀ T, f T = if δ₀ * n ≤ ((X (S T)).card : ℝ) then univ \ X (S T)
        else S T ∪ (S' (S T) T ∪ A' (S T) (S' (S T) T)) := ⟨_, fun _ => rfl⟩
  have hhalf : (n : ℝ) / (2 * Real.sqrt d) + (n : ℝ) / (2 * Real.sqrt d)
      = (n : ℝ) / Real.sqrt d := by
    field_simp
    ring
  refine containers_of_fingerprint ((n : ℝ) / Real.sqrt d) ((1 - δ) * n) Sfin Afin
    (fun I => ∀ e ∈ H, ¬ e ⊆ I) ?_
  intro I hI
  obtain ⟨hSI, hScard₀, hdisj, hindep, hNdeg, hcase⟩ := hmain I hI
  have hScard : ((S I).card : ℝ) ≤ (n : ℝ) / (2 * Real.sqrt d) := by
    refine hScard₀.trans ?_
    rw [show (1 : ℝ) / 2 * (n : ℝ) / Real.sqrt d = (n : ℝ) / (2 * Real.sqrt d) from by ring]
  have hSS : S (S I) = S I := hstab I (S I) hI Subset.rfl hSI
  by_cases hsparse : δ₀ * n ≤ ((X (S I)).card : ℝ)
  · -- The first phase has removed a constant fraction of the vertices.
    have hS1 : Sfin I = S I := by
      rw [hSfin, if_pos hsparse]
    have hA1 : Afin (Sfin I) = univ \ X (S I) := by
      rw [hAfin, hS1, hSS, if_pos hsparse]
    have hIX : I ⊆ univ \ X (S I) := fun x hx =>
      mem_sdiff.mpr ⟨mem_univ x, Finset.disjoint_left.mp hdisj hx⟩
    refine ⟨hS1 ▸ hSI, ?_, ?_, ?_⟩
    · rw [hA1, hS1]
      exact fun x hx => mem_union_right _ (hIX hx)
    · rw [hS1]
      refine hScard.trans ?_
      have h2 : Real.sqrt d ≤ 2 * Real.sqrt d := by linarith
      calc (n : ℝ) / (2 * Real.sqrt d) ≤ (n : ℝ) / Real.sqrt d := by gcongr
        _ = (n : ℝ) / Real.sqrt d := rfl
    · rw [hA1, hS1, union_eq_right.mpr (hSI.trans hIX)]
      have hXle : (X (S I)).card ≤ n := by
        simpa using Finset.card_le_univ (X (S I))
      have hcard : ((univ \ X (S I)).card : ℝ) = (n : ℝ) - ((X (S I)).card : ℝ) := by
        rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin,
          Nat.cast_sub hXle]
      rw [hcard]
      have : δ * n ≤ δ₀ * n := mul_le_mul_of_nonneg_right hδδ₀ hn'.le
      linarith
  · -- The forbidden-pair graph is dense, and the graph container lemma applies to it.
    have hdense : δ₀ * Real.sqrt d * n ≤ ∑ x : Fin n, ((N (S I) x).card : ℝ) :=
      hcase.resolve_left hsparse
    have hdGlb : δ₀ * Real.sqrt d ≤ dG (S I) := by
      rw [hdG, le_div_iff₀ hn']
      linarith
    have hdGpos : 0 < dG (S I) := lt_of_lt_of_le (mul_pos hδ₀ hsd) hdGlb
    have hmaxdeg : ∀ v : Fin n, ((N (S I) v).card : ℝ) ≤ c / δ₀ * dG (S I) := by
      intro v
      calc ((N (S I) v).card : ℝ) ≤ c * Real.sqrt d := hNdeg v
        _ = c / δ₀ * (δ₀ * Real.sqrt d) := by field_simp
        _ ≤ c / δ₀ * dG (S I) := mul_le_mul_of_nonneg_left hdGlb (div_nonneg hc.le hδ₀.le)
    obtain ⟨hgstab, hgmain⟩ := hS' (S I) hdGpos hmaxdeg
    have hIindep :
        (neighborGraph (N (S I)) (hsymm (S I)) (hloop (S I))).IsIndepSet (I : Set (Fin n)) := by
      rw [SimpleGraph.isIndepSet_iff]
      intro x hx y hy _ hadj
      exact hindep x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) hadj
    obtain ⟨hS'sub, hS'cov, hS'card, hS'cont⟩ := hgmain I hIindep
    have hFsub : S I ∪ S' (S I) I ⊆ I := union_subset hSI hS'sub
    have hS2 : Sfin I = S I ∪ S' (S I) I := by
      rw [hSfin, if_neg hsparse]
    have hSSf : S (Sfin I) = S I := by
      rw [hS2]
      exact hstab I _ hI subset_union_left hFsub
    have hS'Sf : S' (S I) (Sfin I) = S' (S I) I :=
      hgstab I (Sfin I) hIindep (hS2 ▸ subset_union_right) (hS2 ▸ hFsub)
    have hA2 : Afin (Sfin I) = S I ∪ (S' (S I) I ∪ A' (S I) (S' (S I) I)) := by
      rw [hAfin, hSSf, hS'Sf, if_neg hsparse]
    refine ⟨hS2 ▸ hFsub, ?_, ?_, ?_⟩
    · rw [hA2]
      exact fun x hx => mem_union_right _ (mem_union_right _ (hS'cov hx))
    · -- the two fingerprints together are still small
      have hS'small : 2 * δ₁ * n / dG (S I) ≤ (n : ℝ) / (2 * Real.sqrt d) := by
        rw [div_le_div_iff₀ hdGpos (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hdGlb hn'.le,
          mul_le_mul_of_nonneg_left hδ₁η (by positivity : (0 : ℝ) ≤ 4 * (n : ℝ) * Real.sqrt d)]
      calc ((Sfin I).card : ℝ) ≤ (((S I).card : ℝ) + ((S' (S I) I).card : ℝ)) := by
            rw [hS2]
            exact_mod_cast Nat.cast_le.mpr (card_union_le _ _)
        _ ≤ (n : ℝ) / (2 * Real.sqrt d) + (n : ℝ) / (2 * Real.sqrt d) :=
            add_le_add hScard (hS'card.trans hS'small)
        _ = (n : ℝ) / Real.sqrt d := hhalf
    · -- the container is still missing a `δ` fraction of the vertices
      have hsubU : Sfin I ∪ Afin (Sfin I)
          ⊆ S I ∪ (S' (S I) I ∪ A' (S I) (S' (S I) I)) := by
        rw [hA2, hS2]
        intro x hx
        rcases mem_union.mp hx with h | h
        · rcases mem_union.mp h with h | h
          · exact mem_union_left _ h
          · exact mem_union_right _ (mem_union_left _ h)
        · exact h
      have hsqδ : Real.sqrt δ ≤ δ₁ / 2 := by
        have h1 : Real.sqrt δ ≤ Real.sqrt (δ₁ ^ 2 / 4) := Real.sqrt_le_sqrt hδsq
        rwa [show δ₁ ^ 2 / 4 = (δ₁ / 2) ^ 2 by ring, Real.sqrt_sq (by positivity)] at h1
      have hinv : 1 / Real.sqrt d ≤ Real.sqrt δ := by
        have h1 : Real.sqrt δ⁻¹ ≤ Real.sqrt d := Real.sqrt_le_sqrt hd
        rw [Real.sqrt_inv] at h1
        have h2 : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδpos
        rw [div_le_iff₀ hsd]
        calc (1 : ℝ) = (Real.sqrt δ)⁻¹ * Real.sqrt δ := (inv_mul_cancel₀ h2.ne').symm
          _ ≤ Real.sqrt d * Real.sqrt δ := mul_le_mul_of_nonneg_right h1 h2.le
          _ = Real.sqrt δ * Real.sqrt d := mul_comm _ _
      have hlast : (n : ℝ) / (2 * Real.sqrt d) + (1 - δ₁) * n ≤ (1 - δ) * n := by
        have h1 : (n : ℝ) / (2 * Real.sqrt d) = (n : ℝ) * (1 / Real.sqrt d) / 2 := by
          field_simp
        rw [h1]
        nlinarith [mul_le_mul_of_nonneg_left hinv hn'.le,
          mul_le_mul_of_nonneg_left hsqδ hn'.le,
          mul_le_mul_of_nonneg_right hδhalf hn'.le]
      calc ((Sfin I ∪ Afin (Sfin I)).card : ℝ)
          ≤ ((S I ∪ (S' (S I) I ∪ A' (S I) (S' (S I) I))).card : ℝ) :=
            Nat.cast_le.mpr (card_le_card hsubU)
        _ ≤ ((S I).card : ℝ) + ((S' (S I) I ∪ A' (S I) (S' (S I) I)).card : ℝ) := by
            exact_mod_cast Nat.cast_le.mpr (card_union_le _ _)
        _ ≤ (n : ℝ) / (2 * Real.sqrt d) + (1 - δ₁) * n := add_le_add hScard hS'cont
        _ ≤ (1 - δ) * n := hlast

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
  sorry

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
