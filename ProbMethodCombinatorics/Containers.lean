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
