import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.Field.ZMod
import ProbMethodCombinatorics.PropertyB

/-!
# Chapter 3: Alterations

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Chapter 3.

The method: make a random construction, then repair its blemishes.
-/

namespace ProbMethodCombinatorics

open Finset

/-- **Markov's inequality**, in the finite-averaging form this project uses: for a nonnegative
`f` on `s`, the number of points of `s` where `f` reaches `a` is at most `(∑ i ∈ s, f i) / a`.

Mathlib's `MeasureTheory.mul_meas_ge_le_lintegral₀` is the measure-theoretic statement; this is
the counting one (Zhao, Theorem 3.3.1). -/
theorem card_filter_le_sum_div {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) {a : ℝ} (ha : 0 < a) :
    ((s.filter fun i => a ≤ f i).card : ℝ) ≤ (∑ i ∈ s, f i) / a := by
  rw [le_div_iff₀ ha]
  have hsum : ∑ i ∈ s.filter fun i => a ≤ f i, f i ≤ ∑ i ∈ s, f i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun i hi _ => hf i hi
  have hcard : ((s.filter fun i => a ≤ f i).card : ℝ) * a
      ≤ ∑ i ∈ s.filter fun i => a ≤ f i, f i := by
    have := Finset.card_nsmul_le_sum (s.filter fun i => a ≤ f i) f a
      fun i hi => (Finset.mem_filter.mp hi).2
    simpa [nsmul_eq_mul, mul_comm] using this
  exact hcard.trans hsum

section Dominating

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `U` is a *dominating set* of `G` if every vertex is in `U` or has a neighbour in `U`. -/
def IsDominating (G : SimpleGraph V) (U : Finset V) : Prop :=
  ∀ v : V, v ∈ U ∨ ∃ u ∈ U, G.Adj u v

/-- **Zhao, Theorem 3.1.1**: a graph on `n` vertices with minimum degree `δ > 1` has a dominating
set of size at most `((log (δ + 1) + 1) / (δ + 1)) * n`. -/
theorem exists_isDominating_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {δ : ℕ} (hδ : 1 < δ) (hdeg : ∀ v : V, δ ≤ G.degree v) :
    ∃ U : Finset V, IsDominating G U ∧
      (U.card : ℝ) ≤ (Real.log (δ + 1) + 1) / (δ + 1) * Fintype.card V := by
  sorry

end Dominating

section Heilbronn

/-- Twice the (unsigned) area of the triangle spanned by `p`, `q`, `r` in the plane. -/
def twiceArea (p q r : ℝ × ℝ) : ℝ :=
  |(q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2)|

/-- **Heilbronn triangle problem** (Zhao, Theorem 3.2.3): for some absolute constant `c > 0` and
every `n`, there are `n` points in the unit square with every triple spanning a triangle of area
at least `c / n ^ 2`. -/
theorem exists_heilbronn_configuration :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∃ S : Finset (ℝ × ℝ), S.card = n ∧
      (∀ p ∈ S, p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → p ≠ r → q ≠ r →
        c / (n : ℝ) ^ 2 ≤ twiceArea p q r := by
  refine ⟨1 / 4, by norm_num, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨∅, rfl, by simp, by simp⟩
  obtain ⟨P, hP, hnP, hP2n⟩ := Nat.exists_prime_lt_and_le_two_mul n hn.ne'
  have : Fact P.Prime := ⟨hP⟩
  have hP0 : 0 < P := hP.pos
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP0
  set g : ℕ → ℝ × ℝ := fun x => ((x : ℝ) / P, ((x ^ 2 % P : ℕ) : ℝ) / P) with hg
  have hginj : Function.Injective g := by
    intro x y hxy
    have h1 : (x : ℝ) / P = (y : ℝ) / P := congrArg Prod.fst hxy
    field_simp at h1
    exact_mod_cast h1
  have hcard : ((Finset.range P).image g).card = P := by
    rw [Finset.card_image_of_injective _ hginj, Finset.card_range]
  obtain ⟨S, hST, hScard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.range P).image g) (n := n) (by omega)
  -- distinct residues below `P` give distinct elements of `ZMod P`
  have hne : ∀ x y : ℕ, x < P → y < P → x ≠ y → (x : ZMod P) ≠ (y : ZMod P) := by
    intro x y hx hy hxy h
    exact hxy (by
      have := congrArg ZMod.val h
      rwa [ZMod.val_cast_of_lt hx, ZMod.val_cast_of_lt hy] at this)
  -- a triangle whose scaled-down vertices come from distinct integer points with non-zero
  -- determinant has twice-area at least `1 / P ^ 2`
  have hmain : ∀ x y z xx yy zz : ℕ,
      ((y : ℤ) - (x : ℤ)) * ((zz : ℤ) - (xx : ℤ))
        - ((z : ℤ) - (x : ℤ)) * ((yy : ℤ) - (xx : ℤ)) ≠ 0 →
      1 / (P : ℝ) ^ 2 ≤
        |((y : ℝ) / P - (x : ℝ) / P) * ((zz : ℝ) / P - (xx : ℝ) / P)
          - ((z : ℝ) / P - (x : ℝ) / P) * ((yy : ℝ) / P - (xx : ℝ) / P)| := by
    intro x y z xx yy zz hD
    have hrw : ((y : ℝ) / P - (x : ℝ) / P) * ((zz : ℝ) / P - (xx : ℝ) / P)
        - ((z : ℝ) / P - (x : ℝ) / P) * ((yy : ℝ) / P - (xx : ℝ) / P)
        = ((((y : ℤ) - (x : ℤ)) * ((zz : ℤ) - (xx : ℤ))
          - ((z : ℤ) - (x : ℤ)) * ((yy : ℤ) - (xx : ℤ)) : ℤ) : ℝ) / (P : ℝ) ^ 2 := by
      push_cast
      field_simp
    rw [hrw, abs_div, abs_of_pos (show (0 : ℝ) < (P : ℝ) ^ 2 by positivity)]
    have h1 : (1 : ℝ) ≤ |((((y : ℤ) - (x : ℤ)) * ((zz : ℤ) - (xx : ℤ))
        - ((z : ℤ) - (x : ℤ)) * ((yy : ℤ) - (xx : ℤ)) : ℤ) : ℝ)| := by
      have := Int.cast_le (R := ℝ) |>.2 (Int.one_le_abs hD)
      simpa using this
    gcongr
  refine ⟨S, hScard, ?_, ?_⟩
  · intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hST hu)
    have hxP : x < P := Finset.mem_range.mp hx
    have hmP : x ^ 2 % P < P := Nat.mod_lt _ hP0
    refine ⟨⟨by positivity, ?_⟩, ⟨by positivity, ?_⟩⟩
    · rw [hg]
      exact (div_le_one hPR).2 (by exact_mod_cast hxP.le)
    · rw [hg]
      exact (div_le_one hPR).2 (by exact_mod_cast hmP.le)
  · intro u hu v hv w hw huv huw hvw
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (hST hu)
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (hST hv)
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp (hST hw)
    have haP : a < P := Finset.mem_range.mp ha
    have hbP : b < P := Finset.mem_range.mp hb
    have hcP : c < P := Finset.mem_range.mp hc
    have hab : a ≠ b := fun h => huv (by rw [h])
    have hac : a ≠ c := fun h => huw (by rw [h])
    have hbc : b ≠ c := fun h => hvw (by rw [h])
    -- twice the area before scaling is an integer, congruent mod `P` to a product of three
    -- differences, none of which vanishes in the field `ZMod P`
    have hDne : ((b : ℤ) - (a : ℤ)) * (((c ^ 2 % P : ℕ) : ℤ) - ((a ^ 2 % P : ℕ) : ℤ))
        - ((c : ℤ) - (a : ℤ)) * (((b ^ 2 % P : ℕ) : ℤ) - ((a ^ 2 % P : ℕ) : ℤ)) ≠ 0 := by
      intro h0
      have hz : ((((b : ℤ) - (a : ℤ)) * (((c ^ 2 % P : ℕ) : ℤ) - ((a ^ 2 % P : ℕ) : ℤ))
          - ((c : ℤ) - (a : ℤ)) * (((b ^ 2 % P : ℕ) : ℤ) - ((a ^ 2 % P : ℕ) : ℤ)) : ℤ)
          : ZMod P) = 0 := by rw [h0]; simp
      push_cast [ZMod.natCast_mod] at hz
      have hprod : ((b : ZMod P) - (a : ZMod P)) * ((c : ZMod P) - (a : ZMod P))
          * ((c : ZMod P) - (b : ZMod P)) = 0 := by linear_combination hz
      rcases mul_eq_zero.mp hprod with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact hne b a hbP haP (Ne.symm hab) (sub_eq_zero.mp h)
        · exact hne c a hcP haP (Ne.symm hac) (sub_eq_zero.mp h)
      · exact hne c b hcP hbP (Ne.symm hbc) (sub_eq_zero.mp h)
    have hP4 : (P : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
      have h2 : (P : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hP2n
      nlinarith [hPR.le]
    have hstep : (1 : ℝ) / 4 / (n : ℝ) ^ 2 ≤ 1 / (P : ℝ) ^ 2 := by
      rw [div_div]
      exact one_div_le_one_div_of_le (by positivity) hP4
    simp only [twiceArea, hg]
    exact hstep.trans (hmain a b c (a ^ 2 % P) (b ^ 2 % P) (c ^ 2 % P) hDne)

end Heilbronn

/-- The colour classes of a proper colouring are independent sets, so a graph colourable with
`m` colours has at most `m * α(G)` vertices.  This is the bound `χ(G) ≥ |V| / α(G)` used in the
last step of Zhao, Theorem 3.4.1, in division-free form. -/
theorem card_le_mul_indepNum_of_colorable {V : Type*} [Fintype V] (G : SimpleGraph V) {m : ℕ}
    (hG : G.Colorable m) : Fintype.card V ≤ m * G.indepNum := by
  obtain ⟨C⟩ := hG
  have key : ∀ c : Fin m, (univ.filter fun v => C v = c).card ≤ G.indepNum := by
    intro c
    refine SimpleGraph.IsIndepSet.card_le_indepNum ?_
    intro v hv w hw _
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv hw
    exact fun hadj => C.valid hadj (hv.trans hw.symm)
  calc Fintype.card V = ∑ c : Fin m, (univ.filter fun v => C v = c).card := by
        rw [← Finset.card_univ]
        exact Finset.card_eq_sum_card_fiberwise fun v _ => Finset.mem_univ (C v)
    _ ≤ ∑ _c : Fin m, G.indepNum := Finset.sum_le_sum fun c _ => key c
    _ = m * G.indepNum := by simp

/-- The number of edges of the random graph used in the proof of Zhao, Theorem 3.4.1: the
uniform model `G(n, M)` is taken with `M = ⌈n (log n) ^ 2⌉`, i.e. edge density
`p ≈ (log n) ^ 2 / n`. -/
noncomputable def girthEdgeCount (n : ℕ) : ℕ := ⌈(n : ℝ) * Real.log n ^ 2⌉₊

/-- The sample space of the uniform random graph `G(n, M)`: the `M`-element sets of unordered
pairs of vertices, each read as a graph through `SimpleGraph.fromEdgeSet`. -/
def graphFamily (n M : ℕ) : Finset (Finset (Sym2 (Fin n))) :=
  Finset.powersetCard M Finset.univ

/-- The vertices lying on a cycle of length at most `l` of the graph read off from the edge set
`E` through `SimpleGraph.fromEdgeSet`. -/
noncomputable def shortCycleSupport (l : ℕ) {n : ℕ} (E : Finset (Sym2 (Fin n))) :
    Finset (Fin n) :=
  (Set.toFinite {v : Fin n | ∃ (a : Fin n)
      (w : (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))).Walk a a),
      w.IsCycle ∧ w.length ≤ l ∧ v ∈ w.support}).toFinset

/-- **The expectation computation** behind the first step of Zhao, Theorem 3.4.1.  The expected
number of cycles of length at most `l` in `G(n, M)` with `M = girthEdgeCount n` is
`∑_{i=3}^{l} (n choose i) (i - 1)! / 2 · p ^ i = O((log n) ^ (2 l))` with `p ≈ 2 (log n) ^ 2 / n`,
so the expected number of vertices lying on such a cycle, at most `l` times that, is `o(n)`:
for all large `n` it is below `n / 4`, here in the division-free form
`4 * ∑ #S(E) < n * #(sample space)`. -/
theorem exists_sum_shortCycleSupport_card_lt (l : ℕ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      4 * ∑ E ∈ graphFamily n (girthEdgeCount n), ((shortCycleSupport l E).card : ℝ)
        < n * ((graphFamily n (girthEdgeCount n)).card : ℝ) := by
  sorry

/-- **Few short cycles** (first step of Zhao, Theorem 3.4.1).  For all large `n`, fewer than half
the graphs of `G(n, M)` with `M = girthEdgeCount n` fail to have a set `S` of at most `n / 2`
vertices meeting every cycle of length at most `l`.

This is the expectation computation `E[#{cycles of length ≤ l}] ≤ l (log n) ^ (2 l) = o(n)`
followed by the counting Markov bound `card_filter_le_sum_div`. -/
theorem exists_bad_card_lt_and_shortCycleCover (l : ℕ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ B ⊆ graphFamily n (girthEdgeCount n),
      2 * B.card < (graphFamily n (girthEdgeCount n)).card ∧
      ∀ E ∈ graphFamily n (girthEdgeCount n), E ∉ B →
        ∃ S : Finset (Fin n), 2 * S.card ≤ n ∧
          ∀ (a : Fin n) (w : (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))).Walk a a),
            w.IsCycle → w.length ≤ l → ∃ v ∈ S, v ∈ w.support := by
  obtain ⟨n₀, hn₀⟩ := exists_sum_shortCycleSupport_card_lt l
  refine ⟨n₀, fun n hn => ?_⟩
  have key := hn₀ n hn
  have hnonneg : ∀ E ∈ graphFamily n (girthEdgeCount n),
      (0 : ℝ) ≤ ((shortCycleSupport l E).card : ℝ) := fun _ _ => by positivity
  have hsum : (0 : ℝ) ≤ ∑ E ∈ graphFamily n (girthEdgeCount n),
      ((shortCycleSupport l E).card : ℝ) := Finset.sum_nonneg hnonneg
  have hprod : (0 : ℝ) < n * ((graphFamily n (girthEdgeCount n)).card : ℝ) := by linarith
  have hnpos : (0 : ℝ) < n := by
    rcases (Nat.cast_nonneg n : (0 : ℝ) ≤ n).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hprod; exact absurd hprod (lt_irrefl 0)
  refine ⟨(graphFamily n (girthEdgeCount n)).filter
    fun E => (n : ℝ) / 2 ≤ ((shortCycleSupport l E).card : ℝ), Finset.filter_subset _ _, ?_, ?_⟩
  · have hmarkov := card_filter_le_sum_div (graphFamily n (girthEdgeCount n))
      (fun E => ((shortCycleSupport l E).card : ℝ)) hnonneg
      (show (0 : ℝ) < (n : ℝ) / 2 by positivity)
    rw [le_div_iff₀ (show (0 : ℝ) < (n : ℝ) / 2 by positivity)] at hmarkov
    have hlt : ((2 * ((graphFamily n (girthEdgeCount n)).filter
        fun E => (n : ℝ) / 2 ≤ ((shortCycleSupport l E).card : ℝ)).card : ℕ) : ℝ) * n
        < ((graphFamily n (girthEdgeCount n)).card : ℝ) * n := by
      push_cast
      nlinarith [hmarkov]
    exact_mod_cast lt_of_mul_lt_mul_right hlt hnpos.le
  · intro E hE hEB
    refine ⟨shortCycleSupport l E, ?_, ?_⟩
    · have : ¬ ((n : ℝ) / 2 ≤ ((shortCycleSupport l E).card : ℝ)) := fun h =>
        hEB (Finset.mem_filter.mpr ⟨hE, h⟩)
      have h2 : ((2 * (shortCycleSupport l E).card : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by
        push_cast
        linarith [not_le.mp this]
      exact_mod_cast h2
    · intro a w hcyc hlen
      exact ⟨a, (Set.Finite.mem_toFinset _).mpr ⟨a, w, hcyc, hlen, w.start_mem_support⟩,
        w.start_mem_support⟩

/-- **No large independent set** (third step of Zhao, Theorem 3.4.1).  For every `ε > 0` and all
large `n`, fewer than half the graphs of `G(n, M)` with `M = girthEdgeCount n` have an independent
set of size `ε n`.

This is the union bound `ℙ(α(G) ≥ x) ≤ (n choose x) (1 - p) ^ (x choose 2)` with `p ≈ (log n)^2/n`,
which tends to `0` for `x = ε n`. -/
theorem exists_bad_card_lt_and_indepNum_le {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ B ⊆ graphFamily n (girthEdgeCount n),
      2 * B.card < (graphFamily n (girthEdgeCount n)).card ∧
      ∀ E ∈ graphFamily n (girthEdgeCount n), E ∉ B →
        ((SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))).indepNum : ℝ) ≤ ε * n := by
  sorry

/-- The union bound combining the two halves of the random-graph step of Zhao, Theorem 3.4.1:
there is a graph on `n > 0` vertices whose cycles of length at most `l` all meet some set `S` of
at most `n / 2` vertices, and whose independence number is at most `ε n`. -/
theorem exists_shortCycleCover_and_indepNum_le (l : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (S : Finset (Fin n)),
      0 < n ∧ 2 * S.card ≤ n ∧
      (∀ (a : Fin n) (w : G.Walk a a), w.IsCycle → w.length ≤ l → ∃ v ∈ S, v ∈ w.support) ∧
      (G.indepNum : ℝ) ≤ ε * n := by
  obtain ⟨n₁, h₁⟩ := exists_bad_card_lt_and_shortCycleCover l
  obtain ⟨n₂, h₂⟩ := exists_bad_card_lt_and_indepNum_le hε
  obtain ⟨n, hn⟩ : ∃ n, n = max (max n₁ n₂) 1 := ⟨_, rfl⟩
  obtain ⟨B₁, hB₁sub, hB₁card, hB₁⟩ := h₁ n (by omega)
  obtain ⟨B₂, hB₂sub, hB₂card, hB₂⟩ := h₂ n (by omega)
  have hsub : B₁ ∪ B₂ ⊆ graphFamily n (girthEdgeCount n) := Finset.union_subset hB₁sub hB₂sub
  have hlt : (B₁ ∪ B₂).card < (graphFamily n (girthEdgeCount n)).card :=
    lt_of_le_of_lt (Finset.card_union_le _ _) (by omega)
  obtain ⟨E, hE, hEnot⟩ : ∃ E ∈ graphFamily n (girthEdgeCount n), E ∉ B₁ ∪ B₂ := by
    by_contra hcon
    have hss : graphFamily n (girthEdgeCount n) ⊆ B₁ ∪ B₂ := by
      intro F hF
      by_contra hFb
      exact hcon ⟨F, hF, hFb⟩
    exact absurd (Finset.card_le_card hss) (not_le.mpr hlt)
  obtain ⟨S, hScard, hcov⟩ := hB₁ E hE fun h => hEnot (Finset.mem_union_left _ h)
  exact ⟨n, SimpleGraph.fromEdgeSet _, S, by omega, hScard, hcov,
    hB₂ E hE fun h => hEnot (Finset.mem_union_right _ h)⟩

/-- **The alteration step** of Zhao, Theorem 3.4.1.  If every cycle of `G` of length at most `l`
meets `S`, then deleting `S` leaves a graph on `n - #S` vertices whose independence number is no
larger than that of `G`, and whose girth exceeds `l` as soon as it still contains a cycle. -/
theorem exists_girth_gt_and_indepNum_le_of_shortCycleCover {n l : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n))
    (hcov : ∀ (a : Fin n) (w : G.Walk a a), w.IsCycle → w.length ≤ l →
      ∃ v ∈ S, v ∈ w.support) :
    ∃ H : SimpleGraph (Fin (n - S.card)),
      H.indepNum ≤ G.indepNum ∧ (¬ H.IsAcyclic → (l : ℕ∞) < H.girth) := by
  have hcardT : Fintype.card ((Sᶜ : Finset (Fin n)) : Type) = n - S.card := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  let e : Fin (n - S.card) ≃ ((Sᶜ : Finset (Fin n)) : Type) :=
    (Fintype.equivFinOfCardEq hcardT).symm
  have hinj : Function.Injective (fun i : Fin (n - S.card) => ((e i : Fin n))) := by
    intro i j h
    exact e.injective (Subtype.ext h)
  let f : Fin (n - S.card) ↪ Fin n := ⟨_, hinj⟩
  have hfmem : ∀ i, f i ∉ S := by
    intro i
    have hi : (e i : Fin n) ∈ (Sᶜ : Finset (Fin n)) := (e i).2
    exact Finset.mem_compl.mp hi
  refine ⟨G.comap (f : Fin (n - S.card) → Fin n), ?_, ?_⟩
  · obtain ⟨t, ht⟩ := (G.comap (f : Fin (n - S.card) → Fin n)).exists_isNIndepSet_indepNum
    have h1 : G.IsIndepSet (t.image f) := by
      intro a ha b hb hab
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha hb
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨y, hy, rfl⟩ := hb
      have hxy : x ≠ y := fun h => hab (by rw [h])
      simpa using ht.isIndepSet hx hy hxy
    have h2 := h1.card_le_indepNum
    rwa [Finset.card_image_of_injective _ f.injective, ht.card_eq] at h2
  · intro hacy
    obtain ⟨a, w, hw, hgirth⟩ := SimpleGraph.exists_girth_eq_length.mpr hacy
    rw [hgirth]
    have hlt : l < w.length := by
      by_contra hle
      have hle' : w.length ≤ l := Nat.le_of_not_lt hle
      set F := SimpleGraph.Hom.comap (f : Fin (n - S.card) → Fin n) G with hF
      have hFinj : Function.Injective (F : Fin (n - S.card) → Fin n) := hinj
      have hWc : (w.map F).IsCycle := hw.map hFinj
      have hWl : (w.map F).length ≤ l := by rwa [SimpleGraph.Walk.length_map]
      obtain ⟨v, hvS, hvsupp⟩ := hcov (F a) (w.map F) hWc hWl
      rw [SimpleGraph.Walk.support_map] at hvsupp
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hvsupp
      exact hfmem x hvS
    exact_mod_cast hlt

/-- The random-graph half of Zhao, Theorem 3.4.1: for every `l` and every `m` there is a graph
whose girth exceeds `l` and whose independence number `α` satisfies `m * α < n`.

Erdős's construction takes `G ~ G(n, p)` with `p = (log n) ^ 2 / n`, deletes one vertex from each
cycle of length at most `l`, and bounds `α` by `3 n / log n`.  Note that `SimpleGraph.girth` is
valued in `ℕ` with junk value `0` on acyclic graphs, so the first conjunct also asserts that the
graph has a cycle. -/
theorem exists_girth_gt_and_mul_indepNum_lt (l m : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), (l : ℕ∞) < G.girth ∧ m * G.indepNum < n := by
  obtain ⟨M, hM⟩ : ∃ M, M = m + 2 := ⟨_, rfl⟩
  have hc : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  obtain ⟨n, G, S, hnpos, hS, hcov, hindep⟩ :=
    exists_shortCycleCover_and_indepNum_le l (ε := 1 / (2 * ((M : ℝ) + 1))) (by positivity)
  obtain ⟨H, hHi, hHg⟩ := exists_girth_gt_and_indepNum_le_of_shortCycleCover (l := l) G S hcov
  have hNn : n ≤ 2 * (n - S.card) := by omega
  have hNpos : 0 < n - S.card := by omega
  have hkey : (M + 1) * H.indepNum ≤ n - S.card := by
    have h1 : (H.indepNum : ℝ) ≤ (G.indepNum : ℝ) := by exact_mod_cast hHi
    have h2 : (n : ℝ) ≤ 2 * ((n - S.card : ℕ) : ℝ) := by
      simpa using (Nat.cast_le (α := ℝ)).mpr hNn
    have h3 : ((M : ℝ) + 1) * (G.indepNum : ℝ)
        ≤ ((M : ℝ) + 1) * (1 / (2 * ((M : ℝ) + 1)) * n) :=
      mul_le_mul_of_nonneg_left hindep hc.le
    have h4 : ((M : ℝ) + 1) * (1 / (2 * ((M : ℝ) + 1)) * n) = (n : ℝ) / 2 := by field_simp
    have h5 : ((M : ℝ) + 1) * (H.indepNum : ℝ) ≤ ((M : ℝ) + 1) * (G.indepNum : ℝ) :=
      mul_le_mul_of_nonneg_left h1 hc.le
    rw [h4] at h3
    have h7 : (((M + 1) * H.indepNum : ℕ) : ℝ) ≤ ((n - S.card : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h7
  have hMlt : M * H.indepNum < n - S.card := by
    rcases Nat.eq_zero_or_pos H.indepNum with h0 | h0
    · rw [h0, Nat.mul_zero]
      exact hNpos
    · have h9 : M * H.indepNum < (M + 1) * H.indepNum := by
        rw [add_mul, one_mul]
        exact Nat.lt_add_of_pos_right h0
      exact lt_of_lt_of_le h9 hkey
  have hacy : ¬ H.IsAcyclic := by
    intro hA
    have hcc := card_le_mul_indepNum_of_colorable H hA.colorable_two
    rw [Fintype.card_fin] at hcc
    have h2a : 2 * H.indepNum ≤ M * H.indepNum := Nat.mul_le_mul (by omega) (le_refl _)
    exact absurd (lt_of_le_of_lt h2a hMlt) (not_lt.mpr hcc)
  exact ⟨n - S.card, H, hHg hacy, lt_of_le_of_lt (Nat.mul_le_mul (by omega) (le_refl _)) hMlt⟩

/-- **Erdős 1959** (Zhao, Theorem 3.4.1): there are graphs of arbitrarily large girth and
arbitrarily large chromatic number — high chromatic number cannot be certified locally. -/
theorem exists_girth_gt_and_chromaticNumber_gt (k l : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      (l : ℕ∞) < G.girth ∧ (k : ℕ∞) < G.chromaticNumber := by
  obtain ⟨n, G, hgirth, hindep⟩ := exists_girth_gt_and_mul_indepNum_lt l k
  refine ⟨n, G, hgirth, ?_⟩
  by_contra hle
  rw [not_lt] at hle
  have hcard := card_le_mul_indepNum_of_colorable G
    (SimpleGraph.chromaticNumber_le_iff_colorable.mp hle)
  rw [Fintype.card_fin] at hcard
  omega

/-- **Radhakrishnan–Srinivasan 2000** (Zhao, Theorem 3.5.1): for some absolute constant `c > 0`,
every `k`-uniform hypergraph with at most `c * √(k / log k) * 2 ^ k` edges is 2-colourable.  This
is the best known lower bound on `m k`, and strengthens `twoColorable_of_card_lt`. -/
theorem exists_twoColorable_of_card_le :
    ∃ c : ℝ, 0 < c ∧ ∀ (α : Type) (_ : Fintype α) (_ : DecidableEq α) (k : ℕ), 2 ≤ k →
      ∀ H : Finset (Finset α), (∀ e ∈ H, e.card = k) →
        (H.card : ℝ) ≤ c * Real.sqrt (k / Real.log k) * 2 ^ k → TwoColorable H := by
  sorry

end ProbMethodCombinatorics
