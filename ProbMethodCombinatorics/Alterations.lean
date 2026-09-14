import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Constructions.Pi
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

section ShortCycleExpectation

/-- **The double count behind the expectation computation** of Zhao, Theorem 3.4.1.  Each vertex
of `shortCycleSupport l E` lies on a cycle of `SimpleGraph.fromEdgeSet E` of some length
`i` with `3 ≤ i ≤ l`; such a cycle is described by one of at most `n ^ i` tuples of vertices,
carries `i` vertices, and forces `i` distinct unordered pairs to lie in `E`.  At most
`(N - i).choose (M - i)` of the `M`-element subsets of the `N = Fintype.card (Sym2 (Fin n))`
unordered pairs contain `i` prescribed ones, so summing over the family gives this bound. -/
theorem sum_shortCycleSupport_card_le_cycleBound (l n M : ℕ) :
    ∑ E ∈ graphFamily n M, (shortCycleSupport l E).card
      ≤ ∑ i ∈ Finset.Icc 3 l,
          i * n ^ i * (Fintype.card (Sym2 (Fin n)) - i).choose (M - i) := by
  obtain ⟨ef, hef⟩ : ∃ ef : (i : ℕ) → (Fin i → Fin n) → Finset (Sym2 (Fin n)),
      ∀ (i : ℕ) (f : Fin i → Fin n), ef i f = Finset.image
        (fun k : Fin i => s(f k, f ⟨(k.val + 1) % i, Nat.mod_lt _ (Nat.zero_lt_of_lt k.isLt)⟩))
        Finset.univ := ⟨_, fun _ _ => rfl⟩
  obtain ⟨cyc, hcyc⟩ : ∃ cyc : (i : ℕ) → Finset (Sym2 (Fin n)) → Finset (Fin i → Fin n),
      ∀ (i : ℕ) (E : Finset (Sym2 (Fin n))), cyc i E =
        Finset.univ.filter (fun f => Function.Injective f ∧ ef i f ⊆ E) := ⟨_, fun _ _ => rfl⟩
  have cardEf : ∀ (i : ℕ), 3 ≤ i → ∀ f : Fin i → Fin n, Function.Injective f →
      (ef i f).card = i := by
    intro i hi3 f hf
    have hsucc : ∀ x : ℕ, x < i →
        ((x + 1) % i = 0 ∧ x + 1 = i) ∨ ((x + 1) % i = x + 1 ∧ x + 1 < i) := by
      intro x hx
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hx) with h | h
      · have h' : x + 1 = i := h
        exact Or.inl ⟨by rw [h', Nat.mod_self], h'⟩
      · exact Or.inr ⟨Nat.mod_eq_of_lt h, h⟩
    have hinj : Function.Injective
        (fun k : Fin i =>
          s(f k, f ⟨(k.val + 1) % i, Nat.mod_lt _ (Nat.zero_lt_of_lt k.isLt)⟩)) := by
      intro k₁ k₂ h
      simp only [Sym2.eq_iff] at h
      rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact hf h1
      · exfalso
        have v1 : (k₁ : ℕ) = ((k₂ : ℕ) + 1) % i := congrArg Fin.val (hf h1)
        have v2 : ((k₁ : ℕ) + 1) % i = (k₂ : ℕ) := congrArg Fin.val (hf h2)
        have b1 := k₁.isLt
        have b2 := k₂.isLt
        rcases hsucc (k₁ : ℕ) b1 with ⟨p1, q1⟩ | ⟨p1, q1⟩ <;>
          rcases hsucc (k₂ : ℕ) b2 with ⟨p2, q2⟩ | ⟨p2, q2⟩ <;>
          rw [p2] at v1 <;> rw [p1] at v2 <;> omega
    rw [hef, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have countSub : ∀ s : Finset (Sym2 (Fin n)),
      ((graphFamily n M).filter (fun E => s ⊆ E)).card
        ≤ (Fintype.card (Sym2 (Fin n)) - s.card).choose (M - s.card) := by
    intro s
    have hmap : ∀ E ∈ (graphFamily n M).filter (fun E => s ⊆ E),
        E \ s ∈ Finset.powersetCard (M - s.card) (Finset.univ \ s) := by
      intro E hE
      rw [graphFamily, Finset.mem_filter, Finset.mem_powersetCard] at hE
      obtain ⟨⟨_, hcard⟩, hsub⟩ := hE
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.sdiff_subset_sdiff (Finset.subset_univ E) le_rfl,
        by rw [Finset.card_sdiff_of_subset hsub, hcard]⟩
    have hinj : Set.InjOn (fun E => E \ s)
        (((graphFamily n M).filter (fun E => s ⊆ E)) : Finset _) := by
      intro E₁ h₁ E₂ h₂ h
      simp only [Finset.coe_filter] at h₁ h₂
      simp only at h
      have e₁ : E₁ \ s ∪ s = E₁ := Finset.sdiff_union_of_subset h₁.2
      have e₂ : E₂ \ s ∪ s = E₂ := Finset.sdiff_union_of_subset h₂.2
      rw [← e₁, ← e₂, h]
    calc ((graphFamily n M).filter (fun E => s ⊆ E)).card
        ≤ (Finset.powersetCard (M - s.card) (Finset.univ \ s)).card :=
          Finset.card_le_card_of_injOn _ hmap hinj
      _ = (Fintype.card (Sym2 (Fin n)) - s.card).choose (M - s.card) := by
          rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ s),
            Finset.card_univ]
  have step1 : ∀ E : Finset (Sym2 (Fin n)),
      (shortCycleSupport l E).card ≤ ∑ i ∈ Finset.Icc 3 l, i * (cyc i E).card := by
    intro E
    have hsub : shortCycleSupport l E ⊆ (Finset.Icc 3 l).biUnion
        (fun i => (cyc i E).biUnion (fun f => Finset.image f Finset.univ)) := by
      intro v hv
      rw [shortCycleSupport, Set.Finite.mem_toFinset] at hv
      obtain ⟨a, w, hcy, hlen, hvs⟩ := hv
      have h3 : 3 ≤ w.length := hcy.isCircuit.three_le_length
      set i := w.length with hi
      have hipos : 0 < i := by omega
      have hend : w.getVert i = w.getVert 0 := by rw [hi, w.getVert_length, w.getVert_zero]
      have hmod : ∀ m : ℕ, m ≤ i → w.getVert (m % i) = w.getVert m := by
        intro m hm
        rcases lt_or_eq_of_le hm with h | h
        · rw [Nat.mod_eq_of_lt h]
        · subst h; rw [Nat.mod_self, hend]
      refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_Icc.mpr ⟨h3, hlen⟩, ?_⟩
      refine Finset.mem_biUnion.mpr ⟨fun k : Fin i => w.getVert k.val, ?_, ?_⟩
      · rw [hcyc, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · intro k₁ k₂ h
          simp only at h
          have hk₁ : (k₁ : ℕ) < i := k₁.isLt
          have hk₂ : (k₂ : ℕ) < i := k₂.isLt
          have m1 : (k₁ : ℕ) ∈ {j : ℕ | j ≤ w.length - 1} := by
            simp only [Set.mem_ofPred_eq]; omega
          have m2 : (k₂ : ℕ) ∈ {j : ℕ | j ≤ w.length - 1} := by
            simp only [Set.mem_ofPred_eq]; omega
          exact Fin.ext (hcy.getVert_injOn' m1 m2 h)
        · rw [hef, Finset.image_subset_iff]
          intro k _
          have hk : (k : ℕ) < i := k.isLt
          have hadj := w.adj_getVert_succ (i := (k : ℕ)) (by omega)
          have hval : w.getVert (((k : ℕ) + 1) % i) = w.getVert ((k : ℕ) + 1) :=
            hmod _ (by omega)
          simp only [hval]
          rw [SimpleGraph.fromEdgeSet_adj] at hadj
          exact hadj.1
      · rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hvs
        obtain ⟨m, hm, hml⟩ := hvs
        refine Finset.mem_image.mpr ⟨⟨m % i, Nat.mod_lt _ hipos⟩, Finset.mem_univ _, ?_⟩
        simp only
        rw [hmod m hml, hm]
    calc (shortCycleSupport l E).card
        ≤ ((Finset.Icc 3 l).biUnion
            (fun i => (cyc i E).biUnion (fun f => Finset.image f Finset.univ))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ i ∈ Finset.Icc 3 l,
            ((cyc i E).biUnion (fun f => Finset.image f Finset.univ)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ i ∈ Finset.Icc 3 l, i * (cyc i E).card := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc ((cyc i E).biUnion (fun f => Finset.image f Finset.univ)).card
              ≤ ∑ _f ∈ cyc i E, (Finset.univ : Finset (Fin i)).card := by
                refine le_trans Finset.card_biUnion_le ?_
                exact Finset.sum_le_sum fun f _ => Finset.card_image_le
            _ = i * (cyc i E).card := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
  have step2 : ∀ i ∈ Finset.Icc 3 l,
      ∑ E ∈ graphFamily n M, (cyc i E).card
        ≤ n ^ i * (Fintype.card (Sym2 (Fin n)) - i).choose (M - i) := by
    intro i hi
    have hi3 : 3 ≤ i := (Finset.mem_Icc.mp hi).1
    calc ∑ E ∈ graphFamily n M, (cyc i E).card
        = ∑ E ∈ graphFamily n M,
            ∑ f ∈ Finset.univ.filter (fun f : Fin i → Fin n => Function.Injective f),
              (if ef i f ⊆ E then 1 else 0) := by
          refine Finset.sum_congr rfl fun E _ => ?_
          rw [hcyc, ← Finset.filter_filter, Finset.card_filter]
      _ = ∑ f ∈ Finset.univ.filter (fun f : Fin i → Fin n => Function.Injective f),
            ∑ E ∈ graphFamily n M, (if ef i f ⊆ E then 1 else 0) := Finset.sum_comm
      _ = ∑ f ∈ Finset.univ.filter (fun f : Fin i → Fin n => Function.Injective f),
            ((graphFamily n M).filter (fun E => ef i f ⊆ E)).card :=
          Finset.sum_congr rfl fun f _ => (Finset.card_filter _ _).symm
      _ ≤ ∑ _f ∈ Finset.univ.filter (fun f : Fin i → Fin n => Function.Injective f),
            (Fintype.card (Sym2 (Fin n)) - i).choose (M - i) := by
          refine Finset.sum_le_sum fun f hf => ?_
          have hfi : Function.Injective f := (Finset.mem_filter.mp hf).2
          have hcount := countSub (ef i f)
          rwa [cardEf i hi3 f hfi] at hcount
      _ = (Finset.univ.filter (fun f : Fin i → Fin n => Function.Injective f)).card
            * (Fintype.card (Sym2 (Fin n)) - i).choose (M - i) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ n ^ i * (Fintype.card (Sym2 (Fin n)) - i).choose (M - i) := by
          refine Nat.mul_le_mul_right _ ?_
          refine le_trans (Finset.card_filter_le _ _) ?_
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  calc ∑ E ∈ graphFamily n M, (shortCycleSupport l E).card
      ≤ ∑ E ∈ graphFamily n M, ∑ i ∈ Finset.Icc 3 l, i * (cyc i E).card :=
        Finset.sum_le_sum fun E _ => step1 E
    _ = ∑ i ∈ Finset.Icc 3 l, i * ∑ E ∈ graphFamily n M, (cyc i E).card := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ i ∈ Finset.Icc 3 l,
          i * (n ^ i * (Fintype.card (Sym2 (Fin n)) - i).choose (M - i)) :=
        Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ (step2 i hi)
    _ = ∑ i ∈ Finset.Icc 3 l,
          i * n ^ i * (Fintype.card (Sym2 (Fin n)) - i).choose (M - i) :=
        Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm

/-- The ratio `(a choose b) / ((a + i) choose (b + i))` is the falling factorial
`b (b - 1) ⋯ (b - i + 1) / (a + i) ⋯ (a + 1)`, so it is at most `((b + i) / a) ^ i`.  This is
the division-free form, the crude estimate `ℙ(i prescribed pairs are all sampled) ≤ (M / N) ^ i`
used in the expectation computation of Zhao, Theorem 3.4.1. -/
theorem choose_mul_pow_le_choose_add_mul_pow (a b i : ℕ) :
    a.choose b * a ^ i ≤ (a + i).choose (b + i) * (b + i) ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have key : (a + i + 1) * (a + i).choose (b + i)
        = (a + (i + 1)).choose (b + (i + 1)) * (b + (i + 1)) := by
      have h := Nat.add_one_mul_choose_eq (a + i) (b + i)
      simpa [Nat.add_assoc] using h
    calc a.choose b * a ^ (i + 1) = a.choose b * a ^ i * a := by ring
      _ ≤ a.choose b * a ^ i * (a + i + 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ (a + i).choose (b + i) * (b + i) ^ i * (a + i + 1) := Nat.mul_le_mul_right _ ih
      _ = (a + i + 1) * (a + i).choose (b + i) * (b + i) ^ i := by ring
      _ = (a + (i + 1)).choose (b + (i + 1)) * (b + (i + 1)) * (b + i) ^ i := by rw [key]
      _ ≤ (a + (i + 1)).choose (b + (i + 1)) * (b + (i + 1)) * (b + (i + 1)) ^ i :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) i)
      _ = (a + (i + 1)).choose (b + (i + 1)) * (b + (i + 1)) ^ (i + 1) := by ring

/-- Any fixed power of `log n` is eventually beaten by `n`, with any constant in front.  This is
`(log n) ^ k = o(n)`, the only analytic input to the expectation computation of Zhao,
Theorem 3.4.1. -/
theorem exists_mul_pow_log_lt (c : ℝ) (k : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → c * Real.log n ^ k < n := by
  have h : (fun x : ℝ => c * Real.log x ^ k) =o[Filter.atTop] id :=
    Real.isLittleO_pow_log_id_atTop.const_mul_left c
  have h2 := h.def (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨a, ha⟩ := (h2.and (Filter.eventually_gt_atTop (0 : ℝ))).exists_forall_of_atTop
  refine ⟨⌈a⌉₊ + 1, fun n hn => ?_⟩
  have hna : a ≤ (n : ℝ) := by
    have h1 : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
    have h3 : ((⌈a⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.le_of_succ_le hn
    linarith
  obtain ⟨hb, hpos⟩ := ha (n : ℝ) hna
  simp only [Real.norm_eq_abs, id_eq, abs_of_pos hpos] at hb
  have hle := le_abs_self (c * Real.log (n : ℝ) ^ k)
  linarith

end ShortCycleExpectation

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
  obtain ⟨n₁, hn₁⟩ := exists_mul_pow_log_lt (4 * (l : ℝ) ^ 2 * 8 ^ l) (2 * l)
  obtain ⟨n₂, hn₂⟩ := exists_mul_pow_log_lt 4 2
  refine ⟨max (max n₁ n₂) (l + 4), fun n hn => ?_⟩
  have hgen1 : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hgen2 : n₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hgen3 : l + 4 ≤ n := le_trans (le_max_right _ _) hn
  have hA := sum_shortCycleSupport_card_le_cycleBound l n (girthEdgeCount n)
  have hfam : ((graphFamily n (girthEdgeCount n)).card : ℝ)
      = (((Fintype.card (Sym2 (Fin n))).choose (girthEdgeCount n) : ℕ) : ℝ) := by
    rw [graphFamily, Finset.card_powersetCard, Finset.card_univ]
  have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 4 ≤ n)
  have hlR : (l : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : l ≤ n)
  set L : ℝ := Real.log n with hLdef
  set M : ℕ := girthEdgeCount n with hMdef
  set N : ℕ := Fintype.card (Sym2 (Fin n)) with hNdef
  have hsmall : 4 * L ^ 2 < (n : ℝ) := by rw [hLdef]; exact hn₂ n hgen2
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv] at h
    linarith
  have hL1 : (1 : ℝ) ≤ L := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have hmono := Real.log_le_log (show (0 : ℝ) < 4 by norm_num) hn4
    rw [h4] at hmono
    rw [hLdef]
    linarith
  have hMub : (M : ℝ) < (n : ℝ) * L ^ 2 + 1 := by
    rw [hMdef, girthEdgeCount, ← hLdef]; exact Nat.ceil_lt_add_one (by positivity)
  have hMlb : (n : ℝ) * L ^ 2 ≤ (M : ℝ) := by
    rw [hMdef, girthEdgeCount, ← hLdef]; exact Nat.le_ceil _
  have hN2 : 2 * N = n * (n + 1) := by
    rw [hNdef, Sym2.card, Fintype.card_fin]
    have h := Nat.add_one_mul_choose_eq n 1
    rw [Nat.choose_one_right] at h
    calc 2 * (n + 1).choose 2 = (n + 1).choose 2 * 2 := by ring
      _ = (n + 1) * n := h.symm
      _ = n * (n + 1) := by ring
  have hNR : (n : ℝ) ^ 2 ≤ 2 * (N : ℝ) := by
    have hc : (2 : ℝ) * (N : ℝ) = (n : ℝ) * ((n : ℝ) + 1) := by exact_mod_cast hN2
    nlinarith
  have hL2 : (1 : ℝ) ≤ L ^ 2 := by nlinarith
  have hnsq : 4 * (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hn16 : (16 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hnL2 : (n : ℝ) ≤ (n : ℝ) * L ^ 2 := by nlinarith
  have h4nL : 4 * ((n : ℝ) * L ^ 2) < (n : ℝ) ^ 2 := by nlinarith
  have hlM : l ≤ M := by
    have hcast : (l : ℝ) ≤ (M : ℝ) := by linarith
    exact_mod_cast hcast
  have hlN : l ≤ N := by
    have hcast : (l : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast hcast
  have hMN : M ≤ N := by
    have hcast : (M : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast hcast
  have hDpos : (0 : ℝ) < ((N.choose M : ℕ) : ℝ) := by exact_mod_cast Nat.choose_pos hMN
  have hterm : ∀ i ∈ Finset.Icc 3 l,
      ((i * n ^ i * ((N - i).choose (M - i)) : ℕ) : ℝ)
        ≤ ((N.choose M : ℕ) : ℝ) * ((l : ℝ) * (8 * L ^ 2) ^ l) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hil : i ≤ l := hi.2
    have hiN : i ≤ N := le_trans hil hlN
    have hiM : i ≤ M := le_trans hil hlM
    have hilR : (i : ℝ) ≤ (l : ℝ) := by exact_mod_cast hil
    have hiR : (i : ℝ) ≤ (n : ℝ) := le_trans hilR hlR
    have hNi : (n : ℝ) ^ 2 / 4 ≤ (N : ℝ) - (i : ℝ) := by linarith
    have hpos : (0 : ℝ) < (N : ℝ) - (i : ℝ) := by nlinarith
    have ht1 : (1 : ℝ) ≤ 8 * L ^ 2 := by linarith
    have hB := choose_mul_pow_le_choose_add_mul_pow (N - i) (M - i) i
    rw [Nat.sub_add_cancel hiN, Nat.sub_add_cancel hiM] at hB
    have hBR : (((N - i).choose (M - i) : ℕ) : ℝ) * ((N : ℝ) - (i : ℝ)) ^ i
        ≤ ((N.choose M : ℕ) : ℝ) * (M : ℝ) ^ i := by
      have hc : (((N - i : ℕ) : ℝ)) = (N : ℝ) - (i : ℝ) := by rw [Nat.cast_sub hiN]
      calc (((N - i).choose (M - i) : ℕ) : ℝ) * ((N : ℝ) - (i : ℝ)) ^ i
          = (((N - i).choose (M - i) * (N - i) ^ i : ℕ) : ℝ) := by push_cast [hc]; ring
        _ ≤ ((N.choose M * M ^ i : ℕ) : ℝ) := by exact_mod_cast hB
        _ = ((N.choose M : ℕ) : ℝ) * (M : ℝ) ^ i := by push_cast; ring
    have hnM : (n : ℝ) * (M : ℝ) ≤ (8 * L ^ 2) * ((N : ℝ) - (i : ℝ)) := by nlinarith
    have h3 : (0 : ℝ) ≤ ((N : ℝ) - (i : ℝ)) ^ i := by positivity
    have hstep : ((n : ℝ) * (M : ℝ)) ^ i ≤ (8 * L ^ 2) ^ l * ((N : ℝ) - (i : ℝ)) ^ i := by
      have h1 : ((n : ℝ) * (M : ℝ)) ^ i ≤ (8 * L ^ 2) ^ i * ((N : ℝ) - (i : ℝ)) ^ i := by
        rw [← mul_pow]; gcongr
      exact le_trans h1 (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ht1 hil) h3)
    have hkey : ((i : ℝ) * (n : ℝ) ^ i * (((N - i).choose (M - i) : ℕ) : ℝ))
        * ((N : ℝ) - (i : ℝ)) ^ i
        ≤ (((N.choose M : ℕ) : ℝ) * ((l : ℝ) * (8 * L ^ 2) ^ l))
          * ((N : ℝ) - (i : ℝ)) ^ i := by
      have hAe : ((i : ℝ) * (n : ℝ) ^ i * (((N - i).choose (M - i) : ℕ) : ℝ))
          * ((N : ℝ) - (i : ℝ)) ^ i
          = (i : ℝ) * (n : ℝ) ^ i
            * ((((N - i).choose (M - i) : ℕ) : ℝ) * ((N : ℝ) - (i : ℝ)) ^ i) := by ring
      rw [hAe]
      refine le_trans (mul_le_mul_of_nonneg_left hBR (by positivity)) ?_
      have hEq : (i : ℝ) * (n : ℝ) ^ i * (((N.choose M : ℕ) : ℝ) * (M : ℝ) ^ i)
          = ((N.choose M : ℕ) : ℝ) * ((i : ℝ) * ((n : ℝ) * (M : ℝ)) ^ i) := by
        rw [mul_pow]; ring
      have hEq2 : (((N.choose M : ℕ) : ℝ) * ((l : ℝ) * (8 * L ^ 2) ^ l))
          * ((N : ℝ) - (i : ℝ)) ^ i
          = ((N.choose M : ℕ) : ℝ)
            * ((l : ℝ) * ((8 * L ^ 2) ^ l * ((N : ℝ) - (i : ℝ)) ^ i)) := by ring
      rw [hEq, hEq2]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hpow0 : (0 : ℝ) ≤ ((n : ℝ) * (M : ℝ)) ^ i := by positivity
      have hlast : (0 : ℝ) ≤ (8 * L ^ 2) ^ l * ((N : ℝ) - (i : ℝ)) ^ i := by positivity
      have hi0 : (0 : ℝ) ≤ (i : ℝ) := by positivity
      nlinarith
    have hfin := le_of_mul_le_mul_right hkey (pow_pos hpos i)
    calc ((i * n ^ i * ((N - i).choose (M - i)) : ℕ) : ℝ)
        = (i : ℝ) * (n : ℝ) ^ i * (((N - i).choose (M - i) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((N.choose M : ℕ) : ℝ) * ((l : ℝ) * (8 * L ^ 2) ^ l) := hfin
  have hcast : ∑ E ∈ graphFamily n M, ((shortCycleSupport l E).card : ℝ)
      ≤ ∑ i ∈ Finset.Icc 3 l, ((i * n ^ i * ((N - i).choose (M - i)) : ℕ) : ℝ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum]
    exact_mod_cast hA
  have hsum := Finset.sum_le_card_nsmul (Finset.Icc 3 l)
    (fun i => ((i * n ^ i * ((N - i).choose (M - i)) : ℕ) : ℝ))
    (((N.choose M : ℕ) : ℝ) * ((l : ℝ) * (8 * L ^ 2) ^ l)) hterm
  rw [nsmul_eq_mul] at hsum
  have hcardIcc : (((Finset.Icc 3 l).card : ℕ) : ℝ) ≤ (l : ℝ) := by
    rw [Nat.card_Icc]
    exact_mod_cast (by omega : l + 1 - 3 ≤ l)
  have hB0 : (0 : ℝ) ≤ ((N.choose M : ℕ) : ℝ) * ((l : ℝ) * (8 * L ^ 2) ^ l) := by positivity
  have htotal : ∑ E ∈ graphFamily n M, ((shortCycleSupport l E).card : ℝ)
      ≤ (l : ℝ) * (((N.choose M : ℕ) : ℝ) * ((l : ℝ) * (8 * L ^ 2) ^ l)) :=
    le_trans hcast (le_trans hsum (mul_le_mul_of_nonneg_right hcardIcc hB0))
  have hlog : (4 * (l : ℝ) ^ 2 * 8 ^ l) * L ^ (2 * l) < (n : ℝ) := by
    rw [hLdef]; exact hn₁ n hgen1
  have htl : (8 * L ^ 2) ^ l = 8 ^ l * L ^ (2 * l) := by rw [mul_pow, pow_mul]
  rw [hfam]
  calc 4 * ∑ E ∈ graphFamily n M, ((shortCycleSupport l E).card : ℝ)
      ≤ 4 * ((l : ℝ) * (((N.choose M : ℕ) : ℝ) * ((l : ℝ) * (8 * L ^ 2) ^ l))) := by linarith
    _ = ((N.choose M : ℕ) : ℝ) * ((4 * (l : ℝ) ^ 2 * 8 ^ l) * L ^ (2 * l)) := by rw [htl]; ring
    _ < ((N.choose M : ℕ) : ℝ) * (n : ℝ) := mul_lt_mul_of_pos_left hlog hDpos
    _ = (n : ℝ) * ((N.choose M : ℕ) : ℝ) := by ring

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

/-- The ratio `(T - c).choose M / T.choose M` is at most `((T - M) / T) ^ c`, in division-free
form.  This is the counting form of the estimate
`ℙ(a uniform M-element subset of a T-element set misses c prescribed elements) ≤ (1 - M / T) ^ c`
used in the union bound of Zhao, Theorem 3.4.1. -/
theorem choose_sub_mul_pow_le_choose_mul_pow (T M : ℕ) : ∀ c ≤ T,
    (T - c).choose M * T ^ c ≤ T.choose M * (T - M) ^ c := by
  intro c
  induction c with
  | zero => simp
  | succ c ih =>
    intro hc
    have hcT : c ≤ T := Nat.le_of_succ_le hc
    have ih' := ih hcT
    have key : (T - (c + 1)).choose M * (T - c) = (T - c).choose M * ((T - c) - M) := by
      have h := Nat.choose_mul_succ_eq (T - (c + 1)) M
      have he : T - (c + 1) + 1 = T - c := by omega
      rwa [he] at h
    have hmul : (T - c - M) * T ≤ (T - M) * (T - c) := by
      rcases le_or_gt (T - c) M with h | h
      · simp [Nat.sub_eq_zero_of_le h]
      · obtain ⟨u, hu⟩ : ∃ u, u = T - c - M := ⟨_, rfl⟩
        have h1 : T - c = u + M := by omega
        have h2 : T - M = u + c := by omega
        have h3 : T = u + M + c := by omega
        rw [← hu, h1, h2, h3]
        nlinarith
    refine Nat.le_of_mul_le_mul_right ?_ (show 0 < T - c by omega)
    calc (T - (c + 1)).choose M * T ^ (c + 1) * (T - c)
        = ((T - (c + 1)).choose M * (T - c)) * T ^ (c + 1) := by ring
      _ = ((T - c).choose M * ((T - c) - M)) * T ^ (c + 1) := by rw [key]
      _ = ((T - c).choose M * T ^ c) * (((T - c) - M) * T) := by ring
      _ ≤ (T.choose M * (T - M) ^ c) * (((T - c) - M) * T) := Nat.mul_le_mul_right _ ih'
      _ ≤ (T.choose M * (T - M) ^ c) * ((T - M) * (T - c)) := Nat.mul_le_mul_left _ hmul
      _ = T.choose M * (T - M) ^ (c + 1) * (T - c) := by ring

/-- The exponential beats the union bound: if `c M > (k + 1) T` then
`2 ^ (k + 1) (1 - M / T) ^ c < 1`, here in division-free form.  The two estimates are
`1 - M / T ≤ exp (-M / T)` and `2 ≤ exp 1`. -/
theorem two_pow_mul_pow_sub_lt_pow {T M c k : ℕ} (hMT : M ≤ T) (hTpos : 0 < T)
    (hkey : ((k : ℝ) + 1) * (T : ℝ) < (c : ℝ) * (M : ℝ)) :
    2 ^ (k + 1) * (T - M) ^ c < T ^ c := by
  have hTposR : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hTpos
  have hMTR : (M : ℝ) ≤ (T : ℝ) := by exact_mod_cast hMT
  have hR : (2 : ℝ) ^ (k + 1) * ((T : ℝ) - (M : ℝ)) ^ c < (T : ℝ) ^ c := by
    have hr : (0 : ℝ) ≤ 1 - (M : ℝ) / (T : ℝ) := by
      have := div_le_one_of_le₀ hMTR (le_of_lt hTposR)
      linarith
    have hexp1 : (1 - (M : ℝ) / (T : ℝ)) ^ c
        ≤ Real.exp (-((c : ℝ) * ((M : ℝ) / (T : ℝ)))) := by
      calc (1 - (M : ℝ) / (T : ℝ)) ^ c ≤ (Real.exp (-((M : ℝ) / (T : ℝ)))) ^ c := by
            refine pow_le_pow_left₀ hr ?_ c
            linarith [Real.add_one_le_exp (-((M : ℝ) / (T : ℝ)))]
        _ = Real.exp (-((c : ℝ) * ((M : ℝ) / (T : ℝ)))) := by
            rw [← Real.exp_nat_mul]; ring_nf
    have h2e : (2 : ℝ) ^ (k + 1) ≤ Real.exp ((k : ℝ) + 1) := by
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      calc (2 : ℝ) ^ (k + 1) ≤ (Real.exp 1) ^ (k + 1) := pow_le_pow_left₀ (by norm_num) h2 _
        _ = Real.exp ((k : ℝ) + 1) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have hsplit : ((T : ℝ) - (M : ℝ)) ^ c = (T : ℝ) ^ c * (1 - (M : ℝ) / (T : ℝ)) ^ c := by
      rw [← mul_pow]
      congr 1
      field_simp
    calc (2 : ℝ) ^ (k + 1) * ((T : ℝ) - (M : ℝ)) ^ c
        = (2 : ℝ) ^ (k + 1) * ((T : ℝ) ^ c * (1 - (M : ℝ) / (T : ℝ)) ^ c) := by rw [hsplit]
      _ ≤ Real.exp ((k : ℝ) + 1)
          * ((T : ℝ) ^ c * Real.exp (-((c : ℝ) * ((M : ℝ) / (T : ℝ))))) := by gcongr
      _ = (T : ℝ) ^ c * Real.exp (((k : ℝ) + 1) + -((c : ℝ) * ((M : ℝ) / (T : ℝ)))) := by
          rw [Real.exp_add ((k : ℝ) + 1) (-((c : ℝ) * ((M : ℝ) / (T : ℝ))))]; ring
      _ < (T : ℝ) ^ c * 1 := by
          refine mul_lt_mul_of_pos_left ?_ (pow_pos hTposR c)
          refine Real.exp_lt_one_iff.mpr ?_
          have hdiv : ((k : ℝ) + 1) < (c : ℝ) * ((M : ℝ) / (T : ℝ)) := by
            rw [← mul_div_assoc, lt_div_iff₀ hTposR]
            exact hkey
          linarith
      _ = (T : ℝ) ^ c := mul_one _
  have hcast : (((2 : ℕ) ^ (k + 1) * (T - M) ^ c : ℕ) : ℝ) < ((T ^ c : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hMT]
    exact hR
  exact_mod_cast hcast

/-- The union bound: a set covered by `k.choose x` pieces of `(T - c).choose M` members each is
less than half of `T.choose M`, as soon as the exponential estimate
`two_pow_mul_pow_sub_lt_pow` holds. -/
theorem two_mul_lt_choose_of_le_mul_choose {T M c x k b : ℕ} (hcT : c ≤ T) (hMT : M ≤ T)
    (hb : b ≤ k.choose x * ((T - c).choose M))
    (hfin : 2 ^ (k + 1) * (T - M) ^ c < T ^ c) :
    2 * b < T.choose M := by
  refine lt_of_mul_lt_mul_right ?_ (Nat.zero_le (T ^ c))
  have h1 : 2 * k.choose x ≤ 2 ^ (k + 1) := by
    have h := Nat.choose_le_two_pow k x
    calc 2 * k.choose x ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 h
      _ = 2 ^ (k + 1) := by ring
  calc 2 * b * T ^ c
      ≤ 2 * (k.choose x * ((T - c).choose M)) * T ^ c :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hb)
    _ = (2 * k.choose x) * ((T - c).choose M * T ^ c) := by ring
    _ ≤ (2 * k.choose x) * (T.choose M * (T - M) ^ c) :=
        Nat.mul_le_mul_left _ (choose_sub_mul_pow_le_choose_mul_pow T M c hcT)
    _ = T.choose M * (2 * k.choose x * (T - M) ^ c) := by ring
    _ ≤ T.choose M * (2 ^ (k + 1) * (T - M) ^ c) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h1)
    _ < T.choose M * T ^ c := mul_lt_mul_of_pos_left hfin (Nat.choose_pos hMT)

/-- Sending an ordered pair of distinct elements to the unordered pair it spans is two-to-one, so
a set of `x` elements spans at least `x (x - 1) / 2` unordered pairs of distinct elements. -/
theorem card_offDiag_le_two_mul_card_image {α : Type*} [DecidableEq α] (S : Finset α) :
    S.offDiag.card ≤ 2 * (S.offDiag.image (fun p : α × α => s(p.1, p.2))).card := by
  refine Finset.card_le_mul_card_image _ 2 ?_
  intro z hz
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
  have hsub : {q ∈ S.offDiag | s(q.1, q.2) = s(p.1, p.2)}
      ⊆ ({p, (p.2, p.1)} : Finset (α × α)) := by
    intro q hq
    have hq2 : s(q.1, q.2) = s(p.1, p.2) := (Finset.mem_filter.mp hq).2
    rw [Sym2.eq_iff] at hq2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hq2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr (Prod.ext h1 h2)
  exact le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_insert_le _ _) (by simp))

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
  suffices h : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ B ⊆ graphFamily n (girthEdgeCount n),
        2 * B.card < (graphFamily n (girthEdgeCount n)).card ∧
        ∀ E ∈ graphFamily n (girthEdgeCount n), E ∉ B →
          ((SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))).indepNum : ℝ) ≤ δ * n by
    obtain ⟨n₀, hn₀⟩ := h (min ε 1) (lt_min hε one_pos) (min_le_right _ _)
    refine ⟨n₀, fun n hn => ?_⟩
    obtain ⟨B, hBsub, hBcard, hB⟩ := hn₀ n hn
    exact ⟨B, hBsub, hBcard, fun E hE hEB =>
      le_trans (hB E hE hEB) (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg n))⟩
  clear hε ε
  intro δ hδ hδ1
  obtain ⟨n₂, hn₂⟩ := exists_mul_pow_log_lt 4 2
  refine ⟨max (max n₂ 4) (max ⌈Real.exp (8 / δ)⌉₊ ⌈4 / δ⌉₊), fun n hn => ?_⟩
  have hgen2 : n₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn4 : 4 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hgen3 : ⌈Real.exp (8 / δ)⌉₊ ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hgen4 : ⌈4 / δ⌉₊ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  obtain ⟨M, hMdef⟩ : ∃ M, M = girthEdgeCount n := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T, T = Fintype.card (Sym2 (Fin n)) := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log n := ⟨_, rfl⟩
  rw [← hMdef]
  -- estimates on the number of edges `M` and the number `T` of unordered pairs
  have hn4R : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsmall : 4 * L ^ 2 < (n : ℝ) := by rw [hLdef]; exact hn₂ n hgen2
  have hMub : (M : ℝ) < (n : ℝ) * L ^ 2 + 1 := by
    rw [hMdef, girthEdgeCount, ← hLdef]; exact Nat.ceil_lt_add_one (by positivity)
  have hMlb : (n : ℝ) * L ^ 2 ≤ (M : ℝ) := by
    rw [hMdef, girthEdgeCount, ← hLdef]; exact Nat.le_ceil _
  have hLlb : 8 / δ ≤ L := by
    have h1 : Real.exp (8 / δ) ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hgen3)
    rw [hLdef]
    exact (Real.le_log_iff_exp_le hnpos).mpr h1
  have hδL : 8 ≤ δ * L := by rw [div_le_iff₀ hδ] at hLlb; linarith
  have hδn : 4 ≤ δ * (n : ℝ) := by
    have h1 : 4 / δ ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hgen4)
    rw [div_le_iff₀ hδ] at h1; linarith
  have hT2 : 2 * T = n * (n + 1) := by
    rw [hTdef, Sym2.card, Fintype.card_fin]
    have h := Nat.add_one_mul_choose_eq n 1
    rw [Nat.choose_one_right] at h
    calc 2 * (n + 1).choose 2 = (n + 1).choose 2 * 2 := by ring
      _ = (n + 1) * n := h.symm
      _ = n * (n + 1) := by ring
  have hT2R : 2 * (T : ℝ) = (n : ℝ) * ((n : ℝ) + 1) := by exact_mod_cast hT2
  have hTpos : 0 < T := by
    have h : 0 < n * (n + 1) := by positivity
    omega
  have hTposR : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hTpos
  have hMT : M ≤ T := by
    have hc : (M : ℝ) ≤ (T : ℝ) := by nlinarith
    exact_mod_cast hc
  -- `x` is the size of the candidate independent sets, `c` a lower bound for the number of
  -- unordered pairs of distinct vertices inside one of them
  obtain ⟨x, hxdef⟩ : ∃ x, x = ⌈δ * (n : ℝ)⌉₊ := ⟨_, rfl⟩
  have hxlb : δ * (n : ℝ) ≤ (x : ℝ) := by rw [hxdef]; exact Nat.le_ceil _
  have hxub : (x : ℝ) < δ * (n : ℝ) + 1 := by
    rw [hxdef]; exact Nat.ceil_lt_add_one (by positivity)
  have hxn : x ≤ n := by
    rw [hxdef]
    exact Nat.ceil_le.mpr (by nlinarith)
  have hx4 : (4 : ℝ) ≤ (x : ℝ) := le_trans hδn hxlb
  obtain ⟨A, hA⟩ : ∃ A, A = x * x := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = n * n := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c, c = (A - x) / 2 := ⟨_, rfl⟩
  have hAP : A ≤ P := by rw [hA, hP]; exact Nat.mul_le_mul hxn hxn
  have hT2' : 2 * T = P + n := by rw [hP, hT2]; ring
  have hcT : c ≤ T := by omega
  have hAc : A ≤ 2 * c + x + 1 := by omega
  have hAcR : (x : ℝ) * (x : ℝ) ≤ 2 * (c : ℝ) + (x : ℝ) + 1 := by
    have h : (A : ℝ) ≤ 2 * (c : ℝ) + (x : ℝ) + 1 := by exact_mod_cast hAc
    rw [hA] at h; push_cast at h; linarith
  -- `K S` is the set of unordered pairs of distinct vertices of `S`
  obtain ⟨K, hK⟩ : ∃ K : Finset (Fin n) → Finset (Sym2 (Fin n)),
      ∀ S : Finset (Fin n), K S = S.offDiag.image (fun p : Fin n × Fin n => s(p.1, p.2)) :=
    ⟨_, fun _ => rfl⟩
  have hcK : ∀ S : Finset (Fin n), S.card = x → c ≤ (K S).card := by
    intro S hS
    have h : S.card * S.card - S.card ≤ 2 * (K S).card := by
      rw [hK, ← Finset.offDiag_card]
      exact card_offDiag_le_two_mul_card_image S
    rw [hS, ← hA] at h
    omega
  refine ⟨(Finset.univ.powersetCard x).biUnion
    (fun S => Finset.powersetCard M (Finset.univ \ K S)), ?_, ?_, ?_⟩
  · refine Finset.biUnion_subset.mpr fun S _ => ?_
    rw [graphFamily]
    exact Finset.powersetCard_mono Finset.sdiff_subset
  · -- the union bound over the `n.choose x` candidate independent sets
    have hfam : (graphFamily n M).card = T.choose M := by
      rw [graphFamily, Finset.card_powersetCard, Finset.card_univ, hTdef]
    have hBcard : ((Finset.univ.powersetCard x).biUnion
        (fun S => Finset.powersetCard M (Finset.univ \ K S))).card
        ≤ n.choose x * ((T - c).choose M) := by
      refine le_trans Finset.card_biUnion_le ?_
      have hterm : ∀ S ∈ Finset.univ.powersetCard x,
          (Finset.powersetCard M (Finset.univ \ K S)).card ≤ (T - c).choose M := by
        intro S hS
        have hSc : S.card = x := (Finset.mem_powersetCard.mp hS).2
        rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ _),
          Finset.card_univ, ← hTdef]
        exact Nat.choose_le_choose _ (Nat.sub_le_sub_left (hcK S hSc) T)
      refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
      rw [smul_eq_mul, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    -- `c M / T` exceeds `n + 1`: the exponent beats the union bound by a wide margin
    have hkey : ((n : ℝ) + 1) * (T : ℝ) < (c : ℝ) * (M : ℝ) := by
      have hM64 : 64 * (n : ℝ) ≤ δ ^ 2 * (M : ℝ) := by
        have h1 : (64 : ℝ) ≤ (δ * L) ^ 2 := by nlinarith
        have h3 : δ ^ 2 * ((n : ℝ) * L ^ 2) ≤ δ ^ 2 * (M : ℝ) := by nlinarith [sq_nonneg δ]
        nlinarith
      have hc4 : δ ^ 2 * (n : ℝ) ^ 2 ≤ 4 * (c : ℝ) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hx4) (by linarith : (0 : ℝ) ≤ (x : ℝ) + 2)]
      have hcM : 16 * (n : ℝ) ^ 3 ≤ (c : ℝ) * (M : ℝ) := by
        have h1 : (δ ^ 2 * (n : ℝ) ^ 2) * (64 * (n : ℝ)) ≤ (4 * (c : ℝ)) * (δ ^ 2 * (M : ℝ)) :=
          mul_le_mul hc4 hM64 (by positivity) (by positivity)
        nlinarith [sq_nonneg δ, mul_pos hδ hδ]
      have hT3 : ((n : ℝ) + 1) * (T : ℝ) ≤ 2 * (n : ℝ) ^ 3 := by nlinarith
      have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
      linarith
    rw [hfam]
    exact two_mul_lt_choose_of_le_mul_choose hcT hMT hBcard
      (two_pow_mul_pow_sub_lt_pow hMT hTpos hkey)
  · -- outside the bad set no `x` vertices are independent
    intro E hE hEB
    have hEcard : E.card = M := by
      rw [graphFamily, Finset.mem_powersetCard] at hE
      exact hE.2
    have hmeet : ∀ S : Finset (Fin n), S.card = x → ∃ e ∈ E, e ∈ K S := by
      intro S hS
      have hSmem : S ∈ Finset.univ.powersetCard x :=
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩
      have hnot : E ∉ Finset.powersetCard M (Finset.univ \ K S) := fun h =>
        hEB (Finset.mem_biUnion.mpr ⟨S, hSmem, h⟩)
      have hnsub : ¬ (E ⊆ Finset.univ \ K S) := fun h =>
        hnot (Finset.mem_powersetCard.mpr ⟨h, hEcard⟩)
      have hd : ¬ Disjoint E (K S) := fun h =>
        hnsub (Finset.subset_sdiff.mpr ⟨Finset.subset_univ _, h⟩)
      obtain ⟨e, heE, heK⟩ := Finset.not_disjoint_iff.mp hd
      exact ⟨e, heE, heK⟩
    have hlt : (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))).indepNum < x := by
      rcases Nat.lt_or_ge (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))).indepNum x with h | h
      · exact h
      · exfalso
        obtain ⟨t, ht⟩ :=
          (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))).exists_isNIndepSet_indepNum
        obtain ⟨u, hut, hucard⟩ :=
          Finset.exists_subset_card_eq (show x ≤ t.card by rw [ht.card_eq]; exact h)
        obtain ⟨e, heE, heK⟩ := hmeet u hucard
        rw [hK, Finset.mem_image] at heK
        obtain ⟨p, hp, hpe⟩ := heK
        rw [Finset.mem_offDiag] at hp
        have hadj : (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))).Adj p.1 p.2 := by
          rw [SimpleGraph.fromEdgeSet_adj]
          refine ⟨?_, hp.2.2⟩
          have hmem : s(p.1, p.2) ∈ E := by rw [hpe]; exact heE
          exact Finset.mem_coe.mpr hmem
        exact ht.isIndepSet (Finset.mem_coe.mpr (hut hp.1)) (Finset.mem_coe.mpr (hut hp.2.1))
          hp.2.2 hadj
    have hltR : ((SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))).indepNum : ℝ) + 1
        ≤ (x : ℝ) := by exact_mod_cast hlt
    linarith

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

section GreedyColoring

/-- A *conflicting pair* for the vertex weights `w`: edges `e` and `f` sharing a vertex `v` whose
weight is largest in `e` and smallest in `f`.

Pluhár's greedy colouring visits the vertices in increasing order of weight and colours each one
blue unless that would complete an all-blue edge; it leaves an edge monochromatic only when the
hypergraph has a conflicting pair. -/
def ConflictingPair {α : Type*} (w : α → ℝ) (e f : Finset α) (v : α) : Prop :=
  v ∈ e ∧ v ∈ f ∧ (∀ u ∈ e, w u ≤ w v) ∧ (∀ u ∈ f, w v ≤ w u)

/-- **Correctness of the greedy colouring** (Pluhár; the combinatorial half of Zhao,
Theorem 3.5.1).  A hypergraph with no empty edge whose vertex weights admit no conflicting pair
is 2-colourable.

Colour the vertices in increasing order of weight, each one blue unless that would make some edge
all blue, in which case red.  No edge is then all blue, because the greedy rule refuses the blue
at its heaviest vertex.  If some edge `f` were all red, its lightest vertex `v` was refused the
blue by an edge `e` all of whose other vertices are lighter than `v`, and then `e`, `f`, `v` is a
conflicting pair. -/
theorem twoColorable_of_no_conflictingPair {α : Type*} [Fintype α] [DecidableEq α]
    {H : Finset (Finset α)} (hne : ∀ e ∈ H, e.Nonempty) (w : α → ℝ)
    (hw : ∀ e ∈ H, ∀ f ∈ H, ∀ v : α, ¬ ConflictingPair w e f v) :
    TwoColorable H := by
  -- Colour a `w`-downward-closed prefix `S` greedily: no edge inside `S` is all blue, and every
  -- red vertex of `S` is the heaviest vertex of some edge.
  have key : ∀ S : Finset α, ∃ c : α → Bool,
      (∀ e ∈ H, e ⊆ S → ∃ u ∈ e, c u = false) ∧
      (∀ v ∈ S, c v = false → ∃ e ∈ H, v ∈ e ∧ ∀ u ∈ e, w u ≤ w v) := by
    intro S
    induction S using Finset.strongInduction with
    | _ S ih =>
      rcases S.eq_empty_or_nonempty with rfl | hS
      · refine ⟨fun _ => true, ?_, ?_⟩
        · intro e he hsub
          obtain ⟨x, hx⟩ := hne e he
          exact absurd (hsub hx) (by simp)
        · intro v hv
          simp at hv
      · obtain ⟨v, hvS, hvmax⟩ := Finset.exists_max_image S w hS
        obtain ⟨c, hA, hB⟩ := ih (S.erase v) (Finset.erase_ssubset hvS)
        have hrest : ∀ e : Finset α, e ⊆ S → v ∉ e → e ⊆ S.erase v :=
          fun e hsub hve x hx =>
          Finset.mem_erase.2 ⟨fun h => hve (h ▸ hx), hsub hx⟩
        by_cases hred : ∃ e ∈ H, v ∈ e ∧ e ⊆ S ∧ ∀ u ∈ e, u ≠ v → c u = true
        · refine ⟨fun u => if u = v then false else c u, ?_, ?_⟩
          · intro e he hsub
            by_cases hve : v ∈ e
            · exact ⟨v, hve, by simp⟩
            · obtain ⟨u, hu, hcu⟩ := hA e he (hrest e hsub hve)
              have huv : u ≠ v := fun h => hve (h ▸ hu)
              exact ⟨u, hu, by simpa only [if_neg huv] using hcu⟩
          · intro u huS hcu
            by_cases huv : u = v
            · subst huv
              obtain ⟨e, he, hue, hsub, -⟩ := hred
              exact ⟨e, he, hue, fun x hx => hvmax x (hsub hx)⟩
            · exact hB u (Finset.mem_erase.2 ⟨huv, huS⟩) (by simpa [huv] using hcu)
        · refine ⟨fun u => if u = v then true else c u, ?_, ?_⟩
          · intro e he hsub
            by_cases hve : v ∈ e
            · by_contra hcon
              refine hred ⟨e, he, hve, hsub, fun u hu huv => ?_⟩
              by_contra hcu
              exact hcon ⟨u, hu, by simpa [huv] using hcu⟩
            · obtain ⟨u, hu, hcu⟩ := hA e he (hrest e hsub hve)
              have huv : u ≠ v := fun h => hve (h ▸ hu)
              exact ⟨u, hu, by simpa only [if_neg huv] using hcu⟩
          · intro u huS hcu
            by_cases huv : u = v
            · simp [huv] at hcu
            · exact hB u (Finset.mem_erase.2 ⟨huv, huS⟩) (by simpa [huv] using hcu)
  obtain ⟨c, hA, hB⟩ := key Finset.univ
  refine ⟨c, fun e he => ?_⟩
  obtain ⟨u, hu, hcu⟩ := hA e he (Finset.subset_univ e)
  by_cases hblue : ∃ x ∈ e, c x = true
  · obtain ⟨x, hx, hcx⟩ := hblue
    exact ⟨u, hu, x, hx, by rw [hcu, hcx]; simp⟩
  · exfalso
    obtain ⟨v, hv, hvmin⟩ := Finset.exists_min_image e w (hne e he)
    have hcv : c v = false := by
      by_contra hcon
      exact hblue ⟨v, hv, by simpa using hcon⟩
    obtain ⟨e', he', hve', hmax⟩ := hB v (Finset.mem_univ v) hcv
    exact hw e' he' e he v ⟨hve', hv, hmax, hvmin⟩

section CherkashinKozik

section UniformWeights

open MeasureTheory

/-- **Independent uniform vertex weights.**  Every vertex of `α` receives a weight drawn
uniformly from `[0, 1]`, independently of the others: the product over `α` of Lebesgue measure
restricted to the unit interval.

This is the continuous counterpart of the uniform measure on two-colourings `α → Bool`. -/
noncomputable def uniformWeights (α : Type*) [Fintype α] : Measure (α → ℝ) :=
  Measure.pi fun _ : α => volume.restrict (Set.Icc (0 : ℝ) 1)

instance (α : Type*) [Fintype α] : IsProbabilityMeasure (uniformWeights α) := by
  have hone : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; norm_num⟩
  rw [uniformWeights]
  infer_instance

/-- The weights are independent, so a box has the product of the lengths of its sides, each side
measured inside `[0, 1]`. -/
theorem uniformWeights_pi (α : Type*) [Fintype α] (s : α → Set ℝ) :
    uniformWeights α (Set.univ.pi s) = ∏ i, volume (s i ∩ Set.Icc (0 : ℝ) 1) := by
  rw [uniformWeights, Measure.pi_pi]
  exact Finset.prod_congr rfl fun i _ => Measure.restrict_apply' measurableSet_Icc

/-- The probability that every vertex of `e` is weighted inside `s` is the `#e`-th power of the
length of `s ∩ [0, 1]`. -/
theorem uniformWeights_forall_mem {α : Type*} [Fintype α] [DecidableEq α]
    (e : Finset α) (s : Set ℝ) :
    uniformWeights α {w : α → ℝ | ∀ u ∈ e, w u ∈ s}
      = volume (s ∩ Set.Icc (0 : ℝ) 1) ^ e.card := by
  have hset : {w : α → ℝ | ∀ u ∈ e, w u ∈ s}
      = Set.univ.pi (fun i => if i ∈ e then s else Set.univ) := by
    ext w
    constructor
    · intro h i _
      show w i ∈ (if i ∈ e then s else Set.univ)
      by_cases hi : i ∈ e
      · rw [if_pos hi]; exact h i hi
      · rw [if_neg hi]; exact Set.mem_univ _
    · intro h u hu
      have hwu : w u ∈ (if u ∈ e then s else Set.univ) := h u (Set.mem_univ u)
      rw [if_pos hu] at hwu
      exact hwu
  rw [hset, uniformWeights_pi]
  have hrew : ∀ i : α, volume ((if i ∈ e then s else Set.univ) ∩ Set.Icc (0 : ℝ) 1)
      = if i ∈ e then volume (s ∩ Set.Icc (0 : ℝ) 1) else 1 := by
    intro i
    by_cases hi : i ∈ e
    · rw [if_pos hi, if_pos hi]
    · rw [if_neg hi, if_neg hi, Set.univ_inter, Real.volume_Icc]
      norm_num
  rw [Finset.prod_congr rfl (fun i _ => hrew i), Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_const]

/-- The probability that `e` lies wholly in the left window `[0, a)` is `a ^ #e`. -/
theorem uniformWeights_forall_lt {α : Type*} [Fintype α] [DecidableEq α]
    (e : Finset α) {a : ℝ} (ha1 : a ≤ 1) :
    uniformWeights α {w : α → ℝ | ∀ u ∈ e, w u < a} = ENNReal.ofReal a ^ e.card := by
  have h := uniformWeights_forall_mem e (Set.Iio a)
  have hs : Set.Iio a ∩ Set.Icc (0 : ℝ) 1 = Set.Ico 0 a := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, le_trans h2.le ha1⟩
  rw [hs, Real.volume_Ico, sub_zero] at h
  exact h

/-- The probability that `e` lies wholly in the right window `(b, 1]` is `(1 - b) ^ #e`. -/
theorem uniformWeights_forall_gt {α : Type*} [Fintype α] [DecidableEq α]
    (e : Finset α) {b : ℝ} (hb0 : 0 ≤ b) :
    uniformWeights α {w : α → ℝ | ∀ u ∈ e, b < w u} = ENNReal.ofReal (1 - b) ^ e.card := by
  have h := uniformWeights_forall_mem e (Set.Ioi b)
  have hs : Set.Ioi b ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc b 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, -, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, le_trans hb0 h1.le, h2⟩
  rw [hs, Real.volume_Ioc] at h
  exact h


/-- **Ties are null.**  Two distinct vertices receive equal weights with probability zero: this
is where the continuity of the weight distribution is used, and it has no counterpart for
two-colourings.

For each `n` the tie event is covered by the `n` boxes on which both coordinates lie in the same
window of length `1 / n`, together with the null event that the first coordinate escapes `[0, 1]`,
so the tie event has measure at most `1 / n`. -/
theorem uniformWeights_eq_null {α : Type*} [Fintype α] [DecidableEq α] {u v : α} (huv : u ≠ v) :
    uniformWeights α {w : α → ℝ | w u = w v} = 0 := by
  have hout : uniformWeights α {w : α → ℝ | w u ∉ Set.Icc (0 : ℝ) 1} = 0 := by
    have hset : {w : α → ℝ | w u ∉ Set.Icc (0 : ℝ) 1}
        = {w : α → ℝ | ∀ t ∈ ({u} : Finset α), w t ∈ (Set.Icc (0 : ℝ) 1)ᶜ} := by
      ext w
      constructor
      · intro hw t ht
        rw [Finset.mem_singleton] at ht
        subst ht
        exact hw
      · intro hw
        exact hw u (Finset.mem_singleton_self u)
    rw [hset, uniformWeights_forall_mem, Set.compl_inter_self, measure_empty,
      Finset.card_singleton, pow_one]
  have hkey : ∀ n : ℕ, uniformWeights α {w : α → ℝ | w u = w v} ≤ (n : ENNReal)⁻¹ := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hcover : {w : α → ℝ | w u = w v} ⊆ {w : α → ℝ | w u ∉ Set.Icc (0 : ℝ) 1} ∪
        ⋃ j ∈ Finset.range n, {w : α → ℝ | ∀ t ∈ ({u, v} : Finset α),
          w t ∈ Set.Icc ((j : ℝ) / n) (((j : ℝ) + 1) / n)} := by
      intro w hw
      have hw' : w u = w v := hw
      by_cases hmem : w u ∈ Set.Icc (0 : ℝ) 1
      · refine Or.inr ?_
        obtain ⟨hx0, hx1⟩ := hmem
        set j : ℕ := min ⌊w u * n⌋₊ (n - 1) with hj
        have hjn : j < n := lt_of_le_of_lt (min_le_right _ _) (by omega)
        have hjle : (j : ℝ) ≤ w u * n := by
          refine le_trans ?_ (Nat.floor_le (by positivity))
          exact_mod_cast min_le_left ⌊w u * n⌋₊ (n - 1)
        have hjlt : w u * n ≤ (j : ℝ) + 1 := by
          by_cases hc : ⌊w u * n⌋₊ ≤ n - 1
          · have hjeq : j = ⌊w u * n⌋₊ := by omega
            rw [hjeq]
            exact le_of_lt (Nat.lt_floor_add_one _)
          · have hjeq : j = n - 1 := by omega
            rw [hjeq]
            have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
              have h1 : (1 : ℕ) ≤ n := hn
              push_cast [Nat.cast_sub h1]
              ring
            rw [hcast]
            nlinarith
        refine Set.mem_biUnion (Finset.mem_range.mpr hjn) ?_
        intro t ht
        have hteq : w t = w u := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl
          · rfl
          · exact hw'.symm
        rw [hteq]
        exact ⟨(div_le_iff₀ hn0).mpr hjle, (le_div_iff₀ hn0).mpr hjlt⟩
      · exact Or.inl hmem
    refine le_trans (measure_mono hcover) ?_
    refine le_trans (measure_union_le _ _) ?_
    rw [hout, zero_add]
    refine le_trans (measure_biUnion_finset_le _ _) ?_
    have hbox : ∀ j ∈ Finset.range n, uniformWeights α {w : α → ℝ | ∀ t ∈ ({u, v} : Finset α),
        w t ∈ Set.Icc ((j : ℝ) / n) (((j : ℝ) + 1) / n)} ≤ ((n : ENNReal)⁻¹) ^ 2 := by
      intro j _
      rw [uniformWeights_forall_mem, Finset.card_pair huv]
      refine pow_le_pow_left₀ zero_le ?_ 2
      refine le_trans (measure_mono Set.inter_subset_left) ?_
      rw [Real.volume_Icc]
      have hlen : ((j : ℝ) + 1) / n - (j : ℝ) / n = 1 / n := by
        rw [div_sub_div_same]
        norm_num
      rw [hlen, one_div, ENNReal.ofReal_inv_of_pos hn0, ENNReal.ofReal_natCast]
    refine le_trans (Finset.sum_le_sum hbox) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, sq, ← mul_assoc,
      ENNReal.mul_inv_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n), one_mul]
  by_contra hne
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hne
  exact absurd (hkey n) (not_le.mpr hn)

end UniformWeights


/-- **The Beta-type integral estimate** at the heart of Cherkashin–Kozik.  Over the middle
window `[(1 - p) / 2, (1 + p) / 2]` of `[0, 1]`, which has length `p`, the integrand
`x ^ n * (1 - x) ^ n = (x * (1 - x)) ^ n` never exceeds `(1 / 4) ^ n`, so

    ∫ x in (1 - p) / 2..(1 + p) / 2, x ^ n * (1 - x) ^ n ≤ p * (1 / 4) ^ n.

With `n = k - 1` this is the bound `p * 4 ^ (1 - k)` used for the probability that a fixed
ordered pair of edges conflicts at a vertex of the middle window. -/
theorem integral_pow_mul_one_sub_pow_le (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∫ x in (1 - p) / 2..(1 + p) / 2, x ^ n * (1 - x) ^ n) ≤ p * (1 / 4) ^ n := by
  have hab : (1 - p) / 2 ≤ (1 + p) / 2 := by linarith
  have hcont : Continuous fun x : ℝ => x ^ n * (1 - x) ^ n := by fun_prop
  have hmono : (∫ x in (1 - p) / 2..(1 + p) / 2, x ^ n * (1 - x) ^ n)
      ≤ ∫ _ in (1 - p) / 2..(1 + p) / 2, ((1 / 4 : ℝ)) ^ n := by
    refine intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) ?_
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have h0 : 0 ≤ x := by linarith
    have h1 : 0 ≤ 1 - x := by linarith
    have hq : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
    calc x ^ n * (1 - x) ^ n = (x * (1 - x)) ^ n := by rw [mul_pow]
      _ ≤ (1 / 4) ^ n := by gcongr
  refine hmono.trans ?_
  rw [intervalIntegral.integral_const, smul_eq_mul]
  have h : (1 + p) / 2 - (1 - p) / 2 = p := by ring
  rw [h]

/-- **The core Beta-type estimate for a single shared vertex.**  Under independent uniform
weights, the probability that `v` is weighted in the middle window `[(1 - p) / 2, (1 + p) / 2]`
while all of `e` sits below it and all of `f` sits above it is at most
`∫ x in (1 - p) / 2..(1 + p) / 2, x ^ n * (1 - x) ^ n`, when `e` and `f` are disjoint `n`-element
sets avoiding `v`.

Cutting the middle window into `N` equal pieces `[t j, t (j + 1)]` bounds the event by `N` boxes:
if `w v` lies in the `j`-th piece then all of `e` lies below `t (j + 1)` and all of `f` above
`t j`, an event of probability `(t (j + 1) - t j) * t (j + 1) ^ n * (1 - t j) ^ n` because the
`2 * n + 1` coordinates involved are independent.  Since `x ^ n * (1 - x) ^ n` moves by at most
`n * (t (j + 1) - t j)` across a piece, the resulting sum exceeds the integral by at most
`n * p ^ 2 / N`, and letting `N` grow gives the bound. -/
theorem uniformWeights_heaviest_lightest_le {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {v : α} {e f : Finset α}
    (hef : Disjoint e f) (hve : v ∉ e) (hvf : v ∉ f) (he : e.card = n) (hf : f.card = n) :
    uniformWeights α {w : α → ℝ | (1 - p) / 2 ≤ w v ∧ w v ≤ (1 + p) / 2 ∧
        (∀ u ∈ e, w u ≤ w v) ∧ (∀ u ∈ f, w v ≤ w u)}
      ≤ ENNReal.ofReal (∫ x in (1 - p) / 2..(1 + p) / 2, x ^ n * (1 - x) ^ n) := by
  have hpow : ∀ (m : ℕ) (x y : ℝ), 0 ≤ x → x ≤ y → y ≤ 1 → y ^ m - x ^ m ≤ m * (y - x) := by
    intro m
    induction m with
    | zero => intro x y _ _ _; simp
    | succ m ih =>
      intro x y hx hxy hy
      have h1 := ih x y hx hxy hy
      have hy0 : (0:ℝ) ≤ y := le_trans hx hxy
      have hxm0 : (0:ℝ) ≤ x ^ m := pow_nonneg hx m
      have hxm1 : x ^ m ≤ 1 := pow_le_one₀ hx (le_trans hxy hy)
      have hd : (0:ℝ) ≤ y - x := by linarith
      have hym : (0:ℝ) ≤ y ^ m - x ^ m := by
        have h := pow_le_pow_left₀ hx hxy m
        linarith
      have hid : y ^ (m + 1) - x ^ (m + 1) = y * (y ^ m - x ^ m) + (y - x) * x ^ m := by ring
      have t1 : y * (y ^ m - x ^ m) ≤ y ^ m - x ^ m := by nlinarith
      have t2 : (y - x) * x ^ m ≤ y - x := by nlinarith
      push_cast
      linarith
  have hpoint : ∀ r s x : ℝ, 0 ≤ r → r ≤ x → x ≤ s → s ≤ 1 →
      s ^ n * (1 - r) ^ n - n * (s - r) ≤ x ^ n * (1 - x) ^ n := by
    intro r s x hr0 hrx hxs hs1
    have hx0 : (0:ℝ) ≤ x := le_trans hr0 hrx
    have hx1 : x ≤ (1:ℝ) := le_trans hxs hs1
    have h1 : s ^ n - x ^ n ≤ n * (s - x) := hpow n x s hx0 hxs hs1
    have h2 : (1 - r) ^ n - (1 - x) ^ n ≤ n * ((1 - r) - (1 - x)) :=
      hpow n (1 - x) (1 - r) (by linarith) (by linarith) (by linarith)
    have h3 : (1 - r) ^ n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have h4 : x ^ n ≤ 1 := pow_le_one₀ hx0 hx1
    have h5 : (0:ℝ) ≤ s ^ n - x ^ n := by
      have h := pow_le_pow_left₀ hx0 hxs n
      linarith
    have h6 : (0:ℝ) ≤ (1 - r) ^ n - (1 - x) ^ n := by
      have h := pow_le_pow_left₀ (show (0:ℝ) ≤ 1 - x by linarith) (show 1 - x ≤ 1 - r by linarith) n
      linarith
    have h7 : (0:ℝ) ≤ x ^ n := pow_nonneg hx0 n
    have h8 : (0:ℝ) ≤ (1 - r) ^ n := pow_nonneg (by linarith) n
    have hid : s ^ n * (1 - r) ^ n - x ^ n * (1 - x) ^ n
        = (1 - r) ^ n * (s ^ n - x ^ n) + x ^ n * ((1 - r) ^ n - (1 - x) ^ n) := by ring
    nlinarith [hid, h1, h2, h3, h4, h5, h6, h7, h8]
  have hint : ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ 1 →
      (s - r) * (s ^ n * (1 - r) ^ n)
        ≤ (∫ x in r..s, x ^ n * (1 - x) ^ n) + n * (s - r) ^ 2 := by
    intro r s hr0 hrs hs1
    have hcont : Continuous fun x : ℝ => x ^ n * (1 - x) ^ n := by fun_prop
    have hmono : (∫ _ in r..s, (s ^ n * (1 - r) ^ n - n * (s - r)))
        ≤ ∫ x in r..s, x ^ n * (1 - x) ^ n :=
      intervalIntegral.integral_mono_on hrs (continuous_const.intervalIntegrable _ _)
        (hcont.intervalIntegrable _ _) fun x hx => hpoint r s x hr0 hx.1 hx.2 hs1
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    nlinarith [hmono]
  have hbox : ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ 1 →
      uniformWeights α {w : α → ℝ | (r ≤ w v ∧ w v ≤ s) ∧ (∀ u ∈ e, w u ≤ s) ∧
          (∀ u ∈ f, r ≤ w u)}
        = ENNReal.ofReal ((s - r) * (s ^ n * (1 - r) ^ n)) := by
    intro r s hr0 hrs hs1
    have hs0 : (0:ℝ) ≤ s := le_trans hr0 hrs
    have hr1 : r ≤ (1:ℝ) := le_trans hrs hs1
    have hconv : ENNReal.ofReal ((s - r) * (s ^ n * (1 - r) ^ n))
        = ENNReal.ofReal (s - r) * ENNReal.ofReal s ^ n * ENNReal.ofReal (1 - r) ^ n := by
      rw [ENNReal.ofReal_mul (by linarith : (0:ℝ) ≤ s - r),
        ENNReal.ofReal_mul (pow_nonneg hs0 n), ENNReal.ofReal_pow hs0,
        ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ 1 - r)]
      ring
    rw [hconv]
    have hset : {w : α → ℝ | (r ≤ w v ∧ w v ≤ s) ∧ (∀ u ∈ e, w u ≤ s) ∧ (∀ u ∈ f, r ≤ w u)}
        = Set.univ.pi (fun i => if i = v then Set.Icc r s else if i ∈ e then Set.Iic s
            else if i ∈ f then Set.Ici r else Set.univ) := by
      ext w
      constructor
      · rintro ⟨hv, hE, hF⟩ i _
        show w i ∈ (if i = v then Set.Icc r s else if i ∈ e then Set.Iic s
            else if i ∈ f then Set.Ici r else Set.univ)
        by_cases h1 : i = v
        · rw [if_pos h1, h1]
          exact ⟨hv.1, hv.2⟩
        · rw [if_neg h1]
          by_cases h2 : i ∈ e
          · rw [if_pos h2]
            exact hE i h2
          · rw [if_neg h2]
            by_cases h3 : i ∈ f
            · rw [if_pos h3]
              exact hF i h3
            · rw [if_neg h3]
              exact Set.mem_univ _
      · intro h
        have hget : ∀ i : α, w i ∈ (if i = v then Set.Icc r s else if i ∈ e then Set.Iic s
            else if i ∈ f then Set.Ici r else Set.univ) := fun i => h i (Set.mem_univ i)
        refine ⟨?_, ?_, ?_⟩
        · have hi := hget v
          rw [if_pos rfl] at hi
          exact ⟨hi.1, hi.2⟩
        · intro u hu
          have hi := hget u
          rw [if_neg (fun hc : u = v => hve (hc ▸ hu)), if_pos hu] at hi
          exact hi
        · intro u hu
          have hi := hget u
          rw [if_neg (fun hc : u = v => hvf (hc ▸ hu)),
            if_neg (Finset.disjoint_right.mp hef hu), if_pos hu] at hi
          exact hi
    rw [hset, uniformWeights_pi]
    have hG : ∀ i : α, MeasureTheory.volume ((if i = v then Set.Icc r s else if i ∈ e then Set.Iic s
        else if i ∈ f then Set.Ici r else Set.univ) ∩ Set.Icc (0:ℝ) 1)
        = if i = v then ENNReal.ofReal (s - r) else if i ∈ e then ENNReal.ofReal s
          else if i ∈ f then ENNReal.ofReal (1 - r) else 1 := by
      intro i
      by_cases h1 : i = v
      · rw [if_pos h1, if_pos h1,
          Set.inter_eq_self_of_subset_left (Set.Icc_subset_Icc hr0 hs1), Real.volume_Icc]
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : i ∈ e
        · rw [if_pos h2, if_pos h2, show Set.Iic s ∩ Set.Icc (0:ℝ) 1 = Set.Icc 0 s from ?_,
            Real.volume_Icc, sub_zero]
          ext x
          simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
          constructor
          · rintro ⟨h1', h2', -⟩
            exact ⟨h2', h1'⟩
          · rintro ⟨h1', h2'⟩
            exact ⟨h2', h1', le_trans h2' hs1⟩
        · rw [if_neg h2, if_neg h2]
          by_cases h3 : i ∈ f
          · rw [if_pos h3, if_pos h3, show Set.Ici r ∩ Set.Icc (0:ℝ) 1 = Set.Icc r 1 from ?_,
              Real.volume_Icc]
            ext x
            simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
            constructor
            · rintro ⟨h1', -, h3'⟩
              exact ⟨h1', h3'⟩
            · rintro ⟨h1', h2'⟩
              exact ⟨h1', le_trans hr0 h1', h2'⟩
          · rw [if_neg h3, if_neg h3, Set.univ_inter, Real.volume_Icc]
            norm_num
    rw [Finset.prod_congr rfl (fun i _ => hG i)]
    have hsub : insert v (e ∪ f) ⊆ (Finset.univ : Finset α) := Finset.subset_univ _
    rw [← Finset.prod_subset hsub (by
      intro i _ hi
      have h1 : i ≠ v := fun hc => hi (Finset.mem_insert.mpr (Or.inl hc))
      have h2 : i ∉ e := fun hc => hi (Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left _ hc)))
      have h3 : i ∉ f := fun hc => hi (Finset.mem_insert.mpr (Or.inr (Finset.mem_union_right _ hc)))
      rw [if_neg h1, if_neg h2, if_neg h3])]
    rw [Finset.prod_insert (by
      intro hc
      rcases Finset.mem_union.mp hc with h | h
      · exact hve h
      · exact hvf h), Finset.prod_union hef]
    have hev : ∀ i ∈ e, (if i = v then ENNReal.ofReal (s - r) else if i ∈ e then ENNReal.ofReal s
        else if i ∈ f then ENNReal.ofReal (1 - r) else 1) = ENNReal.ofReal s := by
      intro i hi
      rw [if_neg (fun hc : i = v => hve (hc ▸ hi)), if_pos hi]
    have hfv : ∀ i ∈ f, (if i = v then ENNReal.ofReal (s - r) else if i ∈ e then ENNReal.ofReal s
        else if i ∈ f then ENNReal.ofReal (1 - r) else 1) = ENNReal.ofReal (1 - r) := by
      intro i hi
      rw [if_neg (fun hc : i = v => hvf (hc ▸ hi)), if_neg (Finset.disjoint_right.mp hef hi),
        if_pos hi]
    rw [Finset.prod_congr rfl hev, Finset.prod_congr rfl hfv, Finset.prod_const, Finset.prod_const,
      he, hf, if_pos rfl, mul_assoc]

  have hcont : Continuous fun x : ℝ => x ^ n * (1 - x) ^ n := by fun_prop
  have hp2 : (0:ℝ) ≤ (1 - p) / 2 := by linarith
  have hI0 : (0:ℝ) ≤ ∫ x in (1 - p) / 2..(1 + p) / 2, x ^ n * (1 - x) ^ n := by
    refine intervalIntegral.integral_nonneg (by linarith) ?_
    intro x hx
    exact mul_nonneg (pow_nonneg (le_trans hp2 hx.1) _) (pow_nonneg (by linarith [hx.2]) _)
  have hmain : ∀ N : ℕ, 0 < N →
      uniformWeights α {w : α → ℝ | (1 - p) / 2 ≤ w v ∧ w v ≤ (1 + p) / 2 ∧
          (∀ u ∈ e, w u ≤ w v) ∧ (∀ u ∈ f, w v ≤ w u)}
        ≤ ENNReal.ofReal ((∫ x in (1 - p) / 2..(1 + p) / 2, x ^ n * (1 - x) ^ n)
            + n * p ^ 2 / N) := by
    intro N hN
    have hNR : (0:ℝ) < N := by exact_mod_cast hN
    have hpN : (0:ℝ) < p / N := by positivity
    obtain ⟨t, ht⟩ : ∃ t : ℕ → ℝ, ∀ j : ℕ, t j = (1 - p) / 2 + j * (p / N) := ⟨_, fun _ => rfl⟩
    have hstep : ∀ j : ℕ, t (j + 1) - t j = p / N := by
      intro j
      rw [ht, ht]
      push_cast
      ring
    have ht0 : t 0 = (1 - p) / 2 := by rw [ht]; norm_num
    have htN : t N = (1 + p) / 2 := by
      rw [ht]
      field_simp
      ring
    have hmono : ∀ i j : ℕ, i ≤ j → t i ≤ t j := by
      intro i j hij
      rw [ht, ht]
      have hc : (i:ℝ) ≤ j := by exact_mod_cast hij
      nlinarith
    have hge0 : ∀ j : ℕ, 0 ≤ t j := by
      intro j
      have h := hmono 0 j (Nat.zero_le j)
      rw [ht0] at h
      linarith
    have hle1 : ∀ j : ℕ, j ≤ N → t j ≤ 1 := by
      intro j hj
      have h := hmono j N hj
      rw [htN] at h
      linarith
    have hcover : {w : α → ℝ | (1 - p) / 2 ≤ w v ∧ w v ≤ (1 + p) / 2 ∧
        (∀ u ∈ e, w u ≤ w v) ∧ (∀ u ∈ f, w v ≤ w u)} ⊆
        ⋃ j ∈ Finset.range N, {w : α → ℝ | (t j ≤ w v ∧ w v ≤ t (j + 1)) ∧
          (∀ u ∈ e, w u ≤ t (j + 1)) ∧ (∀ u ∈ f, t j ≤ w u)} := by
      rintro w ⟨hl, hr, hE, hF⟩
      obtain ⟨j, hjN, hj1, hj2⟩ : ∃ j : ℕ, j < N ∧ t j ≤ w v ∧ w v ≤ t (j + 1) := by
        obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (w v - (1 - p) / 2) * N / p := ⟨_, rfl⟩
        have hy0 : (0:ℝ) ≤ y := by
          rw [hy]
          exact div_nonneg (mul_nonneg (by linarith) hNR.le) hp0.le
        have hyN : y ≤ N := by
          rw [hy, div_le_iff₀ hp0]
          nlinarith
        have hkey : y * (p / N) = w v - (1 - p) / 2 := by
          rw [hy]
          field_simp
        obtain ⟨j, hj⟩ : ∃ j : ℕ, j = min ⌊y⌋₊ (N - 1) := ⟨_, rfl⟩
        have hjlt : j < N := by
          rw [hj]
          exact lt_of_le_of_lt (min_le_right _ _) (by omega)
        have hjle : (j : ℝ) ≤ y := by
          refine le_trans ?_ (Nat.floor_le hy0)
          rw [hj]
          exact_mod_cast min_le_left ⌊y⌋₊ (N - 1)
        have hjge : y ≤ (j : ℝ) + 1 := by
          by_cases hc : ⌊y⌋₊ ≤ N - 1
          · have hje : j = ⌊y⌋₊ := by omega
            rw [hje]
            exact le_of_lt (Nat.lt_floor_add_one _)
          · have hje : j = N - 1 := by omega
            rw [hje]
            have hcast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
              have h1 : (1:ℕ) ≤ N := hN
              push_cast [Nat.cast_sub h1]
              ring
            rw [hcast]
            exact hyN
        refine ⟨j, hjlt, ?_, ?_⟩
        · rw [ht]
          have h := mul_le_mul_of_nonneg_right hjle hpN.le
          rw [hkey] at h
          linarith
        · rw [ht]
          have h := mul_le_mul_of_nonneg_right hjge hpN.le
          rw [hkey] at h
          push_cast
          linarith
      exact Set.mem_biUnion (Finset.mem_range.mpr hjN)
        ⟨⟨hj1, hj2⟩, fun u hu => le_trans (hE u hu) hj2, fun u hu => le_trans hj1 (hF u hu)⟩
    refine le_trans (MeasureTheory.measure_mono hcover) ?_
    refine le_trans (MeasureTheory.measure_biUnion_finset_le _ _) ?_
    have hterm : ∀ j ∈ Finset.range N,
        uniformWeights α {w : α → ℝ | (t j ≤ w v ∧ w v ≤ t (j + 1)) ∧
          (∀ u ∈ e, w u ≤ t (j + 1)) ∧ (∀ u ∈ f, t j ≤ w u)}
        = ENNReal.ofReal ((t (j + 1) - t j) * (t (j + 1) ^ n * (1 - t j) ^ n)) := by
      intro j hj
      rw [Finset.mem_range] at hj
      exact hbox (t j) (t (j + 1)) (hge0 j) (hmono j (j + 1) (Nat.le_succ j))
        (hle1 (j + 1) (by omega))
    have hnn : ∀ j ∈ Finset.range N,
        (0:ℝ) ≤ (t (j + 1) - t j) * (t (j + 1) ^ n * (1 - t j) ^ n) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have h1 : t j ≤ t (j + 1) := hmono j (j + 1) (Nat.le_succ j)
      have h2 : t (j + 1) ≤ 1 := hle1 (j + 1) (by omega)
      have h3 : (0:ℝ) ≤ t (j + 1) := hge0 (j + 1)
      have h4 : t j ≤ 1 := le_trans h1 h2
      exact mul_nonneg (by linarith)
        (mul_nonneg (pow_nonneg h3 n) (pow_nonneg (by linarith) n))
    rw [Finset.sum_congr rfl hterm, ← ENNReal.ofReal_sum_of_nonneg hnn]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsum : ∀ j ∈ Finset.range N,
        (t (j + 1) - t j) * (t (j + 1) ^ n * (1 - t j) ^ n)
          ≤ (∫ x in t j..t (j + 1), x ^ n * (1 - x) ^ n) + n * (p / N) ^ 2 := by
      intro j hj
      rw [Finset.mem_range] at hj
      have h := hint (t j) (t (j + 1)) (hge0 j) (hmono j (j + 1) (Nat.le_succ j))
        (hle1 (j + 1) (by omega))
      rw [← hstep j]
      exact h
    refine le_trans (Finset.sum_le_sum hsum) ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      intervalIntegral.sum_integral_adjacent_intervals
        (fun k _ => (hcont.intervalIntegrable _ _)), ht0, htN]
    have harith : (N : ℝ) * ((n : ℝ) * (p / N) ^ 2) = (n : ℝ) * p ^ 2 / N := by
      field_simp
    rw [harith]
  -- pass to the limit
  have hfin : uniformWeights α {w : α → ℝ | (1 - p) / 2 ≤ w v ∧ w v ≤ (1 + p) / 2 ∧
      (∀ u ∈ e, w u ≤ w v) ∧ (∀ u ∈ f, w v ≤ w u)} ≠ ⊤ := MeasureTheory.measure_ne_top _ _
  have hreal : (uniformWeights α {w : α → ℝ | (1 - p) / 2 ≤ w v ∧ w v ≤ (1 + p) / 2 ∧
      (∀ u ∈ e, w u ≤ w v) ∧ (∀ u ∈ f, w v ≤ w u)}).toReal
      ≤ ∫ x in (1 - p) / 2..(1 + p) / 2, x ^ n * (1 - x) ^ n := by
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    obtain ⟨N, hNgt⟩ := exists_nat_gt (max 1 ((n : ℝ) * p ^ 2 / ε))
    have hN1 : 0 < N := by
      have h : (1:ℝ) ≤ max 1 ((n : ℝ) * p ^ 2 / ε) := le_max_left _ _
      have : (0:ℝ) < N := by linarith
      exact_mod_cast this
    have hNR : (0:ℝ) < N := by exact_mod_cast hN1
    have h2 := ENNReal.toReal_le_of_le_ofReal (by positivity) (hmain N hN1)
    have h3 : (n : ℝ) * p ^ 2 / N < ε := by
      rw [div_lt_iff₀ hNR]
      have h : (n : ℝ) * p ^ 2 / ε ≤ max 1 ((n : ℝ) * p ^ 2 / ε) := le_max_right _ _
      have h4 : (n : ℝ) * p ^ 2 / ε < N := by linarith
      rw [div_lt_iff₀ hε] at h4
      linarith
    linarith
  calc uniformWeights α {w : α → ℝ | (1 - p) / 2 ≤ w v ∧ w v ≤ (1 + p) / 2 ∧
        (∀ u ∈ e, w u ≤ w v) ∧ (∀ u ∈ f, w v ≤ w u)}
      = ENNReal.ofReal ((uniformWeights α {w : α → ℝ | (1 - p) / 2 ≤ w v ∧ w v ≤ (1 + p) / 2 ∧
        (∀ u ∈ e, w u ≤ w v) ∧ (∀ u ∈ f, w v ≤ w u)}).toReal) :=
        (ENNReal.ofReal_toReal hfin).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal


/-- **A fixed ordered pair of edges conflicts in the middle window with probability at most the
Beta-type integral.**  Under independent uniform weights, if `e` and `f` are `k`-element edges
then the chance that some vertex `v` is `w`-heaviest in `e`, `w`-lightest in `f`, and weighted in
the middle window `[(1 - p) / 2, (1 + p) / 2]` is at most
`∫ x in (1 - p) / 2..(1 + p) / 2, x ^ (k - 1) * (1 - x) ^ (k - 1)`.

If `e` and `f` are disjoint there is no such `v` at all.  If they meet in two or more vertices a
conflict at `v` forces a tie between two independent uniform weights, which is a null event.  If
they meet in the single vertex `v`, then conditionally on `w v = x` the remaining `k - 1` vertices
of `e` must all be weighted below `x` and the remaining `k - 1` vertices of `f` all above it;
those `2 * (k - 1)` weights are independent, so the conditional probability is
`x ^ (k - 1) * (1 - x) ^ (k - 1)`, and integrating over the middle window gives the bound. -/
theorem uniformWeights_conflictingPair_mid_le {α : Type*} [Fintype α] [DecidableEq α]
    {k : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {e f : Finset α}
    (he : e.card = k) (hf : f.card = k) :
    uniformWeights α {w : α → ℝ | ∃ v : α, ConflictingPair w e f v ∧
        (1 - p) / 2 ≤ w v ∧ w v ≤ (1 + p) / 2}
      ≤ ENNReal.ofReal (∫ x in (1 - p) / 2..(1 + p) / 2, x ^ (k - 1) * (1 - x) ^ (k - 1)) := by
  rcases Finset.eq_empty_or_nonempty (e ∩ f) with hemp | ⟨v₀, hv₀⟩
  · -- disjoint edges have no shared vertex, so they never conflict
    have hset : {w : α → ℝ | ∃ v : α, ConflictingPair w e f v ∧
        (1 - p) / 2 ≤ w v ∧ w v ≤ (1 + p) / 2} = (∅ : Set (α → ℝ)) := by
      ext w
      constructor
      · rintro ⟨v, ⟨hve, hvf, -, -⟩, -, -⟩
        exact absurd (Finset.mem_inter.mpr ⟨hve, hvf⟩)
          (by rw [hemp]; exact Finset.notMem_empty v)
      · exact fun h => absurd h (Set.notMem_empty w)
    rw [hset, MeasureTheory.measure_empty]
    exact zero_le
  · by_cases hcard : (e ∩ f).card = 1
    · -- the edges meet in the single vertex `v₀`
      have hinter : e ∩ f = {v₀} := by
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
        rw [hx] at hv₀ ⊢
        rw [Finset.mem_singleton.mp hv₀]
      have hv₀e : v₀ ∈ e := (Finset.mem_inter.mp hv₀).1
      have hv₀f : v₀ ∈ f := (Finset.mem_inter.mp hv₀).2
      have hsub : {w : α → ℝ | ∃ v : α, ConflictingPair w e f v ∧
          (1 - p) / 2 ≤ w v ∧ w v ≤ (1 + p) / 2} ⊆
          {w : α → ℝ | (1 - p) / 2 ≤ w v₀ ∧ w v₀ ≤ (1 + p) / 2 ∧
            (∀ u ∈ e.erase v₀, w u ≤ w v₀) ∧ (∀ u ∈ f.erase v₀, w v₀ ≤ w u)} := by
        rintro w ⟨v, ⟨hve, hvf, hmax, hmin⟩, hl, hr⟩
        have hvv : v = v₀ := by
          have hv : v ∈ e ∩ f := Finset.mem_inter.mpr ⟨hve, hvf⟩
          rw [hinter] at hv
          exact Finset.mem_singleton.mp hv
        subst hvv
        exact ⟨hl, hr, fun u hu => hmax u (Finset.mem_of_mem_erase hu),
          fun u hu => hmin u (Finset.mem_of_mem_erase hu)⟩
      refine le_trans (MeasureTheory.measure_mono hsub) ?_
      refine uniformWeights_heaviest_lightest_le hp0 hp1 ?_ (Finset.notMem_erase v₀ e)
        (Finset.notMem_erase v₀ f) ?_ ?_
      · rw [Finset.disjoint_left]
        intro u hue huf
        have hu : u ∈ e ∩ f := Finset.mem_inter.mpr
          ⟨Finset.mem_of_mem_erase hue, Finset.mem_of_mem_erase huf⟩
        rw [hinter, Finset.mem_singleton] at hu
        exact (Finset.ne_of_mem_erase hue) hu
      · rw [Finset.card_erase_of_mem hv₀e, he]
      · rw [Finset.card_erase_of_mem hv₀f, hf]
    · -- two or more shared vertices force a tie, which is a null event
      have hge : 2 ≤ (e ∩ f).card := by
        have h1 : 1 ≤ (e ∩ f).card := Finset.card_pos.mpr ⟨v₀, hv₀⟩
        omega
      have hsub : {w : α → ℝ | ∃ v : α, ConflictingPair w e f v ∧
          (1 - p) / 2 ≤ w v ∧ w v ≤ (1 + p) / 2} ⊆
          ⋃ v ∈ e ∩ f, ⋃ u ∈ (e ∩ f).erase v, {w : α → ℝ | w u = w v} := by
        rintro w ⟨v, ⟨hve, hvf, hmax, hmin⟩, -, -⟩
        have hvmem : v ∈ e ∩ f := Finset.mem_inter.mpr ⟨hve, hvf⟩
        have hne : ((e ∩ f).erase v).Nonempty := by
          rw [← Finset.card_pos, Finset.card_erase_of_mem hvmem]
          omega
        obtain ⟨u, hu⟩ := hne
        refine Set.mem_biUnion hvmem (Set.mem_biUnion hu ?_)
        have humem := Finset.mem_of_mem_erase hu
        exact le_antisymm (hmax u (Finset.mem_inter.mp humem).1)
          (hmin u (Finset.mem_inter.mp humem).2)
      refine le_trans (MeasureTheory.measure_mono hsub) ?_
      refine le_trans (MeasureTheory.measure_biUnion_finset_le _ _) ?_
      refine le_trans
        (Finset.sum_le_sum fun v _ => MeasureTheory.measure_biUnion_finset_le _ _) ?_
      have hz : ∀ v ∈ e ∩ f, ∑ u ∈ (e ∩ f).erase v, uniformWeights α {w : α → ℝ | w u = w v}
          = 0 := fun v _ =>
        Finset.sum_eq_zero fun u hu => uniformWeights_eq_null (Finset.ne_of_mem_erase hu)
      rw [Finset.sum_congr rfl hz, Finset.sum_const, smul_zero]
      exact zero_le

/-- **The union bound behind the Cherkashin–Kozik estimate.**  Give each vertex an independent
uniform weight in `[0, 1]` and split `[0, 1]` into `L = [0, (1 - p) / 2)`, the middle window
`M = [(1 - p) / 2, (1 + p) / 2]`, and `R = ((1 + p) / 2, 1]`.

If some conflicting pair `e`, `f`, `v` occurs then either the shared vertex has weight in `L`,
in which case `e ⊆ L` because `v` is `w`-heaviest in `e`; or it has weight in `R`, in which case
`f ⊆ R` because `v` is `w`-lightest in `f`; or its weight lies in `M`.  The first two events cost
at most `2 * #H * ((1 - p) / 2) ^ k`.  For the third, a fixed ordered pair of edges meeting in a
single vertex conflicts there with probability `∫ x in (1 - p)/2..(1 + p)/2, x^(k-1) * (1-x)^(k-1)`,
and a pair meeting in two or more vertices forces a tie and so contributes nothing; summing over
the `#H ^ 2` ordered pairs gives the second term.

So when the two terms add to less than `1` some weighting is free of conflicting pairs. -/
theorem exists_conflictFree_of_union_bound_lt_one {α : Type*} [Fintype α] [DecidableEq α]
    {k : ℕ} (hk : 2 ≤ k) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {H : Finset (Finset α)}
    (huniform : ∀ e ∈ H, e.card = k)
    (hbound : 2 * (H.card : ℝ) * ((1 - p) / 2) ^ k
        + (H.card : ℝ) ^ 2 * ∫ x in (1 - p) / 2..(1 + p) / 2, x ^ (k - 1) * (1 - x) ^ (k - 1)
        < 1) :
    ∃ w : α → ℝ, ∀ e ∈ H, ∀ f ∈ H, ∀ v : α, ¬ ConflictingPair w e f v := by
  have ha0 : (0 : ℝ) ≤ (1 - p) / 2 := by linarith
  have ha1 : (1 - p) / 2 ≤ (1 : ℝ) := by linarith
  have hab : (1 - p) / 2 ≤ (1 + p) / 2 := by linarith
  have hb0 : (0 : ℝ) ≤ (1 + p) / 2 := by linarith
  have hI0 : (0 : ℝ) ≤ ∫ x in (1 - p) / 2..(1 + p) / 2, x ^ (k - 1) * (1 - x) ^ (k - 1) := by
    refine intervalIntegral.integral_nonneg hab ?_
    intro x hx
    exact mul_nonneg (pow_nonneg (le_trans ha0 hx.1) _) (pow_nonneg (by linarith [hx.2]) _)
  by_contra hcon
  -- every weighting carries a conflicting pair, so the three bad events cover everything
  have hbad : ∀ w : α → ℝ, ∃ e ∈ H, ∃ f ∈ H, ∃ v : α, ConflictingPair w e f v := by
    intro w
    by_contra h
    exact hcon ⟨w, fun e he f hf v hcp => h ⟨e, he, f, hf, v, hcp⟩⟩
  have hcover : (Set.univ : Set (α → ℝ)) ⊆
      ((⋃ e ∈ H, {w : α → ℝ | ∀ u ∈ e, w u < (1 - p) / 2}) ∪
        (⋃ f ∈ H, {w : α → ℝ | ∀ u ∈ f, (1 + p) / 2 < w u})) ∪
      (⋃ e ∈ H, ⋃ f ∈ H, {w : α → ℝ | ∃ v : α, ConflictingPair w e f v ∧
        (1 - p) / 2 ≤ w v ∧ w v ≤ (1 + p) / 2}) := by
    intro w _
    obtain ⟨e, he, f, hf, v, hcp⟩ := hbad w
    obtain ⟨hve, hvf, hmax, hmin⟩ := hcp
    by_cases h1 : w v < (1 - p) / 2
    · exact Or.inl (Or.inl (Set.mem_biUnion he fun u hu => lt_of_le_of_lt (hmax u hu) h1))
    · by_cases h2 : (1 + p) / 2 < w v
      · exact Or.inl (Or.inr (Set.mem_biUnion hf fun u hu => lt_of_lt_of_le h2 (hmin u hu)))
      · exact Or.inr (Set.mem_biUnion he (Set.mem_biUnion hf
          ⟨v, ⟨hve, hvf, hmax, hmin⟩, not_lt.mp h1, not_lt.mp h2⟩))
  have h1 : uniformWeights α (⋃ e ∈ H, {w : α → ℝ | ∀ u ∈ e, w u < (1 - p) / 2})
      ≤ ∑ _e ∈ H, ENNReal.ofReal ((1 - p) / 2) ^ k := by
    refine le_trans (MeasureTheory.measure_biUnion_finset_le H _)
      (Finset.sum_le_sum fun e he => ?_)
    rw [uniformWeights_forall_lt e ha1, huniform e he]
  have h2 : uniformWeights α (⋃ f ∈ H, {w : α → ℝ | ∀ u ∈ f, (1 + p) / 2 < w u})
      ≤ ∑ _f ∈ H, ENNReal.ofReal ((1 - p) / 2) ^ k := by
    refine le_trans (MeasureTheory.measure_biUnion_finset_le H _)
      (Finset.sum_le_sum fun f hf => ?_)
    rw [uniformWeights_forall_gt f hb0, huniform f hf,
      show (1 : ℝ) - (1 + p) / 2 = (1 - p) / 2 by ring]
  have h3 : uniformWeights α (⋃ e ∈ H, ⋃ f ∈ H, {w : α → ℝ | ∃ v : α, ConflictingPair w e f v ∧
        (1 - p) / 2 ≤ w v ∧ w v ≤ (1 + p) / 2})
      ≤ ∑ _e ∈ H, ∑ _f ∈ H,
          ENNReal.ofReal (∫ x in (1 - p) / 2..(1 + p) / 2, x ^ (k - 1) * (1 - x) ^ (k - 1)) := by
    refine le_trans (MeasureTheory.measure_biUnion_finset_le H _)
      (Finset.sum_le_sum fun e he => ?_)
    refine le_trans (MeasureTheory.measure_biUnion_finset_le H _)
      (Finset.sum_le_sum fun f hf => ?_)
    exact uniformWeights_conflictingPair_mid_le hp0 hp1 (huniform e he) (huniform f hf)
  -- the total mass of the three events is at least `1`
  have hchain : (1 : ENNReal) ≤ (H.card : ENNReal) * ENNReal.ofReal ((1 - p) / 2) ^ k
      + (H.card : ENNReal) * ENNReal.ofReal ((1 - p) / 2) ^ k
      + (H.card : ENNReal) ^ 2
        * ENNReal.ofReal (∫ x in (1 - p) / 2..(1 + p) / 2, x ^ (k - 1) * (1 - x) ^ (k - 1)) := by
    rw [show (1 : ENNReal) = uniformWeights α Set.univ from MeasureTheory.measure_univ.symm]
    refine le_trans (MeasureTheory.measure_mono hcover) ?_
    refine le_trans (MeasureTheory.measure_union_le _ _) ?_
    refine le_trans (add_le_add (MeasureTheory.measure_union_le _ _) le_rfl) ?_
    refine add_le_add (add_le_add (le_trans h1 ?_) (le_trans h2 ?_)) (le_trans h3 ?_)
    · rw [Finset.sum_const, nsmul_eq_mul]
    · rw [Finset.sum_const, nsmul_eq_mul]
    · rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc, ← sq]
  -- but the hypothesis says it is less than `1`
  have hreal : (H.card : ℝ) * ((1 - p) / 2) ^ k + (H.card : ℝ) * ((1 - p) / 2) ^ k
      + (H.card : ℝ) ^ 2 * ∫ x in (1 - p) / 2..(1 + p) / 2, x ^ (k - 1) * (1 - x) ^ (k - 1)
      < 1 := by
    have h : 2 * (H.card : ℝ) * ((1 - p) / 2) ^ k
        = (H.card : ℝ) * ((1 - p) / 2) ^ k + (H.card : ℝ) * ((1 - p) / 2) ^ k := by ring
    linarith
  have hconv : ENNReal.ofReal ((H.card : ℝ) * ((1 - p) / 2) ^ k
      + (H.card : ℝ) * ((1 - p) / 2) ^ k
      + (H.card : ℝ) ^ 2 * ∫ x in (1 - p) / 2..(1 + p) / 2, x ^ (k - 1) * (1 - x) ^ (k - 1))
      = (H.card : ENNReal) * ENNReal.ofReal ((1 - p) / 2) ^ k
      + (H.card : ENNReal) * ENNReal.ofReal ((1 - p) / 2) ^ k
      + (H.card : ENNReal) ^ 2
        * ENNReal.ofReal (∫ x in (1 - p) / 2..(1 + p) / 2, x ^ (k - 1) * (1 - x) ^ (k - 1)) := by
    have hpk : (0 : ℝ) ≤ ((1 - p) / 2) ^ k := pow_nonneg ha0 k
    rw [ENNReal.ofReal_add (by positivity) (mul_nonneg (by positivity) hI0),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (sq_nonneg ((H.card : ℝ))),
      ENNReal.ofReal_pow ha0, ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [← hconv] at hchain
  exact absurd (ENNReal.ofReal_lt_one.mpr hreal) (not_lt.mpr hchain)

end CherkashinKozik

/-- **The Cherkashin–Kozik estimate** (the analytic half of Zhao, Theorem 3.5.1).  For some
absolute constant `c > 0` and every large enough `k`, every `k`-uniform hypergraph with at most
`c * √(k / log k) * 2 ^ k` edges carries vertex weights with no conflicting pair.

Give each vertex an independent uniform weight in `[0, 1]` and split `[0, 1]` as `L ∪ M ∪ R`
with `M = [(1 - p) / 2, (1 + p) / 2]` and `p = log (2 ^ (k - 1) * k / m) / k`, `m = #H`.  Some
edge lies wholly in `L` or wholly in `R` with probability at most `2 * m * ((1 - p) / 2) ^ k`.
Otherwise the shared vertex of a conflicting pair lies in `M`, and a fixed ordered pair of edges
conflicts there with probability at most the Beta-type integral
`∫ x in (1 - p) / 2..(1 + p) / 2, x ^ (k - 1) * (1 - x) ^ (k - 1)`, which is at most
`p * 4 ^ (1 - k)`; that costs at most `m ^ 2 * p * 4 ^ (1 - k)`.  For
`m ≤ c * √(k / log k) * 2 ^ k` the two terms sum to less than `1`, so some weighting works. -/
theorem exists_conflictFree_of_card_le :
    ∃ (c : ℝ) (k₀ : ℕ), 0 < c ∧
      ∀ (α : Type) (_ : Fintype α) (_ : DecidableEq α) (k : ℕ), k₀ ≤ k →
        ∀ H : Finset (Finset α), (∀ e ∈ H, e.card = k) →
          (H.card : ℝ) ≤ c * Real.sqrt (k / Real.log k) * 2 ^ k →
          ∃ w : α → ℝ, ∀ e ∈ H, ∀ f ∈ H, ∀ v : α, ¬ ConflictingPair w e f v := by
  refine ⟨1 / 8, 256, by norm_num, ?_⟩
  intro α hfin hdec k hk H huniform hcard
  rcases H.eq_empty_or_nonempty with rfl | hH
  · exact ⟨fun _ => 0, by simp⟩
  have hk2 : 2 ≤ k := by omega
  -- `K = k`, `L = log k`, and the elementary estimates on them
  set K : ℝ := (k : ℝ) with hKdef
  clear_value K
  have hK256 : (256 : ℝ) ≤ K := by rw [hKdef]; exact_mod_cast hk
  have hK0 : 0 < K := by linarith
  set L : ℝ := Real.log K with hLdef
  clear_value L
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2gt : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hL4 : (4 : ℝ) ≤ L := by
    have h256 : Real.log (256 : ℝ) ≤ L := by
      rw [hLdef]; exact Real.log_le_log (by norm_num) hK256
    have h : Real.log (256 : ℝ) = 8 * Real.log 2 := by
      rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.log_pow]
      norm_num
    linarith
  have hL0 : 0 < L := by linarith
  have hLK : L ≤ K - 1 := by rw [hLdef]; exact Real.log_le_sub_one_of_pos hK0
  have hsqK : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK0.le
  have hsqK16 : (16 : ℝ) ≤ Real.sqrt K := by
    have h := Real.sqrt_le_sqrt (show (256 : ℝ) ≤ K by linarith)
    rwa [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h
  have hLsq : L ≤ 2 * (Real.sqrt K - 1) := by
    have h1 : Real.log (Real.sqrt K) ≤ Real.sqrt K - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_sqrt hK0.le, ← hLdef] at h1
    linarith
  -- the number of edges, the abbreviation `B = 2 ^ (k - 1)`, and `t = B * k / #H`
  have hm1 : (1 : ℝ) ≤ (H.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hH
  set m : ℝ := (H.card : ℝ) with hmdef
  clear_value m
  have hm0 : 0 < m := by linarith
  set S : ℝ := Real.sqrt (K / L) with hSdef
  clear_value S
  have hS0 : 0 < S := by rw [hSdef]; exact Real.sqrt_pos.mpr (by positivity)
  set B : ℝ := (2 : ℝ) ^ (k - 1) with hBdef
  clear_value B
  have hB0 : 0 < B := by rw [hBdef]; positivity
  have hBk : B * 2 = (2 : ℝ) ^ k := by
    rw [hBdef, ← pow_succ]
    congr 1
    omega
  set t : ℝ := B * K / m with htdef
  clear_value t
  have ht0 : 0 < t := by rw [htdef]; positivity
  have htm : m * t = B * K := by rw [htdef]; field_simp
  -- the lower bound `t₀ = 4 √(k log k)` on `t`
  set t₀ : ℝ := 4 * Real.sqrt (K * L) with ht₀def
  clear_value t₀
  have hsqKL : Real.sqrt (K * L) ^ 2 = K * L := Real.sq_sqrt (by positivity)
  have hsqKL1 : (1 : ℝ) ≤ Real.sqrt (K * L) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ K * L by nlinarith only [hK256, hL4])
    rwa [Real.sqrt_one] at h
  have ht₀4 : (4 : ℝ) ≤ t₀ := by rw [ht₀def]; linarith
  have ht₀0 : 0 < t₀ := by linarith
  have ht₀sq : t₀ ^ 2 = 16 * (K * L) := by rw [ht₀def, mul_pow, hsqKL]; norm_num
  have hSprod : S * Real.sqrt (K * L) = K := by
    rw [hSdef, ← Real.sqrt_mul (by positivity)]
    rw [show K / L * (K * L) = K ^ 2 by field_simp]
    exact Real.sqrt_sq hK0.le
  have htt₀ : t₀ ≤ t := by
    have hmS : m ≤ S * B / 4 := by
      have h : (1 : ℝ) / 8 * S * 2 ^ k = S * B / 4 := by rw [← hBk]; ring
      linarith
    rw [htdef, le_div_iff₀ hm0]
    have h1 : t₀ * m ≤ t₀ * (S * B / 4) := mul_le_mul_of_nonneg_left hmS ht₀0.le
    have h2 : t₀ * (S * B / 4) = B * K := by
      rw [ht₀def]; linear_combination B * hSprod
    linarith only [h1, h2]
  have ht1 : (1 : ℝ) < t := by linarith
  have ht2 : 0 < t ^ 2 := pow_pos ht0 2
  have ht₀2 : 0 < t₀ ^ 2 := pow_pos ht₀0 2
  -- the split parameter `p = log t / k`
  set p : ℝ := Real.log t / K with hpdef
  clear_value p
  have hlogt0 : 0 ≤ Real.log t₀ := Real.log_nonneg (by linarith)
  have hlogtpos : 0 < Real.log t := Real.log_pos ht1
  have hp0 : 0 < p := by rw [hpdef]; exact div_pos hlogtpos hK0
  have hpK : p * K = Real.log t := by rw [hpdef]; field_simp
  have hp1 : p ≤ 1 := by
    have htB : t ≤ B * K := by
      rw [htdef, div_le_iff₀ hm0]
      nlinarith only [mul_nonneg (mul_pos hB0 hK0).le (sub_nonneg.mpr hm1)]
    have hlogB : Real.log B = (K - 1) * Real.log 2 := by
      rw [hBdef, Real.log_pow, hKdef]
      have h1 : (1 : ℕ) ≤ k := by omega
      rw [Nat.cast_sub h1]
      norm_num
    have h1 : Real.log t ≤ Real.log (B * K) := Real.log_le_log ht0 htB
    rw [Real.log_mul (ne_of_gt hB0) (ne_of_gt hK0), hlogB, ← hLdef] at h1
    rw [hpdef, div_le_one hK0]
    have step1 : (K - 1) * Real.log 2 ≤ (K - 1) * 0.6931471808 :=
      mul_le_mul_of_nonneg_left hlog2lt.le (by linarith)
    have step2 : 2 * Real.sqrt K ≤ 3 / 10 * K := by
      nlinarith only [hsqK, hsqK16, Real.sqrt_nonneg K]
    linarith only [h1, step1, step2, hLsq, hK0]
  -- the tail term: `2 #H ((1 - p) / 2) ^ k ≤ k / t ^ 2`
  have hexp : (1 - p) ^ k ≤ 1 / t := by
    have h2 : 1 - p ≤ Real.exp (-p) := by
      have h := Real.add_one_le_exp (-p); linarith
    have h3 : (1 - p) ^ k ≤ Real.exp (-p) ^ k :=
      pow_le_pow_left₀ (by linarith) h2 k
    have h4 : Real.exp (-p) ^ k = 1 / t := by
      rw [← Real.exp_nat_mul,
        show (k : ℝ) * (-p) = -Real.log t by rw [← hpK, ← hKdef]; ring,
        Real.exp_neg, Real.exp_log ht0]
      ring
    linarith only [h3, h4.le, h4.ge]
  have hterm1 : 2 * m * ((1 - p) / 2) ^ k ≤ K / t ^ 2 := by
    have hstep : 2 * m * ((1 - p) / 2) ^ k ≤ 2 * m * (1 / t / 2 ^ k) := by
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      rw [div_pow]
      gcongr
    have heq : 2 * m * (1 / t / 2 ^ k) = K / t ^ 2 := by
      have hL1 : 2 * m * (1 / t / 2 ^ k) = 2 * m / (t * 2 ^ k) := by ring
      rw [hL1, ← hBk,
        div_eq_div_iff (mul_pos ht0 (by linarith : (0 : ℝ) < B * 2)).ne' ht2.ne']
      linear_combination 2 * t * htm
    linarith only [hstep, heq.le, heq.ge]
  -- the conflicting-pair term: `#H ^ 2 ∫ ≤ k log t / t ^ 2`
  have hB4 : B ^ 2 = (4 : ℝ) ^ (k - 1) := by
    rw [hBdef, ← pow_mul, mul_comm, pow_mul]; norm_num
  have hterm2 : m ^ 2 * (∫ x in (1 - p) / 2..(1 + p) / 2,
      x ^ (k - 1) * (1 - x) ^ (k - 1)) ≤ K * Real.log t / t ^ 2 := by
    have h1 : m ^ 2 * (∫ x in (1 - p) / 2..(1 + p) / 2,
        x ^ (k - 1) * (1 - x) ^ (k - 1)) ≤ m ^ 2 * (p * (1 / 4) ^ (k - 1)) :=
      mul_le_mul_of_nonneg_left
        (integral_pow_mul_one_sub_pow_le (k - 1) hp0.le hp1) (sq_nonneg m)
    have h4pow : ((1 : ℝ) / 4) ^ (k - 1) = 1 / B ^ 2 := by
      rw [hB4, div_pow, one_pow]
    have heq : m ^ 2 * (p * (1 / B ^ 2)) = K * Real.log t / t ^ 2 := by
      have hL1 : m ^ 2 * (p * (1 / B ^ 2)) = m ^ 2 * p / B ^ 2 := by ring
      rw [hL1, div_eq_div_iff (pow_pos hB0 2).ne' ht2.ne', ← hpK]
      linear_combination (p * (m * t + B * K)) * htm
    rw [h4pow] at h1
    linarith only [h1, heq.le, heq.ge]
  -- the two terms together stay below one
  have hmono : K / t ^ 2 + K * Real.log t / t ^ 2 ≤ K * (1 + Real.log t₀) / t₀ ^ 2 := by
    have hcomb : K / t ^ 2 + K * Real.log t / t ^ 2 = K * (1 + Real.log t) / t ^ 2 := by
      field_simp
    rw [hcomb, div_le_div_iff₀ ht2 ht₀2]
    have hlogdiv : Real.log t - Real.log t₀ ≤ t / t₀ - 1 := by
      rw [← Real.log_div (ne_of_gt ht0) (ne_of_gt ht₀0)]
      exact Real.log_le_sub_one_of_pos (div_pos ht0 ht₀0)
    have hlin : (1 + Real.log t) * t₀ ≤ Real.log t₀ * t₀ + t := by
      have h := mul_le_mul_of_nonneg_right hlogdiv ht₀0.le
      rw [sub_mul, sub_mul, div_mul_cancel₀ _ (ne_of_gt ht₀0)] at h
      linarith only [h]
    have e1 := mul_le_mul_of_nonneg_left hlin (mul_nonneg hK0.le ht₀0.le)
    have hsqle : t₀ ^ 2 ≤ t ^ 2 := by nlinarith only [htt₀, ht₀0]
    have e2 : K * Real.log t₀ * t₀ ^ 2 ≤ K * Real.log t₀ * t ^ 2 :=
      mul_le_mul_of_nonneg_left hsqle (mul_nonneg hK0.le hlogt0)
    have e3 := mul_le_mul_of_nonneg_left htt₀ (mul_nonneg hK0.le ht0.le)
    nlinarith only [e1, e2, e3]
  have hA : Real.log t₀ ≤ Real.log 4 + L := by
    have hle : t₀ ≤ 4 * K := by
      have hsle : Real.sqrt (K * L) ≤ K := by
        have h2 := Real.sqrt_le_sqrt
          (show K * L ≤ K ^ 2 by nlinarith only [hLK, hK0])
        rwa [Real.sqrt_sq hK0.le] at h2
      rw [ht₀def]; linarith
    calc Real.log t₀ ≤ Real.log (4 * K) := Real.log_le_log ht₀0 hle
      _ = Real.log 4 + L := by rw [Real.log_mul (by norm_num) (ne_of_gt hK0), ← hLdef]
  have hlog4 : Real.log 4 < 1.3862943616 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
    linarith
  have hlast : K * (1 + Real.log t₀) / t₀ ^ 2 < 1 := by
    rw [div_lt_one ht₀2, ht₀sq]
    have h := mul_pos hK0
      (show (0 : ℝ) < 16 * L - (1 + Real.log t₀) by linarith only [hA, hlog4, hL4])
    nlinarith only [h]
  refine exists_conflictFree_of_union_bound_lt_one hk2 hp0 hp1 huniform ?_
  rw [← hmdef]
  linarith only [hterm1, hterm2, hmono, hlast]

end GreedyColoring

/-- **Radhakrishnan–Srinivasan 2000** (Zhao, Theorem 3.5.1): for some absolute constant `c > 0`,
every `k`-uniform hypergraph with at most `c * √(k / log k) * 2 ^ k` edges is 2-colourable.  This
is the best known lower bound on `m k`, and strengthens `twoColorable_of_card_lt`. -/
theorem exists_twoColorable_of_card_le :
    ∃ c : ℝ, 0 < c ∧ ∀ (α : Type) (_ : Fintype α) (_ : DecidableEq α) (k : ℕ), 2 ≤ k →
      ∀ H : Finset (Finset α), (∀ e ∈ H, e.card = k) →
        (H.card : ℝ) ≤ c * Real.sqrt (k / Real.log k) * 2 ^ k → TwoColorable H := by
  obtain ⟨c₀, k₀, hc₀, hB⟩ := exists_conflictFree_of_card_le
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set s : ℝ := Real.sqrt ((k₀ : ℝ) / Real.log 2)
  have hs0 : (0 : ℝ) ≤ s := Real.sqrt_nonneg _
  have hD : (0 : ℝ) < 1 / (2 * (s + 1)) := by positivity
  refine ⟨min c₀ (1 / (2 * (s + 1))), lt_min hc₀ hD, ?_⟩
  intro α hfin hdec k hk H huniform hcard
  have hsq : (0 : ℝ) ≤ Real.sqrt ((k : ℝ) / Real.log k) := Real.sqrt_nonneg _
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  by_cases hkk : k₀ ≤ k
  · have hle : (H.card : ℝ) ≤ c₀ * Real.sqrt ((k : ℝ) / Real.log k) * 2 ^ k :=
      hcard.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (min_le_left _ _) hsq) h2k.le)
    obtain ⟨w, hw⟩ := hB α hfin hdec k hkk H huniform hle
    exact twoColorable_of_no_conflictingPair
      (fun e he => Finset.card_pos.mp (by rw [huniform e he]; omega)) w hw
  · have hklt : (k : ℝ) ≤ (k₀ : ℝ) := by
      have : k ≤ k₀ := by omega
      exact_mod_cast this
    have hlogk : Real.log 2 ≤ Real.log k :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hk)
    have h1 : (k : ℝ) / Real.log k ≤ (k₀ : ℝ) / Real.log 2 := by
      gcongr
    have h2 : Real.sqrt ((k : ℝ) / Real.log k) ≤ s := Real.sqrt_le_sqrt h1
    have h3 : min c₀ (1 / (2 * (s + 1))) * Real.sqrt ((k : ℝ) / Real.log k)
        ≤ 1 / (2 * (s + 1)) * s :=
      mul_le_mul (min_le_right _ _) h2 hsq hD.le
    have h4 : 1 / (2 * (s + 1)) * s < 1 / 2 := by
      rw [div_mul_eq_mul_div, one_mul,
        div_lt_iff₀ (show (0 : ℝ) < 2 * (s + 1) by positivity)]
      linarith
    have h5 : (H.card : ℝ) < 1 / 2 * 2 ^ k :=
      lt_of_le_of_lt (hcard.trans (mul_le_mul_of_nonneg_right h3 h2k.le))
        (mul_lt_mul_of_pos_right h4 h2k)
    have h6 : (2 : ℝ) ^ (k - 1) * 2 = (2 : ℝ) ^ k := by
      rw [← pow_succ]
      congr 1
      omega
    have h7 : (H.card : ℝ) < ((2 ^ (k - 1) : ℕ) : ℝ) := by
      push_cast
      linarith
    exact twoColorable_of_card_lt hk huniform (by exact_mod_cast h7)

end ProbMethodCombinatorics
