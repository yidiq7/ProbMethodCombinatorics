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

/-- **Erdős 1959** (Zhao, Theorem 3.4.1): there are graphs of arbitrarily large girth and
arbitrarily large chromatic number — high chromatic number cannot be certified locally. -/
theorem exists_girth_gt_and_chromaticNumber_gt (k l : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      (l : ℕ∞) < G.girth ∧ (k : ℕ∞) < G.chromaticNumber := by
  sorry

/-- **Radhakrishnan–Srinivasan 2000** (Zhao, Theorem 3.5.1): for some absolute constant `c > 0`,
every `k`-uniform hypergraph with at most `c * √(k / log k) * 2 ^ k` edges is 2-colourable.  This
is the best known lower bound on `m k`, and strengthens `twoColorable_of_card_lt`. -/
theorem exists_twoColorable_of_card_le :
    ∃ c : ℝ, 0 < c ∧ ∀ (α : Type) (_ : Fintype α) (_ : DecidableEq α) (k : ℕ), 2 ≤ k →
      ∀ H : Finset (Finset α), (∀ e ∈ H, e.card = k) →
        (H.card : ℝ) ≤ c * Real.sqrt (k / Real.log k) * 2 ^ k → TwoColorable H := by
  sorry

end ProbMethodCombinatorics
