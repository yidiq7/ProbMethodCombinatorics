import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Martingale.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Chapter 9: Concentration of Measure

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Chapter 9.

The chapter's slogan: **a Lipschitz function of many independent random variables is
concentrated.**  Chapter 5's Chernoff bound is the special case where the function is a sum.

Mathlib already has the analytic engine — `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`
is Hoeffding's lemma (Lemma 9.2.12), and `measure_sum_ge_le_of_iIndepFun` is Hoeffding's
inequality for sums of independent sub-Gaussian variables.  What it does not have is Azuma's
inequality or the bounded differences inequality, and the latter is what the applications use.

Only the bounded differences inequality is stated here; the rest of the chapter is planned.
-/

namespace ProbMethodCombinatorics

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Resampling one coordinate preserves a product of probability measures: the map
`(x, ω) ↦ Function.update x i ω` pushes `Measure.pi μ ⊗ μ i` forward to `Measure.pi μ`.

This is the structural form of the independence used in the bounded differences inequality:
coordinate `i` of a sample may be replaced by a fresh sample without changing the law. -/
theorem measurePreserving_update_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (i : ι) :
    MeasurePreserving (fun p : (∀ j, Ω j) × Ω i ↦ Function.update p.1 i p.2)
      ((Measure.pi μ).prod (μ i)) (Measure.pi μ) := by
  refine ⟨measurable_update', (Measure.pi_eq fun s hs ↦ ?_).symm⟩
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (∀ j, Ω j) × Ω i ↦ Function.update p.1 i p.2) ⁻¹' (Set.univ.pi s)
      = (Set.univ.pi (Function.update s i Set.univ)) ×ˢ s i := by
    ext p
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro hp
      refine ⟨fun j ↦ ?_, ?_⟩
      · rcases eq_or_ne j i with rfl | hj
        · simp
        · have hj2 := hp j
          rw [Function.update_of_ne hj] at hj2 ⊢
          exact hj2
      · have := hp i
        rwa [Function.update_self] at this
    · rintro ⟨h1, h2⟩ j
      rcases eq_or_ne j i with rfl | hj
      · rwa [Function.update_self]
      · rw [Function.update_of_ne hj]
        have := h1 j
        rwa [Function.update_of_ne hj] at this
  rw [hpre, Measure.prod_prod, Measure.pi_pi,
    ← Finset.mul_prod_erase Finset.univ (fun j ↦ μ j (Function.update s i Set.univ j))
      (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j ↦ μ j (s j)) (Finset.mem_univ i)]
  have h1 : ∀ j ∈ Finset.univ.erase i, μ j (Function.update s i Set.univ j) = μ j (s j) :=
    fun j hj ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [Finset.prod_congr rfl h1, Function.update_self, measure_univ, one_mul, mul_comm]

/-- Integrating a function against `Measure.pi μ` may be done by first integrating out
coordinate `i` against `μ i` and then integrating over the whole product. -/
theorem integral_integral_update_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (i : ι) (G : (∀ j, Ω j) → ℝ) (hG : Integrable G (Measure.pi μ)) :
    ∫ x, G x ∂(Measure.pi μ)
      = ∫ x, (∫ ω, G (Function.update x i ω) ∂(μ i)) ∂(Measure.pi μ) := by
  have hΦ := measurePreserving_update_pi μ i
  have hGm : AEStronglyMeasurable G
      (Measure.map (fun p : (∀ j, Ω j) × Ω i ↦ Function.update p.1 i p.2)
        ((Measure.pi μ).prod (μ i))) := by
    rw [hΦ.map_eq]; exact hG.aestronglyMeasurable
  have h1 := integral_map (φ := fun p : (∀ j, Ω j) × Ω i ↦ Function.update p.1 i p.2)
    (f := G) hΦ.measurable.aemeasurable hGm
  rw [hΦ.map_eq] at h1
  have hint : Integrable (fun p : (∀ j, Ω j) × Ω i ↦ G (Function.update p.1 i p.2))
      ((Measure.pi μ).prod (μ i)) := hΦ.integrable_comp_of_integrable hG
  rw [h1]
  exact integral_prod _ hint

/-- The other order of `integral_integral_update_pi`: the outer integral is the one over
coordinate `i`. -/
theorem integral_integral_update_pi_symm {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (i : ι) (G : (∀ j, Ω j) → ℝ) (hG : Integrable G (Measure.pi μ)) :
    ∫ x, G x ∂(Measure.pi μ)
      = ∫ ω, (∫ x, G (Function.update x i ω) ∂(Measure.pi μ)) ∂(μ i) := by
  have hΦ := measurePreserving_update_pi μ i
  have hGm : AEStronglyMeasurable G
      (Measure.map (fun p : (∀ j, Ω j) × Ω i ↦ Function.update p.1 i p.2)
        ((Measure.pi μ).prod (μ i))) := by
    rw [hΦ.map_eq]; exact hG.aestronglyMeasurable
  have h1 := integral_map (φ := fun p : (∀ j, Ω j) × Ω i ↦ Function.update p.1 i p.2)
    (f := G) hΦ.measurable.aemeasurable hGm
  rw [hΦ.map_eq] at h1
  have hint : Integrable (fun p : (∀ j, Ω j) × Ω i ↦ G (Function.update p.1 i p.2))
      ((Measure.pi μ).prod (μ i)) := hΦ.integrable_comp_of_integrable hG
  rw [h1]
  exact integral_prod_symm _ hint

/-- A measurable function whose values differ by at most `C` is integrable against a
probability measure. -/
theorem integrable_of_abs_sub_le {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (g : α → ℝ) (hg : Measurable g) {C : ℝ}
    (hb : ∀ z z', |g z - g z'| ≤ C) : Integrable g ν := by
  have hne : Nonempty α := nonempty_of_isProbabilityMeasure ν
  obtain ⟨z₀⟩ := id hne
  refine Integrable.of_mem_Icc (g z₀ - C) (g z₀ + C) hg.aemeasurable (ae_of_all _ fun z ↦ ?_)
  have := abs_le.mp (hb z₀ z)
  constructor <;> [linarith [this.2]; linarith [this.1]]

/-- **Hoeffding's lemma** (Zhao, Lemma 9.2.12) in the form used below: a measurable function
whose values oscillate by at most `b` satisfies, after centring at its mean,
`𝔼 exp (t (g - 𝔼 g)) ≤ exp (t² b² / 8)`.

The range of `g` lies in the interval `[sInf (range g), sInf (range g) + b]` of length `b`, so
this is Mathlib's `hasSubgaussianMGF_of_mem_Icc`, whose parameter `((b - a) / 2) ^ 2` is
`b ^ 2 / 4`, read through the definition of a sub-Gaussian moment-generating function. -/
theorem integral_exp_mul_sub_integral_le_of_abs_sub_le {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (g : α → ℝ) (hg : Measurable g) {b : ℝ}
    (hb : ∀ ω ω', |g ω - g ω'| ≤ b) (t : ℝ) :
    ∫ ω, Real.exp (t * (g ω - ∫ ω', g ω' ∂ν)) ∂ν ≤ Real.exp (t ^ 2 * b ^ 2 / 8) := by
  have hne : Nonempty α := nonempty_of_isProbabilityMeasure ν
  obtain ⟨ω₀⟩ := id hne
  have hb0 : 0 ≤ b := le_trans (by simp) (hb ω₀ ω₀)
  have hbdd : BddBelow (Set.range g) := by
    refine ⟨g ω₀ - b, ?_⟩
    rintro _ ⟨ω, rfl⟩
    have := (abs_le.mp (hb ω₀ ω)).2
    linarith
  set a := sInf (Set.range g) with ha
  have hmem : ∀ ω, g ω ∈ Set.Icc a (a + b) := by
    intro ω
    refine ⟨csInf_le hbdd ⟨ω, rfl⟩, ?_⟩
    have : g ω - b ≤ a := by
      refine le_csInf (Set.range_nonempty g) ?_
      rintro _ ⟨ω', rfl⟩
      have := (abs_le.mp (hb ω ω')).2
      linarith
    linarith
  have hsg := hasSubgaussianMGF_of_mem_Icc (μ := ν) (X := g) hg.aemeasurable
    (ae_of_all _ hmem)
  have hmgf := hsg.mgf_le t
  have hcoe : ((((‖a + b - a‖₊ / 2 : NNReal)) ^ 2 : NNReal) : ℝ) = b ^ 2 / 4 := by
    have hnn : (‖a + b - a‖₊ : ℝ) = b := by
      simp [Real.norm_eq_abs, abs_of_nonneg hb0]
    push_cast [hnn]
    ring
  rw [mgf] at hmgf
  refine hmgf.trans_eq ?_
  rw [Real.exp_eq_exp, hcoe]
  ring

/-- A function with bounded differences has oscillation at most `∑ i, c i`: any two points of
the product are joined by a path that changes one coordinate at a time. -/
theorem abs_sub_le_sum_of_bddDiff {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    (f : (∀ i, Ω i) → ℝ) (c : ι → ℝ)
    (hc : ∀ i (x y : ∀ i, Ω i), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    (x y : ∀ i, Ω i) : |f x - f y| ≤ ∑ i, c i := by
  have key : ∀ s : Finset ι, ∀ x y : ∀ i, Ω i, (∀ j, j ∉ s → x j = y j) →
      |f x - f y| ≤ ∑ i ∈ s, c i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro x y h
      have : x = y := funext fun j ↦ h j (by simp)
      simp [this]
    | insert i s hi ih =>
      intro x y h
      have h1 : |f x - f (Function.update x i (y i))| ≤ c i := by
        refine hc i x _ fun j hj ↦ ?_
        rw [Function.update_of_ne hj]
      have h2 : |f (Function.update x i (y i)) - f y| ≤ ∑ j ∈ s, c j := by
        refine ih _ y fun j hj ↦ ?_
        rcases eq_or_ne j i with rfl | hji
        · rw [Function.update_self]
        · rw [Function.update_of_ne hji]
          exact h j fun hmem ↦ by
            rcases Finset.mem_insert.mp hmem with h' | h'
            · exact hji h'
            · exact hj h'
      rw [Finset.sum_insert hi]
      calc |f x - f y| ≤ |f x - f (Function.update x i (y i))|
            + |f (Function.update x i (y i)) - f y| := abs_sub_le _ _ _
        _ ≤ c i + ∑ j ∈ s, c j := add_le_add h1 h2
  exact key Finset.univ x y fun j hj ↦ absurd (Finset.mem_univ j) hj

/-- The function `x ↦ ∫ y, f (x on s, y off s)`, the value at `x` of the Doob martingale of `f`
at time `s`, is measurable. -/
theorem measurable_integral_merge {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, Ω i) → ℝ) (hf : Measurable f) (s : Finset ι) :
    Measurable fun x : ∀ i, Ω i ↦
      ∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ) := by
  have hm : Measurable fun p : ((∀ j, Ω j) × (∀ j, Ω j)) ↦
      f (fun j ↦ if j ∈ s then p.1 j else p.2 j) := by
    refine hf.comp (measurable_pi_lambda _ fun j ↦ ?_)
    by_cases hj : j ∈ s
    · simp only [hj, if_true]
      exact (measurable_pi_apply j).comp measurable_fst
    · simp only [hj, if_false]
      exact (measurable_pi_apply j).comp measurable_snd
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := Measure.pi μ)).measurable

/-- Integrating out the coordinates outside `s` preserves the bounded differences of `f`:
changing coordinate `i` of `x` alone moves `x ↦ ∫ y, f (x on s, y off s)` by at most `c i`. -/
theorem abs_sub_integral_merge_le {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, Ω i) → ℝ) (c : ι → ℝ) (hf : Measurable f)
    (hc : ∀ i (x y : ∀ i, Ω i), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    (s : Finset ι) (i : ι) (x x' : ∀ j, Ω j) (h : ∀ j, j ≠ i → x j = x' j) :
    |(∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ))
      - ∫ y, f (fun j ↦ if j ∈ s then x' j else y j) ∂(Measure.pi μ)| ≤ c i := by
  have hmeas : ∀ z : ∀ j, Ω j, Measurable fun y : ∀ j, Ω j ↦
      f (fun j ↦ if j ∈ s then z j else y j) := by
    intro z
    refine hf.comp (measurable_pi_lambda _ fun j ↦ ?_)
    by_cases hj : j ∈ s
    · simp only [hj, if_true]
      exact measurable_const
    · simp only [hj, if_false]
      exact measurable_pi_apply j
  have hint : ∀ z : ∀ j, Ω j, Integrable (fun y : ∀ j, Ω j ↦
      f (fun j ↦ if j ∈ s then z j else y j)) (Measure.pi μ) := fun z ↦
    integrable_of_abs_sub_le _ _ (hmeas z) (C := ∑ i, c i)
      (fun u v ↦ abs_sub_le_sum_of_bddDiff f c hc _ _)
  rw [← integral_sub (hint x) (hint x')]
  have hb : ∀ y : ∀ j, Ω j, ‖f (fun j ↦ if j ∈ s then x j else y j)
      - f (fun j ↦ if j ∈ s then x' j else y j)‖ ≤ c i := by
    intro y
    rw [Real.norm_eq_abs]
    refine hc i _ _ fun j hj ↦ ?_
    by_cases hjs : j ∈ s
    · simp only [hjs, if_true, h j hj]
    · simp only [hjs, if_false]
  simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const (μ := Measure.pi μ)
    (ae_of_all _ hb)

/-- The moment-generating function bound behind the bounded differences inequality: for every
finite set `s` of coordinates, the function `F s : x ↦ ∫ y, f (x on s, y off s)` obtained by
integrating out the coordinates outside `s`, centred at `∫ f`, satisfies
`𝔼 exp (t (F s - 𝔼 f)) ≤ exp (t² (∑ i ∈ s, c i ^ 2) / 8)`.

This is Zhao's Theorem 9.2.9, the Doob-martingale refinement of Azuma's inequality, proved by
induction on `s`.  Adding a coordinate `i` to `s` multiplies the moment-generating function by
the conditional moment-generating function of the increment `F (insert i s) - F s`, which given
the other coordinates is a mean-zero function of coordinate `i` oscillating by at most `c i`;
Hoeffding's lemma bounds that factor by `exp (t² (c i) ^ 2 / 8)`. -/
theorem integral_exp_mul_integral_merge_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : (∀ i, Ω i) → ℝ) (c : ι → ℝ) (hf : Measurable f)
    (hc : ∀ i (x y : ∀ i, Ω i), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    (t : ℝ) (s : Finset ι) :
    ∫ x, Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ))
      - ∫ y, f y ∂(Measure.pi μ))) ∂(Measure.pi μ)
      ≤ Real.exp (t ^ 2 * (∑ i ∈ s, c i ^ 2) / 8) := by
  have hmeasM : ∀ (s : Finset ι) (z : ∀ j, Ω j),
      Measurable fun y : ∀ j, Ω j ↦ f (fun j ↦ if j ∈ s then z j else y j) := by
    intro s z
    refine hf.comp (measurable_pi_lambda _ fun j ↦ ?_)
    by_cases hj : j ∈ s
    · simp only [hj, if_true]
      exact measurable_const
    · simp only [hj, if_false]
      exact measurable_pi_apply j
  have hintM : ∀ (s : Finset ι) (z : ∀ j, Ω j),
      Integrable (fun y : ∀ j, Ω j ↦ f (fun j ↦ if j ∈ s then z j else y j)) (Measure.pi μ) :=
    fun s z ↦ integrable_of_abs_sub_le _ _ (hmeasM s z) (C := ∑ i, c i)
      (fun u v ↦ abs_sub_le_sum_of_bddDiff f c hc _ _)
  have hintf : Integrable f (Measure.pi μ) :=
    integrable_of_abs_sub_le _ _ hf (fun u v ↦ abs_sub_le_sum_of_bddDiff f c hc _ _)
  have hK : ∀ (s : Finset ι) (x : ∀ j, Ω j),
      |(∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ))
        - ∫ y, f y ∂(Measure.pi μ)| ≤ ∑ i, c i := by
    intro s x
    rw [← integral_sub (hintM s x) hintf]
    have hb : ∀ y : ∀ j, Ω j,
        ‖f (fun j ↦ if j ∈ s then x j else y j) - f y‖ ≤ ∑ i, c i := fun y ↦ by
      rw [Real.norm_eq_abs]
      exact abs_sub_le_sum_of_bddDiff f c hc _ _
    simpa [Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const (μ := Measure.pi μ) (ae_of_all _ hb)
  have hbnd : ∀ (s : Finset ι) (x : ∀ j, Ω j),
      t * ((∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ))
        - ∫ y, f y ∂(Measure.pi μ)) ≤ |t| * ∑ i, c i := by
    intro s x
    have hle : t * ((∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ))
          - ∫ y, f y ∂(Measure.pi μ))
        ≤ |t| * |(∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ))
          - ∫ y, f y ∂(Measure.pi μ)| := by
      rw [← abs_mul]
      exact le_abs_self _
    exact hle.trans (mul_le_mul_of_nonneg_left (hK s x) (abs_nonneg t))
  have hexpInt : ∀ s : Finset ι, Integrable (fun x : ∀ j, Ω j ↦ Real.exp (t *
      ((∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ))
        - ∫ y, f y ∂(Measure.pi μ)))) (Measure.pi μ) := by
    intro s
    exact Integrable.of_mem_Icc 0 (Real.exp (|t| * ∑ i, c i))
      ((((measurable_integral_merge μ f hf s).sub_const _).const_mul t).exp).aemeasurable
      (ae_of_all _ fun x ↦ ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr (hbnd s x)⟩)
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hA : ∀ x : ∀ j, Ω j,
        (∫ ω, (∫ y, f (fun j ↦ if j ∈ insert i s then Function.update x i ω j
            else y j) ∂(Measure.pi μ)) ∂(μ i))
          = ∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ) := by
      intro x
      rw [integral_integral_update_pi_symm μ i
        (fun y ↦ f (fun j ↦ if j ∈ s then x j else y j)) (hintM s x)]
      refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
      refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
      show f (fun j ↦ if j ∈ insert i s then Function.update x i ω j else y j)
        = f (fun j ↦ if j ∈ s then x j else Function.update y i ω j)
      congr 1
      funext j
      rcases eq_or_ne j i with rfl | hj
      · simp [hi]
      · simp [Finset.mem_insert, hj]
    have hstep : ∀ x : ∀ j, Ω j,
        (∫ ω, Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ insert i s then Function.update x i ω j
            else y j) ∂(Measure.pi μ)) - ∫ y, f y ∂(Measure.pi μ))) ∂(μ i))
          ≤ Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ))
            - ∫ y, f y ∂(Measure.pi μ))) * Real.exp (t ^ 2 * c i ^ 2 / 8) := by
      intro x
      have hgm : Measurable fun ω ↦ ∫ y, f (fun j ↦ if j ∈ insert i s then
          Function.update x i ω j else y j) ∂(Measure.pi μ) :=
        (measurable_integral_merge μ f hf (insert i s)).comp (measurable_update x)
      have hgb : ∀ ω ω' : Ω i,
          |(∫ y, f (fun j ↦ if j ∈ insert i s then Function.update x i ω j
              else y j) ∂(Measure.pi μ))
            - (∫ y, f (fun j ↦ if j ∈ insert i s then Function.update x i ω' j
              else y j) ∂(Measure.pi μ))| ≤ c i := by
        intro ω ω'
        refine abs_sub_integral_merge_le μ f c hf hc (insert i s) i _ _ fun j hj ↦ ?_
        rw [Function.update_of_ne hj, Function.update_of_ne hj]
      have hH := integral_exp_mul_sub_integral_le_of_abs_sub_le (μ i)
        (fun ω ↦ ∫ y, f (fun j ↦ if j ∈ insert i s then Function.update x i ω j
          else y j) ∂(Measure.pi μ)) hgm hgb t
      rw [hA x] at hH
      calc (∫ ω, Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ insert i s then
              Function.update x i ω j else y j) ∂(Measure.pi μ))
            - ∫ y, f y ∂(Measure.pi μ))) ∂(μ i))
          = ∫ ω, Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ))
                - ∫ y, f y ∂(Measure.pi μ)))
              * Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ insert i s then
                    Function.update x i ω j else y j) ∂(Measure.pi μ))
                  - (∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ))))
              ∂(μ i) := by
            refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
            show Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ insert i s then
                  Function.update x i ω j else y j) ∂(Measure.pi μ))
                - ∫ y, f y ∂(Measure.pi μ)))
              = Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ))
                  - ∫ y, f y ∂(Measure.pi μ)))
                * Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ insert i s then
                      Function.update x i ω j else y j) ∂(Measure.pi μ))
                    - (∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ))))
            rw [← Real.exp_add, Real.exp_eq_exp]
            ring
        _ = Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ))
                - ∫ y, f y ∂(Measure.pi μ)))
              * ∫ ω, Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ insert i s then
                    Function.update x i ω j else y j) ∂(Measure.pi μ))
                  - (∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ))))
                ∂(μ i) := integral_const_mul _ _
        _ ≤ Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ))
                - ∫ y, f y ∂(Measure.pi μ))) * Real.exp (t ^ 2 * c i ^ 2 / 8) :=
            mul_le_mul_of_nonneg_left hH (Real.exp_pos _).le
    rw [integral_integral_update_pi μ i
      (fun x ↦ Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ insert i s then x j
        else y j) ∂(Measure.pi μ)) - ∫ y, f y ∂(Measure.pi μ)))) (hexpInt (insert i s))]
    calc (∫ x, (∫ ω, Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ insert i s then
              Function.update x i ω j else y j) ∂(Measure.pi μ))
            - ∫ y, f y ∂(Measure.pi μ))) ∂(μ i)) ∂(Measure.pi μ))
        ≤ ∫ x, Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ))
              - ∫ y, f y ∂(Measure.pi μ))) * Real.exp (t ^ 2 * c i ^ 2 / 8)
            ∂(Measure.pi μ) :=
          integral_mono_of_nonneg
            (ae_of_all _ fun x ↦ integral_nonneg fun ω ↦ (Real.exp_pos _).le)
            ((hexpInt s).mul_const _) (ae_of_all _ hstep)
      _ = (∫ x, Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ))
              - ∫ y, f y ∂(Measure.pi μ))) ∂(Measure.pi μ))
            * Real.exp (t ^ 2 * c i ^ 2 / 8) := integral_mul_const _ _
      _ ≤ Real.exp (t ^ 2 * (∑ j ∈ s, c j ^ 2) / 8) * Real.exp (t ^ 2 * c i ^ 2 / 8) :=
          mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
      _ = Real.exp (t ^ 2 * (∑ j ∈ insert i s, c j ^ 2) / 8) := by
          rw [← Real.exp_add, Finset.sum_insert hi]
          ring_nf

/-- A function with bounded differences on a product of probability spaces is sub-Gaussian about
its mean, with parameter `(∑ i, c i ^ 2) / 4`.

This is the whole content of the bounded differences inequality: it is the case `s = univ` of
`integral_exp_mul_integral_merge_le`, whose bound `exp (t² (∑ i, c i ^ 2) / 8)` is exactly the
bound `exp (σ² t² / 2)` defining `HasSubgaussianMGF` for `σ² = (∑ i, c i ^ 2) / 4`. -/
theorem hasSubgaussianMGF_sub_integral_of_bddDiff {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, Ω i) → ℝ) (c : ι → ℝ) (hf : Measurable f)
    (hc : ∀ i (x y : ∀ i, Ω i), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i) :
    HasSubgaussianMGF (fun x ↦ f x - ∫ y, f y ∂(Measure.pi μ))
      (((∑ i, c i ^ 2) / 4).toNNReal) (Measure.pi μ) := by
  let _ : DecidableEq ι := (Fintype.equivFin ι).decidableEq
  have hintf : Integrable f (Measure.pi μ) :=
    integrable_of_abs_sub_le _ _ hf fun u v ↦ abs_sub_le_sum_of_bddDiff f c hc _ _
  have hKuniv : ∀ x : ∀ j, Ω j, |f x - ∫ y, f y ∂(Measure.pi μ)| ≤ ∑ i, c i := by
    intro x
    have h1 : (∫ y, (f x - f y) ∂(Measure.pi μ)) = f x - ∫ y, f y ∂(Measure.pi μ) := by
      rw [integral_sub (integrable_const _) hintf]
      simp
    rw [← h1]
    have hb : ∀ y : ∀ j, Ω j, ‖f x - f y‖ ≤ ∑ i, c i := fun y ↦ by
      rw [Real.norm_eq_abs]
      exact abs_sub_le_sum_of_bddDiff f c hc _ _
    simpa [Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const (μ := Measure.pi μ) (ae_of_all _ hb)
  have huniv : ∀ x : ∀ j, Ω j,
      (∫ y, f (fun j ↦ if j ∈ (Finset.univ : Finset ι) then x j else y j) ∂(Measure.pi μ))
        = f x := by
    intro x
    simp
  constructor
  · intro t
    refine Integrable.of_mem_Icc 0 (Real.exp (|t| * ∑ i, c i))
      (((hf.sub_const _).const_mul t).exp).aemeasurable (ae_of_all _ fun x ↦ ?_)
    refine ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr ?_⟩
    calc t * (f x - ∫ y, f y ∂(Measure.pi μ))
        ≤ |t * (f x - ∫ y, f y ∂(Measure.pi μ))| := le_abs_self _
      _ = |t| * |f x - ∫ y, f y ∂(Measure.pi μ)| := abs_mul _ _
      _ ≤ |t| * ∑ i, c i := mul_le_mul_of_nonneg_left (hKuniv x) (abs_nonneg t)
  · intro t
    have hmain := integral_exp_mul_integral_merge_le μ f c hf hc t Finset.univ
    simp only [huniv] at hmain
    refine (le_of_eq ?_).trans (hmain.trans (le_of_eq ?_))
    · rw [mgf]
    · rw [Real.exp_eq_exp, Real.coe_toNNReal _ (by positivity)]
      ring

/-- **The bounded differences inequality** (Zhao, Theorem 9.1.3; also McDiarmid's inequality and
the Azuma–Hoeffding inequality).  If changing the `i`-th coordinate alone moves `f` by at most
`c i`, then `f` of independent coordinates is concentrated about its mean:

    ℙ(f - 𝔼f ≥ λ) ≤ exp(-2λ² / ∑ᵢ cᵢ²).

Taking `f` to be a sum recovers the Chernoff bound of Chapter 5, so this is a genuine
generalisation: the window of fluctuation has length `O(√n)` for any `1`-Lipschitz `f`, whether
or not it is a sum.

The source proves it from Azuma's inequality applied to the Doob martingale of `f`
(Theorems 9.2.8 and 9.2.9), whose engine is Hoeffding's lemma — already in Mathlib as
`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`.

`f` is assumed measurable, and the assumption is not cosmetic: the bounded differences
condition alone does not give it, a Mathlib measure of a non-measurable set is its *outer*
measure, and `∫` of a non-integrable function is junk `0`.  Without `hf` a non-measurable `f`
with range of diameter `c₀` makes the left-hand side `1` and the statement false.  Measurable
and bounded-differences together do give integrability, so no separate hypothesis is needed for
the `∫`. -/
theorem measure_sub_integral_ge_le {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, Ω i) → ℝ) (c : ι → ℝ) (hf : Measurable f)
    (hc : ∀ i (x y : ∀ i, Ω i), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    (hsum : 0 < ∑ i, c i ^ 2) {lam : ℝ} (hlam : 0 ≤ lam) :
    (Measure.pi μ {x | lam ≤ f x - ∫ y, f y ∂(Measure.pi μ)}).toReal
      ≤ Real.exp (-2 * lam ^ 2 / ∑ i, c i ^ 2) := by
  have hcoe : ((((∑ i, c i ^ 2) / 4).toNNReal : NNReal) : ℝ) = (∑ i, c i ^ 2) / 4 :=
    Real.coe_toNNReal _ (by positivity)
  have := (hasSubgaussianMGF_sub_integral_of_bddDiff μ f c hf hc).measure_ge_le hlam
  rw [Measure.real, hcoe] at this
  refine this.trans_eq ?_
  congr 1
  field_simp
  ring

/-- The two-sided bounded differences inequality: both tails carry the same exponential, so the
union bound costs only a factor `2`.

`-f` has the same bounded differences as `f` and mean `-∫ f`, so `measure_sub_integral_ge_le`
applies to it and bounds the lower tail of `f`. -/
private theorem measure_abs_sub_integral_ge_le {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, Ω i) → ℝ) (c : ι → ℝ) (hf : Measurable f)
    (hc : ∀ i (x y : ∀ i, Ω i), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    (hsum : 0 < ∑ i, c i ^ 2) {lam : ℝ} (hlam : 0 ≤ lam) :
    (Measure.pi μ).real {x | lam ≤ |f x - ∫ y, f y ∂(Measure.pi μ)|}
      ≤ 2 * Real.exp (-2 * lam ^ 2 / ∑ i, c i ^ 2) := by
  have hcneg : ∀ i (x y : ∀ i, Ω i), (∀ j, j ≠ i → x j = y j) → |(-f) x - (-f) y| ≤ c i := by
    intro i x y h
    simp only [Pi.neg_apply, show -f x - -f y = f y - f x from by ring]
    exact hc i y x fun j hj => (h j hj).symm
  have hup := measure_sub_integral_ge_le μ f c hf hc hsum hlam
  have hdown := measure_sub_integral_ge_le μ (-f) c hf.neg hcneg hsum hlam
  have hsub : {x | lam ≤ |f x - ∫ y, f y ∂(Measure.pi μ)|}
      ⊆ {x | lam ≤ f x - ∫ y, f y ∂(Measure.pi μ)}
        ∪ {x | lam ≤ (-f) x - ∫ y, (-f) y ∂(Measure.pi μ)} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    rcases abs_cases (f x - ∫ y, f y ∂(Measure.pi μ)) with ⟨heq, _⟩ | ⟨heq, _⟩
    · exact Or.inl (by rw [heq] at hx; exact hx)
    · refine Or.inr ?_
      simp only [Set.mem_ofPred_eq, Pi.neg_apply, integral_neg]
      rw [heq] at hx
      linarith
  calc (Measure.pi μ).real {x | lam ≤ |f x - ∫ y, f y ∂(Measure.pi μ)|}
      ≤ (Measure.pi μ).real ({x | lam ≤ f x - ∫ y, f y ∂(Measure.pi μ)}
          ∪ {x | lam ≤ (-f) x - ∫ y, (-f) y ∂(Measure.pi μ)}) := measureReal_mono hsub
    _ ≤ (Measure.pi μ).real {x | lam ≤ f x - ∫ y, f y ∂(Measure.pi μ)}
          + (Measure.pi μ).real {x | lam ≤ (-f) x - ∫ y, (-f) y ∂(Measure.pi μ)} :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-2 * lam ^ 2 / ∑ i, c i ^ 2) + Real.exp (-2 * lam ^ 2 / ∑ i, c i ^ 2) :=
        add_le_add hup hdown
    _ = 2 * Real.exp (-2 * lam ^ 2 / ∑ i, c i ^ 2) := by ring

/-! ### §9.2 Azuma's inequality

The martingale route to concentration.  Note that `measure_sub_integral_ge_le` above — the
bounded differences inequality, Theorem 9.1.3 — is **already proved without it**, via Mathlib's
Hoeffding bound for sums of independent sub-Gaussians.  So Azuma is not needed for what this
chapter already has; it is the input to §9.3–§9.6, none of which is stated yet. -/

/-- **Azuma's inequality** (Zhao, Theorem 9.2.8; `sources/mit18_226_f22_lec_full.pdf`, printed
p. 132 = PDF p. 138).  A martingale whose increments are bounded by `cᵢ` is concentrated:

    ℙ(Zₙ - Z₀ ≥ λ) ≤ exp (-λ² / (2 (c₁² + ⋯ + cₙ²))).

Theorem 9.2.7 is the case `cᵢ = 1` with `λ` rescaled by `√n`, and is not stated separately.

**Route.** The moment generating function, exactly as in Chapter 5 but conditionally.  Hoeffding's
lemma (Zhao's Lemma 9.2.12: a mean-zero variable in an interval of length `ℓ` has
`𝔼 eˣ ≤ e^{ℓ²/8}`) is **already upstream** as
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`, which this file already
uses for the bounded differences inequality.  Applied to `Zᵢ - Zᵢ₋₁` conditionally on `ℱ (i-1)`
it gives `𝔼[e^{t(Zᵢ-Zᵢ₋₁)} | ℱ (i-1)] ≤ e^{t²cᵢ²/8}`; iterating over `i` and applying Markov at
`t = 4λ/∑cᵢ²` yields the bound.

**The conditional step is the work.**  Mathlib has `Martingale`, `Filtration` and `condExp`, so
the infrastructure exists — what does not exist is a conditional sub-Gaussian MGF bound, and
getting Hoeffding's lemma to apply under `μ[· | ℱ (i-1)]` rather than under `μ` is the whole
difficulty.  Budget for that rather than for the algebra.

No measurability hypothesis is needed on `Z`: `Martingale` includes `Adapted`, so each `Z i` is
`ℱ i`-measurable and hence `m0`-measurable, which is what makes `{ω | λ ≤ Z n ω - Z 0 ω}`
measurable.  Contrast `measure_sub_integral_ge_le`, where `Measurable f` had to be assumed and
its absence made the statement false. -/
theorem measure_martingale_sub_ge_le {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {Z : ℕ → Ω → ℝ}
    (hZ : Martingale Z ℱ μ) (n : ℕ) (c : ℕ → ℝ)
    (hc : ∀ i ∈ Finset.Icc 1 n, ∀ᵐ ω ∂μ, |Z i ω - Z (i - 1) ω| ≤ c i)
    {lam : ℝ} (hlam : 0 < lam) (hsum : 0 < ∑ i ∈ Finset.Icc 1 n, c i ^ 2) :
    (μ {ω | lam ≤ Z n ω - Z 0 ω}).toReal
      ≤ Real.exp (-lam ^ 2 / (2 * ∑ i ∈ Finset.Icc 1 n, c i ^ 2)) := by
  -- Hoeffding's lemma in its analytic form `cosh y ≤ exp (y² / 2)`.  It is Mathlib's
  -- `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` read on the two-point space: the
  -- moment generating function of a symmetric `±y` random variable is `cosh y`.
  have hcosh : ∀ y : ℝ, Real.cosh y ≤ Real.exp (y ^ 2 / 2) := by
    intro y
    set ν : Measure Bool := ((2 : ℝ≥0∞)⁻¹) • (Measure.dirac true + Measure.dirac false) with hν
    have hprob : IsProbabilityMeasure ν := by
      refine ⟨?_⟩
      rw [hν]
      simp only [Measure.smul_apply, Measure.coe_add, Pi.add_apply, measure_univ, smul_eq_mul]
      rw [one_add_one_eq_two, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
    set X : Bool → ℝ := fun b ↦ if b then y else -y with hX
    have hmean : ∫ b, X b ∂ν = 0 := by
      rw [hν, integral_smul_measure, integral_add_measure (by simp) (by simp)]
      simp [hX]
    have hmgf : mgf X ν 1 = Real.cosh y := by
      rw [mgf, hν, integral_smul_measure, integral_add_measure (by simp) (by simp)]
      simp [hX, Real.cosh_eq]
      ring
    have hicc : ∀ᵐ b ∂ν, X b ∈ Set.Icc (-|y|) |y| := by
      filter_upwards with b
      cases b <;> simp [hX, neg_abs_le, le_abs_self, neg_le_abs]
    have hle := (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := ν) (X := X)
      measurable_from_top.aemeasurable hicc hmean).mgf_le 1
    rw [hmgf] at hle
    refine hle.trans_eq ?_
    rw [Real.exp_eq_exp]
    have hcast : (((‖|y| - -|y|‖₊ / 2) ^ 2 : NNReal) : ℝ) = y ^ 2 := by
      push_cast
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [abs_nonneg y] : (0:ℝ) ≤ |y| - -|y|),
        sub_neg_eq_add, ← two_mul, mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0), sq_abs]
    rw [hcast]
    ring
  -- The conditional form of Hoeffding's lemma: a `μ[· | m]`-centred variable bounded by `b`
  -- has conditional moment generating function at most `exp (s² b² / 2)`.  Mathlib's
  -- `HasCondSubgaussianMGF` says this, but only for `[StandardBorelSpace Ω]`, since it is
  -- defined through `condExpKernel`; stated directly in terms of `condExp` it needs no such
  -- hypothesis.  The proof is the usual one: bound `exp (s ·)` on `[-b, b]` by the chord
  -- through its endpoints, whose conditional expectation is `cosh (s b)`.
  have hcondHoeff : ∀ (m : MeasurableSpace Ω), m ≤ m0 → ∀ (D : Ω → ℝ) (b s : ℝ),
      Integrable D μ → μ[D | m] =ᵐ[μ] 0 → (∀ᵐ ω ∂μ, |D ω| ≤ b) →
      μ[fun ω ↦ Real.exp (s * D ω) | m] ≤ᵐ[μ] fun _ ↦ Real.exp (s ^ 2 * b ^ 2 / 2) := by
    intro m hm D b s hD hD0 hb
    have hmeas : AEStronglyMeasurable[m0] (fun ω ↦ Real.exp (s * D ω)) μ :=
      Real.continuous_exp.comp_aestronglyMeasurable (hD.aestronglyMeasurable.const_mul s)
    have hint1 : Integrable (fun ω ↦ Real.exp (s * D ω)) μ := by
      refine Integrable.mono' (integrable_const (Real.exp (|s| * b))) hmeas ?_
      filter_upwards [hb] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.mpr ?_
      calc s * D ω ≤ |s * D ω| := le_abs_self _
        _ = |s| * |D ω| := abs_mul _ _
        _ ≤ |s| * b := by gcongr
    rcases le_or_gt b 0 with hb0 | hb0
    · have hD00 : ∀ᵐ ω ∂μ, D ω = 0 := by
        filter_upwards [hb] with ω hω
        exact abs_eq_zero.mp (le_antisymm (hω.trans hb0) (abs_nonneg (D ω)))
      have heq : (fun ω ↦ Real.exp (s * D ω)) =ᵐ[μ] fun _ ↦ (1 : ℝ) := by
        filter_upwards [hD00] with ω hω; simp [hω]
      filter_upwards [(condExp_congr_ae heq).trans (by rw [condExp_const hm])] with ω hω
      rw [hω]
      exact Real.one_le_exp (by positivity)
    · set A := Real.cosh (s * b) with hA
      set B := Real.sinh (s * b) / b with hB
      have hint2 : Integrable (fun ω ↦ A + B * D ω) μ := (integrable_const A).add (hD.const_mul B)
      have hle : (fun ω ↦ Real.exp (s * D ω)) ≤ᵐ[μ] fun ω ↦ A + B * D ω := by
        filter_upwards [hb] with ω hω
        rw [abs_le] at hω
        obtain ⟨hd1, hd2⟩ := hω
        set d := D ω
        have hp : (0:ℝ) ≤ (b - d) / (2 * b) := div_nonneg (by linarith) (by linarith)
        have hq : (0:ℝ) ≤ (b + d) / (2 * b) := div_nonneg (by linarith) (by linarith)
        have hpq : (b - d) / (2 * b) + (b + d) / (2 * b) = 1 := by field_simp; ring
        have hcv := convexOn_exp.2 (Set.mem_univ (-(s * b))) (Set.mem_univ (s * b)) hp hq hpq
        simp only [smul_eq_mul] at hcv
        have he : (b - d) / (2 * b) * -(s * b) + (b + d) / (2 * b) * (s * b) = s * d := by
          field_simp; ring
        rw [he] at hcv
        refine hcv.trans_eq ?_
        rw [hA, hB, Real.cosh_eq, Real.sinh_eq]
        field_simp
        ring
      have h1 := condExp_mono (m := m) hint1 hint2 hle
      have h2 : μ[fun ω ↦ A + B * D ω | m] =ᵐ[μ] fun _ ↦ A := by
        have hfun : (fun ω ↦ A + B * D ω) = (fun _ ↦ A) + B • D := by
          funext ω; simp [Pi.add_apply, Pi.smul_apply]
        rw [hfun]
        refine (condExp_add (integrable_const A) (hD.smul B) m).trans ?_
        filter_upwards [condExp_smul (𝕜 := ℝ) B D m, hD0] with ω hω hω0
        simp [condExp_const hm A, hω, hω0]
      filter_upwards [h1, h2] with ω hω hω2
      rw [hω2] at hω
      refine hω.trans ((hcosh (s * b)).trans_eq ?_)
      rw [Real.exp_eq_exp]; ring
  -- Setup.  `t` is the value of the Chernoff parameter that optimises the final bound.
  set S := ∑ i ∈ Finset.Icc 1 n, c i ^ 2 with hSdef
  set t := lam / S with htdef
  have htpos : 0 < t := div_pos hlam hsum
  have hZmeas : ∀ k, StronglyMeasurable[m0] (Z k) := fun k ↦ (hZ.1 k).mono (ℱ.le k)
  have hZint : ∀ k, Integrable (Z k) μ := fun k ↦
    integrable_condExp.congr (hZ.2 k (k + 1) (Nat.le_succ k))
  have hincr : ∀ k, k + 1 ≤ n → ∀ᵐ ω ∂μ, |Z (k + 1) ω - Z k ω| ≤ c (k + 1) := by
    intro k hk
    simpa using hc (k + 1) (Finset.mem_Icc.mpr ⟨Nat.succ_le_succ (Nat.zero_le k), hk⟩)
  -- `Zₖ - Z₀` is bounded, hence `exp (t (Zₖ - Z₀))` is integrable.
  have hbd : ∀ k, k ≤ n → ∀ᵐ ω ∂μ, |Z k ω - Z 0 ω| ≤ ∑ i ∈ Finset.Icc 1 k, c i := by
    intro k
    induction k with
    | zero => intro _; filter_upwards with ω; simp
    | succ k ih =>
      intro hk
      filter_upwards [ih (Nat.le_of_succ_le hk), hincr k hk] with ω h1 h2
      rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le k))]
      calc |Z (k + 1) ω - Z 0 ω| = |(Z (k + 1) ω - Z k ω) + (Z k ω - Z 0 ω)| := by ring_nf
        _ ≤ |Z (k + 1) ω - Z k ω| + |Z k ω - Z 0 ω| := abs_add_le _ _
        _ ≤ c (k + 1) + ∑ i ∈ Finset.Icc 1 k, c i := add_le_add h2 h1
        _ = (∑ i ∈ Finset.Icc 1 k, c i) + c (k + 1) := by ring
  have hexpint : ∀ k, k ≤ n → Integrable (fun ω ↦ Real.exp (t * (Z k ω - Z 0 ω))) μ := by
    intro k hk
    refine Integrable.mono' (integrable_const (Real.exp (|t| * ∑ i ∈ Finset.Icc 1 k, c i)))
      (Real.continuous_exp.comp_aestronglyMeasurable
        ((((hZmeas k).sub (hZmeas 0)).aestronglyMeasurable).const_mul t)) ?_
    filter_upwards [hbd k hk] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    calc t * (Z k ω - Z 0 ω) ≤ |t * (Z k ω - Z 0 ω)| := le_abs_self _
      _ = |t| * |Z k ω - Z 0 ω| := abs_mul _ _
      _ ≤ |t| * ∑ i ∈ Finset.Icc 1 k, c i := by gcongr
  -- The moment generating function bound, by induction on the tower property.
  have key : ∀ k, k ≤ n → (∫ ω, Real.exp (t * (Z k ω - Z 0 ω)) ∂μ)
      ≤ Real.exp (t ^ 2 * (∑ i ∈ Finset.Icc 1 k, c i ^ 2) / 2) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hkn : k ≤ n := Nat.le_of_succ_le hk
      set D := fun ω ↦ Z (k + 1) ω - Z k ω with hDdef
      have hDint : Integrable D μ := (hZint (k + 1)).sub (hZint k)
      have hD0 : μ[D | ℱ k] =ᵐ[μ] 0 := by
        have h1 : D = Z (k + 1) - Z k := rfl
        rw [h1]
        have e3 : μ[Z k | ℱ k] = Z k :=
          condExp_of_stronglyMeasurable (ℱ.le k) (hZ.1 k) (hZint k)
        filter_upwards [condExp_sub (hZint (k + 1)) (hZint k) (ℱ k),
          hZ.2 k (k + 1) (Nat.le_succ k)] with ω e1 e2
        simp [e1, e2, e3, Pi.sub_apply]
      have hcond := hcondHoeff (ℱ k) (ℱ.le k) D (c (k + 1)) t hDint hD0 (hincr k hk)
      set F := fun ω ↦ Real.exp (t * (Z k ω - Z 0 ω)) with hFdef
      set G := fun ω ↦ Real.exp (t * D ω) with hGdef
      have hFG : F * G = fun ω ↦ Real.exp (t * (Z (k + 1) ω - Z 0 ω)) := by
        funext ω
        simp only [hFdef, hGdef, hDdef, Pi.mul_apply, ← Real.exp_add]
        ring_nf
      have hFmeas : StronglyMeasurable[ℱ k] F :=
        Real.continuous_exp.comp_stronglyMeasurable
          (((hZ.1 k).sub ((hZ.1 0).mono (ℱ.mono (Nat.zero_le k)))).const_mul t)
      have hGint : Integrable G μ := by
        refine Integrable.mono' (integrable_const (Real.exp (|t| * c (k + 1))))
          (Real.continuous_exp.comp_aestronglyMeasurable
            (hDint.aestronglyMeasurable.const_mul t)) ?_
        filter_upwards [hincr k hk] with ω hω
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        refine Real.exp_le_exp.mpr ?_
        calc t * D ω ≤ |t * D ω| := le_abs_self _
          _ = |t| * |D ω| := abs_mul _ _
          _ ≤ |t| * c (k + 1) := by gcongr
      have hFGint : Integrable (F * G) μ := by rw [hFG]; exact hexpint (k + 1) hk
      have hstep : (∫ ω, (F * G) ω ∂μ)
          ≤ (∫ ω, F ω ∂μ) * Real.exp (t ^ 2 * c (k + 1) ^ 2 / 2) := by
        rw [← integral_condExp (ℱ.le k) (f := F * G)]
        have hmono : ∀ᵐ ω ∂μ,
            (μ[F * G | ℱ k]) ω ≤ F ω * Real.exp (t ^ 2 * c (k + 1) ^ 2 / 2) := by
          filter_upwards [condExp_mul_of_stronglyMeasurable_left hFmeas hFGint hGint, hcond]
            with ω e1 e2
          rw [e1]
          exact mul_le_mul_of_nonneg_left e2 (Real.exp_pos _).le
        calc (∫ ω, (μ[F * G | ℱ k]) ω ∂μ)
            ≤ ∫ ω, F ω * Real.exp (t ^ 2 * c (k + 1) ^ 2 / 2) ∂μ :=
              integral_mono_ae integrable_condExp ((hexpint k hkn).mul_const _) hmono
          _ = (∫ ω, F ω ∂μ) * Real.exp (t ^ 2 * c (k + 1) ^ 2 / 2) := integral_mul_const _ _
      rw [hFG] at hstep
      refine hstep.trans ?_
      calc (∫ ω, F ω ∂μ) * Real.exp (t ^ 2 * c (k + 1) ^ 2 / 2)
          ≤ Real.exp (t ^ 2 * (∑ i ∈ Finset.Icc 1 k, c i ^ 2) / 2)
              * Real.exp (t ^ 2 * c (k + 1) ^ 2 / 2) :=
            mul_le_mul_of_nonneg_right (ih hkn) (Real.exp_pos _).le
        _ = Real.exp (t ^ 2 * (∑ i ∈ Finset.Icc 1 (k + 1), c i ^ 2) / 2) := by
            rw [← Real.exp_add, Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le k))]
            ring_nf
  -- Chernoff's bound at `t = lam / S`.
  have hmark := measure_ge_le_exp_mul_mgf (μ := μ) (X := fun ω ↦ Z n ω - Z 0 ω) (t := t)
    lam htpos.le (hexpint n le_rfl)
  rw [Measure.real] at hmark
  refine hmark.trans ?_
  calc Real.exp (-t * lam) * mgf (fun ω ↦ Z n ω - Z 0 ω) μ t
      ≤ Real.exp (-t * lam) * Real.exp (t ^ 2 * S / 2) :=
        mul_le_mul_of_nonneg_left (by rw [mgf]; exact key n le_rfl) (Real.exp_pos _).le
    _ = Real.exp (-lam ^ 2 / (2 * S)) := by
        rw [← Real.exp_add, Real.exp_eq_exp, htdef]
        field_simp
        ring

/-! ### §9.3 The vertex-exposure product

`measure_sub_integral_ge_le` bounds a function of *independent coordinates*, and applying it to
`χ(G(n, p))` needs `G(n, p)` presented that way.  Which coordinates are chosen decides the
strength of the result: exposing one edge at a time gives `C(n,2)` coordinates and the weak bound
`exp (-2 λ² / C(n,2))`, while exposing one **vertex** at a time gives `n - 1` nonempty coordinates
and Shamir–Spencer's `exp (-2 λ²)` (Theorem 9.3.1).  The difference is the whole point of the
theorem, so the vertex decomposition is the one built here.
-/

section VertexExposure

open unitInterval SimpleGraph

/-- Coordinate `i` of the vertex-exposure product: the potential edges joining `i` to the
vertices below it.  Coordinate `0` is empty, and the block sizes `0, 1, …, n-1` sum to `C(n,2)`,
the number of potential edges. -/
abbrev ExposureBlock (n : ℕ) (i : Fin n) : Type := {j : Fin n // j < i} → Prop

/-- The graph assembled from a vertex-exposure sample: `a` and `b` are adjacent exactly when the
block of the larger records the smaller.

`SimpleGraph.fromRel` supplies symmetry and looplessness, and the guard `a < b` makes the
underlying relation one-directional, so `fromRel` recovers the intended graph rather than a
symmetrised version of something larger. -/
def graphOfExposure {n : ℕ} (x : ∀ i, ExposureBlock n i) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun a b => if h : a < b then x b ⟨a, h⟩ else False

/-- The law of one vertex-exposure block: each potential edge down from `i` is present
independently with probability `p`.  This is the coordinate measure of `setBernoulli`, carried
over to the block. -/
noncomputable def exposureMeasure (n : ℕ) (p : I) (i : Fin n) : Measure (ExposureBlock n i) :=
  Measure.pi fun _ =>
    (toNNReal p) • Measure.dirac True + (toNNReal (σ p)) • Measure.dirac False

/-- Adjacency in the assembled graph, read off the block of the larger endpoint. -/
private theorem adj_graphOfExposure_iff_of_lt {n : ℕ} (x : ∀ i, ExposureBlock n i) {a b : Fin n}
    (h : a < b) : (graphOfExposure x).Adj a b ↔ x b ⟨a, h⟩ := by
  simp only [graphOfExposure, SimpleGraph.fromRel_adj, ne_eq, dif_pos h, dif_neg (asymm h)]
  simp [h.ne]

/-- `graphOfExposure` is injective with an explicit inverse: the only sample assembling to `G`
records, in block `i`, the neighbours of `i` below `i`. -/
private theorem graphOfExposure_eq_iff_eq_adjBlocks {n : ℕ} (x : ∀ i, ExposureBlock n i)
    (G : SimpleGraph (Fin n)) :
    graphOfExposure x = G ↔ x = fun i (j : {j : Fin n // j < i}) => G.Adj j.1 i := by
  constructor
  · rintro rfl
    funext i j
    obtain ⟨j, hj⟩ := j
    exact propext (adj_graphOfExposure_iff_of_lt x hj).symm
  · rintro rfl
    ext a b
    rcases lt_trichotomy a b with h | rfl | h
    · rw [adj_graphOfExposure_iff_of_lt _ h]
    · simp [graphOfExposure]
    · rw [SimpleGraph.adj_comm, adj_graphOfExposure_iff_of_lt _ h, SimpleGraph.adj_comm]

private theorem measurable_graphOfExposure_blocks {n : ℕ} :
    Measurable (graphOfExposure : (∀ i, ExposureBlock n i) → SimpleGraph (Fin n)) := by
  rw [SimpleGraph.measurable_iff_adj]
  intro a b
  rcases lt_trichotomy a b with h | rfl | h
  · have key : (fun x : ∀ i, ExposureBlock n i => (graphOfExposure x).Adj a b)
        = fun x => x b ⟨a, h⟩ := by
      funext x
      exact propext (adj_graphOfExposure_iff_of_lt x h)
    rw [key]
    exact (measurable_pi_apply _).comp (measurable_pi_apply b)
  · simp [graphOfExposure]
  · have key : (fun x : ∀ i, ExposureBlock n i => (graphOfExposure x).Adj a b)
        = fun x => x a ⟨b, h⟩ := by
      funext x
      exact propext ((SimpleGraph.adj_comm _ _ _).trans (adj_graphOfExposure_iff_of_lt x h))
    rw [key]
    exact (measurable_pi_apply _).comp (measurable_pi_apply a)

private theorem measurableSet_simpleGraph_singleton {n : ℕ} (G : SimpleGraph (Fin n)) :
    MeasurableSet ({G} : Set (SimpleGraph (Fin n))) := by
  have h : ({G} : Set (SimpleGraph (Fin n))) = SimpleGraph.Adj ⁻¹' {G.Adj} := by
    ext H
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun h => h ▸ rfl, fun h => SimpleGraph.ext h⟩
  rw [h]
  exact SimpleGraph.measurable_adj (measurableSet_singleton _)

/-- The coordinate measure of `setBernoulli`, evaluated at a singleton of `Prop`. -/
private theorem bernoulliProp_singleton (p : I) (P : Prop) [Decidable P] :
    ((toNNReal p) • Measure.dirac True + (toNNReal (σ p)) • Measure.dirac False) {P}
      = if P then (toNNReal p : ℝ≥0∞) else (toNNReal (σ p) : ℝ≥0∞) := by
  by_cases h : P <;> simp [h, Set.indicator]

/-- Every potential edge is recorded by at most one exposure coordinate. -/
private theorem injective_sym2_ofExposureIndex {n : ℕ} :
    Function.Injective fun e : Σ i : Fin n, {j : Fin n // j < i} => s(e.2.1, e.1) := by
  rintro ⟨i₁, j₁, h₁⟩ ⟨i₂, j₂, h₂⟩ h
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h
  · rfl
  · exact absurd (h₁.trans h₂) (lt_irrefl _)

/-- Every potential edge is recorded by at least one exposure coordinate: the block of its
larger endpoint. -/
private theorem exists_exposureIndex_of_not_isDiag {n : ℕ} {e : Sym2 (Fin n)} (he : ¬ e.IsDiag) :
    ∃ a : Σ i : Fin n, {j : Fin n // j < i}, s(a.2.1, a.1) = e := by
  induction e with | _ a b
  simp only [Sym2.mk_isDiag_iff] at he
  rcases lt_or_gt_of_ne he with h | h
  · exact ⟨⟨b, a, h⟩, rfl⟩
  · exact ⟨⟨a, b, h⟩, Sym2.eq_swap⟩

private theorem card_exposureBlock_univ {n : ℕ} (i : Fin n) :
    (Finset.univ : Finset {j : Fin n // j < i}).card = (i : ℕ) := by
  rw [Finset.card_univ, Fintype.card_subtype, ← Fin.card_Iio]
  congr 1
  ext j
  simp

/-- The block sizes `0, 1, …, n-1` sum to `C(n, 2)`, the number of potential edges. -/
private theorem sum_val_univ_eq_choose_two (n : ℕ) : ∑ i : Fin n, (i : ℕ) = n.choose 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id, Nat.choose_two_right]

/-- **`G(n, p)` is the vertex-exposure product.**  Assembling independent blocks, one per vertex,
gives exactly the binomial random graph.

This is what lets `measure_sub_integral_ge_le` reach `χ(G(n, p))`, and with it §9.3–§9.6.

`graphOfExposure` is a bijection: for `a < b` the pair `{a, b}` is recorded by exactly one
coordinate, namely `⟨a, _⟩` in block `b`, so the coordinates biject with the `C(n,2)` potential
edges and the two product structures match term by term. -/
theorem binomialRandom_eq_map_graphOfExposure (n : ℕ) (p : I) :
    SimpleGraph.binomialRandom (Fin n) p
      = Measure.map graphOfExposure (Measure.pi (exposureMeasure n p)) := by
  classical
  have hb : IsProbabilityMeasure
      ((toNNReal p) • Measure.dirac True + (toNNReal (σ p)) • Measure.dirac False) := ⟨by simp⟩
  have hpr : ∀ i : Fin n, IsProbabilityMeasure (exposureMeasure n p i) := fun i =>
    inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : {j : Fin n // j < i} =>
      (toNNReal p) • Measure.dirac True + (toNNReal (σ p)) • Measure.dirac False))
  refine Measure.ext_of_singleton fun G => ?_
  rw [Measure.map_apply measurable_graphOfExposure_blocks (measurableSet_simpleGraph_singleton G)]
  have hpre : graphOfExposure ⁻¹' ({G} : Set (SimpleGraph (Fin n)))
      = {fun i (j : {j : Fin n // j < i}) => G.Adj j.1 i} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact graphOfExposure_eq_iff_eq_adjBlocks x G
  rw [hpre, Measure.pi_singleton, SimpleGraph.binomialRandom_singleton]
  simp only [exposureMeasure, Measure.pi_singleton]
  -- Block `i` contributes `p` for each neighbour of `i` below `i` and `σ p` for each non-neighbour.
  have hblock : ∀ i : Fin n,
      (∏ x : {j : Fin n // j < i},
          ((toNNReal p) • Measure.dirac True + (toNNReal (σ p)) • Measure.dirac False)
            {G.Adj x.1 i})
        = (toNNReal p : ℝ≥0∞) ^
              (Finset.univ.filter fun x : {j : Fin n // j < i} => G.Adj x.1 i).card
            * (toNNReal (σ p) : ℝ≥0∞) ^
              (Finset.univ.filter fun x : {j : Fin n // j < i} => ¬ G.Adj x.1 i).card := by
    intro i
    rw [Finset.prod_congr rfl fun x _ => bernoulliProp_singleton p (G.Adj x.1 i),
      Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  -- The coordinates that record an edge biject with the edges, via `⟨i, ⟨j, _⟩⟩ ↦ s(j, i)`.
  have hcount : (∑ i : Fin n,
      (Finset.univ.filter fun x : {j : Fin n // j < i} => G.Adj x.1 i).card)
        = G.edgeSet.toFinset.card := by
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun e _ => s(e.2.1, e.1)) ?_ ?_ ?_
    · intro e he
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at he
      simp [Set.mem_toFinset, he]
    · intro e₁ _ e₂ _ h
      exact injective_sym2_ofExposureIndex h
    · intro e he
      rw [Set.mem_toFinset] at he
      obtain ⟨a, ha⟩ := exists_exposureIndex_of_not_isDiag (G.not_isDiag_of_mem_edgeSet he)
      refine ⟨a, ?_, ha⟩
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← SimpleGraph.mem_edgeSet]
      exact ha ▸ he
  have hsplit : ∀ i : Fin n,
      (Finset.univ.filter fun x : {j : Fin n // j < i} => G.Adj x.1 i).card
        + (Finset.univ.filter fun x : {j : Fin n // j < i} => ¬ G.Adj x.1 i).card = (i : ℕ) :=
    fun i => by rw [Finset.card_filter_add_card_filter_not, card_exposureBlock_univ]
  have hsum : G.edgeSet.toFinset.card
      + (∑ i : Fin n, (Finset.univ.filter fun x : {j : Fin n // j < i} => ¬ G.Adj x.1 i).card)
      = n.choose 2 := by
    rw [← hcount, ← Finset.sum_add_distrib, Finset.sum_congr rfl fun i _ => hsplit i]
    exact sum_val_univ_eq_choose_two n
  have hn : (Nat.card (Fin n)).choose 2 = n.choose 2 := by simp
  rw [Finset.prod_congr rfl fun i _ => hblock i, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, hcount,
    Set.ncard_eq_toFinset_card' G.edgeSet, hn]
  congr 1
  congr 1
  omega

/-- Rewiring the edges at `v` costs at most one colour: a proper `k`-colouring of `G` becomes a
proper `(k + 1)`-colouring of `G'` by moving `v` to the fresh colour `Fin.last k`.

Every edge of `G'` avoiding `v` is an edge of `G` by `h`, so its endpoints keep distinct colours;
every edge of `G'` at `v` has one endpoint on `Fin.last k` and the other in the image of
`Fin.castSucc`. -/
private theorem colorable_succ_of_adj_iff_off_vertex {n k : ℕ} {v : Fin n}
    {G G' : SimpleGraph (Fin n)}
    (h : ∀ a b : Fin n, a ≠ v → b ≠ v → (G.Adj a b ↔ G'.Adj a b)) (hG : G.Colorable k) :
    G'.Colorable (k + 1) := by
  classical
  obtain ⟨c⟩ := hG
  refine ⟨SimpleGraph.Coloring.mk
    (fun u => if u = v then Fin.last k else (c u).castSucc) fun {a b} hab => ?_⟩
  by_cases ha : a = v
  · by_cases hb : b = v
    · subst ha
      subst hb
      simp at hab
    · simpa [ha, hb] using (Fin.castSucc_ne_last (c b)).symm
  · by_cases hb : b = v
    · simp [ha, hb]
    · simpa [ha, hb, Fin.castSucc_inj] using c.valid ((h a b ha hb).mpr hab)

/-- **Rewiring one vertex moves the chromatic number by at most one.**  If `G` and `G'` agree on
every edge avoiding `v`, then `|χ(G) - χ(G')| ≤ 1`.

Each direction is the same one-line construction: a proper colouring of `G` with `χ(G)` colours
becomes a proper colouring of `G'` with `χ(G) + 1` by giving `v` a fresh colour.  Every edge of
`G'` avoiding `v` is an edge of `G` and keeps its old colours; every edge of `G'` at `v` is safe
because no other vertex wears the new colour.

This is the bounded-differences input to Shamir–Spencer (Theorem 9.3.1), and it is the reason
that theorem exposes one *vertex* at a time.  The analogous claim for exposing one edge is also
true but weaker in aggregate: `C(n,2)` coordinates instead of `n - 1`.

`ℕ∞.toNat` sends `⊤` to `0`, which would be a junk value — but `Fin n` is finite, so
`SimpleGraph.colorable_of_fintype` puts every chromatic number here below `⊤` and the coercion
is faithful. -/
theorem abs_sub_chromaticNumber_le_one {n : ℕ} (v : Fin n) (G G' : SimpleGraph (Fin n))
    (h : ∀ a b : Fin n, a ≠ v → b ≠ v → (G.Adj a b ↔ G'.Adj a b)) :
    |(G.chromaticNumber.toNat : ℝ) - (G'.chromaticNumber.toNat : ℝ)| ≤ 1 := by
  -- `Fin n` is finite, so both chromatic numbers are below `⊤` and `ENat.toNat` is faithful.
  have hfin : ∀ K : SimpleGraph (Fin n), K.Colorable n := fun K => by
    simpa using K.colorable_of_fintype
  have htop : ∀ K : SimpleGraph (Fin n), K.chromaticNumber ≠ ⊤ := fun K =>
    SimpleGraph.chromaticNumber_ne_top_iff_exists.mpr ⟨n, hfin K⟩
  have hcolor : ∀ K : SimpleGraph (Fin n), K.Colorable K.chromaticNumber.toNat := fun K =>
    SimpleGraph.chromaticNumber_le_iff_colorable.mp
      (le_of_eq (ENat.natCast_toNat (htop K)).symm)
  have hstep : ∀ K K' : SimpleGraph (Fin n),
      (∀ a b : Fin n, a ≠ v → b ≠ v → (K.Adj a b ↔ K'.Adj a b)) →
        K'.chromaticNumber.toNat ≤ K.chromaticNumber.toNat + 1 := fun K K' hKK' =>
    ENat.toNat_le_of_le_natCast
      (SimpleGraph.Colorable.chromaticNumber_le
        (colorable_succ_of_adj_iff_off_vertex hKK' (hcolor K)))
  have h₁ := hstep G G' h
  have h₂ := hstep G' G fun a b ha hb => (h a b ha hb).symm
  rw [abs_sub_le_iff]
  constructor
  · have : (G.chromaticNumber.toNat : ℝ) ≤ (G'.chromaticNumber.toNat : ℝ) + 1 := by
      exact_mod_cast h₂
    linarith
  · have : (G'.chromaticNumber.toNat : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) + 1 := by
      exact_mod_cast h₁
    linarith

/-- Block `0` of the vertex-exposure product carries no information: its index type
`{j : Fin n // j < 0}` is empty, so the block is a singleton type. -/
private theorem eq_of_exposureBlock_bot {n : ℕ} {i : Fin n} (hi : (i : ℕ) = 0)
    (a b : ExposureBlock n i) : a = b := by
  have he : IsEmpty {j : Fin n // j < i} := by
    refine ⟨fun j => ?_⟩
    have hj := j.2
    rw [Fin.lt_def, hi] at hj
    omega
  exact funext fun j => he.elim j

/-- **Bounded differences for the chromatic number along vertex exposure.**  Changing block `i`
alone rewires only the edges at vertex `i`, so `abs_sub_chromaticNumber_le_one` applies and the
chromatic number moves by at most one; block `0` is a singleton type, so changing it alone
changes nothing at all.

The weight `0` at coordinate `0` is what makes `∑ i, c i ^ 2` equal `n - 1` rather than `n`. -/
private theorem abs_sub_chromaticNumber_graphOfExposure_le {n : ℕ} (i : Fin n)
    (x y : ∀ j, ExposureBlock n j) (h : ∀ j, j ≠ i → x j = y j) :
    |((graphOfExposure x).chromaticNumber.toNat : ℝ)
        - ((graphOfExposure y).chromaticNumber.toNat : ℝ)|
      ≤ if (i : ℕ) = 0 then (0 : ℝ) else 1 := by
  by_cases hi : (i : ℕ) = 0
  · have hxy : x = y := by
      funext j
      rcases eq_or_ne j i with rfl | hj
      · exact eq_of_exposureBlock_bot hi _ _
      · exact h j hj
    rw [hxy, if_pos hi]
    simp
  · rw [if_neg hi]
    refine abs_sub_chromaticNumber_le_one i _ _ fun a b ha hb => ?_
    rcases lt_trichotomy a b with hab | rfl | hab
    · rw [adj_graphOfExposure_iff_of_lt x hab, adj_graphOfExposure_iff_of_lt y hab, h b hb]
    · simp
    · rw [SimpleGraph.adj_comm (graphOfExposure x), SimpleGraph.adj_comm (graphOfExposure y),
        adj_graphOfExposure_iff_of_lt x hab, adj_graphOfExposure_iff_of_lt y hab, h a ha]

/-- The vertex-exposure weights sum to `n - 1`: every block but the empty block `0` contributes
`1`.  This is the `∑ i, c i ^ 2` of the bounded differences inequality, and the reason
Shamir–Spencer has radius `lam √(n-1)`. -/
private theorem sum_sq_exposureWeight (n : ℕ) (hn : 1 ≤ n) :
    ∑ i : Fin n, (if (i : ℕ) = 0 then (0 : ℝ) else 1) ^ 2 = (n : ℝ) - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Fin.sum_univ_succ]
  simp

/-- **The chromatic number of a random graph is concentrated in a window of width `O(√n)`**
(Zhao, Theorem 9.3.1; Shamir and Spencer 1987).  For every `lam ≥ 0`,

    ℙ(|χ(G(n, p)) - 𝔼χ(G(n, p))| ≥ lam √(n-1)) ≤ 2 exp (-2 lam²).

The striking part, as the source puts it, is that this proves concentration *around the mean
without knowing where the mean is*.

**Vertex exposure is what makes the bound this strong.**  Through
`binomialRandom_eq_map_graphOfExposure` the chromatic number becomes a function of `n`
independent blocks, of which `n - 1` are nonempty, and `abs_sub_chromaticNumber_le_one` gives
each of those a bounded difference of `1`.  So `∑ cᵢ² = n - 1`, and
`measure_sub_integral_ge_le` at `lam √(n-1)` returns `exp (-2 lam²)` with the `n - 1` cancelling.
Exposing one edge at a time would give `C(n,2)` coordinates and only `exp (-2 lam² / C(n,2))`.

**`2 ≤ n` is load-bearing.**  At `n = 1` the radius `lam √(n-1)` is `0`, so the event is
everything and the left side is `1`, while the right side drops below `1` as soon as
`lam ≥ 1` — at `lam = 2` it is about `0.0007`.  The source states no hypothesis on `n`, its
interest being asymptotic; the finite form needs one. -/
theorem measure_abs_sub_integral_chromaticNumber_ge_le (n : ℕ) (hn : 2 ≤ n) (p : I)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    (SimpleGraph.binomialRandom (Fin n) p).real
        {G : SimpleGraph (Fin n) | lam * Real.sqrt ((n : ℝ) - 1)
          ≤ |(G.chromaticNumber.toNat : ℝ)
              - ∫ K, (K.chromaticNumber.toNat : ℝ)
                  ∂(SimpleGraph.binomialRandom (Fin n) p)|}
      ≤ 2 * Real.exp (-2 * lam ^ 2) := by
  classical
  have hb : IsProbabilityMeasure ((toNNReal p) • Measure.dirac True
      + (toNNReal (σ p)) • Measure.dirac False) := ⟨by simp⟩
  have hpr : ∀ i : Fin n, IsProbabilityMeasure (exposureMeasure n p i) := fun i =>
    inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : {j : Fin n // j < i} =>
      (toNNReal p) • Measure.dirac True + (toNNReal (σ p)) • Measure.dirac False))
  -- `SimpleGraph (Fin n)` is countable with measurable singletons, hence discrete: the event
  -- and the chromatic number are measurable there.
  have hcount : Countable (SimpleGraph (Fin n)) := SimpleGraph.adj_injective.countable
  have hsingle : MeasurableSingletonClass (SimpleGraph (Fin n)) :=
    ⟨measurableSet_simpleGraph_singleton⟩
  have hchi : Measurable fun G : SimpleGraph (Fin n) => (G.chromaticNumber.toNat : ℝ) :=
    Measurable.of_discrete
  have hf : Measurable fun x : ∀ i : Fin n, ExposureBlock n i =>
      ((graphOfExposure x).chromaticNumber.toNat : ℝ) :=
    hchi.comp measurable_graphOfExposure_blocks
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hcsum : ∑ i : Fin n, (if (i : ℕ) = 0 then (0 : ℝ) else 1) ^ 2 = (n : ℝ) - 1 :=
    sum_sq_exposureWeight n (by omega)
  have hsum : 0 < ∑ i : Fin n, (if (i : ℕ) = 0 then (0 : ℝ) else 1) ^ 2 := hcsum ▸ hn1
  have hlam' : 0 ≤ lam * Real.sqrt ((n : ℝ) - 1) := mul_nonneg hlam (Real.sqrt_nonneg _)
  -- Move the event and the mean to the vertex-exposure product.
  have hstep : (SimpleGraph.binomialRandom (Fin n) p).real
      {G : SimpleGraph (Fin n) | lam * Real.sqrt ((n : ℝ) - 1)
        ≤ |(G.chromaticNumber.toNat : ℝ)
            - ∫ K, (K.chromaticNumber.toNat : ℝ)
                ∂(SimpleGraph.binomialRandom (Fin n) p)|}
      = (Measure.pi (exposureMeasure n p)).real
          {x | lam * Real.sqrt ((n : ℝ) - 1)
            ≤ |((graphOfExposure x).chromaticNumber.toNat : ℝ)
                - ∫ y, ((graphOfExposure y).chromaticNumber.toNat : ℝ)
                    ∂(Measure.pi (exposureMeasure n p))|} := by
    rw [binomialRandom_eq_map_graphOfExposure n p,
      integral_map measurable_graphOfExposure_blocks.aemeasurable hchi.aestronglyMeasurable,
      map_measureReal_apply measurable_graphOfExposure_blocks MeasurableSet.of_discrete,
      Set.preimage_ofPred_eq]
  rw [hstep]
  -- The bounded differences inequality, two-sided, at radius `lam √(n-1)`.
  have hmain := measure_abs_sub_integral_ge_le (exposureMeasure n p)
    (fun x => ((graphOfExposure x).chromaticNumber.toNat : ℝ))
    (fun i : Fin n => if (i : ℕ) = 0 then (0 : ℝ) else 1) hf
    (fun i x y h => abs_sub_chromaticNumber_graphOfExposure_le i x y h) hsum hlam'
  -- `∑ i, c i ^ 2 = n - 1` cancels the radius: the bound is `exp (-2 lam ^ 2)`.
  have hexp : -2 * (lam * Real.sqrt ((n : ℝ) - 1)) ^ 2
      / ∑ i : Fin n, (if (i : ℕ) = 0 then (0 : ℝ) else 1) ^ 2 = -2 * lam ^ 2 := by
    rw [hcsum, mul_pow, Real.sq_sqrt hn1.le]
    field_simp
  rw [hexp] at hmain
  exact hmain

end VertexExposure

/-! ### Edge exposure

The companion to `graphOfExposure`.  Which exposure a bounded-differences argument uses is
decided by what the random variable is Lipschitz in: `χ(G)` moves by at most one when a *vertex*
is rewired, so Shamir–Spencer uses vertex exposure and `n - 1` coordinates; the maximum number of
edge-disjoint `k`-cliques moves by at most one when a single *edge* changes, so §9.3's Lemma
9.3.3 needs edge exposure and `binom(n,2)` coordinates.  Its bound `exp (-2 (𝔼Y)² / binom(n,2))`
is exactly that coordinate count.
-/

section EdgeExposure

open unitInterval SimpleGraph

/-- A potential edge of `G(n, p)`: an unordered pair of distinct vertices. -/
abbrev EdgeSlot (n : ℕ) : Type := {e : Sym2 (Fin n) // ¬ e.IsDiag}

/-- The graph assembled from an assignment of booleans to the potential edges. -/
def graphOfEdgeSlots {n : ℕ} (x : EdgeSlot n → Prop) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e : Sym2 (Fin n) | ∃ h : ¬ e.IsDiag, x ⟨e, h⟩}

/-- Each potential edge present independently with probability `p`. -/
noncomputable def edgeSlotMeasure (n : ℕ) (p : I) : Measure (EdgeSlot n → Prop) :=
  Measure.pi fun _ => (toNNReal p) • Measure.dirac True + (toNNReal (σ p)) • Measure.dirac False

/-- `graphOfEdgeSlots` is measurable: for distinct `a` and `b`, adjacency in the assembled graph
is the single coordinate `s(a, b)`, and for `a = b` it is `False`. -/
private theorem measurable_graphOfEdgeSlots {n : ℕ} :
    Measurable (graphOfEdgeSlots : (EdgeSlot n → Prop) → SimpleGraph (Fin n)) := by
  rw [SimpleGraph.measurable_iff_adj]
  intro a b
  by_cases hab : a = b
  · subst hab
    simp [graphOfEdgeSlots]
  · have key : (fun x : EdgeSlot n → Prop => (graphOfEdgeSlots x).Adj a b)
        = fun x => x ⟨s(a, b), by simpa using hab⟩ := by
      funext x
      simp only [graphOfEdgeSlots, SimpleGraph.fromEdgeSet_adj, Set.mem_ofPred_eq]
      exact propext ⟨fun h => h.1.2, fun h => ⟨⟨by simpa using hab, h⟩, hab⟩⟩
    rw [key]
    exact measurable_pi_apply _

/-- `graphOfEdgeSlots` is injective with an explicit inverse: the only sample assembling to `G`
marks exactly the slots that are edges of `G`.  The slots are already off the diagonal, so
`edgeSet_fromEdgeSet` loses nothing in either direction. -/
private theorem graphOfEdgeSlots_eq_iff_eq_edgeSlots {n : ℕ} (x : EdgeSlot n → Prop)
    (G : SimpleGraph (Fin n)) :
    graphOfEdgeSlots x = G ↔ x = fun e : EdgeSlot n => (e : Sym2 (Fin n)) ∈ G.edgeSet := by
  constructor
  · rintro rfl
    funext e
    simp only [graphOfEdgeSlots, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff,
      Set.mem_ofPred_eq, Sym2.mem_diagSet]
    exact propext ⟨fun h => ⟨⟨e.2, h⟩, e.2⟩, fun h => h.1.2⟩
  · rintro rfl
    have hset : {e : Sym2 (Fin n) | ∃ _ : ¬ e.IsDiag, e ∈ G.edgeSet} = G.edgeSet := by
      ext e
      simp only [Set.mem_ofPred_eq]
      exact ⟨fun h => h.2, fun h => ⟨G.not_isDiag_of_mem_edgeSet h, h⟩⟩
    simp only [graphOfEdgeSlots]
    rw [hset, SimpleGraph.fromEdgeSet_edgeSet]

/-- **`G(n, p)` is the edge-exposure product.**

There are `binom(n,2)` slots, one per unordered pair of distinct vertices, and a graph's mass is
`p^{#E} (1-p)^{binom(n,2) - #E}` either way — which is `SimpleGraph.binomialRandom_singleton`.

Unlike `binomialRandom_eq_map_graphOfExposure` there is no blocking structure here, so the
coordinate set is flat and `graphOfEdgeSlots` is a bijection onto `SimpleGraph (Fin n)` with no
ordering to respect. -/
theorem binomialRandom_eq_map_graphOfEdgeSlots (n : ℕ) (p : I) :
    SimpleGraph.binomialRandom (Fin n) p
      = Measure.map graphOfEdgeSlots (edgeSlotMeasure n p) := by
  classical
  refine Measure.ext_of_singleton fun G => ?_
  rw [Measure.map_apply measurable_graphOfEdgeSlots (measurableSet_simpleGraph_singleton G)]
  have hpre : graphOfEdgeSlots ⁻¹' ({G} : Set (SimpleGraph (Fin n)))
      = {fun e : EdgeSlot n => (e : Sym2 (Fin n)) ∈ G.edgeSet} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact graphOfEdgeSlots_eq_iff_eq_edgeSlots x G
  rw [hpre, SimpleGraph.binomialRandom_singleton, edgeSlotMeasure, Measure.pi_singleton,
    Finset.prod_congr rfl fun (e : EdgeSlot n) _ =>
      bernoulliProp_singleton p ((e : Sym2 (Fin n)) ∈ G.edgeSet),
    Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  -- The slots marked present biject with the edges, via `Subtype.val`.
  have hcount : (Finset.univ.filter
      fun e : EdgeSlot n => (e : Sym2 (Fin n)) ∈ G.edgeSet).card = G.edgeSet.ncard := by
    rw [Set.ncard_eq_toFinset_card' G.edgeSet]
    refine Finset.card_bij (fun e _ => (e : Sym2 (Fin n))) ?_ ?_ ?_
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      simpa [Set.mem_toFinset] using he
    · intro e₁ _ e₂ _ h
      exact Subtype.ext h
    · intro e he
      rw [Set.mem_toFinset] at he
      exact ⟨⟨e, G.not_isDiag_of_mem_edgeSet he⟩, by simp [he], rfl⟩
  -- There are `C(n, 2)` slots in all, so the absent ones number `C(n, 2) - #E`.
  have hsplit : (Finset.univ.filter
        fun e : EdgeSlot n => (e : Sym2 (Fin n)) ∈ G.edgeSet).card
      + (Finset.univ.filter
        fun e : EdgeSlot n => ¬ (e : Sym2 (Fin n)) ∈ G.edgeSet).card = n.choose 2 := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ,
      Sym2.card_subtype_not_diag, Fintype.card_fin]
  have hn : (Nat.card (Fin n)).choose 2 = n.choose 2 := by simp
  rw [hcount, hn]
  congr 1
  congr 1
  omega

end EdgeExposure

end ProbMethodCombinatorics
