import Mathlib.Probability.Moments.SubGaussian
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

theorem integrable_of_abs_sub_le {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (g : α → ℝ) (hg : Measurable g) {C : ℝ}
    (hb : ∀ z z', |g z - g z'| ≤ C) : Integrable g ν := by
  have hne : Nonempty α := nonempty_of_isProbabilityMeasure ν
  obtain ⟨z₀⟩ := id hne
  refine Integrable.of_mem_Icc (g z₀ - C) (g z₀ + C) hg.aemeasurable (ae_of_all _ fun z ↦ ?_)
  have := abs_le.mp (hb z₀ z)
  constructor <;> [linarith [this.2]; linarith [this.1]]

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

theorem integral_exp_mul_integral_merge_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : (∀ i, Ω i) → ℝ) (c : ι → ℝ) (hf : Measurable f)
    (hc : ∀ i (x y : ∀ i, Ω i), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    (t : ℝ) (s : Finset ι) :
    ∫ x, Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ)) - ∫ y, f y ∂(Measure.pi μ))) ∂(Measure.pi μ)
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
  have hK : ∀ (s : Finset ι) (x : ∀ j, Ω j), |(∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ)) - ∫ y, f y ∂(Measure.pi μ)| ≤ ∑ i, c i := by
    intro s x
    rw [← integral_sub (hintM s x) hintf]
    have hb : ∀ y : ∀ j, Ω j,
        ‖f (fun j ↦ if j ∈ s then x j else y j) - f y‖ ≤ ∑ i, c i := fun y ↦ by
      rw [Real.norm_eq_abs]
      exact abs_sub_le_sum_of_bddDiff f c hc _ _
    simpa [Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const (μ := Measure.pi μ) (ae_of_all _ hb)
  have hbnd : ∀ (s : Finset ι) (x : ∀ j, Ω j),
      t * ((∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ)) - ∫ y, f y ∂(Measure.pi μ)) ≤ |t| * ∑ i, c i := by
    intro s x
    calc t * ((∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ)) - ∫ y, f y ∂(Measure.pi μ))
        ≤ |t * ((∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ)) - ∫ y, f y ∂(Measure.pi μ))| := le_abs_self _
      _ = |t| * |(∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ)) - ∫ y, f y ∂(Measure.pi μ)| := abs_mul _ _
      _ ≤ |t| * ∑ i, c i := mul_le_mul_of_nonneg_left (hK s x) (abs_nonneg t)
  have hexpInt : ∀ s : Finset ι,
      Integrable (fun x : ∀ j, Ω j ↦ Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ)) - ∫ y, f y ∂(Measure.pi μ)))) (Measure.pi μ) := by
    intro s
    exact Integrable.of_mem_Icc 0 (Real.exp (|t| * ∑ i, c i))
      ((((measurable_integral_merge μ f hf s).sub_const _).const_mul t).exp).aemeasurable
      (ae_of_all _ fun x ↦ ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr (hbnd s x)⟩)
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hA : ∀ x : ∀ j, Ω j, (∫ ω, (∫ y, f (fun j ↦ if j ∈ insert i s then Function.update x i ω j else y j) ∂(Measure.pi μ)) ∂(μ i)) = ∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ) := by
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
        (∫ ω, Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ insert i s then Function.update x i ω j else y j) ∂(Measure.pi μ)) - ∫ y, f y ∂(Measure.pi μ))) ∂(μ i))
          ≤ Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ)) - ∫ y, f y ∂(Measure.pi μ))) * Real.exp (t ^ 2 * c i ^ 2 / 8) := by
      intro x
      have hgm : Measurable fun ω ↦ ∫ y, f (fun j ↦ if j ∈ insert i s then Function.update x i ω j else y j) ∂(Measure.pi μ) :=
        (measurable_integral_merge μ f hf (insert i s)).comp (measurable_update x)
      have hgb : ∀ ω ω' : Ω i, |(∫ y, f (fun j ↦ if j ∈ insert i s then Function.update x i ω j else y j) ∂(Measure.pi μ)) - (∫ y, f (fun j ↦ if j ∈ insert i s then Function.update x i ω' j else y j) ∂(Measure.pi μ))| ≤ c i := by
        intro ω ω'
        refine abs_sub_integral_merge_le μ f c hf hc (insert i s) i _ _ fun j hj ↦ ?_
        rw [Function.update_of_ne hj, Function.update_of_ne hj]
      have hH := integral_exp_mul_sub_integral_le_of_abs_sub_le (μ i)
        (fun ω ↦ ∫ y, f (fun j ↦ if j ∈ insert i s then Function.update x i ω j else y j) ∂(Measure.pi μ)) hgm hgb t
      rw [hA x] at hH
      calc (∫ ω, Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ insert i s then Function.update x i ω j else y j) ∂(Measure.pi μ)) - ∫ y, f y ∂(Measure.pi μ))) ∂(μ i))
          = ∫ ω, Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ)) - ∫ y, f y ∂(Measure.pi μ)))
              * Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ insert i s then Function.update x i ω j else y j) ∂(Measure.pi μ)) - (∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ)))) ∂(μ i) := by
            refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
            show Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ insert i s then Function.update x i ω j else y j) ∂(Measure.pi μ)) - ∫ y, f y ∂(Measure.pi μ)))
              = Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ)) - ∫ y, f y ∂(Measure.pi μ))) * Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ insert i s then Function.update x i ω j else y j) ∂(Measure.pi μ)) - (∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ))))
            rw [← Real.exp_add, Real.exp_eq_exp]
            ring
        _ = Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ)) - ∫ y, f y ∂(Measure.pi μ)))
              * ∫ ω, Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ insert i s then Function.update x i ω j else y j) ∂(Measure.pi μ)) - (∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ)))) ∂(μ i) := integral_const_mul _ _
        _ ≤ Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ)) - ∫ y, f y ∂(Measure.pi μ))) * Real.exp (t ^ 2 * c i ^ 2 / 8) :=
            mul_le_mul_of_nonneg_left hH (Real.exp_pos _).le
    rw [integral_integral_update_pi μ i
      (fun x ↦ Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ insert i s then x j else y j) ∂(Measure.pi μ))
        - ∫ y, f y ∂(Measure.pi μ)))) (hexpInt (insert i s))]
    calc (∫ x, (∫ ω, Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ insert i s then Function.update x i ω j else y j) ∂(Measure.pi μ)) - ∫ y, f y ∂(Measure.pi μ))) ∂(μ i)) ∂(Measure.pi μ))
        ≤ ∫ x, Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ)) - ∫ y, f y ∂(Measure.pi μ))) * Real.exp (t ^ 2 * c i ^ 2 / 8) ∂(Measure.pi μ) :=
          integral_mono_of_nonneg
            (ae_of_all _ fun x ↦ integral_nonneg fun ω ↦ (Real.exp_pos _).le)
            ((hexpInt s).mul_const _) (ae_of_all _ hstep)
      _ = (∫ x, Real.exp (t * ((∫ y, f (fun j ↦ if j ∈ s then x j else y j) ∂(Measure.pi μ)) - ∫ y, f y ∂(Measure.pi μ))) ∂(Measure.pi μ)) * Real.exp (t ^ 2 * c i ^ 2 / 8) :=
          integral_mul_const _ _
      _ ≤ Real.exp (t ^ 2 * (∑ j ∈ s, c j ^ 2) / 8) * Real.exp (t ^ 2 * c i ^ 2 / 8) :=
          mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
      _ = Real.exp (t ^ 2 * (∑ j ∈ insert i s, c j ^ 2) / 8) := by
          rw [← Real.exp_add, Finset.sum_insert hi]
          ring_nf

/-- **Azuma–Hoeffding for the Doob martingale of a bounded-differences function**: under the
hypotheses of the bounded differences inequality, the centred function `f - 𝔼 f` has a
sub-Gaussian moment-generating function with parameter `(∑ i, c i ^ 2) / 4`.

This is Zhao's Theorem 9.2.9 (the Doob-martingale refinement of Azuma's inequality) combined with
Hoeffding's lemma (Lemma 9.2.12): writing `f - 𝔼 f` as the sum of the increments of the Doob
martingale `Zᵢ = 𝔼[f | x₁, …, xᵢ]`, each increment lies, conditionally on the preceding
coordinates, in an interval of length `c i`, hence is conditionally sub-Gaussian with parameter
`(c i) ^ 2 / 4`, and the parameters add along the martingale. -/
theorem hasSubgaussianMGF_sub_integral_of_bddDiff {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, Ω i) → ℝ) (c : ι → ℝ) (hf : Measurable f)
    (hc : ∀ i (x y : ∀ i, Ω i), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i) :
    HasSubgaussianMGF (fun x ↦ f x - ∫ y, f y ∂(Measure.pi μ))
      (((∑ i, c i ^ 2) / 4).toNNReal) (Measure.pi μ) := by
  sorry

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

end ProbMethodCombinatorics
