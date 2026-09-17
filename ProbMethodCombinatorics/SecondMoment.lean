import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Chapter 4: Second Moment

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Chapter 4.

The chapter's headline results are asymptotic statements about `G(n, p)` — thresholds, the
clique number, Hardy–Ramanujan.  Stated here is the chapter's *engine*: the two finite
inequalities every one of those arguments runs on.  Chebyshev's inequality itself is
Mathlib's `ProbabilityTheory.meas_ge_le_variance_div_sq`, and the Weierstrass approximation
theorem of §4.7 is Mathlib's `polynomialFunctions_closure_eq_top`; neither is restated.
-/

namespace ProbMethodCombinatorics

open Finset MeasureTheory ProbabilityTheory unitInterval SimpleGraph

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Chebyshev bound on the probability of non-existence** (Zhao, Corollary 4.1.7): for any
random variable `X`, `ℙ(X = 0) ≤ Var X / (𝔼 X) ^ 2`.

This is the form in which the second moment method is always applied: a random variable whose
variance is small compared to the square of its mean is positive with high probability. -/
theorem prob_eq_zero_le_variance_div_sq [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : MemLp X 2 μ) (hmean : μ[X] ≠ 0) :
    (μ {ω | X ω = 0}).toReal ≤ Var[X; μ] / μ[X] ^ 2 := by
  have hc : 0 < |μ[X]| := abs_pos.mpr hmean
  have hsub : {ω | X ω = 0} ⊆ {ω | |μ[X]| ≤ |X ω - μ[X]|} := fun ω hω => by
    show |μ[X]| ≤ |X ω - μ[X]|
    rw [show X ω = 0 from hω, zero_sub, abs_neg]
  have hle : μ {ω | X ω = 0} ≤ ENNReal.ofReal (Var[X; μ] / |μ[X]| ^ 2) :=
    (measure_mono hsub).trans (meas_ge_le_variance_div_sq hX hc)
  have hnn : 0 ≤ Var[X; μ] / |μ[X]| ^ 2 :=
    div_nonneg (variance_nonneg X μ) (sq_nonneg _)
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rwa [ENNReal.toReal_ofReal hnn, sq_abs] at this

/-- **The second moment variance bound for sums of indicators** (Zhao, Setup 4.2.2 and the
display preceding Lemma 4.2.4): if `X` counts how many of the events `A i` occur, and `D`
contains every ordered pair of distinct indices whose events are dependent, then

    Var X ≤ 𝔼 X + ∑ (i, j) ∈ D, ℙ(A i ∩ A j).

The dependency set `D` is a parameter rather than something computed from `A`, because
independence is not decidable; a caller supplies whichever `D` its application makes convenient. -/
theorem variance_sum_indicator_le [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (D : Finset (ι × ι))
    (hD : ∀ i j, i ≠ j → (i, j) ∉ D → IndepSet (A i) (A j) μ) :
    Var[fun ω => ∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω; μ]
      ≤ (∑ i, (μ (A i)).toReal) + ∑ q ∈ D, (μ (A q.1 ∩ A q.2)).toReal := by
  have hmem : ∀ i, MemLp ((A i).indicator (fun _ => (1 : ℝ))) 2 μ := fun i =>
    memLp_indicator_const 2 (hA i) 1 (Or.inr (measure_ne_top μ _))
  have hint : ∀ i, μ[(A i).indicator (fun _ => (1 : ℝ))] = (μ (A i)).toReal := fun i => by
    rw [integral_indicator_const _ (hA i), smul_eq_mul, mul_one, measureReal_def]
  have hcov : ∀ i j, cov[(A i).indicator (fun _ => (1 : ℝ)),
      (A j).indicator (fun _ => (1 : ℝ)); μ]
      = (μ (A i ∩ A j)).toReal - (μ (A i)).toReal * (μ (A j)).toReal := by
    intro i j
    have hmul : (A i).indicator (fun _ => (1 : ℝ)) * (A j).indicator (fun _ => (1 : ℝ))
        = (A i ∩ A j).indicator (fun _ => (1 : ℝ)) := by
      funext ω
      simpa using (Set.inter_indicator_mul (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) ω).symm
    rw [covariance_eq_sub (hmem i) (hmem j), hint i, hint j, hmul,
      integral_indicator_const _ ((hA i).inter (hA j)), smul_eq_mul, mul_one,
      measureReal_def]
  set g : ι × ι → ℝ := fun q => (μ (A q.1 ∩ A q.2)).toReal with hg
  have hg0 : ∀ q : ι × ι, 0 ≤ g q := fun _ => ENNReal.toReal_nonneg
  set Δ : Finset (ι × ι) :=
    Finset.univ.map ⟨fun i => (i, i), fun _ _ h => congrArg Prod.fst h⟩ with hΔ
  have hmemΔ : ∀ q : ι × ι, q.1 = q.2 → q ∈ Δ := by
    rintro ⟨a, b⟩ (h : a = b)
    subst h
    rw [hΔ]
    exact Finset.mem_map.2 ⟨a, Finset.mem_univ _, rfl⟩
  have hdiag : ∑ i, (μ (A i)).toReal = ∑ q ∈ Δ, g q := by
    rw [hΔ, Finset.sum_map]
    refine Finset.sum_congr rfl fun i _ => ?_
    show (μ (A i)).toReal = (μ (A i ∩ A i)).toReal
    rw [Set.inter_self]
  have hle : ∀ i j, cov[(A i).indicator (fun _ => (1 : ℝ)),
      (A j).indicator (fun _ => (1 : ℝ)); μ] ≤ g (i, j) := by
    intro i j
    rw [hcov i j, hg]
    exact sub_le_self _ (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  rw [variance_fun_sum hmem, hdiag,
    ← Finset.sum_indicator_subset g Δ.subset_univ,
    ← Finset.sum_indicator_subset g D.subset_univ,
    Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hqΔ : (i, j) ∈ (↑Δ : Set (ι × ι))
  · rw [Set.indicator_of_mem hqΔ]
    exact le_add_of_le_of_nonneg (hle i j) (Set.indicator_nonneg (fun a _ => hg0 a) _)
  by_cases hqD : (i, j) ∈ (↑D : Set (ι × ι))
  · rw [Set.indicator_of_mem hqD]
    exact le_add_of_nonneg_of_le (Set.indicator_nonneg (fun a _ => hg0 a) _) (hle i j)
  have hne : i ≠ j := fun h => hqΔ (Finset.mem_coe.2 (hmemΔ (i, j) h))
  have hnotD : (i, j) ∉ D := fun h => hqD (Finset.mem_coe.2 h)
  rw [Set.indicator_of_notMem hqΔ, Set.indicator_of_notMem hqD, add_zero, hcov i j,
    (hD i j hne hnotD).measure_inter_eq_mul, ENNReal.toReal_mul, sub_self]

/-- **Erdős's distinct-sums bound** (Zhao, Theorem 4.6.3; `sources/mit18_226_f22_lec_full.pdf`,
printed p. 61 = PDF p. 67).  If a `k`-element set of naturals bounded by `n` has all `2 ^ k`
subset sums distinct, then `n ≳ 2 ^ k / √k` — concretely, `3 · 2 ^ k ≤ 8 √k · n`.

This beats the pigeonhole bound `n ≥ 2 ^ k / k` by a factor of `√k`, and it is the chapter's
purest illustration of the second moment method: the pigeonhole argument counts *all* subset
sums, while this one discards the outliers that Chebyshev says are rare.

**Route.**  Let `X = ∑ εᵢ xᵢ` with `εᵢ ∈ {0,1}` independent and uniform.  Then `μ = (∑ xᵢ)/2`
and `σ² = (∑ xᵢ²)/4 ≤ n²k/4`.  Distinctness makes `X` injective on `{0,1}^k`, so
`ℙ(X = x) ≤ 2^{-k}` for every `x`, and a window of half-width `c` around `μ` therefore carries
probability at most `(2c + 1) · 2^{-k}`; Chebyshev bounds the same quantity from below.

**The `+1` is not absorbable, and the proof carries it.**
An *open* interval of length `2c` contains up to `⌊2c⌋ + 1` integers, not `2c`, so the naive
route above — comparing `2n√k · 2^{-k} ≥ 3/4` at `c = 2σ ≤ n√k` — is off by one and does not
close.  Parity does not rescue it: it helps when `∑ xᵢ` is odd and fails when it is even.  The
repair is to apply Chebyshev a shade inside `2σ`, at `c = (7/8)·n·√k`: then `σ²/c² ≤ 16/49`,
so the central mass is `≥ 33/49`, and `(33/49)·2^k ≤ 2c + 1 = (7/4)n√k + 1` beats the target
`3·2^k ≤ 8√k·n` exactly when `2^k ≥ 58`.  Hence the proof **splits at `k ≥ 6`**
(`by_cases hk6 : 6 ≤ k`, with `h64 : 64 ≤ 2^k` load-bearing), and covers `k ≤ 5` by
`interval_cases` against the pigeonhole bound `2^k ≤ nk + 1`, which is derived rather than
assumed and also supplies `1 ≤ n` for free.  The two branches overlap: pigeonhole alone in fact
suffices through `k ≤ 7`.

The engine is Mathlib's `meas_ge_le_variance_div_sq` (Chebyshev) with `IndepFun.variance_sum`;
the `εᵢ` are a genuine product-Bernoulli family (`Measure.pi`), so the variance of the sum is the
sum of the variances.  It uses neither `prob_eq_zero_le_variance_div_sq` nor
`variance_sum_indicator_le`.

Erdős's conjecture that `n ≳ 2 ^ k` (Conjecture 4.6.2) is **open mathematics** and must not be
stated as a theorem.  Theorem 4.6.6 (Dubroff–Fox–Xu), which improves the constant via Harper's
vertex-isoperimetric inequality, is a separate and harder node.

The bound was checked against the known minimal witnesses for `k ≤ 8` (the Conway–Guy
sequence `1, 2, 4, 7, 13, 24, 44, 84`) before publication. -/
theorem le_card_of_distinctSubsetSums {n k : ℕ} (hk : 0 < k) (S : Finset ℕ)
    (hSn : ∀ x ∈ S, x ≤ n) (hScard : S.card = k)
    (hdistinct : ∀ A ⊆ S, ∀ B ⊆ S, ∑ x ∈ A, x = ∑ x ∈ B, x → A = B) :
    3 * 2 ^ k ≤ 8 * Real.sqrt k * n := by
  classical
  have hcard : Fintype.card {a : ℕ // a ∈ S} = k := by rw [Fintype.card_coe, hScard]
  -- `V ω` is the sum of the subset of `S` selected by the `{0,1}`-vector `ω`; distinctness of
  -- subset sums says exactly that `V` is injective.
  set V : ({a : ℕ // a ∈ S} → Bool) → ℕ := fun ω => ∑ i, if ω i then (i : ℕ) else 0 with hVdef
  have hsub : ∀ τ : {a : ℕ // a ∈ S} → Bool,
      ((univ.filter fun i : {a : ℕ // a ∈ S} => τ i = true).image
        (Subtype.val : {a : ℕ // a ∈ S} → ℕ)) ⊆ S := by
    intro τ a ha
    simp only [Finset.mem_image] at ha
    obtain ⟨i, _, rfl⟩ := ha
    exact i.2
  have hsum : ∀ τ : {a : ℕ // a ∈ S} → Bool,
      ∑ a ∈ ((univ.filter fun i : {a : ℕ // a ∈ S} => τ i = true).image
        (Subtype.val : {a : ℕ // a ∈ S} → ℕ)), a = V τ := by
    intro τ
    rw [Finset.sum_image (fun a _ b _ hab => Subtype.ext hab), hVdef]
    simp [Finset.sum_filter]
  have hVinj : Function.Injective V := by
    intro ω ω' h
    have himg := hdistinct _ (hsub ω) _ (hsub ω') (by rw [hsum, hsum, h])
    have hfil := Finset.image_injective Subtype.val_injective himg
    funext i
    simpa using Finset.ext_iff.1 hfil i
  -- Injectivity already gives the pigeonhole bound: the `2 ^ k` subset sums are distinct
  -- naturals bounded by `n * k`.
  have hVle : ∀ ω, V ω ≤ n * k := by
    intro ω
    have : V ω ≤ ∑ _i : {a : ℕ // a ∈ S}, n := by
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases h : ω i
      · simpa [h] using hSn _ i.2
      · simp [h]
    simpa [Finset.sum_const, Finset.card_univ, hScard, mul_comm] using this
  have hpigeon : (2:ℕ) ^ k ≤ n * k + 1 := by
    have h1 : (univ : Finset ({a : ℕ // a ∈ S} → Bool)).card ≤ (Finset.range (n * k + 1)).card :=
      Finset.card_le_card_of_injOn V
        (fun ω _ => Finset.mem_range.2 (Nat.lt_succ_of_le (hVle ω))) hVinj.injOn
    simpa [Finset.card_univ, hScard] using h1
  have hn1 : 1 ≤ n := by
    have h2 : (2:ℕ) ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp only [Nat.zero_mul, Nat.zero_add] at hpigeon
      omega
    · exact h
  set r : ℝ := Real.sqrt k with hrdef
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = (k:ℝ) := Real.sq_sqrt (Nat.cast_nonneg k)
  have hn0 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  have hpigR : (2:ℝ) ^ k ≤ (n:ℝ) * k + 1 := by exact_mod_cast hpigeon
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hrpos : 0 < r := by rw [hrdef]; exact Real.sqrt_pos.mpr hkR
  by_cases hk6 : 6 ≤ k
  · -- For `k ≥ 6` the second moment method wins.  Chebyshev's inequality is applied at
    -- `c = (7/8) * n * √k`, a shade inside the `2σ` of the book's proof; the slack pays for the
    -- integer that the window `(m - c, m + c)` may contain beyond its length `2c`.
    have h64 : (64:ℝ) ≤ 2 ^ k := by
      calc (64:ℝ) = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk6
    -- `P` is the product of `k` fair Bernoulli factors on `{0,1}^S`, and `f i` is the
    -- contribution `εᵢ xᵢ` of the `i`-th element.  The factors being a genuine product measure
    -- is what makes the `f i` independent, hence the variance of their sum additive.
    set p : unitInterval := ⟨1/2, by norm_num⟩ with hp
    set B : {a : ℕ // a ∈ S} → Measure Bool := fun _ => Ber(true, false, p) with hB
    set P : Measure ({a : ℕ // a ∈ S} → Bool) := Measure.pi B with hP
    have : IsProbabilityMeasure P := by rw [hP]; infer_instance
    set x : {a : ℕ // a ∈ S} → ℝ := fun i => ((i : ℕ) : ℝ) with hxdef
    have hxnn : ∀ i, 0 ≤ x i := fun i => by simp [hxdef]
    have hxle : ∀ i, x i ≤ (n:ℝ) := fun i => by
      simpa [hxdef] using (Nat.cast_le (α := ℝ)).2 (hSn _ i.2)
    set f : {a : ℕ // a ∈ S} → (({a : ℕ // a ∈ S} → Bool) → ℝ) :=
      fun i ω => if ω i then x i else 0 with hf
    have hmeas : ∀ i, Measurable (f i) := fun i =>
      (Measurable.of_discrete (f := fun b : Bool => if b = true then x i else 0)).comp
        (measurable_pi_apply i)
    have hmem : ∀ i, MemLp (f i) 2 P := by
      intro i
      refine memLp_of_bounded (a := 0) (b := x i) ?_ (hmeas i).aestronglyMeasurable 2
      filter_upwards with ω
      simp only [hf]
      by_cases h : ω i <;> simp [h, hxnn i]
    have hindep : ProbabilityTheory.iIndepFun f P := by
      rw [hP, hf]
      exact iIndepFun_pi (X := fun i (b : Bool) => if b then x i else 0)
        (fun i => Measurable.of_discrete.aemeasurable)
    have hmean : ∀ i, P[f i] = x i / 2 := by
      intro i
      have key := integral_comp_eval (μ := B) (i := i)
        (f := fun b : Bool => if b = true then x i else 0)
        Measurable.of_discrete.aestronglyMeasurable
      rw [hB, integral_bernoulliMeasure] at key
      show ∫ ω, (fun b : Bool => if b = true then x i else 0) (ω i) ∂P = _
      rw [hP, key]
      simp [hp]
      ring
    have hsq : ∀ i, P[(f i)^2] = x i ^ 2 / 2 := by
      intro i
      have key := integral_comp_eval (μ := B) (i := i)
        (f := fun b : Bool => (if b = true then x i else 0)^2)
        Measurable.of_discrete.aestronglyMeasurable
      rw [hB, integral_bernoulliMeasure] at key
      show ∫ ω, (fun b : Bool => (if b = true then x i else 0)^2) (ω i) ∂P = _
      rw [hP, key]
      simp [hp]
      ring
    have hvar : ∀ i, Var[f i; P] = x i ^ 2 / 4 := by
      intro i
      rw [variance_eq_sub (hmem i), hsq i, hmean i]
      ring
    have hvarsum : Var[∑ i, f i; P] = ∑ i, x i ^ 2 / 4 := by
      rw [IndepFun.variance_sum (fun i _ => hmem i) (fun i _ j _ hij => hindep.indepFun hij)]
      exact Finset.sum_congr rfl fun i _ => hvar i
    have hmemsum : MemLp (∑ i, f i) 2 P := memLp_finsetSum' _ (fun i _ => hmem i)
    -- Each of the `2 ^ k` vectors carries mass exactly `2 ^ (-k)`.
    have hpN : unitInterval.toNNReal p = (2⁻¹ : NNReal) := by
      apply NNReal.coe_injective; simp [hp]
    have hpN2 : unitInterval.toNNReal (unitInterval.symm p) = (2⁻¹ : NNReal) := by
      apply NNReal.coe_injective; simp [hp, unitInterval.coe_symm_eq]; norm_num
    have h2E : ((2⁻¹ : NNReal) : ENNReal) = (2:ENNReal)⁻¹ := by
      rw [ENNReal.coe_inv (by norm_num)]; norm_num
    have hBsingle : ∀ (i : {a : ℕ // a ∈ S}) (b : Bool), B i {b} = (2:ENNReal)⁻¹ := by
      intro i b
      cases b
      · show Ber(true, false, p) ({false} : Set Bool) = _
        rw [bernoulliMeasure_apply_of_notMem_of_mem p (measurableSet_singleton _) (by simp) rfl,
          hpN2, h2E]
      · show Ber(true, false, p) ({true} : Set Bool) = _
        rw [bernoulliMeasure_apply_of_mem_of_notMem p (measurableSet_singleton _) rfl (by simp),
          hpN, h2E]
    have hsingle : ∀ ω : {a : ℕ // a ∈ S} → Bool, P {ω} = (2:ENNReal)⁻¹ ^ k := by
      intro ω
      rw [hP, ← Set.univ_pi_singleton ω, Measure.pi_pi]
      simp [hBsingle, hScard]
    -- `Var[X] = (∑ xᵢ²)/4 ≤ k n²/4`, so Chebyshev bounds the tail at `c` by `16/49`.
    set m : ℝ := P[∑ i, f i] with hmdef
    set c : ℝ := 7/8 * (n:ℝ) * r with hcdef
    have hc0 : 0 < c := by
      rw [hcdef]
      exact mul_pos (mul_pos (by norm_num) (by linarith)) hrpos
    have hc2 : c^2 = 49/64 * (n:ℝ)^2 * (k:ℝ) := by rw [hcdef, ← hr2]; ring
    have hvarle : Var[∑ i, f i; P] ≤ (k:ℝ) * (n:ℝ)^2 / 4 := by
      rw [hvarsum]
      have hterm : ∀ i ∈ (univ : Finset {a : ℕ // a ∈ S}), x i ^ 2 / 4 ≤ (n:ℝ)^2 / 4 := by
        intro i _
        have h1 := hxnn i
        have h2 := hxle i
        nlinarith
      calc ∑ i, x i ^ 2 / 4 ≤ ∑ _i : {a : ℕ // a ∈ S}, (n:ℝ)^2 / 4 := Finset.sum_le_sum hterm
        _ = (k:ℝ) * (n:ℝ)^2 / 4 := by
            rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
            ring
    have hratio : Var[∑ i, f i; P] / c^2 ≤ 16/49 := by
      rw [div_le_iff₀ (pow_pos hc0 2), hc2]
      nlinarith [hvarle]
    have hcheb := meas_ge_le_variance_div_sq hmemsum hc0
    have hGreal : P.real {ω | c ≤ |(∑ i, f i) ω - m|} ≤ 16/49 := by
      have hnn : 0 ≤ Var[∑ i, f i; P] / c^2 :=
        div_nonneg (variance_nonneg _ _) (sq_nonneg _)
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
      rw [ENNReal.toReal_ofReal hnn] at h
      exact h.trans hratio
    -- The window `|X - m| < c` is a finset of vectors, and `V` is injective on it, so its
    -- cardinality is at most the number of integers in an interval of length `2 * c`.
    have hXV : ∀ ω, (∑ i, f i) ω = (V ω : ℝ) := by
      intro ω
      rw [Finset.sum_apply, hVdef]
      push_cast
      exact Finset.sum_congr rfl fun i _ => by by_cases h : ω i <;> simp [hf, h, hxdef]
    set F : Finset ({a : ℕ // a ∈ S} → Bool) :=
      univ.filter (fun ω => |(V ω : ℝ) - m| < c) with hFdef
    have hFset : {ω | |(∑ i, f i) ω - m| < c} = (↑F : Set ({a : ℕ // a ∈ S} → Bool)) := by
      ext ω
      show |(∑ i, f i) ω - m| < c ↔ ω ∈ F
      rw [hXV ω, hFdef]
      simp
    have hlow : (33:ℝ)/49 ≤ P.real (↑F : Set ({a : ℕ // a ∈ S} → Bool)) := by
      have huniv : (Set.univ : Set ({a : ℕ // a ∈ S} → Bool))
          = {ω | c ≤ |(∑ i, f i) ω - m|} ∪ {ω | |(∑ i, f i) ω - m| < c} := by
        ext ω
        simpa using le_or_gt c |(∑ i, f i) ω - m|
      have h1 : P.real (Set.univ : Set ({a : ℕ // a ∈ S} → Bool)) = 1 := by simp
      rw [huniv] at h1
      have h2 := measureReal_union_le (μ := P) {ω | c ≤ |(∑ i, f i) ω - m|}
        {ω | |(∑ i, f i) ω - m| < c}
      rw [← hFset]
      linarith
    have hupp : P.real (↑F : Set ({a : ℕ // a ∈ S} → Bool)) ≤ (F.card : ℝ) * (1/2)^k := by
      have hcov : (↑F : Set ({a : ℕ // a ∈ S} → Bool)) = ⋃ ω ∈ F, ({ω} : Set _) := by
        rw [← Finset.set_biUnion_coe, Set.biUnion_of_singleton]
      have h1 : P (↑F : Set ({a : ℕ // a ∈ S} → Bool)) ≤ (F.card : ENNReal) * (2:ENNReal)⁻¹ ^ k := by
        rw [hcov]
        refine (measure_biUnion_finset_le F _).trans ?_
        rw [Finset.sum_congr rfl (fun ω _ => hsingle ω), Finset.sum_const, nsmul_eq_mul]
      have h2 := ENNReal.toReal_mono (by finiteness) h1
      refine h2.trans ?_
      simp [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
    have hcount : (F.card : ℝ) ≤ 2 * c + 1 := by
      rcases F.eq_empty_or_nonempty with hFe | ⟨ω0, hω0⟩
      · rw [hFe]
        simp
        linarith
      · have hTne : (F.image V).Nonempty := ⟨V ω0, Finset.mem_image_of_mem V hω0⟩
        have hTcard : (F.image V).card = F.card := Finset.card_image_of_injective _ hVinj
        have hbound : ∀ t ∈ F.image V, |(t:ℝ) - m| < c := by
          intro t ht
          rw [Finset.mem_image] at ht
          obtain ⟨ω, hωF, rfl⟩ := ht
          rw [hFdef, Finset.mem_filter] at hωF
          exact hωF.2
        have hlo := (F.image V).min'_mem hTne
        have hhi := (F.image V).max'_mem hTne
        have hsub2 : F.image V ⊆ Finset.Icc ((F.image V).min' hTne) ((F.image V).max' hTne) :=
          fun t ht => Finset.mem_Icc.2 ⟨(F.image V).min'_le t ht, (F.image V).le_max' t ht⟩
        have hle : (F.image V).min' hTne ≤ (F.image V).max' hTne :=
          (F.image V).min'_le _ hhi
        have hcardle : F.card ≤ (F.image V).max' hTne + 1 - (F.image V).min' hTne := by
          rw [← hTcard]
          simpa [Nat.card_Icc] using Finset.card_le_card hsub2
        have hcast : (F.card : ℝ)
            ≤ ((F.image V).max' hTne : ℝ) + 1 - ((F.image V).min' hTne : ℝ) := by
          have := (Nat.cast_le (α := ℝ)).2 hcardle
          rwa [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one] at this
        have h1 := abs_lt.1 (hbound _ hlo)
        have h2 := abs_lt.1 (hbound _ hhi)
        linarith
    -- `33/49 * 2 ^ k ≤ #F ≤ 2 * c + 1 = (7/4) * n * √k + 1`, which is the claim once `2 ^ k ≥ 64`.
    have hpow : ((1:ℝ)/2)^k * 2^k = 1 := by rw [← mul_pow]; norm_num
    have hfinal : 33/49 * 2^k ≤ (F.card : ℝ) := by
      have h := hlow.trans (hupp)
      nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) k, h, hpow]
    rw [hcdef] at hcount
    nlinarith [hfinal, hcount, h64, mul_pos (by linarith : (0:ℝ) < (n:ℝ)) hrpos]
  · -- For `k ≤ 5` the pigeonhole bound `2 ^ k ≤ n * k + 1` is already stronger than the claim.
    have hk6' : k < 6 := by omega
    interval_cases k <;>
      · push_cast at hr2 hpigR ⊢
        nlinarith [hr0, hr2, hpigR, hn0, sq_nonneg (r - 1), sq_nonneg (r - 2), sq_nonneg (r - 3),
          mul_nonneg hr0 (by linarith : (0:ℝ) ≤ (n:ℝ))]

/-! ### §4.1 The triangle count in `G(n, p)` -/

/-- **The number of triangles of `G`**, as a real number: one for each 3-element vertex set whose
three pairs are all edges.

Written with `Set.indicator` rather than a `Finset.filter` over a clique predicate because the
measure ranges over *all* graphs on `Fin n`, where no `DecidableRel G.Adj` is available — and
**this project declares no `Decidable` instances**.  The indicator is over a set of graphs, so
the same expression is both a random variable and, integrated, the expected triangle count.

Sanity: the empty graph has `triangleCount = 0`, since any 3-element `T` contains two distinct
vertices and `⊥` makes them non-adjacent. -/
noncomputable def triangleCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ :=
  ∑ T ∈ (univ : Finset (Fin n)).powersetCard 3,
    ({H : SimpleGraph (Fin n) | ∀ a ∈ T, ∀ b ∈ T, a ≠ b → H.Adj a b}).indicator
      (fun _ => (1 : ℝ)) G

/-- The event that a prescribed finite set of pairs are all edges is measurable. -/
private theorem measurableSet_forall_mem_edgeSet {n : ℕ} (E : Finset (Sym2 (Fin n))) :
    MeasurableSet {G : SimpleGraph (Fin n) | ∀ e ∈ E, e ∈ G.edgeSet} := by
  have hrw : {G : SimpleGraph (Fin n) | ∀ e ∈ E, e ∈ G.edgeSet}
      = ⋂ e ∈ E, {G : SimpleGraph (Fin n) | e ∈ G.edgeSet} := by
    ext G; simp
  rw [hrw]
  refine E.measurableSet_biInter fun e _ => ?_
  induction e using Sym2.ind with
  | _ u v =>
      have : {G : SimpleGraph (Fin n) | s(u, v) ∈ G.edgeSet}
          = {G : SimpleGraph (Fin n) | G.Adj u v} := by ext G; simp [mem_edgeSet]
      rw [this]
      measurability

/-- **A prescribed set of non-loop pairs is present with probability `p ^ |E|`.**  Under
`binomialRandom_apply'` the event is a cylinder in the product of Bernoulli measures on
`Sym2 (Fin n)`, so its probability is the product of the `|E|` factors it constrains. -/
private theorem binomialRandom_forall_mem_edgeSet {n : ℕ} (p : I) (E : Finset (Sym2 (Fin n)))
    (hE : ∀ e ∈ E, ¬ e.IsDiag) :
    binomialRandom (Fin n) p {G : SimpleGraph (Fin n) | ∀ e ∈ E, e ∈ G.edgeSet}
      = (toNNReal p : ENNReal) ^ E.card := by
  have himg : edgeSet '' {G : SimpleGraph (Fin n) | ∀ e ∈ E, e ∈ G.edgeSet}
      = {t ∈ ({t : Set (Sym2 (Fin n)) | ∀ e ∈ E, e ∈ t}) | t ⊆ Sym2.diagSetᶜ} := by
    ext t
    constructor
    · rintro ⟨G, hG, rfl⟩
      exact ⟨hG, G.edgeSet_subset_compl_diagSet⟩
    · rintro ⟨h1, h2⟩
      have hd : Disjoint t Sym2.diagSet := Set.subset_compl_iff_disjoint_right.mp h2
      refine ⟨fromEdgeSet t, ?_, ?_⟩
      · intro e he
        rw [edgeSet_fromEdgeSet, sdiff_eq_left.mpr hd]
        exact h1 e he
      · rw [edgeSet_fromEdgeSet, sdiff_eq_left.mpr hd]
  have hpre : (fun f : Sym2 (Fin n) → Prop ↦ {i | f i}) ⁻¹'
      {t : Set (Sym2 (Fin n)) | ∀ e ∈ E, e ∈ t}
      = Set.pi (↑E) (fun _ ↦ ({True} : Set Prop)) := by
    ext f
    simp [Set.mem_pi, eq_iff_iff]
  rw [binomialRandom_apply', himg, ← setBernoulli_apply_eq_apply_subsets, setBernoulli_apply',
    hpre, Measure.infinitePi_pi _ fun _ _ ↦ MeasurableSet.of_discrete,
    Finset.prod_congr rfl (g := fun _ ↦ (toNNReal p : ENNReal)) ?_, Finset.prod_const]
  intro e he
  have hmem : e ∈ Sym2.diagSetᶜ := by simpa [Sym2.mem_diagSet] using hE e he
  simp [Measure.dirac_apply', eq_true hmem]

/-- **The first moment of the triangle count** (Zhao, the computation behind Proposition 4.1.2):
`𝔼X = binom(n,3) p³`.

Linearity over the `binom(n,3)` indicator terms, each of which is the probability that three
prescribed pairs are all present — `p³`, since distinct pairs are independent under
`binomialRandom`.  `binomialRandom_apply` reduces such an event to an `infinitePi` of Bernoulli
factors, which is the route Chapter 7 already uses. -/
theorem integral_triangleCount (n : ℕ) (p : I) :
    ∫ G, triangleCount G ∂(binomialRandom (Fin n) p) = (n.choose 3 : ℝ) * (p : ℝ) ^ 3 := by
  have key : ∀ T ∈ (univ : Finset (Fin n)).powersetCard 3,
      MeasurableSet {H : SimpleGraph (Fin n) | ∀ a ∈ T, ∀ b ∈ T, a ≠ b → H.Adj a b} ∧
      binomialRandom (Fin n) p {H : SimpleGraph (Fin n) | ∀ a ∈ T, ∀ b ∈ T, a ≠ b → H.Adj a b}
        = (toNNReal p : ENNReal) ^ 3 := by
    intro T hT
    have hcard : T.card = 3 := Finset.mem_powersetCard_univ.mp hT
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
    set E : Finset (Sym2 (Fin n)) := {s(a, b), s(a, c), s(b, c)} with hEdef
    have hEd : ∀ e ∈ E, ¬ e.IsDiag := by
      intro e he
      simp only [hEdef, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl <;> simp [Sym2.mk_isDiag_iff, hab, hac, hbc]
    have hEcard : E.card = 3 := by
      simp only [hEdef]
      rw [Finset.card_insert_of_notMem (by simp [hab, hac, hbc]),
        Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_singleton]
    have hset : {H : SimpleGraph (Fin n) |
          ∀ x ∈ ({a, b, c} : Finset (Fin n)), ∀ y ∈ ({a, b, c} : Finset (Fin n)),
            x ≠ y → H.Adj x y}
        = {G : SimpleGraph (Fin n) | ∀ e ∈ E, e ∈ G.edgeSet} := by
      ext G
      constructor
      · intro h e he
        simp only [hEdef, Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl <;> simp only [mem_edgeSet]
        · exact h a (by simp) b (by simp) hab
        · exact h a (by simp) c (by simp) hac
        · exact h b (by simp) c (by simp) hbc
      · intro h x hx y hy hxy
        have h1 : G.Adj a b := by simpa [mem_edgeSet] using h s(a, b) (by simp [hEdef])
        have h2 : G.Adj a c := by simpa [mem_edgeSet] using h s(a, c) (by simp [hEdef])
        have h3 : G.Adj b c := by simpa [mem_edgeSet] using h s(b, c) (by simp [hEdef])
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
          first
            | exact absurd rfl hxy
            | assumption
            | exact h1.symm
            | exact h2.symm
            | exact h3.symm
    rw [hset]
    exact ⟨measurableSet_forall_mem_edgeSet E,
      by rw [binomialRandom_forall_mem_edgeSet p E hEd, hEcard]⟩
  simp only [triangleCount]
  rw [MeasureTheory.integral_finsetSum _ fun T hT =>
    memLp_one_iff_integrable.mp
      (memLp_indicator_const 1 (key T hT).1 1 (Or.inr (measure_ne_top _ _)))]
  rw [Finset.sum_congr rfl fun T hT => ?_, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [MeasureTheory.integral_indicator_const _ (key T hT).1, Measure.real, (key T hT).2,
    smul_eq_mul, mul_one, ENNReal.toReal_pow, ENNReal.coe_toReal, unitInterval.coe_toNNReal]

/-- **The variance of the triangle count** (Zhao, the second-moment half of Proposition 4.1.2),
in the crude form the threshold argument needs.

Two triangles sharing at most one vertex use disjoint pairs and are independent, so they
contribute nothing to the variance.  What is left is the diagonal — each indicator has variance at
most its mean, giving at most `binom(n,3) p³ ≤ n³p³` — and the pairs sharing exactly one edge,
of which there are at most `n⁴/2`, each contributing at most the probability `p⁵` that their five
pairs are all present.

The constants are deliberately generous: `n³` and `n⁴` rather than the exact binomials, so the
bound can be proved without tracking them. -/
theorem variance_triangleCount_le (n : ℕ) (p : I) :
    variance triangleCount (binomialRandom (Fin n) p)
      ≤ (n : ℝ) ^ 3 * (p : ℝ) ^ 3 + (n : ℝ) ^ 4 * (p : ℝ) ^ 5 := by
  sorry

/-- **The subcritical half of the triangle threshold** (Zhao, Proposition 4.1.2): when `p·n` is
small, `G(n, p)` has no triangle with high probability.

**This is the project's `whp` idiom, and it is the reference for every later use.**  "Whp" is
written out with explicit quantifiers, never as a filter or an `o(1)`, matching the convention
Chapter 5 and Chapter 11 already follow: *for every `ε > 0` there is a threshold such that the
probability is at least `1 - ε`*.  The hypothesis "`p ≪ 1/n`" becomes a `δ` bounding `p · n`, so
no sequence of graphs and no limit appears anywhere.

**No `N` is needed on this half**, which is why it is stated before its supercritical twin.
Markov gives a bound uniform in `n`: `𝔼X = binom(n,3) p³ ≤ (p·n)³/6 ≤ δ³/6`, and since
`triangleCount` is integer-valued, `ℙ(X ≠ 0) = ℙ(X ≥ 1) ≤ 𝔼X`.  Taking `δ = min 1 (6ε)^{1/3}`
makes `δ³/6 ≤ ε`.  The supercritical half needs both a scale `M` and an `N`, because Chebyshev's
error `36/(n³p³) + 36/(n²p)` only vanishes once `n` is large as well — it waits on
`variance_triangleCount_le`. -/
theorem prob_no_triangle_of_mul_le :
    ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ (n : ℕ) (p : I), (p : ℝ) * n ≤ δ →
      1 - ε ≤ (binomialRandom (Fin n) p {G | triangleCount G = 0}).toReal := by
  sorry

end ProbMethodCombinatorics
