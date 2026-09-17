import Mathlib.Combinatorics.SimpleGraph.Finite
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

/-! ### Shared vocabulary for edge events in `G(n, p)`

`offDiagPairs` and the lemmas below are **public on purpose**.  The probability that a prescribed
loop-free set of pairs is entirely present is `p ^ |S|`, and every counting argument in
Chapters 4, 7 and 8 needs it.  `Correlation.lean` holds its own copies of the same facts, but they
are `private` and so unreachable from here — which is how three independent re-derivations of this
one computation came to exist.  Anything new should call these rather than rebuild them. -/

/-- The unordered pairs of **distinct** vertices drawn from `T`: the edge set a triangle on `T`
would have to contain. -/
def offDiagPairs {n : ℕ} (T : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  T.sym2.filter fun e => ¬ e.IsDiag

theorem mem_offDiagPairs {n : ℕ} {T : Finset (Fin n)} {a b : Fin n} :
    s(a, b) ∈ offDiagPairs T ↔ a ∈ T ∧ b ∈ T ∧ a ≠ b := by
  simp [offDiagPairs, and_assoc]

theorem not_isDiag_of_mem_offDiagPairs {n : ℕ} {T : Finset (Fin n)}
    {e : Sym2 (Fin n)} (he : e ∈ offDiagPairs T) : ¬ e.IsDiag :=
  (Finset.mem_filter.1 he).2

/-- Two vertex sets share exactly the pairs drawn from their intersection. -/
theorem offDiagPairs_inter {n : ℕ} (T₁ T₂ : Finset (Fin n)) :
    offDiagPairs T₁ ∩ offDiagPairs T₂ = offDiagPairs (T₁ ∩ T₂) := by
  ext e
  induction e using Sym2.ind with
  | _ a b => simp only [Finset.mem_inter, mem_offDiagPairs, Finset.mem_inter]; tauto

/-- `T` spans `binom(#T, 2)` pairs of distinct vertices, in the additive form that avoids
truncated subtraction: the diagonal accounts for the remaining `#T` members of `T.sym2`. -/
theorem card_offDiagPairs_add {n : ℕ} (T : Finset (Fin n)) :
    (offDiagPairs T).card + T.card = (T.card + 1).choose 2 := by
  have hdiag : T.sym2.filter (fun e => e.IsDiag) = T.image Sym2.diag := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff,
        Finset.mem_image, Sym2.diag, Sym2.eq_iff]
      constructor
      · rintro ⟨⟨ha, _⟩, rfl⟩
        exact ⟨a, ha, by tauto⟩
      · rintro ⟨c, hc, h⟩
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨⟨hc, hc⟩, rfl⟩
  have hinj : Function.Injective (Sym2.diag : Fin n → Sym2 (Fin n)) := by
    intro a b h
    simpa [Sym2.diag, Sym2.eq_iff] using h
  have hsplit : (T.sym2.filter (fun e => e.IsDiag)).card + (offDiagPairs T).card = T.sym2.card :=
    Finset.card_filter_add_card_filter_not _
  rw [hdiag, Finset.card_image_of_injective _ hinj, Finset.card_sym2] at hsplit
  omega

/-- Requiring two sets of pairs is requiring their union. -/
theorem setOf_subset_edgeSet_inter {n : ℕ} (S₁ S₂ : Finset (Sym2 (Fin n))) :
    {G : SimpleGraph (Fin n) | ↑S₁ ⊆ G.edgeSet} ∩ {G : SimpleGraph (Fin n) | ↑S₂ ⊆ G.edgeSet}
      = {G : SimpleGraph (Fin n) | ↑(S₁ ∪ S₂) ⊆ G.edgeSet} := by
  ext G
  simp [Set.union_subset_iff]

/-- "Every pair in `S` is an edge" is a finite intersection of coordinate events, hence
measurable. -/
theorem measurableSet_setOf_subset_edgeSet {n : ℕ} (S : Finset (Sym2 (Fin n))) :
    MeasurableSet {G : SimpleGraph (Fin n) | ↑S ⊆ G.edgeSet} := by
  have h : {G : SimpleGraph (Fin n) | ↑S ⊆ G.edgeSet}
      = ⋂ e ∈ S, {G : SimpleGraph (Fin n) | e ∈ G.edgeSet} := by
    ext G; simp [Set.subset_def]
  rw [h]
  exact S.measurableSet_biInter fun e _ => measurable_edgeSet (measurableSet_mem e)

/-- **`G(n, p)` contains a prescribed finite set of non-loop pairs with probability `p ^ #S`.**

`binomialRandom` is `setBernoulli` read through `fromEdgeSet`, so the event becomes the cylinder
`{R | ↑S ⊆ R}` of the underlying product of Bernoulli coordinates, and `Measure.infinitePi_pi`
evaluates it as a product of `#S` copies of `p`. -/
theorem binomialRandom_setOf_subset_edgeSet {n : ℕ} (p : I) (S : Finset (Sym2 (Fin n)))
    (hS : ∀ e ∈ S, ¬ e.IsDiag) :
    binomialRandom (Fin n) p {G : SimpleGraph (Fin n) | ↑S ⊆ G.edgeSet}
      = (toNNReal p : ENNReal) ^ S.card := by
  rw [binomialRandom_eq_map,
    Measure.map_apply measurable_fromEdgeSet (measurableSet_setOf_subset_edgeSet S),
    setBernoulli_apply']
  have hpre : (fun f : Sym2 (Fin n) → Prop => {e | f e}) ⁻¹'
      (fromEdgeSet ⁻¹' {G : SimpleGraph (Fin n) | ↑S ⊆ G.edgeSet})
      = (↑S : Set (Sym2 (Fin n))).pi (fun _ => ({True} : Set Prop)) := by
    ext f
    simp only [Set.mem_preimage, edgeSet_fromEdgeSet, Set.mem_pi, Set.mem_singleton_iff,
      Set.subset_def, Set.mem_ofPred_eq, Set.mem_sdiff, Finset.mem_coe]
    exact ⟨fun h e he => eq_true (h e he).1,
      fun h e he => ⟨of_eq_true (h e he), by simpa using hS e he⟩⟩
  rw [hpre, Measure.infinitePi_pi _ (fun e _ => MeasurableSet.of_discrete),
    Finset.prod_congr rfl (g := fun _ => (toNNReal p : ENNReal)) ?_, Finset.prod_const]
  intro e he
  have hne : e ∈ (Sym2.diagSetᶜ : Set (Sym2 (Fin n))) := by
    simpa using hS e he
  simp [Measure.dirac_apply', hne]

/-- The event that `T` spans a triangle, in terms of its pairs. -/
theorem setOf_forall_adj_eq_setOf_offDiagPairs {n : ℕ} (T : Finset (Fin n)) :
    {H : SimpleGraph (Fin n) | ∀ a ∈ T, ∀ b ∈ T, a ≠ b → H.Adj a b}
      = {G : SimpleGraph (Fin n) | ↑(offDiagPairs T) ⊆ G.edgeSet} := by
  ext H
  simp only [Set.mem_ofPred_eq, Set.subset_def, Finset.mem_coe]
  constructor
  · intro h e he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨ha, hb, hab⟩ := mem_offDiagPairs.1 he
      exact h a ha b hb hab
  · intro h a ha b hb hab
    exact h s(a, b) (mem_offDiagPairs.2 ⟨ha, hb, hab⟩)

/-- The measurability of the same event, in the `∀ e ∈ E` spelling that `triangleCount`'s
definition produces.  A thin wrapper over `measurableSet_setOf_subset_edgeSet` above; the two sets
differ only by `Set.subset_def`. -/
private theorem measurableSet_forall_mem_edgeSet {n : ℕ} (E : Finset (Sym2 (Fin n))) :
    MeasurableSet {G : SimpleGraph (Fin n) | ∀ e ∈ E, e ∈ G.edgeSet} := by
  simpa [Set.subset_def] using measurableSet_setOf_subset_edgeSet E

/-- The same probability in the `∀ e ∈ E` spelling.  A thin wrapper over
`binomialRandom_setOf_subset_edgeSet` above. -/
private theorem binomialRandom_forall_mem_edgeSet {n : ℕ} (p : I) (E : Finset (Sym2 (Fin n)))
    (hE : ∀ e ∈ E, ¬ e.IsDiag) :
    binomialRandom (Fin n) p {G : SimpleGraph (Fin n) | ∀ e ∈ E, e ∈ G.edgeSet}
      = (toNNReal p : ENNReal) ^ E.card := by
  simpa [Set.subset_def] using binomialRandom_setOf_subset_edgeSet p E hE

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
  -- The triangle count as a sum of indicators indexed by the 3-element vertex sets.
  set 𝒯 : Finset (Finset (Fin n)) := (univ : Finset (Fin n)).powersetCard 3 with h𝒯
  set A : {T // T ∈ 𝒯} → Set (SimpleGraph (Fin n)) :=
    fun T => {G : SimpleGraph (Fin n) | ↑(offDiagPairs T.1) ⊆ G.edgeSet}
  have hcard3' : ∀ T : {T // T ∈ 𝒯}, T.1.card = 3 := fun T => (Finset.mem_powersetCard.1 T.2).2
  have hcard3 : ∀ T : {T // T ∈ 𝒯}, (offDiagPairs T.1).card = 3 := by
    intro T
    have h := card_offDiagPairs_add T.1
    have h6 : (3 + 1).choose 2 = 6 := by decide
    rw [hcard3' T, h6] at h
    omega
  have hmeas : ∀ i, MeasurableSet (A i) := fun i => measurableSet_setOf_subset_edgeSet _
  have hprob : ∀ i, binomialRandom (Fin n) p (A i) = (toNNReal p : ENNReal) ^ 3 := by
    intro i
    show binomialRandom (Fin n) p {G : SimpleGraph (Fin n) | ↑(offDiagPairs i.1) ⊆ G.edgeSet} = _
    rw [binomialRandom_setOf_subset_edgeSet p _
      (fun _ he => not_isDiag_of_mem_offDiagPairs he), hcard3 i]
  have hX : (triangleCount : SimpleGraph (Fin n) → ℝ)
      = fun G => ∑ i, (A i).indicator (fun _ => (1 : ℝ)) G := by
    funext G
    rw [triangleCount, ← Finset.sum_coe_sort 𝒯]
    exact Finset.sum_congr rfl fun i _ => by rw [setOf_forall_adj_eq_setOf_offDiagPairs]
  -- The dependency set: ordered pairs of 3-sets sharing exactly two vertices.
  set D : Finset ({T // T ∈ 𝒯} × {T // T ∈ 𝒯}) :=
    univ.filter (fun q => (q.1.1 ∩ q.2.1).card = 2)
  have hinterle : ∀ i j : {T // T ∈ 𝒯}, i ≠ j → (i.1 ∩ j.1).card ≤ 2 := by
    intro i j hij
    have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    have h3 : (i.1 ∩ j.1).card ≠ 3 := by
      intro h
      exact hne ((Finset.eq_of_subset_of_card_le Finset.inter_subset_left
        (by rw [hcard3' i, h])).symm.trans
        (Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [hcard3' j, h])))
    have := Finset.card_le_card (Finset.inter_subset_left (s₁ := i.1) (s₂ := j.1))
    rw [hcard3' i] at this
    omega
  -- Two triangles span `3 + 3` pairs less the ones drawn from their shared vertices.
  have hunionpairs : ∀ i j : {T // T ∈ 𝒯},
      (offDiagPairs i.1 ∪ offDiagPairs j.1).card + (offDiagPairs (i.1 ∩ j.1)).card = 6 := by
    intro i j
    have h := Finset.card_union_add_card_inter (offDiagPairs i.1) (offDiagPairs j.1)
    rw [offDiagPairs_inter, hcard3 i, hcard3 j] at h
    omega
  -- Sharing at most one vertex means disjoint pair sets, hence independence.
  have hD : ∀ i j, i ≠ j → (i, j) ∉ D →
      IndepSet (A i) (A j) (binomialRandom (Fin n) p) := by
    intro i j hij hnotD
    have h2 : (i.1 ∩ j.1).card ≠ 2 := fun h =>
      hnotD (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    have hle1 : (i.1 ∩ j.1).card ≤ 1 := by have := hinterle i j hij; omega
    have hempty : (offDiagPairs (i.1 ∩ j.1)).card = 0 := by
      have hc0 : (0 + 1).choose 2 = 0 := by decide
      have hc1 : (1 + 1).choose 2 = 1 := by decide
      have h := card_offDiagPairs_add (i.1 ∩ j.1)
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle1 with hk | hk <;> rw [hk] at h <;>
        simp only [hc0, hc1] at h <;> omega
    have hcard6 : (offDiagPairs i.1 ∪ offDiagPairs j.1).card = 6 := by
      have := hunionpairs i j; omega
    rw [indepSet_iff_measure_inter_eq_mul (μ := binomialRandom (Fin n) p) (hmeas i) (hmeas j)]
    show binomialRandom (Fin n) p
        ({G : SimpleGraph (Fin n) | ↑(offDiagPairs i.1) ⊆ G.edgeSet} ∩
          {G : SimpleGraph (Fin n) | ↑(offDiagPairs j.1) ⊆ G.edgeSet}) = _
    rw [setOf_subset_edgeSet_inter,
      binomialRandom_setOf_subset_edgeSet p (offDiagPairs i.1 ∪ offDiagPairs j.1)
        (fun _ he => by
          rcases Finset.mem_union.1 he with h | h <;> exact not_isDiag_of_mem_offDiagPairs h),
      hcard6, hprob i, hprob j]
    ring
  -- Sharing exactly two vertices means five pairs between them.
  have hprob5 : ∀ q ∈ D,
      binomialRandom (Fin n) p (A q.1 ∩ A q.2) = (toNNReal p : ENNReal) ^ 5 := by
    intro q hq
    have h2 : (q.1.1 ∩ q.2.1).card = 2 := (Finset.mem_filter.1 hq).2
    have hone : (offDiagPairs (q.1.1 ∩ q.2.1)).card = 1 := by
      have h := card_offDiagPairs_add (q.1.1 ∩ q.2.1)
      have h3 : (2 + 1).choose 2 = 3 := by decide
      rw [h2, h3] at h
      omega
    have hcard5 : (offDiagPairs q.1.1 ∪ offDiagPairs q.2.1).card = 5 := by
      have := hunionpairs q.1 q.2; omega
    show binomialRandom (Fin n) p
        ({G : SimpleGraph (Fin n) | ↑(offDiagPairs q.1.1) ⊆ G.edgeSet} ∩
          {G : SimpleGraph (Fin n) | ↑(offDiagPairs q.2.1) ⊆ G.edgeSet}) = _
    rw [setOf_subset_edgeSet_inter,
      binomialRandom_setOf_subset_edgeSet p (offDiagPairs q.1.1 ∪ offDiagPairs q.2.1)
        (fun _ he => by
          rcases Finset.mem_union.1 he with h | h <;> exact not_isDiag_of_mem_offDiagPairs h),
      hcard5]
  have hs1 : ∑ i, (binomialRandom (Fin n) p (A i)).toReal = (𝒯.card : ℝ) * (p : ℝ) ^ 3 := by
    rw [Finset.sum_congr rfl (fun i _ => by rw [hprob i]), Finset.sum_const, Finset.card_univ,
      Fintype.card_coe, nsmul_eq_mul]
    simp
  have hs2 : ∑ q ∈ D, (binomialRandom (Fin n) p (A q.1 ∩ A q.2)).toReal
      = (D.card : ℝ) * (p : ℝ) ^ 5 := by
    rw [Finset.sum_congr rfl (fun q hq => by rw [hprob5 q hq]), Finset.sum_const, nsmul_eq_mul]
    simp
  have key := variance_sum_indicator_le (μ := binomialRandom (Fin n) p) A hmeas D hD
  rw [hX]
  refine key.trans ?_
  rw [hs1, hs2]
  have hT : (𝒯.card : ℝ) ≤ (n : ℝ) ^ 3 := by
    rw [h𝒯, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    calc ((n.choose 3 : ℕ) : ℝ) ≤ ((n ^ 3 : ℕ) : ℝ) := Nat.cast_le.2 (Nat.choose_le_pow n 3)
      _ = (n : ℝ) ^ 3 := by push_cast; ring
  -- `(a, b, x, y) ↦ ({x, a, b}, {y, a, b})` covers every member of `D`, so `#D ≤ n ^ 4`.
  have hDnat : D.card ≤ n ^ 4 := by
    have hinjimg : Function.Injective
        (fun q : {T // T ∈ 𝒯} × {T // T ∈ 𝒯} => (q.1.1, q.2.1)) := by
      intro q r h
      exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
    have hsurj : Set.SurjOn
        (fun v : Fin n × Fin n × Fin n × Fin n =>
          (({v.2.2.1, v.1, v.2.1} : Finset (Fin n)), ({v.2.2.2, v.1, v.2.1} : Finset (Fin n))))
        (↑(univ : Finset (Fin n × Fin n × Fin n × Fin n)))
        (↑(D.image (fun q : {T // T ∈ 𝒯} × {T // T ∈ 𝒯} => (q.1.1, q.2.1)))) := by
      intro z hz
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hz
      obtain ⟨q, hq, rfl⟩ := hz
      obtain ⟨a, b, hab, hinter⟩ := Finset.card_eq_two.1 (Finset.mem_filter.1 hq).2
      have hd1 : (q.1.1 \ q.2.1).card = 1 := by
        have := Finset.card_sdiff_add_card_inter q.1.1 q.2.1
        rw [hcard3' q.1, (Finset.mem_filter.1 hq).2] at this
        omega
      have hd2 : (q.2.1 \ q.1.1).card = 1 := by
        have := Finset.card_sdiff_add_card_inter q.2.1 q.1.1
        rw [hcard3' q.2, Finset.inter_comm, (Finset.mem_filter.1 hq).2] at this
        omega
      obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hd1
      obtain ⟨y, hy⟩ := Finset.card_eq_one.1 hd2
      refine ⟨(a, b, x, y), by simp, ?_⟩
      have e1 : q.1.1 = {x, a, b} := by
        rw [← Finset.sdiff_union_inter q.1.1 q.2.1, hx, hinter]
        rfl
      have e2 : q.2.1 = {y, a, b} := by
        rw [← Finset.sdiff_union_inter q.2.1 q.1.1, hy, Finset.inter_comm, hinter]
        rfl
      exact Prod.ext e1.symm e2.symm
    calc D.card = (D.image (fun q : {T // T ∈ 𝒯} × {T // T ∈ 𝒯} => (q.1.1, q.2.1))).card :=
          (Finset.card_image_of_injective _ hinjimg).symm
      _ ≤ (univ : Finset (Fin n × Fin n × Fin n × Fin n)).card :=
          Finset.card_le_card_of_surjOn _ hsurj
      _ = n ^ 4 := by simp [Finset.card_univ]; ring
  have hDc : (D.card : ℝ) ≤ (n : ℝ) ^ 4 := by
    calc ((D.card : ℕ) : ℝ) ≤ ((n ^ 4 : ℕ) : ℝ) := Nat.cast_le.2 hDnat
      _ = (n : ℝ) ^ 4 := by push_cast; ring
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := p.2.1
  have h3 : (0 : ℝ) ≤ (p : ℝ) ^ 3 := by positivity
  have h5 : (0 : ℝ) ≤ (p : ℝ) ^ 5 := by positivity
  exact add_le_add (by gcongr) (by gcongr)


/-- The event that every pair of distinct vertices of `T` is an edge: an intersection over the
finitely many pairs drawn from `T` of the events `Adj a b`, each of which is measurable because
the σ-algebra on `SimpleGraph V` is pulled back along `Adj`. -/
theorem measurableSet_setOf_forall_adj {n : ℕ} (T : Finset (Fin n)) :
    MeasurableSet {H : SimpleGraph (Fin n) | ∀ a ∈ T, ∀ b ∈ T, a ≠ b → H.Adj a b} := by
  have hrw : {H : SimpleGraph (Fin n) | ∀ a ∈ T, ∀ b ∈ T, a ≠ b → H.Adj a b}
      = ⋂ a ∈ T, ⋂ b ∈ T, {H : SimpleGraph (Fin n) | a ≠ b → H.Adj a b} := by
    ext H; simp
  rw [hrw]
  refine T.measurableSet_biInter fun a _ => T.measurableSet_biInter fun b _ => ?_
  by_cases hab : a = b
  · simp [hab]
  · have hset : {H : SimpleGraph (Fin n) | a ≠ b → H.Adj a b}
        = {H : SimpleGraph (Fin n) | H.Adj a b} := by
      ext H; simp [hab]
    rw [hset]
    measurability

/-! ### A finite sum of indicators

Both counting random variables in this file — `triangleCount` and `copyCount` — are finite sums
of `Set.indicator … (fun _ => 1)`.  The four facts each of them needs are facts about that shape
alone, so they are stated once here and the specialisations below are one-liners.

The definitions are *not* unified: `triangleCount` sums over vertex triples and `copyCount` over
injective labellings, and both appear in published statements.  Only the arguments are shared.
-/

section IndicatorSum

variable {α : Type*} {ι : Type*}

theorem sum_indicator_one_nonneg (s : Finset ι) (E : ι → Set α) (x : α) :
    0 ≤ ∑ i ∈ s, (E i).indicator (fun _ => (1 : ℝ)) x :=
  Finset.sum_nonneg fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) x

/-- A finite sum of indicators takes no value strictly between `0` and `1`: if it is nonzero then
some summand is `1`, and the rest are nonnegative.

This is the integrality that turns Markov's inequality into a bound on `ℙ(X ≠ 0)`. -/
theorem one_le_sum_indicator_one_of_ne_zero {s : Finset ι} {E : ι → Set α} {x : α}
    (h : ∑ i ∈ s, (E i).indicator (fun _ => (1 : ℝ)) x ≠ 0) :
    1 ≤ ∑ i ∈ s, (E i).indicator (fun _ => (1 : ℝ)) x := by
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hmem : x ∈ E i := by
    by_contra hc
    exact hne (Set.indicator_of_notMem hc _)
  calc (1 : ℝ) = _ := (Set.indicator_of_mem hmem (fun _ => (1 : ℝ))).symm
    _ ≤ _ := Finset.single_le_sum
        (f := fun i => (E i).indicator (fun _ => (1 : ℝ)) x)
        (fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) x) hi

variable [MeasurableSpace α]

theorem measurable_sum_indicator_one {s : Finset ι} {E : ι → Set α}
    (hE : ∀ i ∈ s, MeasurableSet (E i)) :
    Measurable fun x => ∑ i ∈ s, (E i).indicator (fun _ => (1 : ℝ)) x :=
  Finset.measurable_sum _ fun i hi => measurable_const.indicator (hE i hi)

theorem integrable_sum_indicator_one {μ : Measure α} [IsFiniteMeasure μ] {s : Finset ι}
    {E : ι → Set α} (hE : ∀ i ∈ s, MeasurableSet (E i)) :
    Integrable (fun x => ∑ i ∈ s, (E i).indicator (fun _ => (1 : ℝ)) x) μ :=
  integrable_finsetSum _ fun i hi => (integrable_const (1 : ℝ)).indicator (hE i hi)

end IndicatorSum

/-- `triangleCount` is measurable: a finite sum of indicators of measurable events. -/
private lemma measurable_triangleCount {n : ℕ} :
    Measurable (triangleCount : SimpleGraph (Fin n) → ℝ) := by
  unfold triangleCount
  exact measurable_sum_indicator_one fun T _ => measurableSet_setOf_forall_adj T

/-- `triangleCount` is integrable under `G(n, p)`: a finite sum of indicators of measurable
events under a probability measure. -/
private lemma integrable_triangleCount {n : ℕ} (p : I) :
    Integrable (triangleCount : SimpleGraph (Fin n) → ℝ) (binomialRandom (Fin n) p) := by
  unfold triangleCount
  exact integrable_sum_indicator_one fun T _ => measurableSet_setOf_forall_adj T

/-- Every summand of `triangleCount` is an indicator, hence nonnegative. -/
private lemma triangleCount_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) : 0 ≤ triangleCount G :=
  sum_indicator_one_nonneg _ _ G

/-- `triangleCount` takes no value strictly between `0` and `1`: a nonzero value means some
summand is the indicator value `1`, and the remaining summands are nonnegative.

This is the integrality that turns Markov's inequality into a bound on `ℙ(X ≠ 0)`. -/
private lemma one_le_triangleCount_of_ne_zero {n : ℕ} {G : SimpleGraph (Fin n)}
    (h : triangleCount G ≠ 0) : 1 ≤ triangleCount G := by
  rw [triangleCount] at h ⊢
  exact one_le_sum_indicator_one_of_ne_zero h
/-- **`triangleCount` is square-integrable.**

Needed by `prob_eq_zero_le_variance_div_sq`, whose `MemLp X 2` hypothesis is what makes
`Var[X]/𝔼[X]²` meaningful — so the supercritical half of any threshold argument wants this.
Public, because the same fact is needed wherever Chebyshev is applied to a subgraph count.

A finite sum of bounded indicators over a probability measure, so there is nothing to check
beyond measurability of each event. -/
theorem memLp_triangleCount {n : ℕ} (p : I) :
    MemLp (triangleCount : SimpleGraph (Fin n) → ℝ) 2 (binomialRandom (Fin n) p) := by
  unfold triangleCount
  exact memLp_finsetSum _ fun T _ =>
    memLp_indicator_const 2 (measurableSet_setOf_forall_adj T) 1 (Or.inr (measure_ne_top _ _))

/-- `n³/12 ≤ binom(n,3)` for `6 ≤ n`.

Equivalent to `n² - 6n + 4 ≥ 0`, so **`6` is exactly the threshold**: at `n = 5` the claim is
`10.417 ≤ 10`, which is false.  Both halves of §4.1's triangle threshold and Theorem 8.1.6's
`ε`–`N` form spend this bound at the same place, which is why it has a name. -/
theorem cube_div_twelve_le_choose_three {n : ℕ} (hn : 6 ≤ n) :
    (n : ℝ) ^ 3 / 12 ≤ (n.choose 3 : ℝ) := by
  have hn6 : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnat : 6 * n.choose 3 = n * (n - 1) * (n - 2) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose n 3
    simp only [Nat.descFactorial, Nat.factorial, Nat.sub_zero, mul_one] at h
    rw [← h]; ring
  have hc : (6 : ℝ) * (n.choose 3 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) hnat
    push_cast [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n)] at h
    linarith only [h]
  nlinarith only [hc, hn6]

/-- **The supercritical half of the triangle threshold** (Zhao, Proposition 4.1.2): when `p·n` is
large, `G(n, p)` contains a triangle with high probability.

Together with `prob_no_triangle_of_mul_le` this is the threshold: `1/n` is where the triangle
appears.

**This half needs both a scale `M` and an `N`, unlike the subcritical one.**  Chebyshev's error is
`Var/𝔼² ≤ 144/(p·n)³ + 144/(n·(p·n))` — using `binom(n,3) ≥ n³/12`, valid for `n ≥ 6` — and the
two terms vanish for different reasons: the first once `p·n` is large, the second only once `n`
is large *as well*.  No choice of `M` alone controls it, which is why the statement quantifies
over both.  Take `M` with `144/M³ ≤ ε/2`, then `N ≥ 6` with `144/(N·M) ≤ ε/2`.

The probability is written `Measure.real` rather than `(… ).toReal`, following the convention the
subcritical node's review established; the ingredients are `memLp_triangleCount`,
`integral_triangleCount`, `variance_triangleCount_le` and `prob_eq_zero_le_variance_div_sq`, all
proved above. -/
theorem prob_triangle_of_le_mul :
    ∀ ε : ℝ, 0 < ε → ∃ M > 0, ∃ N : ℕ, ∀ (n : ℕ), N ≤ n → ∀ p : I, M ≤ (p : ℝ) * n →
      1 - ε ≤ (binomialRandom (Fin n) p).real {G | triangleCount G ≠ 0} := by
  intro ε hε
  refine ⟨max 1 (288 / ε), lt_max_iff.mpr (Or.inl one_pos), 6, fun n hn p hpn => ?_⟩
  -- The scale hypothesis gives `p · n ≥ 1` and `(p · n) · ε ≥ 288`; the threshold gives `n ≥ 6`.
  have hM1 : (1 : ℝ) ≤ max 1 (288 / ε) := le_max_left _ _
  have hMe : 288 / ε ≤ max 1 (288 / ε) := le_max_right _ _
  have ht1 : (1 : ℝ) ≤ (p : ℝ) * n := hM1.trans hpn
  have hεt : 288 ≤ (p : ℝ) * n * ε := (div_le_iff₀ hε).mp (hMe.trans hpn)
  have hn6 : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := p.2.1
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hppos : (0 : ℝ) < (p : ℝ) := by
    rcases hp0.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at ht1; linarith
  -- `binom(n,3) = n(n-1)(n-2)/6 ≥ n³/12`, which holds from `n = 6` up.
  have hchoose := cube_div_twelve_le_choose_three hn
  have hmean : ∫ G, triangleCount G ∂(binomialRandom (Fin n) p)
      = (n.choose 3 : ℝ) * (p : ℝ) ^ 3 := integral_triangleCount n p
  have hEpos : 0 < (n.choose 3 : ℝ) * (p : ℝ) ^ 3 := by
    have h3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
    exact mul_pos (by linarith) (pow_pos hppos 3)
  have hcheb := prob_eq_zero_le_variance_div_sq (memLp_triangleCount p)
    (by rw [hmean]; exact hEpos.ne')
  have hvar := variance_triangleCount_le n p
  -- `144 / (p·n)³ ≤ ε/2`: the first Chebyshev term, controlled by the scale alone.
  have hA0 : 288 ≤ ε * ((n : ℝ) ^ 3 * (p : ℝ) ^ 3) := by
    have ht2 : (1 : ℝ) ≤ ((p : ℝ) * n) ^ 2 := by nlinarith only [ht1]
    have e1 : 288 * ((p : ℝ) * n) ^ 2 ≤ (p : ℝ) * n * ε * ((p : ℝ) * n) ^ 2 :=
      mul_le_mul_of_nonneg_right hεt (by positivity)
    linarith only [e1, ht2]
  have hA : 288 * ((n : ℝ) ^ 3 * (p : ℝ) ^ 3) ≤ ε * ((n : ℝ) ^ 6 * (p : ℝ) ^ 6) := by
    have h := mul_le_mul_of_nonneg_right hA0
      (show (0 : ℝ) ≤ (n : ℝ) ^ 3 * (p : ℝ) ^ 3 by positivity)
    linarith only [h]
  -- `144 / (n·(p·n)) ≤ ε/2`: the second term, which also needs `n` large.
  have hB0 : 288 ≤ ε * ((n : ℝ) ^ 2 * (p : ℝ)) := by
    have e1 : 288 * (n : ℝ) ≤ (p : ℝ) * n * ε * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hεt hnpos.le
    linarith only [e1, hn6]
  have hB : 288 * ((n : ℝ) ^ 4 * (p : ℝ) ^ 5) ≤ ε * ((n : ℝ) ^ 6 * (p : ℝ) ^ 6) := by
    have h := mul_le_mul_of_nonneg_right hB0
      (show (0 : ℝ) ≤ (n : ℝ) ^ 4 * (p : ℝ) ^ 5 by positivity)
    linarith only [h]
  -- Chebyshev's error is at most `ε`, since `𝔼² ≥ n⁶p⁶/144`.
  have hkey : Var[(triangleCount : SimpleGraph (Fin n) → ℝ); binomialRandom (Fin n) p]
      / (∫ G, triangleCount G ∂(binomialRandom (Fin n) p)) ^ 2 ≤ ε := by
    have hstep : (n : ℝ) ^ 3 * (p : ℝ) ^ 3 / 12 ≤ (n.choose 3 : ℝ) * (p : ℝ) ^ 3 := by
      have h := mul_le_mul_of_nonneg_right hchoose (pow_nonneg hp0 3)
      linarith only [h]
    have hsq : ((n : ℝ) ^ 3 * (p : ℝ) ^ 3 / 12) ^ 2 ≤ ((n.choose 3 : ℝ) * (p : ℝ) ^ 3) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hstep 2
    rw [hmean, div_le_iff₀ (pow_pos hEpos 2)]
    linarith only [hvar, hA, hB, mul_le_mul_of_nonneg_left hsq hε.le]
  -- Complement: `ℙ(X ≠ 0) = 1 - ℙ(X = 0) ≥ 1 - ε`.
  have hmeasS : MeasurableSet {G : SimpleGraph (Fin n) | triangleCount G = 0} :=
    measurable_triangleCount (measurableSet_singleton 0)
  have hzero : (binomialRandom (Fin n) p).real {G : SimpleGraph (Fin n) | triangleCount G = 0}
      ≤ ε := by
    rw [measureReal_def]
    exact hcheb.trans hkey
  have hset : {G : SimpleGraph (Fin n) | triangleCount G ≠ 0}
      = {G : SimpleGraph (Fin n) | triangleCount G = 0}ᶜ := rfl
  rw [hset, probReal_compl_eq_one_sub hmeasS]
  linarith

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
  intro ε hε
  refine ⟨min 1 ε, lt_min one_pos hε, fun n p hpn => ?_⟩
  set μ := binomialRandom (Fin n) p with hμ
  set S : Set (SimpleGraph (Fin n)) := {G | triangleCount G = 0} with hSdef
  have hmeasS : MeasurableSet S := measurable_triangleCount (measurableSet_singleton 0)
  -- Markov: `triangleCount` dominates the indicator of `{X ≠ 0}`, since it is nonnegative and
  -- at least `1` wherever it is nonzero.
  have hmark : μ.real Sᶜ ≤ ∫ G, triangleCount G ∂μ := by
    have hle : ∀ G, Sᶜ.indicator (fun _ => (1 : ℝ)) G ≤ triangleCount G := by
      intro G
      by_cases hG : G ∈ Sᶜ
      · rw [Set.indicator_of_mem hG]
        exact one_le_triangleCount_of_ne_zero hG
      · rw [Set.indicator_of_notMem hG]
        exact triangleCount_nonneg G
    have h := integral_mono ((integrable_const (1 : ℝ)).indicator hmeasS.compl)
      (integrable_triangleCount p) hle
    rwa [integral_indicator_const _ hmeasS.compl, smul_eq_mul, mul_one] at h
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := p.2.1
  -- `𝔼X = binom(n,3) p³ ≤ (p·n)³/6 ≤ δ³/6 ≤ ε`, uniformly in `n`.
  have hexp : ∫ G, triangleCount G ∂μ ≤ ε := by
    rw [hμ, integral_triangleCount n p]
    have hchoose : (n.choose 3 : ℝ) ≤ (n : ℝ) ^ 3 / 6 := by
      have := Nat.choose_le_pow_div (α := ℝ) 3 n
      norm_num [Nat.factorial] at this ⊢
      linarith
    have hpn0 : (0 : ℝ) ≤ (p : ℝ) * n := by positivity
    have h1 : (n.choose 3 : ℝ) * (p : ℝ) ^ 3 ≤ ((p : ℝ) * n) ^ 3 / 6 := by
      have := mul_le_mul_of_nonneg_right hchoose (pow_nonneg hp0 3)
      nlinarith only [this]
    have h2 : ((p : ℝ) * n) ^ 3 ≤ min 1 ε ^ 3 := pow_le_pow_left₀ hpn0 hpn 3
    have h3 : min 1 ε ^ 3 ≤ ε := by
      have ha : min 1 ε ≤ 1 := min_le_left _ _
      have hb : min 1 ε ≤ ε := min_le_right _ _
      have hc : (0 : ℝ) < min 1 ε := lt_min one_pos hε
      have hkey : (0 : ℝ) ≤ min 1 ε * (1 - min 1 ε) * (1 + min 1 ε) :=
        mul_nonneg (mul_nonneg hc.le (by linarith)) (by linarith)
      linarith only [hkey, hb]
    linarith
  have hcompl : μ.real Sᶜ = 1 - μ.real S := probReal_compl_eq_one_sub hmeasS
  have hfinal : 1 - μ.real S ≤ ε := by rw [← hcompl]; linarith
  rw [hSdef] at hfinal
  simp only [measureReal_def] at hfinal
  linarith

/-! ### §4.2: thresholds for a fixed subgraph

Definition 4.2.7 and the count the threshold is stated against.  `maxEdgeVertexRatio` is `m(H)`,
whose reciprocal `n ^ (-1 / m H)` is the threshold of Theorem 4.2.10 (Bollobás 1981).
-/

section Subgraphs

variable {V : Type*} [Fintype V]

/-- The **edge-vertex ratio** `ρ(H') = e_{H'} / v_{H'}` of Definition 4.2.7, for `H'` the
subgraph of `G` induced on `s`.  Half the average degree of that subgraph.

`s = ∅` gives `0 / 0 = 0`, which is the value `maxEdgeVertexRatio` wants there anyway. -/
noncomputable def edgeVertexRatio (G : SimpleGraph V) (s : Finset V) : ℝ :=
  ({e ∈ G.edgeSet | ∀ v ∈ e, v ∈ s} : Set (Sym2 V)).ncard / s.card

/-- The **maximum edge-vertex ratio over subgraphs**, `m(H)` of Definition 4.2.7.

Zhao maximises over all subgraphs `H' ⊆ H`; the maximum is taken over vertex *subsets* here, and
the two agree.  Within a fixed vertex set, adding an edge of `G` raises `e_{H'}` and leaves
`v_{H'}` alone, so the densest subgraph on a given vertex set is the induced one, and every
subgraph has a vertex set.  On Example 4.2.8 — `K₄` with a pendant edge — this gives
`ρ(H) = 7/5` but `m(H) = ρ(K₄) = 3/2`, matching the source. -/
noncomputable def maxEdgeVertexRatio (G : SimpleGraph V) : ℝ :=
  (univ : Finset (Finset V)).sup' ⟨∅, mem_univ _⟩ (edgeVertexRatio G)

theorem edgeVertexRatio_le_maxEdgeVertexRatio (G : SimpleGraph V) (s : Finset V) :
    edgeVertexRatio G s ≤ maxEdgeVertexRatio G :=
  le_sup' _ (mem_univ s)

theorem maxEdgeVertexRatio_nonneg (G : SimpleGraph V) : 0 ≤ maxEdgeVertexRatio G :=
  le_trans (by simp [edgeVertexRatio]) (le_sup' (edgeVertexRatio G) (mem_univ (∅ : Finset V)))

variable [DecidableEq V]

/-- The edges of `H` transported to `Fin n` along a labelling `f`. -/
def transportedEdges (H : SimpleGraph V) [DecidableRel H.Adj] {n : ℕ} (f : V → Fin n) :
    Finset (Sym2 (Fin n)) := H.edgeFinset.image (Sym2.map f)

/-- The number of **labelled copies** of `H` in `G`: injections `V → Fin n` carrying every edge
of `H` to an edge of `G`.

Written with `Set.indicator` over sets of graphs for the same reason as `triangleCount` — the
measure below ranges over all graphs on `Fin n`, where no `DecidableRel G.Adj` is available. -/
noncomputable def copyCount (H : SimpleGraph V) [DecidableRel H.Adj] {n : ℕ}
    (G : SimpleGraph (Fin n)) : ℝ :=
  ∑ f ∈ (univ : Finset (V → Fin n)).filter Function.Injective,
    ({K : SimpleGraph (Fin n) | ↑(transportedEdges H f) ⊆ K.edgeSet}).indicator (fun _ => 1) G

/-- **The expected number of labelled copies of `H` in `G(n, p)`** is
`n^{\underline{v_H}} · p^{e_H}`.

Each of the `n.descFactorial v_H` injections contributes the probability that its `e_H`
transported edges are all present, which is `p ^ e_H` by
`binomialRandom_setOf_subset_edgeSet` — the transported edges are distinct, and none is a loop,
because the labelling is injective. -/
theorem integral_copyCount (H : SimpleGraph V) [DecidableRel H.Adj] (n : ℕ) (p : I) :
    ∫ G, copyCount H G ∂(binomialRandom (Fin n) p)
      = (n.descFactorial (Fintype.card V) : ℝ) * (p : ℝ) ^ H.edgeFinset.card := by
  have key : ∀ f ∈ (univ : Finset (V → Fin n)).filter Function.Injective,
      MeasurableSet {K : SimpleGraph (Fin n) | ↑(transportedEdges H f) ⊆ K.edgeSet} ∧
      binomialRandom (Fin n) p {K : SimpleGraph (Fin n) | ↑(transportedEdges H f) ⊆ K.edgeSet}
        = (toNNReal p : ENNReal) ^ H.edgeFinset.card := by
    intro f hf
    have hinj : Function.Injective f := (Finset.mem_filter.1 hf).2
    have hnd : ∀ e ∈ transportedEdges H f, ¬ e.IsDiag := by
      intro e he
      obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 he
      rw [Sym2.isDiag_map hinj]
      exact H.not_isDiag_of_mem_edgeSet (mem_edgeFinset.1 he')
    have hcard : (transportedEdges H f).card = H.edgeFinset.card :=
      Finset.card_image_of_injective _ (Sym2.map.injective hinj)
    exact ⟨measurableSet_setOf_subset_edgeSet _,
      by rw [binomialRandom_setOf_subset_edgeSet p _ hnd, hcard]⟩
  have hcount : ((univ : Finset (V → Fin n)).filter Function.Injective).card
      = n.descFactorial (Fintype.card V) := by
    rw [← Fintype.card_subtype,
      Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding V (Fin n)),
      Fintype.card_embedding_eq, Fintype.card_fin]
  simp only [copyCount]
  rw [MeasureTheory.integral_finsetSum _ fun f hf =>
    memLp_one_iff_integrable.mp
      (memLp_indicator_const 1 (key f hf).1 1 (Or.inr (measure_ne_top _ _)))]
  rw [Finset.sum_congr rfl fun f hf => ?_, Finset.sum_const, nsmul_eq_mul, hcount]
  rw [MeasureTheory.integral_indicator_const _ (key f hf).1, Measure.real, (key f hf).2,
    smul_eq_mul, mul_one, ENNReal.toReal_pow, ENNReal.coe_toReal, unitInterval.coe_toNNReal]

/-- `copyCount` is measurable: a finite sum of indicators of measurable events. -/
private lemma measurable_copyCount (H : SimpleGraph V) [DecidableRel H.Adj] {n : ℕ} :
    Measurable fun G : SimpleGraph (Fin n) => copyCount H G := by
  unfold copyCount
  exact measurable_sum_indicator_one fun f _ => measurableSet_setOf_subset_edgeSet _

/-- `copyCount` is integrable under `G(n, p)`: a finite sum of indicators of measurable events
under a probability measure. -/
private lemma integrable_copyCount (H : SimpleGraph V) [DecidableRel H.Adj] {n : ℕ} (p : I) :
    Integrable (fun G : SimpleGraph (Fin n) => copyCount H G) (binomialRandom (Fin n) p) := by
  unfold copyCount
  exact integrable_sum_indicator_one fun f _ => measurableSet_setOf_subset_edgeSet _

/-- Every summand of `copyCount` is an indicator, hence nonnegative. -/
private lemma copyCount_nonneg (H : SimpleGraph V) [DecidableRel H.Adj] {n : ℕ}
    (G : SimpleGraph (Fin n)) : 0 ≤ copyCount H G :=
  sum_indicator_one_nonneg _ _ G

/-- `copyCount` takes no value strictly between `0` and `1`: a nonzero value means some summand
is the indicator value `1`, and the remaining summands are nonnegative.

This is the integrality that turns Markov's inequality into a bound on `ℙ(count ≠ 0)`. -/
private lemma one_le_copyCount_of_ne_zero (H : SimpleGraph V) [DecidableRel H.Adj] {n : ℕ}
    {G : SimpleGraph (Fin n)} (h : copyCount H G ≠ 0) : 1 ≤ copyCount H G := by
  rw [copyCount] at h ⊢
  exact one_le_sum_indicator_one_of_ne_zero h

/-- **The 0-statement's engine** (Zhao, §4.2): `G(n, p)` contains a labelled copy of `H` with
probability at most `n^{\underline{v_H}} p^{e_H}`.

Markov's inequality on `copyCount`, whose mean is `integral_copyCount`: the count is a sum of
indicators, so it is integer-valued and `ℙ(count ≠ 0) = ℙ(count ≥ 1) ≤ 𝔼 count`.

This is the half of Theorem 4.2.10 that needs no second moment.  It is also where Example 4.2.6
bites: run against `H` itself the bound gives the threshold `n^{-v_H/e_H}`, which for `K₄` with a
pendant edge is `n^{-5/7}` rather than the correct `n^{-2/3}`.  The 1-statement has to be run
against the **densest subgraph** `H'`, which is what `maxEdgeVertexRatio` is for. -/
theorem prob_copyCount_ne_zero_le (H : SimpleGraph V) [DecidableRel H.Adj] (n : ℕ) (p : I) :
    (binomialRandom (Fin n) p).real {G : SimpleGraph (Fin n) | copyCount H G ≠ 0}
      ≤ (n.descFactorial (Fintype.card V) : ℝ) * (p : ℝ) ^ H.edgeFinset.card := by
  have hmeas : MeasurableSet {G : SimpleGraph (Fin n) | copyCount H G ≠ 0} :=
    measurable_copyCount H (measurableSet_singleton (0 : ℝ)).compl
  -- Markov: `copyCount` dominates the indicator of `{count ≠ 0}`, being nonnegative and at
  -- least `1` wherever it is nonzero.
  have hle : ∀ G, ({G : SimpleGraph (Fin n) | copyCount H G ≠ 0}).indicator (fun _ => (1 : ℝ)) G
      ≤ copyCount H G := by
    intro G
    by_cases hG : G ∈ {G : SimpleGraph (Fin n) | copyCount H G ≠ 0}
    · rw [Set.indicator_of_mem hG]
      exact one_le_copyCount_of_ne_zero H hG
    · rw [Set.indicator_of_notMem hG]
      exact copyCount_nonneg H G
  have h := integral_mono ((integrable_const (1 : ℝ)).indicator hmeas)
    (integrable_copyCount H p) hle
  rwa [integral_indicator_const _ hmeas, smul_eq_mul, mul_one, integral_copyCount H n p] at h

end Subgraphs

end ProbMethodCombinatorics
