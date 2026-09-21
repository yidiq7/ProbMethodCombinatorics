import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic

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

theorem memLp_sum_indicator_one {μ : Measure α} [IsFiniteMeasure μ] {s : Finset ι}
    {E : ι → Set α} (hE : ∀ i ∈ s, MeasurableSet (E i)) :
    MemLp (fun x => ∑ i ∈ s, (E i).indicator (fun _ => (1 : ℝ)) x) 2 μ :=
  memLp_finsetSum _ fun i hi =>
    memLp_indicator_const 2 (hE i hi) 1 (Or.inr (measure_ne_top μ _))

/-- The mean of a finite sum of indicators is the sum of the event probabilities. -/
theorem integral_sum_indicator_one {μ : Measure α} [IsFiniteMeasure μ] {s : Finset ι}
    {E : ι → Set α} (hE : ∀ i ∈ s, MeasurableSet (E i)) :
    μ[fun x => ∑ i ∈ s, (E i).indicator (fun _ => (1 : ℝ)) x] = ∑ i ∈ s, (μ (E i)).toReal := by
  rw [MeasureTheory.integral_finsetSum _ fun i hi =>
    (integrable_const (1 : ℝ)).indicator (hE i hi)]
  exact Finset.sum_congr rfl fun i hi => by
    rw [integral_indicator_const _ (hE i hi), smul_eq_mul, mul_one, measureReal_def]

end IndicatorSum

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

The second moment is computed directly over `S.powerset` rather than through a measure: an
induction on `S`, carrying a free shift `t`, gives
`∑_{A ⊆ T} (t + 2 ∑_A x - ∑_T x) ^ 2 = 2 ^ #T * (t ^ 2 + ∑_T x ^ 2)`, which at `t = 0` is the
centred second moment of `2 ∑_A x - ∑_S x`.  Chebyshev is then applied in counting form: the
subsets outside the window each contribute at least `d ^ 2`, so at most `16/49` of them miss it.
This is the one Chapter 4 result that touches none of Mathlib's probability API — it uses neither
`prob_eq_zero_le_variance_div_sq` nor `variance_sum_indicator_le`.

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
  -- Distinctness of the subset sums says exactly that `A ↦ ∑ x ∈ A, x` is injective on
  -- `S.powerset`, and every such sum is at most `n * k`: pigeonhole already gives `2 ^ k ≤ n k + 1`.
  have hinj : Set.InjOn (fun A => ∑ x ∈ A, x) ↑S.powerset := fun A hA B hB h =>
    hdistinct A (Finset.mem_powerset.1 hA) B (Finset.mem_powerset.1 hB) h
  have hle : ∀ A ∈ S.powerset, ∑ x ∈ A, x ≤ n * k := fun A hA =>
    calc ∑ x ∈ A, x ≤ ∑ _x ∈ A, n :=
          Finset.sum_le_sum fun x hx => hSn x (Finset.mem_powerset.1 hA hx)
      _ ≤ n * k := by
          simpa [mul_comm] using
            Nat.mul_le_mul_left n (hScard ▸ Finset.card_le_card (Finset.mem_powerset.1 hA))
  have hpigeon : (2:ℕ) ^ k ≤ n * k + 1 := by
    simpa [Finset.card_powerset, hScard] using Finset.card_le_card_of_injOn
      (fun A => ∑ x ∈ A, x) (fun A hA => Finset.mem_range.2 (Nat.lt_succ_of_le (hle A hA))) hinj
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · have h2 : 2 ≤ 2 ^ k := by simpa using Nat.pow_le_pow_right (by norm_num) hk
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
  · have h64 : (64:ℝ) ≤ 2 ^ k := by
      calc (64:ℝ) = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk6
    -- The centred second moment over all subsets of `T`, with a free shift `t` carrying the
    -- induction: `∑_{A ⊆ T} (t + 2 ∑_A x - ∑_T x) ^ 2 = 2 ^ #T * (t ^ 2 + ∑_T x ^ 2)`.
    have key : ∀ (T : Finset ℕ) (t : ℝ),
        ∑ A ∈ T.powerset, (t + 2 * ∑ x ∈ A, (x:ℝ) - ∑ x ∈ T, (x:ℝ)) ^ 2
          = 2 ^ T.card * (t ^ 2 + ∑ x ∈ T, (x:ℝ) ^ 2) := by
      intro T
      induction T using Finset.induction with
      | empty => simp
      | @insert a T ha ih =>
          intro t
          have hout : ∀ A ∈ T.powerset,
              (t + 2 * ∑ x ∈ A, (x:ℝ) - ∑ x ∈ insert a T, (x:ℝ)) ^ 2
                = (t - a + 2 * ∑ x ∈ A, (x:ℝ) - ∑ x ∈ T, (x:ℝ)) ^ 2 := fun A _ => by
            rw [Finset.sum_insert ha]; ring
          have hins : ∀ A ∈ T.powerset,
              (t + 2 * ∑ x ∈ insert a A, (x:ℝ) - ∑ x ∈ insert a T, (x:ℝ)) ^ 2
                = (t + a + 2 * ∑ x ∈ A, (x:ℝ) - ∑ x ∈ T, (x:ℝ)) ^ 2 := fun A hA => by
            rw [Finset.sum_insert (fun h => ha (Finset.mem_powerset.1 hA h)),
              Finset.sum_insert ha]
            ring
          rw [Finset.sum_powerset_insert ha, Finset.sum_congr rfl hout,
            Finset.sum_congr rfl hins, ih (t - a), ih (t + a), Finset.card_insert_of_notMem ha,
            Finset.sum_insert ha]
          ring
    -- `s` is the total and `d` twice the Chebyshev half-width `c = (7/8) * n * √k`, so the
    -- window of half-width `c` about the mean `s / 2` is `|2 * ∑_A x - s| < d`.
    set s : ℝ := ∑ x ∈ S, (x:ℝ) with hs
    set d : ℝ := 7/4 * n * r with hd
    have hd0 : 0 < d := mul_pos (mul_pos (by norm_num) (by linarith)) hrpos
    have hmom : ∑ A ∈ S.powerset, (2 * ∑ x ∈ A, (x:ℝ) - s) ^ 2 = 2 ^ k * ∑ x ∈ S, (x:ℝ) ^ 2 := by
      simpa [hScard, hs] using key S 0
    have hQ : ∑ x ∈ S, (x:ℝ) ^ 2 ≤ (k:ℝ) * (n:ℝ) ^ 2 := by
      calc ∑ x ∈ S, (x:ℝ) ^ 2 ≤ ∑ _x ∈ S, (n:ℝ) ^ 2 := Finset.sum_le_sum fun x hx =>
            pow_le_pow_left₀ (Nat.cast_nonneg x) (by exact_mod_cast hSn x hx) 2
        _ = (k:ℝ) * (n:ℝ) ^ 2 := by rw [Finset.sum_const, hScard, nsmul_eq_mul]
    -- Chebyshev in counting form: at most `16/49` of the subsets miss the window, so the
    -- surviving family `F` carries at least `33/49 * 2 ^ k` of them.
    set F : Finset (Finset ℕ) := S.powerset.filter (fun A => |2 * ∑ x ∈ A, (x:ℝ) - s| < d) with hF
    set G : Finset (Finset ℕ) :=
      S.powerset.filter (fun A => ¬ |2 * ∑ x ∈ A, (x:ℝ) - s| < d)
    have hbad : (G.card : ℝ) * d ^ 2 ≤ 2 ^ k * ((k:ℝ) * (n:ℝ) ^ 2) := by
      calc (G.card : ℝ) * d ^ 2 = ∑ _A ∈ G, d ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ A ∈ G, (2 * ∑ x ∈ A, (x:ℝ) - s) ^ 2 := Finset.sum_le_sum fun A hA => by
            have h1 := not_lt.1 (Finset.mem_filter.1 hA).2
            exact (sq_le_sq' (by linarith [abs_nonneg (2 * ∑ x ∈ A, (x:ℝ) - s)]) h1).trans_eq
              (sq_abs _)
        _ ≤ ∑ A ∈ S.powerset, (2 * ∑ x ∈ A, (x:ℝ) - s) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun A _ _ => sq_nonneg _)
        _ = 2 ^ k * ∑ x ∈ S, (x:ℝ) ^ 2 := hmom
        _ ≤ 2 ^ k * ((k:ℝ) * (n:ℝ) ^ 2) := by gcongr
    have hsplit : (F.card : ℝ) + G.card = 2 ^ k := by
      have := Finset.card_filter_add_card_filter_not (s := S.powerset)
        (p := fun A => |2 * ∑ x ∈ A, (x:ℝ) - s| < d)
      rw [Finset.card_powerset, hScard] at this
      exact_mod_cast congrArg (Nat.cast (R := ℝ)) this
    have hFlow : 33/49 * 2 ^ k ≤ (F.card : ℝ) := by
      have hd2 : d ^ 2 = 49/16 * ((k:ℝ) * (n:ℝ) ^ 2) := by rw [hd, ← hr2]; ring
      have h1 : (G.card : ℝ) ≤ 16/49 * 2 ^ k :=
        le_of_mul_le_mul_right (by rw [hd2] at hbad ⊢; linarith) (pow_pos hd0 2)
      linarith
    -- The sums taken on `F` are distinct naturals inside an interval of length `d`, and an
    -- interval of length `d` holds at most `d + 1` of them.  This is where the `+ 1` enters.
    have hcount : (F.card : ℝ) ≤ d + 1 := by
      rcases F.eq_empty_or_nonempty with hFe | ⟨A₀, hA₀⟩
      · rw [hFe]; simp only [Finset.card_empty, Nat.cast_zero]; linarith
      · set T : Finset ℕ := F.image (fun A => ∑ x ∈ A, x)
        have hTne : T.Nonempty := ⟨_, Finset.mem_image_of_mem _ hA₀⟩
        have hTcard : T.card = F.card :=
          Finset.card_image_of_injOn (hinj.mono (by rw [hF]; exact Finset.filter_subset _ _))
        have hbd : ∀ t ∈ T, |2 * (t:ℝ) - s| < d := by
          intro t ht
          obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 ht
          have h1 := (Finset.mem_filter.1 hA).2
          rwa [Nat.cast_sum]
        have hlo := T.min'_mem hTne
        have hhi := T.max'_mem hTne
        have hsub : T ⊆ Finset.Icc (T.min' hTne) (T.max' hTne) := fun t ht =>
          Finset.mem_Icc.2 ⟨T.min'_le t ht, T.le_max' t ht⟩
        have hcards : T.card ≤ T.max' hTne + 1 - T.min' hTne := by
          simpa [Nat.card_Icc] using Finset.card_le_card hsub
        have hcast : (F.card : ℝ) ≤ (T.max' hTne : ℝ) + 1 - (T.min' hTne : ℝ) := by
          rw [← hTcard]
          have h2 := (Nat.cast_le (α := ℝ)).2 hcards
          rwa [Nat.cast_sub (by have := T.min'_le _ hhi; omega), Nat.cast_add, Nat.cast_one] at h2
        have h1 := abs_lt.1 (hbd _ hlo)
        have h2 := abs_lt.1 (hbd _ hhi)
        linarith
    rw [hd] at hcount
    linarith [hFlow.trans hcount]
  · -- For `k ≤ 5` the pigeonhole bound `2 ^ k ≤ n * k + 1` is already stronger than the claim.
    have hk6' : k < 6 := by omega
    interval_cases k <;>
      · push_cast at hr2 hpigR ⊢
        nlinarith [hr0, hr2, hpigR, hn0, sq_nonneg (r - 1), sq_nonneg (r - 2), sq_nonneg (r - 3),
          mul_nonneg hr0 (by linarith : (0:ℝ) ≤ (n:ℝ))]

/-- **Lemma 4.2.4 in finite form** (Zhao, Setup 4.2.2 and Lemma 4.2.4): for a sum of indicators
with positive mean,

    ℙ(X = 0) ≤ (𝔼X + ∑_{q ∈ D} ℙ(A_{q.1} ∩ A_{q.2})) / (𝔼X)².

Chebyshev — `prob_eq_zero_le_variance_div_sq` — composed with `variance_sum_indicator_le`, whose
right-hand side is already `𝔼X + ∑_D ℙ(A ∩ A)`.  Nothing new is proved; this is the form §4.2's
1-statement consumes, and it is worth naming because both inputs have to be lined up on the same
`D` and the same mean.

Zhao writes the second term as `(𝔼X) Δ*` with `Δ* = max_i ∑_{j ∼ i} ℙ(A_j | A_i)`.  That is the
same quantity bounded above: `∑_D ℙ(A_i ∩ A_j) = ∑_i ℙ(A_i) ∑_{j ∼ i} ℙ(A_j | A_i) ≤ (𝔼X) Δ*`.
The sum form is kept here because `D` is already a parameter of `variance_sum_indicator_le` — it
is not derived from `A`, since independence is not decidable — and introducing `Δ*` as a
definition would add a `max` over conditional probabilities that no consumer needs. -/
theorem prob_sum_indicator_eq_zero_le [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (D : Finset (ι × ι))
    (hD : ∀ i j, i ≠ j → (i, j) ∉ D → IndepSet (A i) (A j) μ)
    (hmean : (∑ i, (μ (A i)).toReal) ≠ 0) :
    (μ {ω | ∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω = 0}).toReal
      ≤ ((∑ i, (μ (A i)).toReal) + ∑ q ∈ D, (μ (A q.1 ∩ A q.2)).toReal)
          / (∑ i, (μ (A i)).toReal) ^ 2 := by
  have hmem : MemLp (fun ω => ∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω) 2 μ :=
    memLp_sum_indicator_one fun i _ => hA i
  have hint : μ[fun ω => ∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω]
      = ∑ i, (μ (A i)).toReal := integral_sum_indicator_one fun i _ => hA i
  -- Chebyshev, with the mean rewritten as `∑ i, ℙ(A i)`.
  have hcheb := prob_eq_zero_le_variance_div_sq hmem (by rw [hint]; exact hmean)
  rw [hint] at hcheb
  -- The variance bound is exactly the claimed numerator, and the denominator is a square.
  exact hcheb.trans
    (div_le_div_of_nonneg_right (variance_sum_indicator_le A hA D hD) (sq_nonneg _))

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

/-- **Vertex sets meeting in at most one vertex span disjoint edge sets.**  A shared edge would
put two shared vertices in the intersection, and `offDiagPairs` of a set of size at most one is
empty — `card_offDiagPairs_add` gives `binom(1,2) = 0` and `binom(2,2) = 1`.

No element is ever named: `offDiagPairs_inter` turns the emptiness of `offDiagPairs (A ∩ B)`
straight into disjointness.  This is the admissibility hypothesis every Janson family over
cliques needs, at any clique size. -/
theorem disjoint_offDiagPairs_of_card_inter_le_one {n : ℕ} (A B : Finset (Fin n))
    (h : (A ∩ B).card ≤ 1) :
    Disjoint (↑(offDiagPairs A) : Set (Sym2 (Fin n)))
      (↑(offDiagPairs B) : Set (Sym2 (Fin n))) := by
  have hcard := card_offDiagPairs_add (A ∩ B)
  have hc : (A ∩ B).card = 0 ∨ (A ∩ B).card = 1 := by omega
  have hempty : offDiagPairs (A ∩ B) = ∅ := by
    rcases hc with hc | hc <;> rw [hc] at hcard <;> simpa [Nat.choose] using hcard
  rw [Finset.disjoint_coe, Finset.disjoint_iff_inter_eq_empty, offDiagPairs_inter]
  exact hempty

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
  -- `#(offDiagPairs S)` depends on `S` only through `#S`, via `binom(#S, 2)`.
  have hoff : ∀ (S : Finset (Fin n)) (m c : ℕ), S.card = m → (m + 1).choose 2 = c + m →
      (offDiagPairs S).card = c := fun S m c hm hc => by
    have h := card_offDiagPairs_add S
    rw [hm, hc] at h
    omega
  have hcard3 : ∀ T : {T // T ∈ 𝒯}, (offDiagPairs T.1).card = 3 :=
    fun T => hoff _ 3 3 (hcard3' T) (by decide)
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
    have hne : i.1 ∩ j.1 ≠ i.1 := fun h => hij (Subtype.ext (Finset.eq_of_subset_of_card_le
      (h ▸ Finset.inter_subset_right) (le_of_eq (by rw [hcard3' i, hcard3' j]))))
    have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.inter_subset_left, hne⟩)
    rw [hcard3' i] at this
    omega
  -- Two triangles span `3 + 3` pairs less the ones drawn from their shared vertices.
  have hunionpairs : ∀ i j : {T // T ∈ 𝒯},
      (offDiagPairs i.1 ∪ offDiagPairs j.1).card + (offDiagPairs (i.1 ∩ j.1)).card = 6 := by
    intro i j
    have h := Finset.card_union_add_card_inter (offDiagPairs i.1) (offDiagPairs j.1)
    rw [offDiagPairs_inter, hcard3 i, hcard3 j] at h
    omega
  -- Both triangles present is exactly: every pair in the union of their pair sets is an edge.
  have hboth : ∀ (i j : {T // T ∈ 𝒯}) (k : ℕ), (offDiagPairs i.1 ∪ offDiagPairs j.1).card = k →
      binomialRandom (Fin n) p (A i ∩ A j) = (toNNReal p : ENNReal) ^ k := by
    intro i j k hk
    show binomialRandom (Fin n) p
        ({G : SimpleGraph (Fin n) | ↑(offDiagPairs i.1) ⊆ G.edgeSet} ∩
          {G : SimpleGraph (Fin n) | ↑(offDiagPairs j.1) ⊆ G.edgeSet}) = _
    rw [setOf_subset_edgeSet_inter,
      binomialRandom_setOf_subset_edgeSet p (offDiagPairs i.1 ∪ offDiagPairs j.1)
        (fun _ he => by
          rcases Finset.mem_union.1 he with h | h <;> exact not_isDiag_of_mem_offDiagPairs h),
      hk]
  -- Sharing at most one vertex means disjoint pair sets, hence independence.
  have hD : ∀ i j, i ≠ j → (i, j) ∉ D →
      IndepSet (A i) (A j) (binomialRandom (Fin n) p) := by
    intro i j hij hnotD
    have h2 : (i.1 ∩ j.1).card ≠ 2 := fun h =>
      hnotD (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    have hle1 : (i.1 ∩ j.1).card ≤ 1 := by have := hinterle i j hij; omega
    have hempty : (offDiagPairs (i.1 ∩ j.1)).card = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle1 with hk | hk
      exacts [hoff _ 0 0 hk (by decide), hoff _ 1 0 hk (by decide)]
    rw [indepSet_iff_measure_inter_eq_mul (μ := binomialRandom (Fin n) p) (hmeas i) (hmeas j),
      hboth i j 6 (by have := hunionpairs i j; omega), hprob i, hprob j]
    ring
  -- Sharing exactly two vertices means five pairs between them.
  have hprob5 : ∀ q ∈ D, binomialRandom (Fin n) p (A q.1 ∩ A q.2) = (toNNReal p : ENNReal) ^ 5 :=
    fun q hq => hboth q.1 q.2 5 (by
      have hone := hoff _ 2 1 (Finset.mem_filter.1 hq).2 (by decide)
      have := hunionpairs q.1 q.2
      omega)
  have hs1 : ∑ i, (binomialRandom (Fin n) p (A i)).toReal = (𝒯.card : ℝ) * (p : ℝ) ^ 3 := by
    rw [Finset.sum_congr rfl (fun i _ => by rw [hprob i]), Finset.sum_const, Finset.card_univ,
      Fintype.card_coe, nsmul_eq_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
      unitInterval.coe_toNNReal]
  have hs2 : ∑ q ∈ D, (binomialRandom (Fin n) p (A q.1 ∩ A q.2)).toReal
      = (D.card : ℝ) * (p : ℝ) ^ 5 := by
    rw [Finset.sum_congr rfl (fun q hq => by rw [hprob5 q hq]), Finset.sum_const, nsmul_eq_mul,
      ENNReal.toReal_pow, ENNReal.coe_toReal, unitInterval.coe_toNNReal]
  have key := variance_sum_indicator_le (μ := binomialRandom (Fin n) p) A hmeas D hD
  rw [hX]
  refine key.trans ?_
  rw [hs1, hs2]
  have hT : (𝒯.card : ℝ) ≤ (n : ℝ) ^ 3 := by
    rw [h𝒯, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast Nat.choose_le_pow n 3
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
      -- Either triangle is the shared pair `{a, b}` together with its one private vertex.
      have hsplit : ∀ S T : Finset (Fin n), S.card = 3 → S ∩ T = {a, b} → ∃ z, S = {z, a, b} := by
        intro S T hS hST
        have h := Finset.card_sdiff_add_card_inter S T
        rw [hS, hST, Finset.card_pair hab] at h
        obtain ⟨z, hz⟩ := Finset.card_eq_one.1 (show (S \ T).card = 1 by omega)
        exact ⟨z, by rw [← Finset.sdiff_union_inter S T, hz, hST]; rfl⟩
      obtain ⟨x, e1⟩ := hsplit q.1.1 q.2.1 (hcard3' q.1) hinter
      obtain ⟨y, e2⟩ := hsplit q.2.1 q.1.1 (hcard3' q.2) (by rw [Finset.inter_comm]; exact hinter)
      exact ⟨(a, b, x, y), Finset.mem_coe.2 (Finset.mem_univ _), Prod.ext e1.symm e2.symm⟩
    calc D.card = (D.image (fun q : {T // T ∈ 𝒯} × {T // T ∈ 𝒯} => (q.1.1, q.2.1))).card :=
          (Finset.card_image_of_injective _ hinjimg).symm
      _ ≤ (univ : Finset (Fin n × Fin n × Fin n × Fin n)).card :=
          Finset.card_le_card_of_surjOn _ hsurj
      _ = n ^ 4 := by
          rw [Finset.card_univ, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod,
            Fintype.card_fin]
          ring
  have hDc : (D.card : ℝ) ≤ (n : ℝ) ^ 4 := by exact_mod_cast hDnat
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := p.2.1
  exact add_le_add (mul_le_mul_of_nonneg_right hT (pow_nonneg hp0 3))
    (mul_le_mul_of_nonneg_right hDc (pow_nonneg hp0 5))


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
  exact memLp_sum_indicator_one fun T _ => measurableSet_setOf_forall_adj T

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

/-! ### §4.4: the clique number of a random graph -/

/-- **The union bound on cliques** (Zhao, §4.4): `G(n, p)` contains a `k`-clique with probability
at most `binom(n,k) p^{binom(k,2)}`.

One term per `k`-subset, each contributing the probability that all `binom(k,2)` pairs inside it
are edges — `binomialRandom_setOf_subset_edgeSet`.  No second moment, no independence beyond the
coordinates themselves.

This is the first-moment half of §4.4: when `binom(n,k) p^{binom(k,2)} → 0` the clique number is
below `k` with high probability, which for `p = 1/2` is the upper bound
`ω(G(n,1/2)) ≤ (2 + o(1)) log₂ n`.  The matching lower bound needs the second moment and is a
separate node.  §8.3 uses the same bound in its exponential form. -/
theorem prob_not_cliqueFree_le (n k : ℕ) (p : I) :
    (binomialRandom (Fin n) p).real {G : SimpleGraph (Fin n) | ¬ G.CliqueFree k}
      ≤ (n.choose k : ℝ) * (p : ℝ) ^ k.choose 2 := by
  -- A `k`-subset spans `binom(k,2)` pairs of distinct vertices.
  have hcard : ∀ S ∈ (univ : Finset (Fin n)).powersetCard k,
      (offDiagPairs S).card = k.choose 2 := by
    intro S hS
    have h := card_offDiagPairs_add S
    rw [(Finset.mem_powersetCard.1 hS).2, Nat.choose_succ_succ', Nat.choose_one_right] at h
    simp only [Nat.reduceAdd] at h
    omega
  -- A graph with a `k`-clique lies in the event indexed by that clique's vertex set.
  have hsub : {G : SimpleGraph (Fin n) | ¬ G.CliqueFree k}
      ⊆ ⋃ S ∈ (univ : Finset (Fin n)).powersetCard k,
          {G : SimpleGraph (Fin n) | ↑(offDiagPairs S) ⊆ G.edgeSet} := by
    intro G hG
    obtain ⟨S, hS⟩ : ∃ S, G.IsNClique k S := by
      by_contra h
      exact hG fun t ht => h ⟨t, ht⟩
    refine Set.mem_iUnion₂.2 ⟨S, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hS.2⟩, ?_⟩
    rw [← setOf_forall_adj_eq_setOf_offDiagPairs]
    exact fun a ha b hb hab => hS.1 ha hb hab
  calc (binomialRandom (Fin n) p).real {G : SimpleGraph (Fin n) | ¬ G.CliqueFree k}
      ≤ (binomialRandom (Fin n) p).real (⋃ S ∈ (univ : Finset (Fin n)).powersetCard k,
          {G : SimpleGraph (Fin n) | ↑(offDiagPairs S) ⊆ G.edgeSet}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ S ∈ (univ : Finset (Fin n)).powersetCard k, (binomialRandom (Fin n) p).real
          {G : SimpleGraph (Fin n) | ↑(offDiagPairs S) ⊆ G.edgeSet} :=
        measureReal_biUnion_finset_le _ _
    _ = (n.choose k : ℝ) * (p : ℝ) ^ k.choose 2 := by
        rw [Finset.sum_congr rfl fun S hS => ?_, Finset.sum_const, nsmul_eq_mul,
          Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
        rw [Measure.real, binomialRandom_setOf_subset_edgeSet p _
          fun _ he => not_isDiag_of_mem_offDiagPairs he, hcard S hS, ENNReal.toReal_pow,
          ENNReal.coe_toReal, unitInterval.coe_toNNReal]

end ProbMethodCombinatorics
