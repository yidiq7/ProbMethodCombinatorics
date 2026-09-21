import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Section 9.4: the two formulations of concentration of measure

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Theorem 9.4.8.

Concentration of measure is stated two ways, and they say the same thing.  The *geometric*
form asks that the `t`-neighbourhood of any set of probability at least `1/2` carry almost all
the mass; the *functional* form asks that any `1`-Lipschitz function exceed its median by more
than `t` only rarely.  Each direction is one substitution: `A ↦ {f ≤ m}` going one way, and
`f ↦ Metric.infDist · A` with median `0` going the other.

The rest of §9.4 rests on inputs the source quotes rather than proves — Harper's
vertex-isoperimetric inequality, Lévy's isoperimetric inequality on the sphere, and Gaussian
isoperimetry — and so is not formalized here.  This theorem quotes nothing, which is why it is
stated while its neighbours are not.
-/

namespace ProbMethodCombinatorics

open MeasureTheory Metric

/-- **Theorem 9.4.8.**  The geometric and functional formulations of concentration of measure
are equivalent.  On the left: every measurable `A` carrying at least half the mass has its
`t`-neighbourhood carrying all but `ε`.  On the right: every `1`-Lipschitz `f` with median at
most `m` exceeds `m + t` with probability at most `ε`.

Both `t` and `ε` are fixed throughout; the equivalence is for each pair separately, not after
quantifying over them. -/
theorem measure_infDist_le_iff_measure_lt_le {Ω : Type*} [MetricSpace Ω] [MeasurableSpace Ω]
    [BorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {t ε : ℝ} (ht : 0 ≤ t)
    (hε : 0 ≤ ε) :
    (∀ A : Set Ω, MeasurableSet A → 1 / 2 ≤ μ.real A →
        1 - ε ≤ μ.real {x | infDist x A ≤ t})
      ↔ (∀ f : Ω → ℝ, LipschitzWith 1 f → ∀ m : ℝ, 1 / 2 ≤ μ.real {x | f x ≤ m} →
        μ.real {x | m + t < f x} ≤ ε) := by
  -- The `μ.real` API lives downstream of this file's imports, so the two facts we need about it
  -- are derived here from the `ENNReal`-valued measure.
  have hmono : ∀ s u : Set Ω, s ⊆ u → μ.real s ≤ μ.real u := fun s u hsu =>
    ENNReal.toReal_mono (measure_ne_top μ u) (measure_mono hsu)
  have hcompl : ∀ s : Set Ω, MeasurableSet s → μ.real sᶜ = 1 - μ.real s := by
    intro s hs
    simp only [Measure.real, prob_compl_eq_one_sub hs,
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
  constructor
  · intro h f hf m hm
    have hAmeas : MeasurableSet {x : Ω | f x ≤ m} :=
      (isClosed_le hf.continuous continuous_const).measurableSet
    -- A set of measure at least `1 / 2` is nonempty.  Without this the inclusion below fails:
    -- `infDist x ∅ = 0`, so the `t`-neighbourhood of `∅` is all of `Ω`.
    have hAne : {x : Ω | f x ≤ m}.Nonempty := by
      rcases Set.eq_empty_or_nonempty {x : Ω | f x ≤ m} with hempty | hne
      · rw [hempty] at hm
        have hzero : μ.real (∅ : Set Ω) = 0 := by simp [Measure.real]
        rw [hzero] at hm
        linarith
      · exact hne
    have hgeo := h {x : Ω | f x ≤ m} hAmeas hm
    have hNmeas : MeasurableSet {x : Ω | infDist x {y : Ω | f y ≤ m} ≤ t} :=
      (isClosed_le (continuous_infDist_pt _) continuous_const).measurableSet
    have hsub : ∀ x : Ω, infDist x {y : Ω | f y ≤ m} ≤ t → f x ≤ m + t := by
      intro x hx
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      obtain ⟨a, haA, hax⟩ :=
        (infDist_lt_iff hAne).mp (lt_of_le_of_lt hx (by linarith : t < t + δ))
      have ham : f a ≤ m := haA
      have hlip : |f x - f a| ≤ dist x a := by
        have hd := hf.dist_le_mul x a
        rwa [Real.dist_eq, NNReal.coe_one, one_mul] at hd
      have hgap : f x - f a ≤ dist x a := (le_abs_self _).trans hlip
      linarith
    have hout : {x : Ω | m + t < f x} ⊆ {x : Ω | infDist x {y : Ω | f y ≤ m} ≤ t}ᶜ := by
      intro x hx
      exact fun hmem => absurd (hsub x hmem) (not_le.mpr hx)
    have hle := hmono _ _ hout
    rw [hcompl _ hNmeas] at hle
    linarith
  · intro h A hA hhalf
    have hmed : 1 / 2 ≤ μ.real {x : Ω | infDist x A ≤ 0} :=
      hhalf.trans (hmono _ _ fun x hx => le_of_eq (infDist_zero_of_mem hx))
    have hkey := h (infDist · A) (lipschitz_infDist_pt A) 0 hmed
    have hNmeas : MeasurableSet {x : Ω | infDist x A ≤ t} :=
      (isClosed_le (continuous_infDist_pt A) continuous_const).measurableSet
    have heq : {x : Ω | 0 + t < infDist x A} = {x : Ω | infDist x A ≤ t}ᶜ := by
      ext x
      simp [not_le]
    rw [heq, hcompl _ hNmeas] at hkey
    linarith

end ProbMethodCombinatorics
