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
  sorry

end ProbMethodCombinatorics
