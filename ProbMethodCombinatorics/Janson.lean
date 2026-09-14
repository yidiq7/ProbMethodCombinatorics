import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Chapter 8: Janson Inequalities

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Chapter 8.

Janson's inequalities bound the probability that a random subset contains **none** of a
prescribed family of sets, and more generally the lower tail of the count.  Where the second
moment method (Chapter 4) gives polynomial decay, these give exponential decay.

Setup 8.1.1 throughout: `R` is a random subset of `ι`, each element kept independently with
probability `p` — Mathlib's `setBernoulli` — and `A i` is the event `S i ⊆ R`.  The dependency
set `D` is a parameter rather than something computed from `S`, exactly as in
`variance_sum_indicator_le`: any `D` containing every dependent ordered pair is admissible, and
a larger `D` only weakens the bound.

Nothing in this chapter is in Mathlib.
-/

namespace ProbMethodCombinatorics

open MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

variable {ι κ : Type*} [Fintype κ]

/-- The expected number of the sets `S i` contained in the random subset: `μ` of Setup 8.1.1. -/
noncomputable def jansonMu (p : I) (S : κ → Set ι) : ℝ :=
  ∑ i, (setBernoulli Set.univ p {R : Set ι | S i ⊆ R}).toReal

/-- The dependency sum `Δ` of Setup 8.1.1, taken over the ordered pairs listed in `D`. -/
noncomputable def jansonDelta (p : I) (S : κ → Set ι) (D : Finset (κ × κ)) : ℝ :=
  ∑ q ∈ D, (setBernoulli Set.univ p {R : Set ι | S q.1 ∪ S q.2 ⊆ R}).toReal

/-- The number of the sets `S i` contained in `R`: the random variable `X` of Setup 8.1.1.

`Set.ncard` rather than `Finset.filter`, because set inclusion on `Set ι` is not decidable and
the project does not introduce `Decidable` instances. -/
noncomputable def jansonCount (S : κ → Set ι) (R : Set ι) : ℝ :=
  ({i | S i ⊆ R} : Set κ).ncard

/-- **Janson's inequality I** (Zhao, Theorem 8.1.2): the probability that the random subset
contains none of the `S i` is at most `exp (-μ + Δ/2)`.

Most useful when `Δ = o(μ)`; Harris' inequality (Chapter 7) gives the matching lower bound
`exp (-(1 + o(1)) μ)` in that regime, so the two together pin the probability down. -/
theorem janson_prob_none_le (p : I) (S : κ → Set ι) (D : Finset (κ × κ))
    (hD : ∀ i j, i ≠ j → (i, j) ∉ D → Disjoint (S i) (S j)) :
    (setBernoulli Set.univ p {R : Set ι | ∀ i, ¬ S i ⊆ R}).toReal
      ≤ Real.exp (-jansonMu p S + jansonDelta p S D / 2) := by
  sorry

/-- The binomial weight of the subsets of `s` containing a fixed `K` sums to `q ^ #K`. -/
private theorem sum_powerset_weight_eq {α : Type*} [DecidableEq α] (q : ℝ) (s K : Finset α)
    (hK : K ⊆ s) :
    ∑ T ∈ s.powerset, (if K ⊆ T then q ^ T.card * (1 - q) ^ (s \ T).card else 0)
      = q ^ K.card := by
  have h := Finset.prod_add (fun _ : α => q) (fun i => if i ∈ K then (0 : ℝ) else 1 - q) s
  have hL : ∏ i ∈ s, ((fun _ : α => q) i + (fun i => if i ∈ K then (0 : ℝ) else 1 - q) i)
      = q ^ K.card := by
    rw [Finset.prod_congr rfl (g := fun i => if i ∈ K then q else 1) (fun i _ => by
      by_cases hi : i ∈ K <;> simp [hi])]
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.2 hK, Finset.prod_const]
  have hR : ∀ T ∈ s.powerset,
      (∏ i ∈ T, (fun _ : α => q) i) * ∏ i ∈ s \ T, (fun i => if i ∈ K then (0 : ℝ) else 1 - q) i
        = if K ⊆ T then q ^ T.card * (1 - q) ^ (s \ T).card else 0 := by
    intro T hT
    simp only [Finset.mem_powerset] at hT
    by_cases hKT : K ⊆ T
    · simp only [hKT, if_true]
      congr 1
      · exact Finset.prod_const _
      · rw [Finset.prod_congr rfl (g := fun _ => (1 - q : ℝ)) (fun i hi => by
          have : i ∉ K := fun hiK => (Finset.mem_sdiff.1 hi).2 (hKT hiK)
          simp [this]), Finset.prod_const]
    · simp only [hKT, if_false]
      obtain ⟨i, hiK, hiT⟩ : ∃ i ∈ K, i ∉ T := by
        by_contra hc
        exact hKT (fun i hi => by by_contra h2; exact hc ⟨i, hi, h2⟩)
      rw [Finset.prod_eq_zero (i := i) (Finset.mem_sdiff.2 ⟨hK hiK, hiT⟩) (by simp [hiK]), mul_zero]
  rw [← Finset.sum_congr rfl hR, ← h, hL]

/-- Averaging a family of sums against the binomial weights: an index `z` survives exactly when
the whole of `K z` is sampled, which happens with weight `q ^ #(K z)`. -/
private theorem sum_powerset_weight_mul {α β : Type*} [DecidableEq α] [Fintype α]
    (q : ℝ) (B : Finset β) (K : β → Finset α) (c : β → ℝ) :
    ∑ T ∈ (Finset.univ : Finset α).powerset, (q ^ T.card * (1 - q) ^ (Finset.univ \ T).card) *
        (∑ z ∈ B.filter (fun z => K z ⊆ T), c z)
      = ∑ z ∈ B, c z * q ^ (K z).card := by
  have h1 : ∀ T ∈ (Finset.univ : Finset α).powerset,
      (q ^ T.card * (1 - q) ^ (Finset.univ \ T).card) * (∑ z ∈ B.filter (fun z => K z ⊆ T), c z)
        = ∑ z ∈ B,
            (if K z ⊆ T then q ^ T.card * (1 - q) ^ (Finset.univ \ T).card else 0) * c z := by
    intro T _
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    by_cases h : K z ⊆ T <;> simp [h]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [← Finset.sum_mul, sum_powerset_weight_eq q Finset.univ (K z) (Finset.subset_univ _),
    mul_comm]

omit [Fintype κ] in
/-- Janson's first inequality applied to the sub-family indexed by a `Finset T`: the events
outside `T` are simply dropped, which can only increase the probability of containing none. -/
private theorem prob_none_le_subfamily [DecidableEq κ] (p : I) (S : κ → Set ι)
    (E : Finset (κ × κ)) (hE : ∀ i j, i ≠ j → (i, j) ∉ E → Disjoint (S i) (S j))
    (T : Finset κ) :
    (setBernoulli Set.univ p {R : Set ι | ∀ i, ¬ S i ⊆ R}).toReal
      ≤ Real.exp (-(∑ i ∈ T, (setBernoulli Set.univ p {R : Set ι | S i ⊆ R}).toReal)
        + (∑ z ∈ E.filter (fun z : κ × κ => z.1 ∈ T ∧ z.2 ∈ T),
            (setBernoulli Set.univ p {R : Set ι | S z.1 ∪ S z.2 ⊆ R}).toReal) / 2) := by
  have hfinj : Function.Injective
      (fun z : {x // x ∈ T} × {x // x ∈ T} => ((z.1 : κ), (z.2 : κ))) := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h ⊢
    exact h
  have hErestr : ∀ i j : {x // x ∈ T}, i ≠ j →
      (i, j) ∉ (E.filter (fun z : κ × κ => z.1 ∈ T ∧ z.2 ∈ T)).preimage
        (fun z : {x // x ∈ T} × {x // x ∈ T} => ((z.1 : κ), (z.2 : κ))) hfinj.injOn →
      Disjoint (S i.1) (S j.1) := by
    intro i j hij hnot
    have hne : (i : κ) ≠ (j : κ) := fun h => hij (Subtype.ext h)
    refine hE _ _ hne (fun hmem => hnot ?_)
    exact Finset.mem_preimage.2 (Finset.mem_filter.2 ⟨hmem, i.2, j.2⟩)
  have h2 := janson_prob_none_le p (fun i : {x // x ∈ T} => S i.1) _ hErestr
  have hmu : jansonMu p (fun i : {x // x ∈ T} => S i.1)
      = ∑ i ∈ T, (setBernoulli Set.univ p {R : Set ι | S i ⊆ R}).toReal :=
    Finset.sum_coe_sort T
      (fun i : κ => (setBernoulli Set.univ p {R : Set ι | S i ⊆ R}).toReal)
  have hdel : jansonDelta p (fun i : {x // x ∈ T} => S i.1)
      ((E.filter (fun z : κ × κ => z.1 ∈ T ∧ z.2 ∈ T)).preimage
        (fun z : {x // x ∈ T} × {x // x ∈ T} => ((z.1 : κ), (z.2 : κ))) hfinj.injOn)
      = ∑ z ∈ E.filter (fun z : κ × κ => z.1 ∈ T ∧ z.2 ∈ T),
          (setBernoulli Set.univ p {R : Set ι | S z.1 ∪ S z.2 ⊆ R}).toReal := by
    rw [jansonDelta]
    refine Finset.sum_preimage _ _ _
      (fun z : κ × κ => (setBernoulli Set.univ p {R : Set ι | S z.1 ∪ S z.2 ⊆ R}).toReal) ?_
    intro x hx hxr
    exact absurd
      ⟨(⟨x.1, (Finset.mem_filter.1 hx).2.1⟩, ⟨x.2, (Finset.mem_filter.1 hx).2.2⟩), rfl⟩ hxr
  rw [hmu, hdel] at h2
  refine le_trans ?_ h2
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun R hR i => hR i.1))


/-- **Janson's inequality II** (Zhao, Theorem 8.1.8): in the regime `Δ ≥ μ`, where the first
inequality says nothing, the probability of containing none of the `S i` is at most
`exp (-μ² / (2Δ))`.

Proved from the first inequality by applying it to a random subsample of the events. -/
theorem janson_prob_none_le_of_mu_le (p : I) (S : κ → Set ι) (D : Finset (κ × κ))
    (hD : ∀ i j, i ≠ j → (i, j) ∉ D → Disjoint (S i) (S j))
    (hΔ : jansonMu p S ≤ jansonDelta p S D) (hΔ0 : 0 < jansonDelta p S D) :
    (setBernoulli Set.univ p {R : Set ι | ∀ i, ¬ S i ⊆ R}).toReal
      ≤ Real.exp (-(jansonMu p S) ^ 2 / (2 * jansonDelta p S D)) := by
  sorry

/-- **Janson's inequality III** (Zhao, Theorem 8.2.2): the lower tail of the count.  For
`0 ≤ t ≤ μ`,

    ℙ(X ≤ μ - t) ≤ exp (-t² / (2(μ + Δ))).

Taking `t = μ` recovers the first two inequalities up to a constant in the exponent, so this is
the strongest of the three.  There is deliberately no companion for the *upper* tail: Example
8.2.4 shows the analogous bound is false, since planting a clique forces an excess of triangles
at far higher probability than any such bound would allow. -/
theorem janson_lower_tail (p : I) (S : κ → Set ι) (D : Finset (κ × κ))
    (hD : ∀ i j, i ≠ j → (i, j) ∉ D → Disjoint (S i) (S j))
    {t : ℝ} (ht0 : 0 ≤ t) (htμ : t ≤ jansonMu p S) :
    (setBernoulli Set.univ p
        {R : Set ι | jansonCount S R ≤ jansonMu p S - t}).toReal
      ≤ Real.exp (-t ^ 2 / (2 * (jansonMu p S + jansonDelta p S D))) := by
  sorry

end ProbMethodCombinatorics
