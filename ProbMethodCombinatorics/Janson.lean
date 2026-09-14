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

**`[Countable ι]` is load-bearing on every theorem below, and is not boilerplate.**  The
measurable space on `Set ι` is the product σ-algebra, in which a set is measurable only if it
depends on countably many coordinates.  For uncountable `S i` the event `{R | S i ⊆ R}` is
therefore not measurable and `setBernoulli` silently returns an *outer* measure.  At `p = 1`
that breaks the inequality outright: with `ι` uncountable, `κ = Unit` and `S 0 = univ`, the
event `{R | R ≠ univ}` has no measurable superset excluding `univ` — a measurable set depends on
countably many coordinates `J`, so containing any `R ≠ univ` forces it to contain `univ` — hence
its outer measure is `1`, while `μ = 1` and `Δ = 0` put the bound at `exp (-1)`.  Mathlib's own
`SetBernoulli` API draws the same line: everything substantive in `SetBernoulli.lean` lives
inside `section Countable`.  Under `[Countable ι]` every event here is a countable intersection
of cylinders and the arguments are sound.  For `p < 1` the uncountable case is merely null
rather than wrong, but the hypothesis is the honest fix.
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

/-- Containing a fixed set is an increasing property of the random subset: `{R | s ⊆ R}` is an
upper set of `Set ι`.  This is what makes Harris' inequality (Chapter 7) applicable to the events
`A i` of Setup 8.1.1. -/
theorem isUpperSet_setOf_subset (s : Set ι) : IsUpperSet {R : Set ι | s ⊆ R} :=
  fun _ _ hle hmem => hmem.trans hle

/-- The conditioning step of the Boppana–Spencer proof of Janson's inequality.

If `i ∉ T` and every `S j` with `j ∈ T` outside `T₁` is disjoint from `S i`, then imposing the
extra event `¬ S i ⊆ R` costs a factor of at most
`1 - ℙ(S i ⊆ R) + ∑_{j ∈ T₁} ℙ(S i ∪ S j ⊆ R)`.

Equivalently, writing `A j` for the event `S j ⊆ R`,

    ℙ(A i ∣ ⋂_{j ∈ T} (A j)ᶜ) ≥ ℙ(A i) - ∑_{j ∈ T₁} ℙ(A i ∩ A j).

The indices of `T` outside `T₁` contribute nothing, `A i` being independent of them; the indices
in `T₁` are handled by Harris' inequality, since `A i ∩ A j` is increasing while
`⋂_{j ∈ T \ T₁} (A j)ᶜ` is decreasing. -/
theorem janson_prob_none_step_le [Countable ι] (p : I) (S : κ → Set ι) (i : κ) (T T₁ : Finset κ)
    (hiT : i ∉ T) (hsub : T₁ ⊆ T) (hindep : ∀ j ∈ T, j ∉ T₁ → Disjoint (S i) (S j)) :
    (setBernoulli Set.univ p {R : Set ι | ¬ S i ⊆ R ∧ ∀ j ∈ T, ¬ S j ⊆ R}).toReal
      ≤ (1 - (setBernoulli Set.univ p {R : Set ι | S i ⊆ R}).toReal
            + ∑ j ∈ T₁, (setBernoulli Set.univ p {R : Set ι | S i ∪ S j ⊆ R}).toReal)
        * (setBernoulli Set.univ p {R : Set ι | ∀ j ∈ T, ¬ S j ⊆ R}).toReal := by
  sorry

/-- **Janson's inequality I** (Zhao, Theorem 8.1.2): the probability that the random subset
contains none of the `S i` is at most `exp (-μ + Δ/2)`.

Most useful when `Δ = o(μ)`; Harris' inequality (Chapter 7) gives the matching lower bound
`exp (-(1 + o(1)) μ)` in that regime, so the two together pin the probability down. -/
theorem janson_prob_none_le [Countable ι] (p : I) (S : κ → Set ι) (D : Finset (κ × κ))
    (hD : ∀ i j, i ≠ j → (i, j) ∉ D → Disjoint (S i) (S j)) :
    (setBernoulli Set.univ p {R : Set ι | ∀ i, ¬ S i ⊆ R}).toReal
      ≤ Real.exp (-jansonMu p S + jansonDelta p S D / 2) := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : κ → ℝ,
      ∀ i, a i = (setBernoulli Set.univ p {R : Set ι | S i ⊆ R}).toReal := ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : κ → κ → ℝ,
      ∀ i j, b i j = (setBernoulli Set.univ p {R : Set ι | S i ∪ S j ⊆ R}).toReal :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Finset κ → ℝ, ∀ T : Finset κ,
      P T = (setBernoulli Set.univ p {R : Set ι | ∀ j ∈ T, ¬ S j ⊆ R}).toReal :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : Finset κ → ℝ, ∀ T : Finset κ,
      E T = ∑ q ∈ D.filter fun q => q.1 ∈ T ∧ q.2 ∈ T, b q.1 q.2 := ⟨_, fun _ => rfl⟩
  have hb0 : ∀ i j, 0 ≤ b i j := by intro i j; rw [hb]; exact ENNReal.toReal_nonneg
  have hbs : ∀ i j, b j i = b i j := by intro i j; rw [hb, hb, Set.union_comm]
  have hP0 : ∀ T, 0 ≤ P T := by intro T; rw [hP]; exact ENNReal.toReal_nonneg
  have key : ∀ T : Finset κ, P T ≤ Real.exp (-∑ j ∈ T, a j + E T / 2) := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · have h1 : {R : Set ι | ∀ j ∈ (∅ : Finset κ), ¬ S j ⊆ R} = Set.univ := by simp
      rw [hP, h1, hE]
      simp
    · intro i T hiT ih
      have hsub : T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D) ⊆ T := Finset.filter_subset _ _
      have hindep : ∀ j ∈ T, j ∉ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D) →
          Disjoint (S i) (S j) := by
        intro j hj hjn
        have hij : i ≠ j := by rintro rfl; exact hiT hj
        have hnot : ¬ ((i, j) ∈ D ∧ (j, i) ∈ D) := fun h => hjn (Finset.mem_filter.2 ⟨hj, h⟩)
        rcases not_and_or.1 hnot with h | h
        · exact hD i j hij h
        · exact (hD j i hij.symm h).symm
      have hstep := janson_prob_none_step_le p S i T
        (T.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D) hiT hsub hindep
      have hins : {R : Set ι | ∀ j ∈ insert i T, ¬ S j ⊆ R}
          = {R : Set ι | ¬ S i ⊆ R ∧ ∀ j ∈ T, ¬ S j ⊆ R} := by
        ext R; simp
      have hsum : ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j
          = ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D),
              (setBernoulli Set.univ p {R : Set ι | S i ∪ S j ⊆ R}).toReal :=
        Finset.sum_congr rfl fun j _ => hb i j
      have hPins : P (insert i T)
          ≤ (1 - a i + ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j) * P T := by
        rw [hP, hins, hP, ha, hsum]
        exact hstep
      have hEineq : E T + 2 * ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j
          ≤ E (insert i T) := by
        have hU : ∑ q ∈ (T.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image
              (fun j => ((i, j) : κ × κ)), b q.1 q.2
            = ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j :=
          Finset.sum_image (fun x _ y _ h => by simpa using h)
        have hV : ∑ q ∈ (T.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image
              (fun j => ((j, i) : κ × κ)), b q.1 q.2
            = ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j := by
          rw [Finset.sum_image (fun x _ y _ h => by simpa using h)]
          exact Finset.sum_congr rfl fun j _ => hbs i j
        have hd1 : Disjoint (D.filter fun q => q.1 ∈ T ∧ q.2 ∈ T)
            ((T.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image fun j => ((i, j) : κ × κ)) := by
          refine Finset.disjoint_left.2 ?_
          rintro q hq hq'
          obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq'
          exact hiT (Finset.mem_filter.1 hq).2.1
        have hd2 : Disjoint ((D.filter fun q => q.1 ∈ T ∧ q.2 ∈ T) ∪
              (T.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image fun j => ((i, j) : κ × κ))
            ((T.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image fun j => ((j, i) : κ × κ)) := by
          refine Finset.disjoint_left.2 ?_
          rintro q hq hq'
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hq'
          rcases Finset.mem_union.1 hq with h | h
          · exact hiT (Finset.mem_filter.1 h).2.2
          · obtain ⟨k, hk, hk'⟩ := Finset.mem_image.1 h
            have : k = i := congrArg Prod.snd hk'
            exact hiT (this ▸ (Finset.mem_filter.1 hk).1)
        have hss : (D.filter fun q => q.1 ∈ T ∧ q.2 ∈ T) ∪
              ((T.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image fun j => ((i, j) : κ × κ)) ∪
              ((T.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image fun j => ((j, i) : κ × κ))
            ⊆ D.filter fun q => q.1 ∈ insert i T ∧ q.2 ∈ insert i T := by
          intro q hq
          rcases Finset.mem_union.1 hq with hq | hq
          · rcases Finset.mem_union.1 hq with hq | hq
            · obtain ⟨hqD, h1, h2⟩ := Finset.mem_filter.1 hq
              exact Finset.mem_filter.2
                ⟨hqD, Finset.mem_insert_of_mem h1, Finset.mem_insert_of_mem h2⟩
            · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hq
              obtain ⟨hjT, hjD, -⟩ := Finset.mem_filter.1 hj
              exact Finset.mem_filter.2
                ⟨hjD, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hjT⟩
          · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hq
            obtain ⟨hjT, -, hjD⟩ := Finset.mem_filter.1 hj
            exact Finset.mem_filter.2
              ⟨hjD, Finset.mem_insert_of_mem hjT, Finset.mem_insert_self _ _⟩
        calc E T + 2 * ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j
            = ∑ q ∈ (D.filter fun q => q.1 ∈ T ∧ q.2 ∈ T) ∪
                ((T.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image fun j => ((i, j) : κ × κ)) ∪
                ((T.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image fun j => ((j, i) : κ × κ)),
                b q.1 q.2 := by
              rw [Finset.sum_union hd2, Finset.sum_union hd1, hU, hV, hE]; ring
          _ ≤ ∑ q ∈ D.filter (fun q => q.1 ∈ insert i T ∧ q.2 ∈ insert i T), b q.1 q.2 :=
              Finset.sum_le_sum_of_subset_of_nonneg hss fun q _ _ => hb0 _ _
          _ = E (insert i T) := (hE _).symm
      calc P (insert i T)
          ≤ (1 - a i + ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j) * P T := hPins
        _ ≤ Real.exp (-(a i - ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j))
              * P T := by
            refine mul_le_mul_of_nonneg_right ?_ (hP0 T)
            have := Real.add_one_le_exp
              (-(a i - ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j))
            linarith
        _ ≤ Real.exp (-(a i - ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j))
              * Real.exp (-∑ j ∈ T, a j + E T / 2) :=
            mul_le_mul_of_nonneg_left ih (Real.exp_nonneg _)
        _ = Real.exp (-(a i - ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j)
              + (-∑ j ∈ T, a j + E T / 2)) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (-∑ j ∈ insert i T, a j + E (insert i T) / 2) := by
            rw [Finset.sum_insert hiT]
            exact Real.exp_le_exp.2 (by linarith)
  have huniv := key Finset.univ
  have h1 : {R : Set ι | ∀ j ∈ (Finset.univ : Finset κ), ¬ S j ⊆ R}
      = {R : Set ι | ∀ i, ¬ S i ⊆ R} := by simp
  have h2 : ∑ j ∈ (Finset.univ : Finset κ), a j = jansonMu p S :=
    Finset.sum_congr rfl fun j _ => ha j
  have h3 : E (Finset.univ : Finset κ) = jansonDelta p S D := by
    rw [hE, Finset.filter_true_of_mem (fun q _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩)]
    exact Finset.sum_congr rfl fun q _ => hb q.1 q.2
  rw [hP, h1, h2, h3] at huniv
  exact huniv

/-- **Janson's inequality II** (Zhao, Theorem 8.1.8): in the regime `Δ ≥ μ`, where the first
inequality says nothing, the probability of containing none of the `S i` is at most
`exp (-μ² / (2Δ))`.

Proved from the first inequality by applying it to a random subsample of the events. -/
theorem janson_prob_none_le_of_mu_le [Countable ι] (p : I) (S : κ → Set ι) (D : Finset (κ × κ))
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
theorem janson_lower_tail [Countable ι] (p : I) (S : κ → Set ι) (D : Finset (κ × κ))
    (hD : ∀ i j, i ≠ j → (i, j) ∉ D → Disjoint (S i) (S j))
    {t : ℝ} (ht0 : 0 ≤ t) (htμ : t ≤ jansonMu p S) :
    (setBernoulli Set.univ p
        {R : Set ι | jansonCount S R ≤ jansonMu p S - t}).toReal
      ≤ Real.exp (-t ^ 2 / (2 * (jansonMu p S + jansonDelta p S D))) := by
  sorry

end ProbMethodCombinatorics
