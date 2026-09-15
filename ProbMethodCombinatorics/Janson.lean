import ProbMethodCombinatorics.Correlation
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
  classical
  simp only [← measureReal_def]
  set μ : Measure (Set ι) := setBernoulli Set.univ p with hμdef
  have hμprob : IsProbabilityMeasure μ := by rw [hμdef]; infer_instance
  have hmeasSub : ∀ s : Set ι, MeasurableSet {R : Set ι | s ⊆ R} := fun s =>
    measurableSet_setOfPred.2 (Measurable.subset measurable_const measurable_id)
  -- `U` indexes the sets disjoint from `S i`, and `v` is the block of coordinates they occupy.
  set U : Set κ := {j | j ∈ T ∧ j ∉ T₁}
  set v : Set ι := ⋃ j ∈ U, S j
  set Ai : Set (Set ι) := {R : Set ι | S i ⊆ R} with hAidef
  set B : Set (Set ι) := {R : Set ι | ∀ j ∈ T, ¬ S j ⊆ R} with hBdef
  set B₀ : Set (Set ι) := {R : Set ι | ∀ j ∈ U, ¬ S j ⊆ R} with hB₀def
  -- `B₀` is a measurable decreasing event containing `B`.
  have hB₀m : MeasurableSet B₀ := by
    have h : B₀ = ⋂ j ∈ U, {R : Set ι | S j ⊆ R}ᶜ := by rw [hB₀def]; ext R; simp
    rw [h]
    exact MeasurableSet.biInter (Set.to_countable U) fun j _ => (hmeasSub (S j)).compl
  have hB₀low : IsLowerSet B₀ := by
    rw [hB₀def]
    intro R R' hle hR j hj hsj
    exact hR j hj (hsj.trans hle)
  have hBsub : B ⊆ B₀ := by
    rw [hBdef, hB₀def]
    exact fun R hR j hj => hR j hj.1
  -- Whether `s ⊆ R` holds depends on `R` only through `R ∩ w`, as soon as `s ⊆ w`.
  have hdep : ∀ w s : Set ι, s ⊆ w → ∀ R R' : Set ι, R ∩ w = R' ∩ w → (s ⊆ R ↔ s ⊆ R') := by
    intro w s hsw
    have key : ∀ X Y : Set ι, X ∩ w = Y ∩ w → s ⊆ X → s ⊆ Y := fun X Y h hX x hx =>
      ((Set.ext_iff.1 h x).1 ⟨hX hx, hsw hx⟩).1
    exact fun R R' h => ⟨key R R' h, key R' R h.symm⟩
  have hSv : ∀ j ∈ U, S j ⊆ v := fun j hj x hx => Set.mem_biUnion hj hx
  have hdisj : Disjoint (S i) v := by
    refine Set.disjoint_left.2 fun x hxi hxv => ?_
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 hxv
    exact Set.disjoint_left.1 (hindep j hj.1 hj.2) hxi hxj
  -- `A i` lives on the block `S i` and `B₀` on the disjoint block `v`, so the two are independent.
  have hind : μ.real (Ai ∩ B₀) = μ.real Ai * μ.real B₀ := by
    have hA : ∀ R R' : Set ι, R ∩ S i = R' ∩ S i → (R ∈ Ai ↔ R' ∈ Ai) := fun R R' h =>
      hdep (S i) (S i) Set.Subset.rfl R R' h
    have hB : ∀ R R' : Set ι, R ∩ v = R' ∩ v → (R ∈ B₀ ↔ R' ∈ B₀) := by
      intro R R' h
      rw [hB₀def]
      exact ⟨fun hR j hj hsj => hR j hj ((hdep v (S j) (hSv j hj) R R' h).2 hsj),
        fun hR j hj hsj => hR j hj ((hdep v (S j) (hSv j hj) R R' h).1 hsj)⟩
    rw [measureReal_def, measureReal_def, measureReal_def,
      setBernoulli_inter_eq_mul_of_disjoint p (S i) v hdisj Ai B₀ hA hB (hAidef ▸ hmeasSub (S i))
        hB₀m, ENNReal.toReal_mul]
  -- Harris, for the increasing event `A i ∩ A j` against the decreasing event `B₀`.
  have harris : ∀ j : κ, μ.real ({R : Set ι | S i ∪ S j ⊆ R} ∩ B₀)
      ≤ μ.real {R : Set ι | S i ∪ S j ⊆ R} * μ.real B₀ := by
    intro j
    have h := setBernoulli_inter_le_mul p {R : Set ι | S i ∪ S j ⊆ R} B₀
      (isUpperSet_setOf_subset _) hB₀low (hmeasSub _) hB₀m
    rw [measureReal_def, measureReal_def, measureReal_def, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (by finiteness) h
  -- Dropping from `B₀` to `B` costs at most one of the events `A j` with `j ∈ T₁`.
  have hcover : Ai ∩ B₀ ⊆ (Ai ∩ B) ∪ ⋃ j ∈ T₁, ({R : Set ι | S i ∪ S j ⊆ R} ∩ B₀) := by
    rintro R ⟨hRi, hRB₀⟩
    by_cases hB₁ : ∀ j ∈ T₁, ¬ S j ⊆ R
    · refine Or.inl ⟨hRi, ?_⟩
      rw [hBdef]
      intro j hjT
      by_cases hj1 : j ∈ T₁
      · exact hB₁ j hj1
      · exact hRB₀ j ⟨hjT, hj1⟩
    · refine Or.inr ?_
      obtain ⟨j, hj, hsj⟩ : ∃ j ∈ T₁, S j ⊆ R := by
        by_contra hcon
        exact hB₁ fun j hj hsj => hcon ⟨j, hj, hsj⟩
      exact Set.mem_biUnion hj ⟨Set.union_subset hRi hsj, hRB₀⟩
  have hmain : μ.real Ai * μ.real B₀
      ≤ μ.real (Ai ∩ B)
        + (∑ j ∈ T₁, μ.real {R : Set ι | S i ∪ S j ⊆ R}) * μ.real B₀ := by
    rw [Finset.sum_mul, ← hind]
    calc μ.real (Ai ∩ B₀)
        ≤ μ.real ((Ai ∩ B) ∪ ⋃ j ∈ T₁, ({R : Set ι | S i ∪ S j ⊆ R} ∩ B₀)) :=
          measureReal_mono hcover
      _ ≤ μ.real (Ai ∩ B) + μ.real (⋃ j ∈ T₁, ({R : Set ι | S i ∪ S j ⊆ R} ∩ B₀)) :=
          measureReal_union_le _ _
      _ ≤ μ.real (Ai ∩ B) + ∑ j ∈ T₁, μ.real ({R : Set ι | S i ∪ S j ⊆ R} ∩ B₀) := by
          gcongr
          exact measureReal_biUnion_finset_le _ _
      _ ≤ μ.real (Ai ∩ B) + ∑ j ∈ T₁, μ.real {R : Set ι | S i ∪ S j ⊆ R} * μ.real B₀ := by
          gcongr with j hj
          exact harris j
  have hLHS : {R : Set ι | ¬ S i ⊆ R ∧ ∀ j ∈ T, ¬ S j ⊆ R} = B \ Ai := by
    rw [hBdef, hAidef]
    ext R
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, and_comm]
  have hAim : MeasurableSet Ai := hAidef ▸ hmeasSub (S i)
  have hdecomp : μ.real (B ∩ Ai) + μ.real (B \ Ai) = μ.real B :=
    measureReal_inter_add_sdiff hAim
  have hq : μ.real B ≤ μ.real B₀ := measureReal_mono hBsub
  -- The bracket may be negative, in which case `B ⊆ B₀` is the wrong way round and unnecessary.
  have hkey : (μ.real Ai - ∑ j ∈ T₁, μ.real {R : Set ι | S i ∪ S j ⊆ R}) * μ.real B
      ≤ μ.real (B ∩ Ai) := by
    rw [Set.inter_comm]
    rcases le_or_gt 0 (μ.real Ai - ∑ j ∈ T₁, μ.real {R : Set ι | S i ∪ S j ⊆ R}) with hc | hc
    · calc (μ.real Ai - ∑ j ∈ T₁, μ.real {R : Set ι | S i ∪ S j ⊆ R}) * μ.real B
          ≤ (μ.real Ai - ∑ j ∈ T₁, μ.real {R : Set ι | S i ∪ S j ⊆ R}) * μ.real B₀ :=
            mul_le_mul_of_nonneg_left hq hc
        _ ≤ μ.real (Ai ∩ B) := by linarith [hmain]
    · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hc.le measureReal_nonneg) measureReal_nonneg
  rw [hLHS]
  linarith [hdecomp, hkey]

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

section LowerTail

/-- The elementary bound `exp (-x) ≤ 1 - x + x ^ 2 / 2` for `x ≥ 0`.

It follows from `1 + x + x ^ 2 / 2 ≤ exp x` because
`(1 - x + x ^ 2 / 2) * (1 + x + x ^ 2 / 2) = 1 + x ^ 4 / 4 ≥ 1`. -/
theorem exp_neg_le_one_sub_add_sq_div_two {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have hA : (0 : ℝ) < 1 + x + x ^ 2 / 2 := by nlinarith [sq_nonneg x]
  have hexp : 1 + x + x ^ 2 / 2 ≤ Real.exp x := Real.quadratic_le_exp_of_nonneg hx
  have h1 : Real.exp (-x) * (1 + x + x ^ 2 / 2) ≤ Real.exp (-x) * Real.exp x :=
    mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
  have h2 : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith [sq_nonneg (x ^ 2), h1, h2, hA]

/-- The Chernoff step of Warnke's proof of Janson's third inequality (Zhao, Theorem 8.2.2).

Write `X` for `jansonCount S`, put `q = 1 - exp (-lam)` for `lam ≥ 0`, and thin the events of
Setup 8.1.1 by keeping each index independently with probability `q`.  The thinned family again
satisfies Setup 8.1.1 — over the pairs of `D` off the diagonal, whose contribution to `Δ` is at
most `jansonDelta p S D` — with `μ` replaced by `q * μ` and `Δ` replaced by `q ^ 2 * Δ`, so
Janson's first inequality bounds the probability that the thinned count vanishes by
`exp (-q * μ + q ^ 2 * Δ / 2)`.  That probability is the moment generating function
`𝔼 [exp (-lam * X)]`, and Markov's inequality applied to it gives the bound below. -/
theorem janson_lower_tail_step_le [Countable ι] (p : I) (S : κ → Set ι) (D : Finset (κ × κ))
    (hD : ∀ i j, i ≠ j → (i, j) ∉ D → Disjoint (S i) (S j)) {lam s : ℝ} (hlam : 0 ≤ lam) :
    (setBernoulli Set.univ p {R : Set ι | jansonCount S R ≤ s}).toReal
      ≤ Real.exp (lam * s - (1 - Real.exp (-lam)) * jansonMu p S
          + (1 - Real.exp (-lam)) ^ 2 * jansonDelta p S D / 2) := by
  -- Write `q = 1 - exp (-lam)`, so `1 - q = exp (-lam) > 0`.  The thinning needs no second
  -- measure: `κ` is finite, so a thinned family is a `Finset κ` and the `q`-average over thinnings
  -- is the finite sum `Φ U = ∑ T ⊆ U, q ^ #T * (1 - q) ^ #(U \ T) * P T`, where `P T` is the
  -- probability that the random subset contains none of the `S j` with `j ∈ T`.  `Φ Finset.univ`
  -- is the moment generating function `𝔼 [exp (-lam * X)]`.
  classical
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = 1 - Real.exp (-lam) := ⟨_, rfl⟩
  have hq1 : 1 - q = Real.exp (-lam) := by rw [hqdef]; ring
  have hq1pos : (0 : ℝ) < 1 - q := by rw [hq1]; exact Real.exp_pos _
  have hq0 : (0 : ℝ) ≤ q := by
    have h := Real.exp_le_one_iff.2 (neg_nonpos.2 hlam)
    rw [hqdef]; linarith
  obtain ⟨a, ha⟩ : ∃ a : κ → ℝ,
      ∀ i, a i = (setBernoulli Set.univ p {R : Set ι | S i ⊆ R}).toReal := ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : κ → κ → ℝ,
      ∀ i j, b i j = (setBernoulli Set.univ p {R : Set ι | S i ∪ S j ⊆ R}).toReal :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Finset κ → ℝ, ∀ T : Finset κ,
      P T = (setBernoulli Set.univ p {R : Set ι | ∀ j ∈ T, ¬ S j ⊆ R}).toReal :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : Finset κ → ℝ, ∀ T : Finset κ,
      E T = ∑ z ∈ D.filter fun z => z.1 ∈ T ∧ z.2 ∈ T, b z.1 z.2 := ⟨_, fun _ => rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Finset κ → Finset κ → ℝ,
      ∀ U T : Finset κ, W U T = q ^ T.card * (1 - q) ^ (U \ T).card := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Finset κ → ℝ,
      ∀ U : Finset κ, Φ U = ∑ T ∈ U.powerset, W U T * P T := ⟨_, fun _ => rfl⟩
  have hb0 : ∀ i j, 0 ≤ b i j := fun i j => by rw [hb]; exact ENNReal.toReal_nonneg
  have hbs : ∀ i j, b j i = b i j := fun i j => by rw [hb, hb, Set.union_comm]
  have hP0 : ∀ T, 0 ≤ P T := fun T => by rw [hP]; exact ENNReal.toReal_nonneg
  have hPmono : ∀ T T' : Finset κ, T ⊆ T' → P T' ≤ P T := by
    intro T T' hsub
    rw [hP, hP]
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
    exact fun R hR j hj => hR j (hsub hj)
  have hW0 : ∀ U T : Finset κ, 0 ≤ W U T := fun U T => by
    rw [hW]; exact mul_nonneg (pow_nonneg hq0 _) (pow_nonneg hq1pos.le _)
  have hΦ0 : ∀ U : Finset κ, 0 ≤ Φ U := fun U => by
    rw [hΦ]; exact Finset.sum_nonneg fun T _ => mul_nonneg (hW0 _ _) (hP0 _)
  -- `P` is decreasing, so an index surviving the thinning is negatively correlated with it:
  -- pairing each `T` not containing `j` with `insert j T` compares the two sums termwise.
  have hcorr : ∀ (U : Finset κ) (j : κ), j ∈ U →
      ∑ T ∈ U.powerset, W U T * (if j ∈ T then P T else 0) ≤ q * Φ U := by
    intro U j hj
    obtain ⟨U', hU'⟩ : ∃ U' : Finset κ, U' = U.erase j := ⟨_, rfl⟩
    have hjU' : j ∉ U' := by rw [hU']; exact Finset.notMem_erase j U
    have hUeq : insert j U' = U := by rw [hU']; exact Finset.insert_erase hj
    obtain ⟨V, hV⟩ : ∃ V : Finset κ → ℝ,
        ∀ T : Finset κ, V T = q ^ T.card * (1 - q) ^ (U' \ T).card := ⟨_, fun _ => rfl⟩
    have hV0 : ∀ T, 0 ≤ V T := fun T => by
      rw [hV]; exact mul_nonneg (pow_nonneg hq0 _) (pow_nonneg hq1pos.le _)
    have hsplit : ∀ f : Finset κ → ℝ,
        ∑ T ∈ U.powerset, f T = (∑ T ∈ U'.powerset, f T) + ∑ T ∈ U'.powerset, f (insert j T) := by
      intro f
      rw [← hUeq]
      exact Finset.sum_powerset_insert hjU' f
    have hW1 : ∀ T ∈ U'.powerset, W U T = (1 - q) * V T := by
      intro T hT
      have hTsub : T ⊆ U' := Finset.mem_powerset.1 hT
      have hjT : j ∉ T := fun h => hjU' (hTsub h)
      have hcard : (U \ T).card = (U' \ T).card + 1 := by
        rw [← hUeq, Finset.insert_sdiff_of_notMem _ hjT,
          Finset.card_insert_of_notMem (fun h => hjU' (Finset.mem_sdiff.1 h).1)]
      rw [hW, hV, hcard, pow_succ]; ring
    have hW2 : ∀ T ∈ U'.powerset, W U (insert j T) = q * V T := by
      intro T hT
      have hTsub : T ⊆ U' := Finset.mem_powerset.1 hT
      have hjT : j ∉ T := fun h => hjU' (hTsub h)
      have hset : U \ insert j T = U' \ T := by
        rw [← hUeq]
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨hx, hx2⟩
          refine ⟨hx.resolve_left fun h => hx2 (Or.inl h), fun h => hx2 (Or.inr h)⟩
        · rintro ⟨hx, hx2⟩
          exact ⟨Or.inr hx, fun h => h.elim (fun hh => hjU' (hh ▸ hx)) hx2⟩
      rw [hW, hV, hset, Finset.card_insert_of_notMem hjT, pow_succ]; ring
    have hL : ∑ T ∈ U.powerset, W U T * (if j ∈ T then P T else 0)
        = q * ∑ T ∈ U'.powerset, V T * P (insert j T) := by
      rw [hsplit fun T => W U T * (if j ∈ T then P T else 0)]
      have h1 : ∀ T ∈ U'.powerset, W U T * (if j ∈ T then P T else 0) = 0 := by
        intro T hT
        have : j ∉ T := fun h => hjU' (Finset.mem_powerset.1 hT h)
        simp [this]
      rw [Finset.sum_congr rfl h1, Finset.sum_const_zero, zero_add, Finset.mul_sum]
      refine Finset.sum_congr rfl fun T hT => ?_
      rw [hW2 T hT]
      simp [Finset.mem_insert_self j T]
      ring
    have hΦeq : Φ U = (1 - q) * (∑ T ∈ U'.powerset, V T * P T)
        + q * ∑ T ∈ U'.powerset, V T * P (insert j T) := by
      rw [hΦ, hsplit fun T => W U T * P T, Finset.mul_sum, Finset.mul_sum]
      refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun T hT => ?_)
        (Finset.sum_congr rfl fun T hT => ?_)
      · rw [hW1 T hT]; ring
      · rw [hW2 T hT]; ring
    have hkey : ∑ T ∈ U'.powerset, V T * P (insert j T) ≤ ∑ T ∈ U'.powerset, V T * P T :=
      Finset.sum_le_sum fun T _ =>
        mul_le_mul_of_nonneg_left (hPmono T (insert j T) (Finset.subset_insert j T)) (hV0 T)
    rw [hL, hΦeq]
    nlinarith [mul_nonneg (mul_nonneg hq0 hq1pos.le) (sub_nonneg.2 hkey)]
  -- The weighted Boppana–Spencer induction.
  have hΦmain : ∀ U : Finset κ, Φ U ≤ Real.exp (-q * ∑ j ∈ U, a j + q ^ 2 * E U / 2) := by
    intro U
    refine Finset.induction_on U ?_ ?_
    · have h1 : {R : Set ι | ∀ j ∈ (∅ : Finset κ), ¬ S j ⊆ R} = Set.univ := by simp
      have hΦe : Φ ∅ = P ∅ := by
        rw [hΦ, Finset.powerset_empty, Finset.sum_singleton, hW]
        simp
      rw [hΦe, hP, h1, hE]
      simp
    · intro i U hiU ih
      obtain ⟨K, hK⟩ : ∃ K : Finset κ, K = U.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D := ⟨_, rfl⟩
      have hKU : K ⊆ U := by rw [hK]; exact Finset.filter_subset _ _
      have hPstep : ∀ T ∈ U.powerset,
          P (insert i T) ≤ (1 - a i + ∑ j ∈ K, (if j ∈ T then b i j else 0)) * P T := by
        intro T hT
        have hTU : T ⊆ U := Finset.mem_powerset.1 hT
        have hiT : i ∉ T := fun h => hiU (hTU h)
        have hsub : T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D) ⊆ T := Finset.filter_subset _ _
        have hindep : ∀ j ∈ T, j ∉ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D) →
            Disjoint (S i) (S j) := by
          intro j hjT hjn
          have hij : i ≠ j := by rintro rfl; exact hiT hjT
          have hnot : ¬ ((i, j) ∈ D ∧ (j, i) ∈ D) := fun h => hjn (Finset.mem_filter.2 ⟨hjT, h⟩)
          rcases not_and_or.1 hnot with h | h
          · exact hD i j hij h
          · exact (hD j i hij.symm h).symm
        have hstep := janson_prob_none_step_le p S i T
          (T.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D) hiT hsub hindep
        have hins : {R : Set ι | ∀ j ∈ insert i T, ¬ S j ⊆ R}
            = {R : Set ι | ¬ S i ⊆ R ∧ ∀ j ∈ T, ¬ S j ⊆ R} := by ext R; simp
        have hsum : ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j
            = ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D),
                (setBernoulli Set.univ p {R : Set ι | S i ∪ S j ⊆ R}).toReal :=
          Finset.sum_congr rfl fun j _ => hb i j
        have hfilter : ∑ j ∈ K, (if j ∈ T then b i j else 0)
            = ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j := by
          rw [hK, ← Finset.sum_filter]
          refine Finset.sum_congr ?_ fun _ _ => rfl
          ext j
          simp only [Finset.mem_filter]
          exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hTU h.1, h.2⟩, h.1⟩⟩
        rw [hfilter, hP, hins, hP, ha, hsum]
        exact hstep
      have hexpand : Φ (insert i U)
          = ∑ T ∈ U.powerset, W U T * ((1 - q) * P T + q * P (insert i T)) := by
        rw [hΦ, Finset.sum_powerset_insert hiU, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun T hT => ?_
        have hTU : T ⊆ U := Finset.mem_powerset.1 hT
        have hiT : i ∉ T := fun h => hiU (hTU h)
        have hc1 : W (insert i U) T = (1 - q) * W U T := by
          rw [hW, hW, Finset.insert_sdiff_of_notMem _ hiT,
            Finset.card_insert_of_notMem (fun h => hiU (Finset.mem_sdiff.1 h).1), pow_succ]
          ring
        have hc2 : W (insert i U) (insert i T) = q * W U T := by
          have hset : insert i U \ insert i T = U \ T := by
            ext x
            simp only [Finset.mem_sdiff, Finset.mem_insert]
            constructor
            · rintro ⟨hx, hx2⟩
              exact ⟨hx.resolve_left fun h => hx2 (Or.inl h), fun h => hx2 (Or.inr h)⟩
            · rintro ⟨hx, hx2⟩
              exact ⟨Or.inr hx, fun h => h.elim (fun hh => hiU (hh ▸ hx)) hx2⟩
          rw [hW, hW, hset, Finset.card_insert_of_notMem hiT, pow_succ]
          ring
        rw [hc1, hc2]; ring
      have hbound : Φ (insert i U) ≤ (1 - q * a i + q ^ 2 * ∑ j ∈ K, b i j) * Φ U := by
        have h1 : Φ (insert i U)
            ≤ ∑ T ∈ U.powerset, W U T * ((1 - q * a i) * P T
                + q * ((∑ j ∈ K, (if j ∈ T then b i j else 0)) * P T)) := by
          rw [hexpand]
          refine Finset.sum_le_sum fun T hT => ?_
          refine mul_le_mul_of_nonneg_left ?_ (hW0 U T)
          have h2 := mul_le_mul_of_nonneg_left (hPstep T hT) hq0
          nlinarith [h2]
        have hswap : ∑ T ∈ U.powerset, W U T * ((1 - q * a i) * P T
              + q * ((∑ j ∈ K, (if j ∈ T then b i j else 0)) * P T))
            = (1 - q * a i) * Φ U
              + q * ∑ j ∈ K, b i j * ∑ T ∈ U.powerset, W U T * (if j ∈ T then P T else 0) := by
          have e1 : ∀ T : Finset κ, W U T * ((1 - q * a i) * P T
                + q * ((∑ j ∈ K, (if j ∈ T then b i j else 0)) * P T))
              = (1 - q * a i) * (W U T * P T)
                + q * ∑ j ∈ K, (if j ∈ T then b i j else 0) * (W U T * P T) := by
            intro T
            rw [← Finset.sum_mul]
            ring
          rw [Finset.sum_congr rfl (fun T _ => e1 T), Finset.sum_add_distrib, ← Finset.mul_sum,
            ← hΦ, ← Finset.mul_sum, Finset.sum_comm]
          congr 2
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun T _ => ?_
          by_cases h : j ∈ T <;> simp [h]
        have h3 : ∑ j ∈ K, b i j * ∑ T ∈ U.powerset, W U T * (if j ∈ T then P T else 0)
            ≤ (∑ j ∈ K, b i j) * (q * Φ U) := by
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun j hj =>
            mul_le_mul_of_nonneg_left (hcorr U j (hKU hj)) (hb0 i j)
        have h4 := mul_le_mul_of_nonneg_left h3 hq0
        calc Φ (insert i U)
            ≤ ∑ T ∈ U.powerset, W U T * ((1 - q * a i) * P T
                + q * ((∑ j ∈ K, (if j ∈ T then b i j else 0)) * P T)) := h1
          _ = (1 - q * a i) * Φ U
              + q * ∑ j ∈ K, b i j * ∑ T ∈ U.powerset, W U T * (if j ∈ T then P T else 0) := hswap
          _ ≤ (1 - q * a i + q ^ 2 * ∑ j ∈ K, b i j) * Φ U := by nlinarith [h4]
      have hEineq : E U + 2 * ∑ j ∈ K, b i j ≤ E (insert i U) := by
        rw [hK]
        have hU : ∑ z ∈ (U.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image
              (fun j => ((i, j) : κ × κ)), b z.1 z.2
            = ∑ j ∈ U.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j :=
          Finset.sum_image (fun x _ y _ h => by simpa using h)
        have hV : ∑ z ∈ (U.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image
              (fun j => ((j, i) : κ × κ)), b z.1 z.2
            = ∑ j ∈ U.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j := by
          rw [Finset.sum_image (fun x _ y _ h => by simpa using h)]
          exact Finset.sum_congr rfl fun j _ => hbs i j
        have hd1 : Disjoint (D.filter fun z => z.1 ∈ U ∧ z.2 ∈ U)
            ((U.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image fun j => ((i, j) : κ × κ)) := by
          refine Finset.disjoint_left.2 ?_
          rintro z hz hz'
          obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz'
          exact hiU (Finset.mem_filter.1 hz).2.1
        have hd2 : Disjoint ((D.filter fun z => z.1 ∈ U ∧ z.2 ∈ U) ∪
              (U.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image fun j => ((i, j) : κ × κ))
            ((U.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image fun j => ((j, i) : κ × κ)) := by
          refine Finset.disjoint_left.2 ?_
          rintro z hz hz'
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hz'
          rcases Finset.mem_union.1 hz with h | h
          · exact hiU (Finset.mem_filter.1 h).2.2
          · obtain ⟨k, hk, hk'⟩ := Finset.mem_image.1 h
            have : k = i := congrArg Prod.snd hk'
            exact hiU (this ▸ (Finset.mem_filter.1 hk).1)
        have hss : (D.filter fun z => z.1 ∈ U ∧ z.2 ∈ U) ∪
              ((U.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image fun j => ((i, j) : κ × κ)) ∪
              ((U.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image fun j => ((j, i) : κ × κ))
            ⊆ D.filter fun z => z.1 ∈ insert i U ∧ z.2 ∈ insert i U := by
          intro z hz
          rcases Finset.mem_union.1 hz with hz | hz
          · rcases Finset.mem_union.1 hz with hz | hz
            · obtain ⟨hzD, h1, h2⟩ := Finset.mem_filter.1 hz
              exact Finset.mem_filter.2
                ⟨hzD, Finset.mem_insert_of_mem h1, Finset.mem_insert_of_mem h2⟩
            · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hz
              obtain ⟨hjU, hjD, -⟩ := Finset.mem_filter.1 hj
              exact Finset.mem_filter.2
                ⟨hjD, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hjU⟩
          · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hz
            obtain ⟨hjU, -, hjD⟩ := Finset.mem_filter.1 hj
            exact Finset.mem_filter.2
              ⟨hjD, Finset.mem_insert_of_mem hjU, Finset.mem_insert_self _ _⟩
        calc E U + 2 * ∑ j ∈ U.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j
            = ∑ z ∈ (D.filter fun z => z.1 ∈ U ∧ z.2 ∈ U) ∪
                ((U.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image fun j => ((i, j) : κ × κ)) ∪
                ((U.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image fun j => ((j, i) : κ × κ)),
                b z.1 z.2 := by
              rw [Finset.sum_union hd2, Finset.sum_union hd1, hU, hV, hE]; ring
          _ ≤ ∑ z ∈ D.filter (fun z => z.1 ∈ insert i U ∧ z.2 ∈ insert i U), b z.1 z.2 :=
              Finset.sum_le_sum_of_subset_of_nonneg hss fun z _ _ => hb0 _ _
          _ = E (insert i U) := (hE _).symm
      calc Φ (insert i U)
          ≤ (1 - q * a i + q ^ 2 * ∑ j ∈ K, b i j) * Φ U := hbound
        _ ≤ Real.exp (-q * a i + q ^ 2 * ∑ j ∈ K, b i j) * Φ U := by
            refine mul_le_mul_of_nonneg_right ?_ (hΦ0 U)
            have := Real.add_one_le_exp (-q * a i + q ^ 2 * ∑ j ∈ K, b i j)
            linarith
        _ ≤ Real.exp (-q * a i + q ^ 2 * ∑ j ∈ K, b i j)
              * Real.exp (-q * ∑ j ∈ U, a j + q ^ 2 * E U / 2) :=
            mul_le_mul_of_nonneg_left ih (Real.exp_nonneg _)
        _ = Real.exp ((-q * a i + q ^ 2 * ∑ j ∈ K, b i j)
              + (-q * ∑ j ∈ U, a j + q ^ 2 * E U / 2)) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (-q * ∑ j ∈ insert i U, a j + q ^ 2 * E (insert i U) / 2) := by
            rw [Finset.sum_insert hiU]
            refine Real.exp_le_exp.2 ?_
            have h5 := mul_le_mul_of_nonneg_left hEineq (sq_nonneg q)
            nlinarith [h5]
  -- Markov's inequality, as a partition rather than an integral: `EV J` is the event that the
  -- sets contained in the random subset are exactly those indexed by `J`, and on it the thinning
  -- misses `J` with probability `(1 - q) ^ #J`, which is at least `exp (-lam * s)` once `#J ≤ s`.
  obtain ⟨EV, hEV⟩ : ∃ EV : Finset κ → Set (Set ι),
      ∀ J : Finset κ, EV J = {R : Set ι | ∀ j, (S j ⊆ R ↔ j ∈ J)} := ⟨_, fun _ => rfl⟩
  obtain ⟨e, he⟩ : ∃ e : Finset κ → ℝ,
      ∀ J : Finset κ, e J = (setBernoulli Set.univ p (EV J)).toReal := ⟨_, fun _ => rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : Finset (Finset κ),
      F = Finset.univ.filter fun J : Finset κ => (J.card : ℝ) ≤ s := ⟨_, rfl⟩
  have he0 : ∀ J, 0 ≤ e J := fun J => by rw [he]; exact ENNReal.toReal_nonneg
  have hmemF : ∀ J : Finset κ, J ∈ F ↔ (J.card : ℝ) ≤ s := by
    intro J; rw [hF]; simp
  have hmeasSub : ∀ t : Set ι, MeasurableSet {R : Set ι | t ⊆ R} := fun t =>
    measurableSet_setOfPred.2 (Measurable.subset measurable_const measurable_id)
  have hEVmeas : ∀ J : Finset κ, MeasurableSet (EV J) := by
    intro J
    have heq : EV J = (⋂ j ∈ (J : Set κ), {R : Set ι | S j ⊆ R})
        ∩ ⋂ j ∈ ((J : Set κ)ᶜ), {R : Set ι | S j ⊆ R}ᶜ := by
      rw [hEV]
      ext R
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff, Finset.mem_coe]
      constructor
      · intro h
        exact ⟨fun j hj => (h j).2 hj, fun j hj hR => hj ((h j).1 hR)⟩
      · rintro ⟨h1, h2⟩ j
        exact ⟨fun hR => not_not.1 fun hj => h2 j hj hR, fun hj => h1 j hj⟩
    rw [heq]
    exact (MeasurableSet.biInter (Set.to_countable _) fun j _ => hmeasSub (S j)).inter
      (MeasurableSet.biInter (Set.to_countable _) fun j _ => (hmeasSub (S j)).compl)
  have hEVdisj : ∀ J J' : Finset κ, J ≠ J' → Disjoint (EV J) (EV J') := by
    intro J J' hne
    rw [Set.disjoint_left]
    intro R hR hR'
    rw [hEV] at hR hR'
    exact hne (Finset.ext fun j => (hR j).symm.trans (hR' j))
  have hsumE : ∀ G : Finset (Finset κ),
      ∑ J ∈ G, e J = (setBernoulli Set.univ p (⋃ J ∈ G, EV J)).toReal := by
    intro G
    rw [measure_biUnion_finset (fun J _ J' _ hne => hEVdisj J J' hne) fun J _ => hEVmeas J,
      ENNReal.toReal_sum fun J _ => measure_ne_top _ _]
    exact Finset.sum_congr rfl fun J _ => he J
  have hAeq : {R : Set ι | jansonCount S R ≤ s} = ⋃ J ∈ F, EV J := by
    ext R
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro hR
      refine ⟨Finset.univ.filter fun j => S j ⊆ R, ?_, ?_⟩
      · rw [hmemF]
        have hcoe : ({i | S i ⊆ R} : Set κ) = ↑(Finset.univ.filter fun j => S j ⊆ R) := by
          ext j; simp
        have h2 : jansonCount S R ≤ s := hR
        simp only [jansonCount, hcoe, Set.ncard_coe_finset] at h2
        exact h2
      · rw [hEV]; intro j; simp
    · rintro ⟨J, hJ, hRJ⟩
      rw [hEV] at hRJ
      have hcoe : ({i | S i ⊆ R} : Set κ) = ↑J := by
        ext j; simpa using hRJ j
      show jansonCount S R ≤ s
      simp only [jansonCount, hcoe, Set.ncard_coe_finset]
      exact (hmemF J).1 hJ
  have hPge : ∀ T : Finset κ, ∑ J ∈ F.filter (fun J => Disjoint J T), e J ≤ P T := by
    intro T
    rw [hsumE, hP]
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
    intro R hR
    simp only [Set.mem_iUnion, exists_prop] at hR
    obtain ⟨J, hJ, hRJ⟩ := hR
    rw [hEV] at hRJ
    intro j hj hSj
    exact Finset.disjoint_left.1 (Finset.mem_filter.1 hJ).2 ((hRJ j).1 hSj) hj
  have hbinom : ∀ u : Finset κ, ∑ t ∈ u.powerset, q ^ t.card * (1 - q) ^ (u \ t).card = 1 := by
    intro u
    have h1 : ∏ _i ∈ u, ((q : ℝ) + (1 - q))
        = ∑ t ∈ u.powerset, (∏ _i ∈ t, (q : ℝ)) * ∏ _i ∈ u \ t, (1 - q) :=
      Finset.prod_add _ _ u
    simp only [Finset.prod_const] at h1
    rw [show (q : ℝ) + (1 - q) = 1 by ring, one_pow] at h1
    exact h1.symm
  have hWsum : ∀ J : Finset κ,
      ∑ T ∈ (Finset.univ : Finset κ).powerset, (if Disjoint J T then W Finset.univ T else 0)
        = (1 - q) ^ J.card := by
    intro J
    have hset : ((Finset.univ : Finset κ).powerset.filter fun T => Disjoint J T) = Jᶜ.powerset := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
      constructor
      · exact fun h x hx => Finset.mem_compl.2 fun hxJ => Finset.disjoint_left.1 h hxJ hx
      · exact fun h => Finset.disjoint_left.2 fun x hxJ hxT => Finset.mem_compl.1 (h hxT) hxJ
    have hcard : ∀ T ∈ Jᶜ.powerset, (Finset.univ \ T).card = (Jᶜ \ T).card + J.card := by
      intro T hT
      have hTc : T ⊆ Jᶜ := Finset.mem_powerset.1 hT
      have hun : Finset.univ \ T = (Jᶜ \ T) ∪ J := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ, Finset.mem_compl, true_and]
        constructor
        · intro hx
          by_cases hxJ : x ∈ J
          · exact Or.inr hxJ
          · exact Or.inl ⟨hxJ, hx⟩
        · rintro (⟨-, h2⟩ | h)
          · exact h2
          · exact fun hxT => Finset.mem_compl.1 (hTc hxT) h
      have hdisj : Disjoint (Jᶜ \ T) J :=
        Finset.disjoint_left.2 fun x hx => Finset.mem_compl.1 (Finset.mem_sdiff.1 hx).1
      rw [hun, Finset.card_union_of_disjoint hdisj]
    rw [← Finset.sum_filter, hset]
    calc ∑ T ∈ Jᶜ.powerset, W Finset.univ T
        = ∑ T ∈ Jᶜ.powerset, q ^ T.card * (1 - q) ^ (Jᶜ \ T).card * (1 - q) ^ J.card := by
          refine Finset.sum_congr rfl fun T hT => ?_
          rw [hW, hcard T hT, pow_add]; ring
      _ = (∑ T ∈ Jᶜ.powerset, q ^ T.card * (1 - q) ^ (Jᶜ \ T).card) * (1 - q) ^ J.card :=
          (Finset.sum_mul _ _ _).symm
      _ = (1 - q) ^ J.card := by rw [hbinom, one_mul]
  have hPart1 : (setBernoulli Set.univ p {R : Set ι | jansonCount S R ≤ s}).toReal
      ≤ Real.exp (lam * s) * Φ Finset.univ := by
    have hexpJ : ∀ J ∈ F, Real.exp (-(lam * s)) ≤ (1 - q) ^ J.card := by
      intro J hJ
      rw [hq1, ← Real.exp_nat_mul]
      refine Real.exp_le_exp.2 ?_
      have hcard := (hmemF J).1 hJ
      nlinarith [hlam]
    have hkey : Real.exp (-(lam * s)) * (∑ J ∈ F, e J) ≤ Φ Finset.univ := by
      calc Real.exp (-(lam * s)) * ∑ J ∈ F, e J
          = ∑ J ∈ F, e J * Real.exp (-(lam * s)) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
        _ ≤ ∑ J ∈ F, e J * (1 - q) ^ J.card :=
            Finset.sum_le_sum fun J hJ => mul_le_mul_of_nonneg_left (hexpJ J hJ) (he0 J)
        _ = ∑ J ∈ F, ∑ T ∈ (Finset.univ : Finset κ).powerset,
              (if Disjoint J T then W Finset.univ T * e J else 0) := by
            refine Finset.sum_congr rfl fun J _ => ?_
            rw [← hWsum J, Finset.mul_sum]
            refine Finset.sum_congr rfl fun T _ => ?_
            by_cases h : Disjoint J T <;> simp [h, mul_comm]
        _ = ∑ T ∈ (Finset.univ : Finset κ).powerset, ∑ J ∈ F,
              (if Disjoint J T then W Finset.univ T * e J else 0) := Finset.sum_comm
        _ ≤ ∑ T ∈ (Finset.univ : Finset κ).powerset, W Finset.univ T * P T := by
            refine Finset.sum_le_sum fun T _ => ?_
            have h1 : ∑ J ∈ F, (if Disjoint J T then W Finset.univ T * e J else 0)
                = W Finset.univ T * ∑ J ∈ F.filter (fun J => Disjoint J T), e J := by
              rw [Finset.sum_filter, Finset.mul_sum]
              refine Finset.sum_congr rfl fun J _ => ?_
              by_cases h : Disjoint J T <;> simp [h, mul_comm]
            rw [h1]
            exact mul_le_mul_of_nonneg_left (hPge T) (hW0 _ _)
        _ = Φ Finset.univ := (hΦ _).symm
    rw [hAeq, ← hsumE]
    have hmul := mul_le_mul_of_nonneg_left hkey (Real.exp_pos (lam * s)).le
    rw [← mul_assoc, ← Real.exp_add] at hmul
    simpa using hmul
  have h2 : ∑ j ∈ (Finset.univ : Finset κ), a j = jansonMu p S :=
    Finset.sum_congr rfl fun j _ => ha j
  have h3 : E (Finset.univ : Finset κ) = jansonDelta p S D := by
    rw [hE, Finset.filter_true_of_mem fun z _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩]
    exact Finset.sum_congr rfl fun z _ => hb z.1 z.2
  calc (setBernoulli Set.univ p {R : Set ι | jansonCount S R ≤ s}).toReal
      ≤ Real.exp (lam * s) * Φ Finset.univ := hPart1
    _ ≤ Real.exp (lam * s) * Real.exp (-q * jansonMu p S + q ^ 2 * jansonDelta p S D / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
        have hu := hΦmain Finset.univ
        rwa [h2, h3] at hu
    _ = Real.exp (lam * s - q * jansonMu p S + q ^ 2 * jansonDelta p S D / 2) := by
        rw [← Real.exp_add]; congr 1; ring
    _ = Real.exp (lam * s - (1 - Real.exp (-lam)) * jansonMu p S
          + (1 - Real.exp (-lam)) ^ 2 * jansonDelta p S D / 2) := by rw [hqdef]

end LowerTail

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
  have hμ0 : 0 ≤ jansonMu p S := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hΔ0 : 0 ≤ jansonDelta p S D := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  rcases ht0.lt_or_eq with ht | ht
  · have hc : 0 < jansonMu p S + jansonDelta p S D := by linarith
    have hcne : jansonMu p S + jansonDelta p S D ≠ 0 := ne_of_gt hc
    have hlam0 : 0 ≤ t / (jansonMu p S + jansonDelta p S D) := div_nonneg ht0 hc.le
    refine (janson_lower_tail_step_le p S D hD
      (lam := t / (jansonMu p S + jansonDelta p S D)) (s := jansonMu p S - t) hlam0).trans
      (Real.exp_le_exp.2 ?_)
    set lam := t / (jansonMu p S + jansonDelta p S D) with hlamdef
    set q := 1 - Real.exp (-lam) with hqdef
    have hq0 : 0 ≤ q := by
      have h := Real.exp_le_one_iff.2 (neg_nonpos.2 hlam0)
      rw [hqdef]; linarith
    have hq1 : q ≤ lam := by
      have h := Real.add_one_le_exp (-lam)
      rw [hqdef]; linarith
    have hq2 : lam - lam ^ 2 / 2 ≤ q := by
      have h := exp_neg_le_one_sub_add_sq_div_two hlam0
      rw [hqdef]; linarith
    have hq3 : q ^ 2 ≤ lam ^ 2 := by nlinarith
    have hfin : -t ^ 2 / (2 * (jansonMu p S + jansonDelta p S D))
        = -lam * t + lam ^ 2 * (jansonMu p S + jansonDelta p S D) / 2 := by
      rw [hlamdef]; field_simp; ring
    rw [hfin]
    nlinarith [mul_nonneg hμ0 (sub_nonneg.2 hq2), mul_nonneg hΔ0 (sub_nonneg.2 hq3)]
  · have hprob : setBernoulli Set.univ p
        {R : Set ι | jansonCount S R ≤ jansonMu p S - t} ≤ 1 := prob_le_one
    have hone : Real.exp (-t ^ 2 / (2 * (jansonMu p S + jansonDelta p S D))) = 1 := by
      rw [← ht]; norm_num
    rw [hone]
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hprob

end ProbMethodCombinatorics
