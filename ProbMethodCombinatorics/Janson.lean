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
  sorry

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
