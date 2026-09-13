import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import ProbMethodCombinatorics.PropertyB
import ProbMethodCombinatorics.Ramsey

/-!
# Chapter 6: Lovász Local Lemma

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Chapter 6.

The local lemma interpolates between the two easy regimes for avoiding a family of bad
events: full independence, and a union bound.  It needs a genuine probability space — the
notion of independence involved is not pairwise independence and does not reduce to
counting — so this chapter, like Chapter 4, is stated over `MeasureTheory.Measure`.
-/

namespace ProbMethodCombinatorics

open Finset MeasureTheory ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The event that each `B j` with `j ∈ s` occurs or fails according to `f`. -/
def pattern (B : ι → Set Ω) (s : Finset ι) (f : ι → Bool) : Set Ω :=
  ⋂ j ∈ s, if f j then B j else (B j)ᶜ

/-- **Independence from a set of events** (Zhao, Definition 6.1.1): `A` is independent of every
event built by intersecting the `B j`, `j ∈ s`, each taken either positively or negatively.

This is strictly stronger than pairwise independence of `A` with each `B j`, which is exactly
why the dependency graph of Definition 6.1.2 is not obtained by joining non-independent pairs. -/
def IndepFrom (μ : Measure Ω) (A : Set Ω) (B : ι → Set Ω) (s : Finset ι) : Prop :=
  ∀ f : ι → Bool, μ (A ∩ pattern B s f) = μ A * μ (pattern B s f)

/-- **Dependency graph** (Zhao, Definition 6.1.2): `N i` lists the neighbours of `i`, and each
`A i` must be independent from every set of events avoiding `i` and its neighbours. -/
def IsDependencyGraph (μ : Measure Ω) (A : ι → Set Ω) (N : ι → Finset ι) : Prop :=
  ∀ i : ι, ∀ s : Finset ι, (∀ j ∈ s, j ≠ i ∧ j ∉ N i) → IndepFrom μ (A i) A s

variable [Fintype ι]

/-- **Lovász local lemma, general form** (Zhao, Theorem 6.1.9; Erdős–Lovász 1975).  If weights
`x i ∈ [0, 1)` satisfy `ℙ(A i) ≤ x i * ∏_{j ∈ N i} (1 - x j)`, then the probability that no
`A i` occurs is at least `∏ i, (1 - x i)`. -/
theorem lovasz_local_lemma [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (N : ι → Finset ι) (hN : IsDependencyGraph μ A N)
    (x : ι → ℝ) (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
    (hbound : ∀ i, (μ (A i)).toReal ≤ x i * ∏ j ∈ N i, (1 - x j)) :
    ∏ i, (1 - x i) ≤ (μ (⋂ i, (A i)ᶜ)).toReal := by
  sorry

/-- **Lovász local lemma, symmetric form** (Zhao, Theorem 6.1.7): if every `A i` has probability
at most `p` and depends on at most `d` others, and `e * p * (d + 1) ≤ 1`, then with positive
probability none of the `A i` occur.  The constant `e` is best possible (Shearer 1985). -/
theorem lovasz_local_lemma_symmetric [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (N : ι → Finset ι) (hN : IsDependencyGraph μ A N)
    {p : ℝ} {d : ℕ} (hp : ∀ i, (μ (A i)).toReal ≤ p)
    (hd : ∀ i, (N i).card ≤ d)
    (h : Real.exp 1 * p * (d + 1) ≤ 1) :
    0 < (μ (⋂ i, (A i)ᶜ)).toReal := by
  -- `ι` carries no `DecidableEq`, which the `Finset` operations below need.
  have : DecidableEq ι := (Fintype.equivFin ι).decidableEq
  -- The general form (Theorem 6.1.9) at the constant weight `t`, which is all that is needed
  -- for the symmetric form.
  have general : ∀ t : ℝ, 0 ≤ t → t < 1 →
      (∀ i, (μ (A i)).toReal ≤ t * (1 - t) ^ (N i).card) →
      (1 - t) ^ Fintype.card ι ≤ (μ (⋂ i, (A i)ᶜ)).toReal := by
    intro t ht₀ ht₁ hbound
    have ht' : (0:ℝ) ≤ 1 - t := by linarith
    have ht1' : (1:ℝ) - t ≤ 1 := by linarith
    obtain ⟨E, hE⟩ : ∃ E : Finset ι → Set Ω, ∀ s, E s = ⋂ j ∈ s, (A j)ᶜ := ⟨_, fun _ => rfl⟩
    have hEinsert : ∀ (j : ι) (s : Finset ι), E (insert j s) = (A j)ᶜ ∩ E s := by
      intro j s; rw [hE, hE, Finset.set_biInter_insert]
    have hEmono : ∀ (s u : Finset ι), u ⊆ s → E s ⊆ E u := by
      intro s u hsub
      rw [hE, hE]
      intro x hx
      simp only [Set.mem_iInter] at hx ⊢
      exact fun j hj => hx j (hsub hj)
    have hEindep : ∀ (i : ι) (s : Finset ι), (∀ j ∈ s, j ≠ i ∧ j ∉ N i) →
        μ (A i ∩ E s) = μ (A i) * μ (E s) := by
      intro i s hs
      have h := hN i s hs (fun _ => false)
      rwa [show pattern A s (fun _ => false) = E s by rw [hE]; simp [pattern]] at h
    -- Intersecting with one more complement removes exactly the mass of `A j ∩ E s`.
    have hstep : ∀ (j : ι) (s : Finset ι),
        (μ (E (insert j s))).toReal = (μ (E s)).toReal - (μ (A j ∩ E s)).toReal := by
      intro j s
      have h1 : μ (E s ∩ A j) + μ (E s \ A j) = μ (E s) := measure_inter_add_sdiff _ (hA j)
      have h2 : E s \ A j = E (insert j s) := by
        rw [hEinsert, Set.sdiff_eq, Set.inter_comm]
      have h3 : E s ∩ A j = A j ∩ E s := Set.inter_comm _ _
      rw [h2, h3] at h1
      have h4 := congrArg ENNReal.toReal h1
      rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at h4
      linarith
    -- The induction of Theorem 6.1.9 on `#s`, stated as `ℙ(A i ∩ E s) ≤ t * ℙ(E s)` rather than
    -- `ℙ(A i | E s) ≤ t`: multiplying through by `ℙ(E s)` removes every positivity side condition.
    have main : ∀ n : ℕ, ∀ s : Finset ι, s.card ≤ n →
        ((1 - t) ^ s.card ≤ (μ (E s)).toReal ∧
         ∀ i, i ∉ s → (μ (A i ∩ E s)).toReal ≤ t * (μ (E s)).toReal) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro s hsn
        constructor
        · rcases Finset.eq_empty_or_nonempty s with rfl | ⟨i, hi⟩
          · simp [hE]
          · have hcard : (s.erase i).card = s.card - 1 := Finset.card_erase_of_mem hi
            have hpos : 1 ≤ s.card := Finset.card_pos.2 ⟨i, hi⟩
            have hlt : s.card - 1 < n := by omega
            obtain ⟨ha, hb⟩ := ih (s.card - 1) hlt (s.erase i) (le_of_eq hcard)
            have hbi := hb i (Finset.notMem_erase i s)
            have heq := hstep i (s.erase i)
            rw [Finset.insert_erase hi] at heq
            have hcards : s.card = (s.erase i).card + 1 := by omega
            rw [hcards, pow_succ]
            calc (1 - t) ^ (s.erase i).card * (1 - t)
                = (1 - t) * (1 - t) ^ (s.erase i).card := mul_comm _ _
              _ ≤ (1 - t) * (μ (E (s.erase i))).toReal := mul_le_mul_of_nonneg_left ha ht'
              _ ≤ (μ (E s)).toReal := by rw [heq]; linarith
        · intro i hi
          have hunion : (s ∩ N i) ∪ (s \ N i) = s := by
            rw [Finset.union_comm]; exact Finset.sdiff_union_inter s (N i)
          have hs2sub : s \ N i ⊆ s := Finset.sdiff_subset
          -- Peeling the neighbours of `i` off `s` one at a time bounds the denominator of the
          -- book's conditional probability from below.
          have hsub : ∀ u : Finset ι, u ⊆ s ∩ N i →
              (1 - t) ^ u.card * (μ (E (s \ N i))).toReal ≤ (μ (E (u ∪ (s \ N i)))).toReal := by
            intro u
            induction u using Finset.induction_on with
            | empty => intro _; simp
            | @insert j u' hju' ihu =>
              intro hins
              have hju : u' ⊆ s ∩ N i := (Finset.subset_insert _ _).trans hins
              have hjmem : j ∈ s ∩ N i := hins (Finset.mem_insert_self j u')
              have hjs : j ∈ s := (Finset.mem_inter.1 hjmem).1
              have hjN : j ∈ N i := (Finset.mem_inter.1 hjmem).2
              have hjnotin : j ∉ u' ∪ (s \ N i) := by
                simp only [Finset.mem_union, Finset.mem_sdiff, not_or, not_and]
                exact ⟨hju', fun _ => not_not_intro hjN⟩
              have hsubs : u' ∪ (s \ N i) ⊆ s := by
                intro x hx
                rcases Finset.mem_union.1 hx with hx | hx
                · exact (Finset.mem_inter.1 (hju hx)).1
                · exact hs2sub hx
              have hcardlt : (u' ∪ (s \ N i)).card < s.card :=
                Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsubs).2 ⟨j, hjs, hjnotin⟩)
              obtain ⟨-, hb⟩ := ih ((u' ∪ (s \ N i)).card) (lt_of_lt_of_le hcardlt hsn) _ le_rfl
              have hbj := hb j hjnotin
              have heq := hstep j (u' ∪ (s \ N i))
              have hih := ihu hju
              rw [Finset.insert_union, Finset.card_insert_of_notMem hju', pow_succ]
              calc (1 - t) ^ u'.card * (1 - t) * (μ (E (s \ N i))).toReal
                  = (1 - t) * ((1 - t) ^ u'.card * (μ (E (s \ N i))).toReal) := by ring
                _ ≤ (1 - t) * (μ (E (u' ∪ (s \ N i)))).toReal := mul_le_mul_of_nonneg_left hih ht'
                _ ≤ (μ (E (insert j (u' ∪ (s \ N i))))).toReal := by rw [heq]; linarith
          have hsubs1 := hsub (s ∩ N i) Finset.Subset.rfl
          rw [hunion] at hsubs1
          have hcard1 : (s ∩ N i).card ≤ (N i).card :=
            Finset.card_le_card Finset.inter_subset_right
          have hindep : μ (A i ∩ E (s \ N i)) = μ (A i) * μ (E (s \ N i)) := by
            refine hEindep i _ fun j hj => ?_
            rw [Finset.mem_sdiff] at hj
            exact ⟨fun hji => hi (hji ▸ hj.1), hj.2⟩
          have hindepR : (μ (A i ∩ E (s \ N i))).toReal
              = (μ (A i)).toReal * (μ (E (s \ N i))).toReal := by
            rw [hindep, ENNReal.toReal_mul]
          have hmono : (μ (A i ∩ E s)).toReal ≤ (μ (A i ∩ E (s \ N i))).toReal :=
            ENNReal.toReal_mono (measure_ne_top μ _)
              (measure_mono (Set.inter_subset_inter_right _ (hEmono s (s \ N i) hs2sub)))
          calc (μ (A i ∩ E s)).toReal
              ≤ (μ (A i)).toReal * (μ (E (s \ N i))).toReal := by rw [← hindepR]; exact hmono
            _ ≤ (t * (1 - t) ^ (s ∩ N i).card) * (μ (E (s \ N i))).toReal := by
                refine mul_le_mul_of_nonneg_right ((hbound i).trans ?_) ENNReal.toReal_nonneg
                exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht' ht1' hcard1) ht₀
            _ = t * ((1 - t) ^ (s ∩ N i).card * (μ (E (s \ N i))).toReal) := by ring
            _ ≤ t * (μ (E s)).toReal := mul_le_mul_of_nonneg_left hsubs1 ht₀
    have hfin := (main (Fintype.card ι) Finset.univ (le_of_eq Finset.card_univ)).1
    rw [Finset.card_univ, hE] at hfin
    simpa using hfin
  -- Take every weight to be `1 / (d + 2)`.  The hypothesis of the general form then amounts to
  -- `(1 + 1 / (d + 1)) ^ (d + 1) ≤ e`, which `1 + x ≤ exp x` supplies; unlike `1 / (d + 1)` this
  -- weight is admissible at `d = 0` as well.
  have hD : ((d:ℝ) + 2) ≠ 0 := by positivity
  have hm : (0:ℝ) < (d:ℝ) + 1 := by positivity
  have hkey : ((d:ℝ) + 2) ^ (d + 1) ≤ Real.exp 1 * ((d:ℝ) + 1) ^ (d + 1) := by
    have h2 := Real.add_one_le_exp (1 / ((d:ℝ) + 1))
    have h3 : ((d:ℝ) + 1) * (1 / ((d:ℝ) + 1) + 1) ≤ ((d:ℝ) + 1) * Real.exp (1 / ((d:ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left h2 hm.le
    have h4 : ((d:ℝ) + 1) * (1 / ((d:ℝ) + 1) + 1) = (d:ℝ) + 2 := by
      field_simp
      ring
    have h1 : (d:ℝ) + 2 ≤ ((d:ℝ) + 1) * Real.exp (1 / ((d:ℝ) + 1)) := by linarith
    have h5 : ((d:ℝ) + 2) ^ (d + 1) ≤ (((d:ℝ) + 1) * Real.exp (1 / ((d:ℝ) + 1))) ^ (d + 1) :=
      pow_le_pow_left₀ (by positivity) h1 _
    have h6 : (((d:ℝ) + 1) * Real.exp (1 / ((d:ℝ) + 1))) ^ (d + 1)
        = ((d:ℝ) + 1) ^ (d + 1) * Real.exp 1 := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      field_simp
    linarith
  have ht₀ : (0:ℝ) ≤ 1 / ((d:ℝ) + 2) := by positivity
  have ht₁ : 1 / ((d:ℝ) + 2) < 1 := by
    rw [div_lt_one (by positivity)]
    have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    linarith
  have h1t : 1 - 1 / ((d:ℝ) + 2) = ((d:ℝ) + 1) / ((d:ℝ) + 2) := by field_simp; ring
  have hbound : ∀ i, (μ (A i)).toReal
      ≤ 1 / ((d:ℝ) + 2) * (1 - 1 / ((d:ℝ) + 2)) ^ (N i).card := by
    intro i
    have hp0 : 0 ≤ p := le_trans ENNReal.toReal_nonneg (hp i)
    refine (hp i).trans (le_trans ?_ (mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by rw [h1t]; positivity) (by rw [h1t]; linarith) (hd i)) ht₀))
    have heq : 1 / ((d:ℝ) + 2) * (1 - 1 / ((d:ℝ) + 2)) ^ d
        = ((d:ℝ) + 1) ^ d / ((d:ℝ) + 2) ^ (d + 1) := by
      rw [h1t, div_pow, pow_succ]
      field_simp
    rw [heq, le_div_iff₀ (by positivity)]
    calc p * ((d:ℝ) + 2) ^ (d + 1) ≤ p * (Real.exp 1 * ((d:ℝ) + 1) ^ (d + 1)) :=
          mul_le_mul_of_nonneg_left hkey hp0
      _ = ((d:ℝ) + 1) ^ d * (Real.exp 1 * p * ((d:ℝ) + 1)) := by rw [pow_succ]; ring
      _ ≤ ((d:ℝ) + 1) ^ d * 1 := mul_le_mul_of_nonneg_left h (by positivity)
      _ = ((d:ℝ) + 1) ^ d := mul_one _
  have hpos : (0:ℝ) < (1 - 1 / ((d:ℝ) + 2)) ^ Fintype.card ι :=
    pow_pos (by rw [h1t]; positivity) _
  linarith [general (1 / ((d:ℝ) + 2)) ht₀ ht₁ hbound]

/-- **Lovász local lemma, small-neighbourhood form** (Zhao, Corollary 6.1.10): if every `A i` has
probability less than `1 / 2` and the probabilities in each neighbourhood sum to at most `1 / 4`,
then with positive probability none of the `A i` occur. -/
theorem lovasz_local_lemma_of_sum_le [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (N : ι → Finset ι) (hN : IsDependencyGraph μ A N)
    (hhalf : ∀ i, (μ (A i)).toReal < 1 / 2)
    (hsum : ∀ i, ∑ j ∈ N i, (μ (A j)).toReal ≤ 1 / 4) :
    0 < (μ (⋂ i, (A i)ᶜ)).toReal := by
  sorry

section Applications

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Local condition for 2-colourability** (Zhao, Theorem 6.2.1): a `k`-uniform hypergraph in
which every edge meets at most `d` other edges is 2-colourable as soon as
`e * (d + 1) ≤ 2 ^ (k - 1)`.

Unlike `twoColorable_of_card_lt` (Theorem 1.3.1) this bounds no global quantity: a hypergraph
with arbitrarily many edges qualifies, provided they are spread out. -/
theorem twoColorable_of_inter_card_le {k : ℕ} (hk : 2 ≤ k) {H : Finset (Finset α)}
    (huniform : ∀ e ∈ H, e.card = k) {d : ℕ}
    (hd : ∀ e ∈ H, ((H.erase e).filter fun f => (e ∩ f).Nonempty).card ≤ d)
    (h : Real.exp 1 * (d + 1) ≤ 2 ^ (k - 1)) :
    TwoColorable H := by
  sorry

/-- **Zhao, Corollary 6.2.2**: for `k ≥ 9` every `k`-uniform `k`-regular hypergraph is
2-colourable, where `k`-regular means every vertex lies in exactly `k` edges.  (The statement
fails for `k = 2` and `k = 3` but holds for all `k ≥ 4`, by Thomassen 1992.) -/
theorem twoColorable_of_regular {k : ℕ} (hk : 9 ≤ k) {H : Finset (Finset α)}
    (huniform : ∀ e ∈ H, e.card = k)
    (hreg : ∀ v ∈ H.biUnion id, (H.filter fun e => v ∈ e).card = k) :
    TwoColorable H := by
  sorry

/-- **Spencer 1977** (Zhao, Theorem 1.1.9): the local lemma improves the Ramsey lower bound of
Theorem 1.1.2 by a further constant factor, giving the best bound on `R(k, k)` known to date.

The hypothesis is the book's `((k choose 2)(n choose (k-2)) + 1) 2 ^ (1 - (k choose 2)) < 1/e`
with denominators cleared. -/
theorem lt_ramseyNumber_of_local_lemma (n k : ℕ) (hk : 2 ≤ k)
    (h : Real.exp 1 * (2 * ((k.choose 2 * n.choose (k - 2) : ℕ) : ℝ) + 2)
      ≤ 2 ^ (k.choose 2)) :
    n < ramseyNumber k := by
  sorry

end Applications

end ProbMethodCombinatorics
