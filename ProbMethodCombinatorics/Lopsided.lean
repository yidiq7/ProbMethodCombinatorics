import ProbMethodCombinatorics.LocalLemma

/-!
# Section 6.5: the lopsided local lemma

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Theorem 6.5.1 and Corollary 6.5.2.

The independence hypothesis of the local lemma is used in exactly one place — equation (6.3),
where `ℙ(A i ∩ ⋂_{j ∈ S} (A j)ᶜ)` is rewritten as `ℙ(A i) · ℙ(⋂_{j ∈ S} (A j)ᶜ)`.  Turning that
`=` into a `≤` costs nothing in the proof and weakens the hypothesis to a *negative* dependency
condition: avoiding some bad events only makes it easier to avoid others.

Note how much weaker this is than `IndepFrom`.  `IndepFrom` quantifies over every pattern
`f : ι → Bool`, positive and negative; `IsNegativeDependencyGraph` asks only about the
all-negative pattern, and only for an inequality in one direction.  That gap is the content of
Remark 6.5.3's warning that a negative dependency graph is still not obtained by checking pairs.
-/

namespace ProbMethodCombinatorics

open Finset MeasureTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Negative dependency graph** (Zhao, Theorem 6.5.1, hypothesis (6.1)): conditioning on
avoiding any set of events away from `i` and its neighbours does not make `A i` more likely. -/
def IsNegativeDependencyGraph (μ : Measure Ω) (A : ι → Set Ω) (N : ι → Finset ι) : Prop :=
  ∀ i : ι, ∀ s : Finset ι, (∀ j ∈ s, j ≠ i ∧ j ∉ N i) →
    μ (A i ∩ ⋂ j ∈ s, (A j)ᶜ) ≤ μ (A i) * μ (⋂ j ∈ s, (A j)ᶜ)

/-- An ordinary dependency graph is a negative dependency graph: independence gives equality,
and the all-negative pattern is one of the patterns `IndepFrom` covers. -/
theorem IsDependencyGraph.isNegativeDependencyGraph {A : ι → Set Ω} {N : ι → Finset ι}
    (h : IsDependencyGraph μ A N) : IsNegativeDependencyGraph μ A N := by
  intro i s hs
  have key := h i s hs (fun _ => false)
  simp only [pattern] at key
  exact le_of_eq key

/-- **The conditional bound of the lopsided local lemma** (Zhao, Theorem 6.5.1, equation (6.1)):
for every `i` and every finite set `S` of indices avoiding `i`,
`ℙ(A i ∩ ⋂_{j ∈ S} (A j)ᶜ) ≤ x i * ℙ(⋂_{j ∈ S} (A j)ᶜ)`.

The induction on `S.card` is the one used for `measure_inter_biInter_compl_le`, splitting `S`
into the part inside `N i` and the part outside.  The outside part is the only place the
dependency hypothesis enters, and `IsNegativeDependencyGraph` supplies there the inequality
`ℙ(A i ∩ ⋂_{j ∈ W₂} (A j)ᶜ) ≤ ℙ(A i) * ℙ(⋂_{j ∈ W₂} (A j)ᶜ)` in place of an equality; every
later step is monotone in that quantity. -/
theorem measure_inter_biInter_compl_le_of_negativeDependency [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (N : ι → Finset ι) (hN : IsNegativeDependencyGraph μ A N)
    (x : ι → ℝ) (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
    (hbound : ∀ i, (μ (A i)).toReal ≤ x i * ∏ j ∈ N i, (1 - x j))
    (i : ι) (S : Finset ι) (hi : i ∉ S) :
    (μ (A i ∩ ⋂ j ∈ S, (A j)ᶜ)).toReal ≤ x i * (μ (⋂ j ∈ S, (A j)ᶜ)).toReal := by
  obtain ⟨B, hB⟩ : ∃ B : Finset ι → Set Ω, ∀ W, B W = ⋂ j ∈ W, (A j)ᶜ := ⟨_, fun _ => rfl⟩
  have hBmem : ∀ (W : Finset ι) (ω : Ω), ω ∈ B W ↔ ∀ j ∈ W, ω ∉ A j := by
    intro W ω; rw [hB]; simp
  have hBempty : B ∅ = Set.univ := by rw [hB]; simp
  have hBcons : ∀ (a : ι) (W : Finset ι) (h : a ∉ W),
      B (Finset.cons a W h) = (A a)ᶜ ∩ B W := by
    intro a W h
    ext ω
    simp only [hBmem, Set.mem_inter_iff, Set.mem_compl_iff, Finset.mem_cons, forall_eq_or_imp]
  have hBmono : ∀ W W' : Finset ι, W ⊆ W' → B W' ⊆ B W := by
    intro W W' hsub ω hω
    rw [hBmem] at hω ⊢
    exact fun j hj => hω j (hsub hj)
  have hBcompl : ∀ (a : ι) (W : Finset ι) (h : a ∉ W),
      (μ (B (Finset.cons a W h))).toReal
        = (μ (B W)).toReal - (μ (A a ∩ B W)).toReal := by
    intro a W h
    have hadd : μ (B W ∩ A a) + μ (B W \ A a) = μ (B W) :=
      measure_inter_add_sdiff _ (hA a)
    have hset : B (Finset.cons a W h) = B W \ A a := by
      rw [hBcons a W h, Set.sdiff_eq]; exact Set.inter_comm _ _
    rw [hset, ← hadd, ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _),
      Set.inter_comm (B W) (A a)]
    ring
  have hx1' : ∀ j, (0 : ℝ) ≤ 1 - x j := fun j => by linarith [hx₁ j]
  have hx1'' : ∀ j, (1 : ℝ) - x j ≤ 1 := fun j => by linarith [hx₀ j]
  have hsplit : ∀ (k : ι) (W : Finset ι), ∃ (W₁ W₂ : Finset ι) (h : Disjoint W₁ W₂),
      W₁.disjUnion W₂ h = W ∧ (∀ j ∈ W₁, j ∈ N k) ∧ (∀ j ∈ W₂, j ∉ N k) := by
    intro k W
    induction W using Finset.cons_induction with
    | empty => exact ⟨∅, ∅, by simp, by simp, by simp, by simp⟩
    | cons a W ha ih =>
      obtain ⟨W₁, W₂, h, hU, h1, h2⟩ := ih
      have hmem : ∀ j, j ∈ W ↔ j ∈ W₁ ∨ j ∈ W₂ := by
        intro j; rw [← hU, Finset.mem_disjUnion]
      have ha1 : a ∉ W₁ := fun hc => ha ((hmem a).2 (Or.inl hc))
      have ha2 : a ∉ W₂ := fun hc => ha ((hmem a).2 (Or.inr hc))
      by_cases hak : a ∈ N k
      · have hd : Disjoint (Finset.cons a W₁ ha1) W₂ := by
          rw [Finset.disjoint_left]
          intro j hj
          rcases Finset.mem_cons.1 hj with rfl | hj
          · exact ha2
          · exact Finset.disjoint_left.1 h hj
        refine ⟨Finset.cons a W₁ ha1, W₂, hd, ?_, ?_, h2⟩
        · ext j
          simp only [Finset.mem_disjUnion, Finset.mem_cons, hmem]
          tauto
        · intro j hj
          rcases Finset.mem_cons.1 hj with rfl | hj
          · exact hak
          · exact h1 j hj
      · have hd : Disjoint W₁ (Finset.cons a W₂ ha2) := by
          rw [Finset.disjoint_left]
          intro j hj
          simp only [Finset.mem_cons, not_or]
          exact ⟨fun hja => ha1 (hja ▸ hj), Finset.disjoint_left.1 h hj⟩
        refine ⟨W₁, Finset.cons a W₂ ha2, hd, ?_, h1, ?_⟩
        · ext j
          simp only [Finset.mem_disjUnion, Finset.mem_cons, hmem]
          tauto
        · intro j hj
          rcases Finset.mem_cons.1 hj with rfl | hj
          · exact hak
          · exact h2 j hj
  have main : ∀ n : ℕ, ∀ (k : ι) (W : Finset ι), W.card ≤ n → k ∉ W →
      (μ (A k ∩ B W)).toReal ≤ x k * (μ (B W)).toReal := by
    intro n
    induction n with
    | zero =>
      intro k W hcard _
      have hW : W = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
      subst hW
      rw [hBempty, Set.inter_univ, measure_univ, ENNReal.toReal_one, mul_one]
      calc (μ (A k)).toReal ≤ x k * ∏ j ∈ N k, (1 - x j) := hbound k
        _ ≤ x k * 1 := mul_le_mul_of_nonneg_left
              (Finset.prod_le_one (fun j _ => hx1' j) (fun j _ => hx1'' j)) (hx₀ k)
        _ = x k := mul_one _
    | succ n ih =>
      have chain : ∀ (T V : Finset ι) (h : Disjoint T V), T.card + V.card ≤ n + 1 →
          (∏ j ∈ T, (1 - x j)) * (μ (B V)).toReal ≤ (μ (B (T.disjUnion V h))).toReal := by
        intro T
        induction T using Finset.cons_induction with
        | empty =>
          intro V h _
          rw [Finset.prod_empty, one_mul, Finset.empty_disjUnion]
        | cons a T' ha ihT =>
          intro V h hc
          rw [Finset.card_cons] at hc
          have hT'V : Disjoint T' V :=
            Finset.disjoint_left.2 fun j hj =>
              Finset.disjoint_left.1 h (Finset.mem_cons.2 (Or.inr hj))
          have haW : a ∉ T'.disjUnion V hT'V := by
            simp only [Finset.mem_disjUnion, not_or]
            exact ⟨ha, Finset.disjoint_left.1 h (Finset.mem_cons.2 (Or.inl rfl))⟩
          have hcard' : (T'.disjUnion V hT'V).card ≤ n := by
            rw [Finset.card_disjUnion]; omega
          have heq : (Finset.cons a T' ha).disjUnion V h
              = Finset.cons a (T'.disjUnion V hT'V) haW := by
            ext j
            simp only [Finset.mem_disjUnion, Finset.mem_cons]
            tauto
          have hstep := ih a (T'.disjUnion V hT'V) hcard' haW
          have hrec := ihT V hT'V (by omega)
          rw [heq, hBcompl, Finset.prod_cons]
          have e1 : (1 - x a) * ((∏ j ∈ T', (1 - x j)) * (μ (B V)).toReal)
              ≤ (1 - x a) * (μ (B (T'.disjUnion V hT'V))).toReal :=
            mul_le_mul_of_nonneg_left hrec (hx1' a)
          linarith [e1, hstep]
      intro k W hcard hkW
      obtain ⟨W₁, W₂, hd, hU, h1, h2⟩ := hsplit k W
      have hsub2 : W₂ ⊆ W := by
        intro j hj; rw [← hU]; exact Finset.mem_disjUnion.2 (Or.inr hj)
      have hchain := chain W₁ W₂ hd
        (by rw [← Finset.card_disjUnion W₁ W₂ hd, hU]; exact hcard)
      rw [hU] at hchain
      have hnegdep : μ (A k ∩ B W₂) ≤ μ (A k) * μ (B W₂) := by
        rw [hB]
        exact hN k W₂ (fun j hj => ⟨fun hjk => hkW (hjk ▸ hsub2 hj), h2 j hj⟩)
      have hmono : μ (A k ∩ B W) ≤ μ (A k ∩ B W₂) :=
        measure_mono (Set.inter_subset_inter (Set.Subset.refl _) (hBmono W₂ W hsub2))
      have key1 : (μ (A k ∩ B W)).toReal ≤ (μ (A k)).toReal * (μ (B W₂)).toReal := by
        rw [← ENNReal.toReal_mul]
        exact ENNReal.toReal_mono
          (ENNReal.mul_ne_top (measure_ne_top μ _) (measure_ne_top μ _)) (hmono.trans hnegdep)
      have key2 : (μ (A k)).toReal ≤ x k * ∏ j ∈ W₁, (1 - x j) :=
        (hbound k).trans (mul_le_mul_of_nonneg_left
          (Finset.prod_le_prod_of_subset_of_le_one (fun j hj => h1 j hj)
            (fun j _ => hx1' j) (fun j _ _ => hx1'' j)) (hx₀ k))
      calc (μ (A k ∩ B W)).toReal
          ≤ (μ (A k)).toReal * (μ (B W₂)).toReal := key1
        _ ≤ (x k * ∏ j ∈ W₁, (1 - x j)) * (μ (B W₂)).toReal :=
            mul_le_mul_of_nonneg_right key2 ENNReal.toReal_nonneg
        _ = x k * ((∏ j ∈ W₁, (1 - x j)) * (μ (B W₂)).toReal) := by ring
        _ ≤ x k * (μ (B W)).toReal := mul_le_mul_of_nonneg_left hchain (hx₀ k)
  have hfin := main S.card i S le_rfl hi
  simpa only [hB] using hfin

variable [Fintype ι]

/-- **The lopsided local lemma** (Zhao, Theorem 6.5.1).  Identical to `lovasz_local_lemma`
except that `IsDependencyGraph` is replaced by `IsNegativeDependencyGraph`. -/
theorem lopsided_local_lemma [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (N : ι → Finset ι) (hN : IsNegativeDependencyGraph μ A N)
    (x : ι → ℝ) (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
    (hbound : ∀ i, (μ (A i)).toReal ≤ x i * ∏ j ∈ N i, (1 - x j)) :
    ∏ i, (1 - x i) ≤ (μ (⋂ i, (A i)ᶜ)).toReal := by
  have key : ∀ S : Finset ι, ∏ j ∈ S, (1 - x j) ≤ (μ (⋂ j ∈ S, (A j)ᶜ)).toReal := by
    intro S
    induction S using Finset.cons_induction with
    | empty => simp
    | cons i S hi ih =>
      have hset : (⋂ j ∈ Finset.cons i S hi, (A j)ᶜ) = (⋂ j ∈ S, (A j)ᶜ) \ A i := by
        ext ω
        simp only [Set.mem_iInter, Finset.mem_cons, Set.mem_sdiff, Set.mem_compl_iff,
          forall_eq_or_imp]
        tauto
      have hadd : μ ((⋂ j ∈ S, (A j)ᶜ) ∩ A i) + μ ((⋂ j ∈ S, (A j)ᶜ) \ A i)
          = μ (⋂ j ∈ S, (A j)ᶜ) := measure_inter_add_sdiff _ (hA i)
      have hreal : (μ ((⋂ j ∈ S, (A j)ᶜ) \ A i)).toReal
          = (μ (⋂ j ∈ S, (A j)ᶜ)).toReal - (μ (A i ∩ ⋂ j ∈ S, (A j)ᶜ)).toReal := by
        rw [← hadd, ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _),
          Set.inter_comm]
        ring
      have hkey := measure_inter_biInter_compl_le_of_negativeDependency A hA N hN x hx₀ hx₁
        hbound i S hi
      have hnonneg : (0 : ℝ) ≤ 1 - x i := by linarith [hx₁ i]
      rw [Finset.prod_cons, hset, hreal]
      nlinarith [mul_le_mul_of_nonneg_left ih hnonneg]
  have h := key Finset.univ
  simpa using h

/-- **The lopsided local lemma, symmetric form** (Zhao, Corollary 6.5.2), at the usual weight
`x i = 1 / (d + 1)`. -/
theorem lopsided_local_lemma_symmetric [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (N : ι → Finset ι) (hN : IsNegativeDependencyGraph μ A N)
    {p : ℝ} {d : ℕ} (hp : ∀ i, (μ (A i)).toReal ≤ p)
    (hd : ∀ i, (N i).card ≤ d)
    (h : Real.exp 1 * p * (d + 1) ≤ 1) :
    0 < (μ (⋂ i, (A i)ᶜ)).toReal := by
  -- Take every weight to be `1 / (d + 2)`.  The hypothesis of Theorem 6.5.1 then amounts to
  -- `(1 + 1 / (d + 1)) ^ (d + 1) ≤ e`, which `1 + x ≤ exp x` supplies; unlike `1 / (d + 1)` this
  -- weight is admissible at `d = 0` as well.
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
  -- `hd` only bounds `(N i).card` from above, so the product over `N i` is compared with the
  -- `d`-fold power by monotonicity of `y ↦ y ^ n` on `[0, 1]`.
  have hbound : ∀ i, (μ (A i)).toReal
      ≤ 1 / ((d:ℝ) + 2) * ∏ _j ∈ N i, (1 - 1 / ((d:ℝ) + 2)) := by
    intro i
    rw [Finset.prod_const]
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
  have hmain := lopsided_local_lemma A hA N hN (fun _ => 1 / ((d:ℝ) + 2))
    (fun _ => ht₀) (fun _ => ht₁) hbound
  have hpos : (0:ℝ) < ∏ _i : ι, (1 - 1 / ((d:ℝ) + 2)) :=
    Finset.prod_pos fun i _ => by rw [h1t]; positivity
  linarith

end ProbMethodCombinatorics
