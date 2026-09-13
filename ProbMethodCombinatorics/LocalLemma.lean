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

omit [Fintype ι] in
/-- **The conditional bound of the local lemma** (Zhao, Theorem 6.1.9, equation (6.1)): under the
hypotheses of `lovasz_local_lemma`, for every `i` and every finite set `S` of indices avoiding
`i`, the event `A i` has conditional probability at most `x i` given that no `A j` with `j ∈ S`
occurs.

Stated in product form, `ℙ(A i ∩ ⋂_{j ∈ S} (A j)ᶜ) ≤ x i * ℙ(⋂_{j ∈ S} (A j)ᶜ)`, which is
equivalent to `ℙ(A i | ⋂_{j ∈ S} (A j)ᶜ) ≤ x i` whenever the conditioning event has positive
measure and is automatically true when it is null.  The book proves it by induction on `S.card`,
splitting `S` into the part inside `N i` and the part outside: the outside part is handled by
`IsDependencyGraph`, the inside part by expanding along a chain and applying the induction
hypothesis to each factor. -/
theorem measure_inter_biInter_compl_le [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (N : ι → Finset ι) (hN : IsDependencyGraph μ A N)
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
      have hpat : pattern A W₂ (fun _ => false) = B W₂ := by
        rw [hB]; simp [pattern]
      have hindepeq : μ (A k ∩ B W₂) = μ (A k) * μ (B W₂) := by
        have := hN k W₂ (fun j hj => ⟨fun hjk => hkW (hjk ▸ hsub2 hj), h2 j hj⟩)
          (fun _ => false)
        rwa [hpat] at this
      have hmono : μ (A k ∩ B W) ≤ μ (A k ∩ B W₂) :=
        measure_mono (Set.inter_subset_inter (Set.Subset.refl _) (hBmono W₂ W hsub2))
      have key1 : (μ (A k ∩ B W)).toReal ≤ (μ (A k)).toReal * (μ (B W₂)).toReal := by
        rw [← ENNReal.toReal_mul, ← hindepeq]
        exact ENNReal.toReal_mono (measure_ne_top μ _) hmono
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

/-- **Lovász local lemma, general form** (Zhao, Theorem 6.1.9; Erdős–Lovász 1975).  If weights
`x i ∈ [0, 1)` satisfy `ℙ(A i) ≤ x i * ∏_{j ∈ N i} (1 - x j)`, then the probability that no
`A i` occurs is at least `∏ i, (1 - x i)`. -/
theorem lovasz_local_lemma [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (N : ι → Finset ι) (hN : IsDependencyGraph μ A N)
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
      have hkey := measure_inter_biInter_compl_le A hA N hN x hx₀ hx₁ hbound i S hi
      have hnonneg : (0 : ℝ) ≤ 1 - x i := by linarith [hx₁ i]
      rw [Finset.prod_cons, hset, hreal]
      nlinarith [mul_le_mul_of_nonneg_left ih hnonneg]
  have h := key Finset.univ
  simpa using h

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
  sorry

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
