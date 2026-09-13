import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
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

/-- **Weierstrass's product inequality**: for weights `y j` lying in `[0, 1]`, the product of the
`1 - y j` over a finite set is at least `1 - ∑ y j`. -/
theorem one_sub_sum_le_prod_one_sub {κ : Type*} (y : κ → ℝ) (s : Finset κ)
    (hy₀ : ∀ j ∈ s, 0 ≤ y j) (hy₁ : ∀ j ∈ s, y j ≤ 1) :
    1 - ∑ j ∈ s, y j ≤ ∏ j ∈ s, (1 - y j) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have hmem : ∀ j ∈ s, j ∈ Finset.cons a s ha := fun j hj => Finset.mem_cons.2 (Or.inr hj)
    have hamem : a ∈ Finset.cons a s ha := Finset.mem_cons.2 (Or.inl rfl)
    have hind := ih (fun j hj => hy₀ j (hmem j hj)) (fun j hj => hy₁ j (hmem j hj))
    have hS : (0 : ℝ) ≤ ∑ j ∈ s, y j := Finset.sum_nonneg fun j hj => hy₀ j (hmem j hj)
    have ha0 : (0 : ℝ) ≤ y a := hy₀ a hamem
    have ha1 : (0 : ℝ) ≤ 1 - y a := by linarith [hy₁ a hamem]
    have hmul : (1 - y a) * (1 - ∑ j ∈ s, y j) ≤ (1 - y a) * ∏ j ∈ s, (1 - y j) :=
      mul_le_mul_of_nonneg_left hind ha1
    rw [Finset.sum_cons, Finset.prod_cons]
    nlinarith [hmul, hS, ha0]

/-- **Lovász local lemma, small-neighbourhood form** (Zhao, Corollary 6.1.10): if every `A i` has
probability less than `1 / 2` and the probabilities in each neighbourhood sum to at most `1 / 4`,
then with positive probability none of the `A i` occur. -/
theorem lovasz_local_lemma_of_sum_le [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (N : ι → Finset ι) (hN : IsDependencyGraph μ A N)
    (hhalf : ∀ i, (μ (A i)).toReal < 1 / 2)
    (hsum : ∀ i, ∑ j ∈ N i, (μ (A j)).toReal ≤ 1 / 4) :
    0 < (μ (⋂ i, (A i)ᶜ)).toReal := by
  obtain ⟨x, hxdef⟩ : ∃ x : ι → ℝ, ∀ i, x i = 2 * (μ (A i)).toReal := ⟨_, fun _ => rfl⟩
  have hx₀ : ∀ i, 0 ≤ x i := fun i => by rw [hxdef]; positivity
  have hx₁ : ∀ i, x i < 1 := fun i => by rw [hxdef]; linarith [hhalf i]
  have hbound : ∀ i, (μ (A i)).toReal ≤ x i * ∏ j ∈ N i, (1 - x j) := by
    intro i
    have hW : 1 - ∑ j ∈ N i, x j ≤ ∏ j ∈ N i, (1 - x j) :=
      one_sub_sum_le_prod_one_sub x (N i) (fun j _ => hx₀ j) (fun j _ => (hx₁ j).le)
    have hsx : ∑ j ∈ N i, x j = 2 * ∑ j ∈ N i, (μ (A j)).toReal := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => hxdef j
    rw [hsx] at hW
    have hprod : (1 : ℝ) / 2 ≤ ∏ j ∈ N i, (1 - x j) := by linarith [hsum i]
    calc (μ (A i)).toReal = x i * (1 / 2) := by rw [hxdef i]; ring
      _ ≤ x i * ∏ j ∈ N i, (1 - x j) := mul_le_mul_of_nonneg_left hprod (hx₀ i)
  have hmain := lovasz_local_lemma A hA N hN x hx₀ hx₁ hbound
  have hpos : 0 < ∏ i, (1 - x i) := Finset.prod_pos fun i _ => by linarith [hx₁ i]
  linarith

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
  -- The uniform random two-colouring of `α`.
  set ν : Measure Bool := (2 : ENNReal)⁻¹ • (Measure.dirac true + Measure.dirac false) with hν
  have hνuniv : ν Set.univ = 1 := by
    rw [hν]
    simp only [Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
    rw [show (1 : ENNReal) + 1 = 2 from by norm_num]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  have : IsProbabilityMeasure ν := ⟨hνuniv⟩
  have hνsingle : ∀ b : Bool, ν {b} = (2 : ENNReal)⁻¹ := by
    intro b
    rw [hν]
    cases b <;> simp [Measure.smul_apply, Measure.add_apply]
  set μ : Measure (α → Bool) := Measure.pi (fun _ : α => ν) with hμ
  have : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  -- The probability that a colouring is constant on a given set of vertices.
  have hcyl : ∀ (T : Finset α) (b : Bool),
      μ {x : α → Bool | ∀ u ∈ T, x u = b} = (2 : ENNReal)⁻¹ ^ T.card := by
    intro T b
    have hset : {x : α → Bool | ∀ u ∈ T, x u = b}
        = Set.univ.pi (fun a => if a ∈ T then ({b} : Set Bool) else Set.univ) := by
      ext x
      constructor
      · intro h a _
        show x a ∈ (if a ∈ T then ({b} : Set Bool) else Set.univ)
        by_cases ha : a ∈ T
        · rw [if_pos ha]; exact h a ha
        · rw [if_neg ha]; exact Set.mem_univ _
      · intro h u hu
        have hxu : x u ∈ (if u ∈ T then ({b} : Set Bool) else Set.univ) := h u (Set.mem_univ u)
        rw [if_pos hu] at hxu
        exact hxu
    rw [hset, hμ, Measure.pi_pi]
    have hrew : ∀ a : α, ν (if a ∈ T then ({b} : Set Bool) else Set.univ)
        = if a ∈ T then (2 : ENNReal)⁻¹ else 1 := by
      intro a
      by_cases ha : a ∈ T
      · rw [if_pos ha, if_pos ha]; exact hνsingle b
      · rw [if_neg ha, if_neg ha]; exact hνuniv
    rw [Finset.prod_congr rfl (fun a _ => hrew a), Finset.prod_ite_mem, Finset.univ_inter,
      Finset.prod_const]
  -- Events depending on disjoint sets of coordinates are independent.
  have key : ∀ (T : Finset α) (S₁ S₂ : Set (α → Bool)),
      (∀ x y : α → Bool, (∀ a ∈ T, x a = y a) → (x ∈ S₁ ↔ y ∈ S₁)) →
      (∀ x y : α → Bool, (∀ a ∉ T, x a = y a) → (x ∈ S₂ ↔ y ∈ S₂)) →
      μ (S₁ ∩ S₂) = μ S₁ * μ S₂ := by
    intro T S₁ S₂ h₁ h₂
    have hindep : iIndepFun (fun (a : α) (x : α → Bool) => x a) μ := by
      rw [hμ]
      exact ProbabilityTheory.iIndepFun_pi (μ := fun _ : α => ν)
        (X := fun _ : α => (id : Bool → Bool)) (fun _ => aemeasurable_id)
    have hind := hindep.indepFun_finset T Tᶜ disjoint_compl_right
      (fun a => measurable_pi_apply a)
    have e₁ : (fun (x : α → Bool) (u : { a // a ∈ T }) => x (u : α)) ⁻¹'
        ((fun (x : α → Bool) (u : { a // a ∈ T }) => x (u : α)) '' S₁) = S₁ := by
      refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
      rintro x ⟨y, hy, hxy⟩
      exact (h₁ y x (fun a ha => congrFun hxy ⟨a, ha⟩)).1 hy
    have e₂ : (fun (x : α → Bool) (u : { a // a ∈ Tᶜ }) => x (u : α)) ⁻¹'
        ((fun (x : α → Bool) (u : { a // a ∈ Tᶜ }) => x (u : α)) '' S₂) = S₂ := by
      refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
      rintro x ⟨y, hy, hxy⟩
      exact (h₂ y x (fun a ha => congrFun hxy ⟨a, Finset.mem_compl.2 ha⟩)).1 hy
    have hmul := hind.measure_inter_preimage_eq_mul
      ((fun (x : α → Bool) (u : { a // a ∈ T }) => x (u : α)) '' S₁)
      ((fun (x : α → Bool) (u : { a // a ∈ Tᶜ }) => x (u : α)) '' S₂)
      (Set.toFinite _).measurableSet (Set.toFinite _).measurableSet
    rw [e₁, e₂] at hmul
    exact hmul
  -- The bad events and their dependency graph.
  obtain ⟨A, hAdef⟩ : ∃ A : { e // e ∈ H } → Set (α → Bool), ∀ e x,
      (x ∈ A e ↔ ∀ u ∈ (e : Finset α), ∀ v ∈ (e : Finset α), x u = x v) :=
    ⟨_, fun _ _ => Iff.rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : { e // e ∈ H } → Finset { e // e ∈ H }, ∀ e f,
      (f ∈ N e ↔ f ≠ e ∧ ((e : Finset α) ∩ (f : Finset α)).Nonempty) :=
    ⟨fun e => Finset.univ.filter fun f => f ≠ e ∧ ((e : Finset α) ∩ (f : Finset α)).Nonempty,
      by simp⟩
  have hAmeas : ∀ i, MeasurableSet (A i) := fun _ => (Set.toFinite _).measurableSet
  -- Two colourings agreeing on an edge agree on whether that edge is monochromatic.
  have hAinv : ∀ (j : { e // e ∈ H }) (x y : α → Bool),
      (∀ a ∈ (j : Finset α), x a = y a) → (x ∈ A j ↔ y ∈ A j) := by
    intro j x y hxy
    rw [hAdef, hAdef]
    constructor
    · intro hx u hu v hv; rw [← hxy u hu, ← hxy v hv]; exact hx u hu v hv
    · intro hy u hu v hv; rw [hxy u hu, hxy v hv]; exact hy u hu v hv
  have hNdep : IsDependencyGraph μ A N := by
    intro i s hs g
    refine key (i : Finset α) (A i) (pattern A s g) (hAinv i) ?_
    intro x y hxy
    have hj : ∀ j ∈ s, (x ∈ (if g j then A j else (A j)ᶜ) ↔ y ∈ (if g j then A j else (A j)ᶜ)) := by
      intro j hjs
      obtain ⟨hjne, hjN⟩ := hs j hjs
      have hdisj : Disjoint (i : Finset α) (j : Finset α) := by
        by_contra hcon
        exact hjN ((hNdef i j).2 ⟨hjne, Finset.not_disjoint_iff_nonempty_inter.1 hcon⟩)
      have hiff := hAinv j x y fun a ha =>
        hxy a fun hai => (Finset.disjoint_left.1 hdisj hai) ha
      by_cases hg : g j
      · rw [if_pos hg]; exact hiff
      · rw [if_neg hg]; exact not_congr hiff
    simp only [pattern, Set.mem_iInter]
    exact ⟨fun h j hjs => (hj j hjs).1 (h j hjs), fun h j hjs => (hj j hjs).2 (h j hjs)⟩
  -- Each bad event has probability at most `2 ^ (1 - k)`.
  have hp : ∀ i, (μ (A i)).toReal ≤ 2 * ((2 : ℝ)⁻¹) ^ k := by
    intro i
    have hne : (i : Finset α).Nonempty := by
      rw [← Finset.card_pos, huniform _ i.2]; omega
    obtain ⟨u₀, hu₀⟩ := hne
    have hsub : A i ⊆ {x : α → Bool | ∀ u ∈ (i : Finset α), x u = true}
        ∪ {x : α → Bool | ∀ u ∈ (i : Finset α), x u = false} := by
      intro x hx
      rw [hAdef] at hx
      cases hb : x u₀
      · right; intro u hu; rw [hx u hu u₀ hu₀, hb]
      · left; intro u hu; rw [hx u hu u₀ hu₀, hb]
    have hle : μ (A i) ≤ 2 * (2 : ENNReal)⁻¹ ^ k := by
      calc μ (A i) ≤ μ ({x : α → Bool | ∀ u ∈ (i : Finset α), x u = true}
              ∪ {x : α → Bool | ∀ u ∈ (i : Finset α), x u = false}) := measure_mono hsub
        _ ≤ μ {x : α → Bool | ∀ u ∈ (i : Finset α), x u = true}
              + μ {x : α → Bool | ∀ u ∈ (i : Finset α), x u = false} := measure_union_le _ _
        _ = 2 * (2 : ENNReal)⁻¹ ^ k := by
            rw [hcyl _ true, hcyl _ false, huniform _ i.2]; ring
    have htop : (2 : ENNReal) * (2 : ENNReal)⁻¹ ^ k ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (by norm_num))
    have := ENNReal.toReal_mono htop hle
    simpa using this
  have hdcard : ∀ i, (N i).card ≤ d := by
    intro i
    refine le_trans (Finset.card_le_card_of_injOn (fun f => (f : Finset α)) ?_ ?_) (hd i i.2)
    · intro f hf
      rw [Finset.mem_coe, hNdef] at hf
      exact Finset.mem_coe.2 (Finset.mem_filter.2
        ⟨Finset.mem_erase.2 ⟨fun h => hf.1 (Subtype.ext h), f.2⟩, hf.2⟩)
    · intro f _ g _ h
      exact Subtype.ext h
  -- `e · 2 ^ (1 - k) · (d + 1) ≤ 1` is exactly the hypothesis `h`.
  have hcond : Real.exp 1 * (2 * ((2 : ℝ)⁻¹) ^ k) * ((d : ℝ) + 1) ≤ 1 := by
    obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [hm] at h ⊢
    rw [show m + 1 - 1 = m from rfl] at h
    have h2m : (0 : ℝ) < 2 ^ m := by positivity
    have hrw : (2 : ℝ) * ((2 : ℝ)⁻¹) ^ (m + 1) = ((2 : ℝ) ^ m)⁻¹ := by
      rw [inv_pow, pow_succ, mul_inv]
      field_simp
    rw [hrw, show Real.exp 1 * ((2 : ℝ) ^ m)⁻¹ * ((d : ℝ) + 1)
      = (Real.exp 1 * ((d : ℝ) + 1)) / 2 ^ m from by ring, div_le_one h2m]
    exact h
  have hpos := lovasz_local_lemma_symmetric A hAmeas N hNdep hp hdcard hcond
  -- A colouring avoiding every bad event exists.
  rcases Set.eq_empty_or_nonempty (⋂ i, (A i)ᶜ) with hempty | ⟨x, hx⟩
  · rw [hempty] at hpos; simp at hpos
  · refine ⟨x, fun e he => ?_⟩
    simp only [Set.mem_iInter, Set.mem_compl_iff] at hx
    by_contra hcon
    refine hx ⟨e, he⟩ ((hAdef ⟨e, he⟩ x).2 fun u hu v hv => ?_)
    by_contra hne
    exact hcon ⟨u, hu, v, hv, hne⟩

/-- **Zhao, Corollary 6.2.2**: for `k ≥ 9` every `k`-uniform `k`-regular hypergraph is
2-colourable, where `k`-regular means every vertex lies in exactly `k` edges.  (The statement
fails for `k = 2` and `k = 3` but holds for all `k ≥ 4`, by Thomassen 1992.) -/
theorem twoColorable_of_regular {k : ℕ} (hk : 9 ≤ k) {H : Finset (Finset α)}
    (huniform : ∀ e ∈ H, e.card = k)
    (hreg : ∀ v ∈ H.biUnion id, (H.filter fun e => v ∈ e).card = k) :
    TwoColorable H := by
  obtain ⟨d, hdeq⟩ : ∃ d : ℕ, d = k * (k - 1) := ⟨_, rfl⟩
  -- Every edge meets at most `k (k - 1)` others: each of its `k` vertices lies in `k - 1`
  -- further edges.
  have hcount : ∀ e ∈ H, ((H.erase e).filter fun f => (e ∩ f).Nonempty).card ≤ d := by
    intro e he
    have hsub : ((H.erase e).filter fun f => (e ∩ f).Nonempty)
        ⊆ e.biUnion (fun v => (H.filter fun f => v ∈ f).erase e) := by
      intro f hf
      simp only [Finset.mem_filter, Finset.mem_erase] at hf
      obtain ⟨⟨hfe, hfH⟩, v, hv⟩ := hf
      rw [Finset.mem_inter] at hv
      exact Finset.mem_biUnion.2 ⟨v, hv.1,
        Finset.mem_erase.2 ⟨hfe, Finset.mem_filter.2 ⟨hfH, hv.2⟩⟩⟩
    calc ((H.erase e).filter fun f => (e ∩ f).Nonempty).card
        ≤ (e.biUnion (fun v => (H.filter fun f => v ∈ f).erase e)).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ v ∈ e, ((H.filter fun f => v ∈ f).erase e).card := Finset.card_biUnion_le
      _ = ∑ _v ∈ e, (k - 1) := by
          refine Finset.sum_congr rfl fun v hv => ?_
          rw [Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨he, hv⟩),
            hreg v (Finset.mem_biUnion.2 ⟨e, he, hv⟩)]
      _ = d := by rw [Finset.sum_const, huniform e he, smul_eq_mul, hdeq]
  -- `6 (d + 1) ≤ 2 ^ k` for `k ≥ 9`, which is where the hypothesis on `k` is used.
  have harith : ∀ m : ℕ, 6 * ((m + 9) * (m + 8) + 1) ≤ 2 ^ (m + 9) := by
    intro m
    induction m with
    | zero => norm_num
    | succ n ih =>
      have hstep : (n + 1 + 9) * (n + 1 + 8) + 1 ≤ 2 * ((n + 9) * (n + 8) + 1) := by nlinarith
      calc 6 * ((n + 1 + 9) * (n + 1 + 8) + 1)
          ≤ 6 * (2 * ((n + 9) * (n + 8) + 1)) := Nat.mul_le_mul_left 6 hstep
        _ = 2 * (6 * ((n + 9) * (n + 8) + 1)) := by ring
        _ ≤ 2 * 2 ^ (n + 9) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1 + 9) := by ring
  have hnat : 6 * (d + 1) ≤ 2 ^ k := by
    rw [hdeq]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 9 := ⟨k - 9, by omega⟩
    rw [show m + 9 - 1 = m + 8 from by omega]
    exact harith m
  -- The uniform random two-colouring of `α`.
  set ν : Measure Bool := (2 : ENNReal)⁻¹ • (Measure.dirac true + Measure.dirac false) with hν
  have hνuniv : ν Set.univ = 1 := by
    rw [hν]
    simp only [Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
    rw [show (1 : ENNReal) + 1 = 2 from by norm_num]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  have : IsProbabilityMeasure ν := ⟨hνuniv⟩
  have hνsingle : ∀ b : Bool, ν {b} = (2 : ENNReal)⁻¹ := by
    intro b
    rw [hν]
    cases b <;> simp [Measure.smul_apply, Measure.add_apply]
  set μ : Measure (α → Bool) := Measure.pi (fun _ : α => ν) with hμ
  have : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  -- The probability that a colouring is constant on a given set of vertices.
  have hcyl : ∀ (T : Finset α) (b : Bool),
      μ {x : α → Bool | ∀ u ∈ T, x u = b} = (2 : ENNReal)⁻¹ ^ T.card := by
    intro T b
    have hset : {x : α → Bool | ∀ u ∈ T, x u = b}
        = Set.univ.pi (fun a => if a ∈ T then ({b} : Set Bool) else Set.univ) := by
      ext x
      constructor
      · intro h a _
        show x a ∈ (if a ∈ T then ({b} : Set Bool) else Set.univ)
        by_cases ha : a ∈ T
        · rw [if_pos ha]; exact h a ha
        · rw [if_neg ha]; exact Set.mem_univ _
      · intro h u hu
        have hxu : x u ∈ (if u ∈ T then ({b} : Set Bool) else Set.univ) := h u (Set.mem_univ u)
        rw [if_pos hu] at hxu
        exact hxu
    rw [hset, hμ, Measure.pi_pi]
    have hrew : ∀ a : α, ν (if a ∈ T then ({b} : Set Bool) else Set.univ)
        = if a ∈ T then (2 : ENNReal)⁻¹ else 1 := by
      intro a
      by_cases ha : a ∈ T
      · rw [if_pos ha, if_pos ha]; exact hνsingle b
      · rw [if_neg ha, if_neg ha]; exact hνuniv
    rw [Finset.prod_congr rfl (fun a _ => hrew a), Finset.prod_ite_mem, Finset.univ_inter,
      Finset.prod_const]
  -- Events depending on disjoint sets of coordinates are independent.
  have key : ∀ (T : Finset α) (S₁ S₂ : Set (α → Bool)),
      (∀ x y : α → Bool, (∀ a ∈ T, x a = y a) → (x ∈ S₁ ↔ y ∈ S₁)) →
      (∀ x y : α → Bool, (∀ a ∉ T, x a = y a) → (x ∈ S₂ ↔ y ∈ S₂)) →
      μ (S₁ ∩ S₂) = μ S₁ * μ S₂ := by
    intro T S₁ S₂ h₁ h₂
    have hindep : iIndepFun (fun (a : α) (x : α → Bool) => x a) μ := by
      rw [hμ]
      exact ProbabilityTheory.iIndepFun_pi (μ := fun _ : α => ν)
        (X := fun _ : α => (id : Bool → Bool)) (fun _ => aemeasurable_id)
    have hind := hindep.indepFun_finset T Tᶜ disjoint_compl_right
      (fun a => measurable_pi_apply a)
    have e₁ : (fun (x : α → Bool) (u : { a // a ∈ T }) => x (u : α)) ⁻¹'
        ((fun (x : α → Bool) (u : { a // a ∈ T }) => x (u : α)) '' S₁) = S₁ := by
      refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
      rintro x ⟨y, hy, hxy⟩
      exact (h₁ y x (fun a ha => congrFun hxy ⟨a, ha⟩)).1 hy
    have e₂ : (fun (x : α → Bool) (u : { a // a ∈ Tᶜ }) => x (u : α)) ⁻¹'
        ((fun (x : α → Bool) (u : { a // a ∈ Tᶜ }) => x (u : α)) '' S₂) = S₂ := by
      refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
      rintro x ⟨y, hy, hxy⟩
      exact (h₂ y x (fun a ha => congrFun hxy ⟨a, Finset.mem_compl.2 ha⟩)).1 hy
    have hmul := hind.measure_inter_preimage_eq_mul
      ((fun (x : α → Bool) (u : { a // a ∈ T }) => x (u : α)) '' S₁)
      ((fun (x : α → Bool) (u : { a // a ∈ Tᶜ }) => x (u : α)) '' S₂)
      (Set.toFinite _).measurableSet (Set.toFinite _).measurableSet
    rw [e₁, e₂] at hmul
    exact hmul
  -- The bad events and their dependency graph.
  obtain ⟨A, hAdef⟩ : ∃ A : { e // e ∈ H } → Set (α → Bool), ∀ e x,
      (x ∈ A e ↔ ∀ u ∈ (e : Finset α), ∀ v ∈ (e : Finset α), x u = x v) :=
    ⟨_, fun _ _ => Iff.rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : { e // e ∈ H } → Finset { e // e ∈ H }, ∀ e f,
      (f ∈ N e ↔ f ≠ e ∧ ((e : Finset α) ∩ (f : Finset α)).Nonempty) :=
    ⟨fun e => Finset.univ.filter fun f => f ≠ e ∧ ((e : Finset α) ∩ (f : Finset α)).Nonempty,
      by simp⟩
  have hAmeas : ∀ i, MeasurableSet (A i) := fun _ => (Set.toFinite _).measurableSet
  -- Two colourings agreeing on an edge agree on whether that edge is monochromatic.
  have hAinv : ∀ (j : { e // e ∈ H }) (x y : α → Bool),
      (∀ a ∈ (j : Finset α), x a = y a) → (x ∈ A j ↔ y ∈ A j) := by
    intro j x y hxy
    rw [hAdef, hAdef]
    constructor
    · intro hx u hu v hv; rw [← hxy u hu, ← hxy v hv]; exact hx u hu v hv
    · intro hy u hu v hv; rw [hxy u hu, hxy v hv]; exact hy u hu v hv
  have hNdep : IsDependencyGraph μ A N := by
    intro i s hs g
    refine key (i : Finset α) (A i) (pattern A s g) (hAinv i) ?_
    intro x y hxy
    have hj : ∀ j ∈ s, (x ∈ (if g j then A j else (A j)ᶜ) ↔ y ∈ (if g j then A j else (A j)ᶜ)) := by
      intro j hjs
      obtain ⟨hjne, hjN⟩ := hs j hjs
      have hdisj : Disjoint (i : Finset α) (j : Finset α) := by
        by_contra hcon
        exact hjN ((hNdef i j).2 ⟨hjne, Finset.not_disjoint_iff_nonempty_inter.1 hcon⟩)
      have hiff := hAinv j x y fun a ha =>
        hxy a fun hai => (Finset.disjoint_left.1 hdisj hai) ha
      by_cases hg : g j
      · rw [if_pos hg]; exact hiff
      · rw [if_neg hg]; exact not_congr hiff
    simp only [pattern, Set.mem_iInter]
    exact ⟨fun h j hjs => (hj j hjs).1 (h j hjs), fun h j hjs => (hj j hjs).2 (h j hjs)⟩
  -- Each bad event has probability at most `2 ^ (1 - k)`.
  have hp : ∀ i, (μ (A i)).toReal ≤ 2 * ((2 : ℝ)⁻¹) ^ k := by
    intro i
    have hne : (i : Finset α).Nonempty := by
      rw [← Finset.card_pos, huniform _ i.2]; omega
    obtain ⟨u₀, hu₀⟩ := hne
    have hsub : A i ⊆ {x : α → Bool | ∀ u ∈ (i : Finset α), x u = true}
        ∪ {x : α → Bool | ∀ u ∈ (i : Finset α), x u = false} := by
      intro x hx
      rw [hAdef] at hx
      cases hb : x u₀
      · right; intro u hu; rw [hx u hu u₀ hu₀, hb]
      · left; intro u hu; rw [hx u hu u₀ hu₀, hb]
    have hle : μ (A i) ≤ 2 * (2 : ENNReal)⁻¹ ^ k := by
      calc μ (A i) ≤ μ ({x : α → Bool | ∀ u ∈ (i : Finset α), x u = true}
              ∪ {x : α → Bool | ∀ u ∈ (i : Finset α), x u = false}) := measure_mono hsub
        _ ≤ μ {x : α → Bool | ∀ u ∈ (i : Finset α), x u = true}
              + μ {x : α → Bool | ∀ u ∈ (i : Finset α), x u = false} := measure_union_le _ _
        _ = 2 * (2 : ENNReal)⁻¹ ^ k := by
            rw [hcyl _ true, hcyl _ false, huniform _ i.2]; ring
    have htop : (2 : ENNReal) * (2 : ENNReal)⁻¹ ^ k ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (by norm_num))
    have := ENNReal.toReal_mono htop hle
    simpa using this
  have hdcard : ∀ i, (N i).card ≤ d := by
    intro i
    refine le_trans (Finset.card_le_card_of_injOn (fun f => (f : Finset α)) ?_ ?_) (hcount i i.2)
    · intro f hf
      rw [Finset.mem_coe, hNdef] at hf
      exact Finset.mem_coe.2 (Finset.mem_filter.2
        ⟨Finset.mem_erase.2 ⟨fun h => hf.1 (Subtype.ext h), f.2⟩, hf.2⟩)
    · intro f _ g _ h
      exact Subtype.ext h
  -- `e · 2 ^ (1 - k) · (d + 1) ≤ 1`.
  have hcond : Real.exp 1 * (2 * ((2 : ℝ)⁻¹) ^ k) * ((d : ℝ) + 1) ≤ 1 := by
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    have hcast : (6 : ℝ) * ((d : ℝ) + 1) ≤ 2 ^ k := by exact_mod_cast hnat
    have hd1 : (0 : ℝ) ≤ (d : ℝ) + 1 := by positivity
    rw [inv_pow, show Real.exp 1 * (2 * ((2 : ℝ) ^ k)⁻¹) * ((d : ℝ) + 1)
      = (Real.exp 1 * 2 * ((d : ℝ) + 1)) / 2 ^ k from by ring, div_le_one h2k]
    nlinarith [Real.exp_one_lt_three, hcast, hd1]
  have hpos := lovasz_local_lemma_symmetric A hAmeas N hNdep hp hdcard hcond
  -- A colouring avoiding every bad event exists.
  rcases Set.eq_empty_or_nonempty (⋂ i, (A i)ᶜ) with hempty | ⟨x, hx⟩
  · rw [hempty] at hpos; simp at hpos
  · refine ⟨x, fun e he => ?_⟩
    simp only [Set.mem_iInter, Set.mem_compl_iff] at hx
    by_contra hcon
    refine hx ⟨e, he⟩ ((hAdef ⟨e, he⟩ x).2 fun u hu v hv => ?_)
    by_contra hne
    exact hcon ⟨u, hu, v, hv, hne⟩

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
