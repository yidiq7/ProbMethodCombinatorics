import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Compactness.Compact
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

section UniformColoring

/-!
### The uniform random two-colouring

Every application of the local lemma in this chapter randomly two-colours a finite set and
asks which events are independent.  The measure and its two working facts are collected here
rather than rebuilt at each call site.  The index type is arbitrary: the applications colour
vertices (`α`), the Ramsey bound colours edges (`Finset (Fin n)`).
-/

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The fair coin on `Bool`. -/
noncomputable def fairCoin : Measure Bool :=
  (2 : ENNReal)⁻¹ • (Measure.dirac true + Measure.dirac false)

theorem fairCoin_univ : fairCoin Set.univ = 1 := by
  rw [fairCoin]
  simp only [Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [show (1 : ENNReal) + 1 = 2 from by norm_num]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

instance : IsProbabilityMeasure fairCoin := ⟨fairCoin_univ⟩

theorem fairCoin_singleton (b : Bool) : fairCoin {b} = (2 : ENNReal)⁻¹ := by
  rw [fairCoin]; cases b <;> simp [Measure.smul_apply, Measure.add_apply]

/-- The uniform probability measure on two-colourings of `κ`: each coordinate is an
independent fair coin. -/
noncomputable def uniformColoring (κ : Type*) [Fintype κ] : Measure (κ → Bool) :=
  Measure.pi fun _ : κ => fairCoin

instance : IsProbabilityMeasure (uniformColoring κ) := by
  rw [uniformColoring]; infer_instance

/-- A uniform random colouring is constant on a given finite set with probability `2 ^ -|T|`. -/
theorem uniformColoring_const (T : Finset κ) (b : Bool) :
    uniformColoring κ {x : κ → Bool | ∀ u ∈ T, x u = b} = (2 : ENNReal)⁻¹ ^ T.card := by
  have hset : {x : κ → Bool | ∀ u ∈ T, x u = b}
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
  rw [hset, uniformColoring, Measure.pi_pi]
  have hrew : ∀ a : κ, fairCoin (if a ∈ T then ({b} : Set Bool) else Set.univ)
      = if a ∈ T then (2 : ENNReal)⁻¹ else 1 := by
    intro a
    by_cases ha : a ∈ T
    · rw [if_pos ha, if_pos ha]; exact fairCoin_singleton b
    · rw [if_neg ha, if_neg ha]; exact fairCoin_univ
  rw [Finset.prod_congr rfl (fun a _ => hrew a), Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_const]

/-- **Events determined by disjoint sets of coordinates are independent** (Setup 6.1.5), for an
arbitrary finite product of probability measures.

`S₁` may depend only on the coordinates in `T`, and `S₂` only on those outside it.  The two
uniform measures this chapter uses — `uniformColoring` on `κ → Bool` and the choice measure on
`ι → Fin n` — are both instances, and both call it rather than repeating the argument.

Finiteness of the fibres is what makes every set measurable, which is what
`IndepFun.measure_inter_preimage_eq_mul` needs; `S₁` and `S₂` therefore carry no measurability
hypothesis. -/
theorem measure_pi_inter_eq_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ i, Finite (α i)] [∀ i, MeasurableSingletonClass (α i)]
    (ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)]
    (T : Finset ι) (S₁ S₂ : Set (∀ i, α i))
    (h₁ : ∀ x y : ∀ i, α i, (∀ a ∈ T, x a = y a) → (x ∈ S₁ ↔ y ∈ S₁))
    (h₂ : ∀ x y : ∀ i, α i, (∀ a ∉ T, x a = y a) → (x ∈ S₂ ↔ y ∈ S₂)) :
    Measure.pi ν (S₁ ∩ S₂) = Measure.pi ν S₁ * Measure.pi ν S₂ := by
  have hindep : iIndepFun (fun (a : ι) (x : ∀ i, α i) => x a) (Measure.pi ν) :=
    ProbabilityTheory.iIndepFun_pi (μ := ν) (X := fun i => (id : α i → α i))
      (fun _ => aemeasurable_id)
  have hind := hindep.indepFun_finset T Tᶜ disjoint_compl_right
    (fun a => measurable_pi_apply a)
  have e₁ : (fun (x : ∀ i, α i) (w : { a // a ∈ T }) => x (w : ι)) ⁻¹'
      ((fun (x : ∀ i, α i) (w : { a // a ∈ T }) => x (w : ι)) '' S₁) = S₁ := by
    refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
    rintro x ⟨y, hy, hxy⟩
    exact (h₁ y x (fun a ha => congrFun hxy ⟨a, ha⟩)).1 hy
  have e₂ : (fun (x : ∀ i, α i) (w : { a // a ∈ Tᶜ }) => x (w : ι)) ⁻¹'
      ((fun (x : ∀ i, α i) (w : { a // a ∈ Tᶜ }) => x (w : ι)) '' S₂) = S₂ := by
    refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
    rintro x ⟨y, hy, hxy⟩
    exact (h₂ y x (fun a ha => congrFun hxy ⟨a, Finset.mem_compl.2 ha⟩)).1 hy
  have hmul := hind.measure_inter_preimage_eq_mul
    ((fun (x : ∀ i, α i) (w : { a // a ∈ T }) => x (w : ι)) '' S₁)
    ((fun (x : ∀ i, α i) (w : { a // a ∈ Tᶜ }) => x (w : ι)) '' S₂)
    (Set.toFinite _).measurableSet (Set.toFinite _).measurableSet
  rw [e₁, e₂] at hmul
  exact hmul

/-- **Events determined by disjoint sets of coordinates are independent.**  This is Setup 6.1.5
specialized to a uniform two-colouring: `S₁` may depend only on the coordinates in `T`, and `S₂`
only on those outside it. -/
theorem uniformColoring_inter_eq_mul (T : Finset κ) (S₁ S₂ : Set (κ → Bool))
    (h₁ : ∀ x y : κ → Bool, (∀ a ∈ T, x a = y a) → (x ∈ S₁ ↔ y ∈ S₁))
    (h₂ : ∀ x y : κ → Bool, (∀ a ∉ T, x a = y a) → (x ∈ S₂ ↔ y ∈ S₂)) :
    uniformColoring κ (S₁ ∩ S₂) = uniformColoring κ S₁ * uniformColoring κ S₂ :=
  measure_pi_inter_eq_mul (fun _ : κ => fairCoin) T S₁ S₂ h₁ h₂

end UniformColoring

section Applications

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A uniform random two-colouring makes a nonempty set `e` monochromatic with probability at
most `2 ^ (1 - |e|)`: the event is covered by the two constant patterns on `e`, each of
probability `2 ^ -|e|`. -/
private theorem uniformColoring_monochromatic_toReal_le (e : Finset α) (he : 1 ≤ e.card) :
    (uniformColoring α {x : α → Bool | ∀ u ∈ e, ∀ v ∈ e, x u = x v}).toReal
      ≤ 1 / 2 ^ (e.card - 1) := by
  obtain ⟨u₀, hu₀⟩ : e.Nonempty := Finset.card_pos.1 he
  have hsub : {x : α → Bool | ∀ u ∈ e, ∀ v ∈ e, x u = x v}
      ⊆ {x : α → Bool | ∀ u ∈ e, x u = true} ∪ {x : α → Bool | ∀ u ∈ e, x u = false} := by
    intro x hx
    cases hb : x u₀
    · right; intro u hu; rw [hx u hu u₀ hu₀, hb]
    · left; intro u hu; rw [hx u hu u₀ hu₀, hb]
  have hle : uniformColoring α {x : α → Bool | ∀ u ∈ e, ∀ v ∈ e, x u = x v}
      ≤ 2 * (2 : ENNReal)⁻¹ ^ e.card :=
    calc uniformColoring α {x : α → Bool | ∀ u ∈ e, ∀ v ∈ e, x u = x v}
        ≤ uniformColoring α ({x : α → Bool | ∀ u ∈ e, x u = true}
            ∪ {x : α → Bool | ∀ u ∈ e, x u = false}) := measure_mono hsub
      _ ≤ uniformColoring α {x : α → Bool | ∀ u ∈ e, x u = true}
            + uniformColoring α {x : α → Bool | ∀ u ∈ e, x u = false} := measure_union_le _ _
      _ = 2 * (2 : ENNReal)⁻¹ ^ e.card := by
          rw [uniformColoring_const _ true, uniformColoring_const _ false]; ring
  have htop : (2 : ENNReal) * (2 : ENNReal)⁻¹ ^ e.card ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (by norm_num))
  have hreal : (uniformColoring α {x : α → Bool | ∀ u ∈ e, ∀ v ∈ e, x u = x v}).toReal
      ≤ 2 * ((2 : ℝ)⁻¹) ^ e.card := by simpa using ENNReal.toReal_mono htop hle
  have hsplit : (2 : ℝ) ^ e.card = 2 ^ (e.card - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  have hval : 2 * ((2 : ℝ)⁻¹) ^ e.card = 1 / 2 ^ (e.card - 1) := by
    have hpos : (0 : ℝ) < 2 ^ (e.card - 1) := by positivity
    rw [inv_pow, hsplit]
    field_simp
  rwa [hval] at hreal

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
  have hNdep : IsDependencyGraph (uniformColoring α) A N := by
    intro i s hs g
    refine uniformColoring_inter_eq_mul (i : Finset α) (A i) (pattern A s g) (hAinv i) ?_
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
  have hp : ∀ i, (uniformColoring α (A i)).toReal ≤ 2 * ((2 : ℝ)⁻¹) ^ k := by
    intro i
    have hcard : (i : Finset α).card = k := huniform _ i.2
    have hAeq : A i = {x : α → Bool | ∀ u ∈ (i : Finset α), ∀ v ∈ (i : Finset α), x u = x v} :=
      Set.ext fun x => hAdef i x
    rw [hAeq]
    refine (uniformColoring_monochromatic_toReal_le _ (by omega)).trans (le_of_eq ?_)
    have hsplit : (2 : ℝ) ^ k = 2 ^ (k - 1) * 2 := by rw [← pow_succ]; congr 1; omega
    rw [hcard, inv_pow, hsplit]
    have hpos : (0 : ℝ) < 2 ^ (k - 1) := by positivity
    field_simp
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
  -- Every edge meets at most `k (k - 1)` others: each of its `k` vertices lies in `k - 1`
  -- further edges.
  have hcount : ∀ e ∈ H, ((H.erase e).filter fun f => (e ∩ f).Nonempty).card ≤ k * (k - 1) := by
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
      _ = k * (k - 1) := by rw [Finset.sum_const, huniform e he, smul_eq_mul]
  -- `6 (k (k - 1) + 1) ≤ 2 ^ k` for `k ≥ 9`, which is where the hypothesis on `k` is used.
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
  -- Since `2 e < 6`, the hypothesis of Theorem 6.2.1 holds with `d = k (k - 1)`.
  refine twoColorable_of_inter_card_le (by omega) huniform hcount ?_
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 9 := ⟨k - 9, by omega⟩
  rw [show m + 9 - 1 = m + 8 from by omega]
  have hcast : (6 : ℝ) * (((m : ℝ) + 9) * ((m : ℝ) + 8) + 1) ≤ 2 * 2 ^ (m + 8) := by
    have h2 : (2 : ℝ) * 2 ^ (m + 8) = 2 ^ (m + 9) := by ring
    rw [h2]
    exact_mod_cast harith m
  have hpos : (0 : ℝ) ≤ ((m : ℝ) + 9) * ((m : ℝ) + 8) + 1 := by positivity
  push_cast
  nlinarith [Real.exp_one_lt_three, hcast, hpos]

/-- **Spencer 1977** (Zhao, Theorem 1.1.9): the local lemma improves the Ramsey lower bound of
Theorem 1.1.2 by a further constant factor, giving the best bound on `R(k, k)` known to date.

The hypothesis is the book's `((k choose 2)(n choose (k-2)) + 1) 2 ^ (1 - (k choose 2)) < 1/e`
with denominators cleared. -/
theorem lt_ramseyNumber_of_local_lemma (n k : ℕ) (hk : 2 ≤ k)
    (h : Real.exp 1 * (2 * ((k.choose 2 * n.choose (k - 2) : ℕ) : ℝ) + 2)
      ≤ 2 ^ (k.choose 2)) :
    n < ramseyNumber k := by
  -- Colour the edges of `K n` independently and uniformly at random.  An edge is a two-element
  -- subset of `Fin n`, so a colouring is a function on `Finset (Fin n)`; restricting it to
  -- two-element sets gives an automatically symmetric edge colouring.
  -- The bad events: `A S` says the `k`-set `S` spans a monochromatic clique.
  obtain ⟨A, hAdef⟩ : ∃ A : {S : Finset (Fin n) // S.card = k} → Set (Finset (Fin n) → Bool),
      ∀ S x, (x ∈ A S ↔ ∀ e ∈ (S : Finset (Fin n)).powersetCard 2,
        ∀ f ∈ (S : Finset (Fin n)).powersetCard 2, x e = x f) := ⟨_, fun _ _ => Iff.rfl⟩
  -- Two `k`-sets are dependent only when they share at least two vertices, hence an edge.
  obtain ⟨N, hNdef⟩ : ∃ N : {S : Finset (Fin n) // S.card = k} →
      Finset {S : Finset (Fin n) // S.card = k}, ∀ S T,
      (T ∈ N S ↔ T ≠ S ∧ 2 ≤ ((S : Finset (Fin n)) ∩ (T : Finset (Fin n))).card) :=
    ⟨fun S => Finset.univ.filter fun T =>
      T ≠ S ∧ 2 ≤ ((S : Finset (Fin n)) ∩ (T : Finset (Fin n))).card, by simp⟩
  have hAmeas : ∀ i, MeasurableSet (A i) := fun _ => (Set.toFinite _).measurableSet
  have hAinv : ∀ (j : {S : Finset (Fin n) // S.card = k}) (x y : Finset (Fin n) → Bool),
      (∀ a ∈ (j : Finset (Fin n)).powersetCard 2, x a = y a) → (x ∈ A j ↔ y ∈ A j) := by
    intro j x y hxy
    rw [hAdef, hAdef]
    constructor
    · intro hx e he f hf; rw [← hxy e he, ← hxy f hf]; exact hx e he f hf
    · intro hy e he f hf; rw [hxy e he, hxy f hf]; exact hy e he f hf
  have hNdep : IsDependencyGraph (uniformColoring (Finset (Fin n))) A N := by
    intro i s hs g
    refine uniformColoring_inter_eq_mul ((i : Finset (Fin n)).powersetCard 2) (A i)
      (pattern A s g) (hAinv i) ?_
    intro x y hxy
    have hj : ∀ j ∈ s,
        (x ∈ (if g j then A j else (A j)ᶜ) ↔ y ∈ (if g j then A j else (A j)ᶜ)) := by
      intro j hjs
      obtain ⟨hjne, hjN⟩ := hs j hjs
      have hdisj : ∀ e ∈ (j : Finset (Fin n)).powersetCard 2,
          e ∉ (i : Finset (Fin n)).powersetCard 2 := by
        intro e hej hei
        refine hjN ((hNdef i j).2 ⟨hjne, ?_⟩)
        rw [Finset.mem_powersetCard] at hei hej
        calc 2 = e.card := hei.2.symm
          _ ≤ ((i : Finset (Fin n)) ∩ (j : Finset (Fin n))).card :=
              Finset.card_le_card (Finset.subset_inter hei.1 hej.1)
      have hiff := hAinv j x y fun a ha => hxy a (hdisj a ha)
      by_cases hg : g j
      · rw [if_pos hg]; exact hiff
      · rw [if_neg hg]; exact not_congr hiff
    simp only [pattern, Set.mem_iInter]
    exact ⟨fun hh j hjs => (hj j hjs).1 (hh j hjs), fun hh j hjs => (hj j hjs).2 (hh j hjs)⟩
  -- Each bad event has probability at most `2 ^ (1 - (k choose 2))`.
  have hKpos : 0 < k.choose 2 := Nat.choose_pos hk
  have hp : ∀ i, (uniformColoring (Finset (Fin n)) (A i)).toReal
      ≤ 2 * ((2 : ℝ)⁻¹) ^ (k.choose 2) := by
    intro i
    have hcardT : ((i : Finset (Fin n)).powersetCard 2).card = k.choose 2 := by
      rw [Finset.card_powersetCard, i.2]
    have hne : ((i : Finset (Fin n)).powersetCard 2).Nonempty := by
      rw [← Finset.card_pos, hcardT]; exact hKpos
    obtain ⟨e₀, he₀⟩ := hne
    have hsub : A i ⊆ {x : Finset (Fin n) → Bool |
          ∀ u ∈ (i : Finset (Fin n)).powersetCard 2, x u = true}
        ∪ {x : Finset (Fin n) → Bool |
          ∀ u ∈ (i : Finset (Fin n)).powersetCard 2, x u = false} := by
      intro x hx
      rw [hAdef] at hx
      cases hb : x e₀
      · right; intro u hu; rw [hx u hu e₀ he₀, hb]
      · left; intro u hu; rw [hx u hu e₀ he₀, hb]
    have hle : uniformColoring (Finset (Fin n)) (A i)
        ≤ 2 * (2 : ENNReal)⁻¹ ^ (k.choose 2) := by
      refine (measure_mono hsub).trans ((measure_union_le _ _).trans (le_of_eq ?_))
      rw [uniformColoring_const _ true, uniformColoring_const _ false, hcardT]
      ring
    have htop : (2 : ENNReal) * (2 : ENNReal)⁻¹ ^ (k.choose 2) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (by norm_num))
    have := ENNReal.toReal_mono htop hle
    simpa using this
  -- The dependency degree: a `k`-set meeting `S` in at least two vertices is determined by an
  -- edge inside `S` together with its remaining `k - 2` vertices.
  have hdcard : ∀ S : {S : Finset (Fin n) // S.card = k},
      (N S).card ≤ k.choose 2 * n.choose (k - 2) := by
    intro S
    have himg : ((N S).image
        (fun T : {S : Finset (Fin n) // S.card = k} => (T : Finset (Fin n)))).card
        = (N S).card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    have hsub : (N S).image (fun T : {S : Finset (Fin n) // S.card = k} => (T : Finset (Fin n))) ⊆
        ((S : Finset (Fin n)).powersetCard 2).biUnion fun P =>
          ((univ : Finset (Fin n)).powersetCard (k - 2)).image fun R => P ∪ R := by
      intro U hU
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hU
      obtain ⟨hne, hcard⟩ := (hNdef S T).1 hT
      obtain ⟨P, hPsub, hPcard⟩ :=
        Finset.exists_subset_card_eq hcard
      have hPT : P ⊆ (T : Finset (Fin n)) := hPsub.trans Finset.inter_subset_right
      refine Finset.mem_biUnion.2 ⟨P, Finset.mem_powersetCard.2
        ⟨hPsub.trans Finset.inter_subset_left, hPcard⟩, Finset.mem_image.2
        ⟨(T : Finset (Fin n)) \ P, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, ?_⟩, ?_⟩⟩
      · rw [Finset.card_sdiff_of_subset hPT, hPcard, T.2]
      · exact Finset.union_sdiff_of_subset hPT
    calc (N S).card = ((N S).image
          (fun T : {S : Finset (Fin n) // S.card = k} => (T : Finset (Fin n)))).card :=
        himg.symm
      _ ≤ (((S : Finset (Fin n)).powersetCard 2).biUnion fun P =>
            ((univ : Finset (Fin n)).powersetCard (k - 2)).image fun R => P ∪ R).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ _P ∈ (S : Finset (Fin n)).powersetCard 2, n.choose (k - 2) := by
          refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun P _ => ?_)
          refine le_trans Finset.card_image_le (le_of_eq ?_)
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      _ = k.choose 2 * n.choose (k - 2) := by
          rw [Finset.sum_const, Finset.card_powersetCard, S.2, smul_eq_mul]
  -- `e · 2 ^ (1 - (k choose 2)) · (d + 1) ≤ 1` is exactly the hypothesis `h`.
  have h2K : (0 : ℝ) < 2 ^ (k.choose 2) := by positivity
  have h2K' : (2 : ℝ) ^ (k.choose 2) ≠ 0 := ne_of_gt h2K
  have hcond : Real.exp 1 * (2 * ((2 : ℝ)⁻¹) ^ (k.choose 2))
      * (((k.choose 2 * n.choose (k - 2) : ℕ) : ℝ) + 1) ≤ 1 := by
    rw [inv_pow, show Real.exp 1 * (2 * ((2 : ℝ) ^ (k.choose 2))⁻¹)
        * (((k.choose 2 * n.choose (k - 2) : ℕ) : ℝ) + 1)
        = (Real.exp 1 * (2 * ((k.choose 2 * n.choose (k - 2) : ℕ) : ℝ) + 2))
          / 2 ^ (k.choose 2) from by field_simp, div_le_one h2K]
    exact h
  have hpos := lovasz_local_lemma_symmetric A hAmeas N hNdep hp hdcard hcond
  -- A colouring avoiding every bad event exists; reading it off the two-element sets gives a
  -- symmetric edge colouring of `K n` with no monochromatic `k`-clique.
  rcases Set.eq_empty_or_nonempty (⋂ i, (A i)ᶜ) with hempty | ⟨x, hx⟩
  · rw [hempty] at hpos; simp at hpos
  · simp only [Set.mem_iInter, Set.mem_compl_iff] at hx
    have hsymm : ∀ i j : Fin n, x {i, j} = x {j, i} := fun i j => by rw [Finset.pair_comm]
    have hno : ∀ S : Finset (Fin n), S.card = k →
        ¬ IsMonochromatic (fun i j => x {i, j}) S := by
      intro S hS hmono
      obtain ⟨b, hb⟩ := hmono
      have hval : ∀ e ∈ S.powersetCard 2, x e = b := by
        intro e he
        rw [Finset.mem_powersetCard] at he
        obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 he.2
        exact hb i (he.1 (by simp)) j (he.1 (by simp)) hij
      exact hx ⟨S, hS⟩ ((hAdef ⟨S, hS⟩ x).2 fun e he f hf => by rw [hval e he, hval f hf])
    have hnonempty : {m | RamseyProperty m k}.Nonempty := exists_ramseyProperty k
    have hmem : RamseyProperty (ramseyNumber k) k := Nat.sInf_mem hnonempty
    by_contra hlt
    obtain ⟨S, hcard, hmono⟩ :=
      hmem.mono (Nat.not_lt.1 hlt) (fun i j => x {i, j}) hsymm
    exact hno S hcard hmono

/-- **Non-uniform hypergraphs are 2-colourable under a local weighted condition**
(Zhao, Theorem 6.2.4).  Where `twoColorable_of_inter_card_le` caps how many edges each edge
*meets*, this weights each neighbour by its own size, so a hypergraph with a few small edges and
many large ones can still qualify.

The bad event for an edge `f` is that `f` is monochromatic, of probability `2 ^ (1 - |f|)`, which
is the `1 / 2 ^ (f.card - 1)` appearing in the sum.  `lovasz_local_lemma_of_sum_le` is the form to
apply — the asymmetric one — rather than the symmetric form, which cannot see the individual
sizes.

**`3 ≤ e.card` is not decoration.**  `lovasz_local_lemma_of_sum_le` requires every bad event to
have probability below `1/2`, and a 2-element edge is monochromatic with probability exactly
`1/2`.  So edges of size 2 are excluded, and they must be: a hypergraph containing `{u, v}` and
`{u, w}` and `{v, w}` is not 2-colourable at all.

In the uniform case this is *weaker* than `twoColorable_of_inter_card_le` — it permits
`d ≤ 2^(k-1)/4` against that theorem's `d + 1 ≤ 2^(k-1)/e` — because the sum form's `1/4` is
cruder than the symmetric form's `e`.  Its value is the non-uniform case, which the other cannot
state. -/
theorem twoColorable_of_sum_inv_two_pow_le {H : Finset (Finset α)}
    (hsize : ∀ e ∈ H, 3 ≤ e.card)
    (hsum : ∀ e ∈ H, ∑ f ∈ (H.erase e).filter (fun f => (e ∩ f).Nonempty),
        (1 : ℝ) / 2 ^ (f.card - 1) ≤ 1 / 4) :
    TwoColorable H := by
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
  have hNdep : IsDependencyGraph (uniformColoring α) A N := by
    intro i s hs g
    refine uniformColoring_inter_eq_mul (i : Finset α) (A i) (pattern A s g) (hAinv i) ?_
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
  -- The bad event for `f` has probability at most `1 / 2 ^ (|f| - 1)`, the weight in `hsum`.
  have hp : ∀ i : { e // e ∈ H },
      (uniformColoring α (A i)).toReal ≤ 1 / 2 ^ ((i : Finset α).card - 1) := by
    intro i
    have hAeq : A i = {x : α → Bool | ∀ u ∈ (i : Finset α), ∀ v ∈ (i : Finset α), x u = x v} :=
      Set.ext fun x => hAdef i x
    rw [hAeq]
    exact uniformColoring_monochromatic_toReal_le _ (by have := hsize _ i.2; omega)
  -- An edge of at least three vertices is monochromatic with probability at most `1 / 4`.
  have hhalf : ∀ i, (uniformColoring α (A i)).toReal < 1 / 2 := by
    intro i
    have h3 := hsize _ i.2
    have hmono : (4 : ℝ) ≤ 2 ^ ((i : Finset α).card - 1) :=
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ ((i : Finset α).card - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hquarter : (1 : ℝ) / 2 ^ ((i : Finset α).card - 1) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) hmono
    linarith [hp i]
  -- The neighbourhood sum is the hypothesis, reindexed along the coercion out of the subtype.
  have hsumN : ∀ i, ∑ j ∈ N i, (uniformColoring α (A j)).toReal ≤ 1 / 4 := by
    intro i
    have himg : (N i).image (fun f : { e // e ∈ H } => (f : Finset α))
        = (H.erase (i : Finset α)).filter (fun f => ((i : Finset α) ∩ f).Nonempty) := by
      ext g
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨f, hf, rfl⟩
        rw [hNdef] at hf
        exact ⟨⟨fun h => hf.1 (Subtype.ext h), f.2⟩, hf.2⟩
      · rintro ⟨⟨hne, hgH⟩, hint⟩
        exact ⟨⟨g, hgH⟩,
          (hNdef i ⟨g, hgH⟩).2 ⟨fun h => hne (congrArg Subtype.val h), hint⟩, rfl⟩
    calc ∑ j ∈ N i, (uniformColoring α (A j)).toReal
        ≤ ∑ j ∈ N i, (1 : ℝ) / 2 ^ ((j : Finset α).card - 1) :=
          Finset.sum_le_sum fun j _ => hp j
      _ = ∑ f ∈ (H.erase (i : Finset α)).filter (fun f => ((i : Finset α) ∩ f).Nonempty),
            (1 : ℝ) / 2 ^ (f.card - 1) := by
          rw [← himg, Finset.sum_image
            (Function.Injective.injOn fun a b h => Subtype.ext h)]
      _ ≤ 1 / 4 := hsum _ i.2
  have hpos := lovasz_local_lemma_of_sum_le A hAmeas N hNdep hhalf hsumN
  -- A colouring avoiding every bad event exists.
  rcases Set.eq_empty_or_nonempty (⋂ i, (A i)ᶜ) with hempty | ⟨x, hx⟩
  · rw [hempty] at hpos; simp at hpos
  · refine ⟨x, fun e he => ?_⟩
    simp only [Set.mem_iInter, Set.mem_compl_iff] at hx
    by_contra hcon
    refine hx ⟨e, he⟩ ((hAdef ⟨e, he⟩ x).2 fun u hu v hv => ?_)
    by_contra hne
    exact hcon ⟨u, hu, v, hv, hne⟩

/-!
### The uniform random transversal

The independent-transversal argument of Theorem 6.3.1 picks one vertex uniformly at random out
of each finset of a family `Q`, independently across the family.  The measure lives on choice
functions and is the product of the uniform measures on the `Q j`; the three facts needed about
it are the probability of fixing two coordinates, that the choice functions selecting inside
every `Q j` carry full measure, and independence of events reading disjoint sets of coordinates.
-/

/-- One vertex chosen uniformly at random from each `Q j`, independently across `j`. -/
private noncomputable def unifChoice {n : ℕ} {ι : Type*} [Fintype ι] (Q : ι → Finset (Fin n)) :
    Measure (ι → Fin n) :=
  Measure.pi fun j => uniformOn (Q j : Set (Fin n))

private theorem isProbabilityMeasure_unifChoice {n : ℕ} {ι : Type*} [Fintype ι]
    {Q : ι → Finset (Fin n)} (hQ : ∀ j, (Q j).Nonempty) :
    IsProbabilityMeasure (unifChoice Q) := by
  have : ∀ j, IsProbabilityMeasure (uniformOn (Q j : Set (Fin n))) := fun j =>
    isProbabilityMeasure_uniformOn (Set.toFinite _) (Finset.coe_nonempty.2 (hQ j))
  rw [unifChoice]
  infer_instance

/-- Two distinct coordinates take two prescribed values with probability `|Q j|⁻¹ |Q k|⁻¹`. -/
private theorem unifChoice_pair {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : ι → Finset (Fin n)} (hQ : ∀ j, (Q j).Nonempty) {j k : ι} (hjk : j ≠ k) {u v : Fin n}
    (hu : u ∈ Q j) (hv : v ∈ Q k) :
    unifChoice Q {c : ι → Fin n | c j = u ∧ c k = v}
      = ((Q j).card : ENNReal)⁻¹ * ((Q k).card : ENNReal)⁻¹ := by
  have hprob : ∀ j, IsProbabilityMeasure (uniformOn (Q j : Set (Fin n))) := fun j =>
    isProbabilityMeasure_uniformOn (Set.toFinite _) (Finset.coe_nonempty.2 (hQ j))
  have hsing : ∀ (s : Finset (Fin n)) (w : Fin n), w ∈ s →
      uniformOn (s : Set (Fin n)) {w} = (s.card : ENNReal)⁻¹ := by
    intro s w hw
    have hcoe : ((({w} : Finset (Fin n)) : Set (Fin n))) = ({w} : Set (Fin n)) := by simp
    rw [← hcoe, uniformOn_apply_finset, Finset.inter_singleton_of_mem hw,
      Finset.card_singleton, Nat.cast_one, one_div]
  have hset : {c : ι → Fin n | c j = u ∧ c k = v}
      = Set.univ.pi (fun a => if a = j then ({u} : Set (Fin n))
          else if a = k then ({v} : Set (Fin n)) else Set.univ) := by
    ext c
    simp only [Set.mem_univ_pi]
    show (c j = u ∧ c k = v) ↔ _
    constructor
    · intro ⟨h1, h2⟩ a
      by_cases ha : a = j
      · subst ha; simpa using h1
      · by_cases ha' : a = k
        · subst ha'; simp [ha, h2]
        · simp [ha, ha']
    · intro h
      refine ⟨?_, ?_⟩
      · have := h j; simpa using this
      · have := h k; simp [hjk.symm] at this; exact this
  rw [hset, unifChoice, Measure.pi_pi]
  refine Finset.prod_eq_mul_of_mem j k (Finset.mem_univ _) (Finset.mem_univ _) hjk ?_ |>.trans ?_
  · intro a _ ha
    simp [ha.1, ha.2]
  · rw [if_pos rfl, if_neg hjk.symm, if_pos rfl, hsing _ _ hu, hsing _ _ hv]

/-- Almost every choice function selects inside every `Q j`. -/
private theorem unifChoice_pi_self {n : ℕ} {ι : Type*} [Fintype ι] {Q : ι → Finset (Fin n)}
    (hQ : ∀ j, (Q j).Nonempty) :
    unifChoice Q (Set.univ.pi fun j => (Q j : Set (Fin n))) = 1 := by
  rw [unifChoice, Measure.pi_pi]
  refine Finset.prod_eq_one fun j _ => ?_
  exact uniformOn_self (Set.toFinite _) (Finset.coe_nonempty.2 (hQ j))

/-- **Events determined by disjoint sets of coordinates are independent.**  This is Setup 6.1.5
for a uniform random choice: `S₁` may depend only on the coordinates in `T`, and `S₂` only on
those outside it. -/
private theorem unifChoice_inter_eq_mul {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : ι → Finset (Fin n)} (hQ : ∀ j, (Q j).Nonempty) (T : Finset ι) (S₁ S₂ : Set (ι → Fin n))
    (h₁ : ∀ x y : ι → Fin n, (∀ a ∈ T, x a = y a) → (x ∈ S₁ ↔ y ∈ S₁))
    (h₂ : ∀ x y : ι → Fin n, (∀ a ∉ T, x a = y a) → (x ∈ S₂ ↔ y ∈ S₂)) :
    unifChoice Q (S₁ ∩ S₂) = unifChoice Q S₁ * unifChoice Q S₂ := by
  have hprob : ∀ j, IsProbabilityMeasure (uniformOn (Q j : Set (Fin n))) := fun j =>
    isProbabilityMeasure_uniformOn (Set.toFinite _) (Finset.coe_nonempty.2 (hQ j))
  exact measure_pi_inter_eq_mul (fun j => uniformOn (Q j : Set (Fin n))) T S₁ S₂ h₁ h₂

/-- **Independent transversals** (Zhao, §6.3): a graph of degree at most `Δ` whose vertices are
partitioned into parts, each larger than `2eΔ`, has an independent set containing exactly one
vertex from every part.

The transversal is returned as a choice function `f` picking a vertex out of each part —
`part (f j) = j` — which is automatically injective, so the two conclusions say exactly that the
chosen vertices form an independent transversal.

**The size hypothesis is strict, and that is a repair rather than a transcription.**  The source
asks for parts of size `≥ 2eΔ`.  At `Δ = 0` that reads `0 ≤ |part|`, which permits an **empty**
part — and then no transversal exists and the statement is false.  Strict `<` is the minimal
repair, and it is minimal in a precise sense: for `Δ ≥ 1` the number `2eΔ` is irrational, so it
is never equal to a part size, and `≤` and `<` are *logically equivalent* hypotheses there.  The
two forms differ at exactly one point, `Δ = 0`, which is exactly where the non-strict form fails.
No margin is being spent, and there is none to trade.

**Route.**  Pass first to subsets `Q j` of a **common size** `m`, discarding surplus vertices;
every part has more than `2eΔ` vertices, so `m` may be taken to be any natural number with
`2eΔ < m`.  This step is load-bearing rather than tidying: with heterogeneous parts the bad event
for an edge between parts `j` and `k` has probability `1/(|Q j| · |Q k|)`, bounded only by
`1/m²` for the *minimum* size, while the dependency degree scales with the *maximum*, and the
local lemma's condition fails once the parts are far apart in size.

Then choose one vertex uniformly at random from each `Q j`, independently.  For each edge whose
endpoints lie in different parts, its bad event is that both endpoints were chosen, of
probability `1/m²`.  Two bad events are dependent only when their edges meet a common part, which
gives dependency degree `d = 2mΔ - 1`, and `lovasz_local_lemma_symmetric` applies because
`e · (1/m²) · (d + 1) = 2eΔ/m ≤ 1`.

**The `- 1` is load-bearing too.**  With `d = 2mΔ` the condition reads `2eΔ/m + e/m² ≤ 1`, which
fails at `Δ = 2, m = 11` — the smallest `m` the hypothesis allows, since `2eΔ = 10.873…` — where
it evaluates to `1.0109`.  The hypothesis leaves about `1.2%` of room and the spurious `+1`
costs `2.2%`.

Edges inside a single part need no event: at most one vertex per part is ever chosen. -/
theorem exists_independent_transversal {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (Δ : ℕ) (part : Fin n → ι)
    (hdeg : ∀ v, G.degree v ≤ Δ)
    (hsize : ∀ j : ι, 2 * Real.exp 1 * Δ < ((univ.filter fun v => part v = j).card : ℝ)) :
    ∃ f : ι → Fin n, (∀ j, part (f j) = j) ∧ ∀ j k, j ≠ k → ¬ G.Adj (f j) (f k) := by
  classical
  -- Strictness of the size hypothesis makes every part nonempty.
  have hPne : ∀ j : ι, (univ.filter fun v => part v = j).Nonempty := by
    intro j
    rw [← Finset.card_pos]
    have h0 : (0:ℝ) ≤ 2 * Real.exp 1 * Δ := by positivity
    have hlt : (0:ℝ) < ((univ.filter fun v => part v = j).card : ℝ) :=
      lt_of_le_of_lt h0 (hsize j)
    exact_mod_cast hlt
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨fun j => isEmptyElim j, fun j => isEmptyElim j, fun j => isEmptyElim j⟩
  -- With `Δ = 0` the graph has no edges at all and any transversal works.
  rcases Nat.eq_zero_or_pos Δ with hΔ | hΔ
  · choose f hf using hPne
    refine ⟨f, fun j => by simpa using hf j, fun j k _ hadj => ?_⟩
    have hdpos := (G.degree_pos_iff_exists_adj (f j)).2 ⟨f k, hadj⟩
    have hdle := hdeg (f j)
    omega
  -- Shrinking every part to the size `m` of the smallest one makes the probability of a bad
  -- event the same for all of them, which is what the symmetric form needs.
  obtain ⟨j₀, hj₀⟩ := Finite.exists_min (fun j : ι => (univ.filter fun v => part v = j).card)
  set m := (univ.filter fun v => part v = j₀).card
  have hmle : ∀ j, m ≤ (univ.filter fun v => part v = j).card := hj₀
  have hmlt : 2 * Real.exp 1 * Δ < m := hsize j₀
  have hm1 : 1 ≤ m := by
    have h0 : (0:ℝ) ≤ 2 * Real.exp 1 * Δ := by positivity
    have hpos : (0:ℝ) < m := lt_of_le_of_lt h0 hmlt
    have : 0 < m := by exact_mod_cast hpos
    omega
  choose Q hQP hQcard using fun j : ι => Finset.exists_subset_card_eq (hmle j)
  have hQne : ∀ j, (Q j).Nonempty := fun j => Finset.card_pos.1 (by rw [hQcard j]; omega)
  have hQpart : ∀ (j : ι) (v : Fin n), v ∈ Q j → part v = j := by
    intro j v hv
    have := hQP j hv
    simpa using this
  -- An edge carries a bad event exactly when it joins two distinct parts inside the shrunken
  -- family; listing the vertices of an edge in increasing order names each such edge once.
  obtain ⟨R, hR⟩ : ∃ R : Fin n × Fin n → Prop, ∀ e : Fin n × Fin n,
      (R e ↔ e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ part e.1 ≠ part e.2 ∧
        e.1 ∈ Q (part e.1) ∧ e.2 ∈ Q (part e.2)) := ⟨_, fun _ => Iff.rfl⟩
  -- The bad event of an edge: both of its endpoints are chosen.
  obtain ⟨A, hA⟩ : ∃ A : Fin n × Fin n → Set (ι → Fin n), ∀ (e : Fin n × Fin n) (c : ι → Fin n),
      (c ∈ A e ↔ R e ∧ c (part e.1) = e.1 ∧ c (part e.2) = e.2) := ⟨_, fun _ _ => Iff.rfl⟩
  -- Two bad events are joined when their edges meet a common part.
  obtain ⟨N, hN⟩ : ∃ N : Fin n × Fin n → Finset (Fin n × Fin n), ∀ e w,
      (w ∈ N e ↔ R e ∧ R w ∧ w ≠ e ∧ (part w.1 = part e.1 ∨ part w.1 = part e.2 ∨
        part w.2 = part e.1 ∨ part w.2 = part e.2)) :=
    ⟨fun e => univ.filter fun w => R e ∧ R w ∧ w ≠ e ∧ (part w.1 = part e.1 ∨
      part w.1 = part e.2 ∨ part w.2 = part e.1 ∨ part w.2 = part e.2), by
      intro e w; simp⟩
  have hprob : IsProbabilityMeasure (unifChoice Q) := isProbabilityMeasure_unifChoice hQne
  have hAmeas : ∀ i, MeasurableSet (A i) := fun _ => (Set.toFinite _).measurableSet
  -- A pair that carries no bad event contributes nothing, neither to the dependency graph nor
  -- to the probability bound.
  have hAempty : ∀ e, ¬ R e → A e = ∅ := by
    intro e he
    ext c
    simp [hA, he]
  -- A bad event reads only the two coordinates indexed by the parts of its edge.
  have hAinv : ∀ (e : Fin n × Fin n) (x y : ι → Fin n),
      (∀ a ∈ ({part e.1, part e.2} : Finset ι), x a = y a) → (x ∈ A e ↔ y ∈ A e) := by
    intro e x y hxy
    rw [hA, hA, hxy (part e.1) (by simp), hxy (part e.2) (by simp)]
  have hdep : IsDependencyGraph (unifChoice Q) A N := by
    intro i s hs g
    by_cases hRi : R i
    · refine unifChoice_inter_eq_mul hQne ({part i.1, part i.2} : Finset ι) (A i)
        (pattern A s g) (hAinv i) ?_
      intro x y hxy
      have hj : ∀ j ∈ s,
          (x ∈ (if g j then A j else (A j)ᶜ) ↔ y ∈ (if g j then A j else (A j)ᶜ)) := by
        intro j hjs
        obtain ⟨hjne, hjN⟩ := hs j hjs
        have hiff : x ∈ A j ↔ y ∈ A j := by
          by_cases hRj : R j
          · have hshare : ¬ (part j.1 = part i.1 ∨ part j.1 = part i.2 ∨
                part j.2 = part i.1 ∨ part j.2 = part i.2) := fun hc =>
              hjN ((hN i j).2 ⟨hRi, hRj, hjne, hc⟩)
            refine hAinv j x y ?_
            intro a ha
            simp only [Finset.mem_insert, Finset.mem_singleton] at ha
            refine hxy a ?_
            simp only [Finset.mem_insert, Finset.mem_singleton]
            rcases ha with ha | ha <;> subst ha <;> tauto
          · rw [hAempty j hRj]; simp
        by_cases hg : g j
        · rw [if_pos hg]; exact hiff
        · rw [if_neg hg]; exact not_congr hiff
      simp only [pattern, Set.mem_iInter]
      exact ⟨fun h j hjs => (hj j hjs).1 (h j hjs), fun h j hjs => (hj j hjs).2 (h j hjs)⟩
    · rw [hAempty i hRi]
      simp
  -- Each bad event asks for one prescribed vertex in each of two distinct parts.
  have hp : ∀ i, ((unifChoice Q) (A i)).toReal ≤ ((m:ℝ))⁻¹ * ((m:ℝ))⁻¹ := by
    intro i
    by_cases hRi : R i
    · obtain ⟨h12, hadj, hpart, hu, hv⟩ := (hR i).1 hRi
      have hset : A i = {c : ι → Fin n | c (part i.1) = i.1 ∧ c (part i.2) = i.2} := by
        ext c
        rw [hA]
        simp [hRi]
      rw [hset, unifChoice_pair hQne hpart hu hv, hQcard, hQcard, ENNReal.toReal_mul,
        ENNReal.toReal_inv]
      simp
    · rw [hAempty i hRi]
      simp
      positivity
  -- Every edge joined to `i` has an endpoint among the `2 m` vertices chosen from the two parts
  -- of `i`, and the edge of `i` itself is one of the edges so counted but not one of its
  -- neighbours.
  have hd : ∀ i, (N i).card ≤ 2 * m * Δ - 1 := by
    intro i
    by_cases hRi : R i
    · obtain ⟨h12, hadj, hpart, hu, hv⟩ := (hR i).1 hRi
      set T := Q (part i.1) ∪ Q (part i.2)
      set D := T.biUnion fun x => (G.neighborFinset x).image fun y => (min x y, max x y)
      have hDmem : ∀ (z : Fin n × Fin n) (x : Fin n), x ∈ T → ∀ y, G.Adj x y →
          z = (min x y, max x y) → z ∈ D := by
        intro z x hx y hxy hz
        exact Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2 ⟨y, by simpa using hxy, hz.symm⟩⟩
      have hiD : i ∈ D := hDmem i i.1 (Finset.mem_union_left _ hu) i.2 hadj
        (by rw [min_eq_left h12.le, max_eq_right h12.le])
      have hDcard : D.card ≤ 2 * m * Δ := by
        calc D.card
            ≤ ∑ x ∈ T, ((G.neighborFinset x).image fun y => (min x y, max x y)).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ _x ∈ T, Δ := Finset.sum_le_sum fun x _ =>
              le_trans Finset.card_image_le (hdeg x)
          _ = T.card * Δ := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ 2 * m * Δ := by
              refine Nat.mul_le_mul_right _ ?_
              calc T.card ≤ (Q (part i.1)).card + (Q (part i.2)).card := Finset.card_union_le _ _
                _ = 2 * m := by rw [hQcard, hQcard]; ring
      have hsub : N i ⊆ D.erase i := by
        intro w hw
        rw [hN] at hw
        obtain ⟨-, hRw, hwne, hshare⟩ := hw
        obtain ⟨hw12, hwadj, hwpart, hwu, hwv⟩ := (hR w).1 hRw
        refine Finset.mem_erase.2 ⟨hwne, ?_⟩
        have hend : w.1 ∈ T ∨ w.2 ∈ T := by
          rcases hshare with h | h | h | h
          · exact Or.inl (Finset.mem_union_left _ (h ▸ hwu))
          · exact Or.inl (Finset.mem_union_right _ (h ▸ hwu))
          · exact Or.inr (Finset.mem_union_left _ (h ▸ hwv))
          · exact Or.inr (Finset.mem_union_right _ (h ▸ hwv))
        rcases hend with h | h
        · exact hDmem w w.1 h w.2 hwadj (by rw [min_eq_left hw12.le, max_eq_right hw12.le])
        · exact hDmem w w.2 h w.1 hwadj.symm
            (by rw [min_eq_right hw12.le, max_eq_left hw12.le])
      calc (N i).card ≤ (D.erase i).card := Finset.card_le_card hsub
        _ = D.card - 1 := Finset.card_erase_of_mem hiD
        _ ≤ 2 * m * Δ - 1 := Nat.sub_le_sub_right hDcard 1
    · have hNempty : N i = ∅ := by
        ext w
        simp [hN, hRi]
      simp [hNempty]
  have hmR : (0:ℝ) < m := by exact_mod_cast hm1
  -- `e · m⁻² · 2 m Δ ≤ 1` is exactly `2 e Δ ≤ m`.
  have hcond : Real.exp 1 * (((m:ℝ))⁻¹ * ((m:ℝ))⁻¹) * (((2 * m * Δ - 1 : ℕ) : ℝ) + 1) ≤ 1 := by
    have h1 : 1 ≤ 2 * m * Δ := by
      have h2m : 1 ≤ 2 * m := by omega
      calc 1 = 1 * 1 := by norm_num
        _ ≤ (2 * m) * Δ := Nat.mul_le_mul h2m hΔ
    have hcast : (((2 * m * Δ - 1 : ℕ) : ℝ) + 1) = 2 * m * Δ := by
      rw [Nat.cast_sub h1]
      push_cast
      ring
    rw [hcast, show Real.exp 1 * (((m:ℝ))⁻¹ * ((m:ℝ))⁻¹) * (2 * (m:ℝ) * Δ)
      = (2 * Real.exp 1 * Δ) / m from by field_simp, div_le_one hmR]
    exact hmlt.le
  have hpos := lovasz_local_lemma_symmetric A hAmeas N hdep hp hd hcond
  -- A choice function avoiding every bad event and selecting inside every `Q j` exists.
  have hfull : unifChoice Q (Set.univ.pi fun j => (Q j : Set (Fin n))) = 1 :=
    unifChoice_pi_self hQne
  have hcompl : unifChoice Q ((Set.univ.pi fun j => (Q j : Set (Fin n)))ᶜ) = 0 := by
    rw [measure_compl (Set.toFinite _).measurableSet (measure_ne_top _ _), hfull]
    simp
  have hne : ((⋂ i, (A i)ᶜ) ∩ Set.univ.pi fun j => (Q j : Set (Fin n))).Nonempty := by
    rcases Set.eq_empty_or_nonempty
      ((⋂ i, (A i)ᶜ) ∩ Set.univ.pi fun j => (Q j : Set (Fin n))) with hempty | h
    · exfalso
      have hle := measure_le_inter_add_sdiff (unifChoice Q) (⋂ i, (A i)ᶜ)
        (Set.univ.pi fun j => (Q j : Set (Fin n)))
      rw [hempty, measure_empty] at hle
      have hzero : unifChoice Q ((⋂ i, (A i)ᶜ) \ Set.univ.pi fun j => (Q j : Set (Fin n))) = 0 :=
        measure_mono_null (fun x hx => hx.2) hcompl
      rw [hzero] at hle
      simp only [zero_add, nonpos_iff_eq_zero] at hle
      rw [hle] at hpos
      simp at hpos
    · exact h
  obtain ⟨c, hc, hcQ⟩ := hne
  have hcQ' : ∀ a, c a ∈ Q a := fun a => by
    have := hcQ a (Set.mem_univ a)
    simpa using this
  simp only [Set.mem_iInter, Set.mem_compl_iff] at hc
  refine ⟨c, fun j => hQpart j _ (hcQ' j), fun j k hjk hadj => ?_⟩
  have hjpart : part (c j) = j := hQpart j _ (hcQ' j)
  have hkpart : part (c k) = k := hQpart k _ (hcQ' k)
  have hne' : c j ≠ c k := fun h => hjk (by rw [← hjpart, ← hkpart, h])
  rcases lt_or_gt_of_ne hne' with hlt | hlt
  · refine hc (c j, c k) ((hA _ c).2 ⟨(hR _).2 ⟨hlt, hadj, ?_, ?_, ?_⟩, ?_, ?_⟩)
    · simpa [hjpart, hkpart] using hjk
    · simpa [hjpart] using hcQ' j
    · simpa [hkpart] using hcQ' k
    · simp [hjpart]
    · simp [hkpart]
  · refine hc (c k, c j) ((hA _ c).2 ⟨(hR _).2 ⟨hlt, hadj.symm, ?_, ?_, ?_⟩, ?_, ?_⟩)
    · simpa [hjpart, hkpart] using hjk.symm
    · simpa [hkpart] using hcQ' k
    · simpa [hjpart] using hcQ' j
    · simp [hkpart]
    · simp [hjpart]

end Applications

section Compactness

/-! ### Infinite vertex sets

Theorem 6.2.6 colours a hypergraph on a *possibly infinite* vertex set, so the results here
cannot live in `Applications` above, whose `variable` line fixes `[Fintype α]`.
-/

variable {α : Type*} [DecidableEq α]

/-- **The compactness argument** (Zhao, Lemma 6.2.7).  In the random variable model with
finitely many choices per variable, avoiding every *finite* collection of bad events already
avoids all of them, however many there are.  This is what lets Theorems 6.2.6, 6.2.10 and
6.2.11 run the local lemma on finite subsystems and then pass to an infinite vertex set.

`hdet` is the book's "each event depends on a finite subset of variables", written as
invariance under changes outside that subset — the form a caller can actually establish, and
the same shape as the `hAinv` side conditions the finite applications above already discharge.

Remark 6.2.8 is the warning that the conclusion needs the variable model: `hdet` and the
finiteness of each `α i` are both doing work, and dropping either makes it false. -/
theorem exists_forall_notMem_of_forall_finset {ι κ : Type*} {α : ι → Type*}
    [∀ i, Finite (α i)] (E : κ → Set (∀ i, α i)) (s : κ → Finset ι)
    (hdet : ∀ (j : κ) (x y : ∀ i, α i), (∀ i ∈ s j, x i = y i) → (x ∈ E j ↔ y ∈ E j))
    (h : ∀ F : Finset κ, ∃ x, ∀ j ∈ F, x ∉ E j) :
    ∃ x, ∀ j, x ∉ E j := by
  classical
  -- Give each variable type the discrete topology; finiteness makes the product compact.
  let _ : ∀ i, TopologicalSpace (α i) := fun _ => ⊥
  have : ∀ i, DiscreteTopology (α i) := fun _ => ⟨rfl⟩
  -- `hdet` says each `E j` contains the basic open box cut out by the coordinates in `s j`.
  have hopen : ∀ j, IsOpen (E j) := by
    intro j
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    refine ⟨⋂ i ∈ s j, (fun y : ∀ i, α i => y i) ⁻¹' {x i}, ?_, ?_, ?_⟩
    · intro y hy
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff] at hy
      exact (hdet j y x hy).2 hx
    · exact isOpen_biInter_finset fun i _ =>
        (continuous_apply i).isOpen_preimage _ (isOpen_discrete _)
    · simp
  by_contra hcon
  push Not at hcon
  -- The closed sets `(E j)ᶜ` have the finite intersection property, so compactness of the
  -- product gives a point avoiding every `E j`.
  have hempty : (Set.univ ∩ ⋂ j, (E j)ᶜ : Set (∀ i, α i)) = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_iInter, Set.mem_compl_iff,
      Set.mem_empty_iff_false, iff_false, not_forall, not_not]
    exact hcon x
  obtain ⟨u, hu⟩ := (CompactSpace.isCompact_univ (X := ∀ i, α i)).elim_finite_subfamily_closed
      (fun j => (E j)ᶜ) (fun j => (hopen j).isClosed_compl) hempty
  obtain ⟨x, hx⟩ := h u
  have hmem : x ∈ Set.univ ∩ ⋂ j ∈ u, (E j)ᶜ := ⟨Set.mem_univ x, by simpa using hx⟩
  rw [hu] at hmem
  exact hmem

/-- `twoColorable_of_inter_card_le` on an arbitrary vertex type.  Only the vertices occurring
in `H` matter, and there are finitely many of them, so the `[Fintype α]` version applies after
restricting every edge to the subtype of `H.sup id`. -/
private theorem twoColorable_of_inter_card_le' {k : ℕ} (hk : 2 ≤ k) {H : Finset (Finset α)}
    (huniform : ∀ e ∈ H, e.card = k) {d : ℕ}
    (hd : ∀ e ∈ H, ((H.erase e).filter fun f => (e ∩ f).Nonempty).card ≤ d)
    (h : Real.exp 1 * (d + 1) ≤ 2 ^ (k - 1)) :
    TwoColorable H := by
  classical
  set V : Finset α := H.sup id
  have hsubV : ∀ e ∈ H, e ⊆ V := fun e he => Finset.le_sup (f := id) he
  set Φ : Finset α → Finset {a // a ∈ V} := fun e => e.subtype (· ∈ V) with hΦ
  have hmemΦ : ∀ (e : Finset α) (a : {a // a ∈ V}), a ∈ Φ e ↔ (a : α) ∈ e := by
    intro e a; simp [hΦ]
  have hcardΦ : ∀ e ∈ H, (Φ e).card = e.card := by
    intro e he
    rw [hΦ]
    simp only [Finset.card_subtype]
    congr 1
    exact Finset.filter_true_of_mem fun a ha => hsubV e he ha
  have hinj : Set.InjOn Φ H := by
    intro e he f hf hef
    ext a
    constructor
    · intro hae
      have hmem : (⟨a, hsubV e he hae⟩ : {a // a ∈ V}) ∈ Φ e := (hmemΦ e _).2 hae
      rw [hef] at hmem
      exact (hmemΦ f _).1 hmem
    · intro haf
      have hmem : (⟨a, hsubV f hf haf⟩ : {a // a ∈ V}) ∈ Φ f := (hmemΦ f _).2 haf
      rw [← hef] at hmem
      exact (hmemΦ e _).1 hmem
  have hinter : ∀ e ∈ H, ∀ f ∈ H, ((Φ e ∩ Φ f).Nonempty ↔ (e ∩ f).Nonempty) := by
    intro e he f hf
    constructor
    · rintro ⟨a, ha⟩
      rw [Finset.mem_inter, hmemΦ, hmemΦ] at ha
      exact ⟨a, Finset.mem_inter.2 ha⟩
    · rintro ⟨a, ha⟩
      rw [Finset.mem_inter] at ha
      exact ⟨⟨a, hsubV e he ha.1⟩,
        Finset.mem_inter.2 ⟨(hmemΦ e _).2 ha.1, (hmemΦ f _).2 ha.2⟩⟩
  set H' : Finset (Finset {a // a ∈ V}) := H.image Φ with hH'
  have hmemH' : ∀ e ∈ H, Φ e ∈ H' := by
    intro e he; rw [hH']; exact Finset.mem_image_of_mem Φ he
  have huniform' : ∀ e' ∈ H', e'.card = k := by
    intro e' he'
    rw [hH', Finset.mem_image] at he'
    obtain ⟨e, he, rfl⟩ := he'
    rw [hcardΦ e he, huniform e he]
  have hd' : ∀ e' ∈ H', ((H'.erase e').filter fun f' => (e' ∩ f').Nonempty).card ≤ d := by
    intro e' he'
    rw [hH', Finset.mem_image] at he'
    obtain ⟨e, he, rfl⟩ := he'
    calc ((H'.erase (Φ e)).filter fun f' => (Φ e ∩ f').Nonempty).card
        ≤ (((H.erase e).filter fun f => (e ∩ f).Nonempty).image Φ).card := by
          refine Finset.card_le_card ?_
          intro g' hg'
          rw [Finset.mem_filter, Finset.mem_erase] at hg'
          obtain ⟨⟨hne, hmem⟩, hne'⟩ := hg'
          rw [hH', Finset.mem_image] at hmem
          obtain ⟨f, hf, rfl⟩ := hmem
          refine Finset.mem_image.2 ⟨f, Finset.mem_filter.2
            ⟨Finset.mem_erase.2 ⟨fun hfe => hne (by rw [hfe]), hf⟩, ?_⟩, rfl⟩
          exact (hinter e he f hf).1 hne'
      _ = ((H.erase e).filter fun f => (e ∩ f).Nonempty).card := by
          refine Finset.card_image_of_injOn fun a ha b hb hab => hinj ?_ ?_ hab
          · exact Finset.mem_of_mem_erase (Finset.mem_filter.1 ha).1
          · exact Finset.mem_of_mem_erase (Finset.mem_filter.1 hb).1
      _ ≤ d := hd e he
  obtain ⟨g, hg⟩ := twoColorable_of_inter_card_le hk huniform' hd' h
  refine ⟨fun a => if ha : a ∈ V then g ⟨a, ha⟩ else false, fun e he => ?_⟩
  obtain ⟨u, hu, v, hv, huv⟩ := hg (Φ e) (hmemH' e he)
  refine ⟨u, (hmemΦ e u).1 hu, v, (hmemΦ e v).1 hv, ?_⟩
  simpa [dif_pos u.2, dif_pos v.2] using huv

/-- **The symmetric condition without uniformity, on an arbitrary vertex type.**  Relative to
`twoColorable_of_inter_card_le` this asks only `k ≤ e.card` rather than `e.card = k`, and drops
`[Fintype α]`.  Both are needed for Theorem 6.2.6: its edges have *at least* `k` vertices, and
its vertex set is infinite. -/
theorem twoColorable_of_le_card_inter_card_le {k : ℕ} (hk : 2 ≤ k) {H : Finset (Finset α)}
    (hcard : ∀ e ∈ H, k ≤ e.card) {d : ℕ}
    (hd : ∀ e ∈ H, ((H.erase e).filter fun f => (e ∩ f).Nonempty).card ≤ d)
    (h : Real.exp 1 * (d + 1) ≤ 2 ^ (k - 1)) :
    TwoColorable H := by
  classical
  choose! φ hφsub hφcard using fun e (he : e ∈ H) => Finset.exists_subset_card_eq (hcard e he)
  set H₀ : Finset (Finset α) := H.image φ with hH₀
  have hmemH₀ : ∀ e ∈ H, φ e ∈ H₀ := by
    intro e he; rw [hH₀]; exact Finset.mem_image_of_mem φ he
  have huniform : ∀ e₀ ∈ H₀, e₀.card = k := by
    intro e₀ he₀
    rw [hH₀, Finset.mem_image] at he₀
    obtain ⟨e, he, rfl⟩ := he₀
    exact hφcard e he
  have hd₀ : ∀ e₀ ∈ H₀, ((H₀.erase e₀).filter fun f₀ => (e₀ ∩ f₀).Nonempty).card ≤ d := by
    intro e₀ he₀
    rw [hH₀, Finset.mem_image] at he₀
    obtain ⟨e, he, rfl⟩ := he₀
    calc ((H₀.erase (φ e)).filter fun f₀ => (φ e ∩ f₀).Nonempty).card
        ≤ (((H.erase e).filter fun f => (e ∩ f).Nonempty).image φ).card := by
          refine Finset.card_le_card ?_
          intro g hg
          rw [Finset.mem_filter, Finset.mem_erase] at hg
          obtain ⟨⟨hne, hmem⟩, hne'⟩ := hg
          rw [hH₀, Finset.mem_image] at hmem
          obtain ⟨f, hf, rfl⟩ := hmem
          refine Finset.mem_image.2 ⟨f, Finset.mem_filter.2
            ⟨Finset.mem_erase.2 ⟨fun hfe => hne (by rw [hfe]), hf⟩, ?_⟩, rfl⟩
          obtain ⟨a, ha⟩ := hne'
          rw [Finset.mem_inter] at ha
          exact ⟨a, Finset.mem_inter.2 ⟨hφsub e he ha.1, hφsub f hf ha.2⟩⟩
      _ ≤ ((H.erase e).filter fun f => (e ∩ f).Nonempty).card := Finset.card_image_le
      _ ≤ d := hd e he
  obtain ⟨g, hg⟩ := twoColorable_of_inter_card_le' hk huniform hd₀ h
  refine ⟨g, fun e he => ?_⟩
  obtain ⟨u, hu, v, hv, huv⟩ := hg (φ e) (hmemH₀ e he)
  exact ⟨u, hφsub e he hu, v, hφsub e he hv, huv⟩

/-- Proper 2-colourability of a possibly infinite hypergraph: every edge sees both colours. -/
def SetTwoColorable (H : Set (Finset α)) : Prop :=
  ∃ f : α → Bool, ∀ e ∈ H, ∃ u ∈ e, ∃ v ∈ e, f u ≠ f v

/-- **Theorem 6.2.6**: the local condition for 2-colourability survives on an infinite vertex
set.  The local lemma colours every finite subhypergraph, and `exists_forall_notMem_of_forall_finset`
assembles those colourings into one. -/
theorem setTwoColorable_of_le_card_inter_card_le {k : ℕ} (hk : 2 ≤ k) {H : Set (Finset α)}
    (hcard : ∀ e ∈ H, k ≤ e.card) {d : ℕ}
    (hdfin : ∀ e ∈ H, {f | f ∈ H ∧ f ≠ e ∧ (e ∩ f).Nonempty}.Finite)
    (hd : ∀ e ∈ H, {f | f ∈ H ∧ f ≠ e ∧ (e ∩ f).Nonempty}.ncard ≤ d)
    (h : Real.exp 1 * (d + 1) ≤ 2 ^ (k - 1)) :
    SetTwoColorable H := by
  sorry

end Compactness

end ProbMethodCombinatorics
