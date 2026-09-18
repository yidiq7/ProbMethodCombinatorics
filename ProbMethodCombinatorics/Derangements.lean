import ProbMethodCombinatorics.Lopsided

/-!
# Section 6.5: the derangement bound

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Corollary 6.5.6: a uniform random
permutation of `[n]` has no fixed point with probability at least `(1 - 1/n) ^ n`.

This is the smallest application of the lopsided local lemma in the chapter, and the one that
does not need Setup 6.5.4's general random-injection model: the bad events `σ i = i` come from
pairwise vertex-disjoint single edges, so the canonical negative dependency graph is *empty*
and only the single-edge case of Theorem 6.5.5 is required.

**The source has a typo here.**  It writes "Since `ℙ(Aᵢ) = 1 - 1/n`, we can set `xᵢ = 1 - 1/n`".
Both should be `1/n`: the probability that `σ` fixes `i` is `1/n`, and it is `xᵢ = 1/n` that
makes `∏ (1 - xᵢ)` equal the stated `(1 - 1/n) ^ n`.  With `xᵢ = 1 - 1/n` the conclusion would
read `(1/n) ^ n`.

**The instances below are explicitly named, and that is not cosmetic.**  `MeasurableSpace
(Equiv.Perm (Fin n))` appears inside the term of every statement in this file, and an
*anonymous* instance's auto-generated name does not survive the `ChoirBase.` module prefixing
that `comparator` applies to the base tree — the gate then reports `statement-mismatch` on a
statement whose bytes are identical.  `Concentration.lean`'s named instances never had the
problem.  See `skills/conventions.md`.

Both facts below were checked by exhaustive enumeration before being stated: the negative
dependency inequality has no violations over every `n ≤ 7`, every `i`, and every `S`, and the
corollary holds at `n = 1, …, 8`.
-/

namespace ProbMethodCombinatorics

open Finset MeasureTheory ProbabilityTheory

variable {n : ℕ}

instance instMeasurableSpacePermFin : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

instance instMeasurableSingletonClassPermFin :
    MeasurableSingletonClass (Equiv.Perm (Fin n)) := ⟨fun _ => trivial⟩

/-- The uniform measure on permutations of `Fin n`. -/
noncomputable def uniformPerm (n : ℕ) : Measure (Equiv.Perm (Fin n)) :=
  uniformOn (Set.univ : Set (Equiv.Perm (Fin n)))

instance instIsProbabilityMeasureUniformPerm : IsProbabilityMeasure (uniformPerm n) := by
  rw [uniformPerm]; infer_instance

/-- The event that `i` is a fixed point of the permutation. -/
def fixedPointEvent (i : Fin n) : Set (Equiv.Perm (Fin n)) := {σ | σ i = i}

private lemma card_perm_fiber_eq (i j : Fin n) :
    (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = j).card
      = (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i).card := by
  refine Finset.card_equiv (Equiv.mulLeft (Equiv.swap j i)) fun σ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulLeft,
    Equiv.Perm.mul_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]

private lemma card_perm_fixed_mul (i : Fin n) :
    n * (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i).card = Nat.factorial n := by
  have h : (univ : Finset (Equiv.Perm (Fin n))).card
      = ∑ _j : Fin n, (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm (Fin n) => σ i)
      (t := (univ : Finset (Fin n))) fun σ _ => Finset.mem_univ _]
    exact Finset.sum_congr rfl fun j _ => card_perm_fiber_eq i j
  rw [Finset.sum_const, smul_eq_mul] at h
  simp only [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at h
  exact h.symm

/-- **A uniform permutation fixes a given point with probability `1/n`.** -/
theorem uniformPerm_fixedPointEvent [NeZero n] (i : Fin n) :
    (uniformPerm n).real (fixedPointEvent i) = 1 / (n : ℝ) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hfac : (0 : ℝ) < (Nat.factorial n : ℕ) := Nat.cast_pos.mpr n.factorial_pos
  have hset : fixedPointEvent i
      = ((univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i : Finset (Equiv.Perm (Fin n)))
          : Set (Equiv.Perm (Fin n))) := by
    ext σ
    simp [fixedPointEvent]
  rw [measureReal_def, uniformPerm, hset, uniformOn_univ, Measure.count_apply_finset,
    Fintype.card_perm, Fintype.card_fin, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast, div_eq_div_iff hfac.ne' hn.ne', one_mul, mul_comm]
  exact_mod_cast card_perm_fixed_mul i

/-- Left multiplication by `Equiv.swap x y` injects the permutations sending `i` to `x` into the
permutations sending `i` to `y`. -/
private lemma card_perm_fiber_le (i x y : Fin n) :
    #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = x)
      ≤ #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = y) := by
  refine Finset.card_le_card_of_injOn (fun σ => Equiv.swap x y * σ) ?_
    (fun _ _ _ _ h => mul_left_cancel h)
  intro σ hσ
  simp only [mem_coe, mem_filter, mem_univ, true_and] at hσ ⊢
  rw [Equiv.Perm.mul_apply, hσ, Equiv.swap_apply_left]

/-- All `n` fibres of `σ ↦ σ i` have the same size, so the permutations fixing `i` are exactly a
`1 / n` fraction of all permutations. -/
private lemma mul_card_perm_fixedPoint (i : Fin n) :
    n * #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i)
      = Fintype.card (Equiv.Perm (Fin n)) := by
  have h : #(univ : Finset (Equiv.Perm (Fin n)))
      = ∑ y : Fin n, #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = y) :=
    Finset.card_eq_sum_card_fiberwise fun _ _ => mem_univ _
  rw [← Finset.card_univ, h, Finset.sum_congr rfl fun y _ =>
    le_antisymm (card_perm_fiber_le i y i) (card_perm_fiber_le i i y),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **The injection behind the negative dependency inequality.**  For `i ∉ s`, left multiplication
by `Equiv.swap i y` injects the permutations that fix `i` and move every point of `s` into those
that send `i` to `y` and still move every point of `s`.

No case distinction on whether `y ∈ s` is needed: a permutation `σ` with `σ i = i` never sends a
point `j ∈ s` to `i`, since `σ j = i = σ i` would force `j = i`. -/
private lemma card_fixedPoint_le_card_fiber (i : Fin n) (s : Finset (Fin n)) (hi : i ∉ s)
    (y : Fin n) :
    #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i ∧ ∀ j ∈ s, σ j ≠ j)
      ≤ #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = y ∧ ∀ j ∈ s, σ j ≠ j) := by
  refine Finset.card_le_card_of_injOn (fun σ => Equiv.swap i y * σ) ?_
    (fun _ _ _ _ h => mul_left_cancel h)
  intro σ hσ
  simp only [mem_coe, mem_filter, mem_univ, true_and] at hσ ⊢
  obtain ⟨hfix, hmove⟩ := hσ
  refine ⟨by rw [Equiv.Perm.mul_apply, hfix, Equiv.swap_apply_left], fun j hj => ?_⟩
  have hji : j ≠ i := fun h => hi (h ▸ hj)
  have hne : σ j ≠ i := fun h => hji (σ.injective (h.trans hfix.symm))
  rw [Equiv.Perm.mul_apply]
  by_cases hy : σ j = y
  · rw [hy, Equiv.swap_apply_right]
    exact hji.symm
  · rw [Equiv.swap_apply_of_ne_of_ne hne hy]
    exact hmove j hj

/-- The counting core: the `n` fibres of `σ ↦ σ i` partition the permutations moving every point of
`s`, and each is at least as large as the fibre over `i`. -/
private lemma mul_card_fixedPoint_le_card_move (i : Fin n) (s : Finset (Fin n)) (hi : i ∉ s) :
    n * #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i ∧ ∀ j ∈ s, σ j ≠ j)
      ≤ #(univ.filter fun σ : Equiv.Perm (Fin n) => ∀ j ∈ s, σ j ≠ j) := by
  have h : #(univ.filter fun σ : Equiv.Perm (Fin n) => ∀ j ∈ s, σ j ≠ j)
      = ∑ y : Fin n,
          #{σ ∈ univ.filter fun σ : Equiv.Perm (Fin n) => ∀ j ∈ s, σ j ≠ j | σ i = y} :=
    Finset.card_eq_sum_card_fiberwise fun _ _ => mem_univ _
  have key : ∀ y : Fin n,
      #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i ∧ ∀ j ∈ s, σ j ≠ j)
        ≤ #{σ ∈ univ.filter fun σ : Equiv.Perm (Fin n) => ∀ j ∈ s, σ j ≠ j | σ i = y} := by
    intro y
    refine (card_fixedPoint_le_card_fiber i s hi y).trans (le_of_eq ?_)
    congr 1
    ext σ
    simp only [mem_filter, mem_univ, true_and]
    exact and_comm
  calc n * #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i ∧ ∀ j ∈ s, σ j ≠ j)
      = ∑ _y : Fin n,
          #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i ∧ ∀ j ∈ s, σ j ≠ j) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum fun y _ => key y
    _ = _ := h.symm

/-- **Fixed points are negatively dependent** (Zhao, Theorem 6.5.5 for pairwise disjoint single
edges): knowing that some other points are *not* fixed never makes `i` more likely to be fixed.

Since distinct single edges `(i, i)` and `(j, j)` are vertex disjoint, the canonical negative
dependency graph has no edges at all, which is why `N` is constantly `∅`. -/
theorem uniformPerm_isNegativeDependencyGraph :
    IsNegativeDependencyGraph (uniformPerm n) (fixedPointEvent (n := n)) (fun _ => ∅) := by
  intro i s hs
  have hi : i ∉ s := fun h => (hs i h).1 rfl
  have hAD : fixedPointEvent i ∩ ⋂ j ∈ s, (fixedPointEvent j)ᶜ
      = ↑(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i ∧ ∀ j ∈ s, σ j ≠ j) := by
    ext σ; simp [fixedPointEvent]
  have hA : fixedPointEvent i
      = ↑(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i) := by
    ext σ; simp [fixedPointEvent]
  have hD : (⋂ j ∈ s, (fixedPointEvent j)ᶜ)
      = ↑(univ.filter fun σ : Equiv.Perm (Fin n) => ∀ j ∈ s, σ j ≠ j) := by
    ext σ; simp [fixedPointEvent]
  rw [hAD, hA, hD]
  simp only [uniformPerm, uniformOn_univ, Measure.count_apply_finset]
  have hcard : n * #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i)
      = Fintype.card (Equiv.Perm (Fin n)) := mul_card_perm_fixedPoint i
  have hmove : n * #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i ∧ ∀ j ∈ s, σ j ≠ j)
      ≤ #(univ.filter fun σ : Equiv.Perm (Fin n) => ∀ j ∈ s, σ j ≠ j) :=
    mul_card_fixedPoint_le_card_move i s hi
  have hNpos : 0 < Fintype.card (Equiv.Perm (Fin n)) := Fintype.card_pos_iff.mpr ⟨1⟩
  set N := Fintype.card (Equiv.Perm (Fin n))
  set a := #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i ∧ ∀ j ∈ s, σ j ≠ j)
  set b := #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i)
  set c := #(univ.filter fun σ : Equiv.Perm (Fin n) => ∀ j ∈ s, σ j ≠ j)
  have hkey : a * N ≤ b * c :=
    calc a * N = b * (n * a) := by rw [← hcard]; ring
      _ ≤ b * c := Nat.mul_le_mul le_rfl hmove
  have hN0 : (N : ENNReal) ≠ 0 := by
    simpa using hNpos.ne'
  have hNt : (N : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top N
  calc (a : ENNReal) / (N : ENNReal)
      = ((a : ENNReal) * (N : ENNReal)) / ((N : ENNReal) * (N : ENNReal)) :=
        (ENNReal.mul_div_mul_right _ _ hN0 hNt).symm
    _ ≤ ((b : ENNReal) * (c : ENNReal)) / ((N : ENNReal) * (N : ENNReal)) :=
        ENNReal.div_le_div_right (by exact_mod_cast hkey) _
    _ = (b : ENNReal) / (N : ENNReal) * ((c : ENNReal) / (N : ENNReal)) := by
        simp only [div_eq_mul_inv]
        rw [ENNReal.mul_inv (Or.inl hN0) (Or.inl hNt)]
        exact mul_mul_mul_comm _ _ _ _

/-- **Corollary 6.5.6** (derangement lower bound): a uniform random permutation of `Fin n` has
no fixed point with probability at least `(1 - 1/n) ^ n`.

Asymptotically optimal — both sides tend to `1/e`, the exact value being `∑ (-1)ⁱ / i!`. -/
theorem uniformPerm_derangement_ge [NeZero n] :
    (1 - 1 / (n : ℝ)) ^ n
      ≤ (uniformPerm n).real {σ : Equiv.Perm (Fin n) | ∀ i, σ i ≠ i} := by
  have hset : {σ : Equiv.Perm (Fin n) | ∀ i, σ i ≠ i} = ⋂ i, (fixedPointEvent i)ᶜ := by
    ext σ
    simp [fixedPointEvent]
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have hn1 : n = 1 := by
      have := Nat.pos_of_ne_zero (NeZero.ne n)
      omega
    subst hn1
    have hzero : (1 - 1 / ((1 : ℕ) : ℝ)) ^ 1 = 0 := by norm_num
    rw [hzero, measureReal_def]
    exact ENNReal.toReal_nonneg
  · have hnpos : (0 : ℝ) < n := by
      have h : 0 < n := by omega
      exact_mod_cast h
    have hx₁ : 1 / (n : ℝ) < 1 := by
      rw [div_lt_one hnpos]
      have h : (1 : ℕ) < n := by omega
      exact_mod_cast h
    have key := lopsided_local_lemma (μ := uniformPerm n) (fixedPointEvent (n := n))
      (fun _ => trivial) (fun _ => ∅) uniformPerm_isNegativeDependencyGraph
      (fun _ => 1 / (n : ℝ)) (fun _ => by positivity) (fun _ => hx₁)
      (fun i => by
        rw [Finset.prod_empty, mul_one, ← measureReal_def]
        exact le_of_eq (uniformPerm_fixedPointEvent i))
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at key
    rw [hset, measureReal_def]
    exact key

end ProbMethodCombinatorics
