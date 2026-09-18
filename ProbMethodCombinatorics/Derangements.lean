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

Both facts below were checked by exhaustive enumeration before being stated: the negative
dependency inequality has no violations over every `n ≤ 7`, every `i`, and every `S`, and the
corollary holds at `n = 1, …, 8`.
-/

namespace ProbMethodCombinatorics

open Finset MeasureTheory ProbabilityTheory

variable {n : ℕ}

instance : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

instance : MeasurableSingletonClass (Equiv.Perm (Fin n)) := ⟨fun _ => trivial⟩

/-- The uniform measure on permutations of `Fin n`. -/
noncomputable def uniformPerm (n : ℕ) : Measure (Equiv.Perm (Fin n)) :=
  uniformOn (Set.univ : Set (Equiv.Perm (Fin n)))

instance : IsProbabilityMeasure (uniformPerm n) := by
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

/-- **Fixed points are negatively dependent** (Zhao, Theorem 6.5.5 for pairwise disjoint single
edges): knowing that some other points are *not* fixed never makes `i` more likely to be fixed.

Since distinct single edges `(i, i)` and `(j, j)` are vertex disjoint, the canonical negative
dependency graph has no edges at all, which is why `N` is constantly `∅`. -/
theorem uniformPerm_isNegativeDependencyGraph :
    IsNegativeDependencyGraph (uniformPerm n) (fixedPointEvent (n := n)) (fun _ => ∅) := by
  sorry

/-- **Corollary 6.5.6** (derangement lower bound): a uniform random permutation of `Fin n` has
no fixed point with probability at least `(1 - 1/n) ^ n`.

Asymptotically optimal — both sides tend to `1/e`, the exact value being `∑ (-1)ⁱ / i!`. -/
theorem uniformPerm_derangement_ge [NeZero n] :
    (1 - 1 / (n : ℝ)) ^ n
      ≤ (uniformPerm n).real {σ : Equiv.Perm (Fin n) | ∀ i, σ i ≠ i} := by
  sorry

end ProbMethodCombinatorics
