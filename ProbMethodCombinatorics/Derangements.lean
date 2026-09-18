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

/-- **A uniform permutation fixes a given point with probability `1/n`.** -/
theorem uniformPerm_fixedPointEvent [NeZero n] (i : Fin n) :
    (uniformPerm n).real (fixedPointEvent i) = 1 / (n : ℝ) := by
  sorry

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
