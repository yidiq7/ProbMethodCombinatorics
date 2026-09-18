import ProbMethodCombinatorics.Derangements

/-!
# Section 6.5: Latin transversals

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Theorem 6.5.11 (Erdős–Spencer
1991): every `n × n` array in which each symbol occurs at most `n / (4e)` times has a Latin
transversal.

A transversal picks one entry from each row and column, so it *is* a permutation `σ`, and it is
Latin when the entries `A i (σ i)` are distinct.  That makes the conclusion cheap to state; the
work is in the hypothesis of the lopsided local lemma.

**This file specialises Setup 6.5.4 to permutations.**  The source works with a uniformly random
injection `X → Y` for `|X| ≤ |Y|`; for Theorem 6.5.11 only `X = Y = [n]` is needed, where an
injection is a permutation and a matching is a partial permutation.  That avoids authoring the
general random-injection model while keeping the argument intact.

`uniformPerm_isNegativeDependencyGraph` in `Derangements.lean` is the single-edge case of
`uniformPerm_negativeDependency_matchings` below; the general statement is what Theorem 6.5.11
needs, since its bad events involve two entries at a time.

Checked before stating: `ℙ(A_F) = (n - |F|)! / n!` at `n = 4, 5` for matchings of size 1, 2, 3;
the degree bound `(4n-4)(n/(4e) - 1) ≤ n(n-1)/e - 1` at `n = 10, 50, 100, 1000`; and the
resulting `e · p · (d+1) ≤ 1` holds with equality in the worst case.
-/

namespace ProbMethodCombinatorics

open Finset MeasureTheory Nat

variable {n : ℕ}

/-- A set of array positions with at most one entry in each row and each column. -/
def IsPartialMatching (F : Finset (Fin n × Fin n)) : Prop :=
  (∀ p ∈ F, ∀ q ∈ F, p.1 = q.1 → p = q) ∧ (∀ p ∈ F, ∀ q ∈ F, p.2 = q.2 → p = q)

/-- Two position sets share no row and no column. -/
def VertexDisjoint (F G : Finset (Fin n × Fin n)) : Prop :=
  (∀ p ∈ F, ∀ q ∈ G, p.1 ≠ q.1) ∧ (∀ p ∈ F, ∀ q ∈ G, p.2 ≠ q.2)

/-- The event that the transversal uses every position in `F`. -/
def containsEntries (F : Finset (Fin n × Fin n)) : Set (Equiv.Perm (Fin n)) :=
  {σ | ∀ p ∈ F, σ p.1 = p.2}

/-- **A random transversal uses a prescribed partial matching with probability
`(n - |F|)! / n!`.** -/
theorem uniformPerm_containsEntries (F : Finset (Fin n × Fin n)) (hF : IsPartialMatching F) :
    (uniformPerm n).real (containsEntries F) = ((n - F.card)! : ℝ) / (n ! : ℝ) := by
  sorry

/-- **Theorem 6.5.5 for permutations**: joining two events whose position sets share a row or a
column gives a valid negative dependency graph. -/
theorem uniformPerm_negativeDependency_matchings {ι : Type*} [Fintype ι]
    (F : ι → Finset (Fin n × Fin n)) (hF : ∀ i, IsPartialMatching (F i)) (N : ι → Finset ι)
    (hN : ∀ i j, j ≠ i → j ∉ N i → VertexDisjoint (F i) (F j)) :
    IsNegativeDependencyGraph (uniformPerm n) (fun i => containsEntries (F i)) N := by
  sorry

/-- **Theorem 6.5.11** (Erdős–Spencer 1991): an `n × n` array in which every symbol occurs at
most `n / (4e)` times has a Latin transversal — a permutation `σ` along which the entries
`A i (σ i)` are all distinct. -/
theorem exists_latin_transversal {α : Type*} [DecidableEq α] (A : Fin n → Fin n → α)
    (h : ∀ s : α,
      (((univ : Finset (Fin n × Fin n)).filter fun p => A p.1 p.2 = s).card : ℝ)
        ≤ (n : ℝ) / (4 * Real.exp 1)) :
    ∃ σ : Equiv.Perm (Fin n), Function.Injective fun i => A i (σ i) := by
  sorry

end ProbMethodCombinatorics
