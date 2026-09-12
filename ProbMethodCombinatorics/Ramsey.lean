import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Perm

/-!
# Chapter 1.1: Lower bounds to Ramsey numbers

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Section 1.1.

An edge colouring of the complete graph `K n` is a symmetric function `c : Fin n → Fin n → Bool`;
the value on the diagonal is irrelevant throughout.
-/

namespace ProbMethodCombinatorics

open Finset

/-- The vertex set `S` spans a monochromatic clique under the edge colouring `c`. -/
def IsMonochromatic {α : Type*} (c : α → α → Bool) (S : Finset α) : Prop :=
  ∃ b : Bool, ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c i j = b

/-- `RamseyProperty n k` says every red/blue edge colouring of `K n` has a monochromatic `K k`. -/
def RamseyProperty (n k : ℕ) : Prop :=
  ∀ c : Fin n → Fin n → Bool, (∀ i j, c i j = c j i) →
    ∃ S : Finset (Fin n), S.card = k ∧ IsMonochromatic c S

/-- The diagonal Ramsey number `R(k, k)`: the least `n` such that every red/blue edge colouring of
`K n` contains a monochromatic clique on `k` vertices. -/
noncomputable def ramseyNumber (k : ℕ) : ℕ := sInf {n | RamseyProperty n k}

/-- The Ramsey property is monotone in the number of vertices. -/
theorem RamseyProperty.mono {m n k : ℕ} (hmn : m ≤ n) (h : RamseyProperty m k) :
    RamseyProperty n k := by
  sorry

/-- **Erdős 1947** (Zhao, Theorem 1.1.2): if `2 * (n.choose k) < 2 ^ (k.choose 2)` then some red/blue
edge colouring of `K n` has no monochromatic `K k`.  The hypothesis is the book's
`(n.choose k) * 2 ^ (1 - k.choose 2) < 1`, cleared of denominators. -/
theorem exists_coloring_no_isMonochromatic (n k : ℕ) (hk : 2 ≤ k)
    (h : 2 * n.choose k < 2 ^ k.choose 2) :
    ∃ c : Fin n → Fin n → Bool, (∀ i j, c i j = c j i) ∧
      ∀ S : Finset (Fin n), S.card = k → ¬ IsMonochromatic c S := by
  sorry

/-- **Erdős 1947** (Zhao, Theorem 1.1.2), stated for the Ramsey number: if
`2 * (n.choose k) < 2 ^ (k.choose 2)` then `R(k, k) > n`. -/
theorem lt_ramseyNumber (n k : ℕ) (hk : 2 ≤ k)
    (h : 2 * n.choose k < 2 ^ k.choose 2) : n < ramseyNumber k := by
  sorry

end ProbMethodCombinatorics
