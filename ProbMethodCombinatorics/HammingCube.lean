import Mathlib.InformationTheory.Hamming
import ProbMethodCombinatorics.Concentration

/-!
# Groundwork for §9.4: neighbourhoods in the Hamming cube

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), §9.4.

**This file is not Harper's theorem.**  Theorem 9.4.3 is *quoted* by the source rather than
proved, and its formalisation is a separate project of research scale — see the plan in
`roadmap/concentration.md`, whose step 5 (a set fixed by every compression need not be an
initial segment of the simplicial order) is not currently routable.  What is here is the
vocabulary and the inductive engine that any proof of it needs, and which are worth having
independently.

`hammingDist` comes from `Mathlib/InformationTheory/Hamming.lean`; the neighbourhood, the ball
and the slice decomposition are authored here, Mathlib having none of them.

The slice decomposition was checked exhaustively before being stated: over every subset of
every cube with `n ≤ 4` — 65812 subsets — both inclusions hold with no exceptions.
-/

namespace ProbMethodCombinatorics

open Finset

variable {n : ℕ}

/-- The `t`-neighbourhood of `A` in the Hamming cube. -/
def cubeNbhd (A : Finset (Fin n → Bool)) (t : ℕ) : Finset (Fin n → Bool) :=
  univ.filter fun x => ∃ a ∈ A, hammingDist x a ≤ t

/-- The Hamming ball of radius `r` about `c`. -/
def cubeBall (c : Fin n → Bool) (r : ℕ) : Finset (Fin n → Bool) :=
  univ.filter fun x => hammingDist x c ≤ r

/-- The slice of `A` on which the last coordinate is `b`, as a subset of the smaller cube. -/
def cubeSlice (A : Finset (Fin (n + 1) → Bool)) (b : Bool) : Finset (Fin n → Bool) :=
  univ.filter fun x => Fin.snoc x b ∈ A

/-- Neighbourhoods are monotone in the set. -/
theorem cubeNbhd_mono {A B : Finset (Fin n → Bool)} (h : A ⊆ B) (t : ℕ) :
    cubeNbhd A t ⊆ cubeNbhd B t := by
  sorry

private theorem hammingDist_snoc_snoc (x y : Fin n → Bool) (b c : Bool) :
    hammingDist (Fin.snoc x b : Fin (n + 1) → Bool) (Fin.snoc y c) =
      hammingDist x y + if b = c then 0 else 1 := by
  simp only [hammingDist, Finset.card_filter, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
    Fin.snoc_last]
  cases b <;> cases c <;> simp

private theorem hammingDist_snoc_same (x y : Fin n → Bool) (b : Bool) :
    hammingDist (Fin.snoc x b : Fin (n + 1) → Bool) (Fin.snoc y b) = hammingDist x y := by
  simp [hammingDist_snoc_snoc]

private theorem hammingDist_snoc_not (x : Fin n → Bool) (b : Bool) :
    hammingDist (Fin.snoc x b : Fin (n + 1) → Bool) (Fin.snoc x !b) = 1 := by
  rw [hammingDist_snoc_snoc]
  cases b <;> simp

/-- **The slice decomposition**, the inductive engine of Harper's theorem: a point of the
smaller cube lands in the `b`-slice of `A`'s neighbourhood as soon as it is either adjacent to
the `b`-slice of `A`, or already in the *opposite* slice — the second case being the step
across the coordinate being split on.

Both halves of the source's `(A_t)₀ ⊇ (A₀)_t ∪ (A₁)_{t-1}` at `t = 1`, stated once by
quantifying over `b`. -/
theorem cubeNbhd_one_slice_superset (A : Finset (Fin (n + 1) → Bool)) (b : Bool) :
    cubeNbhd (cubeSlice A b) 1 ∪ cubeSlice A (!b) ⊆ cubeSlice (cubeNbhd A 1) b := by
  intro x hx
  simp only [mem_union, cubeNbhd, cubeSlice, mem_filter, mem_univ, true_and] at hx ⊢
  rcases hx with ⟨y, hy, hxy⟩ | hx
  · exact ⟨Fin.snoc y b, hy, by rwa [hammingDist_snoc_same]⟩
  · exact ⟨Fin.snoc x !b, hx, by rw [hammingDist_snoc_not]⟩

end ProbMethodCombinatorics
