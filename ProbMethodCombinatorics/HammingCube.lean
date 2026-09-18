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

Everything here was checked exhaustively before being stated.  The slice decomposition holds
over every subset of every cube with `n ≤ 4` (65812 subsets); the two compression lemmas hold
over every subset and every coordinate in the same range (262948 checks).  No exceptions in
either case.
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
  intro x hx
  simp only [cubeNbhd, mem_filter, mem_univ, true_and] at hx ⊢
  obtain ⟨a, haA, hd⟩ := hx
  exact ⟨a, h haA, hd⟩

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

/-- **Down-compression** in coordinate `i`: push each element of `A` to the `false` side of
coordinate `i` whenever that slot is free.

A point with `x i = false` survives if it was already in `A` or if its partner was; a point
with `x i = true` survives only if both it and its partner were in `A`, the partner having
otherwise absorbed it. -/
def cubeCompress (i : Fin n) (A : Finset (Fin n → Bool)) : Finset (Fin n → Bool) :=
  univ.filter fun x =>
    if x i then x ∈ A ∧ Function.update x i false ∈ A
    else x ∈ A ∨ Function.update x i true ∈ A

/-- **Compression preserves size.**  Each partner pair contributes the same number of points
before and after. -/
theorem card_cubeCompress (i : Fin n) (A : Finset (Fin n → Bool)) :
    (cubeCompress i A).card = A.card := by
  sorry

/-- **Compression does not increase the neighbourhood.**  This is the step that makes the
compression argument work at all, and the one Mathlib's `UV`/`Down` results do *not* give —
theirs bound the shadow of a `k`-uniform family, not the neighbourhood of an arbitrary
subset. -/
theorem card_cubeNbhd_cubeCompress_le (i : Fin n) (A : Finset (Fin n → Bool)) :
    (cubeNbhd (cubeCompress i A) 1).card ≤ (cubeNbhd A 1).card := by
  sorry

end ProbMethodCombinatorics
