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

private lemma update_false_eq_self {i : Fin n} {x : Fin n → Bool} (hx : x i = false) :
    Function.update x i false = x :=
  Function.update_eq_self_iff.mpr hx.symm

private lemma mem_cubeCompress_true {i : Fin n} {A : Finset (Fin n → Bool)}
    {x : Fin n → Bool} (hx : x i = true) :
    x ∈ cubeCompress i A ↔ x ∈ A ∧ Function.update x i false ∈ A := by
  simp [cubeCompress, hx]

private lemma mem_cubeCompress_false {i : Fin n} {A : Finset (Fin n → Bool)}
    {x : Fin n → Bool} (hx : x i = false) :
    x ∈ cubeCompress i A ↔ x ∈ A ∨ Function.update x i true ∈ A := by
  simp [cubeCompress, hx]

/-- A point of the compression that was not already in `A` sits on the `false` side of
coordinate `i`, and its partner is the point of `A` that pushed it there. -/
private lemma cubeCompress_of_notMem {i : Fin n} {A : Finset (Fin n → Bool)}
    {x : Fin n → Bool} (hx : x ∈ cubeCompress i A) (hxA : x ∉ A) :
    x i = false ∧ Function.update x i true ∈ A := by
  rcases Bool.dichotomy (x i) with hb | hb
  · exact ⟨hb, ((mem_cubeCompress_false hb).1 hx).resolve_left hxA⟩
  · exact absurd ((mem_cubeCompress_true hb).1 hx).1 hxA

/-- **Compression preserves size.**  Each partner pair contributes the same number of points
before and after. -/
theorem card_cubeCompress (i : Fin n) (A : Finset (Fin n → Bool)) :
    (cubeCompress i A).card = A.card := by
  refine Finset.card_nbij'
      (fun x => if x ∈ A then x else Function.update x i true)
      (fun y => if Function.update y i false ∈ A then y else Function.update y i false)
      ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe] at hx ⊢
    by_cases hxA : x ∈ A
    · rwa [if_pos hxA]
    · rw [if_neg hxA]
      exact (cubeCompress_of_notMem hx hxA).2
  · intro y hy
    simp only [Finset.mem_coe] at hy ⊢
    by_cases hy' : Function.update y i false ∈ A
    · rw [if_pos hy']
      rcases Bool.dichotomy (y i) with hb | hb
      · exact (mem_cubeCompress_false hb).2 (Or.inl hy)
      · exact (mem_cubeCompress_true hb).2 ⟨hy, hy'⟩
    · have hb : y i = true := by
        rcases Bool.dichotomy (y i) with hb | hb
        · exact absurd (by rwa [update_false_eq_self hb]) hy'
        · exact hb
      rw [if_neg hy']
      refine (mem_cubeCompress_false (Function.update_self i false y)).2 (Or.inr ?_)
      rwa [Function.update_idem, Function.update_eq_self_iff.mpr hb.symm]
  · intro x hx
    simp only [Finset.mem_coe] at hx
    dsimp only
    by_cases hxA : x ∈ A
    · rw [if_pos hxA]
      rcases Bool.dichotomy (x i) with hb | hb
      · rw [if_pos (by rwa [update_false_eq_self hb])]
      · rw [if_pos ((mem_cubeCompress_true hb).1 hx).2]
    · obtain ⟨hb, -⟩ := cubeCompress_of_notMem hx hxA
      rw [if_neg hxA, Function.update_idem, update_false_eq_self hb, if_neg hxA]
  · intro y hy
    simp only [Finset.mem_coe] at hy
    dsimp only
    by_cases hy' : Function.update y i false ∈ A
    · rw [if_pos hy', if_pos hy]
    · have hb : y i = true := by
        rcases Bool.dichotomy (y i) with hb | hb
        · exact absurd (by rwa [update_false_eq_self hb]) hy'
        · exact hb
      rw [if_neg hy', if_neg hy', Function.update_idem]
      exact Function.update_eq_self_iff.mpr hb.symm

private lemma mem_cubeNbhd_of {A : Finset (Fin n → Bool)} {x a : Fin n → Bool} {t : ℕ}
    (ha : a ∈ A) (h : hammingDist x a ≤ t) : x ∈ cubeNbhd A t := by
  simp only [cubeNbhd, mem_filter, mem_univ, true_and]
  exact ⟨a, ha, h⟩

private lemma hammingDist_update_update_le (i : Fin n) (b : Bool) (x y : Fin n → Bool) :
    hammingDist (Function.update x i b) (Function.update y i b) ≤ hammingDist x y := by
  unfold hammingDist
  refine Finset.card_le_card fun j hj => ?_
  simp only [mem_filter, mem_univ, true_and] at hj ⊢
  by_cases hji : j = i
  · subst hji
    exact absurd (by rw [Function.update_self, Function.update_self]) hj
  · rwa [Function.update_of_ne hji, Function.update_of_ne hji] at hj

private lemma hammingDist_update_le_one (i : Fin n) (b : Bool) (x : Fin n → Bool) :
    hammingDist (Function.update x i b) x ≤ 1 := by
  unfold hammingDist
  refine le_trans (Finset.card_le_card (t := ({i} : Finset (Fin n))) fun j hj => ?_) ?_
  · simp only [mem_filter, mem_univ, true_and] at hj
    simp only [mem_singleton]
    by_contra hji
    exact hj (Function.update_of_ne hji b x)
  · simp

/-- Two points at Hamming distance at most one that already differ at `i` differ *only* at
`i`, so each is obtained from the other by updating that coordinate. -/
private lemma update_eq_of_hammingDist_le_one {i : Fin n} {y z : Fin n → Bool}
    (h : hammingDist y z ≤ 1) (hne : y i ≠ z i) : Function.update y i (z i) = z := by
  unfold hammingDist at h
  have key : ∀ j, j ≠ i → y j = z j := by
    intro j hji
    by_contra hcon
    have hsub : ({i, j} : Finset (Fin n)) ⊆ univ.filter fun k => y k ≠ z k := by
      intro k hk
      simp only [mem_insert, mem_singleton] at hk
      simp only [mem_filter, mem_univ, true_and]
      rcases hk with rfl | rfl
      · exact hne
      · exact hcon
    have hc := Finset.card_le_card hsub
    rw [card_insert_of_notMem (by simpa using Ne.symm hji), card_singleton] at hc
    omega
  funext j
  by_cases hji : j = i
  · rw [hji, Function.update_self]
  · rw [Function.update_of_ne hji]
    exact key j hji

/-- A point of the compression that is already in `A` keeps its partner on the `false` side
inside `A`. -/
private lemma update_false_mem_of_mem {i : Fin n} {A : Finset (Fin n → Bool)}
    {z : Fin n → Bool} (hz : z ∈ cubeCompress i A) (hzA : z ∈ A) :
    Function.update z i false ∈ A := by
  rcases Bool.dichotomy (z i) with hb | hb
  · rwa [update_false_eq_self hb]
  · exact ((mem_cubeCompress_true hb).1 hz).2

/-- Compression and the one-neighbourhood almost commute: compressing first can only land
inside the compression of the neighbourhood. -/
private lemma cubeNbhd_cubeCompress_subset (i : Fin n) (A : Finset (Fin n → Bool)) :
    cubeNbhd (cubeCompress i A) 1 ⊆ cubeCompress i (cubeNbhd A 1) := by
  intro y hy
  simp only [cubeNbhd, mem_filter, mem_univ, true_and] at hy
  obtain ⟨z, hz, hyz⟩ := hy
  rcases Bool.dichotomy (y i) with hyi | hyi
  · refine (mem_cubeCompress_false hyi).2 ?_
    by_cases hzA : z ∈ A
    · exact Or.inl (mem_cubeNbhd_of hzA hyz)
    · obtain ⟨-, hz'⟩ := cubeCompress_of_notMem hz hzA
      exact Or.inr (mem_cubeNbhd_of hz'
        ((hammingDist_update_update_le i true y z).trans hyz))
  · refine (mem_cubeCompress_true hyi).2 ⟨?_, ?_⟩
    · by_cases hzA : z ∈ A
      · exact mem_cubeNbhd_of hzA hyz
      · obtain ⟨-, hz'⟩ := cubeCompress_of_notMem hz hzA
        refine mem_cubeNbhd_of hz' ?_
        have hy' : Function.update y i true = y := Function.update_eq_self_iff.mpr hyi.symm
        calc hammingDist y (Function.update z i true)
            = hammingDist (Function.update y i true) (Function.update z i true) := by rw [hy']
          _ ≤ hammingDist y z := hammingDist_update_update_le i true y z
          _ ≤ 1 := hyz
    · by_cases hzA : z ∈ A
      · exact mem_cubeNbhd_of (update_false_mem_of_mem hz hzA)
          ((hammingDist_update_update_le i false y z).trans hyz)
      · obtain ⟨hzi, hz'⟩ := cubeCompress_of_notMem hz hzA
        have hyz' : Function.update y i false = z := by
          have hu : Function.update y i (z i) = z :=
            update_eq_of_hammingDist_le_one hyz (by simp [hyi, hzi])
          rwa [hzi] at hu
        rw [hyz']
        refine mem_cubeNbhd_of hz' ?_
        rw [hammingDist_comm]
        exact hammingDist_update_le_one i true z

/-- **Compression does not increase the neighbourhood.**  This is the step that makes the
compression argument work at all, and the one Mathlib's `UV`/`Down` results do *not* give —
theirs bound the shadow of a `k`-uniform family, not the neighbourhood of an arbitrary
subset. -/
theorem card_cubeNbhd_cubeCompress_le (i : Fin n) (A : Finset (Fin n → Bool)) :
    (cubeNbhd (cubeCompress i A) 1).card ≤ (cubeNbhd A 1).card := by
  exact (Finset.card_le_card (cubeNbhd_cubeCompress_subset i A)).trans_eq
    (card_cubeCompress i (cubeNbhd A 1))

end ProbMethodCombinatorics
