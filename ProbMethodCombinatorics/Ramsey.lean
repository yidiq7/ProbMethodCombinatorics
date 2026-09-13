import Mathlib.Algebra.Order.BigOperators.Group.Finset
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
  intro c hc
  obtain ⟨S, hcard, b, hb⟩ :=
    h (fun i j => c (Fin.castLE hmn i) (Fin.castLE hmn j)) fun i j => hc _ _
  refine ⟨S.map (Fin.castLEEmb hmn), by rw [card_map]; exact hcard, b, ?_⟩
  intro i hi j hj hij
  obtain ⟨i, hiS, rfl⟩ := mem_map.1 hi
  obtain ⟨j, hjS, rfl⟩ := mem_map.1 hj
  exact hb i hiS j hjS fun hij' => hij (congrArg _ hij')

/-- **Erdős 1947** (Zhao, Theorem 1.1.2): if `2 * (n.choose k) < 2 ^ (k.choose 2)` then some red/blue
edge colouring of `K n` has no monochromatic `K k`.  The hypothesis is the book's
`(n.choose k) * 2 ^ (1 - k.choose 2) < 1`, cleared of denominators. -/
theorem exists_coloring_no_isMonochromatic (n k : ℕ) (hk : 2 ≤ k)
    (h : 2 * n.choose k < 2 ^ k.choose 2) :
    ∃ c : Fin n → Fin n → Bool, (∀ i j, c i j = c j i) ∧
      ∀ S : Finset (Fin n), S.card = k → ¬ IsMonochromatic c S := by
  by_cases hkn : k ≤ n
  · -- A colouring is a set `A` of edges, an edge being a two-element set of vertices; `A`
    -- collects the edges coloured `true`.  `D` is the edge set of `K n`.
    set D : Finset (Finset (Fin n)) := univ.powersetCard 2 with hDdef
    have hDcard : D.card = n.choose 2 := by
      rw [hDdef, card_powersetCard, card_univ, Fintype.card_fin]
    have hPsub : ∀ S : Finset (Fin n), S.powersetCard 2 ⊆ D := by
      intro S T hT
      rw [mem_powersetCard] at hT ⊢
      exact ⟨subset_univ T, hT.2⟩
    have hkn2 : k.choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hkn
    -- A colouring spoiled by `S` either contains every edge inside `S` or misses them all,
    -- so the spoiled colourings are covered by two copies of the powerset of `D \ S`-edges.
    set Bad : Finset (Finset (Finset (Fin n))) :=
      (univ.powersetCard k).biUnion (fun S =>
        (D \ S.powersetCard 2).powerset ∪
          (D \ S.powersetCard 2).powerset.image (fun A => A ∪ S.powersetCard 2)) with hBaddef
    have hBadcard : Bad.card < D.powerset.card := by
      have h1 : Bad.card ≤ n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2)) := by
        rw [hBaddef]
        refine le_trans
          (card_biUnion_le_card_mul _ _ (2 * 2 ^ (n.choose 2 - k.choose 2)) ?_) ?_
        · intro S hS
          rw [mem_powersetCard] at hS
          have hPc : (D \ S.powersetCard 2).card = n.choose 2 - k.choose 2 := by
            rw [card_sdiff_of_subset (hPsub S), hDcard, card_powersetCard, hS.2]
          have e1 : (D \ S.powersetCard 2).powerset.card = 2 ^ (n.choose 2 - k.choose 2) := by
            rw [card_powerset, hPc]
          have e2 : ((D \ S.powersetCard 2).powerset.image
              (fun A => A ∪ S.powersetCard 2)).card ≤ 2 ^ (n.choose 2 - k.choose 2) :=
            le_trans card_image_le (le_of_eq e1)
          have := card_union_le ((D \ S.powersetCard 2).powerset)
            ((D \ S.powersetCard 2).powerset.image (fun A => A ∪ S.powersetCard 2))
          omega
        · rw [card_powersetCard, card_univ, Fintype.card_fin]
      have h3 : n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2)) < 2 ^ n.choose 2 := by
        have h4 : 2 * n.choose k * 2 ^ (n.choose 2 - k.choose 2)
            < 2 ^ k.choose 2 * 2 ^ (n.choose 2 - k.choose 2) :=
          Nat.mul_lt_mul_of_lt_of_le h (le_refl _) (Nat.two_pow_pos _)
        rw [← pow_add, Nat.add_sub_cancel' hkn2] at h4
        calc n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2))
            = 2 * n.choose k * 2 ^ (n.choose 2 - k.choose 2) := by
              rw [← Nat.mul_assoc, Nat.mul_comm (n.choose k) 2]
          _ < 2 ^ n.choose 2 := h4
      rw [card_powerset, hDcard]
      omega
    obtain ⟨A, hAmem, hAnot⟩ :=
      not_subset.mp (fun hsub => absurd (card_le_card hsub) (not_le.mpr hBadcard))
    have hAD : A ⊆ D := mem_powerset.mp hAmem
    refine ⟨fun i j => decide ({i, j} ∈ A), fun i j => by simp only [pair_comm i j], ?_⟩
    intro S hScard hmono
    refine hAnot ?_
    rw [hBaddef, mem_biUnion]
    refine ⟨S, mem_powersetCard.mpr ⟨subset_univ S, hScard⟩, ?_⟩
    obtain ⟨b, hb⟩ := hmono
    cases b with
    | false =>
      refine mem_union_left _ (mem_powerset.mpr fun T hT => mem_sdiff.mpr ⟨hAD hT, ?_⟩)
      intro hTP
      rw [mem_powersetCard] at hTP
      obtain ⟨i, j, hij, rfl⟩ := card_eq_two.mp hTP.2
      have := hb i (hTP.1 (by simp)) j (hTP.1 (by simp)) hij
      simp only [decide_eq_false_iff_not] at this
      exact this hT
    | true =>
      have hPA : S.powersetCard 2 ⊆ A := by
        intro T hT
        rw [mem_powersetCard] at hT
        obtain ⟨i, j, hij, rfl⟩ := card_eq_two.mp hT.2
        have := hb i (hT.1 (by simp)) j (hT.1 (by simp)) hij
        simpa using this
      refine mem_union_right _ (mem_image.mpr ⟨A \ S.powersetCard 2, ?_, ?_⟩)
      · exact mem_powerset.mpr fun T hT =>
          mem_sdiff.mpr ⟨hAD (mem_sdiff.mp hT).1, (mem_sdiff.mp hT).2⟩
      · rw [sdiff_union_of_subset hPA]
  · -- Fewer than `k` vertices: no `k`-set exists, so any colouring will do.
    refine ⟨fun _ _ => false, fun i j => rfl, ?_⟩
    intro S hS _
    have hle : S.card ≤ n := by simpa using card_le_univ S
    omega

/-- **Ramsey's theorem** (Ramsey 1929; Zhao, Section 1.1): `R(k, k)` is finite, i.e. some
complete graph is large enough that every red/blue edge colouring of it has a monochromatic
`k`-clique.  Without this the infimum defining `ramseyNumber` could be taken over the empty set. -/
theorem exists_ramseyProperty (k : ℕ) : ∃ n, RamseyProperty n k := by
  sorry

/-- **Erdős 1947** (Zhao, Theorem 1.1.2), stated for the Ramsey number: if
`2 * (n.choose k) < 2 ^ (k.choose 2)` then `R(k, k) > n`. -/
theorem lt_ramseyNumber (n k : ℕ) (hk : 2 ≤ k)
    (h : 2 * n.choose k < 2 ^ k.choose 2) : n < ramseyNumber k := by
  obtain ⟨c, hsymm, hc⟩ := exists_coloring_no_isMonochromatic n k hk h
  have hne : {m | RamseyProperty m k}.Nonempty := exists_ramseyProperty k
  have hmem : RamseyProperty (ramseyNumber k) k := Nat.sInf_mem hne
  by_contra hlt
  obtain ⟨S, hcard, hmono⟩ := hmem.mono (Nat.not_lt.1 hlt) c hsymm
  exact hc S hcard hmono

end ProbMethodCombinatorics
