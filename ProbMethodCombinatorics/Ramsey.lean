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

/-- **Erdős–Szekeres** (Zhao, Remark 1.1.5), in the off-diagonal form the induction needs:
any vertex set with at least `(k + l).choose k` elements carries, under every symmetric
red/blue edge colouring, either a `true`-coloured clique on `k` vertices or a
`false`-coloured clique on `l` vertices.

The vertex set is an arbitrary `Finset`, not an initial segment, so that the inductive step
— fix a vertex and recurse on the two colour classes of its neighbourhood — stays inside the
statement. -/
theorem exists_monochromatic_of_choose_le {α : Type*} [DecidableEq α] (k : ℕ) :
    ∀ (l : ℕ) (V : Finset α) (c : α → α → Bool), (∀ i j, c i j = c j i) →
      (k + l).choose k ≤ V.card →
      (∃ S ⊆ V, S.card = k ∧ ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c i j = true) ∨
        (∃ S ⊆ V, S.card = l ∧ ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c i j = false) := by
  induction k with
  | zero => exact fun l V c _ _ => Or.inl ⟨∅, empty_subset _, card_empty, by simp⟩
  | succ k ih =>
    intro l
    induction l with
    | zero => exact fun V c _ _ => Or.inr ⟨∅, empty_subset _, card_empty, by simp⟩
    | succ l ihl =>
      intro V c hc hcard
      -- Pascal's rule splits the hypothesis into the two inductive budgets.
      have hcard' : (k + (l + 1)).choose k + (k + 1 + l).choose (k + 1) ≤ V.card := by
        have h1 : k + 1 + (l + 1) = k + l + 1 + 1 := by omega
        have h2 : k + (l + 1) = k + l + 1 := by omega
        have h3 : k + 1 + l = k + l + 1 := by omega
        rw [h2, h3]
        rwa [h1, Nat.choose_succ_succ] at hcard
      have hpos : 0 < (k + (l + 1)).choose k := Nat.choose_pos (Nat.le_add_right k (l + 1))
      obtain ⟨v, hv⟩ : V.Nonempty := card_pos.mp (by omega)
      set W : Finset α := V.erase v with hW
      set A : Finset α := W.filter (fun w => c v w = true) with hA
      set B : Finset α := W.filter (fun w => ¬ c v w = true) with hB
      have hAB : A.card + B.card = W.card := card_filter_add_card_filter_not _
      have hWcard : W.card = V.card - 1 := by rw [hW, card_erase_of_mem hv]
      have hAV : ∀ w ∈ A, w ∈ V := fun w hw => mem_of_mem_erase (mem_filter.mp hw).1
      have hBV : ∀ w ∈ B, w ∈ V := fun w hw => mem_of_mem_erase (mem_filter.mp hw).1
      have hvA : v ∉ A := fun hvA => notMem_erase v V (mem_filter.mp hvA).1
      have hvB : v ∉ B := fun hvB => notMem_erase v V (mem_filter.mp hvB).1
      have hsplit : (k + (l + 1)).choose k ≤ A.card ∨
          (k + 1 + l).choose (k + 1) ≤ B.card := by
        by_contra hcon
        simp only [not_or, not_le] at hcon
        omega
      rcases hsplit with hle | hle
      · -- Enough `true`-neighbours: recurse there and prepend `v` to a `true`-clique.
        rcases ih (l + 1) A c hc hle with ⟨S, hSA, hScard, hS⟩ | ⟨S, hSA, hScard, hS⟩
        · refine Or.inl ⟨insert v S, ?_, ?_, ?_⟩
          · exact insert_subset hv fun w hw => hAV w (hSA hw)
          · rw [card_insert_of_notMem fun hvS => hvA (hSA hvS), hScard]
          · intro i hi j hj hij
            rcases mem_insert.mp hi with rfl | hiS
            · rcases mem_insert.mp hj with rfl | hjS
              · exact absurd rfl hij
              · exact (mem_filter.mp (hSA hjS)).2
            · rcases mem_insert.mp hj with rfl | hjS
              · rw [hc]; exact (mem_filter.mp (hSA hiS)).2
              · exact hS i hiS j hjS hij
        · exact Or.inr ⟨S, fun w hw => hAV w (hSA hw), hScard, hS⟩
      · -- Enough `false`-neighbours: recurse there and prepend `v` to a `false`-clique.
        rcases ihl B c hc hle with ⟨S, hSB, hScard, hS⟩ | ⟨S, hSB, hScard, hS⟩
        · exact Or.inl ⟨S, fun w hw => hBV w (hSB hw), hScard, hS⟩
        · refine Or.inr ⟨insert v S, ?_, ?_, ?_⟩
          · exact insert_subset hv fun w hw => hBV w (hSB hw)
          · rw [card_insert_of_notMem fun hvS => hvB (hSB hvS), hScard]
          · intro i hi j hj hij
            rcases mem_insert.mp hi with rfl | hiS
            · rcases mem_insert.mp hj with rfl | hjS
              · exact absurd rfl hij
              · exact Bool.eq_false_iff.mpr (mem_filter.mp (hSB hjS)).2
            · rcases mem_insert.mp hj with rfl | hjS
              · rw [hc]; exact Bool.eq_false_iff.mpr (mem_filter.mp (hSB hiS)).2
              · exact hS i hiS j hjS hij

/-- **Ramsey's theorem** (Ramsey 1929; Zhao, Section 1.1): `R(k, k)` is finite, i.e. some
complete graph is large enough that every red/blue edge colouring of it has a monochromatic
`k`-clique.  Without this the infimum defining `ramseyNumber` could be taken over the empty set. -/
theorem exists_ramseyProperty (k : ℕ) : ∃ n, RamseyProperty n k := by
  refine ⟨(k + k).choose k, fun c hc => ?_⟩
  have hcard : (k + k).choose k ≤ (univ : Finset (Fin ((k + k).choose k))).card := by
    rw [card_univ, Fintype.card_fin]
  rcases exists_monochromatic_of_choose_le k k univ c hc hcard with
    ⟨S, -, hScard, hS⟩ | ⟨S, -, hScard, hS⟩
  · exact ⟨S, hScard, true, hS⟩
  · exact ⟨S, hScard, false, hS⟩

/-- **Erdős 1947** (Zhao, Theorem 1.1.2), stated for the Ramsey number: if
`2 * (n.choose k) < 2 ^ (k.choose 2)` then `R(k, k) > n`. -/
theorem lt_ramseyNumber (n k : ℕ) (hk : 2 ≤ k)
    (h : 2 * n.choose k < 2 ^ k.choose 2) : n < ramseyNumber k := by
  sorry

end ProbMethodCombinatorics
