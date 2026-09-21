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
  obtain ⟨c, hsymm, hc⟩ := exists_coloring_no_isMonochromatic n k hk h
  have hne : {m | RamseyProperty m k}.Nonempty := exists_ramseyProperty k
  have hmem : RamseyProperty (ramseyNumber k) k := Nat.sInf_mem hne
  by_contra hlt
  obtain ⟨S, hcard, hmono⟩ := hmem.mono (Nat.not_lt.1 hlt) c hsymm
  exact hc S hcard hmono

/-- **Erdős 1961, the alteration bound** (Zhao, Theorem 1.1.6), stated for the Ramsey number:
delete one vertex from each monochromatic `k`-set of a random colouring of `K_n` and what
survives is a colouring with none, so `R(k, k) > n - binom(n,k) * 2 ^ (1 - binom(k,2))`.

In `ℕ` the conclusion is read off a surviving size `m`: the hypothesis
`2 * binom(n,k) ≤ (n - m) * 2 ^ binom(k,2)` says exactly that the expected number of
monochromatic `k`-sets, `2 * binom(n,k) / 2 ^ binom(k,2)`, is at most the number `n - m` of
vertices we are allowed to delete.

**This is §1.1's middle bound, and it is weaker than the union bound for small `k`.**
`lt_ramseyNumber` (Theorem 1.1.2) gives `R > 3, 6, 11, 17` at `k = 3, 4, 5, 6`, where this gives
`3, 5, 10, 17`.  **Alteration first wins at `k = 7`** (`28` against `27`) and the margin then
grows: `46` against `42` at `k = 8`, `115` against `100` at `k = 10`, `275` against `231` at
`k = 12`.  **A smaller
number at small `k` is the expected behaviour, not a defect** — the alteration argument pays a
constant to win asymptotically, and Remark 1.1.7's optimisation over `n` is what turns that into
the usual `(1/e + o(1)) k 2 ^ (k/2)`.  That asymptotic form is a separate node and is not stated
here.

`hmn : m ≤ n` is needed because the subtraction is truncated: without it `n - m = 0` and the
hypothesis would read `binom(n,k) = 0`, which is a different claim.  It is load-bearing against
the statement, not just the proof: at `k = 2, n = 0, m = 5` the hypothesis holds vacuously while
`5 < ramseyNumber 2 = 2` is false.

`hk : 2 ≤ k` is stronger than the proof needs — only `0 < k` is used, for the non-emptiness of a
`k`-set — and it is kept deliberately, matching the other Ramsey bounds in this file, so that the
statement is about the mathematics rather than about degenerate cases.  Some lower bound is
required: at `k = 0, m = 0, n = 2` the hypothesis reads `2 ≤ 2` while `ramseyNumber 0 = 0`. -/
theorem lt_ramseyNumber_of_alteration (m n k : ℕ) (hk : 2 ≤ k) (hmn : m ≤ n)
    (h : 2 * n.choose k ≤ (n - m) * 2 ^ k.choose 2) : m < ramseyNumber k := by
  -- The whole argument produces a colouring of `K m` with no monochromatic `K k`.
  have main : ∃ c : Fin m → Fin m → Bool, (∀ i j, c i j = c j i) ∧
      ∀ S : Finset (Fin m), S.card = k → ¬ IsMonochromatic c S := by
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
      -- `Mono A` collects the `k`-sets all of whose edges `A` contains, and those none of
      -- whose edges it contains: the monochromatic `k`-sets of the colouring `A`.
      set Mono : Finset (Finset (Fin n)) → Finset (Finset (Fin n)) := fun A =>
        (univ.powersetCard k).filter
          (fun S => S.powersetCard 2 ⊆ A ∨ S.powersetCard 2 ∩ A = ∅) with hMonodef
      -- One `k`-set is monochromatic for at most `2 * 2 ^ (binom(n,2) - binom(k,2))`
      -- colourings: its own edges go all in or all out, the others are free.
      have hfib : ∀ S : Finset (Fin n), S ∈ univ.powersetCard k →
          (D.powerset.filter
              (fun A => S.powersetCard 2 ⊆ A ∨ S.powersetCard 2 ∩ A = ∅)).card
            ≤ 2 * 2 ^ (n.choose 2 - k.choose 2) := by
        intro S hS
        rw [mem_powersetCard] at hS
        have hPc : (D \ S.powersetCard 2).card = n.choose 2 - k.choose 2 := by
          rw [card_sdiff_of_subset (hPsub S), hDcard, card_powersetCard, hS.2]
        have e1 : (D \ S.powersetCard 2).powerset.card = 2 ^ (n.choose 2 - k.choose 2) := by
          rw [card_powerset, hPc]
        have hsub : D.powerset.filter
            (fun A => S.powersetCard 2 ⊆ A ∨ S.powersetCard 2 ∩ A = ∅) ⊆
              (D \ S.powersetCard 2).powerset.image (fun B => B ∪ S.powersetCard 2) ∪
                (D \ S.powersetCard 2).powerset := by
          intro A hA
          rw [mem_filter, mem_powerset] at hA
          rcases hA.2 with hin | hout
          · refine mem_union_left _
              (mem_image.mpr ⟨A \ S.powersetCard 2, mem_powerset.mpr ?_, ?_⟩)
            · exact fun T hT => mem_sdiff.mpr ⟨hA.1 (mem_sdiff.mp hT).1, (mem_sdiff.mp hT).2⟩
            · rw [sdiff_union_of_subset hin]
          · refine mem_union_right _ (mem_powerset.mpr fun T hT => mem_sdiff.mpr ⟨hA.1 hT, ?_⟩)
            intro hTS
            have hTmem : T ∈ S.powersetCard 2 ∩ A := mem_inter.mpr ⟨hTS, hT⟩
            rw [hout] at hTmem
            exact notMem_empty T hTmem
        have h2 := card_le_card hsub
        have h3 := card_union_le ((D \ S.powersetCard 2).powerset.image
          (fun B => B ∪ S.powersetCard 2)) ((D \ S.powersetCard 2).powerset)
        have h4 : ((D \ S.powersetCard 2).powerset.image
            (fun B => B ∪ S.powersetCard 2)).card ≤ 2 ^ (n.choose 2 - k.choose 2) :=
          le_trans card_image_le (le_of_eq e1)
        omega
      -- Double count the pairs (colouring, monochromatic `k`-set of it).
      have hswap : ∑ A ∈ D.powerset, (Mono A).card
          = ∑ S ∈ univ.powersetCard k, (D.powerset.filter
              (fun A => S.powersetCard 2 ⊆ A ∨ S.powersetCard 2 ∩ A = ∅)).card := by
        simp only [hMonodef, card_eq_sum_ones, sum_filter]
        exact sum_comm
      have hsum : ∑ A ∈ D.powerset, (Mono A).card
          ≤ n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2)) := by
        rw [hswap]
        refine le_trans (sum_le_sum hfib) ?_
        rw [sum_const_nat (m := 2 * 2 ^ (n.choose 2 - k.choose 2)) fun _ _ => rfl,
          card_powersetCard, card_univ, Fintype.card_fin]
      -- Averaging: some colouring has at most `n - m` monochromatic `k`-sets.
      obtain ⟨A, -, hAcard⟩ : ∃ A ∈ D.powerset, (Mono A).card ≤ n - m := by
        by_contra hcon
        have hall : ∀ A ∈ D.powerset, n - m + 1 ≤ (Mono A).card := fun A hA =>
          Nat.not_le.1 fun hle => hcon ⟨A, hA, hle⟩
        have hconst : ∑ _A ∈ D.powerset, (n - m + 1) = 2 ^ n.choose 2 * (n - m + 1) := by
          rw [sum_const_nat (m := n - m + 1) fun _ _ => rfl, card_powerset, hDcard]
        have hlow : 2 ^ n.choose 2 * (n - m + 1) ≤ ∑ A ∈ D.powerset, (Mono A).card := by
          rw [← hconst]
          exact sum_le_sum hall
        have hup : n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2))
            ≤ 2 ^ n.choose 2 * (n - m) := by
          have h1 : 2 * n.choose k * 2 ^ (n.choose 2 - k.choose 2)
              ≤ (n - m) * 2 ^ k.choose 2 * 2 ^ (n.choose 2 - k.choose 2) :=
            Nat.mul_le_mul h (le_refl (2 ^ (n.choose 2 - k.choose 2)))
          rw [Nat.mul_assoc (n - m) (2 ^ k.choose 2) (2 ^ (n.choose 2 - k.choose 2)),
            ← pow_add, Nat.add_sub_cancel' hkn2] at h1
          calc n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2))
              = 2 * n.choose k * 2 ^ (n.choose 2 - k.choose 2) := by
                rw [← Nat.mul_assoc, Nat.mul_comm (n.choose k) 2]
            _ ≤ (n - m) * 2 ^ n.choose 2 := h1
            _ = 2 ^ n.choose 2 * (n - m) := Nat.mul_comm _ _
        have hfin := Nat.le_of_mul_le_mul_left (hlow.trans (hsum.trans hup))
          (Nat.two_pow_pos (n.choose 2))
        omega
      -- Delete the least vertex of each monochromatic `k`-set of that colouring.
      set c : Fin n → Fin n → Bool := fun i j => decide ({i, j} ∈ A) with hcdef
      have hcsymm : ∀ i j, c i j = c j i := by
        intro i j
        rw [hcdef]
        simp only [pair_comm i j]
      have hmonoMem : ∀ S : Finset (Fin n), S.card = k → IsMonochromatic c S → S ∈ Mono A := by
        intro S hScard hmono
        obtain ⟨b, hb⟩ := hmono
        rw [hMonodef]
        refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ S, hScard⟩, ?_⟩
        cases b with
        | true =>
          refine Or.inl fun T hT => ?_
          rw [mem_powersetCard] at hT
          obtain ⟨i, j, hij, rfl⟩ := card_eq_two.mp hT.2
          have hcij := hb i (hT.1 (by simp)) j (hT.1 (by simp)) hij
          rw [hcdef] at hcij
          simpa using hcij
        | false =>
          refine Or.inr (eq_empty_iff_forall_notMem.mpr fun T hT => ?_)
          rw [mem_inter, mem_powersetCard] at hT
          obtain ⟨i, j, hij, rfl⟩ := card_eq_two.mp hT.1.2
          have hcij := hb i (hT.1.1 (by simp)) j (hT.1.1 (by simp)) hij
          rw [hcdef] at hcij
          simp only [decide_eq_false_iff_not] at hcij
          exact hcij hT.2
      set Del : Finset (Fin n) :=
        (Mono A).biUnion (fun S => if hS : S.Nonempty then {S.min' hS} else ∅) with hDeldef
      have hDelcard : Del.card ≤ n - m := by
        refine le_trans (card_biUnion_le_card_mul _ _ 1 ?_) ?_
        · intro S _
          by_cases hS : S.Nonempty
          · rw [dif_pos hS, card_singleton]
          · rw [dif_neg hS, card_empty]
            exact Nat.zero_le 1
        · rw [Nat.mul_one]
          exact hAcard
      have hsurv : m ≤ (univ \ Del).card := by
        rw [card_univ_sdiff, Fintype.card_fin]
        omega
      obtain ⟨T, hTsub, hTcard⟩ := exists_subset_card_eq hsurv
      -- Restrict the colouring along an injection onto `m` of the surviving vertices.
      obtain ⟨f, hfinj, hfmem⟩ : ∃ f : Fin m → Fin n, Function.Injective f ∧ ∀ i, f i ∈ T := by
        refine ⟨fun i => (T.equivFin.symm (Fin.cast hTcard.symm i) : Fin n), ?_, ?_⟩
        · intro a b hab
          have h' := T.equivFin.symm.injective (Subtype.ext hab)
          simpa [Fin.ext_iff] using h'
        · exact fun i => (T.equivFin.symm (Fin.cast hTcard.symm i)).2
      refine ⟨fun i j => c (f i) (f j), fun i j => hcsymm _ _, ?_⟩
      intro S hScard hmono
      obtain ⟨b, hb⟩ := hmono
      have himcard : (S.image f).card = k := by
        rw [card_image_of_injective _ hfinj, hScard]
      have himmono : IsMonochromatic c (S.image f) := by
        refine ⟨b, fun i hi j hj hij => ?_⟩
        obtain ⟨a, ha, rfl⟩ := mem_image.1 hi
        obtain ⟨d, hd, rfl⟩ := mem_image.1 hj
        exact hb a ha d hd fun had => hij (congrArg f had)
      have hne : (S.image f).Nonempty := by
        rw [← card_pos, himcard]
        omega
      have hdel : (S.image f).min' hne ∈ Del := by
        rw [hDeldef]
        refine mem_biUnion.mpr ⟨S.image f, hmonoMem _ himcard himmono, ?_⟩
        rw [dif_pos hne]
        exact mem_singleton_self _
      have hminT : (S.image f).min' hne ∈ T := by
        obtain ⟨a, -, ha⟩ := mem_image.1 (min'_mem _ hne)
        rw [← ha]
        exact hfmem a
      exact (mem_sdiff.mp (hTsub hminT)).2 hdel
    · -- Fewer than `k` vertices in all: no `k`-set exists, so any colouring will do.
      refine ⟨fun _ _ => false, fun i j => rfl, ?_⟩
      intro S hS _
      have hle : S.card ≤ m := by simpa using card_le_univ S
      omega
  obtain ⟨c, hsymm, hc⟩ := main
  have hne : {p | RamseyProperty p k}.Nonempty := exists_ramseyProperty k
  have hmem : RamseyProperty (ramseyNumber k) k := Nat.sInf_mem hne
  by_contra hlt
  obtain ⟨S, hcard, hmono⟩ := hmem.mono (Nat.not_lt.1 hlt) c hsymm
  exact hc S hcard hmono

end ProbMethodCombinatorics
