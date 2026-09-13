import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Chapter 1.2: Set systems — Bollobás' two families theorem

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Theorem 1.2.6.

Sperner's theorem, the LYM inequality and Erdős–Ko–Rado, the other results of Section 1.2, are
already in Mathlib (`IsAntichain.sperner`, `Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose`,
`Finset.erdos_ko_rado`), so only Bollobás' theorem is formalized here.
-/

namespace ProbMethodCombinatorics

open Finset

variable {α : Type*} [DecidableEq α]

/-- An ordering of a ground set `S` with `S.card = n` is an embedding `{x // x ∈ S} ↪ Fin n`;
`orderingsPrecede S A B n` collects those orderings placing every element of `A` strictly before
every element of `B`. -/
noncomputable def orderingsPrecede (S A B : Finset α) (n : ℕ) : Finset ({x // x ∈ S} ↪ Fin n) :=
  Finset.univ.filter fun r => ∀ a b : {x // x ∈ S}, (a : α) ∈ A → (b : α) ∈ B → r a < r b

/-- Membership in `orderingsPrecede` unfolds to the defining precedence condition. -/
theorem mem_orderingsPrecede {S A B : Finset α} {n : ℕ} {r : {x // x ∈ S} ↪ Fin n} :
    r ∈ orderingsPrecede S A B n ↔
      ∀ a b : {x // x ∈ S}, (a : α) ∈ A → (b : α) ∈ B → r a < r b := by
  simp [orderingsPrecede]

/-- Removing the element an ordering ranks first gives an ordering of the rest of the ground set. -/
def eraseOrdering {S : Finset α} {x : α} {n : ℕ} (hx : x ∈ S)
    (r : {y // y ∈ S} ↪ Fin (n + 1)) (hr : r ⟨x, hx⟩ = 0) :
    {y // y ∈ S.erase x} ↪ Fin n where
  toFun y := (r ⟨y.1, Finset.mem_of_mem_erase y.2⟩).pred (fun h =>
    Finset.ne_of_mem_erase y.2 (congrArg Subtype.val (r.injective (h.trans hr.symm))))
  inj' := by
    intro y z h
    have h2 := congrArg Subtype.val (r.injective (Fin.pred_inj.mp h))
    exact Subtype.ext h2

/-- `eraseOrdering` shifts every rank down by one. -/
theorem succ_eraseOrdering {S : Finset α} {x : α} {n : ℕ} (hx : x ∈ S)
    (r : {y // y ∈ S} ↪ Fin (n + 1)) (hr : r ⟨x, hx⟩ = 0) (y : {y // y ∈ S.erase x}) :
    (eraseOrdering hx r hr y).succ = r ⟨y.1, Finset.mem_of_mem_erase y.2⟩ :=
  Fin.succ_pred (r ⟨y.1, Finset.mem_of_mem_erase y.2⟩) (fun h =>
    Finset.ne_of_mem_erase y.2 (congrArg Subtype.val (r.injective (h.trans hr.symm))))

/-- Prepending `x` to an ordering of `S.erase x` gives an ordering of `S` ranking `x` first. -/
def consOrdering {S : Finset α} {x : α} {n : ℕ}
    (r : {y // y ∈ S.erase x} ↪ Fin n) : {y // y ∈ S} ↪ Fin (n + 1) where
  toFun y := if h : y.1 = x then 0 else (r ⟨y.1, Finset.mem_erase.mpr ⟨h, y.2⟩⟩).succ
  inj' := by
    intro y z h
    dsimp only at h
    by_cases hy : y.1 = x
    · by_cases hz : z.1 = x
      · exact Subtype.ext (hy.trans hz.symm)
      · rw [dif_pos hy, dif_neg hz] at h
        exact absurd h.symm (Fin.succ_ne_zero _)
    · by_cases hz : z.1 = x
      · rw [dif_neg hy, dif_pos hz] at h
        exact absurd h (Fin.succ_ne_zero _)
      · rw [dif_neg hy, dif_neg hz] at h
        have h2 := congrArg Subtype.val (r.injective (Fin.succ_inj.mp h))
        exact Subtype.ext h2

/-- `consOrdering r` ranks `x` first. -/
theorem consOrdering_self {S : Finset α} {x : α} {n : ℕ} (hx : x ∈ S)
    (r : {y // y ∈ S.erase x} ↪ Fin n) : consOrdering r ⟨x, hx⟩ = 0 :=
  dif_pos rfl

/-- Away from `x`, `consOrdering r` shifts every rank of `r` up by one. -/
theorem consOrdering_of_ne {S : Finset α} {x : α} {n : ℕ}
    (r : {y // y ∈ S.erase x} ↪ Fin n) (y : {y // y ∈ S}) (hy : y.1 ≠ x) :
    consOrdering r y = (r ⟨y.1, Finset.mem_erase.mpr ⟨hy, y.2⟩⟩).succ :=
  dif_neg hy

/-- `consOrdering` undoes `eraseOrdering`. -/
theorem consOrdering_eraseOrdering {S : Finset α} {x : α} {n : ℕ} (hx : x ∈ S)
    (r : {y // y ∈ S} ↪ Fin (n + 1)) (hr : r ⟨x, hx⟩ = 0) :
    consOrdering (eraseOrdering hx r hr) = r := by
  ext y
  by_cases hy : y.1 = x
  · rw [show y = (⟨x, hx⟩ : {y // y ∈ S}) from Subtype.ext hy, consOrdering_self hx, hr]
  · rw [consOrdering_of_ne _ y hy, succ_eraseOrdering]

/-- `eraseOrdering` undoes `consOrdering`. -/
theorem eraseOrdering_consOrdering {S : Finset α} {x : α} {n : ℕ} (hx : x ∈ S)
    (r : {y // y ∈ S.erase x} ↪ Fin n) (hr : consOrdering r ⟨x, hx⟩ = 0) :
    eraseOrdering hx (consOrdering r) hr = r := by
  ext y : 1
  rw [← Fin.succ_inj, succ_eraseOrdering,
    consOrdering_of_ne r ⟨y.1, Finset.mem_of_mem_erase y.2⟩ (Finset.ne_of_mem_erase y.2)]

/-- No ordering ranking an element of `B` first can place a nonempty `A` before `B`. -/
theorem filter_orderingsPrecede_eq_empty {S A B : Finset α} {n : ℕ} (y : {z // z ∈ S})
    (hyB : (y : α) ∈ B) (hA : A.Nonempty) (hAS : A ⊆ S) :
    ((orderingsPrecede S A B (n + 1)).filter fun r => r y = 0) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro r hr
  rw [Finset.mem_filter, mem_orderingsPrecede] at hr
  obtain ⟨a, ha⟩ := hA
  have hlt := hr.1 ⟨a, hAS ha⟩ y ha hyB
  rw [hr.2] at hlt
  exact absurd hlt (Fin.not_lt_zero _)

/-- Orderings of `S` ranking some `y ∉ B` first and placing `A` before `B` correspond to the
orderings of `S.erase y` placing `A.erase y` before `B`. -/
theorem card_filter_orderingsPrecede {S A B : Finset α} {n : ℕ} (y : {z // z ∈ S})
    (hyB : (y : α) ∉ B) :
    ((orderingsPrecede S A B (n + 1)).filter fun r => r y = 0).card
      = (orderingsPrecede (S.erase (y : α)) (A.erase (y : α)) B n).card := by
  refine Finset.card_bij' (fun r hr => eraseOrdering y.2 r (Finset.mem_filter.mp hr).2)
    (fun r _ => consOrdering r) ?_ ?_ ?_ ?_
  · intro r hr
    rw [Finset.mem_filter] at hr
    rw [mem_orderingsPrecede]
    intro a b ha hb
    rw [← Fin.succ_lt_succ_iff, succ_eraseOrdering, succ_eraseOrdering]
    exact mem_orderingsPrecede.mp hr.1 _ _ (Finset.mem_of_mem_erase ha) hb
  · intro r hr
    rw [Finset.mem_filter]
    refine ⟨mem_orderingsPrecede.mpr ?_, consOrdering_self y.2 r⟩
    intro a b ha hb
    have hbx : (b : α) ≠ (y : α) := fun h => hyB (h ▸ hb)
    rw [consOrdering_of_ne _ b hbx]
    by_cases hax : (a : α) = (y : α)
    · rw [show a = (⟨(y : α), y.2⟩ : {z // z ∈ S}) from Subtype.ext hax, consOrdering_self y.2]
      exact Fin.succ_pos _
    · rw [consOrdering_of_ne _ a hax, Fin.succ_lt_succ_iff]
      exact mem_orderingsPrecede.mp hr _ _ (Finset.mem_erase.mpr ⟨hax, ha⟩) hb
  · intro r hr
    exact consOrdering_eraseOrdering y.2 r (Finset.mem_filter.mp hr).2
  · intro r hr
    exact eraseOrdering_consOrdering y.2 r _

/-- The condition defining `orderingsPrecede` is vacuous for an empty `A`, so all `n !` orderings
of an `n`-element ground set are counted. -/
theorem card_orderingsPrecede_empty (S B : Finset α) {n : ℕ} (hS : S.card = n) :
    (orderingsPrecede S ∅ B n).card = Nat.factorial n := by
  have h : orderingsPrecede S ∅ B n = Finset.univ := by
    ext r
    simp [orderingsPrecede]
  rw [h, Finset.card_univ, Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe, hS,
    Nat.descFactorial_self]

/-- Of the `n !` orderings of an `n`-element ground set `S`, exactly a
`(A.card + B.card).choose A.card`-th place all of `A` before all of `B`, for disjoint `A B ⊆ S`. -/
theorem card_orderingsPrecede_mul_choose (n : ℕ) (S A B : Finset α) (hS : S.card = n)
    (hA : A ⊆ S) (hB : B ⊆ S) (hAB : A ∩ B = ∅) :
    (orderingsPrecede S A B n).card * (A.card + B.card).choose A.card = Nat.factorial n := by
  induction n generalizing S A B with
  | zero =>
    have hAe : A = ∅ := Finset.subset_empty.mp (Finset.card_eq_zero.mp hS ▸ hA)
    subst hAe
    rw [card_orderingsPrecede_empty S B hS]
    simp
  | succ n ih =>
    rcases A.eq_empty_or_nonempty with rfl | hAne
    · rw [card_orderingsPrecede_empty S B hS]
      simp
    obtain ⟨a', ha'⟩ : ∃ a', A.card = a' + 1 :=
      ⟨A.card - 1, (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr hAne)).symm⟩
    have hnotboth : ∀ z : α, z ∈ A → z ∈ B → False := by
      intro z hz₁ hz₂
      have hz : z ∈ A ∩ B := Finset.mem_inter.mpr ⟨hz₁, hz₂⟩
      rw [hAB] at hz
      exact absurd hz (Finset.notMem_empty z)
    have hsurj : ∀ r : {y // y ∈ S} ↪ Fin (n + 1), ∃ y, r y = 0 := by
      intro r
      have hbij : Function.Bijective r :=
        (Fintype.bijective_iff_injective_and_card r).mpr
          ⟨r.injective, by rw [Fintype.card_coe, hS, Fintype.card_fin]⟩
      exact hbij.2 0
    have hdisjf : ∀ y ∈ S.attach, ∀ z ∈ S.attach, y ≠ z →
        Disjoint ((orderingsPrecede S A B (n + 1)).filter fun r => r y = 0)
          ((orderingsPrecede S A B (n + 1)).filter fun r => r z = 0) := by
      intro y _ z _ hyz
      rw [Finset.disjoint_left]
      intro r hr₁ hr₂
      exact hyz (r.injective (((Finset.mem_filter.mp hr₁).2).trans
        ((Finset.mem_filter.mp hr₂).2).symm))
    have hunion : orderingsPrecede S A B (n + 1)
        = S.attach.biUnion fun y => (orderingsPrecede S A B (n + 1)).filter fun r => r y = 0 := by
      ext r
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_attach, true_and]
      constructor
      · intro hr
        obtain ⟨y, hy⟩ := hsurj r
        exact ⟨y, hr, hy⟩
      · rintro ⟨y, hr, -⟩
        exact hr
    have hcard : (orderingsPrecede S A B (n + 1)).card
        = ∑ y ∈ S.attach, ((orderingsPrecede S A B (n + 1)).filter fun r => r y = 0).card := by
      rw [← Finset.card_biUnion hdisjf]
      exact congrArg Finset.card hunion
    have hterm : ∀ y ∈ S.attach,
        A.card * (((orderingsPrecede S A B (n + 1)).filter fun r => r y = 0).card
          * (A.card + B.card).choose A.card)
        = if (y : α) ∈ A then (A.card + B.card) * Nat.factorial n
          else if (y : α) ∈ B then 0 else A.card * Nat.factorial n := by
      intro y _
      by_cases hyB : (y : α) ∈ B
      · rw [filter_orderingsPrecede_eq_empty y hyB hAne hA, Finset.card_empty,
          if_neg (fun h => hnotboth _ h hyB), if_pos hyB, Nat.zero_mul, Nat.mul_zero]
      · rw [card_filter_orderingsPrecede y hyB]
        have hcard' : (S.erase (y : α)).card = n := by
          rw [Finset.card_erase_of_mem y.2, hS]
          omega
        have IHy := ih (S.erase (y : α)) (A.erase (y : α)) B hcard'
          (Finset.erase_subset_erase _ hA) (Finset.subset_erase.mpr ⟨hB, hyB⟩)
          (by
            rw [← Finset.subset_empty, ← hAB]
            exact Finset.inter_subset_inter (Finset.erase_subset _ _) (Finset.Subset.refl _))
        by_cases hyA : (y : α) ∈ A
        · rw [Finset.card_erase_of_mem hyA, ha', Nat.add_sub_cancel] at IHy
          rw [if_pos hyA, ha',
            show a' + 1 + B.card = a' + B.card + 1 from by omega]
          calc (a' + 1) * ((orderingsPrecede (S.erase (y : α)) (A.erase (y : α)) B n).card
                * (a' + B.card + 1).choose (a' + 1))
              = (orderingsPrecede (S.erase (y : α)) (A.erase (y : α)) B n).card
                * ((a' + B.card + 1).choose (a' + 1) * (a' + 1)) := by ring
            _ = (orderingsPrecede (S.erase (y : α)) (A.erase (y : α)) B n).card
                * ((a' + B.card + 1) * (a' + B.card).choose a') := by
                  rw [Nat.add_one_mul_choose_eq]
            _ = (a' + B.card + 1) * ((orderingsPrecede (S.erase (y : α)) (A.erase (y : α)) B n).card
                * (a' + B.card).choose a') := by ring
            _ = (a' + B.card + 1) * Nat.factorial n := by rw [IHy]
        · rw [Finset.erase_eq_of_notMem hyA] at IHy ⊢
          rw [if_neg hyA, if_neg hyB, IHy]
    have hABS : A ∪ B ⊆ S := Finset.union_subset hA hB
    have hABcard : (A ∪ B).card = A.card + B.card :=
      Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.mpr hAB)
    obtain ⟨k, hk⟩ : ∃ k, n + 1 = A.card + B.card + k :=
      ⟨n + 1 - (A.card + B.card), by
        have hle := Finset.card_le_card hABS
        rw [hABcard, hS] at hle
        omega⟩
    have hkcard : (S \ (A ∪ B)).card = k := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hABS, hABcard, hS]
      omega
    have hsplit : ∑ x ∈ S, (if x ∈ A then (A.card + B.card) * Nat.factorial n
        else if x ∈ B then 0 else A.card * Nat.factorial n)
        = A.card * ((A.card + B.card) * Nat.factorial n) + 0
          + k * (A.card * Nat.factorial n) := by
      rw [← Finset.union_sdiff_of_subset hABS, Finset.sum_union Finset.disjoint_sdiff,
        Finset.sum_union (Finset.disjoint_iff_inter_eq_empty.mpr hAB)]
      have e₁ : ∀ x ∈ A, (if x ∈ A then (A.card + B.card) * Nat.factorial n
          else if x ∈ B then 0 else A.card * Nat.factorial n)
          = (A.card + B.card) * Nat.factorial n := fun x hx => if_pos hx
      have e₂ : ∀ x ∈ B, (if x ∈ A then (A.card + B.card) * Nat.factorial n
          else if x ∈ B then 0 else A.card * Nat.factorial n) = 0 := fun x hx => by
        rw [if_neg (fun h => hnotboth x h hx), if_pos hx]
      have e₃ : ∀ x ∈ S \ (A ∪ B), (if x ∈ A then (A.card + B.card) * Nat.factorial n
          else if x ∈ B then 0 else A.card * Nat.factorial n)
          = A.card * Nat.factorial n := fun x hx => by
        have hx' := Finset.mem_sdiff.mp hx
        rw [if_neg fun h => hx'.2 (Finset.mem_union_left _ h),
          if_neg fun h => hx'.2 (Finset.mem_union_right _ h)]
      rw [Finset.sum_congr rfl e₁, Finset.sum_congr rfl e₂, Finset.sum_congr rfl e₃,
        Finset.sum_const, Finset.sum_const, Finset.sum_const, hkcard, smul_eq_mul, smul_eq_mul,
        smul_eq_mul, Nat.mul_zero]
    refine Nat.eq_of_mul_eq_mul_left (Finset.card_pos.mpr hAne) ?_
    rw [hcard, Finset.sum_mul, Finset.mul_sum, Finset.sum_congr rfl hterm,
      Finset.sum_attach S fun x => if x ∈ A then (A.card + B.card) * Nat.factorial n
        else if x ∈ B then 0 else A.card * Nat.factorial n,
      hsplit, Nat.factorial_succ, hk]
    ring

/-- If `A₁` meets `B₂` and `A₂` meets `B₁`, no single ordering can place `A₁` before `B₁` and
`A₂` before `B₂` at the same time. -/
theorem disjoint_orderingsPrecede (S A₁ B₁ A₂ B₂ : Finset α) (n : ℕ) (h₁ : A₁ ⊆ S) (h₂ : A₂ ⊆ S)
    (hm₁ : (A₁ ∩ B₂).Nonempty) (hm₂ : (A₂ ∩ B₁).Nonempty) :
    Disjoint (orderingsPrecede S A₁ B₁ n) (orderingsPrecede S A₂ B₂ n) := by
  rw [Finset.disjoint_left]
  intro r hr₁ hr₂
  obtain ⟨x, hx⟩ := hm₁
  obtain ⟨y, hy⟩ := hm₂
  rw [Finset.mem_inter] at hx hy
  rw [mem_orderingsPrecede] at hr₁ hr₂
  exact lt_asymm (hr₁ ⟨x, h₁ hx.1⟩ ⟨y, h₂ hy.1⟩ hx.1 hy.2)
    (hr₂ ⟨y, h₂ hy.1⟩ ⟨x, h₁ hx.1⟩ hy.1 hx.2)

/-- **Bollobás' two families theorem** (Zhao, Theorem 1.2.6): if `A i ∩ B i = ∅` for every `i` and
`A i ∩ B j ≠ ∅` whenever `i ≠ j`, then `∑ i, (|A i| + |B i|).choose |A i| ⁻¹ ≤ 1`. -/
theorem bollobas_two_families {α : Type*} [DecidableEq α] {m : ℕ}
    (A B : Fin m → Finset α)
    (hdisj : ∀ i, A i ∩ B i = ∅)
    (hmeet : ∀ i j, i ≠ j → (A i ∩ B j).Nonempty) :
    ∑ i : Fin m, (((A i).card + (B i).card).choose (A i).card : ℝ)⁻¹ ≤ 1 := by
  set S : Finset α := Finset.univ.biUnion fun i => A i ∪ B i
  have hAS : ∀ i, A i ⊆ S := fun i x hx =>
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_union_left _ hx⟩
  have hBS : ∀ i, B i ⊆ S := fun i x hx =>
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_union_right _ hx⟩
  have hcount : ∀ i, (orderingsPrecede S (A i) (B i) S.card).card *
      ((A i).card + (B i).card).choose (A i).card = Nat.factorial S.card := fun i =>
    card_orderingsPrecede_mul_choose S.card S (A i) (B i) rfl (hAS i) (hBS i) (hdisj i)
  have hpair : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j → Disjoint (orderingsPrecede S (A i) (B i) S.card)
        (orderingsPrecede S (A j) (B j) S.card) :=
    fun i _ j _ hij => disjoint_orderingsPrecede S (A i) (B i) (A j) (B j) S.card (hAS i) (hAS j)
      (hmeet i j hij) (hmeet j i hij.symm)
  have hsum : ∑ i : Fin m, (orderingsPrecede S (A i) (B i) S.card).card
      ≤ Nat.factorial S.card := by
    rw [← Finset.card_biUnion hpair]
    refine le_trans (Finset.card_le_univ _) ?_
    rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe, Nat.descFactorial_self]
  have hfac : (0 : ℝ) < (Nat.factorial S.card : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have key : ∀ i : Fin m, ((((A i).card + (B i).card).choose (A i).card : ℝ))⁻¹
      = ((orderingsPrecede S (A i) (B i) S.card).card : ℝ) / (Nat.factorial S.card : ℝ) := by
    intro i
    have hc : ((((A i).card + (B i).card).choose (A i).card : ℝ)) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (Nat.le_add_right _ _)).ne'
    have h : ((orderingsPrecede S (A i) (B i) S.card).card : ℝ) *
        ((((A i).card + (B i).card).choose (A i).card : ℝ)) = (Nat.factorial S.card : ℝ) := by
      exact_mod_cast hcount i
    field_simp
    linarith [h]
  calc ∑ i : Fin m, (((A i).card + (B i).card).choose (A i).card : ℝ)⁻¹
      = ∑ i : Fin m, ((orderingsPrecede S (A i) (B i) S.card).card : ℝ)
          / (Nat.factorial S.card : ℝ) :=
        Finset.sum_congr rfl fun i _ => key i
    _ = (∑ i : Fin m, ((orderingsPrecede S (A i) (B i) S.card).card : ℝ))
        / (Nat.factorial S.card : ℝ) := by rw [Finset.sum_div]
    _ ≤ 1 := by
        rw [div_le_one hfac]
        exact_mod_cast hsum

end ProbMethodCombinatorics
