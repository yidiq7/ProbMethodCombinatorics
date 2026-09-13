import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Chapter 1.3: 2-colourable hypergraphs

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Theorem 1.3.1.

A hypergraph is a finite family of edges, each a `Finset` of vertices; it is `k`-uniform when every
edge has exactly `k` vertices.
-/

namespace ProbMethodCombinatorics

open Finset

/-- A hypergraph is *2-colourable* (has *property B*) if its vertices can be two-coloured with no
edge monochromatic. -/
def TwoColorable {α : Type*} (H : Finset (Finset α)) : Prop :=
  ∃ f : α → Bool, ∀ e ∈ H, ∃ u ∈ e, ∃ v ∈ e, f u ≠ f v

/-- **Erdős 1964** (Zhao, Theorem 1.3.1): every `k`-uniform hypergraph with fewer than `2 ^ (k - 1)`
edges is 2-colourable.  Equivalently `m k ≥ 2 ^ (k - 1)`, where `m k` is the least number of edges
in a non-2-colourable `k`-uniform hypergraph. -/
theorem twoColorable_of_card_lt {α : Type*} [Fintype α] [DecidableEq α]
    {k : ℕ} (hk : 2 ≤ k) {H : Finset (Finset α)}
    (huniform : ∀ e ∈ H, e.card = k) (hcard : H.card < 2 ^ (k - 1)) :
    TwoColorable H := by
  rcases H.eq_empty_or_nonempty with rfl | ⟨e₀, he₀⟩
  · exact ⟨fun _ => true, by simp⟩
  have hkn : k ≤ Fintype.card α := by
    rw [← huniform e₀ he₀, ← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ e₀)
  -- `mono e` collects the colourings that are constant on the edge `e`.
  obtain ⟨mono, hmono⟩ : ∃ m : Finset α → Finset (α → Bool),
      ∀ e f, f ∈ m e ↔ ∀ u ∈ e, ∀ v ∈ e, f u = f v :=
    ⟨fun e => Finset.univ.filter fun f => ∀ u ∈ e, ∀ v ∈ e, f u = f v, by simp⟩
  -- A colouring constant on `e` is determined by its values off `e` together with its value on `e`.
  have hmono_card : ∀ e ∈ H, (mono e).card ≤ 2 ^ (Fintype.card α - k) * 2 := by
    intro e he
    have hne : e.Nonempty := by
      rw [← Finset.card_pos, huniform e he]; omega
    obtain ⟨a, ha⟩ := hne
    have hle : (mono e).card ≤ Fintype.card ((↥(eᶜ : Finset α) → Bool) × Bool) := by
      rw [← Finset.card_univ]
      refine Finset.card_le_card_of_injOn (fun f => (fun x => f x.1, f a))
        (fun _ _ => Finset.mem_univ _) ?_
      intro f hf g hg hfg
      rw [Finset.mem_coe, hmono] at hf hg
      have h1 := congrFun (congrArg Prod.fst hfg)
      have h2 := congrArg Prod.snd hfg
      simp only at h1 h2
      funext x
      by_cases hx : x ∈ e
      · rw [hf x hx a ha, hg x hx a ha, h2]
      · exact h1 ⟨x, Finset.mem_compl.2 hx⟩
    refine hle.trans_eq ?_
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
      Finset.card_compl, huniform e he]
  -- Fewer than `2 ^ (k - 1)` edges cannot spoil all `2 ^ |α|` colourings.
  have hsum : ∑ e ∈ H, (mono e).card ≤ H.card * (2 ^ (Fintype.card α - k) * 2) := by
    have hle := Finset.sum_le_sum hmono_card
    rwa [Finset.sum_const_nat (m := 2 ^ (Fintype.card α - k) * 2) fun _ _ => rfl] at hle
  have hpos : 0 < 2 ^ (Fintype.card α - k) * 2 :=
    Nat.mul_pos (Nat.two_pow_pos _) (by omega)
  have hlt : H.card * (2 ^ (Fintype.card α - k) * 2)
      < 2 ^ (k - 1) * (2 ^ (Fintype.card α - k) * 2) :=
    Nat.mul_lt_mul_of_lt_of_le hcard le_rfl hpos
  have heq : 2 ^ (k - 1) * (2 ^ (Fintype.card α - k) * 2)
      = (Finset.univ : Finset (α → Bool)).card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, ← pow_succ, ← pow_add]
    congr 1
    omega
  have hbig : (H.biUnion mono).card < (Finset.univ : Finset (α → Bool)).card :=
    lt_of_lt_of_eq (lt_of_le_of_lt (Finset.card_biUnion_le.trans hsum) hlt) heq
  obtain ⟨f, -, hf⟩ := Finset.exists_mem_notMem_of_card_lt_card hbig
  refine ⟨f, fun e he => ?_⟩
  by_contra hcontra
  exact hf (Finset.mem_biUnion.2 ⟨e, he, (hmono e f).2 (by simpa using hcontra)⟩)

end ProbMethodCombinatorics
