import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Chapter 1.2: Set systems — Bollobás' two families theorem

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Theorem 1.2.6.

Sperner's theorem, the LYM inequality and Erdős–Ko–Rado, the other results of Section 1.2, are
already in Mathlib (`IsAntichain.sperner`, `Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose`,
`Finset.erdos_ko_rado`), so only Bollobás' theorem is formalized here.
-/

namespace ProbMethodCombinatorics

open Finset

/-- **Bollobás' two families theorem** (Zhao, Theorem 1.2.6): if `A i ∩ B i = ∅` for every `i` and
`A i ∩ B j ≠ ∅` whenever `i ≠ j`, then `∑ i, (|A i| + |B i|).choose |A i| ⁻¹ ≤ 1`. -/
theorem bollobas_two_families {α : Type*} [DecidableEq α] {m : ℕ}
    (A B : Fin m → Finset α)
    (hdisj : ∀ i, A i ∩ B i = ∅)
    (hmeet : ∀ i j, i ≠ j → (A i ∩ B j).Nonempty) :
    ∑ i : Fin m, (((A i).card + (B i).card).choose (A i).card : ℝ)⁻¹ ≤ 1 := by
  sorry

end ProbMethodCombinatorics
