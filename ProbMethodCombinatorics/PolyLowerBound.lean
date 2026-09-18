import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Topology.Algebra.Polynomial
import ProbMethodCombinatorics.Expectation

/-!
# Lemma 2.5.3: a uniform lower bound on normalised polynomials

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Lemma 2.5.3.

Let `P k` be the polynomials in `k` variables of total degree at most `k` whose coefficients
all have absolute value at most `1` and whose `p₁p₂⋯p_k` coefficient is exactly `1`.  Then some
`c k > 0` bounds `max_{[0,1]^k} |g|` from below, *uniformly over `g ∈ P k`*.

The uniformity is the whole point, and it is what makes the constant in Theorem 2.5.2
independent of the colouring.  The source's proof is a compactness argument: `P k` is a closed
bounded subset of the finite-dimensional space of coefficient vectors, `g ↦ max_{[0,1]^k} |g|`
is continuous and strictly positive on it (a polynomial with a nonzero coefficient cannot
vanish identically on `[0,1]^k`), so it attains a positive minimum.

This is the missing input to **Theorem 2.5.2**, whose own statement needs `k`-partite
`k`-uniform hypergraph vocabulary and is not attempted here.
-/

namespace ProbMethodCombinatorics

open MvPolynomial

/-- The all-ones exponent vector, whose coefficient in `g` is the `p₁p₂⋯p_k` coefficient. -/
noncomputable def allOnes (k : ℕ) : Fin k →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => 1

section FiniteDifference

variable {k : ℕ}

private lemma allOnes_apply (k : ℕ) (i : Fin k) : allOnes k i = 1 := rfl

/-- On a `0/1` point of the cube the monomial `∏ i, xᵢ ^ dᵢ` collapses to a product over the
complement of the support of the point. -/
private lemma prod_cubePoint_pow (S : Finset (Fin k)) (d : Fin k →₀ ℕ) :
    ∏ i : Fin k, (if i ∈ S then (1 : ℝ) else 0) ^ d i
      = ∏ i ∈ Finset.univ \ S, (0 : ℝ) ^ d i := by
  have h1 : ∀ i ∈ S, (if i ∈ S then (1 : ℝ) else 0) ^ d i = 1 := by
    intro i hi
    rw [if_pos hi, one_pow]
  have h2 : ∀ i ∈ Finset.univ \ S, (if i ∈ S then (1 : ℝ) else 0) ^ d i = (0 : ℝ) ^ d i := by
    intro i hi
    rw [if_neg (Finset.mem_sdiff.mp hi).2]
  rw [← Finset.prod_sdiff (Finset.subset_univ S), Finset.prod_congr rfl h1,
    Finset.prod_congr rfl h2, Finset.prod_const_one, mul_one]

/-- The signed sum of a monomial over all `0/1` points of the cube factors as a product. -/
private lemma sum_signed_prod_cubePoint (d : Fin k →₀ ℕ) :
    ∑ S : Finset (Fin k), (-1 : ℝ) ^ S.card *
        ∏ i : Fin k, (if i ∈ S then (1 : ℝ) else 0) ^ d i
      = ∏ i : Fin k, ((-1 : ℝ) + (0 : ℝ) ^ d i) := by
  rw [Finset.prod_add (fun _ : Fin k => (-1 : ℝ)) (fun i : Fin k => (0 : ℝ) ^ d i) Finset.univ,
    Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [prod_cubePoint_pow, Finset.prod_const]

private lemma prod_neg_one_add_zero_pow_of_forall (d : Fin k →₀ ℕ) (h : ∀ i, d i ≠ 0) :
    ∏ i : Fin k, ((-1 : ℝ) + (0 : ℝ) ^ d i) = (-1 : ℝ) ^ k := by
  rw [Finset.prod_congr rfl (fun i _ => by rw [zero_pow (h i), add_zero]), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

private lemma prod_neg_one_add_zero_pow_of_eq_zero (d : Fin k →₀ ℕ) (i : Fin k) (h : d i = 0) :
    ∏ i : Fin k, ((-1 : ℝ) + (0 : ℝ) ^ d i) = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [h, pow_zero, neg_add_cancel]

/-- An exponent vector of a polynomial of total degree at most `k` in `k` variables all of whose
entries are nonzero is the all-ones vector. -/
private lemma eq_allOnes_of_forall_ne_zero {g : MvPolynomial (Fin k) ℝ}
    (hdeg : g.totalDegree ≤ k) {d : Fin k →₀ ℕ} (hd : d ∈ g.support) (h : ∀ i, d i ≠ 0) :
    d = allOnes k := by
  have hsupp : d.support = Finset.univ := by
    ext i
    simp [Finsupp.mem_support_iff, h i]
  have hbig : ∑ i : Fin k, d i ≤ k := by
    have hle := MvPolynomial.le_totalDegree hd
    rw [Finsupp.sum, hsupp] at hle
    exact hle.trans hdeg
  have hone : ∀ i ∈ (Finset.univ : Finset (Fin k)), 1 ≤ d i := fun i _ =>
    Nat.one_le_iff_ne_zero.mpr (h i)
  have hconst : ∑ _i : Fin k, (1 : ℕ) = k := by simp
  have heq : ∑ _i : Fin k, (1 : ℕ) = ∑ i : Fin k, d i := by
    refine le_antisymm (Finset.sum_le_sum hone) ?_
    rw [hconst]
    exact hbig
  ext i
  exact ((Finset.sum_eq_sum_iff_of_le hone).mp heq i (Finset.mem_univ i)).symm.trans
    (allOnes_apply k i).symm

/-- **Finite differences.**  The signed sum of `g` over the `2 ^ k` vertices of the cube picks out
exactly the `p₁p₂⋯p_k` coefficient, when `g` has total degree at most `k`. -/
private lemma sum_signed_eval_eq_coeff (g : MvPolynomial (Fin k) ℝ) (hdeg : g.totalDegree ≤ k) :
    ∑ S : Finset (Fin k), (-1 : ℝ) ^ S.card *
        MvPolynomial.eval (fun i => if i ∈ S then (1 : ℝ) else 0) g
      = (-1 : ℝ) ^ k * MvPolynomial.coeff (allOnes k) g := by
  have step : ∀ S : Finset (Fin k),
      (-1 : ℝ) ^ S.card * MvPolynomial.eval (fun i => if i ∈ S then (1 : ℝ) else 0) g
        = ∑ d ∈ g.support, MvPolynomial.coeff d g *
            ((-1 : ℝ) ^ S.card * ∏ i : Fin k, (if i ∈ S then (1 : ℝ) else 0) ^ d i) := by
    intro S
    rw [MvPolynomial.eval_eq', Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  have step2 : ∀ d ∈ g.support,
      (∑ S : Finset (Fin k), MvPolynomial.coeff d g *
          ((-1 : ℝ) ^ S.card * ∏ i : Fin k, (if i ∈ S then (1 : ℝ) else 0) ^ d i))
        = MvPolynomial.coeff d g * ∏ i : Fin k, ((-1 : ℝ) + (0 : ℝ) ^ d i) := by
    intro d _
    rw [← Finset.mul_sum, sum_signed_prod_cubePoint]
  rw [Finset.sum_congr rfl fun S _ => step S, Finset.sum_comm, Finset.sum_congr rfl step2,
    Finset.sum_eq_single (allOnes k)]
  · rw [prod_neg_one_add_zero_pow_of_forall _ (fun i => by rw [allOnes_apply]; exact one_ne_zero),
      mul_comm]
  · intro d hd hne
    rcases not_forall.mp (fun hz => hne (eq_allOnes_of_forall_ne_zero hdeg hd hz)) with ⟨i, hi⟩
    rw [prod_neg_one_add_zero_pow_of_eq_zero d i (not_not.mp hi), mul_zero]
  · intro hns
    rw [MvPolynomial.notMem_support_iff.mp hns, zero_mul]

end FiniteDifference

/-- **Lemma 2.5.3.**  A constant `c > 0` that no normalised polynomial can beat downwards on
the unit cube.

`0 < k` is needed: at `k = 0` the only exponent vector is empty, `allOnes 0` is `0`, and the
hypotheses force the constant polynomial `1`, for which the statement is true but degenerate —
the bound is kept nontrivial by excluding it. -/
theorem exists_pos_forall_exists_abs_eval_ge (k : ℕ) (hk : 0 < k) :
    ∃ c : ℝ, 0 < c ∧ ∀ g : MvPolynomial (Fin k) ℝ,
      g.totalDegree ≤ k →
      (∀ m : Fin k →₀ ℕ, |MvPolynomial.coeff m g| ≤ 1) →
      MvPolynomial.coeff (allOnes k) g = 1 →
      ∃ p : Fin k → ℝ, (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) ∧
        c ≤ |MvPolynomial.eval p g| := by
  -- `0 < k` is not needed: the identity below holds for every `k`.
  have _hk : 0 < k := hk
  refine ⟨((2 : ℝ) ^ k)⁻¹, by positivity, ?_⟩
  intro g hdeg _ hone
  have key := sum_signed_eval_eq_coeff g hdeg
  rw [hone, mul_one] at key
  have habs : (1 : ℝ) ≤ ∑ S : Finset (Fin k),
      |MvPolynomial.eval (fun i => if i ∈ S then (1 : ℝ) else 0) g| := by
    calc (1 : ℝ) = |(-1 : ℝ) ^ k| := by rw [abs_pow, abs_neg, abs_one, one_pow]
      _ = |∑ S : Finset (Fin k), (-1 : ℝ) ^ S.card *
            MvPolynomial.eval (fun i => if i ∈ S then (1 : ℝ) else 0) g| := by rw [key]
      _ ≤ ∑ S : Finset (Fin k), |(-1 : ℝ) ^ S.card *
            MvPolynomial.eval (fun i => if i ∈ S then (1 : ℝ) else 0) g| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ S : Finset (Fin k),
            |MvPolynomial.eval (fun i => if i ∈ S then (1 : ℝ) else 0) g| := by
          simp [abs_mul, abs_pow]
  have hsum : ∑ _S : Finset (Fin k), ((2 : ℝ) ^ k)⁻¹ ≤ ∑ S : Finset (Fin k),
      |MvPolynomial.eval (fun i => if i ∈ S then (1 : ℝ) else 0) g| := by
    refine le_trans (le_of_eq ?_) habs
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    exact mul_inv_cancel₀ (by positivity)
  obtain ⟨S, -, hS⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  refine ⟨fun i => if i ∈ S then (1 : ℝ) else 0, fun i => ?_, hS⟩
  by_cases hi : i ∈ S
  · simp [hi]
  · simp [hi]

end ProbMethodCombinatorics
