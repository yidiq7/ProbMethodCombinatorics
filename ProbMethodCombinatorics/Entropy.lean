import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Chapter 10: Entropy

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Chapter 10.

Mathlib has `Real.negMulLog` and `Real.binEntropy`, but no Shannon entropy of a discrete
random variable, and none of this chapter's results (Brégman–Minc, Sidorenko, Shearer,
Loomis–Whitney).  So the chapter opens with a small **shared layer**, proved here, that every
task in the chapter is expected to use:

* `probOf p X s` — the probability that `X` takes the value `s` under the mass function `p`;
* `entropy p X` — Shannon entropy in bits, `∑ s, -p_s * log₂ p_s` (Definition 10.1.1);
* `condEntropy p X Y` — conditional entropy `H(X ∣ Y)` (Definition 10.1.6), spelled out as
  `∑_y P(Y = y) ∑_x -P(X = x ∣ Y = y) log₂ P(X = x ∣ Y = y)` rather than defined as a
  difference, so that the chain rule stays a theorem;
* `uniformPMF A` — the uniform mass function on a finite set, the distribution used by almost
  every application in the chapter.

Joint entropy needs no separate definition: `H(X, Y)` is `entropy p fun ω => (X ω, Y ω)`, and
`H(X₁, …, Xₙ)` is `entropy p fun ω i => X i ω`.

Throughout, the convention "if `pₛ = 0` then the summand is zero" is automatic, because
`Real.logb 2 0 = 0`.

Everything is finite and counting-flavoured, so this chapter follows the `Finset`/`Fintype`
convention of Chapters 1–3 and 5, not the measure-theoretic convention of Chapters 4 and 6–9.
-/

namespace ProbMethodCombinatorics

open Finset

variable {Ω S T : Type*}

section Defs

variable [Fintype Ω] [Fintype S] [DecidableEq S]

/-- `probOf p X s` is the probability that the random variable `X : Ω → S` takes the value
`s`, where `p` is a probability mass function on the finite sample space `Ω`. -/
noncomputable def probOf (p : Ω → ℝ) (X : Ω → S) (s : S) : ℝ :=
  ∑ ω ∈ univ.filter fun ω => X ω = s, p ω

/-- The Shannon entropy, in bits, of a random variable `X : Ω → S` on the finite probability
space `(Ω, p)`.  This is Definition 10.1.1; the convention that a zero probability contributes
nothing holds because `Real.logb 2 0 = 0`. -/
noncomputable def entropy (p : Ω → ℝ) (X : Ω → S) : ℝ :=
  ∑ s : S, -probOf p X s * Real.logb 2 (probOf p X s)

/-- The conditional entropy `H(X ∣ Y)` of Definition 10.1.6, written out as
`∑_y P(Y = y) ∑_x -P(X = x ∣ Y = y) log₂ P(X = x ∣ Y = y)`.  The factor `P(Y = y)` has been
absorbed into the joint probability, so that the `y` with `P(Y = y) = 0` contribute nothing. -/
noncomputable def condEntropy [Fintype T] [DecidableEq T] (p : Ω → ℝ) (X : Ω → S) (Y : Ω → T) :
    ℝ :=
  ∑ t : T, ∑ s : S, -probOf p (fun ω => (X ω, Y ω)) (s, t) *
    Real.logb 2 (probOf p (fun ω => (X ω, Y ω)) (s, t) / probOf p Y t)

/-- The uniform probability mass function on a finite set `A`. -/
noncomputable def uniformPMF [DecidableEq Ω] (A : Finset Ω) : Ω → ℝ :=
  fun ω => if ω ∈ A then ((A.card : ℝ))⁻¹ else 0

end Defs

section Basic

variable [Fintype Ω] [Fintype S] [DecidableEq S] {p : Ω → ℝ} {X : Ω → S}

omit [Fintype S] in
theorem probOf_nonneg (hp : ∀ ω, 0 ≤ p ω) (X : Ω → S) (s : S) : 0 ≤ probOf p X s :=
  Finset.sum_nonneg fun ω _ => hp ω

/-- The fibres of `X` partition `Ω`, so the probabilities of its values sum to the total mass. -/
theorem sum_probOf (p : Ω → ℝ) (X : Ω → S) : ∑ s : S, probOf p X s = ∑ ω, p ω :=
  Finset.sum_fiberwise_eq_sum_filter univ univ X p ▸ by simp

theorem probOf_le_one (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (X : Ω → S) (s : S) :
    probOf p X s ≤ 1 := by
  rw [← hp1, ← sum_probOf p X]
  exact Finset.single_le_sum (fun t _ => probOf_nonneg hp X t) (Finset.mem_univ s)

variable [DecidableEq Ω]

omit [Fintype Ω] in
theorem uniformPMF_nonneg (A : Finset Ω) (ω : Ω) : 0 ≤ uniformPMF A ω := by
  unfold uniformPMF
  split <;> positivity

theorem sum_uniformPMF {A : Finset Ω} (hA : A.Nonempty) : ∑ ω, uniformPMF A ω = 1 := by
  have hcard : (A.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hA.card_ne_zero
  simp [uniformPMF, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
    mul_inv_cancel₀ hcard]

end Basic

/-! ### 10.1 Basic properties -/

section BasicProperties

variable [Fintype Ω] [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
variable {p : Ω → ℝ}

/-- Entropy is nonnegative: each probability lies in `[0, 1]`, so `-pₛ log₂ pₛ ≥ 0`. -/
theorem entropy_nonneg (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (X : Ω → S) :
    0 ≤ entropy p X := by
  sorry

/-- **Uniform bound** (Lemma 10.1.4): `H(X) ≤ log₂ |support X|`.  The support is supplied as a
finset `A` containing it, which avoids needing decidable equality on `ℝ`; taking `A` to be the
support itself gives the statement in the book. -/
theorem entropy_le_logb_card (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (X : Ω → S)
    (A : Finset S) (hA : ∀ s ∉ A, probOf p X s = 0) :
    entropy p X ≤ Real.logb 2 (A.card : ℝ) := by
  sorry

/-- Conditional entropy is the difference of a joint and a marginal entropy; this is the
computation on p. 176 of the notes.  Together with symmetry of the joint entropy it gives the
**chain rule** `H(X, Y) = H(Y) + H(X ∣ Y)` (Lemma 10.1.7). -/
theorem condEntropy_eq_sub (hp : ∀ ω, 0 ≤ p ω) (X : Ω → S) (Y : Ω → T) :
    condEntropy p X Y = entropy p (fun ω => (X ω, Y ω)) - entropy p Y := by
  sorry

/-- **Subadditivity** for two variables (Lemma 10.1.8): `H(X, Y) ≤ H(X) + H(Y)`, equivalently
that the mutual information `I(X; Y)` is nonnegative.  The proof is Jensen's inequality applied
to the convex function `t ↦ log₂ (1 / t)`. -/
theorem entropy_pair_le_add (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (X : Ω → S) (Y : Ω → T) :
    entropy p (fun ω => (X ω, Y ω)) ≤ entropy p X + entropy p Y := by
  sorry

/-- **Dropping conditioning** (Lemma 10.1.10): `H(X ∣ Y) ≤ H(X)`.  This is immediate from
`condEntropy_eq_sub` and `entropy_pair_le_add`. -/
theorem condEntropy_le_entropy (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (X : Ω → S)
    (Y : Ω → T) :
    condEntropy p X Y ≤ entropy p X := by
  sorry

end BasicProperties

section Subadditivity

variable [Fintype Ω] {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
variable [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]

/-- **Subadditivity** in general (Lemma 10.1.8): `H(X₁, …, Xₙ) ≤ H(X₁) + ⋯ + H(Xₙ)`, obtained
by iterating `entropy_pair_le_add`. -/
theorem entropy_pi_le_sum (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (X : ∀ i, Ω → α i) :
    entropy p (fun ω i => X i ω) ≤ ∑ i, entropy p fun ω => X i ω := by
  sorry

/-- **Shearer's lemma** (Theorem 10.4.5).  If every index `i` lies in at least `k` of the sets
`A j`, then `k · H(X₁, …, Xₙ) ≤ ∑ⱼ H(X_{A j})`.  Use the chain rule together with
`condEntropy_le_entropy`; do not re-derive the basic properties. -/
theorem shearer {κ : Type*} [Fintype κ] [DecidableEq κ] (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (hp1 : ∑ ω, p ω = 1) (X : ∀ i, Ω → α i) (A : κ → Finset ι) (k : ℕ)
    (hk : ∀ i : ι, k ≤ (univ.filter fun j => i ∈ A j).card) :
    (k : ℝ) * entropy p (fun ω i => X i ω) ≤ ∑ j, entropy p fun ω (i : A j) => X i.1 ω := by
  sorry

end Subadditivity

section ShearerApplications

variable [Fintype Ω] [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

/-- **Shearer's lemma, special case** (Theorem 10.4.1): `2 H(X, Y, Z) ≤ H(X, Y) + H(X, Z) +
H(Y, Z)`.  A direct consequence of `shearer` with the three two-element subsets of `{1, 2, 3}`,
each index being covered twice. -/
theorem shearer_triple {U : Type*} [Fintype U] [DecidableEq U] (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (X : Ω → S) (Y : Ω → T) (Z : Ω → U) :
    2 * entropy p (fun ω => (X ω, Y ω, Z ω)) ≤
      entropy p (fun ω => (X ω, Y ω)) + entropy p (fun ω => (X ω, Z ω))
        + entropy p (fun ω => (Y ω, Z ω)) := by
  sorry

end ShearerApplications

/-- **Discrete Loomis–Whitney in three coordinates** (Theorem 10.4.3): a finite set of points in
a product of three types has `|A|² ≤ |π₁₂ A| · |π₁₃ A| · |π₂₃ A|`.  Apply `shearer_triple` to a
uniform random point of `A`, using `entropy_le_logb_card` on each projection. -/
theorem card_sq_le_prod_card_image {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] (A : Finset (α × β × γ)) :
    A.card ^ 2 ≤ (A.image fun x => (x.1, x.2.1)).card * (A.image fun x => (x.1, x.2.2)).card
      * (A.image fun x => x.2).card := by
  sorry

/-- The three edges of the triangle on the vertices `a`, `b`, `c`, as unordered pairs. -/
def triangleEdges {α : Type*} [DecidableEq α] (a b c : α) : Finset (Sym2 α) :=
  {s(a, b), s(a, c), s(b, c)}

/-- **Triangle-intersecting families** (Theorem 10.4.9, Chung–Graham–Frankl–Shearer 1986).  A
family of graphs on `n` labelled vertices, any two of whose members share a triangle, has fewer
than `2 ^ (binom n 2 - 2)` members — a factor `4` below the trivial bound.  Graphs are recorded
as their edge sets; the hypothesis `hdiag` says these really are edge sets of simple graphs. -/
theorem card_lt_of_triangleIntersecting {n : ℕ} (𝒢 : Finset (Finset (Sym2 (Fin n))))
    (hdiag : ∀ G ∈ 𝒢, ∀ e ∈ G, ¬ e.IsDiag)
    (hinter : ∀ G ∈ 𝒢, ∀ H ∈ 𝒢, ∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      triangleEdges a b c ⊆ G ∩ H) :
    𝒢.card < 2 ^ (n.choose 2 - 2) := by
  sorry

/-- **Brégman–Minc inequality** (Theorem 10.2.1, conjectured by Minc 1963, proved by Brégman
1973).  For a `0/1` matrix whose `i`-th row sums to `dᵢ`, the permanent — the number of perfect
matchings of the corresponding bipartite graph — is at most `∏ᵢ (dᵢ!) ^ (1 / dᵢ)`.  The proof is
Radhakrishnan's: reveal the entries of a uniform random permutation in a uniform random order. -/
theorem permanent_le_prod_factorial {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) (d : Fin n → ℕ) (hd : ∀ i, ∑ j, A i j = (d i : ℝ)) :
    A.permanent ≤ ∏ i, (Nat.factorial (d i) : ℝ) ^ ((d i : ℝ))⁻¹ := by
  sorry

/-- **Entropy bound on a binomial tail** (Theorem 10.1.12).  For `0 < k ≤ n / 2`,
`∑_{i ≤ k} binom n i ≤ 2 ^ (H(k/n) n)`, where `H` is the binary entropy function.  Mathlib's
`Real.binEntropy` uses the natural logarithm, so the bound is written with `Real.exp`. -/
theorem sum_choose_le_exp_binEntropy {n k : ℕ} (hk : 0 < k) (h2k : 2 * k ≤ n) :
    ((∑ i ∈ range (k + 1), n.choose i : ℕ) : ℝ)
      ≤ Real.exp (n * Real.binEntropy ((k : ℝ) / n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
  have hkm : k ≤ m := by omega
  have hm : 0 < m := lt_of_lt_of_le hk hkm
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hx0 : (0:ℝ) < (k:ℝ) / m := div_pos hkR hmR
  have hx1 : (k:ℝ) / m ≤ 1 := (div_le_one hmR).mpr (by exact_mod_cast hkm)
  -- the moment generating function inequality
  have hmgf : (∑ i ∈ range (k + 1), (((k + m).choose i : ℕ) : ℝ)) * ((k:ℝ)/m) ^ k
      ≤ (1 + (k:ℝ)/m) ^ (k + m) := by
    rw [Finset.sum_mul]
    calc ∑ i ∈ range (k + 1), (((k + m).choose i : ℕ) : ℝ) * ((k:ℝ)/m) ^ k
        ≤ ∑ i ∈ range (k + 1), (((k + m).choose i : ℕ) : ℝ) * ((k:ℝ)/m) ^ i := by
          refine Finset.sum_le_sum fun i hi => ?_
          have : ((k:ℝ)/m) ^ k ≤ ((k:ℝ)/m) ^ i :=
            pow_le_pow_of_le_one hx0.le hx1 (Nat.lt_succ_iff.mp (mem_range.mp hi))
          exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
      _ ≤ ∑ i ∈ range (k + m + 1), (((k + m).choose i : ℕ) : ℝ) * ((k:ℝ)/m) ^ i := by
          have hsub : range (k + 1) ⊆ range (k + m + 1) :=
            Finset.range_subset_range.mpr (by omega)
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity
      _ = (1 + (k:ℝ)/m) ^ (k + m) := by
          rw [add_comm (1:ℝ) ((k:ℝ)/m), add_pow]
          exact Finset.sum_congr rfl fun i _ => by rw [one_pow, mul_one]; ring
  -- clear the denominators
  have h1 : (1:ℝ) + (k:ℝ)/m = ((k:ℝ) + m)/m := by field_simp; ring
  rw [h1, div_pow, div_pow] at hmgf
  have key : (∑ i ∈ range (k + 1), (((k + m).choose i : ℕ) : ℝ)) * ((k:ℝ)^k * (m:ℝ)^m)
      ≤ ((k:ℝ) + m) ^ (k + m) := by
    have hpos : (0:ℝ) < (m:ℝ) ^ (k + m) := by positivity
    have h2 := mul_le_mul_of_nonneg_right hmgf hpos.le
    calc (∑ i ∈ range (k + 1), (((k + m).choose i : ℕ) : ℝ)) * ((k:ℝ)^k * (m:ℝ)^m)
        = (∑ i ∈ range (k + 1), (((k + m).choose i : ℕ) : ℝ)) * ((k:ℝ)^k / (m:ℝ)^k)
            * (m:ℝ) ^ (k + m) := by
          rw [pow_add]
          field_simp
      _ ≤ ((k:ℝ) + m) ^ (k + m) / (m:ℝ) ^ (k + m) * (m:ℝ) ^ (k + m) := h2
      _ = ((k:ℝ) + m) ^ (k + m) := by field_simp
  -- the entropy bound is the logarithm of the same quantity
  have hlog : ((k:ℝ) + m) * Real.binEntropy ((k:ℝ) / ((k:ℝ) + m))
      = Real.log (((k:ℝ) + m) ^ (k + m) / ((k:ℝ)^k * (m:ℝ)^m)) := by
    have hsub : (1:ℝ) - (k:ℝ) / ((k:ℝ) + m) = (m:ℝ) / ((k:ℝ) + m) := by field_simp; ring
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.binEntropy, hsub, inv_div, inv_div,
      Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity)]
    field_simp
    push_cast
    ring
  push_cast
  rw [hlog, Real.exp_log (by positivity), le_div_iff₀ (by positivity)]
  exact key

end ProbMethodCombinatorics
