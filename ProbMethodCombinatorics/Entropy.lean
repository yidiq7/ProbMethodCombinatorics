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

/-! ### Auxiliary results for Shearer's lemma

Shearer's lemma is proved by running the chain rule along a fixed order of the coordinates.
Doing so needs two ingredients that §10.1 does not supply: the *conditioned* form of
`condEntropy_le_entropy`, namely `H(X ∣ Y, Z) ≤ H(X ∣ Z)`, which rests on submodularity of
entropy; and the bookkeeping that identifies `H(X_B)` for a finset `B` of coordinates with a
joint entropy of two blocks.  Both are collected here.
-/

section ShearerAux

/-- A Gibbs-type inequality.  If `a` is a probability vector, `b` is nonnegative with total
mass at most `1`, and `b` is nonzero wherever `a` is, then `∑ a log₂ b ≤ ∑ a log₂ a`.  The
proof is `log t ≤ t - 1` applied to `t = b i / a i`. -/
theorem sum_mul_logb_le_of_sum_le {σ : Type*} [Fintype σ] (a b : σ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hab : ∀ i, 0 < a i → 0 < b i)
    (ha1 : ∑ i, a i = 1) (hb1 : ∑ i, b i ≤ 1) :
    ∑ i, a i * Real.logb 2 (b i) ≤ ∑ i, a i * Real.logb 2 (a i) := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have key : ∀ i : σ, a i * Real.logb 2 (b i) - a i * Real.logb 2 (a i)
      ≤ (b i - a i) / Real.log 2 := by
    intro i
    rcases eq_or_lt_of_le (ha i) with h | h
    · rw [← h]
      simp only [zero_mul, sub_zero, sub_self]
      exact div_nonneg (hb i) hlog.le
    · have hbi : 0 < b i := hab i h
      have hstep : a i * Real.log (b i) - a i * Real.log (a i) ≤ b i - a i := by
        have h2 := Real.log_le_sub_one_of_pos (div_pos hbi h)
        rw [Real.log_div (ne_of_gt hbi) (ne_of_gt h)] at h2
        have h3 := mul_le_mul_of_nonneg_left h2 h.le
        have h4 : a i * (b i / a i) = b i := mul_div_cancel₀ _ (ne_of_gt h)
        nlinarith
      have heq : a i * Real.logb 2 (b i) - a i * Real.logb 2 (a i)
          = (a i * Real.log (b i) - a i * Real.log (a i)) / Real.log 2 := by
        simp only [Real.logb]
        ring
      rw [heq]
      gcongr
  have hsum : ∑ i, (a i * Real.logb 2 (b i) - a i * Real.logb 2 (a i))
      ≤ ∑ i, (b i - a i) / Real.log 2 := Finset.sum_le_sum fun i _ => key i
  rw [Finset.sum_sub_distrib] at hsum
  have hrw : ∑ i, (b i - a i) / Real.log 2 = (∑ i, b i - ∑ i, a i) / Real.log 2 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
  rw [hrw, ha1] at hsum
  have hle : (∑ i, b i - 1) / Real.log 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hlog.le
  linarith

/-- Submodularity, stated for the joint mass function of three variables.  If `P3` has the
marginals `Pxz`, `Pyz` and `Pz` recorded in `m1`–`m4` and total mass `1`, then the Shannon
entropies built from them satisfy `H(x,y,z) + H(z) ≤ H(x,z) + H(y,z)`.  The comparison vector
is `Pxz · Pyz / Pz`, whose total mass is again `1`. -/
theorem sum_logb_submodular {S' T' U' : Type*} [Fintype S'] [Fintype T'] [Fintype U']
    (P3 : S' → T' → U' → ℝ) (Pxz : S' → U' → ℝ) (Pyz : T' → U' → ℝ) (Pz : U' → ℝ)
    (h3 : ∀ x y z, 0 ≤ P3 x y z)
    (m1 : ∀ x z, ∑ y, P3 x y z = Pxz x z) (m2 : ∀ y z, ∑ x, P3 x y z = Pyz y z)
    (m3 : ∀ z, ∑ x, Pxz x z = Pz z) (m4 : ∀ z, ∑ y, Pyz y z = Pz z)
    (htot : ∑ z, Pz z = 1) :
    (∑ x, ∑ y, ∑ z, -P3 x y z * Real.logb 2 (P3 x y z)) + ∑ z, -Pz z * Real.logb 2 (Pz z)
      ≤ (∑ x, ∑ z, -Pxz x z * Real.logb 2 (Pxz x z))
        + ∑ y, ∑ z, -Pyz y z * Real.logb 2 (Pyz y z) := by
  have hxz : ∀ x z, 0 ≤ Pxz x z := by
    intro x z; rw [← m1 x z]; exact Finset.sum_nonneg fun y _ => h3 x y z
  have hyz : ∀ y z, 0 ≤ Pyz y z := by
    intro y z; rw [← m2 y z]; exact Finset.sum_nonneg fun x _ => h3 x y z
  have hz : ∀ z, 0 ≤ Pz z := by
    intro z; rw [← m3 z]; exact Finset.sum_nonneg fun x _ => hxz x z
  have le1 : ∀ x y z, P3 x y z ≤ Pxz x z := by
    intro x y z; rw [← m1 x z]
    exact Finset.single_le_sum (fun y' _ => h3 x y' z) (Finset.mem_univ y)
  have le2 : ∀ x y z, P3 x y z ≤ Pyz y z := by
    intro x y z; rw [← m2 y z]
    exact Finset.single_le_sum (fun x' _ => h3 x' y z) (Finset.mem_univ x)
  have le3 : ∀ x z, Pxz x z ≤ Pz z := by
    intro x z; rw [← m3 z]
    exact Finset.single_le_sum (fun x' _ => hxz x' z) (Finset.mem_univ x)
  have reorder : ∀ f : S' → T' → U' → ℝ, ∑ x, ∑ y, ∑ z, f x y z = ∑ z, ∑ x, ∑ y, f x y z := by
    intro f
    have step : ∀ x : S', ∑ y, ∑ z, f x y z = ∑ z, ∑ y, f x y z := fun x => Finset.sum_comm
    rw [Finset.sum_congr rfl fun x _ => step x, Finset.sum_comm]
  have tri : ∀ f : S' × T' × U' → ℝ, ∑ w : S' × T' × U', f w = ∑ x, ∑ y, ∑ z, f (x, y, z) := by
    intro f
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => Fintype.sum_prod_type _
  have hA1 : ∑ x, ∑ y, ∑ z, P3 x y z = 1 := by
    rw [reorder]
    calc ∑ z, ∑ x, ∑ y, P3 x y z
        = ∑ z, ∑ x, Pxz x z :=
          Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun x _ => m1 x z
      _ = ∑ z, Pz z := Finset.sum_congr rfl fun z _ => m3 z
      _ = 1 := htot
  have hB1 : ∑ x, ∑ y, ∑ z, Pxz x z * Pyz y z / Pz z = 1 := by
    rw [reorder]
    have inner : ∀ z, ∑ x, ∑ y, Pxz x z * Pyz y z / Pz z = Pz z := by
      intro z
      have e : ∀ x : S', ∑ y, Pxz x z * Pyz y z / Pz z = Pxz x z * Pz z / Pz z := by
        intro x
        rw [← Finset.sum_div, ← Finset.mul_sum, m4 z]
      rw [Finset.sum_congr rfl fun x _ => e x, ← Finset.sum_div, ← Finset.sum_mul, m3 z]
      rcases eq_or_ne (Pz z) 0 with h | h
      · simp [h]
      · field_simp
    rw [Finset.sum_congr rfl fun z _ => inner z, htot]
  have key := sum_mul_logb_le_of_sum_le (σ := S' × T' × U')
      (fun w => P3 w.1 w.2.1 w.2.2)
      (fun w => Pxz w.1 w.2.2 * Pyz w.2.1 w.2.2 / Pz w.2.2)
      (fun w => h3 _ _ _)
      (fun w => div_nonneg (mul_nonneg (hxz _ _) (hyz _ _)) (hz _))
      (fun w hw => div_pos
        (mul_pos (lt_of_lt_of_le hw (le1 _ _ _)) (lt_of_lt_of_le hw (le2 _ _ _)))
        (lt_of_lt_of_le hw (le_trans (le1 _ _ _) (le3 _ _))))
      (by rw [tri]; exact hA1) (by rw [tri]; exact le_of_eq hB1)
  rw [tri, tri] at key
  simp only at key
  have hsplit : ∀ x y z, P3 x y z * Real.logb 2 (Pxz x z * Pyz y z / Pz z)
      = P3 x y z * Real.logb 2 (Pxz x z) + P3 x y z * Real.logb 2 (Pyz y z)
        - P3 x y z * Real.logb 2 (Pz z) := by
    intro x y z
    rcases eq_or_lt_of_le (h3 x y z) with h | h
    · rw [← h]; ring
    · have h1 : Pxz x z ≠ 0 := ne_of_gt (lt_of_lt_of_le h (le1 x y z))
      have h2 : Pyz y z ≠ 0 := ne_of_gt (lt_of_lt_of_le h (le2 x y z))
      have h4 : Pz z ≠ 0 := ne_of_gt (lt_of_lt_of_le h (le_trans (le1 x y z) (le3 x z)))
      rw [Real.logb_div (mul_ne_zero h1 h2) h4, Real.logb_mul h1 h2]
      ring
  have e1 : ∑ x, ∑ y, ∑ z, P3 x y z * Real.logb 2 (Pxz x z)
      = ∑ x, ∑ z, Pxz x z * Real.logb 2 (Pxz x z) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← Finset.sum_mul, m1 x z]
  have e2 : ∑ x, ∑ y, ∑ z, P3 x y z * Real.logb 2 (Pyz y z)
      = ∑ y, ∑ z, Pyz y z * Real.logb 2 (Pyz y z) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← Finset.sum_mul, m2 y z]
  have e3 : ∑ x, ∑ y, ∑ z, P3 x y z * Real.logb 2 (Pz z)
      = ∑ z, Pz z * Real.logb 2 (Pz z) := by
    rw [reorder]
    refine Finset.sum_congr rfl fun z _ => ?_
    have e : ∀ x : S', ∑ y, P3 x y z * Real.logb 2 (Pz z) = Pxz x z * Real.logb 2 (Pz z) := by
      intro x; rw [← Finset.sum_mul, m1 x z]
    rw [Finset.sum_congr rfl fun x _ => e x, ← Finset.sum_mul, m3 z]
  have hL : ∑ x, ∑ y, ∑ z, P3 x y z * Real.logb 2 (Pxz x z * Pyz y z / Pz z)
      = (∑ x, ∑ z, Pxz x z * Real.logb 2 (Pxz x z))
        + (∑ y, ∑ z, Pyz y z * Real.logb 2 (Pyz y z))
        - ∑ z, Pz z * Real.logb 2 (Pz z) := by
    rw [← e1, ← e2, ← e3]
    simp only [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hL] at key
  simp only [neg_mul, Finset.sum_neg_distrib]
  linarith

/-- The counting step of Shearer's lemma: if every index lies in at least `k` of the sets
`A j` and the weights `c` are nonnegative, then `k · ∑ᵢ cᵢ ≤ ∑ⱼ ∑_{i ∈ A j} cᵢ`. -/
theorem sum_card_filter_mul_le {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : κ → Finset ι) (k : ℕ) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hk : ∀ i : ι, k ≤ (univ.filter fun j => i ∈ A j).card) :
    (k : ℝ) * ∑ i, c i ≤ ∑ j : κ, ∑ i ∈ A j, c i := by
  have h1 : ∀ j : κ, ∑ i : ι, (if i ∈ A j then c i else 0) = ∑ i ∈ A j, c i := by
    intro j
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [Finset.mul_sum]
  calc ∑ i : ι, (k : ℝ) * c i
      ≤ ∑ i : ι, ((univ.filter fun j => i ∈ A j).card : ℝ) * c i :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (by exact_mod_cast hk i) (hc i)
    _ = ∑ j : κ, ∑ i ∈ A j, c i := by
        simp only [← h1]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

variable [Fintype Ω] [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T] {p : Ω → ℝ}

omit [Fintype S] [Fintype T] in
/-- Relabelling the values of a random variable by an injection does not move the mass of a
fibre. -/
theorem probOf_comp_inj {f : S → T} (hf : Function.Injective f) (X : Ω → S) (s : S) :
    probOf p (fun ω => f (X ω)) (f s) = probOf p X s := by
  unfold probOf
  congr 1
  ext ω
  simp [hf.eq_iff]

/-- Entropy is invariant under an injective relabelling of the values. -/
theorem entropy_comp_inj {f : S → T} (hf : Function.Injective f) (X : Ω → S) :
    entropy p (fun ω => f (X ω)) = entropy p X := by
  have hzero : ∀ t ∈ (univ : Finset T), t ∉ univ.image f →
      -probOf p (fun ω => f (X ω)) t * Real.logb 2 (probOf p (fun ω => f (X ω)) t) = 0 := by
    intro t _ ht
    have h0 : probOf p (fun ω => f (X ω)) t = 0 := by
      have he : (univ.filter fun ω => f (X ω) = t) = ∅ := by
        ext ω
        simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
        intro h
        exact ht (mem_image.mpr ⟨X ω, mem_univ _, h⟩)
      simp [probOf, he]
    simp [h0]
  rw [entropy, ← Finset.sum_subset (Finset.subset_univ (univ.image f)) hzero,
    Finset.sum_image (fun a _ b _ h => hf h)]
  simp only [probOf_comp_inj hf]
  rfl

omit [Fintype S] in
/-- The fibres of a pair over a fixed first coordinate partition the fibre of that
coordinate. -/
theorem sum_probOf_pair (X : Ω → S) (Y : Ω → T) (s : S) :
    ∑ t : T, probOf p (fun ω => (X ω, Y ω)) (s, t) = probOf p X s := by
  have h : ∀ t : T, (univ.filter fun ω => (X ω, Y ω) = (s, t))
      = (univ.filter fun ω => X ω = s).filter fun ω => Y ω = t := by
    intro t
    ext ω
    simp [Prod.ext_iff]
  simp only [probOf, h]
  rw [Finset.sum_fiberwise_eq_sum_filter]
  simp

omit [Fintype T] in
/-- The second-coordinate form of `sum_probOf_pair`. -/
theorem sum_probOf_pair_left (X : Ω → S) (Y : Ω → T) (t : T) :
    ∑ s : S, probOf p (fun ω => (X ω, Y ω)) (s, t) = probOf p Y t := by
  have hswap : ∀ s : S, probOf p (fun ω => (Y ω, X ω)) (t, s)
      = probOf p (fun ω => (X ω, Y ω)) (s, t) := fun s =>
    probOf_comp_inj (p := p) (f := Prod.swap) Prod.swap_injective (fun ω => (X ω, Y ω)) (s, t)
  simp only [← hswap]
  exact sum_probOf_pair Y X t

omit [Fintype T] in
/-- A joint probability is at most the marginal of its second coordinate. -/
theorem probOf_pair_le_right (hp : ∀ ω, 0 ≤ p ω) (X : Ω → S) (Y : Ω → T) (s : S) (t : T) :
    probOf p (fun ω => (X ω, Y ω)) (s, t) ≤ probOf p Y t := by
  have hswap : probOf p (fun ω => (Y ω, X ω)) (t, s)
      = probOf p (fun ω => (X ω, Y ω)) (s, t) :=
    probOf_comp_inj (p := p) (f := Prod.swap) Prod.swap_injective (fun ω => (X ω, Y ω)) (s, t)
  rw [← hswap, ← sum_probOf_pair (p := p) Y X t]
  exact Finset.single_le_sum
    (fun s' _ => probOf_nonneg hp (fun ω => (Y ω, X ω)) (t, s')) (Finset.mem_univ s)

/-- A random variable with only one possible value carries no entropy. -/
theorem entropy_eq_zero_of_subsingleton [Subsingleton S] (hp1 : ∑ ω, p ω = 1) (X : Ω → S) :
    entropy p X = 0 := by
  have h : ∀ s : S, probOf p X s = 1 := by
    intro s
    have hf : (univ.filter fun ω => X ω = s) = univ := by
      ext ω; simp [Subsingleton.elim (X ω) s]
    rw [probOf, hf, hp1]
  simp [entropy, h]

/-- Conditional entropy is nonnegative: each conditional probability lies in `[0, 1]`. -/
theorem condEntropy_nonneg (hp : ∀ ω, 0 ≤ p ω) (X : Ω → S) (Y : Ω → T) :
    0 ≤ condEntropy p X Y := by
  refine Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun s _ => ?_
  have h1 : 0 ≤ probOf p (fun ω => (X ω, Y ω)) (s, t) := probOf_nonneg hp _ _
  have h2 : probOf p (fun ω => (X ω, Y ω)) (s, t) / probOf p Y t ≤ 1 :=
    div_le_one_of_le₀ (probOf_pair_le_right hp X Y s t) (probOf_nonneg hp Y t)
  have h3 : Real.logb 2 (probOf p (fun ω => (X ω, Y ω)) (s, t) / probOf p Y t) ≤ 0 :=
    Real.logb_nonpos (by norm_num) (div_nonneg h1 (probOf_nonneg hp Y t)) h2
  nlinarith

/-- Conditional entropy is invariant under an injective relabelling of the conditioning
variable. -/
theorem condEntropy_comp_inj {U : Type*} [Fintype U] [DecidableEq U] (hp : ∀ ω, 0 ≤ p ω)
    {f : T → U} (hf : Function.Injective f) (X : Ω → S) (Y : Ω → T) :
    condEntropy p X (fun ω => f (Y ω)) = condEntropy p X Y := by
  have hg : Function.Injective (fun w : S × T => (w.1, f w.2)) := by
    rintro ⟨s1, t1⟩ ⟨s2, t2⟩ h
    simp only [Prod.mk.injEq] at h
    simp [h.1, hf h.2]
  rw [condEntropy_eq_sub hp X (fun ω => f (Y ω)), condEntropy_eq_sub hp X Y,
    entropy_comp_inj hf Y, entropy_comp_inj hg (fun ω => (X ω, Y ω))]

/-- **Submodularity of entropy**: `H(X, Y, Z) + H(Z) ≤ H(X, Z) + H(Y, Z)`.  Taking `Z`
constant recovers subadditivity; the general case is `sum_logb_submodular` applied to the
joint mass function and its three marginals. -/
theorem entropy_triple_add_le {U : Type*} [Fintype U] [DecidableEq U]
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (X : Ω → S) (Y : Ω → T) (Z : Ω → U) :
    entropy p (fun ω => (X ω, Y ω, Z ω)) + entropy p Z ≤
      entropy p (fun ω => (X ω, Z ω)) + entropy p (fun ω => (Y ω, Z ω)) := by
  have hf1 : Function.Injective (fun w : S × T × U => ((w.1, w.2.2), w.2.1)) := by
    rintro ⟨x1, y1, z1⟩ ⟨x2, y2, z2⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨e1, e2⟩, e3⟩ := h
    simp [e1, e2, e3]
  have hf2 : Function.Injective (fun w : S × T × U => ((w.2.1, w.2.2), w.1)) := by
    rintro ⟨x1, y1, z1⟩ ⟨x2, y2, z2⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨e1, e2⟩, e3⟩ := h
    simp [e1, e2, e3]
  have m1 : ∀ (x : S) (z : U), ∑ y : T, probOf p (fun ω => (X ω, Y ω, Z ω)) (x, y, z)
      = probOf p (fun ω => (X ω, Z ω)) (x, z) := by
    intro x z
    rw [← sum_probOf_pair (p := p) (fun ω => (X ω, Z ω)) Y (x, z)]
    exact Finset.sum_congr rfl fun y _ =>
      (probOf_comp_inj (p := p) hf1 (fun ω => (X ω, Y ω, Z ω)) (x, y, z)).symm
  have m2 : ∀ (y : T) (z : U), ∑ x : S, probOf p (fun ω => (X ω, Y ω, Z ω)) (x, y, z)
      = probOf p (fun ω => (Y ω, Z ω)) (y, z) := by
    intro y z
    rw [← sum_probOf_pair (p := p) (fun ω => (Y ω, Z ω)) X (y, z)]
    exact Finset.sum_congr rfl fun x _ =>
      (probOf_comp_inj (p := p) hf2 (fun ω => (X ω, Y ω, Z ω)) (x, y, z)).symm
  have m3 : ∀ z : U, ∑ x : S, probOf p (fun ω => (X ω, Z ω)) (x, z) = probOf p Z z :=
    fun z => sum_probOf_pair_left X Z z
  have m4 : ∀ z : U, ∑ y : T, probOf p (fun ω => (Y ω, Z ω)) (y, z) = probOf p Z z :=
    fun z => sum_probOf_pair_left Y Z z
  have htot : ∑ z : U, probOf p Z z = 1 := by rw [sum_probOf, hp1]
  have hE3 : entropy p (fun ω => (X ω, Y ω, Z ω))
      = ∑ x : S, ∑ y : T, ∑ z : U, -probOf p (fun ω => (X ω, Y ω, Z ω)) (x, y, z)
          * Real.logb 2 (probOf p (fun ω => (X ω, Y ω, Z ω)) (x, y, z)) := by
    rw [entropy, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => Fintype.sum_prod_type _
  have hExz : entropy p (fun ω => (X ω, Z ω))
      = ∑ x : S, ∑ z : U, -probOf p (fun ω => (X ω, Z ω)) (x, z)
          * Real.logb 2 (probOf p (fun ω => (X ω, Z ω)) (x, z)) := by
    rw [entropy, Fintype.sum_prod_type]
  have hEyz : entropy p (fun ω => (Y ω, Z ω))
      = ∑ y : T, ∑ z : U, -probOf p (fun ω => (Y ω, Z ω)) (y, z)
          * Real.logb 2 (probOf p (fun ω => (Y ω, Z ω)) (y, z)) := by
    rw [entropy, Fintype.sum_prod_type]
  rw [hE3, hExz, hEyz, entropy]
  exact sum_logb_submodular _ _ _ _ (fun x y z => probOf_nonneg hp _ _) m1 m2 m3 m4 htot

/-- **Dropping conditioning, conditioned form**: `H(X ∣ Y, Z) ≤ H(X ∣ Z)`.  This is the
refinement of `condEntropy_le_entropy` that Shearer's lemma needs; it is the chain rule
`condEntropy_eq_sub` together with submodularity of entropy. -/
theorem condEntropy_pair_le {U : Type*} [Fintype U] [DecidableEq U]
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (X : Ω → S) (Y : Ω → T) (Z : Ω → U) :
    condEntropy p X (fun ω => (Y ω, Z ω)) ≤ condEntropy p X Z := by
  rw [condEntropy_eq_sub hp X (fun ω => (Y ω, Z ω)), condEntropy_eq_sub hp X Z]
  have hsub := entropy_triple_add_le (p := p) hp hp1 X Y Z
  linarith

end ShearerAux

section ShearerPiAux

variable [Fintype Ω] {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
variable [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)] {p : Ω → ℝ}

omit [Fintype ι] [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)] in
/-- Splitting off the coordinate `i` from `insert i C` is injective on tuples. -/
theorem pi_insert_injective (C : Finset ι) (i : ι) :
    Function.Injective (fun g : ∀ j : ↥(insert i C), α j.1 =>
      (g ⟨i, Finset.mem_insert_self i C⟩,
        fun j : C => g ⟨j.1, Finset.mem_insert_of_mem j.2⟩)) := by
  intro g g' h
  funext j
  obtain ⟨x, hx⟩ := j
  rcases Finset.mem_insert.mp hx with rfl | hxC
  · exact congrArg Prod.fst h
  · exact congrFun (congrArg Prod.snd h) ⟨x, hxC⟩

omit [Fintype ι] [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)] in
/-- Splitting a tuple indexed by `D` into its `D \ C` and `C` blocks is injective. -/
theorem pi_sdiff_injective {C D : Finset ι} (hCD : C ⊆ D) :
    Function.Injective (fun g : ∀ j : D, α j.1 =>
      ((fun j : (D \ C : Finset ι) => g ⟨j.1, Finset.sdiff_subset j.2⟩),
        fun j : C => g ⟨j.1, hCD j.2⟩)) := by
  intro g g' h
  funext j
  obtain ⟨x, hx⟩ := j
  by_cases hxC : x ∈ C
  · exact congrFun (congrArg Prod.snd h) ⟨x, hxC⟩
  · exact congrFun (congrArg Prod.fst h) ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxC⟩⟩

omit [Fintype ι] in
/-- `H(X_{insert i C})` is the joint entropy of `X i` and `X_C`. -/
theorem entropy_pi_insert (X : ∀ i, Ω → α i) (C : Finset ι) (i : ι) :
    entropy p (fun ω (j : ↥(insert i C)) => X j.1 ω)
      = entropy p (fun ω => (X i ω, fun j : C => X j.1 ω)) :=
  (entropy_comp_inj (p := p) (pi_insert_injective C i) fun ω (j : ↥(insert i C)) => X j.1 ω).symm

omit [Fintype ι] in
/-- For `C ⊆ D`, `H(X_D)` is the joint entropy of the blocks `X_{D \ C}` and `X_C`. -/
theorem entropy_pi_sdiff (X : ∀ i, Ω → α i) {C D : Finset ι} (hCD : C ⊆ D) :
    entropy p (fun ω (j : D) => X j.1 ω)
      = entropy p (fun ω => ((fun j : (D \ C : Finset ι) => X j.1 ω),
          fun j : C => X j.1 ω)) :=
  (entropy_comp_inj (p := p) (pi_sdiff_injective hCD) fun ω (j : D) => X j.1 ω).symm

omit [Fintype ι] in
/-- Joint entropy is monotone in the set of coordinates. -/
theorem entropy_pi_mono (hp : ∀ ω, 0 ≤ p ω) (X : ∀ i, Ω → α i) {C D : Finset ι} (hCD : C ⊆ D) :
    entropy p (fun ω (j : C) => X j.1 ω) ≤ entropy p (fun ω (j : D) => X j.1 ω) := by
  have h1 := condEntropy_nonneg (p := p) hp
    (fun ω (j : (D \ C : Finset ι)) => X j.1 ω) (fun ω (j : C) => X j.1 ω)
  rw [condEntropy_eq_sub hp] at h1
  rw [entropy_pi_sdiff X hCD]
  linarith

omit [Fintype ι] in
/-- Adding the coordinate `i` to `C` raises the joint entropy by `H(X i ∣ X_C)`. -/
theorem entropy_pi_insert_sub (hp : ∀ ω, 0 ≤ p ω) (X : ∀ i, Ω → α i) (C : Finset ι) (i : ι) :
    entropy p (fun ω (j : ↥(insert i C)) => X j.1 ω) - entropy p (fun ω (j : C) => X j.1 ω)
      = condEntropy p (X i) (fun ω (j : C) => X j.1 ω) := by
  rw [condEntropy_eq_sub hp, entropy_pi_insert X C i]

omit [Fintype ι] in
/-- Conditioning on more coordinates can only lower the conditional entropy. -/
theorem condEntropy_pi_le (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (X : ∀ i, Ω → α i)
    {C D : Finset ι} (hCD : C ⊆ D) (i : ι) :
    condEntropy p (X i) (fun ω (j : D) => X j.1 ω)
      ≤ condEntropy p (X i) (fun ω (j : C) => X j.1 ω) := by
  rw [← condEntropy_comp_inj hp (pi_sdiff_injective hCD) (X i) (fun ω (j : D) => X j.1 ω)]
  exact condEntropy_pair_le hp hp1 (X i) _ _

omit [Fintype ι] in
/-- **The chain rule along a linear order.**  For an injective rank function `r`, the joint
entropy of the coordinates in `B` is the sum over `i ∈ B` of `H(X i ∣ X_{B ∩ [< i]})`. -/
theorem entropy_pi_eq_sum_condEntropy (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (X : ∀ i, Ω → α i) {r : ι → ℕ} (hr : Function.Injective r) (B : Finset ι) :
    entropy p (fun ω (j : B) => X j.1 ω)
      = ∑ i ∈ B, condEntropy p (X i)
          (fun ω (j : (B.filter fun x => r x < r i)) => X j.1 ω) := by
  induction B using Finset.strongInduction with
  | _ B ih =>
    rcases B.eq_empty_or_nonempty with rfl | hB
    · rw [Finset.sum_empty]
      have : Subsingleton (∀ j : ↥(∅ : Finset ι), α j.1) :=
        ⟨fun f g => funext fun j => absurd j.2 (Finset.notMem_empty j.1)⟩
      exact entropy_eq_zero_of_subsingleton hp1 _
    · obtain ⟨i₀, hi₀B, hmax⟩ := Finset.exists_max_image B r hB
      have hi₀lt : ∀ x ∈ B, x ≠ i₀ → r x < r i₀ := fun x hx hne =>
        lt_of_le_of_ne (hmax x hx) fun he => hne (hr he)
      have hfilt : (B.filter fun x => r x < r i₀) = B.erase i₀ := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hx, hlt⟩
          exact ⟨fun he => by rw [he] at hlt; exact lt_irrefl _ hlt, hx⟩
        · rintro ⟨hne, hx⟩
          exact ⟨hx, hi₀lt x hx hne⟩
      have hins : insert i₀ (B.erase i₀) = B := Finset.insert_erase hi₀B
      have hrest : ∀ i ∈ B.erase i₀,
          (B.filter fun x => r x < r i) = ((B.erase i₀).filter fun x => r x < r i) := by
        intro i hi
        have hib : i ∈ B := Finset.mem_of_mem_erase hi
        have hlti : r i < r i₀ := hi₀lt i hib (Finset.ne_of_mem_erase hi)
        ext x
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hx, hlt⟩
          refine ⟨⟨fun he => ?_, hx⟩, hlt⟩
          rw [he] at hlt
          exact absurd (lt_trans hlt hlti) (lt_irrefl _)
        · rintro ⟨⟨_, hx⟩, hlt⟩
          exact ⟨hx, hlt⟩
      have step := entropy_pi_insert_sub (p := p) hp X (B.erase i₀) i₀
      rw [hins] at step
      have ihB := ih (B.erase i₀) (Finset.erase_ssubset hi₀B)
      have hsum : ∑ i ∈ B.erase i₀, condEntropy p (X i)
            (fun ω (j : (B.filter fun x => r x < r i)) => X j.1 ω)
          = ∑ i ∈ B.erase i₀, condEntropy p (X i)
            (fun ω (j : ((B.erase i₀).filter fun x => r x < r i)) => X j.1 ω) :=
        Finset.sum_congr rfl fun i hi => by rw [hrest i hi]
      rw [← Finset.add_sum_erase B _ hi₀B, hfilt, hsum, ← ihB]
      linarith

end ShearerPiAux

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
  obtain ⟨r, hr⟩ : ∃ r : ι → ℕ, Function.Injective r :=
    ⟨fun i => ((Fintype.equivFin ι) i : ℕ), fun a b h =>
      (Fintype.equivFin ι).injective (Fin.val_injective h)⟩
  have hfu : Function.Injective (fun g : ∀ i, α i => fun j : (univ : Finset ι) => g j.1) := by
    intro g g' h
    funext i
    exact congrFun h ⟨i, Finset.mem_univ i⟩
  have huniv : entropy p (fun ω i => X i ω)
      = entropy p (fun ω (j : (univ : Finset ι)) => X j.1 ω) :=
    (entropy_comp_inj hfu (fun ω i => X i ω)).symm
  have hjb : ∀ j : κ, ∑ i ∈ A j, condEntropy p (X i)
        (fun ω (j' : ((univ : Finset ι).filter fun x => r x < r i)) => X j'.1 ω)
      ≤ entropy p (fun ω (i : A j) => X i.1 ω) := by
    intro j
    rw [entropy_pi_eq_sum_condEntropy hp hp1 X hr (A j)]
    refine Finset.sum_le_sum fun i _ => ?_
    exact condEntropy_pi_le hp hp1 X
      (Finset.filter_subset_filter _ (Finset.subset_univ (A j))) i
  rw [huniv, entropy_pi_eq_sum_condEntropy hp hp1 X hr univ]
  refine le_trans (sum_card_filter_mul_le A k _ (fun i => condEntropy_nonneg hp _ _) hk) ?_
  exact Finset.sum_le_sum fun j _ => hjb j

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
  sorry

end ProbMethodCombinatorics
