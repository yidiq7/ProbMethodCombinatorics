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
  refine Finset.sum_nonneg fun s _ => ?_
  have h0 : 0 ≤ probOf p X s := probOf_nonneg hp X s
  have h1 : probOf p X s ≤ 1 := probOf_le_one hp hp1 X s
  have hlog : Real.logb 2 (probOf p X s) ≤ 0 := Real.logb_nonpos one_lt_two h0 h1
  nlinarith

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
  have key : ∀ t : T, ∑ s : S, probOf p (fun ω => (X ω, Y ω)) (s, t) = probOf p Y t := by
    intro t
    have hfil : ∀ s : S, (univ.filter fun ω => (X ω, Y ω) = (s, t))
        = (univ.filter fun ω => Y ω = t).filter fun ω => X ω = s := by
      intro s
      ext ω
      simp [Prod.ext_iff, and_comm]
    calc ∑ s : S, probOf p (fun ω => (X ω, Y ω)) (s, t)
        = ∑ s : S, ∑ ω ∈ (univ.filter fun ω => Y ω = t).filter fun ω => X ω = s, p ω := by
          simp only [probOf, hfil]
      _ = ∑ ω ∈ (univ.filter fun ω => Y ω = t).filter fun ω => X ω ∈ (univ : Finset S), p ω :=
          Finset.sum_fiberwise_eq_sum_filter _ _ _ _
      _ = probOf p Y t := by simp [probOf]
  have aux : ∀ (b : ℝ) (a : S → ℝ), (∀ s, 0 ≤ a s) → ∑ s, a s = b →
      ∑ s, -a s * Real.logb 2 (a s / b)
        = (∑ s, -a s * Real.logb 2 (a s)) - -b * Real.logb 2 b := by
    intro b a ha hab
    have hb0 : (0 : ℝ) ≤ b := hab ▸ Finset.sum_nonneg fun s _ => ha s
    rcases hb0.eq_or_lt with hb | hb
    · have hz : ∀ s, a s = 0 := fun s =>
        (Finset.sum_eq_zero_iff_of_nonneg fun s _ => ha s).1 (hab.trans hb.symm) s (mem_univ s)
      subst hb
      simp [hz]
    · have hbne : b ≠ 0 := ne_of_gt hb
      have hpt : ∀ s ∈ (univ : Finset S), -a s * Real.logb 2 (a s / b)
          = -a s * Real.logb 2 (a s) + a s * Real.logb 2 b := by
        intro s _
        rcases (ha s).eq_or_lt with hs | hs
        · simp [← hs]
        · rw [Real.logb_div (ne_of_gt hs) hbne]; ring
      rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ← Finset.sum_mul, hab]
      ring
  simp only [condEntropy, entropy]
  conv_rhs => rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun t _ =>
    aux _ _ (fun s => probOf_nonneg hp _ (s, t)) (key t)

/-- **Subadditivity** for two variables (Lemma 10.1.8): `H(X, Y) ≤ H(X) + H(Y)`, equivalently
that the mutual information `I(X; Y)` is nonnegative.  The proof is Jensen's inequality applied
to the convex function `t ↦ log₂ (1 / t)`. -/
theorem entropy_pair_le_add (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (X : Ω → S) (Y : Ω → T) :
    entropy p (fun ω => (X ω, Y ω)) ≤ entropy p X + entropy p Y := by
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hqnn : ∀ x : S × T, 0 ≤ probOf p (fun ω => (X ω, Y ω)) x := fun x => probOf_nonneg hp _ x
  have hsumY : ∑ t : T, probOf p Y t = 1 := by rw [sum_probOf]; exact hp1
  have hmargX : ∀ s : S, ∑ t : T, probOf p (fun ω => (X ω, Y ω)) (s, t) = probOf p X s := by
    intro s
    have hfib : ∀ t : T, probOf p (fun ω => (X ω, Y ω)) (s, t)
        = ∑ ω ∈ (univ.filter fun ω => X ω = s).filter fun ω => Y ω = t, p ω := by
      intro t
      unfold probOf
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
    calc ∑ t : T, probOf p (fun ω => (X ω, Y ω)) (s, t)
        = ∑ t : T, ∑ ω ∈ (univ.filter fun ω => X ω = s).filter fun ω => Y ω = t, p ω :=
          Finset.sum_congr rfl fun t _ => hfib t
      _ = probOf p X s := by
          rw [Finset.sum_fiberwise_eq_sum_filter]
          simp [probOf]
  have hmargY : ∀ t : T, ∑ s : S, probOf p (fun ω => (X ω, Y ω)) (s, t) = probOf p Y t := by
    intro t
    have hfib : ∀ s : S, probOf p (fun ω => (X ω, Y ω)) (s, t)
        = ∑ ω ∈ (univ.filter fun ω => Y ω = t).filter fun ω => X ω = s, p ω := by
      intro s
      unfold probOf
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
      tauto
    calc ∑ s : S, probOf p (fun ω => (X ω, Y ω)) (s, t)
        = ∑ s : S, ∑ ω ∈ (univ.filter fun ω => Y ω = t).filter fun ω => X ω = s, p ω :=
          Finset.sum_congr rfl fun s _ => hfib s
      _ = probOf p Y t := by
          rw [Finset.sum_fiberwise_eq_sum_filter]
          simp [probOf]
  have hqleX : ∀ (s : S) (t : T), probOf p (fun ω => (X ω, Y ω)) (s, t) ≤ probOf p X s := by
    intro s t
    rw [← hmargX s]
    exact Finset.single_le_sum (fun t' _ => hqnn (s, t')) (Finset.mem_univ t)
  have hqleY : ∀ (s : S) (t : T), probOf p (fun ω => (X ω, Y ω)) (s, t) ≤ probOf p Y t := by
    intro s t
    rw [← hmargY t]
    exact Finset.single_le_sum (fun s' _ => hqnn (s', t)) (Finset.mem_univ s)
  have key : ∀ u v w : ℝ, 0 ≤ w → w ≤ u → w ≤ v →
      -w * Real.logb 2 w
        ≤ -w * Real.logb 2 u + -w * Real.logb 2 v + (u * v - w) / Real.log 2 := by
    intro u v w hw hwu hwv
    rcases hw.eq_or_lt with rfl | hw0
    · simp only [neg_zero, zero_mul, sub_zero, zero_add]
      exact div_nonneg (mul_nonneg hwu hwv) hL.le
    · have hu0 : 0 < u := lt_of_lt_of_le hw0 hwu
      have hv0 : 0 < v := lt_of_lt_of_le hw0 hwv
      have h1 : Real.log (u * v / w) ≤ u * v / w - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h2 := mul_le_mul_of_nonneg_left h1 hw
      rw [Real.log_div (by positivity) (ne_of_gt hw0),
        Real.log_mul (ne_of_gt hu0) (ne_of_gt hv0)] at h2
      have h3 : w * (u * v / w - 1) = u * v - w := by field_simp
      rw [h3] at h2
      have h4 : -w * Real.log w ≤ -w * Real.log u + -w * Real.log v + (u * v - w) := by
        linarith
      have h5 := mul_le_mul_of_nonneg_right h4 (le_of_lt (inv_pos.mpr hL))
      calc -w * Real.logb 2 w = (-w * Real.log w) * (Real.log 2)⁻¹ := by
            rw [Real.logb]; ring
        _ ≤ (-w * Real.log u + -w * Real.log v + (u * v - w)) * (Real.log 2)⁻¹ := h5
        _ = -w * Real.logb 2 u + -w * Real.logb 2 v + (u * v - w) / Real.log 2 := by
            rw [Real.logb, Real.logb]; ring
  have hjoint : entropy p (fun ω => (X ω, Y ω))
      = ∑ s : S, ∑ t : T, -probOf p (fun ω => (X ω, Y ω)) (s, t)
          * Real.logb 2 (probOf p (fun ω => (X ω, Y ω)) (s, t)) := by
    rw [entropy, Fintype.sum_prod_type]
  have hX : ∑ s : S, ∑ t : T, -probOf p (fun ω => (X ω, Y ω)) (s, t)
      * Real.logb 2 (probOf p X s) = entropy p X := by
    rw [entropy]
    refine Finset.sum_congr rfl fun s _ => ?_
    calc ∑ t : T, -probOf p (fun ω => (X ω, Y ω)) (s, t) * Real.logb 2 (probOf p X s)
        = (∑ t : T, probOf p (fun ω => (X ω, Y ω)) (s, t)) * -Real.logb 2 (probOf p X s) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun t _ => by ring
      _ = -probOf p X s * Real.logb 2 (probOf p X s) := by rw [hmargX s]; ring
  have hY : ∑ s : S, ∑ t : T, -probOf p (fun ω => (X ω, Y ω)) (s, t)
      * Real.logb 2 (probOf p Y t) = entropy p Y := by
    rw [Finset.sum_comm, entropy]
    refine Finset.sum_congr rfl fun t _ => ?_
    calc ∑ s : S, -probOf p (fun ω => (X ω, Y ω)) (s, t) * Real.logb 2 (probOf p Y t)
        = (∑ s : S, probOf p (fun ω => (X ω, Y ω)) (s, t)) * -Real.logb 2 (probOf p Y t) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun s _ => by ring
      _ = -probOf p Y t * Real.logb 2 (probOf p Y t) := by rw [hmargY t]; ring
  have hZero : ∑ s : S, ∑ t : T, (probOf p X s * probOf p Y t
      - probOf p (fun ω => (X ω, Y ω)) (s, t)) / Real.log 2 = 0 := by
    have h0 : ∀ s : S, ∑ t : T, (probOf p X s * probOf p Y t
        - probOf p (fun ω => (X ω, Y ω)) (s, t)) = 0 := by
      intro s
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsumY, mul_one, hmargX s, sub_self]
    calc ∑ s : S, ∑ t : T, (probOf p X s * probOf p Y t
          - probOf p (fun ω => (X ω, Y ω)) (s, t)) / Real.log 2
        = ∑ s : S, (∑ t : T, (probOf p X s * probOf p Y t
            - probOf p (fun ω => (X ω, Y ω)) (s, t))) / Real.log 2 :=
          Finset.sum_congr rfl fun s _ => (Finset.sum_div _ _ _).symm
      _ = 0 := by simp [h0]
  calc entropy p (fun ω => (X ω, Y ω))
      = ∑ s : S, ∑ t : T, -probOf p (fun ω => (X ω, Y ω)) (s, t)
          * Real.logb 2 (probOf p (fun ω => (X ω, Y ω)) (s, t)) := hjoint
    _ ≤ ∑ s : S, ∑ t : T, (-probOf p (fun ω => (X ω, Y ω)) (s, t) * Real.logb 2 (probOf p X s)
          + -probOf p (fun ω => (X ω, Y ω)) (s, t) * Real.logb 2 (probOf p Y t)
          + (probOf p X s * probOf p Y t
              - probOf p (fun ω => (X ω, Y ω)) (s, t)) / Real.log 2) :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ =>
          key _ _ _ (hqnn (s, t)) (hqleX s t) (hqleY s t)
    _ = entropy p X + entropy p Y := by
        simp only [Finset.sum_add_distrib]
        rw [hX, hY, hZero, add_zero]

/-- **Dropping conditioning** (Lemma 10.1.10): `H(X ∣ Y) ≤ H(X)`.  This is immediate from
`condEntropy_eq_sub` and `entropy_pair_le_add`. -/
theorem condEntropy_le_entropy (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (X : Ω → S)
    (Y : Ω → T) :
    condEntropy p X Y ≤ entropy p X := by
  rw [condEntropy_eq_sub hp X Y]
  have h := entropy_pair_le_add hp hp1 X Y
  linarith

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

private theorem entropy_const [Fintype S] [DecidableEq S] {p : Ω → ℝ} (hp1 : ∑ ω, p ω = 1)
    (c : S) : entropy p (fun _ : Ω => c) = 0 := by
  unfold entropy
  refine Finset.sum_eq_zero fun s _ => ?_
  rcases eq_or_ne c s with rfl | hcs
  · have h : probOf p (fun _ : Ω => c) c = 1 := by simp [probOf, hp1]
    rw [h]; simp
  · have h : probOf p (fun _ : Ω => c) s = 0 := by simp [probOf, hcs]
    rw [h]; simp

private theorem entropy_eq_of_comp [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    (p : Ω → ℝ) {f : S → T} (hf : Function.Injective f) (X : Ω → S) (Z : Ω → T)
    (hZ : ∀ ω, Z ω = f (X ω)) : entropy p Z = entropy p X := by
  have hfun : Z = fun ω => f (X ω) := funext hZ
  subst hfun
  have hprob : ∀ s : S, probOf p (fun ω => f (X ω)) (f s) = probOf p X s := by
    intro s
    unfold probOf
    exact Finset.sum_congr (Finset.filter_congr fun ω _ => by simp [hf.eq_iff]) fun _ _ => rfl
  unfold entropy
  rw [← Finset.sum_subset (Finset.subset_univ ((univ : Finset S).image f))]
  · rw [Finset.sum_image fun x _ y _ h => hf h]
    exact Finset.sum_congr rfl fun s _ => by rw [hprob s]
  · intro t _ ht
    have h0 : probOf p (fun ω => f (X ω)) t = 0 := by
      unfold probOf
      refine Finset.sum_eq_zero fun ω hω => ?_
      exact absurd (Finset.mem_image.mpr
        ⟨X ω, Finset.mem_univ _, (Finset.mem_filter.mp hω).2⟩) ht
    rw [h0]; simp

/-- **Subadditivity** in general (Lemma 10.1.8): `H(X₁, …, Xₙ) ≤ H(X₁) + ⋯ + H(Xₙ)`, obtained
by iterating `entropy_pair_le_add`. -/
theorem entropy_pi_le_sum (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (X : ∀ i, Ω → α i) :
    entropy p (fun ω i => X i ω) ≤ ∑ i, entropy p fun ω => X i ω := by
  obtain ⟨Y, hY⟩ : ∃ Y : Finset ι → Ω → ∀ i, Option (α i),
      ∀ (s : Finset ι) (ω : Ω) (i : ι), Y s ω i = if i ∈ s then some (X i ω) else none :=
    ⟨_, fun _ _ _ => rfl⟩
  have key : ∀ s : Finset ι, entropy p (Y s) ≤ ∑ i ∈ s, entropy p fun ω => X i ω := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have h : Y ∅ = fun (_ : Ω) (_ : ι) => none := by
          funext ω i; rw [hY]; simp
        rw [h, entropy_const hp1]
        simp
    | @insert a s ha ih =>
        have hinj : Function.Injective
            (fun g : ∀ i, Option (α i) => (g a, Function.update g a (none : Option (α a)))) := by
          intro g h hgh
          funext i
          by_cases hi : i = a
          · subst hi; exact congrArg Prod.fst hgh
          · have h2 : Function.update g a (none : Option (α a)) i
                = Function.update h a (none : Option (α a)) i :=
              congrFun (congrArg Prod.snd hgh) i
            rwa [Function.update_of_ne hi, Function.update_of_ne hi] at h2
        have h1 : entropy p (fun ω => (some (X a ω), Y s ω)) = entropy p (Y (insert a s)) := by
          refine entropy_eq_of_comp p hinj (Y (insert a s)) _ fun ω => ?_
          refine Prod.ext ?_ ?_
          · simpa using (hY (insert a s) ω a).symm
          · funext i
            by_cases hi : i = a
            · subst hi
              simp only [Function.update_self]
              rw [hY]
              simp [ha]
            · simp only [Function.update_of_ne hi]
              rw [hY, hY]
              simp [hi]
        have h2 := entropy_pair_le_add hp hp1 (fun ω => some (X a ω)) (Y s)
        have h3 : entropy p (fun ω => some (X a ω)) = entropy p fun ω => X a ω :=
          entropy_eq_of_comp p (Option.some_injective (α a)) _ _ fun _ => rfl
        rw [Finset.sum_insert ha, ← h1]
        calc entropy p (fun ω => (some (X a ω), Y s ω))
            ≤ entropy p (fun ω => some (X a ω)) + entropy p (Y s) := h2
          _ ≤ (entropy p fun ω => X a ω) + ∑ i ∈ s, entropy p fun ω => X i ω := by
              rw [h3]; linarith [ih]
  have hsome : Function.Injective
      (fun (g : ∀ i, α i) (i : ι) => (some (g i) : Option (α i))) := by
    intro g h hgh
    funext i
    exact Option.some_injective _ (congrFun hgh i)
  have hfin : entropy p (Y univ) = entropy p (fun ω i => X i ω) :=
    entropy_eq_of_comp p hsome _ _ fun ω => by funext i; rw [hY]; simp
  rw [← hfin]
  exact key univ

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

/-- A value outside the range of `X` has probability zero. -/
private theorem probOf_eq_zero_of_notMem_image {Ω S : Type*} [Fintype Ω] [Fintype S]
    [DecidableEq S] (p : Ω → ℝ) (X : Ω → S) (s : S)
    (hs : s ∉ (univ : Finset Ω).image X) : probOf p X s = 0 := by
  refine Finset.sum_eq_zero fun ω hω => absurd ?_ hs
  rw [Finset.mem_filter] at hω
  exact hω.2 ▸ Finset.mem_image_of_mem X (Finset.mem_univ ω)

/-- Entropy is at most the logarithm of the size of the range. -/
private theorem entropy_le_logb_card_image {Ω S : Type*} [Fintype Ω] [Fintype S]
    [DecidableEq S] {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (X : Ω → S) :
    entropy p X ≤ Real.logb 2 (((univ : Finset Ω).image X).card : ℝ) :=
  entropy_le_logb_card hp hp1 X _ fun s hs => probOf_eq_zero_of_notMem_image p X s hs

/-- The uniform distribution on `Ω` gives an injective random variable entropy `log₂ |Ω|`. -/
private theorem entropy_uniformPMF_univ_of_injective {Ω S : Type*} [Fintype Ω] [DecidableEq Ω]
    [Nonempty Ω] [Fintype S] [DecidableEq S] {X : Ω → S} (hX : Function.Injective X) :
    entropy (uniformPMF (univ : Finset Ω)) X = Real.logb 2 (Fintype.card Ω : ℝ) := by
  have hn : ((Fintype.card Ω : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hval : ∀ ω : Ω, uniformPMF (univ : Finset Ω) ω = ((Fintype.card Ω : ℝ))⁻¹ := by
    intro ω
    simp [uniformPMF]
  have hprob : ∀ s : S, probOf (uniformPMF (univ : Finset Ω)) X s
      = if s ∈ (univ : Finset Ω).image X then ((Fintype.card Ω : ℝ))⁻¹ else 0 := by
    intro s
    by_cases hs : s ∈ (univ : Finset Ω).image X
    · obtain ⟨ω, -, rfl⟩ := Finset.mem_image.mp hs
      rw [if_pos hs]
      show (∑ ω' ∈ univ.filter fun ω' => X ω' = X ω, uniformPMF (univ : Finset Ω) ω')
        = ((Fintype.card Ω : ℝ))⁻¹
      rw [show (univ.filter fun ω' => X ω' = X ω) = {ω} from by ext ω'; simp [hX.eq_iff]]
      simp [hval]
    · rw [if_neg hs]
      exact probOf_eq_zero_of_notMem_image _ X s hs
  have hsum : entropy (uniformPMF (univ : Finset Ω)) X
      = ∑ s : S, if s ∈ (univ : Finset Ω).image X then
          -((Fintype.card Ω : ℝ))⁻¹ * Real.logb 2 (((Fintype.card Ω : ℝ))⁻¹) else 0 := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hprob s]
    split_ifs <;> simp
  rw [hsum]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
    Finset.card_image_of_injective _ hX, Finset.card_univ, nsmul_eq_mul]
  rw [Real.logb_inv]
  field_simp

/-- The range of `ω ↦ g ω` over the subtype `↥A` is the image of `A` under `g`. -/
private theorem card_image_univ_coe {σ τ : Type*} [DecidableEq σ] [DecidableEq τ]
    (A : Finset σ) (g : σ → τ) :
    ((univ : Finset ↥A).image fun ω => g ω.1).card = (A.image g).card := by
  congr 1
  ext t
  simp

/-- Postcomposing with an injection does not change the size of a range. -/
private theorem card_image_univ_of_injective {Ω S S' : Type*} [Fintype Ω] [DecidableEq S]
    [DecidableEq S'] (W : Ω → S) (f : S → S') (hf : Function.Injective f) :
    ((univ : Finset Ω).image W).card = ((univ : Finset Ω).image fun ω => f (W ω)).card := by
  rw [show ((univ : Finset Ω).image fun ω => f (W ω))
      = ((univ : Finset Ω).image W).image f from (Finset.image_image).symm,
    Finset.card_image_of_injective _ hf]

/-- The range of a pair of subtype-valued coordinates has the same size as the corresponding
image of `A` under the pair of the underlying maps. -/
private theorem card_image_univ_pair {σ τ₁ τ₂ : Type*} [DecidableEq σ] [DecidableEq τ₁]
    [DecidableEq τ₂] (A : Finset σ) {B₁ : Finset τ₁} {B₂ : Finset τ₂}
    (W₁ : ↥A → ↥B₁) (W₂ : ↥A → ↥B₂) (g₁ : σ → τ₁) (g₂ : σ → τ₂)
    (h₁ : ∀ ω : ↥A, (W₁ ω : τ₁) = g₁ ω.1) (h₂ : ∀ ω : ↥A, (W₂ ω : τ₂) = g₂ ω.1) :
    ((univ : Finset ↥A).image fun ω => (W₁ ω, W₂ ω)).card
      = (A.image fun x => (g₁ x, g₂ x)).card := by
  rw [card_image_univ_of_injective (fun ω : ↥A => (W₁ ω, W₂ ω))
    (fun q : ↥B₁ × ↥B₂ => ((q.1 : τ₁), (q.2 : τ₂)))
    (by intro q q' h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2))]
  simp only [h₁, h₂]
  exact card_image_univ_coe A (fun x => (g₁ x, g₂ x))

/-- **Discrete Loomis–Whitney in three coordinates** (Theorem 10.4.3): a finite set of points in
a product of three types has `|A|² ≤ |π₁₂ A| · |π₁₃ A| · |π₂₃ A|`.  Apply `shearer_triple` to a
uniform random point of `A`, using `entropy_le_logb_card` on each projection. -/
theorem card_sq_le_prod_card_image {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] (A : Finset (α × β × γ)) :
    A.card ^ 2 ≤ (A.image fun x => (x.1, x.2.1)).card * (A.image fun x => (x.1, x.2.2)).card
      * (A.image fun x => x.2).card := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp
  obtain ⟨a₀, ha₀⟩ := id hA
  have : Nonempty ↥A := ⟨⟨a₀, ha₀⟩⟩
  obtain ⟨X, hX⟩ : ∃ X : ↥A → ↥(A.image fun x => x.1), ∀ ω : ↥A, (X ω : α) = ω.1.1 :=
    ⟨fun ω => ⟨ω.1.1, Finset.mem_image_of_mem _ ω.2⟩, fun _ => rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ↥A → ↥(A.image fun x => x.2.1), ∀ ω : ↥A, (Y ω : β) = ω.1.2.1 :=
    ⟨fun ω => ⟨ω.1.2.1, Finset.mem_image_of_mem _ ω.2⟩, fun _ => rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ↥A → ↥(A.image fun x => x.2.2), ∀ ω : ↥A, (Z ω : γ) = ω.1.2.2 :=
    ⟨fun ω => ⟨ω.1.2.2, Finset.mem_image_of_mem _ ω.2⟩, fun _ => rfl⟩
  have hp : ∀ ω : ↥A, 0 ≤ uniformPMF (univ : Finset ↥A) ω := uniformPMF_nonneg _
  have hp1 : ∑ ω : ↥A, uniformPMF (univ : Finset ↥A) ω = 1 := sum_uniformPMF Finset.univ_nonempty
  have hinj : Function.Injective fun ω : ↥A => (X ω, Y ω, Z ω) := by
    intro ω ω' h
    simp only [Prod.mk.injEq] at h
    refine Subtype.ext ?_
    have e1 : (ω : α × β × γ).1 = (ω' : α × β × γ).1 := by rw [← hX, ← hX, h.1]
    have e2 : (ω : α × β × γ).2.1 = (ω' : α × β × γ).2.1 := by rw [← hY, ← hY, h.2.1]
    have e3 : (ω : α × β × γ).2.2 = (ω' : α × β × γ).2.2 := by rw [← hZ, ← hZ, h.2.2]
    exact Prod.ext e1 (Prod.ext e2 e3)
  have hmain : 2 * Real.logb 2 (A.card : ℝ)
      ≤ Real.logb 2 ((A.image fun x => (x.1, x.2.1)).card : ℝ)
        + Real.logb 2 ((A.image fun x => (x.1, x.2.2)).card : ℝ)
        + Real.logb 2 ((A.image fun x => x.2).card : ℝ) := by
    have hs := shearer_triple (uniformPMF (univ : Finset ↥A)) hp hp1 X Y Z
    rw [entropy_uniformPMF_univ_of_injective hinj, Fintype.card_coe] at hs
    refine hs.trans (add_le_add (add_le_add ?_ ?_) ?_)
    · refine (entropy_le_logb_card_image hp hp1 _).trans (le_of_eq ?_)
      rw [card_image_univ_pair A X Y (fun x => x.1) (fun x => x.2.1) hX hY]
    · refine (entropy_le_logb_card_image hp hp1 _).trans (le_of_eq ?_)
      rw [card_image_univ_pair A X Z (fun x => x.1) (fun x => x.2.2) hX hZ]
    · refine (entropy_le_logb_card_image hp hp1 _).trans (le_of_eq ?_)
      rw [card_image_univ_pair A Y Z (fun x => x.2.1) (fun x => x.2.2) hY hZ]
  have hApos : (0 : ℝ) < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hA
  have h1 : (0 : ℝ) < ((A.image fun x => (x.1, x.2.1)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (hA.image _)
  have h2 : (0 : ℝ) < ((A.image fun x => (x.1, x.2.2)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (hA.image _)
  have h3 : (0 : ℝ) < ((A.image fun x => x.2).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (hA.image _)
  have hfin : ((A.card : ℝ)) ^ 2
      ≤ ((A.image fun x => (x.1, x.2.1)).card : ℝ) * ((A.image fun x => (x.1, x.2.2)).card : ℝ)
        * ((A.image fun x => x.2).card : ℝ) := by
    rw [← Real.logb_le_logb (b := 2) one_lt_two (by positivity) (by positivity),
      Real.logb_pow, Real.logb_mul (by positivity) h3.ne', Real.logb_mul h1.ne' h2.ne']
    push_cast
    linarith
  exact_mod_cast hfin

/-- **Shearer's lemma for set families** (Corollary 10.4.7).  Let `ℱ` be a nonempty family of
subsets of a ground set `E`, and let `A j`, for `j` in a finite index set `J`, be sets such that
every element of `E` lies in at least `k` of them.  Then

    `|ℱ| ^ k ≤ ∏_{j ∈ J} |ℱ|_{A j}|`,

where the restriction `ℱ|_{A} = {F ∩ A : F ∈ ℱ}`.  This is `shearer` applied to the indicator
random variables `X i = [i ∈ F]` of a uniformly random `F ∈ ℱ`: the left side is
`k · H(X) = k · log₂ |ℱ|` and each term on the right is bounded by `log₂ |ℱ|_{A j}|` using
`entropy_le_logb_card`. -/
theorem card_pow_le_prod_card_image_inter {ι κ : Type*} [DecidableEq ι]
    (ℱ : Finset (Finset ι)) (hℱ : ℱ.Nonempty) (E : Finset ι) (hE : ∀ F ∈ ℱ, F ⊆ E)
    (J : Finset κ) (A : κ → Finset ι) (k : ℕ)
    (hk : ∀ i ∈ E, k ≤ (J.filter fun j => i ∈ A j).card) :
    ℱ.card ^ k ≤ ∏ j ∈ J, (ℱ.image fun F => F ∩ A j).card := by
  obtain ⟨F₀, hF₀⟩ := id hℱ
  have hne : Nonempty ↥ℱ := ⟨⟨F₀, hF₀⟩⟩
  obtain ⟨e⟩ : Nonempty (Fin J.card ≃ ↥J) := ⟨J.equivFin.symm⟩
  obtain ⟨B, hB⟩ : ∃ B : Fin J.card → Finset ↥E,
      ∀ (m : Fin J.card) (i : ↥E), i ∈ B m ↔ i.1 ∈ A (e m).1 :=
    ⟨fun m => univ.filter fun i : ↥E => i.1 ∈ A (e m).1, by intro m i; simp⟩
  have hp : ∀ ω : ↥ℱ, 0 ≤ uniformPMF (univ : Finset ↥ℱ) ω := uniformPMF_nonneg _
  have hp1 : ∑ ω : ↥ℱ, uniformPMF (univ : Finset ↥ℱ) ω = 1 := sum_uniformPMF Finset.univ_nonempty
  have hk' : ∀ i : ↥E, k ≤ ((univ : Finset (Fin J.card)).filter fun m => i ∈ B m).card := by
    intro i
    refine (hk i.1 i.2).trans (le_of_eq ?_)
    rw [Finset.card_filter, Finset.card_filter,
      ← Finset.sum_coe_sort J fun j => if i.1 ∈ A j then 1 else 0]
    exact (Fintype.sum_equiv e (fun m => if i ∈ B m then (1 : ℕ) else 0)
      (fun j : ↥J => if i.1 ∈ A j.1 then (1 : ℕ) else 0)
      fun m => if_congr (hB m i) rfl rfl).symm
  have hinj : Function.Injective fun (ω : ↥ℱ) (i : ↥E) => decide (i.1 ∈ ω.1) := by
    intro ω ω' h
    refine Subtype.ext (Finset.ext fun x => ?_)
    by_cases hx : x ∈ E
    · simpa using congrFun h ⟨x, hx⟩
    · exact ⟨fun hm => absurd (hE _ ω.2 hm) hx, fun hm => absurd (hE _ ω'.2 hm) hx⟩
  have hL : entropy (uniformPMF (univ : Finset ↥ℱ))
      (fun (ω : ↥ℱ) (i : ↥E) => decide (i.1 ∈ ω.1)) = Real.logb 2 (ℱ.card : ℝ) := by
    rw [entropy_uniformPMF_univ_of_injective hinj, Fintype.card_coe]
  have hterm : ∀ m : Fin J.card,
      entropy (uniformPMF (univ : Finset ↥ℱ))
          (fun (ω : ↥ℱ) (i : ↥(B m)) => decide (i.1.1 ∈ ω.1))
        ≤ Real.logb 2 (((ℱ.image fun F => F ∩ A (e m).1).card : ℝ)) := by
    intro m
    refine (entropy_le_logb_card_image hp hp1 _).trans ?_
    have hsub : ((univ : Finset ↥ℱ).image
          fun (ω : ↥ℱ) (i : ↥(B m)) => decide (i.1.1 ∈ ω.1))
        ⊆ (ℱ.image fun F => F ∩ A (e m).1).image
          fun G => fun (i : ↥(B m)) => decide (i.1.1 ∈ G) := by
      intro s hs
      obtain ⟨ω, -, rfl⟩ := Finset.mem_image.mp hs
      refine Finset.mem_image.mpr ⟨ω.1 ∩ A (e m).1,
        Finset.mem_image_of_mem _ ω.2, funext fun i => ?_⟩
      have hi : i.1.1 ∈ A (e m).1 := (hB m i.1).mp i.2
      simp [Finset.mem_inter, hi]
    have h0 : (0 : ℝ) < (((univ : Finset ↥ℱ).image
        fun (ω : ↥ℱ) (i : ↥(B m)) => decide (i.1.1 ∈ ω.1)).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr (Finset.univ_nonempty.image _)
    have h1 : (0 : ℝ) < (((ℱ.image fun F => F ∩ A (e m).1).card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr (hℱ.image _)
    refine (Real.logb_le_logb one_lt_two h0 h1).mpr ?_
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
  have hs := shearer (uniformPMF (univ : Finset ↥ℱ)) hp hp1
    (fun (i : ↥E) (ω : ↥ℱ) => decide (i.1 ∈ ω.1)) B k hk'
  have hmain : (k : ℝ) * Real.logb 2 (ℱ.card : ℝ)
      ≤ ∑ m : Fin J.card, Real.logb 2 (((ℱ.image fun F => F ∩ A (e m).1).card : ℝ)) := by
    rw [← hL]
    exact hs.trans (Finset.sum_le_sum fun m _ => hterm m)
  have hsum : ∑ m : Fin J.card, Real.logb 2 (((ℱ.image fun F => F ∩ A (e m).1).card : ℝ))
      = ∑ j ∈ J, Real.logb 2 (((ℱ.image fun F => F ∩ A j).card : ℝ)) := by
    rw [← Finset.sum_coe_sort J fun j => Real.logb 2 (((ℱ.image fun F => F ∩ A j).card : ℝ))]
    exact Fintype.sum_equiv e _ _ fun m => rfl
  have hpos : ∀ j : κ, (0 : ℝ) < ((ℱ.image fun F => F ∩ A j).card : ℝ) := fun j => by
    exact_mod_cast Finset.card_pos.mpr (hℱ.image _)
  have hcpos : (0 : ℝ) < (ℱ.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hℱ
  have hfin : ((ℱ.card : ℝ)) ^ k ≤ ∏ j ∈ J, ((ℱ.image fun F => F ∩ A j).card : ℝ) := by
    refine (Real.logb_le_logb one_lt_two (by positivity)
      (Finset.prod_pos fun j _ => hpos j)).mp ?_
    rw [Real.logb_pow, Real.logb_prod J _ fun j _ => (hpos j).ne', ← hsum]
    exact hmain
  exact_mod_cast hfin

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
  rcases 𝒢.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨G₀, hG₀⟩ := hne
  have hne' : 𝒢.Nonempty := ⟨G₀, hG₀⟩
  have hn : 3 ≤ n := by
    obtain ⟨a, b, c, hab, hac, hbc, -⟩ := hinter G₀ hG₀ G₀ hG₀
    have h3 : ({a, b, c} : Finset (Fin n)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
        Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
    calc (3 : ℕ) = ({a, b, c} : Finset (Fin n)).card := h3.symm
      _ ≤ Fintype.card (Fin n) := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  have hz : (⟨0, by omega⟩ : Fin n) ∈ (univ : Finset (Fin n)) := Finset.mem_univ _
  have hemp : (∅ : Finset (Fin n)) ≠ univ := fun h => by simp [← h] at hz
  -- `E` is the edge set of `Kₙ`; for a vertex set `S` the cut `A S` collects the edges with both
  -- endpoints in `S` and those with both endpoints in `Sᶜ`; `J` indexes the proper nonempty cuts.
  obtain ⟨E, hEdef⟩ : ∃ E : Finset (Sym2 (Fin n)),
      E = univ.filter (fun e => ¬ e.IsDiag) := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : Finset (Fin n) → Finset (Sym2 (Fin n)),
      ∀ S, A S = E.filter (fun e => e ∈ S.sym2 ∨ e ∈ Sᶜ.sym2) := ⟨_, fun _ => rfl⟩
  obtain ⟨J, hJdef⟩ : ∃ J : Finset (Finset (Fin n)),
      J = (univ : Finset (Finset (Fin n))) \ {∅, univ} := ⟨_, rfl⟩
  have hmemE : ∀ e : Sym2 (Fin n), e ∈ E ↔ ¬ e.IsDiag := by
    intro e; rw [hEdef]; simp
  have hmemA : ∀ (S : Finset (Fin n)) (u v : Fin n),
      s(u, v) ∈ A S ↔ (u ≠ v ∧ ((u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∉ S))) := by
    intro S u v
    rw [hAdef, Finset.mem_filter, hmemE]
    simp
  have hAE : ∀ S, A S ⊆ E := by
    intro S; rw [hAdef]; exact Finset.filter_subset _ _
  have hEcard : E.card = n.choose 2 := by
    rw [hEdef, ← Fintype.card_subtype, Sym2.card_subtype_not_diag, Fintype.card_fin]
  -- Each edge lies in `2 ^ (n - 1) - 2` of the cut sets `A S`, `S ∈ J`.
  have hcount : ∀ e ∈ E, (J.filter fun S => e ∈ A S).card = 2 ^ (n - 1) - 2 := by
    intro e
    induction e using Sym2.ind with
    | _ u v =>
      intro he
      have huv : u ≠ v := by simpa [hmemE] using he
      have hfil : (J.filter fun S => s(u, v) ∈ A S)
          = J.filter (fun S => (u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∉ S)) := by
        apply Finset.filter_congr
        intro S _
        simp [hmemA S u v, huv]
      have hout : (univ.filter fun S : Finset (Fin n) => u ∉ S ∧ v ∉ S).card = 2 ^ (n - 2) := by
        have h : (univ.filter fun S : Finset (Fin n) => u ∉ S ∧ v ∉ S)
            = (({u, v} : Finset (Fin n))ᶜ).powerset := by
          ext S
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset,
            Finset.subset_iff, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨h1, h2⟩ x hx
            rintro (rfl | rfl)
            · exact h1 hx
            · exact h2 hx
          · intro h
            exact ⟨fun hu => h hu (Or.inl rfl), fun hv => h hv (Or.inr rfl)⟩
        rw [h, Finset.card_powerset, Finset.card_compl, Fintype.card_fin,
          Finset.card_insert_of_notMem (by simpa using huv), Finset.card_singleton]
      have hin : (univ.filter fun S : Finset (Fin n) => u ∈ S ∧ v ∈ S).card
          = (univ.filter fun S : Finset (Fin n) => u ∉ S ∧ v ∉ S).card := by
        refine Finset.card_nbij' (fun S => Sᶜ) (fun S => Sᶜ) ?_ ?_ ?_ ?_ <;>
          intro S hS <;> simp_all
      have hall : (univ.filter fun S : Finset (Fin n) => (u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∉ S)).card
          = 2 ^ (n - 1) := by
        have hd : Disjoint (univ.filter fun S : Finset (Fin n) => u ∈ S ∧ v ∈ S)
            (univ.filter fun S : Finset (Fin n) => u ∉ S ∧ v ∉ S) := by
          rw [Finset.disjoint_left]
          intro S hS hS'
          simp only [Finset.mem_filter] at hS hS'
          exact hS'.2.1 hS.2.1
        rw [Finset.filter_or, Finset.card_union_of_disjoint hd, hin, hout]
        have hn1 : n - 1 = (n - 2) + 1 := by omega
        rw [hn1, pow_succ]
        ring
      have hpair : ({∅, univ} : Finset (Finset (Fin n))).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simpa using hemp), Finset.card_singleton]
      have hsub : ({∅, univ} : Finset (Finset (Fin n)))
          ⊆ univ.filter (fun S : Finset (Fin n) => (u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∉ S)) := by
        intro S hS
        simp only [Finset.mem_insert, Finset.mem_singleton] at hS
        rcases hS with rfl | rfl <;> simp
      have hsplit : ((univ \ ({∅, univ} : Finset (Finset (Fin n)))).filter
            (fun S : Finset (Fin n) => (u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∉ S)))
          = (univ.filter (fun S : Finset (Fin n) => (u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∉ S)))
            \ ({∅, univ} : Finset (Finset (Fin n))) := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
        tauto
      rw [hfil, hJdef, hsplit, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hall, hpair]
  -- Double counting: the cut sets have total size `|E| * k`.
  have hsum : ∑ S ∈ J, (A S).card = E.card * (2 ^ (n - 1) - 2) := by
    have h1 : ∀ S ∈ J, (A S).card = ∑ e ∈ E, if e ∈ A S then 1 else 0 := by
      intro S _
      rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hAE S)]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    have h2 : ∀ e ∈ E, (∑ S ∈ J, if e ∈ A S then 1 else 0) = 2 ^ (n - 1) - 2 := by
      intro e he
      rw [← Finset.card_filter]
      exact hcount e he
    rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul]
  have hJcard : J.card = 2 ^ n - 2 := by
    rw [hJdef, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_insert_of_notMem (by simpa using hemp),
      Finset.card_singleton, Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
  -- Pigeonhole: two of any three vertices lie on the same side of the cut.
  have hpigeon : ∀ (S : Finset (Fin n)) (a b c : Fin n), a ≠ b → a ≠ c → b ≠ c →
      ∃ e ∈ triangleEdges a b c, e ∈ A S := by
    intro S a b c hab hac hbc
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> by_cases hc : c ∈ S
    · exact ⟨s(a, b), by simp [triangleEdges], (hmemA S a b).mpr ⟨hab, Or.inl ⟨ha, hb⟩⟩⟩
    · exact ⟨s(a, b), by simp [triangleEdges], (hmemA S a b).mpr ⟨hab, Or.inl ⟨ha, hb⟩⟩⟩
    · exact ⟨s(a, c), by simp [triangleEdges], (hmemA S a c).mpr ⟨hac, Or.inl ⟨ha, hc⟩⟩⟩
    · exact ⟨s(b, c), by simp [triangleEdges], (hmemA S b c).mpr ⟨hbc, Or.inr ⟨hb, hc⟩⟩⟩
    · exact ⟨s(b, c), by simp [triangleEdges], (hmemA S b c).mpr ⟨hbc, Or.inl ⟨hb, hc⟩⟩⟩
    · exact ⟨s(a, c), by simp [triangleEdges], (hmemA S a c).mpr ⟨hac, Or.inr ⟨ha, hc⟩⟩⟩
    · exact ⟨s(a, b), by simp [triangleEdges], (hmemA S a b).mpr ⟨hab, Or.inr ⟨ha, hb⟩⟩⟩
    · exact ⟨s(a, b), by simp [triangleEdges], (hmemA S a b).mpr ⟨hab, Or.inr ⟨ha, hb⟩⟩⟩
  -- Each restriction is an intersecting family of subsets of `A S`.
  have hrestr : ∀ S : Finset (Fin n),
      2 * (𝒢.image fun G => G ∩ A S).card ≤ 2 ^ (A S).card := by
    intro S
    set F := 𝒢.image fun G => G ∩ A S
    have hsub : ∀ X ∈ F, X ⊆ A S := by
      intro X hX
      obtain ⟨G, -, rfl⟩ := Finset.mem_image.mp hX
      exact Finset.inter_subset_right
    have hint : ∀ X ∈ F, ∀ Y ∈ F, (X ∩ Y).Nonempty := by
      intro X hX Y hY
      obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hX
      obtain ⟨H, hH, rfl⟩ := Finset.mem_image.mp hY
      obtain ⟨a, b, c, hab, hac, hbc, htri⟩ := hinter G hG H hH
      obtain ⟨e, hetri, heA⟩ := hpigeon S a b c hab hac hbc
      have heGH : e ∈ G ∩ H := htri hetri
      exact ⟨e, by
        simp only [Finset.mem_inter] at heGH ⊢
        exact ⟨⟨heGH.1, heA⟩, ⟨heGH.2, heA⟩⟩⟩
    have hinj : Set.InjOn (fun X => A S \ X) (F : Set (Finset (Sym2 (Fin n)))) := by
      intro X hX Y hY h
      simpa [Finset.sdiff_sdiff_eq_self (hsub X hX), Finset.sdiff_sdiff_eq_self (hsub Y hY)] using
        congrArg (fun Z => A S \ Z) h
    have hcard : (F.image fun X => A S \ X).card = F.card := Finset.card_image_of_injOn hinj
    have hdisj : Disjoint F (F.image fun X => A S \ X) := by
      rw [Finset.disjoint_right]
      rintro Z hZ hZF
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hZ
      obtain ⟨x, hx⟩ := hint _ hZF _ hY
      simp only [Finset.mem_inter, Finset.mem_sdiff] at hx
      exact hx.1.2 hx.2
    have hcup : (F ∪ F.image fun X => A S \ X) ⊆ (A S).powerset := by
      intro Z hZ
      rcases Finset.mem_union.mp hZ with h | h
      · exact Finset.mem_powerset.mpr (hsub Z h)
      · obtain ⟨Y, -, rfl⟩ := Finset.mem_image.mp h
        exact Finset.mem_powerset.mpr Finset.sdiff_subset
    calc 2 * F.card = F.card + (F.image fun X => A S \ X).card := by rw [hcard]; ring
      _ = (F ∪ F.image fun X => A S \ X).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (A S).powerset.card := Finset.card_le_card hcup
      _ = 2 ^ (A S).card := Finset.card_powerset _
  -- Shearer for set families.  `hdiag` enters here: it is what makes every member of `𝒢` a subset
  -- of `E`, and only the elements of `E` are covered by the cuts.
  have hcor := card_pow_le_prod_card_image_inter 𝒢 hne' E
    (fun G hG e he => (hmemE e).mpr (hdiag G hG e he)) J A (2 ^ (n - 1) - 2)
    (fun i hi => (hcount i hi).ge)
  have hprod : 2 ^ J.card * 𝒢.card ^ (2 ^ (n - 1) - 2) ≤ 2 ^ (∑ S ∈ J, (A S).card) := by
    calc 2 ^ J.card * 𝒢.card ^ (2 ^ (n - 1) - 2)
        ≤ 2 ^ J.card * ∏ S ∈ J, (𝒢.image fun G => G ∩ A S).card :=
          Nat.mul_le_mul_left _ hcor
      _ = ∏ S ∈ J, 2 * (𝒢.image fun G => G ∩ A S).card := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ ∏ S ∈ J, 2 ^ (A S).card := Finset.prod_le_prod' fun S _ => hrestr S
      _ = 2 ^ (∑ S ∈ J, (A S).card) := Finset.prod_pow_eq_pow_sum _ _ _
  -- If `2 ^ (binom n 2 - 2) ≤ |𝒢|` the two sides of `hprod` read
  -- `2 ^ (2 ^ n - 2 + (binom n 2 - 2) * k) ≤ 2 ^ (binom n 2 * k)` with `k = 2 ^ (n - 1) - 2`,
  -- forcing `2 ^ n - 2 ≤ 2 * k = 2 ^ n - 4`.
  by_contra hcon
  have hge : 2 ^ (n.choose 2 - 2) ≤ 𝒢.card := Nat.le_of_not_lt hcon
  have hC : 3 ≤ n.choose 2 := by
    have := Nat.choose_le_choose 2 hn
    simpa using this
  have hkey : (2 : ℕ) ^ (J.card + (n.choose 2 - 2) * (2 ^ (n - 1) - 2))
      ≤ 2 ^ (n.choose 2 * (2 ^ (n - 1) - 2)) := by
    calc (2 : ℕ) ^ (J.card + (n.choose 2 - 2) * (2 ^ (n - 1) - 2))
        = 2 ^ J.card * (2 ^ (n.choose 2 - 2)) ^ (2 ^ (n - 1) - 2) := by
          rw [pow_add, pow_mul]
      _ ≤ 2 ^ J.card * 𝒢.card ^ (2 ^ (n - 1) - 2) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hge _)
      _ ≤ 2 ^ (∑ S ∈ J, (A S).card) := hprod
      _ = 2 ^ (n.choose 2 * (2 ^ (n - 1) - 2)) := by rw [hsum, hEcard]
  have hle := (Nat.pow_le_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp hkey
  rw [hJcard, Nat.sub_mul] at hle
  have h2k : 2 * (2 ^ (n - 1) - 2) ≤ n.choose 2 * (2 ^ (n - 1) - 2) :=
    Nat.mul_le_mul_right _ (by omega)
  obtain ⟨m, hm⟩ : ∃ m, n.choose 2 * (2 ^ (n - 1) - 2) = m := ⟨_, rfl⟩
  rw [hm] at hle h2k
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]; ring
  have hpow4 : (4 : ℕ) ≤ 2 ^ (n - 1) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-! ### 10.2 The Brégman–Minc inequality -/

section Bregman

/-- The permutations counted by the permanent of a `0/1` matrix `A`: those `π` with
`A i (π i) = 1` for every `i`, i.e. the perfect matchings of the associated bipartite graph. -/
noncomputable def permSupport {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Finset (Equiv.Perm (Fin n)) :=
  univ.filter fun π => ∀ i, A i (π i) = 1

/-- Radhakrishnan's counter `Nᵢ`.  Reveal the entries `(j, π j)` of the matching `π` in the order
given by `τ` — row `j` before row `k` when `τ j < τ k`.  When row `i` is revealed, the entries of
row `i` still available are the ones in row `i` whose column `π j` has not been used by an
earlier row, and `availCount A π τ i` counts them.  Row `i` itself is always available, so the
count is at least `1`, and it is at most the number `dᵢ` of ones in row `i`. -/
noncomputable def availCount {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (π τ : Equiv.Perm (Fin n))
    (i : Fin n) : ℕ :=
  (univ.filter fun j => A i (π j) = 1 ∧ τ i ≤ τ j).card

/-- The part of the matching `π` that has been revealed strictly before row `i`, when the rows
are revealed in the order given by `τ`: the entry of row `j` if `τ j < τ i`, and `none`
otherwise. -/
def revealedBefore {n : ℕ} (τ : Equiv.Perm (Fin n)) (i : Fin n) (π : Equiv.Perm (Fin n)) :
    Fin n → Option (Fin n) :=
  fun j => if τ j < τ i then some (π j) else none

/-- For a `0/1` matrix the permanent counts the permutations lying in the support: each term of
`∑ σ, ∏ i, A (σ i) i` is `1` when `σ` is a matching and `0` otherwise. -/
theorem permanent_eq_card_permSupport {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) : A.permanent = ((permSupport A).card : ℝ) := by
  have h1 : A.permanent = ∑ π : Equiv.Perm (Fin n), ∏ i, A i (π i) := by
    rw [← Matrix.permanent_transpose A]
    simp [Matrix.permanent]
  rw [h1, permSupport, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun π _ => ?_
  by_cases h : ∀ i, A i (π i) = 1
  · simp [h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    rw [if_neg h, Finset.prod_eq_zero (mem_univ i) ((hA i (π i)).resolve_right hi)]

/-- The entropy of a uniform random element of a nonempty finset `P` is `log₂ |P|`.  This is the
equality case of `entropy_le_logb_card`, and it is how every application in this chapter turns a
count into an entropy. -/
theorem entropy_uniformPMF [Fintype Ω] [DecidableEq Ω] {P : Finset Ω} (hP : P.Nonempty) :
    entropy (uniformPMF P) id = Real.logb 2 (P.card : ℝ) := by
  have hcard : (P.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hP.card_ne_zero
  have hprob : ∀ s : Ω, probOf (uniformPMF P) id s = uniformPMF P s := by
    intro s
    unfold probOf
    simp [Finset.filter_eq']
  have hterm : ∀ s : Ω, -uniformPMF P s * Real.logb 2 (uniformPMF P s)
      = if s ∈ P then ((P.card : ℝ))⁻¹ * Real.logb 2 (P.card : ℝ) else 0 := by
    intro s
    unfold uniformPMF
    split
    · rw [Real.logb_inv]; ring
    · simp
  rw [entropy]
  simp only [hprob, hterm, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]

/-- Row `i` of a `0/1` matrix has exactly `dᵢ` ones, in whatever order a permutation `π` lists
the columns. -/
theorem card_filter_row_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) (d : Fin n → ℕ) (hd : ∀ i, ∑ j, A i j = (d i : ℝ))
    (i : Fin n) (π : Equiv.Perm (Fin n)) :
    (univ.filter fun j => A i (π j) = 1).card = d i := by
  have h1 : (univ.filter fun j => A i (π j) = 1).card = (univ.filter fun j => A i j = 1).card :=
    Finset.card_equiv π (by intro j; simp)
  have h2 : ((univ.filter fun j => A i j = 1).card : ℝ) = (d i : ℝ) := by
    rw [Finset.card_filter]
    push_cast
    rw [← hd i]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases hA i j with h | h <;> simp [h]
  rw [h1]
  exact_mod_cast h2

/-- `log₂ (k!)` is the sum of `log₂ m` over `1 ≤ m ≤ k`. -/
theorem sum_logb_Icc_eq {k : ℕ} :
    ∑ m ∈ Finset.Icc 1 k, Real.logb 2 (m : ℝ) = Real.logb 2 (Nat.factorial k : ℝ) := by
  have hIcc : Finset.Icc 1 k = Finset.Ico 1 (k + 1) := by ext m; simp
  rw [hIcc, ← Finset.prod_Ico_id_eq_factorial k, Nat.cast_prod, Real.logb_prod]
  intro m hm
  have : 1 ≤ m := (Finset.mem_Ico.mp hm).1
  positivity

/-- **The combinatorial heart of Radhakrishnan's proof**, the step the notes leave as "Why?" on
p. 180.  Fix a finset `D` of `[n]` and an element `i ∈ D`.  For a uniform random permutation `τ`
the rank of `i` inside `D`, counted from the top — the number of `j ∈ D` with `τ i ≤ τ j` — is
uniform on `{1, …, |D|}`: each of those `|D|` values is taken by exactly `n! / |D|` of the `n!`
permutations.

In the Brégman–Minc proof `D` is the set of `j` with `A i (π j) = 1`, which has `dᵢ` elements and
contains `i`, and the rank is `availCount A π τ i`; the conclusion is that `Nᵢ` is uniform on
`[dᵢ]` for a fixed matching `π`.

This is stated multiplicatively to stay in `ℕ`.  The proof is a double count: for a fixed `τ`
the rank is injective on `D`, so exactly one `j ∈ D` has rank `m`; and composing `τ` with the
transposition of `i` and `j` exchanges the rank of `i` with the rank of `j`, so all `j ∈ D` give
the same fibre size. -/
theorem card_filter_rank_mul_card_eq_factorial {n : ℕ} (D : Finset (Fin n)) (i : Fin n)
    (hi : i ∈ D) {m : ℕ} (hm : m ∈ Finset.Icc 1 D.card) :
    (univ.filter fun τ : Equiv.Perm (Fin n) =>
        (D.filter fun j => τ i ≤ τ j).card = m).card * D.card = Nat.factorial n := by
  obtain ⟨rank, hrank⟩ : ∃ r : Equiv.Perm (Fin n) → Fin n → ℕ,
      ∀ τ j, r τ j = (D.filter fun l => τ j ≤ τ l).card := ⟨_, fun _ _ => rfl⟩
  have hmono : ∀ (τ : Equiv.Perm (Fin n)) (j j' : Fin n), j ∈ D → τ j < τ j' →
      rank τ j' < rank τ j := by
    intro τ j j' hjD hlt
    rw [hrank, hrank]
    refine Finset.card_lt_card ⟨fun l hl => ?_, fun hsub => ?_⟩
    · rw [Finset.mem_filter] at hl ⊢
      exact ⟨hl.1, le_trans hlt.le hl.2⟩
    · have hj : j ∈ D.filter fun l => τ j ≤ τ l := Finset.mem_filter.mpr ⟨hjD, le_rfl⟩
      have h2 := hsub hj
      rw [Finset.mem_filter] at h2
      exact absurd h2.2 (not_le.mpr hlt)
  have hinj : ∀ (τ : Equiv.Perm (Fin n)), ∀ j ∈ D, ∀ j' ∈ D, rank τ j = rank τ j' → j = j' := by
    intro τ j hjD j' hj'D heq
    rcases lt_trichotomy (τ j) (τ j') with h | h | h
    · have := hmono τ j j' hjD h
      omega
    · exact τ.injective h
    · have := hmono τ j' j hj'D h
      omega
  have hmemIcc : ∀ (τ : Equiv.Perm (Fin n)), ∀ j ∈ D, rank τ j ∈ Finset.Icc 1 D.card := by
    intro τ j hjD
    rw [Finset.mem_Icc, hrank]
    exact ⟨Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨hjD, le_rfl⟩⟩,
      Finset.card_le_card (Finset.filter_subset _ _)⟩
  have himg : ∀ τ : Equiv.Perm (Fin n), D.image (rank τ) = Finset.Icc 1 D.card := by
    intro τ
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · obtain ⟨j, hjD, rfl⟩ := Finset.mem_image.mp hx
      exact hmemIcc τ j hjD
    · rw [Finset.card_image_of_injOn (fun j hj j' hj' h => hinj τ j hj j' hj' h), Nat.card_Icc]
      omega
  have hone : ∀ τ : Equiv.Perm (Fin n), (D.filter fun j => rank τ j = m).card = 1 := by
    intro τ
    have hmimg : m ∈ D.image (rank τ) := by rw [himg τ]; exact hm
    obtain ⟨j, hjD, hj⟩ := Finset.mem_image.mp hmimg
    rw [Finset.card_eq_one]
    refine ⟨j, Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hjD, hj⟩, ?_⟩⟩
    intro x hx
    rw [Finset.mem_filter] at hx
    exact hinj τ x hx.1 j hjD (by rw [hx.2, hj])
  have hswap : ∀ j ∈ D, (univ.filter fun τ : Equiv.Perm (Fin n) => rank τ j = m).card
      = (univ.filter fun τ : Equiv.Perm (Fin n) => rank τ i = m).card := by
    intro j hjD
    have hcD : ∀ l, l ∈ D ↔ (Equiv.swap i j) l ∈ D := by
      intro l
      rcases eq_or_ne l i with rfl | hli
      · simp [Equiv.swap_apply_left, hi, hjD]
      · rcases eq_or_ne l j with rfl | hlj
        · simp [Equiv.swap_apply_right, hi, hjD]
        · rw [Equiv.swap_apply_of_ne_of_ne hli hlj]
    have hkey : ∀ τ : Equiv.Perm (Fin n), rank (τ * Equiv.swap i j) i = rank τ j := by
      intro τ
      rw [hrank, hrank]
      refine Finset.card_equiv (Equiv.swap i j) fun l => ?_
      rw [Finset.mem_filter, Finset.mem_filter, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
        Equiv.swap_apply_left]
      exact and_congr (hcD l) Iff.rfl
    refine Finset.card_equiv (Equiv.mulRight (Equiv.swap i j)) fun τ => ?_
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, Equiv.coe_mulRight, hkey τ]
  have hcount : ∑ τ : Equiv.Perm (Fin n), (D.filter fun j => rank τ j = m).card
      = Nat.factorial n := by
    rw [Finset.sum_congr rfl (fun τ _ => hone τ)]
    simp [Fintype.card_perm]
  have hswapsum : ∑ τ : Equiv.Perm (Fin n), (D.filter fun j => rank τ j = m).card
      = D.card * (univ.filter fun τ : Equiv.Perm (Fin n) => rank τ i = m).card := by
    calc ∑ τ : Equiv.Perm (Fin n), (D.filter fun j => rank τ j = m).card
        = ∑ τ : Equiv.Perm (Fin n), ∑ j ∈ D, (if rank τ j = m then 1 else 0) := by
          simp only [Finset.card_filter]
      _ = ∑ j ∈ D, ∑ τ : Equiv.Perm (Fin n), (if rank τ j = m then 1 else 0) := Finset.sum_comm
      _ = ∑ j ∈ D, (univ.filter fun τ : Equiv.Perm (Fin n) => rank τ j = m).card := by
          simp only [Finset.card_filter]
      _ = ∑ j ∈ D, (univ.filter fun τ : Equiv.Perm (Fin n) => rank τ i = m).card :=
          Finset.sum_congr rfl hswap
      _ = D.card * (univ.filter fun τ : Equiv.Perm (Fin n) => rank τ i = m).card := by
          rw [Finset.sum_const, smul_eq_mul]
  simp only [← hrank]
  rw [mul_comm, ← hswapsum]
  exact hcount

/-- Averaging `log₂ Nᵢ` over the reveal order: for a fixed matching `π` in the support,
`∑_τ log₂ (availCount A π τ i) = (n! / dᵢ) · log₂ (dᵢ!)`, i.e. `𝔼_τ log₂ Nᵢ = log₂(dᵢ!)/dᵢ`.
This is `card_filter_rank_mul_card_eq_factorial` summed against `log₂`. -/
theorem sum_logb_availCount {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) (d : Fin n → ℕ) (hd : ∀ i, ∑ j, A i j = (d i : ℝ))
    {π : Equiv.Perm (Fin n)} (hπ : π ∈ permSupport A) (i : Fin n) :
    ∑ τ : Equiv.Perm (Fin n), Real.logb 2 (availCount A π τ i)
      = (Nat.factorial n : ℝ) / (d i : ℝ) * Real.logb 2 (Nat.factorial (d i) : ℝ) := by
  have hπ' : ∀ k, A k (π k) = 1 := (Finset.mem_filter.mp hπ).2
  have hDcard : (univ.filter fun j => A i (π j) = 1).card = d i :=
    card_filter_row_eq A hA d hd i π
  have hiD : i ∈ (univ.filter fun j => A i (π j) = 1) := by simp [hπ' i]
  have hav : ∀ τ : Equiv.Perm (Fin n), availCount A π τ i
      = ((univ.filter fun j => A i (π j) = 1).filter fun j => τ i ≤ τ j).card := by
    intro τ
    rw [availCount, Finset.filter_filter]
  have hmem : ∀ τ : Equiv.Perm (Fin n), availCount A π τ i ∈ Finset.Icc 1 (d i) := by
    intro τ
    rw [Finset.mem_Icc, hav τ]
    refine ⟨Finset.card_pos.mpr ⟨i, by simp [hπ' i]⟩, ?_⟩
    rw [← hDcard]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  rw [← Finset.sum_fiberwise_of_maps_to (fun τ _ => hmem τ)
    (fun τ => Real.logb 2 (availCount A π τ i))]
  have key : ∀ m ∈ Finset.Icc 1 (d i),
      ∑ τ ∈ univ.filter (fun τ : Equiv.Perm (Fin n) => availCount A π τ i = m),
          Real.logb 2 (availCount A π τ i)
        = (Nat.factorial n : ℝ) / (d i : ℝ) * Real.logb 2 (m : ℝ) := by
    intro m hm
    rw [Finset.sum_congr rfl (fun τ hτ => by rw [(Finset.mem_filter.mp hτ).2]),
      Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hcnt := card_filter_rank_mul_card_eq_factorial
      (univ.filter fun j => A i (π j) = 1) i hiD (m := m) (by rwa [hDcard])
    have hd0 : (d i : ℝ) ≠ 0 := by
      have : 1 ≤ d i := (Finset.mem_Icc.mp hm).1.trans (Finset.mem_Icc.mp hm).2
      positivity
    rw [eq_div_iff hd0]
    simp only [hav] at *
    rw [hDcard] at hcnt
    exact_mod_cast hcnt
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, sum_logb_Icc_eq]

/-- **The chain rule along a reveal order.**  Reveal the values of a random permutation `π` in
the order given by `τ` — row `j` before row `k` when `τ j < τ k`.  Then the entropy of `π` is the
sum, over the rows `i`, of the entropy of `π i` conditioned on what was revealed before row `i`.

This is Lemma 10.1.7 (`condEntropy_eq_sub`) telescoped along the order `τ`: writing `Pₖ` for the
first `k` entries revealed, `H(P_{k+1}) = H(Pₖ) + H(π_{τ⁻¹ k} ∣ Pₖ)`, with `P₀` constant and
`Pₙ` determining `π`. -/
theorem entropy_eq_sum_condEntropy_revealedBefore {n : ℕ} (p : Equiv.Perm (Fin n) → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (τ : Equiv.Perm (Fin n)) :
    entropy p id = ∑ i, condEntropy p (fun π => π i) (revealedBefore τ i) := by
  sorry

/-- **The greedy bound on one conditional entropy** (the "`≤ log₂ Nᵢ`" step of Theorem 10.2.1).
Condition a uniform matching `π` of the `0/1` matrix `A` on the entries revealed before row `i`.
The count `availCount A π τ i` is determined by those entries — it is `dᵢ` minus the number of
ones of row `i` in a column already used — and `π i` must be one of the ones of row `i` in a
column not yet used, so it takes at most `availCount A π τ i` values.  The uniform bound
`entropy_le_logb_card`, applied inside each fibre of the conditioning variable and averaged,
therefore bounds the conditional entropy by the expectation of `log₂ Nᵢ`. -/
theorem condEntropy_le_expected_logb_availCount {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) (hP : (permSupport A).Nonempty)
    (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    condEntropy (uniformPMF (permSupport A)) (fun π => π i) (revealedBefore τ i)
      ≤ ((permSupport A).card : ℝ)⁻¹ *
        ∑ π ∈ permSupport A, Real.logb 2 (availCount A π τ i) := by
  sorry

/-- **Radhakrishnan's entropy bound, for one reveal order** (the displayed inequality on p. 180
of the notes).  Let `π` be uniform on the matchings of `A`, and fix an order `τ` in which to
reveal the entries `(j, π j)` — row `j` before row `k` when `τ j < τ k`.  The chain rule
`condEntropy_eq_sub`, applied along that order, gives

`H(π) = ∑ᵢ H(πᵢ ∣ πⱼ : j revealed before i)`,

and conditioned on the entries already revealed, `πᵢ` is confined to the `availCount A π τ i`
columns of row `i` that are still free, so `entropy_le_logb_card` applied inside each fibre
bounds the `i`-th term by the average of `log₂ Nᵢ`.  The right-hand side below is that average
over `π ∈ permSupport A`.

The inequality holds for each fixed `τ` separately; what Radhakrishnan's proof gains by taking
`τ` random is that averaging the right-hand side over `τ` makes it computable, which is
`card_filter_rank_mul_card_eq_factorial`. -/
theorem entropy_permSupport_le_expected_logb_availCount {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) (hP : (permSupport A).Nonempty)
    (τ : Equiv.Perm (Fin n)) :
    entropy (uniformPMF (permSupport A)) id ≤
      ((permSupport A).card : ℝ)⁻¹ *
        ∑ π ∈ permSupport A, ∑ i, Real.logb 2 (availCount A π τ i) := by
  rw [entropy_eq_sum_condEntropy_revealedBefore (uniformPMF (permSupport A))
    (uniformPMF_nonneg _) (sum_uniformPMF hP) τ]
  refine (Finset.sum_le_sum fun i (_ : i ∈ univ) =>
    condEntropy_le_expected_logb_availCount A hA hP τ i).trans_eq ?_
  rw [← Finset.mul_sum, Finset.sum_comm]

end Bregman

/-- **Brégman–Minc inequality** (Theorem 10.2.1, conjectured by Minc 1963, proved by Brégman
1973).  For a `0/1` matrix whose `i`-th row sums to `dᵢ`, the permanent — the number of perfect
matchings of the corresponding bipartite graph — is at most `∏ᵢ (dᵢ!) ^ (1 / dᵢ)`.  The proof is
Radhakrishnan's: reveal the entries of a uniform random permutation in a uniform random order. -/
theorem permanent_le_prod_factorial {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) (d : Fin n → ℕ) (hd : ∀ i, ∑ j, A i j = (d i : ℝ)) :
    A.permanent ≤ ∏ i, (Nat.factorial (d i) : ℝ) ^ ((d i : ℝ))⁻¹ := by
  have hfacpos : ∀ i, (0 : ℝ) < (Nat.factorial (d i) : ℝ) := fun i => by
    exact_mod_cast Nat.factorial_pos (d i)
  have hRpos : 0 < ∏ i, (Nat.factorial (d i) : ℝ) ^ ((d i : ℝ))⁻¹ :=
    Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hfacpos i) _
  have hperm : A.permanent = ((permSupport A).card : ℝ) := permanent_eq_card_permSupport A hA
  rcases (permSupport A).eq_empty_or_nonempty with hP | hP
  · rw [hperm, hP]
    simpa using hRpos.le
  · have hcardpos : (0 : ℝ) < ((permSupport A).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hP
    have hfac : (Nat.factorial n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    have hd1 : ∀ i, (d i : ℝ) ≠ 0 := by
      obtain ⟨π, hπ⟩ := hP
      have hπ' : ∀ k, A k (π k) = 1 := (Finset.mem_filter.mp hπ).2
      intro i
      have h1 : (1 : ℝ) ≤ (d i : ℝ) := by
        rw [← hd i, ← hπ' i]
        exact Finset.single_le_sum (f := fun j => A i j)
          (fun j _ => by rcases hA i j with h | h <;> simp [h]) (mem_univ (π i))
      linarith
    have hlogR : Real.logb 2 (∏ i, (Nat.factorial (d i) : ℝ) ^ ((d i : ℝ))⁻¹)
        = ∑ i, ((d i : ℝ))⁻¹ * Real.logb 2 (Nat.factorial (d i) : ℝ) := by
      rw [Real.logb_prod _ _ (fun i _ => ne_of_gt (Real.rpow_pos_of_pos (hfacpos i) _))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.logb, Real.logb, Real.log_rpow (hfacpos i)]
      ring
    have hmain : Real.logb 2 ((permSupport A).card : ℝ)
        ≤ ∑ i, ((d i : ℝ))⁻¹ * Real.logb 2 (Nat.factorial (d i) : ℝ) := by
      have hstep : ∀ τ : Equiv.Perm (Fin n), Real.logb 2 ((permSupport A).card : ℝ)
          ≤ ((permSupport A).card : ℝ)⁻¹ *
            ∑ π ∈ permSupport A, ∑ i, Real.logb 2 (availCount A π τ i) := by
        intro τ
        have h := entropy_permSupport_le_expected_logb_availCount A hA hP τ
        rwa [entropy_uniformPMF hP] at h
      have havg := Finset.sum_le_sum
        (fun τ (_ : τ ∈ (univ : Finset (Equiv.Perm (Fin n)))) => hstep τ)
      rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin, Finset.sum_comm] at havg
      have h1 : Real.logb 2 ((permSupport A).card : ℝ)
          ≤ ((permSupport A).card : ℝ)⁻¹ * ((Nat.factorial n : ℝ))⁻¹ *
            ∑ π ∈ permSupport A, ∑ τ : Equiv.Perm (Fin n),
              ∑ i, Real.logb 2 (availCount A π τ i) := by
        rw [mul_comm ((permSupport A).card : ℝ)⁻¹, mul_assoc,
          le_inv_mul_iff₀ (by exact_mod_cast Nat.factorial_pos n : (0 : ℝ) < Nat.factorial n)]
        exact havg
      refine h1.trans_eq ?_
      have hsum : ∀ π ∈ permSupport A,
          ∑ τ : Equiv.Perm (Fin n), ∑ i, Real.logb 2 (availCount A π τ i)
            = ∑ i, (Nat.factorial n : ℝ) / (d i : ℝ) * Real.logb 2 (Nat.factorial (d i) : ℝ) := by
        intro π hπ
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => sum_logb_availCount A hA d hd hπ i
      rw [Finset.sum_congr rfl hsum, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    rw [hperm]
    refine (Real.logb_le_logb one_lt_two hcardpos hRpos).mp ?_
    rw [hlogR]
    exact hmain

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
