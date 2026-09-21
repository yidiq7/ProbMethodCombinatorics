import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Matching

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

/-- **Gibbs' inequality**, in the form the uniform bound needs: a probability weighting on a
finite set `A` has Shannon entropy at most `log₂ |A|`.

Split out of `entropy_le_logb_card` after that task was claimed and released twice with no PR.
**This is all of its mathematical content**, stated over an arbitrary weight function so that no
`probOf`, no `entropy` and no measure appears — it is a fact about finitely many nonnegative
reals summing to `1`, and nothing else.

**Route.** The elementary one, which is this project's house style for entropy sums and is
shorter here than Mathlib's `ConcaveOn` API — see the conventions note. Write `m = A.card`. For
each `s`, `Real.log_le_sub_one_of_pos` at `1 / (w s * m)` gives

    w s * log (1 / (w s * m)) ≤ w s * (1 / (w s * m) - 1),

and summing the right-hand side over `A` telescopes to `m * (1/m) - 1 = 0` using `hw1`.
Rearranging gives `∑ -w s * log (w s) ≤ log m`, and dividing by `Real.log 2 > 0` converts to
`Real.logb`. The `w s = 0` terms vanish on both sides, since `Real.logb 2 0 = 0`, so they need
no separate case.

`entropy_pair_le_add` in this file is the worked precedent for both the `log t ≤ t - 1` step and
the closing `Real.logb`-to-`Real.log` rescaling.

Verified on 20000 random weightings before publication; `A = ∅` is vacuous because `hw1` would
read `0 = 1`, and `A` a singleton gives `0 ≤ 0`. -/
theorem sum_negMulLogb_le_logb_card {S : Type*} (A : Finset S) (w : S → ℝ)
    (hw0 : ∀ s ∈ A, 0 ≤ w s) (hw1 : ∑ s ∈ A, w s = 1) :
    ∑ s ∈ A, -w s * Real.logb 2 (w s) ≤ Real.logb 2 (A.card : ℝ) := by
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hne : A.Nonempty := by
    rcases A.eq_empty_or_nonempty with rfl | h
    · rw [Finset.sum_empty] at hw1
      exact absurd hw1 (by norm_num)
    · exact h
  have hm : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
  have hmne : (A.card : ℝ) ≠ 0 := ne_of_gt hm
  have key : ∀ x : ℝ, 0 ≤ x →
      -x * Real.log x ≤ x * Real.log (A.card : ℝ) + (1 / (A.card : ℝ) - x) := by
    intro x hx
    rcases hx.eq_or_lt with rfl | hx0
    · simp only [neg_zero, zero_mul, Real.log_zero, mul_zero, zero_add, sub_zero]
      exact le_of_lt (one_div_pos.mpr hm)
    · have hxm : (0 : ℝ) < x * (A.card : ℝ) := mul_pos hx0 hm
      have h1 : Real.log (1 / (x * (A.card : ℝ))) ≤ 1 / (x * (A.card : ℝ)) - 1 :=
        Real.log_le_sub_one_of_pos (one_div_pos.mpr hxm)
      have h2 := mul_le_mul_of_nonneg_left h1 hx
      rw [Real.log_div one_ne_zero (ne_of_gt hxm), Real.log_one,
        Real.log_mul (ne_of_gt hx0) hmne] at h2
      have h3 : x * (1 / (x * (A.card : ℝ)) - 1) = 1 / (A.card : ℝ) - x := by
        field_simp
      rw [h3] at h2
      nlinarith [h2]
  have hsum : ∑ s ∈ A, -w s * Real.log (w s) ≤ Real.log (A.card : ℝ) := by
    have hle : ∑ s ∈ A, -w s * Real.log (w s)
        ≤ ∑ s ∈ A, (w s * Real.log (A.card : ℝ) + (1 / (A.card : ℝ) - w s)) :=
      Finset.sum_le_sum fun s hs => key (w s) (hw0 s hs)
    have hrhs : ∑ s ∈ A, (w s * Real.log (A.card : ℝ) + (1 / (A.card : ℝ) - w s))
        = Real.log (A.card : ℝ) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul, Finset.sum_sub_distrib,
        hw1, Finset.sum_const, nsmul_eq_mul, mul_one_div, div_self hmne, sub_self, add_zero]
    exact hrhs ▸ hle
  calc ∑ s ∈ A, -w s * Real.logb 2 (w s)
      = (∑ s ∈ A, -w s * Real.log (w s)) * (Real.log 2)⁻¹ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun s _ => by rw [Real.logb]; ring
    _ ≤ Real.log (A.card : ℝ) * (Real.log 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hsum (le_of_lt (inv_pos.mpr hL))
    _ = Real.logb 2 (A.card : ℝ) := by rw [Real.logb]; ring

/-- **Uniform bound** (Lemma 10.1.4): `H(X) ≤ log₂ |support X|`.  The support is supplied as a
finset `A` containing it, which avoids needing decidable equality on `ℝ`; taking `A` to be the
support itself gives the statement in the book. -/
theorem entropy_le_logb_card (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (X : Ω → S)
    (A : Finset S) (hA : ∀ s ∉ A, probOf p X s = 0) :
    entropy p X ≤ Real.logb 2 (A.card : ℝ) := by
  have hsub : A ⊆ (univ : Finset S) := Finset.subset_univ A
  -- Outside `A` every probability, hence every entropy summand, is zero.
  have hzero : ∀ s ∈ (univ : Finset S), s ∉ A →
      -probOf p X s * Real.logb 2 (probOf p X s) = 0 := by
    intro s _ hs
    rw [hA s hs]
    simp
  have hmass : ∑ s ∈ A, probOf p X s = 1 := by
    rw [Finset.sum_subset hsub fun s _ hs => hA s hs, sum_probOf, hp1]
  have hent : entropy p X = ∑ s ∈ A, -probOf p X s * Real.logb 2 (probOf p X s) :=
    (Finset.sum_subset hsub hzero).symm
  rw [hent]
  exact sum_negMulLogb_le_logb_card A (probOf p X) (fun s _ => probOf_nonneg hp X s) hmass

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

/-- A constant random variable carries no entropy. -/
theorem entropy_const (hp1 : ∑ ω, p ω = 1) (c : S) : entropy p (fun _ : Ω => c) = 0 := by
  unfold entropy
  refine Finset.sum_eq_zero fun s _ => ?_
  rcases eq_or_ne c s with rfl | hcs
  · have h : probOf p (fun _ : Ω => c) c = 1 := by simp [probOf, hp1]
    rw [h]; simp
  · have h : probOf p (fun _ : Ω => c) s = 0 := by simp [probOf, hcs]
    rw [h]; simp

/-- **Uniform distributions** : if `X` is injective on a nonempty finset `P`, then a uniform
random element of `P` gives `X` entropy `log₂ |P|`.  This is the equality case of
`entropy_le_logb_card`, and it is how every application in this chapter turns a count into an
entropy. -/
theorem entropy_uniformPMF_of_injOn [DecidableEq Ω] {P : Finset Ω} (hP : P.Nonempty)
    {X : Ω → S} (hX : Set.InjOn X P) :
    entropy (uniformPMF P) X = Real.logb 2 (P.card : ℝ) := by
  have hcard : (P.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hP.card_ne_zero
  have hprob : ∀ s : S, probOf (uniformPMF P) X s
      = if s ∈ P.image X then ((P.card : ℝ))⁻¹ else 0 := by
    intro s
    have hfib : (univ.filter fun ω => X ω = s) ∩ P = P.filter fun ω => X ω = s := by
      ext ω; simp [and_comm]
    rw [probOf]
    simp only [uniformPMF]
    rw [Finset.sum_ite_mem, hfib, Finset.sum_const, nsmul_eq_mul]
    by_cases hs : s ∈ P.image X
    · obtain ⟨ω₀, hω₀, rfl⟩ := Finset.mem_image.mp hs
      rw [if_pos hs, show (P.filter fun ω => X ω = X ω₀) = {ω₀} from Finset.eq_singleton_iff_unique_mem.mpr
        ⟨Finset.mem_filter.mpr ⟨hω₀, rfl⟩, fun ω hω =>
          hX (Finset.mem_filter.mp hω).1 hω₀ (Finset.mem_filter.mp hω).2⟩]
      simp
    · rw [if_neg hs, Finset.filter_eq_empty_iff.mpr fun ω hω h =>
        hs (Finset.mem_image.mpr ⟨ω, hω, h⟩)]
      simp
  have hsum : entropy (uniformPMF P) X
      = ∑ s : S, if s ∈ P.image X then
          -((P.card : ℝ))⁻¹ * Real.logb 2 (((P.card : ℝ))⁻¹) else 0 := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hprob s]
    split_ifs <;> simp
  rw [hsum, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
    Finset.card_image_of_injOn hX, nsmul_eq_mul, Real.logb_inv]
  field_simp

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
  rcases isEmpty_or_nonempty S with h | h
  · simp [entropy]
  · obtain ⟨c⟩ := h
    rw [show X = fun _ => c from funext fun _ => Subsingleton.elim _ _, entropy_const hp1]

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
          refine Eq.trans (congrArg (entropy p) (funext fun ω => ?_)) (entropy_comp_inj hinj _)
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
          entropy_comp_inj (Option.some_injective (α a)) _
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
    Eq.trans (congrArg (entropy p) (funext fun ω => by funext i; rw [hY]; simp))
      (entropy_comp_inj hsome _)
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
  have hassoc : Function.Injective (fun w : S × T × U => ((w.1, w.2.1), w.2.2)) := by
    rintro ⟨x₁, y₁, z₁⟩ ⟨x₂, y₂, z₂⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨e₁, e₂⟩, e₃⟩ := h
    simp [e₁, e₂, e₃]
  -- Chain rule for the pair `(X, Y)` against `Z`: `H(X, Y, Z) ≤ H(X, Y) + H(Z)`.
  have hpair : entropy p (fun ω => (X ω, Y ω, Z ω))
      ≤ entropy p (fun ω => (X ω, Y ω)) + entropy p Z := by
    rw [← entropy_comp_inj (p := p) hassoc (fun ω => (X ω, Y ω, Z ω))]
    exact entropy_pair_le_add hp hp1 (fun ω => (X ω, Y ω)) Z
  -- Submodularity: `H(X, Y, Z) + H(Z) ≤ H(X, Z) + H(Y, Z)`.
  have hsub := entropy_triple_add_le (p := p) hp hp1 X Y Z
  linarith

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
  rw [entropy_uniformPMF_of_injOn Finset.univ_nonempty hX.injOn, Finset.card_univ]

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
  obtain ⟨G₀, hG₀⟩ := id hne
  have hn : 3 ≤ n := by
    obtain ⟨a, b, c, hab, hac, hbc, -⟩ := hinter G₀ hG₀ G₀ hG₀
    have h3 := Finset.card_le_univ ({a, b, c} : Finset (Fin n))
    rw [Fintype.card_fin, Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton] at h3
    omega
  have hemp : (∅ : Finset (Fin n)) ≠ univ := fun h => by
    simpa [← h] using Finset.mem_univ (⟨0, by omega⟩ : Fin n)
  -- Exactly half of the `2 ^ n` vertex sets keep two given distinct vertices on the same side:
  -- erasing `u` is a bijection onto the subsets avoiding `u`.
  have hsame : ∀ u v : Fin n, u ≠ v →
      (univ.filter fun S : Finset (Fin n) => (u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∉ S)).card
        = 2 ^ (n - 1) := by
    intro u v huv
    rw [show (2 : ℕ) ^ (n - 1) = (({u} : Finset (Fin n))ᶜ).powerset.card by
      rw [Finset.card_powerset, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]]
    refine Finset.card_nbij' (fun S => S.erase u)
      (fun T => if v ∈ T then insert u T else T) ?_ ?_ ?_ ?_ <;>
      intro x hx <;> simp_all <;> split_ifs <;> simp_all [Finset.insert_erase, Ne.symm huv]
  -- `E` is the edge set of `Kₙ`; for a vertex set `S` the cut `A S` collects the edges with both
  -- endpoints in `S` and those with both endpoints in `Sᶜ`; `J` indexes the proper nonempty cuts.
  obtain ⟨E, hEdef⟩ : ∃ E : Finset (Sym2 (Fin n)),
      E = univ.filter (fun e => ¬ e.IsDiag) := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : Finset (Fin n) → Finset (Sym2 (Fin n)),
      ∀ S, A S = E.filter (fun e => e ∈ S.sym2 ∨ e ∈ Sᶜ.sym2) := ⟨_, fun _ => rfl⟩
  obtain ⟨J, hJdef⟩ : ∃ J : Finset (Finset (Fin n)),
      J = (univ : Finset (Finset (Fin n))) \ {∅, univ} := ⟨_, rfl⟩
  have hmemE : ∀ e : Sym2 (Fin n), e ∈ E ↔ ¬ e.IsDiag := fun e => by rw [hEdef]; simp
  have hmemA : ∀ (S : Finset (Fin n)) (u v : Fin n),
      s(u, v) ∈ A S ↔ (u ≠ v ∧ ((u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∉ S))) := fun S u v => by
    rw [hAdef, Finset.mem_filter, hmemE]; simp
  have hAE : ∀ S, A S ⊆ E := fun S => by rw [hAdef]; exact Finset.filter_subset _ _
  have hEcard : E.card = n.choose 2 := by
    rw [hEdef, ← Fintype.card_subtype, Sym2.card_subtype_not_diag, Fintype.card_fin]
  -- Each edge lies in `2 ^ (n - 1) - 2` of the cut sets `A S`, `S ∈ J`.
  have hcount : ∀ e ∈ E, (J.filter fun S => e ∈ A S).card = 2 ^ (n - 1) - 2 := by
    refine Sym2.ind fun u v he => ?_
    have huv : u ≠ v := by simpa [hmemE] using he
    have hfil : (J.filter fun S => s(u, v) ∈ A S)
        = (univ.filter (fun S : Finset (Fin n) => (u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∉ S)))
          \ ({∅, univ} : Finset (Finset (Fin n))) := by
      rw [hJdef]; ext S
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, hmemA S u v,
        huv, ne_eq, not_false_eq_true, true_and]
      tauto
    rw [hfil, Finset.card_sdiff, Finset.inter_eq_left.mpr (by simp [Finset.insert_subset_iff]),
      hsame u v huv, Finset.card_insert_of_notMem (by simpa using hemp), Finset.card_singleton]
  -- Double counting: the cut sets have total size `|E| * k`.
  have hsum : ∑ S ∈ J, (A S).card = E.card * (2 ^ (n - 1) - 2) := by
    have h1 : ∀ S ∈ J, (A S).card = ∑ e ∈ E, if e ∈ A S then 1 else 0 := fun S _ => by
      rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hAE S)]
    have h2 : ∀ e ∈ E, (∑ S ∈ J, if e ∈ A S then 1 else 0) = 2 ^ (n - 1) - 2 := fun e he => by
      rw [← Finset.card_filter]; exact hcount e he
    rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.sum_congr rfl h2, Finset.sum_const,
      smul_eq_mul]
  have hJcard : J.card = 2 ^ n - 2 := by
    rw [hJdef, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_insert_of_notMem (by simpa using hemp),
      Finset.card_singleton, Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
  -- Pigeonhole: two of any three vertices lie on the same side of the cut.
  have hpigeon : ∀ (S : Finset (Fin n)) (a b c : Fin n), a ≠ b → a ≠ c → b ≠ c →
      ∃ e ∈ triangleEdges a b c, e ∈ A S := by
    intro S a b c hab hac hbc
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> by_cases hc : c ∈ S <;>
      simp [triangleEdges, hmemA S, hab, hac, hbc, ha, hb, hc]
  -- Each restriction is an intersecting family of subsets of `A S`.
  have hrestr : ∀ S : Finset (Fin n),
      2 * (𝒢.image fun G => G ∩ A S).card ≤ 2 ^ (A S).card := by
    intro S
    set F := 𝒢.image fun G => G ∩ A S
    have hsub : ∀ X ∈ F, X ⊆ A S := fun X hX => by
      obtain ⟨G, -, rfl⟩ := Finset.mem_image.mp hX; exact Finset.inter_subset_right
    have hint : ∀ X ∈ F, ∀ Y ∈ F, (X ∩ Y).Nonempty := by
      intro X hX Y hY
      obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hX
      obtain ⟨H, hH, rfl⟩ := Finset.mem_image.mp hY
      obtain ⟨a, b, c, hab, hac, hbc, htri⟩ := hinter G hG H hH
      obtain ⟨e, hetri, heA⟩ := hpigeon S a b c hab hac hbc
      exact ⟨e, by simpa [Finset.mem_inter, heA] using htri hetri⟩
    have hcard : (F.image fun X => A S \ X).card = F.card :=
      Finset.card_image_of_injOn fun X hX Y hY h => by
        simpa [Finset.sdiff_sdiff_eq_self (hsub X hX), Finset.sdiff_sdiff_eq_self (hsub Y hY)]
          using congrArg (fun Z => A S \ Z) h
    have hdisj : Disjoint F (F.image fun X => A S \ X) :=
      Finset.disjoint_right.mpr fun Z hZ hZF => by
        obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hZ
        obtain ⟨x, hx⟩ := hint _ hZF _ hY
        exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).1).2 (Finset.mem_inter.mp hx).2
    have hcup : (F ∪ F.image fun X => A S \ X) ⊆ (A S).powerset :=
      Finset.union_subset (fun Z h => Finset.mem_powerset.mpr (hsub Z h))
        (Finset.image_subset_iff.mpr fun Y _ => Finset.mem_powerset.mpr Finset.sdiff_subset)
    have hle := Finset.card_le_card hcup
    rw [Finset.card_union_of_disjoint hdisj, hcard, Finset.card_powerset] at hle
    omega
  -- Shearer for set families.  `hdiag` enters here: it is what makes every member of `𝒢` a subset
  -- of `E`, and only the elements of `E` are covered by the cuts.
  have hcor := card_pow_le_prod_card_image_inter 𝒢 hne E
    (fun G hG e he => (hmemE e).mpr (hdiag G hG e he)) J A (2 ^ (n - 1) - 2)
    (fun i hi => (hcount i hi).ge)
  have hprod : 2 ^ J.card * 𝒢.card ^ (2 ^ (n - 1) - 2) ≤ 2 ^ (∑ S ∈ J, (A S).card) := by
    calc 2 ^ J.card * 𝒢.card ^ (2 ^ (n - 1) - 2)
        ≤ 2 ^ J.card * ∏ S ∈ J, (𝒢.image fun G => G ∩ A S).card := Nat.mul_le_mul_left _ hcor
      _ = ∏ S ∈ J, 2 * (𝒢.image fun G => G ∩ A S).card := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ ∏ S ∈ J, 2 ^ (A S).card := Finset.prod_le_prod' fun S _ => hrestr S
      _ = 2 ^ (∑ S ∈ J, (A S).card) := Finset.prod_pow_eq_pow_sum _ _ _
  -- If `2 ^ (binom n 2 - 2) ≤ |𝒢|` the two sides of `hprod` read
  -- `2 ^ (2 ^ n - 2 + (binom n 2 - 2) * k) ≤ 2 ^ (binom n 2 * k)` with `k = 2 ^ (n - 1) - 2`,
  -- forcing `2 ^ n - 2 ≤ 2 * k = 2 ^ n - 4`.
  by_contra hcon
  have hC : 3 ≤ n.choose 2 := by simpa using Nat.choose_le_choose 2 hn
  have hkey : (2 : ℕ) ^ (J.card + (n.choose 2 - 2) * (2 ^ (n - 1) - 2))
      ≤ 2 ^ (n.choose 2 * (2 ^ (n - 1) - 2)) := by
    calc (2 : ℕ) ^ (J.card + (n.choose 2 - 2) * (2 ^ (n - 1) - 2))
        = 2 ^ J.card * (2 ^ (n.choose 2 - 2)) ^ (2 ^ (n - 1) - 2) := by rw [pow_add, pow_mul]
      _ ≤ 2 ^ J.card * 𝒢.card ^ (2 ^ (n - 1) - 2) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_of_not_lt hcon) _)
      _ ≤ 2 ^ (∑ S ∈ J, (A S).card) := hprod
      _ = 2 ^ (n.choose 2 * (2 ^ (n - 1) - 2)) := by rw [hsum, hEcard]
  have hle := (Nat.pow_le_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp hkey
  have h2k : 2 * (2 ^ (n - 1) - 2) ≤ n.choose 2 * (2 ^ (n - 1) - 2) :=
    Nat.mul_le_mul_right _ (by omega)
  have hpow : 2 * 2 ^ (n - 1) = 2 ^ n := by rw [← pow_succ']; congr 1; omega
  have hpow4 : (4 : ℕ) ≤ 2 ^ (n - 1) := by
    simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (show 2 ≤ n - 1 by omega)
  rw [hJcard, Nat.sub_mul] at hle
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
    entropy (uniformPMF P) id = Real.logb 2 (P.card : ℝ) :=
  entropy_uniformPMF_of_injOn hP (Set.injOn_id _)

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

/-- Reading off a permutation's values at every row is injective. -/
private theorem perm_toPi_injective {n : ℕ} :
    Function.Injective fun σ : Equiv.Perm (Fin n) =>
      fun j : ↥(univ : Finset (Fin n)) => σ j.1 := by
  intro σ σ' h
  refine Equiv.ext fun x => ?_
  exact congrFun h ⟨x, Finset.mem_univ x⟩

/-- `revealedBefore τ i` is an injective relabelling of the tuple of entries in the rows that
precede `i` in the order `τ`: padding those entries out to a function on all of `Fin n` with
`none` outside loses nothing. -/
private theorem exists_revealedBefore_comp {n : ℕ} (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    ∃ g : (↥((univ : Finset (Fin n)).filter fun x => ((τ x : ℕ)) < ((τ i : ℕ))) → Fin n) →
        (Fin n → Option (Fin n)),
      Function.Injective g ∧
        ∀ π : Equiv.Perm (Fin n), g (fun j => π j.1) = revealedBefore τ i π := by
  refine ⟨fun h j => if hj : ((τ j : Fin n) : ℕ) < ((τ i : Fin n) : ℕ) then
      some (h ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩) else none, ?_, ?_⟩
  · intro h h' e
    funext j
    obtain ⟨x, hx⟩ := j
    have hx' : ((τ x : Fin n) : ℕ) < ((τ i : Fin n) : ℕ) := (Finset.mem_filter.mp hx).2
    have hval := congrFun e x
    simp only [dif_pos hx'] at hval
    exact Option.some_injective _ hval
  · intro π
    funext j
    simp only [revealedBefore]
    by_cases hj : ((τ j : Fin n) : ℕ) < ((τ i : Fin n) : ℕ)
    · rw [dif_pos hj, if_pos (Fin.lt_def.mpr hj)]
    · rw [dif_neg hj, if_neg fun hc => hj (Fin.lt_def.mp hc)]

/-- **The chain rule along a reveal order.**  Reveal the values of a random permutation `π` in
the order given by `τ` — row `j` before row `k` when `τ j < τ k`.  Then the entropy of `π` is the
sum, over the rows `i`, of the entropy of `π i` conditioned on what was revealed before row `i`.

This is Lemma 10.1.7 (`condEntropy_eq_sub`) telescoped along the order `τ`: writing `Pₖ` for the
first `k` entries revealed, `H(P_{k+1}) = H(Pₖ) + H(π_{τ⁻¹ k} ∣ Pₖ)`, with `P₀` constant and
`Pₙ` determining `π`. -/
theorem entropy_eq_sum_condEntropy_revealedBefore {n : ℕ} (p : Equiv.Perm (Fin n) → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (τ : Equiv.Perm (Fin n)) :
    entropy p id = ∑ i, condEntropy p (fun π => π i) (revealedBefore τ i) := by
  have hr : Function.Injective fun i : Fin n => ((τ i : Fin n) : ℕ) :=
    fun a b h => τ.injective (Fin.val_injective h)
  have hL : entropy p (fun (ω : Equiv.Perm (Fin n)) (j : ↥(univ : Finset (Fin n))) => ω j.1)
      = entropy p id := entropy_comp_inj (p := p) perm_toPi_injective id
  have key : entropy p (fun (ω : Equiv.Perm (Fin n)) (j : ↥(univ : Finset (Fin n))) => ω j.1)
      = ∑ i ∈ (univ : Finset (Fin n)), condEntropy p (fun π : Equiv.Perm (Fin n) => π i)
          (fun (ω : Equiv.Perm (Fin n))
            (j : ↥((univ : Finset (Fin n)).filter fun x => ((τ x : ℕ)) < ((τ i : ℕ)))) =>
              ω j.1) :=
    entropy_pi_eq_sum_condEntropy (p := p) (α := fun _ : Fin n => Fin n) hp hp1
      (fun i π => π i) hr univ
  have hR : ∀ i : Fin n, condEntropy p (fun π : Equiv.Perm (Fin n) => π i)
      (fun (ω : Equiv.Perm (Fin n))
        (j : ↥((univ : Finset (Fin n)).filter fun x => ((τ x : ℕ)) < ((τ i : ℕ)))) => ω j.1)
      = condEntropy p (fun π : Equiv.Perm (Fin n) => π i) (revealedBefore τ i) := by
    intro i
    obtain ⟨g, hginj, hgeq⟩ := exists_revealedBefore_comp τ i
    have h1 : condEntropy p (fun π : Equiv.Perm (Fin n) => π i)
        (fun ω : Equiv.Perm (Fin n) => g fun j => ω j.1)
        = condEntropy p (fun π : Equiv.Perm (Fin n) => π i)
          (fun (ω : Equiv.Perm (Fin n))
            (j : ↥((univ : Finset (Fin n)).filter fun x => ((τ x : ℕ)) < ((τ i : ℕ)))) =>
              ω j.1) := condEntropy_comp_inj hp hginj _ _
    have h2 : (fun ω : Equiv.Perm (Fin n) => g fun j => ω j.1) = revealedBefore τ i :=
      funext hgeq
    rw [← h1, h2]
  rw [← hL, key]
  exact Finset.sum_congr rfl fun i _ => hR i

/-- The expectation of a function of a random variable, rewritten as a sum over the sample
space. -/
private theorem sum_probOf_mul {Ω T : Type*} [Fintype Ω] [Fintype T] [DecidableEq T]
    (p : Ω → ℝ) (Y : Ω → T) (f : T → ℝ) :
    ∑ t : T, probOf p Y t * f t = ∑ ω, p ω * f (Y ω) := by
  have h : ∀ t : T, probOf p Y t * f t
      = ∑ ω ∈ univ.filter fun ω => Y ω = t, p ω * f (Y ω) := by
    intro t
    simp only [probOf, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ω hω => ?_
    rw [(Finset.mem_filter.mp hω).2]
  rw [Finset.sum_congr rfl fun t (_ : t ∈ univ) => h t,
    Finset.sum_fiberwise_eq_sum_filter (univ : Finset Ω) univ Y fun ω => p ω * f (Y ω)]
  simp

/-- **The uniform bound applied fibre by fibre.**  If, inside every fibre of the conditioning
variable `Y`, the variable `X` is confined to the finset `B t`, then `H(X ∣ Y)` is at most the
expectation of `log₂ |B t|`.  The conditional distribution in the fibre `t` is a probability
mass function in its own right, so `entropy_le_logb_card` bounds its entropy by
`log₂ |B t|`, and the fibres are weighted by `P(Y = t)`. -/
private theorem condEntropy_le_sum_probOf_mul_logb {Ω S T : Type*} [Fintype Ω] [Fintype S]
    [DecidableEq S] [Fintype T] [DecidableEq T] {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω)
    (X : Ω → S) (Y : Ω → T) (B : T → Finset S)
    (hB : ∀ (t : T) (s : S), s ∉ B t → probOf p (fun ω => (X ω, Y ω)) (s, t) = 0) :
    condEntropy p X Y ≤ ∑ t : T, probOf p Y t * Real.logb 2 ((B t).card : ℝ) := by
  rw [condEntropy]
  refine Finset.sum_le_sum fun t _ => ?_
  rcases eq_or_lt_of_le (probOf_nonneg hp Y t) with hq | hq
  · have hj : ∀ s : S, probOf p (fun ω => (X ω, Y ω)) (s, t) = 0 := fun s =>
      le_antisymm ((probOf_pair_le_right hp X Y s t).trans hq.ge) (probOf_nonneg hp _ _)
    simp [hj, ← hq]
  · have hq0 : probOf p Y t ≠ 0 := ne_of_gt hq
    have hfil : ∀ s : S, (univ.filter fun ω => (X ω, Y ω) = (s, t))
        = (univ.filter fun ω => X ω = s).filter fun ω => Y ω = t := by
      intro s
      ext ω
      simp [Prod.ext_iff]
    have hsum : ∀ s : S,
        probOf (fun ω => if Y ω = t then p ω / probOf p Y t else 0) X s
          = probOf p (fun ω => (X ω, Y ω)) (s, t) / probOf p Y t := by
      intro s
      simp only [probOf, hfil s]
      rw [Finset.sum_div, ← Finset.sum_filter]
    have hptnn : ∀ ω, 0 ≤ (if Y ω = t then p ω / probOf p Y t else 0) := by
      intro ω
      split
      · exact div_nonneg (hp ω) hq.le
      · exact le_rfl
    have hpt1 : ∑ ω, (if Y ω = t then p ω / probOf p Y t else 0) = 1 := by
      rw [← Finset.sum_filter, ← Finset.sum_div]
      exact div_self hq0
    have hent := entropy_le_logb_card hptnn hpt1 X (B t)
      fun s hs => by rw [hsum s, hB t s hs, zero_div]
    rw [entropy] at hent
    simp only [hsum] at hent
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hent hq.le)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hcancel : probOf p Y t * (probOf p (fun ω => (X ω, Y ω)) (s, t) / probOf p Y t)
        = probOf p (fun ω => (X ω, Y ω)) (s, t) := by
      field_simp
    linear_combination
      Real.logb 2 (probOf p (fun ω => (X ω, Y ω)) (s, t) / probOf p Y t) * hcancel

/-- The columns of row `i` that a matching may still use once the entries revealed before row
`i` are known: the ones of row `i` in a column that `y` does not already occupy. -/
private noncomputable def availSet {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (y : Fin n → Option (Fin n)) : Finset (Fin n) :=
  univ.filter fun c => A i c = 1 ∧ ∀ j, y j ≠ some c

/-- A column `π k` is free at row `i` exactly when row `k` is not revealed before row `i`. -/
private theorem revealedBefore_ne_some_iff {n : ℕ} (τ π : Equiv.Perm (Fin n)) (i k : Fin n) :
    (∀ j, revealedBefore τ i π j ≠ some (π k)) ↔ τ i ≤ τ k := by
  simp only [revealedBefore]
  constructor
  · intro h
    by_contra hc
    exact h k (by rw [if_pos (not_le.mp hc)])
  · intro h j hj
    by_cases hlt : τ j < τ i
    · rw [if_pos hlt] at hj
      rw [π.injective (Option.some_injective _ hj)] at hlt
      exact absurd hlt (not_lt.mpr h)
    · rw [if_neg hlt] at hj
      exact absurd hj (by simp)

/-- `availCount` is determined by what was revealed before row `i`: it counts the free columns
of row `i`, and `π` matches them bijectively with the rows not yet revealed. -/
private theorem card_availSet_revealedBefore {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (π τ : Equiv.Perm (Fin n)) (i : Fin n) :
    (availSet A i (revealedBefore τ i π)).card = availCount A π τ i := by
  rw [availSet, availCount]
  refine Finset.card_equiv π.symm fun c => ?_
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, Equiv.apply_symm_apply]
  exact and_congr Iff.rfl (by
    rw [← revealedBefore_ne_some_iff τ π i (π.symm c), Equiv.apply_symm_apply])

/-- The entry of row `i` is itself a free column: it is a one of row `i`, and no earlier row
occupies it. -/
private theorem mem_availSet_of_mem_permSupport {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {π : Equiv.Perm (Fin n)} (hπ : π ∈ permSupport A) (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    π i ∈ availSet A i (revealedBefore τ i π) := by
  rw [availSet, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hπ).2 i,
    (revealedBefore_ne_some_iff τ π i i).mpr le_rfl⟩

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
  have hB : ∀ (t : Fin n → Option (Fin n)) (s : Fin n), s ∉ availSet A i t →
      probOf (uniformPMF (permSupport A))
        (fun π : Equiv.Perm (Fin n) => (π i, revealedBefore τ i π)) (s, t) = 0 := by
    intro t s hs
    refine Finset.sum_eq_zero fun π hπ => ?_
    rw [Finset.mem_filter, Prod.mk.injEq] at hπ
    by_cases hmem : π ∈ permSupport A
    · have hmemA := mem_availSet_of_mem_permSupport A hmem τ i
      rw [hπ.2.1, hπ.2.2] at hmemA
      exact absurd hmemA hs
    · simp [uniformPMF, hmem]
  refine (condEntropy_le_sum_probOf_mul_logb (uniformPMF_nonneg (permSupport A))
    (fun π : Equiv.Perm (Fin n) => π i) (revealedBefore τ i) (availSet A i) hB).trans_eq ?_
  rw [sum_probOf_mul, Finset.mul_sum]
  simp only [uniformPMF, ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  exact Finset.sum_congr rfl fun π _ => by rw [card_availSet_revealedBefore]

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

/-! ### 10.2 Kahn–Lovász: the bipartite double cover

Corollary 10.2.2 reduces to Brégman–Minc — proved above as `permanent_le_prod_factorial` — via
the bipartite double cover.  Both objects the reduction needs are absent from Mathlib and are
authored here: `SimpleGraph.Subgraph.IsPerfectMatching` exists only as a predicate, with no
count, and Mathlib's `□` (`boxProd`) is the **Cartesian** product, not the one wanted.
-/

section DoubleCover

variable {V : Type*}

/-- The **bipartite double cover** `G × K₂`: vertices `V × Bool`, with `(u, i)` adjacent to
`(v, j)` when `u` and `v` are adjacent in `G` *and* `i ≠ j`.

**This is the tensor product, not Mathlib's `boxProd`.**  `boxProd` joins `(u, i)` to `(v, j)`
when `u = v ∧ i ≠ j` or `i = j ∧ u ~ v`, which is a different graph: on `K₂` the double cover is
`2K₂`, two disjoint edges, while `boxProd` gives the 4-cycle.  Reaching for `□` here would build
a graph about which every subsequent theorem is true and useless.

`fromRel` supplies symmetry and looplessness, and recovers exactly the intended relation: the
underlying relation is already symmetric, and `i ≠ j` forces `(u, i) ≠ (v, j)`. -/
def doubleCover (G : SimpleGraph V) : SimpleGraph (V × Bool) :=
  SimpleGraph.fromRel fun a b => G.Adj a.1 b.1 ∧ a.2 ≠ b.2

@[simp] theorem doubleCover_adj {G : SimpleGraph V} {a b : V × Bool} :
    (doubleCover G).Adj a b ↔ G.Adj a.1 b.1 ∧ a.2 ≠ b.2 := by
  simp only [doubleCover, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, ⟨h, h2⟩ | ⟨h, h2⟩⟩
    · exact ⟨h, h2⟩
    · exact ⟨h.symm, h2.symm⟩
  · rintro ⟨h, h2⟩
    exact ⟨fun hab => h2 (by rw [hab]), Or.inl ⟨h, h2⟩⟩

/-- The number of perfect matchings of `G`, written `pm(G)` in the source.

`Nat.card` rather than a `Finset.card`: `Subgraph.IsPerfectMatching` has no `DecidablePred`
instance and this project declares none.  For finite `V` the subtype is `Finite`, so the count is
the honest cardinality and not `Nat.card`'s junk value at infinite types. -/
noncomputable def perfectMatchingCount [Fintype V] (G : SimpleGraph V) : ℕ :=
  Nat.card {M : G.Subgraph // M.IsPerfectMatching}

/-- The subgraph of the double cover picked out by a permutation `σ`: the edges are the
`(i, false) — (σ i, true)`, and every vertex is included.  The adjacency relation carries the
double cover's own adjacency, so the subgraph is defined for every `σ`; it is a perfect matching
exactly when `i` and `σ i` are adjacent in `G` for every `i`. -/
private def doubleCoverSubgraphOfPerm {n : ℕ} (G : SimpleGraph (Fin n))
    (σ : Equiv.Perm (Fin n)) : (doubleCover G).Subgraph where
  verts := Set.univ
  Adj a b := (doubleCover G).Adj a b ∧ (b = (σ a.1, true) ∨ a = (σ b.1, true))
  adj_sub h := h.1
  edge_vert _ := Set.mem_univ _
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩

/-- `doubleCoverSubgraphOfPerm G σ` is a perfect matching as soon as `σ` moves every vertex along
an edge of `G`: the vertex `(i, false)` is matched to `(σ i, true)`, and `(j, true)` to
`(σ⁻¹ j, false)`, which is where the surjectivity of `σ` enters. -/
private theorem doubleCoverSubgraphOfPerm_isPerfectMatching {n : ℕ} {G : SimpleGraph (Fin n)}
    {σ : Equiv.Perm (Fin n)} (hσ : ∀ i, G.Adj i (σ i)) :
    (doubleCoverSubgraphOfPerm G σ).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  rintro ⟨u, c⟩
  cases c with
  | false =>
    refine ⟨(σ u, true), ⟨by simpa using hσ u, Or.inl rfl⟩, ?_⟩
    rintro ⟨v, d⟩ ⟨-, h2 | h2⟩
    · exact h2
    · simp at h2
  | true =>
    refine ⟨(σ.symm u, false), ⟨by simpa using (hσ (σ.symm u)).symm, Or.inr (by simp)⟩, ?_⟩
    rintro ⟨v, d⟩ ⟨h1, h2 | h2⟩
    · rw [h2] at h1
      simp at h1
    · have hu : u = σ v := by simpa using h2
      have hd : d = false := by
        rw [doubleCover_adj] at h1
        simpa using h1.2
      subst hd
      rw [hu, Equiv.symm_apply_apply]

/-- **The double cover's perfect matchings are the permanent of the adjacency matrix.**

A perfect matching of `G × K₂` sends each `(u, false)` to some `(σ u, true)`, and covering the
`true` side forces `σ` to be a bijection; adjacency in the double cover says exactly that `u` and
`σ u` are adjacent in `G`.  So perfect matchings correspond to the permutations counted by
`permSupport` of the adjacency matrix.

This is the bridge from Corollary 10.2.2 to `permanent_le_prod_factorial`: with
`permanent_eq_card_permSupport` it turns a statement about perfect matchings into one about a
permanent, which Brégman–Minc then bounds. -/
theorem perfectMatchingCount_doubleCover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    perfectMatchingCount (doubleCover G)
      = (univ.filter fun σ : Equiv.Perm (Fin n) => ∀ i, G.Adj i (σ i)).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, perfectMatchingCount]
  refine (Nat.card_eq_of_bijective
    (fun σ => (⟨doubleCoverSubgraphOfPerm G σ.1,
      doubleCoverSubgraphOfPerm_isPerfectMatching σ.2⟩ :
        {M : (doubleCover G).Subgraph // M.IsPerfectMatching})) ⟨?_, ?_⟩).symm
  · rintro ⟨σ, hσ⟩ ⟨τ, _⟩ h
    simp only [Subtype.mk_eq_mk] at h
    refine Subtype.ext (Equiv.ext fun i => ?_)
    have h1 : (doubleCoverSubgraphOfPerm G τ).Adj (i, false) (σ i, true) := by
      rw [← h]; exact ⟨by simpa using hσ i, Or.inl rfl⟩
    rcases h1.2 with h2 | h2
    · simpa using h2
    · simp at h2
  · rintro ⟨M, hM⟩
    have hu : ∀ i : Fin n, ∃! j : Fin n, M.Adj (i, false) (j, true) := by
      intro i
      obtain ⟨⟨v, d⟩, hw, hwu⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM (i, false)
      have hd : d = true := by
        have := M.adj_sub hw
        rw [doubleCover_adj] at this
        simpa using this.2
      subst hd
      exact ⟨v, hw, fun j hj => by simpa using hwu (j, true) hj⟩
    choose σ₀ hσ₀ hσ₀u using hu
    have hinj : Function.Injective σ₀ := by
      intro i j hij
      have h2 : M.Adj (j, false) (σ₀ i, true) := by rw [hij]; exact hσ₀ j
      simpa using hM.1.eq_of_adj_right (hσ₀ i) h2
    have hbij := Finite.injective_iff_bijective.mp hinj
    have hcoe : ∀ i, (Equiv.ofBijective σ₀ hbij) i = σ₀ i := fun _ => rfl
    have hGadj : ∀ i, G.Adj i (σ₀ i) := by
      intro i
      have := M.adj_sub (hσ₀ i)
      rw [doubleCover_adj] at this
      exact this.1
    refine ⟨⟨Equiv.ofBijective σ₀ hbij, by simpa only [hcoe] using hGadj⟩, Subtype.ext ?_⟩
    refine SimpleGraph.Subgraph.ext ((Set.eq_univ_iff_forall.mpr hM.2).symm) ?_
    funext a b
    obtain ⟨u, c⟩ := a
    obtain ⟨v, d⟩ := b
    simp only [eq_iff_iff]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · obtain ⟨rfl, rfl⟩ : v = σ₀ u ∧ d = true := by simpa only [hcoe, Prod.mk.injEq] using h2
        have hc : c = false := by
          rw [doubleCover_adj] at h1
          simpa using h1.2
        subst hc
        exact hσ₀ u
      · obtain ⟨rfl, rfl⟩ : u = σ₀ v ∧ c = true := by simpa only [hcoe, Prod.mk.injEq] using h2
        have hd : d = false := by
          rw [doubleCover_adj] at h1
          simpa using h1.2
        subst hd
        exact (hσ₀ v).symm
    · intro hadj
      have hdc := M.adj_sub hadj
      rw [doubleCover_adj] at hdc
      refine ⟨M.adj_sub hadj, ?_⟩
      cases c with
      | false =>
        have hd : d = true := by simpa using hdc.2
        subst hd
        exact Or.inl (by rw [hcoe, hσ₀u u v hadj])
      | true =>
        have hd : d = false := by simpa using hdc.2
        subst hd
        exact Or.inr (by rw [hcoe, hσ₀u v u hadj.symm])

/-- The subgraph of `G` picked out by a vertex map `f`: the edges are the `v — f v`, and every
vertex is included.  The adjacency relation carries `G`'s own adjacency, so the subgraph is
defined for every `f`; it is a perfect matching exactly when `f` is a fixed-point-free
involution moving every vertex along an edge of `G`. -/
private def involSubgraph (G : SimpleGraph V) (f : V → V) : G.Subgraph where
  verts := Set.univ
  Adj a b := G.Adj a b ∧ (b = f a ∨ a = f b)
  adj_sub h := h.1
  edge_vert _ := Set.mem_univ _
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩

/-- `involSubgraph G f` is a perfect matching as soon as `f` is an involution moving every
vertex along an edge of `G`: the unique neighbour of `v` is `f v`, since `v = f w` forces
`w = f v`. -/
private theorem involSubgraph_isPerfectMatching {G : SimpleGraph V} {f : V → V}
    (hadj : ∀ v, G.Adj v (f v)) (hinv : ∀ v, f (f v) = v) :
    (involSubgraph G f).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro v
  refine ⟨f v, ⟨hadj v, Or.inl rfl⟩, ?_⟩
  intro w hw
  rcases hw.2 with h | h
  · exact h
  · rw [h, hinv]

/-- **Perfect matchings are involutions.**  A perfect matching of `G` is the same data as a map
`f : V → V` with `v` and `f v` adjacent and `f ∘ f = id`; looplessness of `G` then makes `f`
fixed-point-free automatically.  This is the form in which the symmetric-difference argument
manipulates matchings, and it applies verbatim to `doubleCover G` on `V × Bool`. -/
private theorem perfectMatchingCount_eq_card_invol [Fintype V] (G : SimpleGraph V) :
    perfectMatchingCount G
      = Nat.card {f : V → V // (∀ v, G.Adj v (f v)) ∧ ∀ v, f (f v) = v} := by
  rw [perfectMatchingCount]
  refine (Nat.card_eq_of_bijective
    (fun f => (⟨involSubgraph G f.1, involSubgraph_isPerfectMatching f.2.1 f.2.2⟩ :
      {M : G.Subgraph // M.IsPerfectMatching})) ⟨?_, ?_⟩).symm
  · rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    simp only [Subtype.mk_eq_mk] at h
    refine Subtype.ext (funext fun v => ?_)
    show f v = g v
    have h1 : (involSubgraph G g).Adj v (f v) := by
      rw [← h]; exact ⟨hf.1 v, Or.inl rfl⟩
    rcases h1.2 with h2 | h2
    · exact h2
    · have e : g (g (f v)) = f v := hg.2 (f v)
      rw [← h2] at e
      exact e.symm
  · rintro ⟨M, hM⟩
    have hu : ∀ v : V, ∃! w, M.Adj v w := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM
    choose f hf hfu using hu
    have hadj : ∀ v, G.Adj v (f v) := fun v => M.adj_sub (hf v)
    have hinv : ∀ v, f (f v) = v := fun v => (hfu (f v) v (hf v).symm).symm
    refine ⟨⟨f, hadj, hinv⟩, Subtype.ext ?_⟩
    refine SimpleGraph.Subgraph.ext ((Set.eq_univ_iff_forall.mpr hM.2).symm) ?_
    funext a b
    simp only [eq_iff_iff]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · rw [h2]; exact hf a
      · rw [h2]; exact (hf b).symm
    · intro hab
      exact ⟨M.adj_sub hab, Or.inl (hfu a b hab)⟩

/-- **The union of two perfect matchings has no odd closed walk.**  For fixed-point-free
involutions `m` and `n` write `s = m ∘ n`; the `s`-orbits are the two colour classes of each
component of `m ∪ n`, so no vertex shares its `s`-orbit with its `m`-partner.

The halving argument is the whole content: an orbit step `s^[k] v = m v` yields a fixed point of
`m` at `s^[k/2] v` when `k` is even, and a fixed point of `n` at `s^[(k-1)/2] v` when `k` is
odd.  A walk in the orbit relation, which may run either way along `s`, is reduced to a one-sided
orbit step by cancelling the common prefix. -/
private theorem not_orbit_rel_invol (m n : V → V) (R : V → V → Prop)
    (hR : ∀ x y, R x y ↔ (y = m (n x) ∨ x = m (n y)))
    (hm : ∀ v, m (m v) = v) (hn : ∀ v, n (n v) = v)
    (hm' : ∀ v, m v ≠ v) (hn' : ∀ v, n v ≠ v) (v : V) :
    ¬ Relation.ReflTransGen R v (m v) := by
  obtain ⟨s, hsd⟩ : ∃ s : V → V, ∀ x, s x = m (n x) := ⟨_, fun _ => rfl⟩
  obtain ⟨t, htd⟩ : ∃ t : V → V, ∀ x, t x = n (m x) := ⟨_, fun _ => rfl⟩
  have hminj : Function.Injective m := fun a b h => by rw [← hm a, h, hm b]
  have hninj : Function.Injective n := fun a b h => by rw [← hn a, h, hn b]
  have hsinj : Function.Injective s := by
    intro a b h
    rw [hsd a, hsd b] at h
    exact hninj (hminj h)
  have hts : ∀ x, t (s x) = x := by intro x; simp only [hsd, htd, hm, hn]
  have hms1 : ∀ x, m (s x) = n x := by intro x; simp only [hsd, hm]
  have htm : ∀ x, t (m x) = n x := by intro x; simp only [htd, hm]
  have hcomm : ∀ (j : ℕ) (y : V), s (s^[j] y) = s^[j] (s y) := fun j y =>
    (Function.iterate_succ_apply' s j y).symm.trans (Function.iterate_succ_apply s j y)
  have htiters : ∀ (j : ℕ) (x : V), t^[j] (s^[j] x) = x := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [Function.iterate_succ_apply (f := s), Function.iterate_succ_apply' (f := t), ih, hts]
  have hms : ∀ (j : ℕ) (x : V), m (s^[j] x) = t^[j] (m x) := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        simp only [Function.iterate_succ_apply]
        rw [ih (s x), hms1, htm]
  have hkey : ∀ (k : ℕ) (x : V), s^[k] x ≠ m x := by
    intro k x h
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · have ha : s^[j] (s^[j] x) = m x := by
        rw [← Function.iterate_add_apply, ← hj]; exact h
      have hfix : m (s^[j] x) = s^[j] x := by rw [hms j x, ← ha, htiters]
      exact hm' _ hfix
    · have ha : s^[j] (s (s^[j] x)) = m x := by
        rw [hcomm, ← Function.iterate_succ_apply (f := s), ← Function.iterate_add_apply]
        simp only [Nat.succ_eq_add_one]
        rw [show j + (j + 1) = k by omega]
        exact h
      have hfix : m (s^[j] x) = s (s^[j] x) := by rw [hms j x, ← ha, htiters]
      rw [hsd] at hfix
      exact hn' _ (hminj hfix).symm
  have horb_ex : ∀ a b, Relation.ReflTransGen R a b → ∃ p q : ℕ, s^[p] a = s^[q] b := by
    intro a b h
    induction h with
    | refl => exact ⟨0, 0, rfl⟩
    | @tail x y hax hxy ih =>
        obtain ⟨p, q, hpq⟩ := ih
        rcases (hR x y).mp hxy with hc | hc
        · refine ⟨p + 1, q, ?_⟩
          rw [hc, ← hsd, Function.iterate_succ_apply' (f := s), hpq, hcomm]
        · refine ⟨p, q + 1, ?_⟩
          rw [hpq, hc, ← hsd, Function.iterate_succ_apply]
  intro h
  obtain ⟨p, q, hpq⟩ := horb_ex v (m v) h
  rcases le_total p q with hle | hle
  · obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hle
    rw [hr, Function.iterate_add_apply] at hpq
    have he := hsinj.iterate p hpq
    exact hkey r (m v) (by rw [hm]; exact he.symm)
  · obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hle
    rw [hr, Function.iterate_add_apply] at hpq
    exact hkey r v (hsinj.iterate q hpq)

/-- **The union of two perfect matchings is bipartite, canonically.**  For fixed-point-free
involutions `m` and `n` there is a two-colouring `c` of `V` flipping across every `m`-edge and
every `n`-edge, normalised so that the least-rank vertex of each component gets `true`.

The colour of `v` records whether the least-rank vertex of `v`'s component lies in the
`m ∘ n`-orbit of `v` or in the other orbit of that component; `not_orbit_rel_invol` is what makes
those two orbits distinct, and the normalisation is what makes the colouring depend only on the
unordered pair `{m, n}`.  As in `indepSetCount_sq_le_doubleCover` the least-rank vertex enters as
a bare existential rather than as a representative function. -/
private theorem exists_flip_coloring [Fintype V] (rk : V → ℕ)
    (hrk : Function.Injective rk) (m n : V → V)
    (hm : ∀ v, m (m v) = v) (hn : ∀ v, n (n v) = v)
    (hm' : ∀ v, m v ≠ v) (hn' : ∀ v, n v ≠ v) :
    ∃ c : V → Bool, (∀ v, c (m v) = !c v) ∧ (∀ v, c (n v) = !c v) ∧
      ∀ u, (∀ w, Relation.ReflTransGen (fun x y => y = m x ∨ y = n x) w u → rk u ≤ rk w) →
        c u = true := by
  classical
  obtain ⟨R, hRd⟩ : ∃ R : V → V → Prop, ∀ x y, R x y ↔ (y = m (n x) ∨ x = m (n y)) :=
    ⟨_, fun _ _ => Iff.rfl⟩
  obtain ⟨O, hOd⟩ : ∃ O : V → V → Prop, ∀ x y, O x y ↔ Relation.ReflTransGen R x y :=
    ⟨_, fun _ _ => Iff.rfl⟩
  obtain ⟨K, hKd⟩ : ∃ K : V → V → Prop,
      ∀ x y, K x y ↔ Relation.ReflTransGen (fun a b => b = m a ∨ b = n a) x y :=
    ⟨_, fun _ _ => Iff.rfl⟩
  -- basic closure properties of the orbit relation `O`
  have hOrefl : ∀ v, O v v := fun v => (hOd v v).mpr Relation.ReflTransGen.refl
  have hOtrans : ∀ a b c, O a b → O b c → O a c := fun a b c hab hbc =>
    (hOd a c).mpr (((hOd a b).mp hab).trans ((hOd b c).mp hbc))
  have hOsymm : ∀ a b, O a b → O b a := by
    intro a b hab
    rw [hOd] at hab ⊢
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | @tail x y _ hxy ih =>
        refine (Relation.ReflTransGen.single ?_).trans ih
        rw [hRd] at hxy ⊢
        exact hxy.symm
  have hOstep : ∀ v, O v (m (n v)) := fun v =>
    (hOd _ _).mpr (Relation.ReflTransGen.single ((hRd _ _).mpr (Or.inl rfl)))
  have hOnm : ∀ v, O (n v) (m v) := fun v =>
    (hOd _ _).mpr (Relation.ReflTransGen.single ((hRd _ _).mpr (Or.inl (by rw [hn]))))
  have hOnot : ∀ v, ¬ O v (m v) := by
    intro v hv
    exact not_orbit_rel_invol m n R hRd hm hn hm' hn' v ((hOd _ _).mp hv)
  -- basic closure properties of the component relation `K`
  have hKrefl : ∀ v, K v v := fun v => (hKd v v).mpr Relation.ReflTransGen.refl
  have hKtrans : ∀ a b c, K a b → K b c → K a c := fun a b c hab hbc =>
    (hKd a c).mpr (((hKd a b).mp hab).trans ((hKd b c).mp hbc))
  have hKsymm : ∀ a b, K a b → K b a := by
    intro a b hab
    rw [hKd] at hab ⊢
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | @tail x y _ hxy ih =>
        refine (Relation.ReflTransGen.single ?_).trans ih
        rcases hxy with h | h
        · exact Or.inl (by rw [h, hm])
        · exact Or.inr (by rw [h, hn])
  have hKm : ∀ v, K v (m v) := fun v => (hKd _ _).mpr (Relation.ReflTransGen.single (Or.inl rfl))
  have hKn : ∀ v, K v (n v) := fun v => (hKd _ _).mpr (Relation.ReflTransGen.single (Or.inr rfl))
  have hOK : ∀ a b, O a b → K a b := by
    intro a b hab
    rw [hOd] at hab
    induction hab with
    | refl => exact hKrefl _
    | @tail x y _ hxy ih =>
        refine hKtrans _ _ _ ih ?_
        rcases (hRd x y).mp hxy with h | h
        · exact h ▸ hKtrans _ _ _ (hKn x) (hKm (n x))
        · exact hKsymm _ _ (h ▸ hKtrans _ _ _ (hKn y) (hKm (n y)))
  -- least-rank element of an orbit
  have hmin : ∀ v : V, ∃ x, O x v ∧ ∀ w, O w v → rk x ≤ rk w := by
    intro v
    obtain ⟨x, hx, hxmin⟩ := Finset.exists_min_image (univ.filter fun x => O x v) rk
      ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hOrefl v⟩⟩
    rw [Finset.mem_filter] at hx
    exact ⟨x, hx.2, fun w hw => hxmin w (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩)⟩
  obtain ⟨P, hPd⟩ : ∃ P : V → Prop,
      ∀ v, P v ↔ (∃ x, O x v ∧ ∀ w, O w (m v) → rk x < rk w) := ⟨_, fun _ => Iff.rfl⟩
  have hPchar : ∀ (v a b : V), O a v → (∀ w, O w v → rk a ≤ rk w) → O b (m v) →
      (∀ w, O w (m v) → rk b ≤ rk w) → (P v ↔ rk a < rk b) := by
    intro v a b hav hamin hbmv hbmin
    rw [hPd]
    refine ⟨?_, fun hlt => ⟨a, hav, fun w hw => lt_of_lt_of_le hlt (hbmin w hw)⟩⟩
    rintro ⟨x, hx, hxlt⟩
    exact lt_of_le_of_lt (hamin x hx) (hxlt b hbmv)
  have hxor : ∀ v, P v ↔ ¬ P (m v) := by
    intro v
    obtain ⟨a, hav, hamin⟩ := hmin v
    obtain ⟨b, hbmv, hbmin⟩ := hmin (m v)
    have h1 : P v ↔ rk a < rk b := hPchar v a b hav hamin hbmv hbmin
    have h2 : P (m v) ↔ rk b < rk a := by
      refine hPchar (m v) b a hbmv hbmin ?_ ?_
      · rw [hm]; exact hav
      · rw [hm]; exact hamin
    have hne : rk a ≠ rk b := by
      intro he
      have : a = b := hrk he
      exact hOnot v (hOtrans v a (m v) (hOsymm a v hav) (this ▸ hbmv))
    rw [h1, h2]
    omega
  have hPmn : ∀ v, P (m (n v)) ↔ P v := by
    intro v
    rw [hPd, hPd, hm]
    constructor
    · rintro ⟨x, hx, hxlt⟩
      exact ⟨x, hOtrans _ _ _ hx (hOsymm _ _ (hOstep v)),
        fun w hw => hxlt w (hOtrans _ _ _ hw (hOsymm _ _ (hOnm v)))⟩
    · rintro ⟨x, hx, hxlt⟩
      exact ⟨x, hOtrans _ _ _ hx (hOstep v),
        fun w hw => hxlt w (hOtrans _ _ _ hw (hOnm v))⟩
  refine ⟨fun v => decide (P v), ?_, ?_, ?_⟩
  · intro v
    show decide (P (m v)) = !decide (P v)
    by_cases hp : P v
    · rw [decide_eq_false ((hxor v).mp hp), decide_eq_true hp]; rfl
    · rw [decide_eq_true (not_not.mp fun hc => hp ((hxor v).mpr hc)), decide_eq_false hp]; rfl
  · intro v
    show decide (P (n v)) = !decide (P v)
    have hnv : P (n v) ↔ ¬ P v := by
      have e1 : P (m (n v)) ↔ ¬ P (n v) := by
        have := hxor (m (n v)); rw [hm] at this; exact this
      have e2 := hPmn v
      tauto
    by_cases hp : P v
    · rw [decide_eq_false (fun hc => (hnv.mp hc) hp), decide_eq_true hp]; rfl
    · rw [decide_eq_true (hnv.mpr hp), decide_eq_false hp]; rfl
  · intro u hu
    have hu' : ∀ w, K w u → rk u ≤ rk w := fun w hw => hu w ((hKd w u).mp hw)
    show decide (P u) = true
    refine decide_eq_true ((hPd u).mpr ⟨u, hOrefl u, fun w hw => ?_⟩)
    have h1 : K w u := hKtrans _ _ _ (hOK _ _ hw) (hKsymm _ _ (hKm u))
    rcases eq_or_lt_of_le (hu' w h1) with he | hlt
    · exact absurd ((hrk he.symm) ▸ hw) (hOnot u)
    · exact hlt

/-- **Walk parity fixes a two-colouring.**  Two `Bool`-valued functions that both flip across
every step of `R` and agree at one end of an `R`-walk agree at the other. -/
private theorem flip_agree_of_reflTransGen {R : V → V → Prop} (c d : V → Bool)
    (hc : ∀ x y, R x y → c y = !c x) (hd : ∀ x y, R x y → d y = !d x)
    {u v : V} (h : Relation.ReflTransGen R u v) (hu : c u = d u) : c v = d v := by
  induction h with
  | refl => exact hu
  | tail _ hbc ih => rw [hc _ _ hbc, hd _ _ hbc, ih]

/-- **The second half of Kahn–Lovász** (Zhao, Corollary 10.2.2): squaring the perfect-matching
count is dominated by passing to the double cover.

With `perfectMatchingCount_doubleCover` — which identifies the right-hand side with the permanent
of the adjacency matrix — and the proved `permanent_le_prod_factorial` (Brégman–Minc), this
completes the reduction of Corollary 10.2.2 to Chapter 10's entropy bound.

**The route is the symmetric-difference argument, the same device that proves
`indepSetCount_sq_le_doubleCover`.**  Given perfect matchings `M` and `N`, the edges of `M ∆ N`
form a disjoint union of even alternating cycles, with `M ∩ N` untouched.  Orienting each cycle —
sending it into one side of the cover or the other according to a canonical representative, say
its least-rank vertex — produces a perfect matching of `doubleCover G`, and the map is injective
because the two sides recover `M ∩ N`, the cycle decomposition, and the per-cycle choice.

This was recorded as *verified but unstated* from 2026-09-17 because the naive map fails —
sending `(u, false)` to `(M u, true)` and `(u, true)` to `(N u, false)` is not a matching unless
`M = N`, since `(u, false)` is then claimed both as a source and as the target of `(N u, true)`.
The component-orientation device is what repairs it, and it only became available once
`indepSetCount_sq_le_doubleCover` demonstrated it on independent sets. -/
theorem perfectMatchingCount_sq_le_doubleCover [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    perfectMatchingCount G ^ 2 ≤ perfectMatchingCount (doubleCover G) := by
  classical
  obtain ⟨rk, hrk⟩ : ∃ rk : V → ℕ, Function.Injective rk :=
    ⟨fun v => ((Fintype.equivFin V) v : ℕ), fun a b h =>
      (Fintype.equivFin V).injective (Fin.val_injective h)⟩
  rw [perfectMatchingCount_eq_card_invol G, perfectMatchingCount_eq_card_invol (doubleCover G),
    pow_two, ← Nat.card_prod]
  have hcol : ∀ q : {f : V → V // (∀ v, G.Adj v (f v)) ∧ ∀ v, f (f v) = v} ×
      {f : V → V // (∀ v, G.Adj v (f v)) ∧ ∀ v, f (f v) = v},
      ∃ c : V → Bool, (∀ v, c (q.1.1 v) = !c v) ∧ (∀ v, c (q.2.1 v) = !c v) ∧
        ∀ u, (∀ w, Relation.ReflTransGen (fun x y => y = q.1.1 x ∨ y = q.2.1 x) w u →
          rk u ≤ rk w) → c u = true :=
    fun q => exists_flip_coloring rk hrk q.1.1 q.2.1 q.1.2.2 q.2.2.2
      (fun v => (G.ne_of_adj (q.1.2.1 v)).symm) (fun v => (G.ne_of_adj (q.2.2.1 v)).symm)
  choose col hcol1 hcol2 hcol3 using hcol
  obtain ⟨F, hF⟩ : ∃ F : ({f : V → V // (∀ v, G.Adj v (f v)) ∧ ∀ v, f (f v) = v} ×
      {f : V → V // (∀ v, G.Adj v (f v)) ∧ ∀ v, f (f v) = v}) → (V × Bool → V × Bool),
      ∀ q (v : V) (b : Bool),
        F q (v, b) = (if col q v = b then q.1.1 v else q.2.1 v, !b) :=
    ⟨fun q p => (if col q p.1 = p.2 then q.1.1 p.1 else q.2.1 p.1, !p.2), fun _ _ _ => rfl⟩
  have hFadj : ∀ q p, (doubleCover G).Adj p (F q p) := by
    intro q p
    obtain ⟨v, b⟩ := p
    rw [hF, doubleCover_adj]
    refine ⟨?_, by simp⟩
    by_cases hc : col q v = b
    · simpa [hc] using q.1.2.1 v
    · simpa [hc] using q.2.2.1 v
  have hFinv : ∀ q p, F q (F q p) = p := by
    intro q p
    obtain ⟨v, b⟩ := p
    rw [hF q v b]
    by_cases hc : col q v = b
    · rw [if_pos hc, hF q (q.1.1 v) (!b), if_pos (by rw [hcol1 q v, hc]), q.1.2.2 v, Bool.not_not]
    · have hcb : col q v = !b := by revert hc; cases b <;> cases col q v <;> simp
      rw [if_neg hc, hF q (q.2.1 v) (!b),
        if_neg (by rw [hcol2 q v, hcb, Bool.not_not]; simp), q.2.2.2 v, Bool.not_not]
  refine Nat.card_le_card_of_injective (fun q => ⟨F q, hFadj q, hFinv q⟩) ?_
  intro q₁ q₂ heq
  have hFeq : F q₁ = F q₂ := congrArg Subtype.val heq
  have hE : ∀ (v : V) (b : Bool),
      (if col q₁ v = b then q₁.1.1 v else q₁.2.1 v)
        = (if col q₂ v = b then q₂.1.1 v else q₂.2.1 v) := by
    intro v b
    have h := congrFun hFeq (v, b)
    rw [hF, hF] at h
    exact ((Prod.mk.injEq _ _ _ _).mp h).1
  have hA : ∀ v, col q₁ v = col q₂ v → q₁.1.1 v = q₂.1.1 v ∧ q₁.2.1 v = q₂.2.1 v := by
    intro v hcv
    have e1 := hE v (col q₁ v)
    have e2 := hE v (!(col q₁ v))
    rw [if_pos rfl, if_pos hcv.symm] at e1
    rw [if_neg (by simp), if_neg (by rw [← hcv]; simp)] at e2
    exact ⟨e1, e2⟩
  have hB : ∀ v, col q₁ v ≠ col q₂ v → q₁.1.1 v = q₂.2.1 v ∧ q₁.2.1 v = q₂.1.1 v := by
    intro v hcv
    have hcb : col q₂ v = !(col q₁ v) := by
      revert hcv; cases col q₁ v <;> cases col q₂ v <;> simp
    have e1 := hE v (col q₁ v)
    have e2 := hE v (!(col q₁ v))
    rw [if_pos rfl, if_neg (by rw [hcb]; simp)] at e1
    rw [if_neg (by simp), if_pos hcb] at e2
    exact ⟨e1, e2⟩
  have hsame : ∀ x y : V, (y = q₁.1.1 x ∨ y = q₁.2.1 x) ↔ (y = q₂.1.1 x ∨ y = q₂.2.1 x) := by
    intro x y
    by_cases hcv : col q₁ x = col q₂ x
    · obtain ⟨h1, h2⟩ := hA x hcv; rw [h1, h2]
    · obtain ⟨h1, h2⟩ := hB x hcv; rw [h1, h2]; tauto
  have hf1 : ∀ x y : V, (y = q₁.1.1 x ∨ y = q₁.2.1 x) → col q₁ y = !col q₁ x := by
    intro x y h
    rcases h with h | h
    · rw [h]; exact hcol1 q₁ x
    · rw [h]; exact hcol2 q₁ x
  have hf2 : ∀ x y : V, (y = q₁.1.1 x ∨ y = q₁.2.1 x) → col q₂ y = !col q₂ x := by
    intro x y h
    rcases (hsame x y).mp h with h' | h'
    · rw [h']; exact hcol1 q₂ x
    · rw [h']; exact hcol2 q₂ x
  have hmono : ∀ w u : V,
      Relation.ReflTransGen (fun x y => y = q₂.1.1 x ∨ y = q₂.2.1 x) w u →
      Relation.ReflTransGen (fun x y => y = q₁.1.1 x ∨ y = q₁.2.1 x) w u := by
    intro w u h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact ih.tail ((hsame _ _).mpr hbc)
  have hcoleq : ∀ v, col q₁ v = col q₂ v := by
    intro v
    obtain ⟨u, hu, humin⟩ := Finset.exists_min_image
      (univ.filter fun w =>
        Relation.ReflTransGen (fun x y => y = q₁.1.1 x ∨ y = q₁.2.1 x) w v) rk
      ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩⟩
    rw [Finset.mem_filter] at hu
    have humin' : ∀ w, Relation.ReflTransGen (fun x y => y = q₁.1.1 x ∨ y = q₁.2.1 x) w u →
        rk u ≤ rk w := fun w hw =>
      humin w (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw.trans hu.2⟩)
    have h1 : col q₁ u = true := hcol3 q₁ u humin'
    have h2 : col q₂ u = true := hcol3 q₂ u fun w hw =>
      humin' w (hmono w u hw)
    exact flip_agree_of_reflTransGen (col q₁) (col q₂) hf1 hf2 hu.2 (by rw [h1, h2])
  exact Prod.ext (Subtype.ext (funext fun v => (hA v (hcoleq v)).1))
    (Subtype.ext (funext fun v => (hA v (hcoleq v)).2))

end DoubleCover

/-! ### 10.4 Counting independent sets

Kahn's theorem and Kahn–Zhao (Theorem 10.4.12) bound the number of independent sets of a regular
graph by a power of the count for `K_{d,d}`.  Mathlib has `SimpleGraph.IsIndepSet` and
`SimpleGraph.indepNum`, the size of the *largest* independent set, but **no count of them**, so
`i(G)` is authored here.
-/

section IndepSetCount

variable {V : Type*} [Fintype V]

/-- `i(G)`, the number of independent sets of `G`, counting the empty set.

`Nat.card` rather than a `Finset.card`: `IsIndepSet` has no `DecidablePred` instance and this
project declares none.  For finite `V` the subtype is `Finite`, so the count is the honest
cardinality rather than `Nat.card`'s junk value. -/
noncomputable def indepSetCount (G : SimpleGraph V) : ℕ :=
  Nat.card {S : Finset V // G.IsIndepSet (S : Set V)}

/-- An independent set of `K_{d,d}` misses one of the two sides entirely: every crossing pair
is an edge, so a set meeting both sides is not independent. -/
private theorem isIndepSet_completeBipartiteGraph_iff_sideFree {d : ℕ}
    (S : Finset (Fin d ⊕ Fin d)) :
    (completeBipartiteGraph (Fin d) (Fin d)).IsIndepSet (S : Set (Fin d ⊕ Fin d)) ↔
      ((∀ x ∈ S, x.isLeft) ∨ (∀ x ∈ S, x.isRight)) := by
  rw [SimpleGraph.isIndepSet_iff]
  constructor
  · intro h
    by_cases hl : ∀ x ∈ S, Sum.isLeft x
    · exact Or.inl hl
    · refine Or.inr fun x hx => ?_
      simp only [not_forall] at hl
      obtain ⟨y, hy, hyl⟩ := hl
      cases x with
      | inr b => rfl
      | inl a =>
        cases y with
        | inl b => exact absurd rfl hyl
        | inr b =>
          exact ((h (by simpa using hx) (by simpa using hy) (by simp)) (by simp)).elim
  · intro h x hx y hy _
    simp only [Finset.mem_coe] at hx hy
    rcases h with hl | hl
    · cases x <;> cases y <;> simp_all
    · cases x <;> cases y <;> simp_all

/-- The subsets of `Fin d ⊕ Fin d` contained in the left side are the `2 ^ d` subsets of it. -/
private theorem card_filter_forall_isLeft_pow (d : ℕ) :
    #(univ.filter fun S : Finset (Fin d ⊕ Fin d) => ∀ x ∈ S, x.isLeft) = 2 ^ d := by
  have h : (univ.filter fun S : Finset (Fin d ⊕ Fin d) => ∀ x ∈ S, x.isLeft)
      = (univ.map (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d)).powerset := by
    ext S; simp [Finset.subset_iff, Sum.isLeft_iff]
  rw [h, Finset.card_powerset, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- The subsets of `Fin d ⊕ Fin d` contained in the right side are the `2 ^ d` subsets of it. -/
private theorem card_filter_forall_isRight_pow (d : ℕ) :
    #(univ.filter fun S : Finset (Fin d ⊕ Fin d) => ∀ x ∈ S, x.isRight) = 2 ^ d := by
  have h : (univ.filter fun S : Finset (Fin d ⊕ Fin d) => ∀ x ∈ S, x.isRight)
      = (univ.map (Function.Embedding.inr : Fin d ↪ Fin d ⊕ Fin d)).powerset := by
    ext S; simp [Finset.subset_iff, Sum.isRight_iff]
  rw [h, Finset.card_powerset, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- The two sides of `Fin d ⊕ Fin d` share only the empty subset. -/
private theorem filter_forall_isLeft_inter_isRight_eq (d : ℕ) :
    (univ.filter fun S : Finset (Fin d ⊕ Fin d) => ∀ x ∈ S, x.isLeft) ∩
      (univ.filter fun S : Finset (Fin d ⊕ Fin d) => ∀ x ∈ S, x.isRight) = {∅} := by
  ext S
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  refine ⟨fun ⟨h₁, h₂⟩ => Finset.eq_empty_of_forall_notMem fun x hx =>
    not_isLeft_and_isRight ⟨h₁ x hx, h₂ x hx⟩, ?_⟩
  rintro rfl
  simp

/-- **`i(K_{d,d}) = 2^{d+1} - 1`.**

An independent set of the complete bipartite graph cannot meet both sides, since every crossing
pair is an edge; so it is a subset of one side or the other, and the two families overlap in the
empty set alone.  Hence `2^d + 2^d - 1`.

This is the base of Kahn–Zhao's bound `i(G) ≤ i(K_{d,d})^{n/(2d)}` for `d`-regular `G` on `n`
vertices, so the exponent there is what makes the constant matter. -/
theorem indepSetCount_completeBipartiteGraph (d : ℕ) :
    indepSetCount (completeBipartiteGraph (Fin d) (Fin d)) = 2 ^ (d + 1) - 1 := by
  have hcount : indepSetCount (completeBipartiteGraph (Fin d) (Fin d))
      = #((univ.filter fun S : Finset (Fin d ⊕ Fin d) => ∀ x ∈ S, x.isLeft) ∪
          (univ.filter fun S : Finset (Fin d ⊕ Fin d) => ∀ x ∈ S, x.isRight)) := by
    rw [indepSetCount,
      Nat.card_congr (Equiv.subtypeEquivRight isIndepSet_completeBipartiteGraph_iff_sideFree),
      Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_or]
  have hio := Finset.card_union_add_card_inter
    (univ.filter fun S : Finset (Fin d ⊕ Fin d) => ∀ x ∈ S, x.isLeft)
    (univ.filter fun S : Finset (Fin d ⊕ Fin d) => ∀ x ∈ S, x.isRight)
  rw [filter_forall_isLeft_inter_isRight_eq, Finset.card_singleton,
    card_filter_forall_isLeft_pow, card_filter_forall_isRight_pow] at hio
  rw [hcount, pow_succ]
  omega

/-- **Gibbs' inequality with a per-value bonus.**  For a probability weighting `w` on `A` and
positive weights `b`, `∑ (-w log₂ w + w log₂ b) ≤ log₂ (∑ b)`.  Taking `b = 1` recovers
`sum_negMulLogb_le_logb_card`; the extra term is what lets an entropy be traded against an
expectation.  The proof is the same one: `Real.log_le_sub_one_of_pos` at `b s / (w s * ∑ b)`,
summed over `A`, where the right-hand side telescopes to zero. -/
private theorem sum_negMulLogb_add_mul_logb_le {σ : Type*} (A : Finset σ) (w b : σ → ℝ)
    (hw0 : ∀ s ∈ A, 0 ≤ w s) (hw1 : ∑ s ∈ A, w s = 1) (hb : ∀ s ∈ A, 0 < b s) :
    ∑ s ∈ A, (-w s * Real.logb 2 (w s) + w s * Real.logb 2 (b s))
      ≤ Real.logb 2 (∑ s ∈ A, b s) := by
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hne : A.Nonempty := by
    rcases A.eq_empty_or_nonempty with rfl | h
    · rw [Finset.sum_empty] at hw1
      exact absurd hw1 (by norm_num)
    · exact h
  have hM : (0 : ℝ) < ∑ s ∈ A, b s := Finset.sum_pos hb hne
  have hMne : (∑ s ∈ A, b s) ≠ 0 := ne_of_gt hM
  have key : ∀ x y : ℝ, 0 ≤ x → 0 < y →
      -x * Real.log x + x * Real.log y
        ≤ x * Real.log (∑ s ∈ A, b s) + (y / (∑ s ∈ A, b s) - x) := by
    intro x y hx hy
    rcases hx.eq_or_lt with rfl | hx0
    · simp only [neg_zero, zero_mul, Real.log_zero, mul_zero, zero_add, sub_zero]
      positivity
    · have hxm : (0 : ℝ) < x * (∑ s ∈ A, b s) := mul_pos hx0 hM
      have h1 : Real.log (y / (x * (∑ s ∈ A, b s))) ≤ y / (x * (∑ s ∈ A, b s)) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hy hxm)
      have h2 := mul_le_mul_of_nonneg_left h1 hx
      rw [Real.log_div (ne_of_gt hy) (ne_of_gt hxm), Real.log_mul (ne_of_gt hx0) hMne] at h2
      have h3 : x * (y / (x * (∑ s ∈ A, b s)) - 1) = y / (∑ s ∈ A, b s) - x := by
        field_simp
      rw [h3] at h2
      nlinarith [h2]
  have hsum : ∑ s ∈ A, (-w s * Real.log (w s) + w s * Real.log (b s))
      ≤ Real.log (∑ s ∈ A, b s) := by
    have hle : ∑ s ∈ A, (-w s * Real.log (w s) + w s * Real.log (b s))
        ≤ ∑ s ∈ A, (w s * Real.log (∑ t ∈ A, b t) + (b s / (∑ t ∈ A, b t) - w s)) :=
      Finset.sum_le_sum fun s hs => key (w s) (b s) (hw0 s hs) (hb s hs)
    have hrhs : ∑ s ∈ A, (w s * Real.log (∑ t ∈ A, b t) + (b s / (∑ t ∈ A, b t) - w s))
        = Real.log (∑ s ∈ A, b s) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul, Finset.sum_sub_distrib,
        hw1, ← Finset.sum_div, div_self hMne, sub_self, add_zero]
    exact hrhs ▸ hle
  calc ∑ s ∈ A, (-w s * Real.logb 2 (w s) + w s * Real.logb 2 (b s))
      = (∑ s ∈ A, (-w s * Real.log (w s) + w s * Real.log (b s))) * (Real.log 2)⁻¹ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun s _ => by rw [Real.logb, Real.logb]; ring
    _ ≤ Real.log (∑ s ∈ A, b s) * (Real.log 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hsum (le_of_lt (inv_pos.mpr hL))
    _ = Real.logb 2 (∑ s ∈ A, b s) := by rw [Real.logb]; ring


/-- Indexing a tuple by `(univ : Finset W)` rather than by `W` does not change its entropy. -/
private theorem entropy_pi_univ_eq {Ω W : Type*} [Fintype Ω] [Fintype W] [DecidableEq W]
    (p : Ω → ℝ) (X : W → Ω → Bool) :
    entropy p (fun ω (j : (univ : Finset W)) => X j.1 ω) = entropy p (fun ω i => X i ω) := by
  have hfu : Function.Injective (fun g : W → Bool => fun j : (univ : Finset W) => g j.1) := by
    intro g g' h
    funext i
    exact congrFun h ⟨i, Finset.mem_univ i⟩
  exact entropy_comp_inj (p := p) hfu (fun ω i => X i ω)

/-- **Shearer's lemma for a sub-family.**  `shearer` bounds the entropy of the *whole* tuple, so
it needs every index covered `k` times.  Here the sets `D j` all lie inside a fixed `C`, every
index of `C` is covered `k` times, and the conclusion bounds `H(X_C)` alone.  This is `shearer`
with the index type taken to be `↥C`, the covering family pulled back along `↥C → W`. -/
private theorem shearer_subset_le {Ω W : Type*} [Fintype Ω] [Fintype W] [DecidableEq W]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (X : W → Ω → Bool)
    (C : Finset W) (D : W → Finset W) (k : ℕ) (hD : ∀ j, D j ⊆ C)
    (hk : ∀ i ∈ C, k ≤ #(univ.filter fun j : W => i ∈ D j)) :
    (k : ℝ) * entropy p (fun ω (i : C) => X i.1 ω)
      ≤ ∑ j : W, entropy p (fun ω (u : D j) => X u.1 ω) := by
  have hcov : ∀ i : ↥C, k ≤ #(univ.filter fun j : W =>
      i ∈ univ.filter fun i' : ↥C => i'.1 ∈ D j) := by
    intro i
    have he : (univ.filter fun j : W => i ∈ univ.filter fun i' : ↥C => i'.1 ∈ D j)
        = (univ.filter fun j : W => i.1 ∈ D j) := by
      ext j; simp
    rw [he]
    exact hk i.1 i.2
  have hsh := shearer (ι := ↥C) (α := fun _ => Bool) (κ := W) p hp hp1
    (fun (i : ↥C) ω => X i.1 ω) (fun j => univ.filter fun i' : ↥C => i'.1 ∈ D j) k hcov
  refine hsh.trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
  have hsurj : Function.Surjective
      (fun x : ↥(univ.filter fun i' : ↥C => i'.1 ∈ D j) =>
        (⟨x.1.1, (Finset.mem_filter.mp x.2).2⟩ : ↥(D j))) := by
    intro u
    exact ⟨⟨⟨u.1, hD j u.2⟩, by simp [u.2]⟩, rfl⟩
  exact entropy_comp_inj (p := p) (hsurj.injective_comp_right)
    (fun ω (u : ↥(D j)) => X u.1 ω)

/-- An injective rank on `W` that puts every `side`-`false` vertex before every `side`-`true`
one; this is the vertex order the chain rule is applied along. -/
private theorem exists_rank_side_lt {W : Type*} [Fintype W] (side : W → Bool) :
    ∃ r : W → ℕ, Function.Injective r ∧
      ∀ u v : W, side u = false → side v = true → r u < r v := by
  refine ⟨fun v => (if side v = true then Fintype.card W else 0)
      + ((Fintype.equivFin W) v : ℕ), ?_, ?_⟩
  · intro u v huv
    have hu := ((Fintype.equivFin W) u).isLt
    have hv := ((Fintype.equivFin W) v).isLt
    refine (Fintype.equivFin W).injective (Fin.val_injective ?_)
    by_cases h1 : side u = true <;> by_cases h2 : side v = true <;>
      simp only [h1, h2, Bool.false_eq_true, if_true, if_false] at huv <;> omega
  · intro u v hu hv
    have h := ((Fintype.equivFin W) u).isLt
    simp only [hu, hv, if_true, if_false, Bool.false_eq_true]
    omega

/-- **The chain rule across a cut.**  If the rank `r` orders `C` before its complement, then
`H(X) - H(X_C)`, which is `H(X_{Cᶜ} ∣ X_C)`, is at most the sum over `j ∉ C` of
`H(X_j ∣ X_{D j})` for any sets `D j` of coordinates preceding `j`.  The two chain rules along
`r`, over `univ` and over `C`, share their `C`-terms; the remaining terms are then cut down by
`condEntropy_pi_le`. -/
private theorem entropy_sub_le_sum_cond_rank {Ω W : Type*} [Fintype Ω] [Fintype W]
    [DecidableEq W] {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (X : W → Ω → Bool)
    (C : Finset W) (D : W → Finset W) (r : W → ℕ) (hr : Function.Injective r)
    (hD : ∀ j ∈ univ \ C, D j ⊆ univ.filter fun x => r x < r j)
    (hCr : ∀ v ∈ C, (univ.filter fun x => r x < r v) = C.filter fun x => r x < r v) :
    entropy p (fun ω i => X i ω) - entropy p (fun ω (i : C) => X i.1 ω)
      ≤ ∑ j ∈ univ \ C, condEntropy p (X j) (fun ω (u : D j) => X u.1 ω) := by
  have h1 := entropy_pi_eq_sum_condEntropy (p := p) hp hp1 X hr univ
  have h2 := entropy_pi_eq_sum_condEntropy (p := p) hp hp1 X hr C
  rw [entropy_pi_univ_eq] at h1
  have h3 : ∑ i ∈ C, condEntropy p (X i)
        (fun ω (j : (C.filter fun x => r x < r i)) => X j.1 ω)
      = ∑ i ∈ C, condEntropy p (X i)
        (fun ω (j : (univ.filter fun x => r x < r i)) => X j.1 ω) :=
    Finset.sum_congr rfl fun i hi => by rw [hCr i hi]
  have hsplit := Finset.sum_sdiff (f := fun i => condEntropy p (X i)
      (fun ω (j : (univ.filter fun x => r x < r i)) => X j.1 ω)) (Finset.subset_univ C)
  refine le_trans (le_of_eq ?_)
    (Finset.sum_le_sum fun i hi => condEntropy_pi_le hp hp1 X (hD i hi) i)
  rw [h1, h2, h3]
  linarith [hsplit]

/-- **The local bound**, the step where `i(K_{d,d})` enters.  Let `Z` record the independent set
on a `d`-element neighbourhood and let `Y` be the indicator of its common neighbour.  Then `Y`
can only be `1` when `Z` is identically `0`, and

    H(Z) + d · H(Y ∣ Z) ≤ log₂ (2 ^ (d + 1) - 1) = log₂ i(K_{d,d}).

`condEntropy_le_sum_probOf_mul_logb` gives `H(Y ∣ Z) ≤ P(Z = 0)`, since outside that fibre `Y`
is forced.  Then `sum_negMulLogb_add_mul_logb_le`, applied with bonus `2 ^ d` at `Z = 0` and `1`
elsewhere, bounds the total by `log₂ (2 ^ d + (2 ^ d - 1))`, and the `2 ^ d` subsets of the
neighbourhood make that exactly `log₂ i(K_{d,d})`.  Equality is the reason no constant in
Kahn–Zhao can be improved. -/
private theorem entropy_add_mul_condEntropy_le {Ω : Type*} [Fintype Ω] {p : Ω → ℝ}
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Z : Ω → (ι → Bool)) (Y : Ω → Bool) (d : ℕ) (hd : Fintype.card ι = d)
    (hind : ∀ ω, p ω ≠ 0 → Y ω = true → Z ω = fun _ => false) :
    entropy p Z + (d : ℝ) * condEntropy p Y Z
      ≤ Real.logb 2 ((2 ^ (d + 1) - 1 : ℕ) : ℝ) := by
  have h2d : (1 : ℕ) ≤ 2 ^ d := Nat.one_le_two_pow
  have hcardf : Fintype.card (ι → Bool) = 2 ^ d := by
    rw [Fintype.card_fun, Fintype.card_bool, hd]
  have hlogb2 : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)
  have hbpos : ∀ w ∈ (univ : Finset (ι → Bool)),
      0 < (if w = (fun _ => false) then (2 : ℝ) ^ d else 1) := by
    intro w _
    split <;> positivity
  have hgibbs := sum_negMulLogb_add_mul_logb_le (univ : Finset (ι → Bool))
    (probOf p Z) (fun w => if w = (fun _ => false) then (2 : ℝ) ^ d else 1)
    (fun w _ => probOf_nonneg hp Z w) (by rw [sum_probOf]; exact hp1) hbpos
  have hsumb : ∑ w : ι → Bool, (if w = (fun _ => false) then (2 : ℝ) ^ d else 1)
      = ((2 ^ (d + 1) - 1 : ℕ) : ℝ) := by
    rw [← Finset.add_sum_erase univ _ (Finset.mem_univ (fun _ => false : ι → Bool))]
    rw [Finset.sum_congr rfl (fun w hw => if_neg (Finset.ne_of_mem_erase hw))]
    rw [if_pos rfl, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, hcardf]
    have : ((2 ^ d - 1 : ℕ) : ℝ) = (2 : ℝ) ^ d - 1 := by
      push_cast [h2d]
      ring
    rw [nsmul_eq_mul, mul_one, this, Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    ring
  have hcond : condEntropy p Y Z ≤ probOf p Z (fun _ => false) := by
    have hB := condEntropy_le_sum_probOf_mul_logb hp Y Z
      (fun w => if w = (fun _ => false) then (univ : Finset Bool) else {false}) ?_
    · refine hB.trans (le_of_eq ?_)
      have hterm : ∀ w : ι → Bool, probOf p Z w * Real.logb 2
          ((((if w = (fun _ => false) then (univ : Finset Bool) else {false})).card : ℕ) : ℝ)
          = if w = (fun _ => false) then probOf p Z (fun _ => false) else 0 := by
        intro w
        by_cases h : w = (fun _ => false)
        · subst h
          rw [if_pos rfl, if_pos rfl, Finset.card_univ, Fintype.card_bool]
          norm_num [hlogb2]
        · rw [if_neg h, if_neg h, Finset.card_singleton]
          norm_num
      rw [Finset.sum_congr rfl fun w _ => hterm w]
      simp
    · intro w y hy
      by_cases hw : w = (fun _ => false)
      · exact absurd (by rw [if_pos hw]; exact Finset.mem_univ y) hy
      · rw [if_neg hw, Finset.mem_singleton] at hy
        have hytrue : y = true := by cases y <;> simp_all
        subst hytrue
        refine Finset.sum_eq_zero fun ω hω => ?_
        by_cases hpω : p ω = 0
        · exact hpω
        · exfalso
          rw [Finset.mem_filter] at hω
          have h2 : Y ω = true ∧ Z ω = w := Prod.mk.injEq .. ▸ hω.2
          exact hw (h2.2 ▸ hind ω hpω h2.1)
  have hterm2 : ∑ w : ι → Bool, probOf p Z w *
      Real.logb 2 (if w = (fun _ => false) then (2 : ℝ) ^ d else 1)
      = probOf p Z (fun _ => false) * (d : ℝ) := by
    have hterm : ∀ w : ι → Bool, probOf p Z w *
        Real.logb 2 (if w = (fun _ => false) then (2 : ℝ) ^ d else 1)
        = if w = (fun _ => false) then probOf p Z (fun _ => false) * (d : ℝ) else 0 := by
      intro w
      by_cases h : w = (fun _ => false)
      · subst h
        rw [if_pos rfl, if_pos rfl, Real.logb_pow, hlogb2, mul_one]
      · rw [if_neg h, if_neg h, Real.logb_one, mul_zero]
    rw [Finset.sum_congr rfl fun w _ => hterm w]
    simp
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  rw [← hsumb]
  refine le_trans ?_ hgibbs
  rw [Finset.sum_add_distrib, hterm2]
  have : entropy p Z = ∑ w : ι → Bool, -probOf p Z w * Real.logb 2 (probOf p Z w) := rfl
  rw [this]
  nlinarith [hcond, hdnn]

omit [Fintype V] in
/-- `IsIndepSet` on a coerced finset, unpacked; the `x = y` case is looplessness. -/
private theorem forall_not_adj_of_isIndepSet (G : SimpleGraph V) {S : Finset V}
    (h : G.IsIndepSet (S : Set V)) : ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y := by
  rw [SimpleGraph.isIndepSet_iff] at h
  intro x hx y hy hadj
  rcases eq_or_ne x y with rfl | hne
  · exact G.irrefl hadj
  · exact h (by simpa using hx) (by simpa using hy) hne hadj

omit [Fintype V] in
/-- The converse of `forall_not_adj_of_isIndepSet`. -/
private theorem isIndepSet_of_forall_not_adj (G : SimpleGraph V) {S : Finset V}
    (h : ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y) : G.IsIndepSet (S : Set V) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro x hx y hy _ hadj
  exact h x (by simpa using hx) y (by simpa using hy) hadj

/-- `indepSetCount` as an honest `Finset.card`, available because `∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y`
is decidable while `IsIndepSet` carries no `DecidablePred` instance. -/
private theorem card_filter_indep_eq (H : SimpleGraph V) [DecidableEq V] [DecidableRel H.Adj] :
    #(univ.filter fun S : Finset V => ∀ x ∈ S, ∀ y ∈ S, ¬ H.Adj x y) = indepSetCount H := by
  rw [indepSetCount, Nat.card_congr (Equiv.subtypeEquivRight fun _ : Finset V =>
      ⟨forall_not_adj_of_isIndepSet H, isIndepSet_of_forall_not_adj H⟩),
    Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **Kahn's theorem for a bipartite graph, one side at a time.**  For `H` `d`-regular with
every edge crossing the `side` cut,

    d · log₂ i(H) ≤ |{v : side v}| · log₂ i(K_{d,d}).

Take `I` uniform among the independent sets of `H`, so that `H(X) = log₂ i(H)`
(`entropy_uniformPMF_of_injOn`), and split the vertices as `A` (`side` false) and `B`.  Writing
`H(X) = H(X_A) + (H(X) - H(X_A))`, the first part is bounded by `shearer_subset_le` over the
cover of `A` by the neighbourhoods `N(b)`, `b ∈ B`, each vertex of `A` being covered exactly `d`
times; the second by `entropy_sub_le_sum_cond_rank` along a rank that puts `A` first.  That
leaves `∑_{b ∈ B} (H(X_{N(b)}) + d · H(X_b ∣ X_{N(b)}))`, and
`entropy_add_mul_condEntropy_le` bounds each summand by `log₂ i(K_{d,d})`. -/
theorem indepSetCount_logb_half_le [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d : ℕ) (side : V → Bool)
    (hcross : ∀ u v, H.Adj u v → side u ≠ side v)
    (hreg : ∀ v, Nat.card {u // H.Adj v u} = d) :
    (d : ℝ) * Real.logb 2 (indepSetCount H : ℝ)
      ≤ (#(univ.filter fun v => side v = true) : ℝ)
          * Real.logb 2 ((2 ^ (d + 1) - 1 : ℕ) : ℝ) := by
  obtain ⟨r, hrinj, hrlt⟩ := exists_rank_side_lt side
  set P : Finset (Finset V) := univ.filter (fun S : Finset V => ∀ x ∈ S, ∀ y ∈ S, ¬ H.Adj x y)
    with hPdef
  set A : Finset V := univ.filter (fun v => side v = false) with hAdef
  set B : Finset V := univ.filter (fun v => side v = true) with hBdef
  set nb : V → Finset V := fun v => univ.filter (fun u => H.Adj v u) with hnbdef
  set D : V → Finset V := fun j => (nb j).filter (fun u => side u = false) with hDdef
  set X : V → Finset V → Bool := fun v S => decide (v ∈ S) with hXdef
  set p : Finset V → ℝ := uniformPMF P with hpdef
  have hPne : P.Nonempty := ⟨∅, by simp [hPdef]⟩
  have hp : ∀ ω, 0 ≤ p ω := by rw [hpdef]; exact uniformPMF_nonneg P
  have hp1 : ∑ ω, p ω = 1 := by rw [hpdef]; exact sum_uniformPMF hPne
  have hPmem : ∀ ω : Finset V, p ω ≠ 0 → ω ∈ P := by
    intro ω hω
    by_contra h
    simp [hpdef, uniformPMF, h] at hω
  have hPprop : ∀ ω ∈ P, ∀ x ∈ ω, ∀ y ∈ ω, ¬ H.Adj x y := by
    intro ω hω
    rw [hPdef, Finset.mem_filter] at hω
    exact hω.2
  have hXinj : Function.Injective (fun (S : Finset V) (v : V) => X v S) := by
    intro S T hST
    ext v
    have h := congrFun hST v
    rw [hXdef] at h
    simpa using h
  have hent : entropy p (fun ω i => X i ω) = Real.logb 2 (indepSetCount H : ℝ) := by
    rw [hpdef, entropy_uniformPMF_of_injOn hPne hXinj.injOn, hPdef, card_filter_indep_eq]
  have hnbcard : ∀ v, #(nb v) = d := by
    intro v
    rw [hnbdef]
    rw [← Fintype.card_subtype (fun u => H.Adj v u), ← Nat.card_eq_fintype_card]
    exact hreg v
  have hsideB : ∀ b ∈ B, side b = true := by
    intro b hb; rw [hBdef, Finset.mem_filter] at hb; exact hb.2
  have hsideA : ∀ a ∈ A, side a = false := by
    intro a ha; rw [hAdef, Finset.mem_filter] at ha; exact ha.2
  have hDsubA : ∀ j, D j ⊆ A := by
    intro j u hu
    rw [hDdef, Finset.mem_filter] at hu
    rw [hAdef, Finset.mem_filter]
    exact ⟨Finset.mem_univ u, hu.2⟩
  have hDadj : ∀ j : V, ∀ u ∈ D j, H.Adj j u := by
    intro j u hu
    rw [hDdef, Finset.mem_filter, hnbdef, Finset.mem_filter] at hu
    exact hu.1.2
  have hDb : ∀ b ∈ B, D b = nb b := by
    intro b hb
    rw [hDdef]
    refine Finset.filter_true_of_mem fun u hu => ?_
    rw [hnbdef, Finset.mem_filter] at hu
    have hne := hcross b u hu.2
    rw [hsideB b hb] at hne
    cases hu' : side u with
    | false => rfl
    | true => exact absurd hu'.symm hne
  have hDempty : ∀ j, j ∉ B → D j = ∅ := by
    intro j hj
    have hjf : side j = false := by
      rw [hBdef, Finset.mem_filter] at hj
      simp only [Finset.mem_univ, true_and] at hj
      cases hj' : side j with
      | false => rfl
      | true => exact absurd hj' hj
    refine Finset.eq_empty_of_forall_notMem fun u hu => ?_
    rw [hDdef, Finset.mem_filter, hnbdef, Finset.mem_filter] at hu
    have hne := hcross j u hu.1.2
    rw [hjf, hu.2] at hne
    exact hne rfl
  have hcover : ∀ i ∈ A, d ≤ #(univ.filter fun j : V => i ∈ D j) := by
    intro i hi
    have he : (univ.filter fun j : V => i ∈ D j) = nb i := by
      ext j
      rw [Finset.mem_filter, hDdef]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnbdef, hsideA i hi, and_true]
      exact ⟨fun h => h.symm, fun h => h.symm⟩
    rw [he, hnbcard i]
  have hDr : ∀ j ∈ univ \ A, D j ⊆ univ.filter fun x => r x < r j := by
    intro j hj u hu
    rw [Finset.mem_sdiff, hAdef, Finset.mem_filter] at hj
    have hjt : side j = true := by
      cases hj' : side j with
      | false => exact absurd ⟨Finset.mem_univ j, hj'⟩ hj.2
      | true => rfl
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ u, hrlt u j (hsideA u (hDsubA j hu)) hjt⟩
  have hAr : ∀ v ∈ A, (univ.filter fun x => r x < r v) = A.filter fun x => r x < r v := by
    intro v hv
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
    rw [hAdef, Finset.mem_filter]
    refine ⟨Finset.mem_univ x, ?_⟩
    cases hx : side x with
    | false => rfl
    | true => exact absurd (hrlt v x (hsideA v hv) hx) (by omega)
  have hABuniv : univ \ A = B := by
    ext v
    rw [Finset.mem_sdiff, hAdef, hBdef, Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    cases hv : side v with
    | false => simp
    | true => simp
  have hsh := shearer_subset_le p hp hp1 X A D d hDsubA hcover
  have hsum1 : ∑ j : V, entropy p (fun ω (u : D j) => X u.1 ω)
      = ∑ b ∈ B, entropy p (fun ω (u : D b) => X u.1 ω) := by
    refine (Finset.sum_subset (Finset.subset_univ B) fun j _ hj => ?_).symm
    rw [hDempty j hj]
    have hsubsing : Subsingleton (↥(∅ : Finset V) → Bool) :=
      ⟨fun f g => funext fun a => absurd a.2 (Finset.notMem_empty a.1)⟩
    exact entropy_eq_zero_of_subsingleton hp1 _
  have hchain := entropy_sub_le_sum_cond_rank hp hp1 X A D r hrinj hDr hAr
  rw [hABuniv] at hchain
  rw [hsum1] at hsh
  have hlocal : ∀ b ∈ B, entropy p (fun ω (u : D b) => X u.1 ω)
      + (d : ℝ) * condEntropy p (X b) (fun ω (u : D b) => X u.1 ω)
      ≤ Real.logb 2 ((2 ^ (d + 1) - 1 : ℕ) : ℝ) := by
    intro b hb
    refine entropy_add_mul_condEntropy_le hp hp1 (fun ω (u : ↥(D b)) => X u.1 ω) (X b) d ?_ ?_
    · rw [Fintype.card_coe, hDb b hb, hnbcard b]
    · intro ω hpω hYω
      funext u
      have hωP := hPmem ω hpω
      have hbω : b ∈ ω := by
        rw [hXdef] at hYω
        simpa using hYω
      have hadj : H.Adj b u.1 := hDadj b u.1 u.2
      rw [hXdef]
      simp only [decide_eq_false_iff_not]
      intro huω
      exact hPprop ω hωP b hbω u.1 huω hadj
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have h3 := mul_le_mul_of_nonneg_left hchain hd0
  calc (d : ℝ) * Real.logb 2 (indepSetCount H : ℝ)
      = (d : ℝ) * entropy p (fun ω i => X i ω) := by rw [hent]
    _ ≤ ∑ b ∈ B, (entropy p (fun ω (u : D b) => X u.1 ω)
          + (d : ℝ) * condEntropy p (X b) (fun ω (u : D b) => X u.1 ω)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        linarith [hsh, h3]
    _ ≤ ∑ _b ∈ B, Real.logb 2 ((2 ^ (d + 1) - 1 : ℕ) : ℝ) := Finset.sum_le_sum hlocal
    _ = (#B : ℝ) * Real.logb 2 ((2 ^ (d + 1) - 1 : ℕ) : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- `Real.logb 2` reflects `≤` on the positives. -/
private theorem le_of_logb_two_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : Real.logb 2 x ≤ Real.logb 2 y) : x ≤ y := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  simp only [Real.logb] at h
  have e1 : Real.log x = Real.log x / Real.log 2 * Real.log 2 := by field_simp
  have e2 : Real.log y = Real.log y / Real.log 2 * Real.log 2 := by field_simp
  have h1 : Real.log x ≤ Real.log y := by
    rw [e1, e2]; exact mul_le_mul_of_nonneg_right h hlog2.le
  have h2 := Real.exp_le_exp.mpr h1
  rwa [Real.exp_log hx, Real.exp_log hy] at h2

/-- **Kahn's theorem** (Kahn 2001): a `d`-regular graph all of whose edges cross a two-colouring
of its vertices has `i(H)^{2d} ≤ i(K_{d,d})^{|V|}`.  Applying `indepSetCount_logb_half_le` to
`side` and to its negation bounds `d · log₂ i(H)` by each side's share of the vertices; adding
the two gives `2d · log₂ i(H) ≤ |V| · log₂ i(K_{d,d})`, which `le_of_logb_two_le` turns back
into an inequality of natural numbers. -/
private theorem indepSetCount_pow_le_of_side [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d : ℕ) (side : V → Bool)
    (hcross : ∀ u v, H.Adj u v → side u ≠ side v)
    (hreg : ∀ v, Nat.card {u // H.Adj v u} = d) :
    indepSetCount H ^ (2 * d) ≤ (2 ^ (d + 1) - 1) ^ Fintype.card V := by
  have h1 := indepSetCount_logb_half_le H d side hcross hreg
  have h2 := indepSetCount_logb_half_le H d (fun v => !side v)
    (fun u v huv hh => hcross u v huv (by cases side u <;> cases side v <;> simp_all)) hreg
  have hcompl : (univ.filter fun v => (!side v) = true)
      = (univ.filter fun v => ¬ (side v = true)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases side v <;> simp
  have hcard : #(univ.filter fun v => side v = true)
      + #(univ.filter fun v => (!side v) = true) = Fintype.card V := by
    rw [hcompl, Finset.card_filter_add_card_filter_not (s := (univ : Finset V))
      (p := fun v => side v = true), Finset.card_univ]
  have hipos : 0 < indepSetCount H := by
    rw [← card_filter_indep_eq H]
    exact Finset.card_pos.mpr ⟨∅, by simp⟩
  have hK2 : 2 ≤ 2 ^ (d + 1) := by
    have h := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) (show 1 ≤ d + 1 by omega)
    simpa using h
  have hKpos : 0 < 2 ^ (d + 1) - 1 := by omega
  have hc : ((#(univ.filter fun v => side v = true) : ℝ)
      + (#(univ.filter fun v => (!side v) = true) : ℝ)) = (Fintype.card V : ℝ) := by
    rw [← Nat.cast_add, hcard]
  have hsum : (2 : ℝ) * ((d : ℝ) * Real.logb 2 (indepSetCount H : ℝ))
      ≤ (Fintype.card V : ℝ) * Real.logb 2 ((2 ^ (d + 1) - 1 : ℕ) : ℝ) := by
    have h := add_le_add h1 h2
    have hr : (#(univ.filter fun v => side v = true) : ℝ)
          * Real.logb 2 ((2 ^ (d + 1) - 1 : ℕ) : ℝ)
        + (#(univ.filter fun v => (!side v) = true) : ℝ)
          * Real.logb 2 ((2 ^ (d + 1) - 1 : ℕ) : ℝ)
        = (Fintype.card V : ℝ) * Real.logb 2 ((2 ^ (d + 1) - 1 : ℕ) : ℝ) := by
      rw [← add_mul, hc]
    linarith [h, hr]
  have hxpos : (0 : ℝ) < ((indepSetCount H ^ (2 * d) : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_pos hipos (n := 2 * d)
  have hypos : (0 : ℝ) < (((2 ^ (d + 1) - 1) ^ Fintype.card V : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_pos hKpos (n := Fintype.card V)
  have hL : Real.logb 2 ((indepSetCount H ^ (2 * d) : ℕ) : ℝ)
      ≤ Real.logb 2 (((2 ^ (d + 1) - 1) ^ Fintype.card V : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_pow, Real.logb_pow, Real.logb_pow]
    push_cast
    linarith [hsum]
  exact_mod_cast le_of_logb_two_le hxpos hypos hL

omit [Fintype V] in
/-- In the graph `G` restricted to `S`, anything reaching a vertex of `S` lies in `S`. -/
private theorem mem_of_reflTransGen_restrict (G : SimpleGraph V) (S : Finset V) {u v : V}
    (h : Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∈ S ∧ b ∈ S) u v) :
    v ∈ S → u ∈ S := by
  induction h with
  | refl => exact fun hv => hv
  | tail _ hbc ih => exact fun _ => ih hbc.2.1

omit [Fintype V] in
/-- **Walk parity fixes the side.**  If `σ` and `τ` both flip across every edge of `G`
restricted to `S`, then `σ = τ` propagates along paths: agreeing at one end of a walk forces
agreement at the other.  This is what makes the swapping trick injective. -/
private theorem decide_mem_eq_of_reflTransGen (G : SimpleGraph V) (S : Finset V)
    (σ τ : V → Bool)
    (hσ : ∀ a b, G.Adj a b → a ∈ S → b ∈ S → σ a ≠ σ b)
    (hτ : ∀ a b, G.Adj a b → a ∈ S → b ∈ S → τ a ≠ τ b)
    {u v : V} (h : Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∈ S ∧ b ∈ S) u v)
    (hu : σ u = τ u) : σ v = τ v := by
  induction h with
  | refl => exact hu
  | tail _ hbc ih =>
      have e1 := Bool.eq_not_iff.mpr (Ne.symm (hσ _ _ hbc.1 hbc.2.1 hbc.2.2))
      have e2 := Bool.eq_not_iff.mpr (Ne.symm (hτ _ _ hbc.1 hbc.2.1 hbc.2.2))
      rw [e1, e2, ih]

omit [Fintype V] in
/-- **The swap kills every crossing edge.**  Let `I, J` be independent, `S = I ∆ J`, and let `P`
be constant on the `S`-components.  Then no `G`-edge joins `A = (I ∩ J) ∪ {v ∈ S | P v}` to
`B = (I ∩ J) ∪ {v ∈ S | ¬ P v}`: an edge meeting `I ∩ J` would sit inside `I` or inside `J`, and
an edge inside `S` has `P` equal at both ends, so it cannot cross from `A` to `B`. -/
private theorem no_adj_between_sides [DecidableEq V] (G : SimpleGraph V) (I J : Finset V)
    (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) (hJ : ∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y)
    (P : V → Prop) (A B : Finset V)
    (hA : ∀ v, v ∈ A ↔ (v ∈ I ∧ v ∈ J) ∨ (v ∈ (I \ J) ∪ (J \ I) ∧ P v))
    (hB : ∀ v, v ∈ B ↔ (v ∈ I ∧ v ∈ J) ∨ (v ∈ (I \ J) ∪ (J \ I) ∧ ¬ P v))
    (hP : ∀ u v, G.Adj u v → u ∈ (I \ J) ∪ (J \ I) → v ∈ (I \ J) ∪ (J \ I) →
      (P u ↔ P v)) :
    ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b := by
  intro a ha b hb hadj
  rcases (hA a).mp ha with ⟨haI, haJ⟩ | ⟨haS, haP⟩
  · rcases (hB b).mp hb with ⟨hbI, _⟩ | ⟨hbS, _⟩
    · exact hI a haI b hbI hadj
    · rcases Finset.mem_union.mp hbS with h | h
      · exact hI a haI b (Finset.mem_sdiff.mp h).1 hadj
      · exact hJ a haJ b (Finset.mem_sdiff.mp h).1 hadj
  · rcases (hB b).mp hb with ⟨hbI, hbJ⟩ | ⟨hbS, hbP⟩
    · rcases Finset.mem_union.mp haS with h | h
      · exact hI a (Finset.mem_sdiff.mp h).1 b hbI hadj
      · exact hJ a (Finset.mem_sdiff.mp h).1 b hbJ hadj
    · exact hbP ((hP a b hadj haS hbS).mp haP)

omit [Fintype V] in
/-- `A × {false} ∪ B × {true}` is independent in `doubleCover G` exactly when no `G`-edge joins
`A` to `B`; only this direction is needed. -/
private theorem isIndepSet_doubleCover_pack [DecidableEq V] (G : SimpleGraph V) (A B : Finset V)
    (h : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    (doubleCover G).IsIndepSet
      ((A.image (fun v => (v, false)) ∪ B.image (fun v => (v, true)) : Finset (V × Bool)) :
        Set (V × Bool)) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro x hx y hy _ hadj
  rw [doubleCover_adj] at hadj
  simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
    Finset.mem_coe] at hx hy
  rcases hx with ⟨a, haA, rfl⟩ | ⟨a, haB, rfl⟩ <;>
    rcases hy with ⟨b, hbA, rfl⟩ | ⟨b, hbB, rfl⟩
  · exact hadj.2 rfl
  · exact h a haA b hbB hadj.1
  · exact h b hbA a haB hadj.1.symm
  · exact hadj.2 rfl

omit [Fintype V] in
/-- `(A, B) ↦ A × {false} ∪ B × {true}` is injective. -/
private theorem pack_eq_pair [DecidableEq V] {A₁ B₁ A₂ B₂ : Finset V}
    (h : A₁.image (fun v => (v, false)) ∪ B₁.image (fun v => (v, true))
       = A₂.image (fun v => (v, false)) ∪ B₂.image (fun v => (v, true))) :
    A₁ = A₂ ∧ B₁ = B₂ := by
  refine ⟨Finset.ext fun v => ?_, Finset.ext fun v => ?_⟩
  · simpa using Finset.ext_iff.mp h (v, false)
  · simpa using Finset.ext_iff.mp h (v, true)

omit [Fintype V] in
/-- A least-rank vertex of the `S`-component of `v`. -/
private theorem exists_min_reflTransGen [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    (rk : V → ℕ) {v : V} (hv : v ∈ S) :
    ∃ u, u ∈ S ∧ Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∈ S ∧ b ∈ S) u v ∧
      ∀ w, Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∈ S ∧ b ∈ S) w v → rk u ≤ rk w := by
  classical
  obtain ⟨u, hu, hmin⟩ := Finset.exists_min_image
    (S.filter fun x => Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∈ S ∧ b ∈ S) x v) rk
    ⟨v, Finset.mem_filter.mpr ⟨hv, Relation.ReflTransGen.refl⟩⟩
  rw [Finset.mem_filter] at hu
  refine ⟨u, hu.1, hu.2, fun w hw => ?_⟩
  exact hmin w (Finset.mem_filter.mpr ⟨mem_of_reflTransGen_restrict G S hw hv, hw⟩)

omit [Fintype V] in
/-- Every edge of `G` inside `I ∆ J` flips membership of `I`: both endpoints in `I` contradicts
independence of `I`, and neither in `I` puts both in `J`. -/
private theorem decide_mem_ne_of_adj_symmDiff [DecidableEq V] (G : SimpleGraph V)
    (I J : Finset V) (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y)
    (hJ : ∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y) {a b : V} (hab : G.Adj a b)
    (ha : a ∈ (I \ J) ∪ (J \ I)) (hb : b ∈ (I \ J) ∪ (J \ I)) :
    decide (a ∈ I) ≠ decide (b ∈ I) := by
  rcases Finset.mem_union.mp ha with ha' | ha' <;>
    rcases Finset.mem_union.mp hb with hb' | hb' <;>
    rw [Finset.mem_sdiff] at ha' hb'
  · exact absurd hab (hI a ha'.1 b hb'.1)
  · simp [ha'.1, hb'.2]
  · simp [ha'.2, hb'.1]
  · exact absurd hab (hJ a ha'.1 b hb'.1)

omit [Fintype V] in
/-- **The swap is reversible.**  From `A` and `B` alone one reads off `I ∩ J` as `A ∩ B`, the
symmetric difference `I ∆ J` as `A ∆ B`, and on `I ∆ J` the value of `P` as membership of `A`. -/
private theorem sides_determine [DecidableEq V] (I J : Finset V) (P : V → Prop)
    (A B : Finset V)
    (hA : ∀ v, v ∈ A ↔ (v ∈ I ∧ v ∈ J) ∨ (v ∈ (I \ J) ∪ (J \ I) ∧ P v))
    (hB : ∀ v, v ∈ B ↔ (v ∈ I ∧ v ∈ J) ∨ (v ∈ (I \ J) ∪ (J \ I) ∧ ¬ P v)) :
    (∀ v, (v ∈ A ∧ v ∈ B) ↔ (v ∈ I ∧ v ∈ J))
      ∧ (∀ v, (v ∈ (I \ J) ∪ (J \ I)) ↔ ¬ (v ∈ A ↔ v ∈ B))
      ∧ (∀ v ∈ (I \ J) ∪ (J \ I), (v ∈ A ↔ P v)) := by
  have hS : ∀ v, v ∈ (I \ J) ∪ (J \ I) → ¬ (v ∈ I ∧ v ∈ J) := by
    intro v hv
    rcases Finset.mem_union.mp hv with h | h <;> rw [Finset.mem_sdiff] at h
    · exact fun hc => h.2 hc.2
    · exact fun hc => h.2 hc.1
  refine ⟨fun v => ?_, fun v => ?_, fun v hv => ?_⟩
  · rw [hA, hB]
    by_cases hv : v ∈ (I \ J) ∪ (J \ I)
    · have h0 := hS v hv
      by_cases hp : P v <;> tauto
    · tauto
  · rw [hA, hB]
    by_cases hv : v ∈ (I \ J) ∪ (J \ I)
    · have h0 := hS v hv
      by_cases hp : P v <;> simp_all
    · simp [hv]
  · rw [hA]
    have h0 := hS v hv
    tauto

/-- **Zhao's bipartite swapping trick** (Zhao 2010): `i(G)^2 ≤ i(G × K₂)`.

This is the step of Kahn–Zhao that is not entropy: it upgrades Kahn's bipartite theorem to
arbitrary regular graphs, since `doubleCover G` is bipartite and `d`-regular whenever `G` is.

An independent set of `doubleCover G` is a pair `(A, B)` of vertex sets with no `G`-edge between
them, so the claim is an injection from pairs of independent sets into such pairs.  Given
independent `I, J`, the graph `G` restricted to `S = I ∆ J` has all of its edges between `I \ J`
and `J \ I`, and none of them meets `I ∩ J`; sending each `S`-component entirely into `A` or
entirely into `B`, according to whether the component's least-rank vertex lies in `I`, gives a
pair with no crossing edge (`no_adj_between_sides`).  It is injective because `A` and `B`
recover `I ∩ J`, `S` and the per-component choice (`sides_determine`), and inside a component
the side of a vertex is then forced by the side of the least-rank vertex together with the
parity of a walk to it (`decide_mem_eq_of_reflTransGen`), every edge inside `S` flipping sides
(`decide_mem_ne_of_adj_symmDiff`). -/
private theorem indepSetCount_sq_le_doubleCover (G : SimpleGraph V) :
    indepSetCount G ^ 2 ≤ indepSetCount (doubleCover G) := by
  classical
  obtain ⟨rk, hrk⟩ : ∃ rk : V → ℕ, Function.Injective rk :=
    ⟨fun v => ((Fintype.equivFin V) v : ℕ), fun a b h =>
      (Fintype.equivFin V).injective (Fin.val_injective h)⟩
  set Pr : Finset V → Finset V → V → Prop := fun S I v =>
    ∃ u, Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∈ S ∧ b ∈ S) u v ∧ u ∈ I ∧
      ∀ w, Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∈ S ∧ b ∈ S) w v → rk u ≤ rk w
    with hPr
  set Aof : Finset V → Finset V → Finset V := fun I J =>
    (I ∩ J) ∪ ((I \ J) ∪ (J \ I)).filter (Pr ((I \ J) ∪ (J \ I)) I) with hAof
  set Bof : Finset V → Finset V → Finset V := fun I J =>
    (I ∩ J) ∪ ((I \ J) ∪ (J \ I)).filter (fun v => ¬ Pr ((I \ J) ∪ (J \ I)) I v) with hBof
  set F : Finset V → Finset V → Finset (V × Bool) := fun I J =>
    ((Aof I J).image fun v => (v, false)) ∪ ((Bof I J).image fun v => (v, true)) with hF
  have hmemA : ∀ I J v, v ∈ Aof I J ↔
      (v ∈ I ∧ v ∈ J) ∨ (v ∈ (I \ J) ∪ (J \ I) ∧ Pr ((I \ J) ∪ (J \ I)) I v) := by
    intro I J v
    simp only [hAof]
    rw [Finset.mem_union, Finset.mem_inter, Finset.mem_filter]
  have hmemB : ∀ I J v, v ∈ Bof I J ↔
      (v ∈ I ∧ v ∈ J) ∨ (v ∈ (I \ J) ∪ (J \ I) ∧ ¬ Pr ((I \ J) ∪ (J \ I)) I v) := by
    intro I J v
    simp only [hBof]
    rw [Finset.mem_union, Finset.mem_inter, Finset.mem_filter]
  have hPrcongr : ∀ (S I : Finset V) (u v : V), G.Adj u v → u ∈ S → v ∈ S →
      (Pr S I u ↔ Pr S I v) := by
    intro S I u v huv hu hv
    simp only [hPr]
    constructor
    · rintro ⟨w, hw1, hw2, hw3⟩
      exact ⟨w, hw1.tail ⟨huv, hu, hv⟩, hw2, fun x hx => hw3 x (hx.tail ⟨huv.symm, hv, hu⟩)⟩
    · rintro ⟨w, hw1, hw2, hw3⟩
      exact ⟨w, hw1.tail ⟨huv.symm, hv, hu⟩, hw2, fun x hx => hw3 x (hx.tail ⟨huv, hu, hv⟩)⟩
  have hPrmin : ∀ (S I : Finset V) (v u : V),
      Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∈ S ∧ b ∈ S) u v →
      (∀ w, Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∈ S ∧ b ∈ S) w v → rk u ≤ rk w) →
      (Pr S I v ↔ u ∈ I) := by
    intro S I v u hru hmin
    simp only [hPr]
    refine ⟨?_, fun h => ⟨u, hru, h, hmin⟩⟩
    rintro ⟨u', h1, h2, h3⟩
    exact (hrk (le_antisymm (hmin u' h1) (h3 u hru))) ▸ h2
  have hmap : ∀ I J : Finset V, G.IsIndepSet ↑I → G.IsIndepSet ↑J →
      (doubleCover G).IsIndepSet ↑(F I J) := by
    intro I J hI hJ
    simp only [hF]
    refine isIndepSet_doubleCover_pack G _ _ ?_
    exact no_adj_between_sides G I J (forall_not_adj_of_isIndepSet G hI)
      (forall_not_adj_of_isIndepSet G hJ) _ _ _ (hmemA I J) (hmemB I J)
      (hPrcongr ((I \ J) ∪ (J \ I)) I)
  have hinj : ∀ I₁ J₁ I₂ J₂ : Finset V, G.IsIndepSet ↑I₁ → G.IsIndepSet ↑J₁ →
      G.IsIndepSet ↑I₂ → G.IsIndepSet ↑J₂ → F I₁ J₁ = F I₂ J₂ → I₁ = I₂ ∧ J₁ = J₂ := by
    intro I₁ J₁ I₂ J₂ hI₁ hJ₁ hI₂ hJ₂ heq
    simp only [hF] at heq
    obtain ⟨hA, hB⟩ := pack_eq_pair heq
    obtain ⟨hC1, hS1, hP1⟩ := sides_determine I₁ J₁ (Pr ((I₁ \ J₁) ∪ (J₁ \ I₁)) I₁)
      (Aof I₁ J₁) (Bof I₁ J₁) (hmemA I₁ J₁) (hmemB I₁ J₁)
    obtain ⟨hC2, hS2, hP2⟩ := sides_determine I₂ J₂ (Pr ((I₂ \ J₂) ∪ (J₂ \ I₂)) I₂)
      (Aof I₂ J₂) (Bof I₂ J₂) (hmemA I₂ J₂) (hmemB I₂ J₂)
    have hCeq : ∀ v, (v ∈ I₁ ∧ v ∈ J₁) ↔ (v ∈ I₂ ∧ v ∈ J₂) := by
      intro v; rw [← hC1 v, ← hC2 v, hA, hB]
    have hSeq : ∀ v, v ∈ (I₁ \ J₁) ∪ (J₁ \ I₁) ↔ v ∈ (I₂ \ J₂) ∪ (J₂ \ I₂) := by
      intro v; rw [hS1 v, hS2 v, hA, hB]
    have hS2eq : (I₂ \ J₂) ∪ (J₂ \ I₂) = (I₁ \ J₁) ∪ (J₁ \ I₁) :=
      Finset.ext fun v => (hSeq v).symm
    have hPeq : ∀ v ∈ (I₁ \ J₁) ∪ (J₁ \ I₁),
        (Pr ((I₁ \ J₁) ∪ (J₁ \ I₁)) I₁ v ↔ Pr ((I₁ \ J₁) ∪ (J₁ \ I₁)) I₂ v) := by
      intro v hv
      have h2 := hP2 v ((hSeq v).mp hv)
      rw [hS2eq] at h2
      rw [← hP1 v hv, ← h2, hA]
    have hflip1 : ∀ a b, G.Adj a b → a ∈ (I₁ \ J₁) ∪ (J₁ \ I₁) → b ∈ (I₁ \ J₁) ∪ (J₁ \ I₁) →
        decide (a ∈ I₁) ≠ decide (b ∈ I₁) := fun a b hab ha hb =>
      decide_mem_ne_of_adj_symmDiff G I₁ J₁ (forall_not_adj_of_isIndepSet G hI₁)
        (forall_not_adj_of_isIndepSet G hJ₁) hab ha hb
    have hflip2 : ∀ a b, G.Adj a b → a ∈ (I₁ \ J₁) ∪ (J₁ \ I₁) → b ∈ (I₁ \ J₁) ∪ (J₁ \ I₁) →
        decide (a ∈ I₂) ≠ decide (b ∈ I₂) := fun a b hab ha hb =>
      decide_mem_ne_of_adj_symmDiff G I₂ J₂ (forall_not_adj_of_isIndepSet G hI₂)
        (forall_not_adj_of_isIndepSet G hJ₂) hab ((hSeq a).mp ha) ((hSeq b).mp hb)
    have hIeq : ∀ v ∈ (I₁ \ J₁) ∪ (J₁ \ I₁), decide (v ∈ I₁) = decide (v ∈ I₂) := by
      intro v hv
      obtain ⟨u, _, huR, humin⟩ := exists_min_reflTransGen G ((I₁ \ J₁) ∪ (J₁ \ I₁)) rk hv
      have hu : decide (u ∈ I₁) = decide (u ∈ I₂) := by
        have e1 := hPrmin ((I₁ \ J₁) ∪ (J₁ \ I₁)) I₁ v u huR humin
        have e2 := hPrmin ((I₁ \ J₁) ∪ (J₁ \ I₁)) I₂ v u huR humin
        have e3 := hPeq v hv
        simp only [decide_eq_decide]
        rw [← e1, ← e2]
        exact e3
      exact decide_mem_eq_of_reflTransGen G ((I₁ \ J₁) ∪ (J₁ \ I₁))
        (fun x => decide (x ∈ I₁)) (fun x => decide (x ∈ I₂)) hflip1 hflip2 huR hu
    have hIfin : I₁ = I₂ := by
      ext v
      by_cases hv : v ∈ (I₁ \ J₁) ∪ (J₁ \ I₁)
      · simpa using hIeq v hv
      · refine ⟨fun h => ?_, fun h => ?_⟩
        · have hj : v ∈ J₁ := by
            by_contra hc
            exact hv (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h, hc⟩))
          exact ((hCeq v).mp ⟨h, hj⟩).1
        · have hj : v ∈ J₂ := by
            by_contra hc
            exact hv ((hSeq v).mpr (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h, hc⟩)))
          exact ((hCeq v).mpr ⟨h, hj⟩).1
    refine ⟨hIfin, ?_⟩
    ext v
    by_cases hv : v ∈ (I₁ \ J₁) ∪ (J₁ \ I₁)
    · have h1 : v ∈ J₁ ↔ v ∉ I₁ := by
        rcases Finset.mem_union.mp hv with h | h <;> rw [Finset.mem_sdiff] at h <;>
          simp [h.1, h.2]
      have h2 : v ∈ J₂ ↔ v ∉ I₂ := by
        rcases Finset.mem_union.mp ((hSeq v).mp hv) with h | h <;> rw [Finset.mem_sdiff] at h <;>
          simp [h.1, h.2]
      rw [h1, h2, hIfin]
    · refine ⟨fun h => ?_, fun h => ?_⟩
      · have hi : v ∈ I₁ := by
          by_contra hc
          exact hv (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h, hc⟩))
        exact ((hCeq v).mp ⟨hi, h⟩).2
      · have hi : v ∈ I₂ := by
          by_contra hc
          exact hv ((hSeq v).mpr (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h, hc⟩)))
        exact ((hCeq v).mpr ⟨hi, h⟩).2
  rw [pow_two, indepSetCount, indepSetCount, ← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun q => ⟨F q.1.1 q.2.1, hmap _ _ q.1.2 q.2.2⟩) ?_
  rintro ⟨⟨I₁, hI₁⟩, ⟨J₁, hJ₁⟩⟩ ⟨⟨I₂, hI₂⟩, ⟨J₂, hJ₂⟩⟩ heq
  obtain ⟨e1, e2⟩ := hinj I₁ J₁ I₂ J₂ hI₁ hJ₁ hI₂ hJ₂ (congrArg Subtype.val heq)
  subst e1
  subst e2
  rfl
/-- **Kahn–Zhao** (Zhao, Theorem 10.4.12; Kahn 2001 for the bipartite case, Zhao 2010 in
general): a `d`-regular graph on `n` vertices has at most `i(K_{d,d})^{n/(2d)}` independent sets.

Stated as `i(G)^{2d} ≤ i(K_{d,d})^n` to stay in `ℕ`, which is the same inequality with the root
cleared — the chapter's other bounds are written the same way.

`indepSetCount_completeBipartiteGraph` evaluates the right-hand base as `2^{d+1} - 1`, so the
content is that the disjoint union of `n/(2d)` copies of `K_{d,d}` is extremal among `d`-regular
graphs.  Equality holds exactly there, so no constant in this statement can be improved.

`d = 0` is excluded by the regularity hypothesis only when `n > 0`; at `d = 0` the bound reads
`i(G)^0 = 1 ≤ 1^n`, which holds, so no positivity hypothesis is needed. -/
theorem indepSetCount_pow_le (n d : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = d) :
    indepSetCount G ^ (2 * d) ≤ indepSetCount (completeBipartiteGraph (Fin d) (Fin d)) ^ n := by
  rw [indepSetCount_completeBipartiteGraph]
  have : DecidableRel (doubleCover G).Adj := fun a b => decidable_of_iff _ doubleCover_adj.symm
  have hregD : ∀ a : Fin n × Bool, Nat.card {u // (doubleCover G).Adj a u} = d := by
    intro a
    have e : {u // (doubleCover G).Adj a u} ≃ {w // G.Adj a.1 w} :=
      { toFun := fun u => ⟨u.1.1, (doubleCover_adj.mp u.2).1⟩
        invFun := fun w => ⟨(w.1, !a.2), doubleCover_adj.mpr ⟨w.2, by simp⟩⟩
        left_inv := by
          intro u
          have hb : (!a.2) = (u.1 : Fin n × Bool).2 :=
            (Bool.eq_not_iff.mpr (Ne.symm (doubleCover_adj.mp u.2).2)).symm
          exact Subtype.ext (Prod.ext rfl hb)
        right_inv := fun w => rfl }
    have hdeg : Nat.card {w // G.Adj a.1 w} = G.degree a.1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, SimpleGraph.degree,
        SimpleGraph.neighborFinset_eq_filter]
    rw [Nat.card_congr e, hdeg, hreg a.1]
  have hkahn := indepSetCount_pow_le_of_side (doubleCover G) d Prod.snd
    (fun u v huv => (doubleCover_adj.mp huv).2) hregD
  have hcard : Fintype.card (Fin n × Bool) = 2 * n := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; ring
  rw [hcard] at hkahn
  have hzhao := indepSetCount_sq_le_doubleCover G
  have hstep : (indepSetCount G ^ (2 * d)) ^ 2 ≤ ((2 ^ (d + 1) - 1) ^ n) ^ 2 := by
    calc (indepSetCount G ^ (2 * d)) ^ 2 = (indepSetCount G ^ 2) ^ (2 * d) := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ indepSetCount (doubleCover G) ^ (2 * d) := Nat.pow_le_pow_left hzhao _
      _ ≤ (2 ^ (d + 1) - 1) ^ (2 * n) := hkahn
      _ = ((2 ^ (d + 1) - 1) ^ n) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp hstep

end IndepSetCount

end ProbMethodCombinatorics
