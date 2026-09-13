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
