import ProbMethodCombinatorics.Derangements

/-!
# Section 6.5: Latin transversals

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Theorem 6.5.11 (Erdős–Spencer
1991): every `n × n` array in which each symbol occurs at most `n / (4e)` times has a Latin
transversal.

A transversal picks one entry from each row and column, so it *is* a permutation `σ`, and it is
Latin when the entries `A i (σ i)` are distinct.  That makes the conclusion cheap to state; the
work is in the hypothesis of the lopsided local lemma.

**This file specialises Setup 6.5.4 to permutations.**  The source works with a uniformly random
injection `X → Y` for `|X| ≤ |Y|`; for Theorem 6.5.11 only `X = Y = [n]` is needed, where an
injection is a permutation and a matching is a partial permutation.  That avoids authoring the
general random-injection model while keeping the argument intact.

`uniformPerm_isNegativeDependencyGraph` in `Derangements.lean` is the single-edge case of
`uniformPerm_negativeDependency_matchings` below; the general statement is what Theorem 6.5.11
needs, since its bad events involve two entries at a time.

Checked before stating: `ℙ(A_F) = (n - |F|)! / n!` at `n = 4, 5` for matchings of size 1, 2, 3;
the degree bound `(4n-4)(n/(4e) - 1) ≤ n(n-1)/e - 1` at `n = 10, 50, 100, 1000`; and the
resulting `e · p · (d+1) ≤ 1` holds with equality in the worst case.
-/

namespace ProbMethodCombinatorics

open Finset MeasureTheory Nat

variable {n : ℕ}

/-- A set of array positions with at most one entry in each row and each column. -/
def IsPartialMatching (F : Finset (Fin n × Fin n)) : Prop :=
  (∀ p ∈ F, ∀ q ∈ F, p.1 = q.1 → p = q) ∧ (∀ p ∈ F, ∀ q ∈ F, p.2 = q.2 → p = q)

/-- Two position sets share no row and no column. -/
def VertexDisjoint (F G : Finset (Fin n × Fin n)) : Prop :=
  (∀ p ∈ F, ∀ q ∈ G, p.1 ≠ q.1) ∧ (∀ p ∈ F, ∀ q ∈ G, p.2 ≠ q.2)

/-- The event that the transversal uses every position in `F`. -/
def containsEntries (F : Finset (Fin n × Fin n)) : Set (Equiv.Perm (Fin n)) :=
  {σ | ∀ p ∈ F, σ p.1 = p.2}

/-- **A random transversal uses a prescribed partial matching with probability
`(n - |F|)! / n!`.** -/
theorem uniformPerm_containsEntries (F : Finset (Fin n × Fin n)) (hF : IsPartialMatching F) :
    (uniformPerm n).real (containsEntries F) = ((n - F.card)! : ℝ) / (n ! : ℝ) := by
  sorry

/-- The uniform measure of a set of permutations is its size divided by `n !`. -/
private lemma uniformPerm_apply_ncard (t : Set (Equiv.Perm (Fin n))) :
    uniformPerm n t = (t.ncard : ENNReal) / (Nat.card (Equiv.Perm (Fin n)) : ENNReal) := by
  have hms : MeasurableSet t := trivial
  have hnum : Measure.count t = (t.ncard : ENNReal) := by
    rw [Measure.count_apply hms, ← t.toFinite.cast_ncard_eq]
    rfl
  rw [uniformPerm, ProbabilityTheory.uniformOn_univ, hnum,
    Nat.card_eq_fintype_card (α := Equiv.Perm (Fin n))]

/-- Clearing the common denominator `M` in the negative dependency inequality.  The bound is
tight, so the division has to be handled without discarding any factor. -/
private lemma natCast_div_le_mul_div (a b c M : ℕ) (hM : M ≠ 0) (h : a * M ≤ b * c) :
    (a : ENNReal) / (M : ENNReal)
      ≤ ((b : ENNReal) / (M : ENNReal)) * ((c : ENNReal) / (M : ENNReal)) := by
  have hM0 : (M : ENNReal) ≠ 0 := by exact_mod_cast hM
  have hMt : (M : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top M
  calc (a : ENNReal) / (M : ENNReal)
      = ((a * M : ℕ) : ENNReal) / ((M : ENNReal) * (M : ENNReal)) := by
        push_cast
        rw [ENNReal.mul_div_mul_right _ _ hM0 hMt]
    _ ≤ ((b * c : ℕ) : ENNReal) / ((M : ENNReal) * (M : ENNReal)) :=
        ENNReal.div_le_div_right (Nat.cast_le.2 h) _
    _ = ((b : ENNReal) / (M : ENNReal)) * ((c : ENNReal) / (M : ENNReal)) := by
        push_cast
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
          ENNReal.mul_inv (Or.inl hM0) (Or.inl hMt), mul_mul_mul_comm]

/-- The shift permutation of Setup 6.5.4: given an injective target `T` for the rows of `G`, a
permutation carrying each column of `G` to its target, moving no other point except into the
columns of `G`.  It is built by extending the two injections `p ↦ p.2` and `T`, each enlarged by
the identity off the union of their ranges, to a permutation of `Fin n`. -/
private lemma exists_matchingShift (G : Finset (Fin n × Fin n))
    (hG : IsPartialMatching G) (T : {x // x ∈ G} → Fin n) (hT : Function.Injective T) :
    ∃ g : Equiv.Perm (Fin n),
      (∀ p : {x // x ∈ G}, g ((p : Fin n × Fin n).2) = T p) ∧
      ∀ x : Fin n, (∀ p ∈ G, x ≠ p.2) → (g x = x ∨ ∃ q ∈ G, g x = q.2) := by
  classical
  have hcolinj : Function.Injective (fun p : {x // x ∈ G} => (p : Fin n × Fin n).2) := by
    intro p q h
    exact Subtype.ext (hG.2 _ p.2 _ q.2 h)
  set S : Set (Fin n) :=
    Set.range (fun p : {x // x ∈ G} => (p : Fin n × Fin n).2) ∪ Set.range T with hSdef
  have hinj : ∀ u : {x // x ∈ G} → Fin n, Function.Injective u → (∀ p, u p ∈ S) →
      Function.Injective (Sum.elim u (fun x : ↥(Sᶜ) => (x : Fin n))) := by
    intro u hu hmem
    rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg Sum.inl (hu h)
    · exact absurd (h ▸ hmem a) b.2
    · exact absurd (h.symm ▸ hmem b) a.2
    · exact congrArg Sum.inr (Subtype.ext h)
  obtain ⟨g, hg⟩ := Equiv.Perm.exists_extending_pair
      (Sum.elim (fun p : {x // x ∈ G} => (p : Fin n × Fin n).2) (fun x : ↥(Sᶜ) => (x : Fin n)))
      (Sum.elim T (fun x : ↥(Sᶜ) => (x : Fin n)))
      (hinj _ hcolinj fun p => Or.inl ⟨p, rfl⟩) (hinj _ hT fun p => Or.inr ⟨p, rfl⟩)
  have hfix : ∀ x : Fin n, x ∈ Sᶜ → g x = x := fun x hx => hg (Sum.inr ⟨x, hx⟩)
  have hcol : ∀ p : {x // x ∈ G}, g ((p : Fin n × Fin n).2) = T p := fun p => hg (Sum.inl p)
  refine ⟨g, hcol, fun x hx => ?_⟩
  by_cases hgx : ∃ q ∈ G, g x = q.2
  · exact Or.inr hgx
  · refine Or.inl ?_
    have hgxS : g x ∈ Sᶜ := by
      rintro (⟨p, hp⟩ | ⟨p, hp⟩)
      · exact hgx ⟨(p : Fin n × Fin n), p.2, hp.symm⟩
      · have hpx : g ((p : Fin n × Fin n).2) = g x := by rw [hcol p, hp]
        exact hx _ p.2 (g.injective hpx).symm
    exact g.injective (hfix _ hgxS)

/-- **The injection behind Theorem 6.5.5.**  Write `A` for the event that the transversal
contains `G`.  If `D` is stable under composing on the left with a shift permutation, then
`|A ∩ D| · n ! ≤ |A| · |D|`: the map `(σ, τ) ↦ (g τ⁻¹ * τ, g τ * σ)`, where `g τ` shifts the
columns of `G` onto `τ`'s values on the rows of `G`, embeds `(A ∩ D) × Perm` into `A × D`. -/
private lemma ncard_mul_card_perm_le (G : Finset (Fin n × Fin n)) (hG : IsPartialMatching G)
    (D : Set (Equiv.Perm (Fin n)))
    (hD : ∀ g σ : Equiv.Perm (Fin n),
      (∀ x : Fin n, (∀ p ∈ G, x ≠ p.2) → (g x = x ∨ ∃ q ∈ G, g x = q.2)) →
      σ ∈ containsEntries G → σ ∈ D → g * σ ∈ D) :
    (containsEntries G ∩ D).ncard * Nat.card (Equiv.Perm (Fin n))
      ≤ (containsEntries G).ncard * D.ncard := by
  classical
  have hrow : ∀ τ : Equiv.Perm (Fin n),
      Function.Injective (fun p : {x // x ∈ G} => τ ((p : Fin n × Fin n).1)) := by
    intro τ p q h
    exact Subtype.ext (hG.1 _ p.2 _ q.2 (τ.injective h))
  have key : ∀ T : {x // x ∈ G} → Fin n, ∃ g : Equiv.Perm (Fin n),
      Function.Injective T →
        ((∀ p : {x // x ∈ G}, g ((p : Fin n × Fin n).2) = T p) ∧
          ∀ x : Fin n, (∀ p ∈ G, x ≠ p.2) → (g x = x ∨ ∃ q ∈ G, g x = q.2)) := by
    intro T
    by_cases hT : Function.Injective T
    · obtain ⟨g, h1, h2⟩ := exists_matchingShift G hG T hT
      exact ⟨g, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨1, fun h => absurd h hT⟩
  choose sh hsh using key
  set sft : Equiv.Perm (Fin n) → Equiv.Perm (Fin n) :=
    fun τ => sh fun p : {x // x ∈ G} => τ ((p : Fin n × Fin n).1) with hsftdef
  have hsft1 : ∀ (τ : Equiv.Perm (Fin n)) (p : Fin n × Fin n), p ∈ G → sft τ p.2 = τ p.1 :=
    fun τ p hp => (hsh _ (hrow τ)).1 ⟨p, hp⟩
  have hsft2 : ∀ τ : Equiv.Perm (Fin n), ∀ x : Fin n, (∀ p ∈ G, x ≠ p.2) →
      (sft τ x = x ∨ ∃ q ∈ G, sft τ x = q.2) := fun τ => (hsh _ (hrow τ)).2
  have hmemA : ∀ τ : Equiv.Perm (Fin n), (sft τ)⁻¹ * τ ∈ containsEntries G := by
    intro τ p hp
    show (sft τ)⁻¹ (τ p.1) = p.2
    rw [← hsft1 τ p hp]
    exact Equiv.Perm.inv_eq_iff_eq.mpr rfl
  have hmemD : ∀ σ : Equiv.Perm (Fin n), σ ∈ containsEntries G ∩ D →
      ∀ τ : Equiv.Perm (Fin n), sft τ * σ ∈ D :=
    fun σ hσ τ => hD _ _ (hsft2 τ) hσ.1 hσ.2
  simp only [← Nat.card_coe_set_eq, ← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun x => (⟨(sft x.2)⁻¹ * x.2, hmemA x.2⟩, ⟨sft x.2 * (x.1 : Equiv.Perm (Fin n)),
      hmemD _ x.1.2 x.2⟩)) ?_
  rintro ⟨⟨σ, hσ⟩, τ⟩ ⟨⟨σ', hσ'⟩, τ'⟩ h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hT : (fun p : {x // x ∈ G} => τ ((p : Fin n × Fin n).1))
      = fun p : {x // x ∈ G} => τ' ((p : Fin n × Fin n).1) := by
    funext p
    have e1 : (sft τ * σ) ((p : Fin n × Fin n).1) = τ ((p : Fin n × Fin n).1) := by
      rw [Equiv.Perm.mul_apply, hσ.1 _ p.2, hsft1 τ _ p.2]
    have e2 : (sft τ' * σ') ((p : Fin n × Fin n).1) = τ' ((p : Fin n × Fin n).1) := by
      rw [Equiv.Perm.mul_apply, hσ'.1 _ p.2, hsft1 τ' _ p.2]
    rw [← e1, ← e2, h2]
  have hg : sft τ = sft τ' := by
    simp only [hsftdef]
    exact congrArg sh hT
  rw [hg] at h1 h2
  have hσσ : σ = σ' := mul_left_cancel h2
  have hττ : τ = τ' := mul_left_cancel h1
  subst hσσ
  subst hττ
  rfl

/-- **Theorem 6.5.5 for permutations**: joining two events whose position sets share a row or a
column gives a valid negative dependency graph. -/
theorem uniformPerm_negativeDependency_matchings {ι : Type*} [Fintype ι]
    (F : ι → Finset (Fin n × Fin n)) (hF : ∀ i, IsPartialMatching (F i)) (N : ι → Finset ι)
    (hN : ∀ i j, j ≠ i → j ∉ N i → VertexDisjoint (F i) (F j)) :
    IsNegativeDependencyGraph (uniformPerm n) (fun i => containsEntries (F i)) N := by
  intro i s hs
  have hstable : ∀ g σ : Equiv.Perm (Fin n),
      (∀ x : Fin n, (∀ p ∈ F i, x ≠ p.2) → (g x = x ∨ ∃ q ∈ F i, g x = q.2)) →
      σ ∈ containsEntries (F i) → σ ∈ ⋂ j ∈ s, (containsEntries (F j))ᶜ →
      g * σ ∈ ⋂ j ∈ s, (containsEntries (F j))ᶜ := by
    intro g σ hdich hσA hσD
    rw [Set.mem_iInter₂]
    intro j hj
    have hvd : VertexDisjoint (F i) (F j) := hN i j (hs j hj).1 (hs j hj).2
    have hσj : σ ∉ containsEntries (F j) := Set.mem_iInter₂.1 hσD j hj
    intro hc
    refine hσj fun p hp => ?_
    have hcp : g (σ p.1) = p.2 := by
      have hgc := hc p hp
      rwa [Equiv.Perm.mul_apply] at hgc
    have hnotcol : ∀ q ∈ F i, σ p.1 ≠ q.2 := by
      intro q hq hEq
      have hss : σ p.1 = σ q.1 := by rw [hEq, hσA q hq]
      exact hvd.1 q hq p hp (σ.injective hss).symm
    rcases hdich (σ p.1) hnotcol with hfix | ⟨r, hr, hrr⟩
    · exact hfix.symm.trans hcp
    · exact absurd (hrr.symm.trans hcp) (hvd.2 r hr p hp)
  show uniformPerm n (containsEntries (F i) ∩ ⋂ j ∈ s, (containsEntries (F j))ᶜ)
      ≤ uniformPerm n (containsEntries (F i)) * uniformPerm n (⋂ j ∈ s, (containsEntries (F j))ᶜ)
  rw [uniformPerm_apply_ncard, uniformPerm_apply_ncard, uniformPerm_apply_ncard]
  exact natCast_div_le_mul_div _ _ _ _ Nat.card_pos.ne'
    (ncard_mul_card_perm_le (F i) (hF i) _ hstable)

/-- **Theorem 6.5.11** (Erdős–Spencer 1991): an `n × n` array in which every symbol occurs at
most `n / (4e)` times has a Latin transversal — a permutation `σ` along which the entries
`A i (σ i)` are all distinct. -/
theorem exists_latin_transversal {α : Type*} [DecidableEq α] (A : Fin n → Fin n → α)
    (h : ∀ s : α,
      (((univ : Finset (Fin n × Fin n)).filter fun p => A p.1 p.2 = s).card : ℝ)
        ≤ (n : ℝ) / (4 * Real.exp 1)) :
    ∃ σ : Equiv.Perm (Fin n), Function.Injective fun i => A i (σ i) := by
  sorry

end ProbMethodCombinatorics
