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
  classical
  have hmemC : ∀ σ : Equiv.Perm (Fin n), σ ∈ containsEntries F ↔ ∀ p ∈ F, σ p.1 = p.2 :=
    fun _ => Iff.rfl
  obtain ⟨σ₀, hσ₀⟩ :=
    Equiv.Perm.exists_extending_pair (fun p : {x : Fin n × Fin n // x ∈ F} => p.1.1)
      (fun p : {x : Fin n × Fin n // x ∈ F} => p.1.2)
      (fun p q h => Subtype.ext (hF.1 p.1 p.2 q.1 q.2 h))
      (fun p q h => Subtype.ext (hF.2 p.1 p.2 q.1 q.2 h))
  have hσ₀' : ∀ p ∈ F, σ₀ p.1 = p.2 := fun p hp => hσ₀ ⟨p, hp⟩
  have hiff : ∀ (σ : Equiv.Perm (Fin n)) (a : Fin n), (σ₀⁻¹ * σ) a = a ↔ σ a = σ₀ a := by
    intro σ a
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
  have hmem : ∀ σ : Equiv.Perm (Fin n),
      σ ∈ containsEntries F ↔ ∀ a, ¬ a ∉ F.image Prod.fst → (σ₀⁻¹ * σ) a = a := by
    intro σ
    rw [hmemC]
    simp only [hiff, not_not]
    refine ⟨fun hσ a ha => ?_, fun h p hp => ?_⟩
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ha
      rw [hσ p hp, hσ₀' p hp]
    · rw [h p.1 (Finset.mem_image_of_mem _ hp), hσ₀' p hp]
  have hRcard : (F.image Prod.fst).card = F.card :=
    Finset.card_image_of_injOn fun p hp q hq h => hF.1 p hp q hq h
  have hcard : Fintype.card {σ : Equiv.Perm (Fin n) // σ ∈ containsEntries F}
      = (n - F.card)! := by
    have e1 : {σ : Equiv.Perm (Fin n) // σ ∈ containsEntries F}
        ≃ Equiv.Perm {i : Fin n // i ∉ F.image Prod.fst} :=
      (Equiv.subtypeEquiv (Equiv.mulLeft σ₀⁻¹) hmem).trans
        (Equiv.Perm.subtypeEquivSubtypePerm fun i : Fin n => i ∉ F.image Prod.fst).symm
    rw [Fintype.card_congr e1, Fintype.card_perm, Fintype.card_subtype_compl,
      Fintype.card_coe, Fintype.card_fin, hRcard]
  have hcount : Measure.count (containsEntries F) = (((n - F.card)! : ℕ) : ENNReal) := by
    have hms : MeasurableSet (containsEntries F) := trivial
    rw [Measure.count_apply hms, Set.encard_eq_coe_toFinset_card, Set.toFinset_card, hcard]
    norm_cast
  rw [measureReal_def, uniformPerm, ProbabilityTheory.uniformOn_univ, hcount, Fintype.card_perm,
    Fintype.card_fin, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]

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

/-- `(n - 2)! / n !` is `1 / (n (n - 1))` once `n ≥ 2`. -/
private theorem latin_factorial_pair_div (hn : 2 ≤ n) :
    ((n - 2)! : ℝ) / (n ! : ℝ) = 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have hmpos : (0 : ℝ) < ((m ! : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hm0 : ((m ! : ℕ) : ℝ) ≠ 0 := ne_of_gt hmpos
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
  have hkey : m + 1 + 1 - 2 = m := by omega
  have hfac : (m + 1 + 1)! = (m + 1 + 1) * ((m + 1) * m !) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
  rw [hkey, hfac]
  have hc : (((m + 1 + 1) * ((m + 1) * m !) : ℕ) : ℝ)
      = ((m : ℝ) + 2) * (((m : ℝ) + 1) * ((m ! : ℕ) : ℝ)) := by push_cast; ring
  have hd : ((m + 1 + 1 : ℕ) : ℝ) * (((m + 1 + 1 : ℕ) : ℝ) - 1)
      = ((m : ℝ) + 2) * ((m : ℝ) + 1) := by push_cast; ring
  rw [hc, hd, div_eq_div_iff (mul_ne_zero hm2 (mul_ne_zero hm1 hm0)) (mul_ne_zero hm2 hm1)]
  ring

/-- Two rows and two columns of the array meet at most `4n` positions. -/
private theorem latin_cross_card_le (r₁ r₂ c₁ c₂ : Fin n) :
    (({r₁} ×ˢ (univ : Finset (Fin n)) ∪ {r₂} ×ˢ (univ : Finset (Fin n))
        ∪ (univ : Finset (Fin n)) ×ˢ {c₁} ∪ (univ : Finset (Fin n)) ×ˢ {c₂} :
      Finset (Fin n × Fin n))).card ≤ 4 * n := by
  have hrow : ∀ r : Fin n,
      ({r} ×ˢ (univ : Finset (Fin n)) : Finset (Fin n × Fin n)).card = n := by
    intro r
    rw [Finset.card_product]
    simp
  have hcol : ∀ c : Fin n,
      ((univ : Finset (Fin n)) ×ˢ {c} : Finset (Fin n × Fin n)).card = n := by
    intro c
    rw [Finset.card_product]
    simp
  refine le_trans (Finset.card_union_le _ _) ?_
  refine le_trans (Nat.add_le_add_right (Finset.card_union_le _ _) _) ?_
  refine le_trans (Nat.add_le_add_right
    (Nat.add_le_add_right (Finset.card_union_le _ _) _) _) ?_
  rw [hrow, hrow, hcol, hcol]
  omega

/-- A union over an index `Finset` of blocks of size at most `b` has size at most
`card * b`. -/
private theorem latin_biUnion_card_le {β : Type*} [DecidableEq β]
    (Z : Finset (Fin n × Fin n)) (S : Fin n × Fin n → Finset β) (b : ℝ)
    (hS : ∀ z, ((S z).card : ℝ) ≤ b) :
    (((Z.biUnion S).card : ℕ) : ℝ) ≤ (Z.card : ℝ) * b := by
  calc (((Z.biUnion S).card : ℕ) : ℝ) ≤ ((∑ z ∈ Z, (S z).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ = ∑ z ∈ Z, ((S z).card : ℝ) := Nat.cast_sum _ _
    _ ≤ ∑ z ∈ Z, b := Finset.sum_le_sum fun z _ => hS z
    _ = (Z.card : ℝ) * b := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Positions carrying the same symbol as `z`, other than `z` itself, number at most
`n / (4e) - 1`. -/
private theorem latin_symbol_class_card_le {α : Type*} [DecidableEq α] (A : Fin n → Fin n → α)
    (h : ∀ s : α,
      (((univ : Finset (Fin n × Fin n)).filter fun p => A p.1 p.2 = s).card : ℝ)
        ≤ (n : ℝ) / (4 * Real.exp 1)) (z : Fin n × Fin n) :
    ((((univ : Finset (Fin n × Fin n)).filter
        fun w => w ≠ z ∧ A w.1 w.2 = A z.1 z.2).image fun w => (z, w)).card : ℝ)
      ≤ (n : ℝ) / (4 * Real.exp 1) - 1 := by
  have himg : (((univ : Finset (Fin n × Fin n)).filter
      fun w => w ≠ z ∧ A w.1 w.2 = A z.1 z.2).image fun w => (z, w)).card
      = ((univ : Finset (Fin n × Fin n)).filter
          fun w => w ≠ z ∧ A w.1 w.2 = A z.1 z.2).card :=
    Finset.card_image_of_injective _ fun a b hab => congrArg Prod.snd hab
  have hz : z ∈ (univ : Finset (Fin n × Fin n)).filter fun w => A w.1 w.2 = A z.1 z.2 := by
    simp
  have herase : ((univ : Finset (Fin n × Fin n)).filter
      fun w => w ≠ z ∧ A w.1 w.2 = A z.1 z.2)
      = ((univ : Finset (Fin n × Fin n)).filter fun w => A w.1 w.2 = A z.1 z.2).erase z := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  have hone : 1 ≤ ((univ : Finset (Fin n × Fin n)).filter
      fun w => A w.1 w.2 = A z.1 z.2).card := Finset.card_pos.2 ⟨z, hz⟩
  rw [himg, herase, Finset.card_erase_of_mem hz, Nat.cast_sub hone, Nat.cast_one]
  have hb := h (A z.1 z.2)
  linarith

/-- The arithmetic behind step 4: `(4n)(n/(4e) - 1) ≤ n(n-1)/e - 1` for `n ≥ 11`. -/
private theorem latin_degree_arith_le (hn : 11 ≤ n) {c z : ℝ}
    (h1 : c ≤ z * ((n : ℝ) / (4 * Real.exp 1) - 1)) (h2 : z ≤ 4 * (n : ℝ)) :
    c ≤ (n : ℝ) * ((n : ℝ) - 1) / Real.exp 1 - 1 := by
  have hElow : (2.7 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have hEhigh : Real.exp 1 < 2.72 := by
    have := Real.exp_one_lt_d9
    linarith
  have hEpos : (0 : ℝ) < Real.exp 1 := by linarith
  have hn11 : (11 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hB : (0 : ℝ) ≤ (n : ℝ) / (4 * Real.exp 1) - 1 := by
    have hge : (1 : ℝ) ≤ (n : ℝ) / (4 * Real.exp 1) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    linarith
  have step1 : c ≤ 4 * (n : ℝ) * ((n : ℝ) / (4 * Real.exp 1) - 1) :=
    h1.trans (mul_le_mul_of_nonneg_right h2 hB)
  have hexp : 4 * (n : ℝ) * ((n : ℝ) / (4 * Real.exp 1) - 1)
      = (n : ℝ) * (n : ℝ) / Real.exp 1 - 4 * (n : ℝ) := by
    field_simp
  have hexp2 : (n : ℝ) * ((n : ℝ) - 1) / Real.exp 1 - 1
      = (n : ℝ) * (n : ℝ) / Real.exp 1 - (n : ℝ) / Real.exp 1 - 1 := by
    field_simp
  have hdiv : (n : ℝ) / Real.exp 1 ≤ (n : ℝ) := div_le_self (by linarith) (by linarith)
  rw [hexp] at step1
  rw [hexp2]
  linarith

/-- Step 4: a bad pair has at most `n(n-1)/e - 1` neighbours in the dependency graph. -/
private theorem latin_degree_card_le {T : Type*} [Fintype T] {α : Type*} [DecidableEq α]
    (hn : 11 ≤ n) (A : Fin n → Fin n → α)
    (h : ∀ s : α,
      (((univ : Finset (Fin n × Fin n)).filter fun p => A p.1 p.2 = s).card : ℝ)
        ≤ (n : ℝ) / (4 * Real.exp 1))
    (g : T → (Fin n × Fin n) × (Fin n × Fin n)) (hginj : Function.Injective g)
    (hgP : ∀ t : T, (g t).1.1 < (g t).2.1 ∧ (g t).1.2 ≠ (g t).2.2 ∧
      A (g t).1.1 (g t).1.2 = A (g t).2.1 (g t).2.2)
    (F : T → Finset (Fin n × Fin n))
    (hFmem : ∀ (t : T) (x : Fin n × Fin n), x ∈ F t ↔ x = (g t).1 ∨ x = (g t).2)
    (N : T → Finset T)
    (hNmem : ∀ t t' : T, t' ∈ N t ↔ ∃ x ∈ F t, ∃ y ∈ F t', x.1 = y.1 ∨ x.2 = y.2)
    (t : T) : ((N t).card : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) / Real.exp 1 - 1 := by
  have hgne : ∀ s : T, (g s).1 ≠ (g s).2 := fun s hEq =>
    absurd (congrArg Prod.fst hEq) (ne_of_lt (hgP s).1)
  obtain ⟨Z, hZdef⟩ : ∃ Z : Finset (Fin n × Fin n), Z =
      {(g t).1.1} ×ˢ (univ : Finset (Fin n)) ∪ {(g t).2.1} ×ˢ (univ : Finset (Fin n))
        ∪ (univ : Finset (Fin n)) ×ˢ {(g t).1.2}
        ∪ (univ : Finset (Fin n)) ×ˢ {(g t).2.2} := ⟨_, rfl⟩
  have hZmem : ∀ x : Fin n × Fin n, x ∈ Z ↔
      (x.1 = (g t).1.1 ∨ x.1 = (g t).2.1 ∨ x.2 = (g t).1.2 ∨ x.2 = (g t).2.2) := by
    intro x
    rw [hZdef]
    simp only [Finset.mem_union, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
      and_true, true_and, or_assoc]
  have hZcard : (Z.card : ℝ) ≤ 4 * (n : ℝ) := by
    have hcc := latin_cross_card_le (g t).1.1 (g t).2.1 (g t).1.2 (g t).2.2
    rw [← hZdef] at hcc
    exact_mod_cast hcc
  obtain ⟨W, hWdef⟩ : ∃ W : Finset ((Fin n × Fin n) × (Fin n × Fin n)), W =
      Z.biUnion (fun z => ((univ : Finset (Fin n × Fin n)).filter
        fun w => w ≠ z ∧ A w.1 w.2 = A z.1 z.2).image fun w => (z, w)) := ⟨_, rfl⟩
  have hWcard : (W.card : ℝ) ≤ (Z.card : ℝ) * ((n : ℝ) / (4 * Real.exp 1) - 1) := by
    rw [hWdef]
    exact latin_biUnion_card_le Z _ _ fun z => latin_symbol_class_card_le A h z
  obtain ⟨pk, hpkdef⟩ : ∃ pk : T → (Fin n × Fin n) × (Fin n × Fin n), ∀ s : T,
      pk s = if (g s).1 ∈ Z then ((g s).1, (g s).2) else ((g s).2, (g s).1) :=
    ⟨_, fun _ => rfl⟩
  have hpkinj : ∀ a b : T, pk a = pk b → a = b := by
    intro a b hab
    rw [hpkdef, hpkdef] at hab
    by_cases ha : (g a).1 ∈ Z
    · rw [if_pos ha] at hab
      by_cases hb : (g b).1 ∈ Z
      · rw [if_pos hb, Prod.mk.injEq] at hab
        exact hginj (Prod.ext_iff.mpr ⟨hab.1, hab.2⟩)
      · rw [if_neg hb, Prod.mk.injEq] at hab
        exfalso
        have hlt := (hgP a).1
        rw [hab.1, hab.2] at hlt
        exact absurd (hlt.trans (hgP b).1) (lt_irrefl _)
    · rw [if_neg ha] at hab
      by_cases hb : (g b).1 ∈ Z
      · rw [if_pos hb, Prod.mk.injEq] at hab
        exfalso
        have hlt := (hgP b).1
        rw [← hab.1, ← hab.2] at hlt
        exact absurd (hlt.trans (hgP a).1) (lt_irrefl _)
      · rw [if_neg hb, Prod.mk.injEq] at hab
        exact hginj (Prod.ext_iff.mpr ⟨hab.2, hab.1⟩)
  have hpkmaps : ∀ s ∈ N t, pk s ∈ W := by
    intro s hs
    rw [hNmem] at hs
    obtain ⟨x, hx, y, hy, hxy⟩ := hs
    have hyZ : y ∈ Z := by
      rw [hZmem]
      rw [hFmem] at hx
      rcases hx with rfl | rfl
      · rcases hxy with hxy | hxy
        · exact Or.inl hxy.symm
        · exact Or.inr (Or.inr (Or.inl hxy.symm))
      · rcases hxy with hxy | hxy
        · exact Or.inr (Or.inl hxy.symm)
        · exact Or.inr (Or.inr (Or.inr hxy.symm))
    have hor : (g s).1 ∈ Z ∨ (g s).2 ∈ Z := by
      rcases (hFmem s y).1 hy with rfl | rfl
      · exact Or.inl hyZ
      · exact Or.inr hyZ
    rw [hWdef, hpkdef]
    by_cases hz : (g s).1 ∈ Z
    · rw [if_pos hz]
      refine Finset.mem_biUnion.2 ⟨(g s).1, hz, Finset.mem_image.2 ⟨(g s).2, ?_, rfl⟩⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (hgne s).symm, ((hgP s).2.2).symm⟩
    · rw [if_neg hz]
      refine Finset.mem_biUnion.2
        ⟨(g s).2, hor.resolve_left hz, Finset.mem_image.2 ⟨(g s).1, ?_, rfl⟩⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hgne s, (hgP s).2.2⟩
  have hcards : (N t).card ≤ W.card :=
    Finset.card_le_card_of_injOn pk
      (fun s hs => Finset.mem_coe.2 (hpkmaps s (Finset.mem_coe.1 hs)))
      (fun a _ b _ hab => hpkinj a b hab)
  have hfin : ((N t).card : ℝ) ≤ (Z.card : ℝ) * ((n : ℝ) / (4 * Real.exp 1) - 1) := by
    have hcast : ((N t).card : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hcards
    linarith
  exact latin_degree_arith_le hn hfin hZcard

/-- Steps 1–6 of the Erdős–Spencer argument for `n ≥ 11`: some permutation avoids every
bad pair of equal entries. -/
private theorem latin_exists_avoiding {α : Type*} [DecidableEq α] (hn : 11 ≤ n)
    (A : Fin n → Fin n → α)
    (h : ∀ s : α,
      (((univ : Finset (Fin n × Fin n)).filter fun p => A p.1 p.2 = s).card : ℝ)
        ≤ (n : ℝ) / (4 * Real.exp 1)) :
    ∃ σ : Equiv.Perm (Fin n), ∀ p q : Fin n × Fin n, p.1 < q.1 → p.2 ≠ q.2 →
      A p.1 p.2 = A q.1 q.2 → ¬(σ p.1 = p.2 ∧ σ q.1 = q.2) := by
  classical
  obtain ⟨T, instT, g, hginj, hgP, hgsurj⟩ :
      ∃ (T : Type) (_ : Fintype T) (g : T → (Fin n × Fin n) × (Fin n × Fin n)),
        Function.Injective g ∧
        (∀ t : T, (g t).1.1 < (g t).2.1 ∧ (g t).1.2 ≠ (g t).2.2 ∧
          A (g t).1.1 (g t).1.2 = A (g t).2.1 (g t).2.2) ∧
        (∀ e : (Fin n × Fin n) × (Fin n × Fin n), e.1.1 < e.2.1 → e.1.2 ≠ e.2.2 →
          A e.1.1 e.1.2 = A e.2.1 e.2.2 → ∃ t : T, g t = e) :=
    ⟨{e : (Fin n × Fin n) × (Fin n × Fin n) // e.1.1 < e.2.1 ∧ e.1.2 ≠ e.2.2 ∧
        A e.1.1 e.1.2 = A e.2.1 e.2.2}, inferInstance, Subtype.val, Subtype.val_injective,
      fun t => t.2, fun e h1 h2 h3 => ⟨⟨e, h1, h2, h3⟩, rfl⟩⟩
  have hgne : ∀ t : T, (g t).1 ≠ (g t).2 := fun t hEq =>
    absurd (congrArg Prod.fst hEq) (ne_of_lt (hgP t).1)
  obtain ⟨F, hFdef⟩ : ∃ F : T → Finset (Fin n × Fin n), ∀ t : T, F t = {(g t).1, (g t).2} :=
    ⟨_, fun _ => rfl⟩
  have hFmem : ∀ (t : T) (x : Fin n × Fin n), x ∈ F t ↔ x = (g t).1 ∨ x = (g t).2 := by
    intro t x
    rw [hFdef]
    simp only [Finset.mem_insert, Finset.mem_singleton]
  have hFcard : ∀ t : T, (F t).card = 2 := by
    intro t
    rw [hFdef]
    exact Finset.card_pair (hgne t)
  have hFmatch : ∀ t : T, IsPartialMatching (F t) := by
    intro t
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxy
      rw [hFmem] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · rfl
      · exact absurd hxy (ne_of_lt (hgP t).1)
      · exact absurd hxy.symm (ne_of_lt (hgP t).1)
      · rfl
    · intro x hx y hy hxy
      rw [hFmem] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · rfl
      · exact absurd hxy (hgP t).2.1
      · exact absurd hxy.symm (hgP t).2.1
      · rfl
  obtain ⟨N, hNdef⟩ : ∃ N : T → Finset T, ∀ t : T, N t =
      univ.filter (fun t' => ∃ x ∈ F t, ∃ y ∈ F t', x.1 = y.1 ∨ x.2 = y.2) :=
    ⟨_, fun _ => rfl⟩
  have hNmem : ∀ t t' : T, t' ∈ N t ↔ ∃ x ∈ F t, ∃ y ∈ F t', x.1 = y.1 ∨ x.2 = y.2 := by
    intro t t'
    rw [hNdef, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
  have hNvd : ∀ t t' : T, t' ≠ t → t' ∉ N t → VertexDisjoint (F t) (F t') := by
    intro t t' _ hnot
    rw [hNmem] at hnot
    exact ⟨fun x hx y hy hEq => hnot ⟨x, hx, y, hy, Or.inl hEq⟩,
      fun x hx y hy hEq => hnot ⟨x, hx, y, hy, Or.inr hEq⟩⟩
  have hND : IsNegativeDependencyGraph (uniformPerm n) (fun t => containsEntries (F t)) N :=
    uniformPerm_negativeDependency_matchings F hFmatch N hNvd
  have hprob : ∀ t : T, ((uniformPerm n) (containsEntries (F t))).toReal
      = 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    intro t
    have hval := uniformPerm_containsEntries (F t) (hFmatch t)
    rw [measureReal_def] at hval
    rw [hval, hFcard t]
    exact latin_factorial_pair_div (by omega)
  have hdeg : ∀ t : T, ((N t).card : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) / Real.exp 1 - 1 :=
    fun t => latin_degree_card_le hn A h g hginj hgP F hFmem N hNmem t
  have hEpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hEne : Real.exp 1 ≠ 0 := ne_of_gt hEpos
  have hn11 : (11 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hM : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have hMne : (n : ℝ) * ((n : ℝ) - 1) ≠ 0 := ne_of_gt hM
  have hD1 : 1 ≤ ⌊(n : ℝ) * ((n : ℝ) - 1) / Real.exp 1⌋₊ := by
    refine Nat.le_floor ?_
    rw [Nat.cast_one, le_div_iff₀ hEpos]
    have hEhigh : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - 11)
      (by linarith : (0 : ℝ) ≤ (n : ℝ) + 10)]
  have hfloorle : ((⌊(n : ℝ) * ((n : ℝ) - 1) / Real.exp 1⌋₊ : ℕ) : ℝ)
      ≤ (n : ℝ) * ((n : ℝ) - 1) / Real.exp 1 := Nat.floor_le (le_of_lt (div_pos hM hEpos))
  have hdle : ∀ t : T, (N t).card ≤ ⌊(n : ℝ) * ((n : ℝ) - 1) / Real.exp 1⌋₊ - 1 := by
    intro t
    have h2 : (((N t).card + 1 : ℕ) : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) / Real.exp 1 := by
      have h1 := hdeg t
      push_cast
      linarith
    have h3 := Nat.le_floor h2
    omega
  have harith : Real.exp 1 * (1 / ((n : ℝ) * ((n : ℝ) - 1)))
      * (((⌊(n : ℝ) * ((n : ℝ) - 1) / Real.exp 1⌋₊ - 1 : ℕ) : ℝ) + 1) ≤ 1 := by
    have hc : (((⌊(n : ℝ) * ((n : ℝ) - 1) / Real.exp 1⌋₊ - 1 : ℕ) : ℝ) + 1)
        = ((⌊(n : ℝ) * ((n : ℝ) - 1) / Real.exp 1⌋₊ : ℕ) : ℝ) := by
      rw [Nat.cast_sub hD1, Nat.cast_one]
      ring
    have hnn : (0 : ℝ) ≤ Real.exp 1 * (1 / ((n : ℝ) * ((n : ℝ) - 1))) :=
      mul_nonneg hEpos.le (one_div_pos.2 hM).le
    rw [hc]
    calc Real.exp 1 * (1 / ((n : ℝ) * ((n : ℝ) - 1)))
          * ((⌊(n : ℝ) * ((n : ℝ) - 1) / Real.exp 1⌋₊ : ℕ) : ℝ)
        ≤ Real.exp 1 * (1 / ((n : ℝ) * ((n : ℝ) - 1)))
          * ((n : ℝ) * ((n : ℝ) - 1) / Real.exp 1) := mul_le_mul_of_nonneg_left hfloorle hnn
      _ = (Real.exp 1 / Real.exp 1)
          * (((n : ℝ) * ((n : ℝ) - 1)) / ((n : ℝ) * ((n : ℝ) - 1))) := by ring
      _ = 1 := by rw [div_self hEne, div_self hMne, one_mul]
  have hpos : 0 < ((uniformPerm n) (⋂ t : T, (containsEntries (F t))ᶜ)).toReal :=
    lopsided_local_lemma_symmetric (fun t => containsEntries (F t)) (fun _ => trivial) N hND
      (p := 1 / ((n : ℝ) * ((n : ℝ) - 1)))
      (d := ⌊(n : ℝ) * ((n : ℝ) - 1) / Real.exp 1⌋₊ - 1)
      (fun t => le_of_eq (hprob t)) hdle harith
  rcases Set.eq_empty_or_nonempty (⋂ t : T, (containsEntries (F t))ᶜ) with hE | hE
  · rw [hE, measure_empty] at hpos
    simp at hpos
  obtain ⟨σ, hσ⟩ := hE
  refine ⟨σ, ?_⟩
  rintro p q hpq hcol hsym ⟨h1, h2⟩
  obtain ⟨t, ht⟩ := hgsurj (p, q) hpq hcol hsym
  have hmem : σ ∉ containsEntries (F t) := Set.mem_iInter.1 hσ t
  refine hmem fun x hx => ?_
  rw [hFmem, ht] at hx
  rcases hx with rfl | rfl
  · exact h1
  · exact h2

/-- **Theorem 6.5.11** (Erdős–Spencer 1991): an `n × n` array in which every symbol occurs at
most `n / (4e)` times has a Latin transversal — a permutation `σ` along which the entries
`A i (σ i)` are all distinct. -/
theorem exists_latin_transversal {α : Type*} [DecidableEq α] (A : Fin n → Fin n → α)
    (h : ∀ s : α,
      (((univ : Finset (Fin n × Fin n)).filter fun p => A p.1 p.2 = s).card : ℝ)
        ≤ (n : ℝ) / (4 * Real.exp 1)) :
    ∃ σ : Equiv.Perm (Fin n), Function.Injective fun i => A i (σ i) := by
  rcases Nat.lt_or_ge n 11 with hsmall | hbig
  · rcases Nat.eq_zero_or_pos n with rfl | hpos
    · refine ⟨1, ?_⟩
      intro a b _
      exact a.elim0
    · exfalso
      obtain ⟨z⟩ : Nonempty (Fin n × Fin n) := ⟨(⟨0, hpos⟩, ⟨0, hpos⟩)⟩
      have hz : z ∈ (univ : Finset (Fin n × Fin n)).filter fun p => A p.1 p.2 = A z.1 z.2 := by
        simp
      have honeN : 1 ≤ ((univ : Finset (Fin n × Fin n)).filter
          fun p => A p.1 p.2 = A z.1 z.2).card := Finset.card_pos.2 ⟨z, hz⟩
      have hone : (1 : ℝ) ≤ (((univ : Finset (Fin n × Fin n)).filter
          fun p => A p.1 p.2 = A z.1 z.2).card : ℝ) := by exact_mod_cast honeN
      have hb := h (A z.1 z.2)
      have hElow : (2.7 : ℝ) < Real.exp 1 := by
        have := Real.exp_one_gt_d9
        linarith
      have hn10 : (n : ℝ) ≤ 10 := by
        have hle : n ≤ 10 := by omega
        exact_mod_cast hle
      have hlt1 : (n : ℝ) / (4 * Real.exp 1) < 1 := by
        rw [div_lt_one (by linarith)]
        linarith
      linarith
  · obtain ⟨σ, hσ⟩ := latin_exists_avoiding hbig A h
    refine ⟨σ, ?_⟩
    intro i j hij
    by_contra hne
    rcases lt_trichotomy i j with hlt | heq | hlt
    · exact hσ (i, σ i) (j, σ j) hlt (fun hc => hne (σ.injective hc)) hij ⟨rfl, rfl⟩
    · exact hne heq
    · exact hσ (j, σ j) (i, σ i) hlt (fun hc => hne (σ.injective hc).symm) hij.symm ⟨rfl, rfl⟩

end ProbMethodCombinatorics
