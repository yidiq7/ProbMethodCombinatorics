import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.Order.UpperLower.Basic
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.Probability.Independence.InfinitePi

/-!
# Chapter 7: Correlation Inequalities

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Chapter 7.

The chapter's slogan is that **increasing events of independent variables are positively
correlated**.  Two pieces of it are already in Mathlib and are recorded as upstream nodes:

* `IsUpperSet.le_card_inter_finset` — Harris–Kleitman, which is Theorem 7.1.1 for the
  *uniform* measure on subsets, in counting form;
* `fkg` — the Fortuin–Kasteleyn–Ginibre inequality for a log-supermodular measure on a
  distributive lattice.

What is not upstream is the case the applications need: a product of Bernoulli measures with
*arbitrary* edge probability, i.e. the binomial random graph `G(V, p)`.  That is stated here.
-/

namespace ProbMethodCombinatorics

open MeasureTheory ProbabilityTheory unitInterval SimpleGraph
open scoped ENNReal

variable {V : Type*} [Fintype V]

/-- **Harris' inequality for the binomial random graph** (Zhao, Theorem 7.1.1).  Two increasing
graph properties are positively correlated under `G(V, p)`.

Mathlib's `IsUpperSet.le_card_inter_finset` is the `p = 1/2` case in counting form; the content
here is that the edge probability may be arbitrary. -/
theorem binomialRandom_mul_le_inter (p : I) (A B : Set (SimpleGraph V))
    (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    binomialRandom V p A * binomialRandom V p B ≤ binomialRandom V p (A ∩ B) := by
  classical
  -- `SimpleGraph V` carries the discrete σ-algebra, so every singleton is measurable.
  have : MeasurableSingletonClass (SimpleGraph V) :=
    ⟨fun G => by
      have h : ({G} : Set (SimpleGraph V)) = SimpleGraph.Adj ⁻¹' {G.Adj} := by
        ext H; simp only [Set.mem_singleton_iff, Set.mem_preimage, SimpleGraph.adj_inj]
      rw [h]; exact measurable_adj (measurableSet_singleton _)⟩
  -- `μ G` is the `ℝ≥0`-valued mass that `G(V, p)` puts on the single graph `G`.
  obtain ⟨μ, hμ⟩ : ∃ μ : SimpleGraph V → NNReal,
      ∀ G, (μ G : ENNReal) = binomialRandom V p {G} :=
    ⟨fun G => (binomialRandom V p {G}).toNNReal,
      fun G => ENNReal.coe_toNNReal (measure_ne_top _ _)⟩
  -- Since there are finitely many graphs, `G(V, p) S` is the sum of `μ` over the members of `S`.
  have key : ∀ S : Set (SimpleGraph V),
      ((∑ G, μ G * (if G ∈ S then 1 else 0) : NNReal) : ENNReal) = binomialRandom V p S := by
    intro S
    rw [ENNReal.ofNNReal_finsetSum]
    simp only [hμ, apply_ite (ENNReal.ofNNReal), ENNReal.coe_zero, mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter, sum_measure_singleton]
    congr 1
    ext G
    simp
  -- The indicator of an upper set is monotone.
  have hmono : ∀ S : Set (SimpleGraph V), IsUpperSet S →
      Monotone (fun G : SimpleGraph V => if G ∈ S then (1 : NNReal) else 0) := by
    intro S hS a b hab
    dsimp only
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (hS hab h1) h2
    · exact zero_le
    · exact le_rfl
  -- `μ` is log-modular, because the edge count is a modular function of the graph.
  have hmod : ∀ a b : SimpleGraph V, μ a * μ b ≤ μ (a ⊓ b) * μ (a ⊔ b) := by
    have hle : ∀ K : SimpleGraph V, K.edgeSet.ncard ≤ (Nat.card V).choose 2 := by
      intro K
      have hcard : (Nat.card V).choose 2 = (Sym2.diagSetᶜ : Set (Sym2 V)).ncard := by
        rw [Nat.card_eq_fintype_card, ← Sym2.card_diagSet_compl, Fintype.card_eq_nat_card,
          ← Nat.card_coe_set_eq]
      rw [hcard]
      exact Set.ncard_le_ncard K.edgeSet_subset_compl_diagSet (Set.toFinite _)
    intro a b
    rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, ENNReal.coe_mul, hμ, hμ, hμ, hμ]
    have e1 : (a ⊓ b).edgeSet.ncard + (a ⊔ b).edgeSet.ncard
        = a.edgeSet.ncard + b.edgeSet.ncard := by
      rw [edgeSet_inf, edgeSet_sup,
        Set.ncard_inter_add_ncard_union _ _ (Set.toFinite _) (Set.toFinite _)]
    have e2 : ((Nat.card V).choose 2 - (a ⊓ b).edgeSet.ncard)
        + ((Nat.card V).choose 2 - (a ⊔ b).edgeSet.ncard)
        = ((Nat.card V).choose 2 - a.edgeSet.ncard)
          + ((Nat.card V).choose 2 - b.edgeSet.ncard) := by
      have := hle a; have := hle b; have := hle (a ⊓ b); have := hle (a ⊔ b); omega
    simp only [binomialRandom_singleton]
    rw [mul_mul_mul_comm, mul_mul_mul_comm ((toNNReal p : ENNReal) ^ (a ⊓ b).edgeSet.ncard),
      ← pow_add, ← pow_add, ← pow_add, ← pow_add, e1, e2]
  have hone : (∑ G, μ G) = 1 := by
    have h := key Set.univ
    simp only [Set.mem_univ, if_true, mul_one, measure_univ] at h
    exact_mod_cast h
  rw [← key A, ← key B, ← key (A ∩ B), ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  have hfkg := fkg (fun G : SimpleGraph V => if G ∈ A then (1 : NNReal) else 0)
    (fun G : SimpleGraph V => if G ∈ B then (1 : NNReal) else 0) μ
    (fun _ => zero_le) (fun _ => zero_le) (fun _ => zero_le)
    (hmono A hA) (hmono B hB) hmod
  rw [hone, one_mul] at hfkg
  refine hfkg.trans_eq (Finset.sum_congr rfl fun G _ => ?_)
  by_cases h1 : G ∈ A <;> by_cases h2 : G ∈ B <;> simp [h1, h2]

/-- **Decreasing events correlate too, and any number of them** (Zhao, Corollary 7.1.6): the
probability that every one of finitely many decreasing graph properties holds is at least the
product of their probabilities.

This is the form the applications use.  It follows from the pairwise increasing case by
complementation and induction on the family. -/
theorem prod_le_binomialRandom_iInter {ι : Type*} [Fintype ι] (p : I)
    (A : ι → Set (SimpleGraph V)) (hA : ∀ i, IsLowerSet (A i))
    (hAm : ∀ i, MeasurableSet (A i)) :
    ∏ i, binomialRandom V p (A i) ≤ binomialRandom V p (⋂ i, A i) := by
  classical
  -- The inclusion-exclusion rearrangement, additively so as to avoid truncated subtraction:
  -- `a`, `b` are the probabilities of two events, `a'`, `b'` those of their complements, and
  -- `u`, `w`, `c` those of the union, its complement, and the intersection.
  have arith : ∀ a a' b b' u w c : ENNReal, a + a' = 1 → b + b' = 1 → u + w = 1 →
      u + c = a + b → a' * b' ≤ w → a * b ≤ c := by
    intro a a' b b' u w c ha hb hu hc h
    have ha' : a' ≤ 1 := by rw [← ha]; exact le_add_self
    have hb' : b' ≤ 1 := by rw [← hb]; exact le_add_self
    have hab' : a' * b' ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (by simpa using mul_le_mul' ha' hb')
    have hutop : u ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (by rw [← hu]; exact le_self_add)
    have hexp : a * b + (a * b' + a' * b) + a' * b' = 1 := by
      calc a * b + (a * b' + a' * b) + a' * b' = (a + a') * (b + b') := by ring
        _ = 1 := by rw [ha, hb, one_mul]
    have hule : u ≤ a * b + (a * b' + a' * b) := by
      refine (ENNReal.add_le_add_iff_right hab').mp ?_
      calc u + a' * b' ≤ u + w := by gcongr
        _ = 1 := hu
        _ = a * b + (a * b' + a' * b) + a' * b' := hexp.symm
    refine (ENNReal.add_le_add_iff_right hutop).mp ?_
    calc a * b + u ≤ a * b + (a * b + (a * b' + a' * b)) := by gcongr
      _ = a * (b + b') + (a + a') * b := by ring
      _ = a + b := by rw [ha, hb, mul_one, one_mul]
      _ = c + u := by rw [← hc]; ring
  -- Two decreasing events, from the increasing case applied to the complements.
  have pair : ∀ S T : Set (SimpleGraph V), IsLowerSet S → IsLowerSet T →
      MeasurableSet S → MeasurableSet T →
      binomialRandom V p S * binomialRandom V p T ≤ binomialRandom V p (S ∩ T) := by
    intro S T hS hT hSm hTm
    have hcompl := binomialRandom_mul_le_inter p Sᶜ Tᶜ hS.compl hT.compl hSm.compl hTm.compl
    rw [← Set.compl_union] at hcompl
    have hSsum := measure_add_measure_compl (μ := binomialRandom V p) hSm
    have hTsum := measure_add_measure_compl (μ := binomialRandom V p) hTm
    have hUsum := measure_add_measure_compl (μ := binomialRandom V p) (hSm.union hTm)
    rw [measure_univ] at hSsum hTsum hUsum
    exact arith _ _ _ _ _ _ _ hSsum hTsum hUsum
      (measure_union_add_inter (μ := binomialRandom V p) S hTm) hcompl
  -- Induction on the family; a finite intersection of lower sets is again a lower set.
  have main : ∀ s : Finset ι,
      ∏ i ∈ s, binomialRandom V p (A i) ≤ binomialRandom V p (⋂ i ∈ s, A i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.set_biInter_insert]
        exact (mul_le_mul_right ih _).trans
          (pair (A a) (⋂ i ∈ s, A i) (hA a) (isLowerSet_iInter₂ fun i _ => hA i) (hAm a)
            (s.measurableSet_biInter fun i _ => hAm i))
  simpa using main Finset.univ

/-- **Zhao, Theorem 7.2.2**: `ℙ(G(n, p) is triangle-free) ≥ (1 - p³) ^ (n choose 3)`.

For each triple of vertices, "this triple does not span a triangle" is a decreasing event of
probability `1 - p³`; the triples are not independent, but Harris' inequality bounds the
probability that all of them hold by the product.

Chapter 8 proves a matching upper bound via Janson's inequality. -/
theorem le_binomialRandom_cliqueFree_three {n : ℕ} (p : I) :
    ENNReal.ofReal ((1 - (p : ℝ) ^ 3) ^ (n.choose 3))
      ≤ binomialRandom (Fin n) p {G : SimpleGraph (Fin n) | G.CliqueFree 3} := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := p.2.1
  have hcube : (p : ℝ) ^ 3 ≤ 1 := pow_le_one₀ hp0 p.2.2
  have hofReal : ENNReal.ofReal (p : ℝ) = (toNNReal p : ℝ≥0∞) := by
    rw [ENNReal.ofReal, Real.toNNReal_of_nonneg hp0]; rfl
  -- A prescribed finite set of non-loop edges is present with probability `p ^ |E|`: under the
  -- product of Bernoulli measures on `Sym2 (Fin n)` this event is a cylinder.
  have hedges : ∀ E : Finset (Sym2 (Fin n)), (∀ e ∈ E, ¬ e.IsDiag) →
      binomialRandom (Fin n) p {G : SimpleGraph (Fin n) | ∀ e ∈ E, e ∈ G.edgeSet}
        = (toNNReal p : ℝ≥0∞) ^ E.card := by
    intro E hE
    have himg : edgeSet '' {G : SimpleGraph (Fin n) | ∀ e ∈ E, e ∈ G.edgeSet}
        = {t ∈ ({t : Set (Sym2 (Fin n)) | ∀ e ∈ E, e ∈ t}) | t ⊆ Sym2.diagSetᶜ} := by
      ext t
      constructor
      · rintro ⟨G, hG, rfl⟩
        exact ⟨hG, G.edgeSet_subset_compl_diagSet⟩
      · rintro ⟨h1, h2⟩
        have hd : Disjoint t Sym2.diagSet := Set.subset_compl_iff_disjoint_right.mp h2
        refine ⟨fromEdgeSet t, ?_, ?_⟩
        · intro e he
          rw [edgeSet_fromEdgeSet, sdiff_eq_left.mpr hd]
          exact h1 e he
        · rw [edgeSet_fromEdgeSet, sdiff_eq_left.mpr hd]
    have hpre : (fun f : Sym2 (Fin n) → Prop ↦ {i | f i}) ⁻¹'
        {t : Set (Sym2 (Fin n)) | ∀ e ∈ E, e ∈ t}
        = Set.pi (↑E) (fun _ ↦ ({True} : Set Prop)) := by
      ext f
      simp [Set.mem_pi, eq_iff_iff]
    rw [binomialRandom_apply', himg, ← setBernoulli_apply_eq_apply_subsets, setBernoulli_apply',
      hpre, Measure.infinitePi_pi _ fun _ _ ↦ MeasurableSet.of_discrete,
      Finset.prod_congr rfl (g := fun _ ↦ (toNNReal p : ℝ≥0∞)) ?_, Finset.prod_const]
    intro e he
    have hmem : e ∈ Sym2.diagSetᶜ := by simpa [Sym2.mem_diagSet] using hE e he
    simp [Measure.dirac_apply', eq_true hmem]
  -- For a triple of vertices, "this triple is not a triangle" is measurable of probability
  -- `1 - p ^ 3`, since its complement asks for three distinct edges.
  have hkey : ∀ s : ↥(Finset.powersetCard 3 (Finset.univ : Finset (Fin n))),
      MeasurableSet {G : SimpleGraph (Fin n) | ¬ G.IsNClique 3 (s : Finset (Fin n))} ∧
      binomialRandom (Fin n) p {G : SimpleGraph (Fin n) | ¬ G.IsNClique 3 (s : Finset (Fin n))}
        = 1 - (toNNReal p : ℝ≥0∞) ^ 3 := by
    rintro ⟨s, hs⟩
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ :=
      Finset.card_eq_three.mp (Finset.mem_powersetCard_univ.mp hs)
    set E : Finset (Sym2 (Fin n)) := {s(a, b), s(a, c), s(b, c)} with hEdef
    have hEd : ∀ e ∈ E, ¬ e.IsDiag := by
      intro e he
      simp only [hEdef, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl <;> simp [Sym2.mk_isDiag_iff, hab, hac, hbc]
    have hEcard : E.card = 3 := by
      simp only [hEdef]
      rw [Finset.card_insert_of_notMem (by simp [hab, hac, hbc]),
        Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_singleton]
    have hcompl : {G : SimpleGraph (Fin n) | ¬ G.IsNClique 3 ({a, b, c} : Finset (Fin n))}
        = {G : SimpleGraph (Fin n) | ∀ e ∈ E, e ∈ G.edgeSet}ᶜ := by
      ext G
      simp [hEdef, is3Clique_triple_iff, mem_edgeSet]
    have hmeas : MeasurableSet {G : SimpleGraph (Fin n) | ∀ e ∈ E, e ∈ G.edgeSet} := by
      have hsplit : {G : SimpleGraph (Fin n) | ∀ e ∈ E, e ∈ G.edgeSet}
          = {G : SimpleGraph (Fin n) | G.Adj a b} ∩
            ({G : SimpleGraph (Fin n) | G.Adj a c} ∩ {G : SimpleGraph (Fin n) | G.Adj b c}) := by
        ext G
        simp [hEdef, mem_edgeSet]
      rw [hsplit]
      refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_) <;> measurability
    refine ⟨hcompl ▸ hmeas.compl, ?_⟩
    rw [hcompl, prob_compl_eq_one_sub hmeas, hedges E hEd, hEcard]
  -- Harris' inequality over all `n.choose 3` triples.
  have main := prod_le_binomialRandom_iInter (V := Fin n) p
    (fun s : ↥(Finset.powersetCard 3 (Finset.univ : Finset (Fin n))) =>
      {G : SimpleGraph (Fin n) | ¬ G.IsNClique 3 (s : Finset (Fin n))})
    (fun _ _ _ hGH hG hcl => hG (hcl.mono hGH)) fun s => (hkey s).1
  have hinter : (⋂ s : ↥(Finset.powersetCard 3 (Finset.univ : Finset (Fin n))),
      {G : SimpleGraph (Fin n) | ¬ G.IsNClique 3 (s : Finset (Fin n))})
      = {G : SimpleGraph (Fin n) | G.CliqueFree 3} := by
    ext G
    constructor
    · intro hG t ht
      exact Set.mem_iInter.mp hG ⟨t, Finset.mem_powersetCard_univ.mpr ht.card_eq⟩ ht
    · intro hG
      exact Set.mem_iInter.mpr fun _ => hG _
  rw [hinter] at main
  refine le_trans (le_of_eq ?_) main
  rw [Finset.prod_congr rfl fun s _ => (hkey s).2, Finset.prod_const, Finset.card_univ,
    Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
    ENNReal.ofReal_pow (by linarith), ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one,
    ENNReal.ofReal_pow hp0, hofReal]

/-! ### Harris' inequality for a random subset

`fkg` is a statement about a *finite* distributive lattice, so the counting proof of
`binomialRandom_mul_le_inter` does not transfer to `Set ι`, which is infinite as soon as `ι` is.
What replaces it is the standard approximation: condition on the coordinates in a finite
`s ⊆ ι`, apply the four functions theorem to the resulting functions of the trace — a sum over
`s.powerset`, hence a finite lattice after all — and take `s` large enough to approximate both
events by cylinders.
-/

section SetBernoulliHarris

variable {ι : Type*}

/-- The probability that a `p`-random subset of `ι` contains every element of `J` and no element
of the disjoint finite set `K`. -/
private theorem setBernoulli_cylinder (p : I) (J K : Finset ι) (hJK : Disjoint J K) :
    setBernoulli Set.univ p {R : Set ι | (∀ i ∈ J, i ∈ R) ∧ ∀ i ∈ K, i ∉ R}
      = (toNNReal p : ℝ≥0∞) ^ J.card * (toNNReal (σ p) : ℝ≥0∞) ^ K.card := by
  classical
  have hpre : (fun f : ι → Prop ↦ {i | f i}) ⁻¹'
      {R : Set ι | (∀ i ∈ J, i ∈ R) ∧ ∀ i ∈ K, i ∉ R}
      = Set.pi (↑(J ∪ K)) (fun i ↦ if i ∈ J then ({True} : Set Prop) else {False}) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_pi, Finset.coe_union, Set.mem_union,
      Finset.mem_coe]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      by_cases hiJ : i ∈ J
      · simp [hiJ, h1 i hiJ]
      · simp [hiJ, h2 i (hi.resolve_left hiJ)]
    · intro h
      refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
      · simpa [hi] using h i (Or.inl hi)
      · simpa [Finset.disjoint_right.mp hJK hi] using h i (Or.inr hi)
  rw [setBernoulli_apply', hpre,
    Measure.infinitePi_pi _ fun _ _ ↦ MeasurableSet.of_discrete, Finset.prod_union hJK]
  congr 1
  · rw [Finset.prod_congr rfl (g := fun _ ↦ (toNNReal p : ℝ≥0∞)) ?_, Finset.prod_const]
    intro i hi
    simp [hi, Measure.dirac_apply']
  · rw [Finset.prod_congr rfl (g := fun _ ↦ (toNNReal (σ p) : ℝ≥0∞)) ?_, Finset.prod_const]
    intro i hi
    simp [Finset.disjoint_right.mp hJK hi, Measure.dirac_apply']

/-- The σ-algebra on `Set ι` is generated by any family of measurable sets that contains every
coordinate event `{R | a ∈ R}`. -/
private theorem measurableSpace_set_eq_generateFrom (C : Set (Set (Set ι)))
    (h1 : ∀ E ∈ C, MeasurableSet E) (h2 : ∀ a : ι, {R : Set ι | a ∈ R} ∈ C) :
    (inferInstance : MeasurableSpace (Set ι)) = MeasurableSpace.generateFrom C := by
  refine le_antisymm (fun E hE ↦ ?_) (MeasurableSpace.generateFrom_le h1)
  have hid : @Measurable (Set ι) (Set ι) (MeasurableSpace.generateFrom C) inferInstance id := by
    refine (@measurable_set_iff ι (Set ι) (MeasurableSpace.generateFrom C) id).2 fun a ↦ ?_
    exact (@measurableSet_setOfPred (Set ι) (MeasurableSpace.generateFrom C)
      (fun R : Set ι ↦ a ∈ R)).1 (MeasurableSpace.measurableSet_generateFrom (h2 a))
  exact hid hE

/-- Containing a fixed finite set is a measurable event. -/
private theorem measurableSet_setOf_coe_subset (J : Finset ι) :
    MeasurableSet {R : Set ι | ↑J ⊆ R} := by
  have : {R : Set ι | ↑J ⊆ R} = ⋂ i ∈ J, {R : Set ι | i ∈ R} := by
    ext R; simp [Set.subset_def]
  rw [this]
  exact J.measurableSet_biInter fun i _ ↦ measurableSet_mem i

/-- A `p`-random subset contains a fixed finite set `J` with probability `p ^ #J`. -/
private theorem setBernoulli_setOf_coe_subset [Countable ι] (p : I) (J : Finset ι) :
    setBernoulli Set.univ p {R : Set ι | ↑J ⊆ R} = (toNNReal p : ℝ≥0∞) ^ J.card := by
  have h := setBernoulli_cylinder p J ∅ (by simp)
  simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, and_true,
    Finset.card_empty, pow_zero, mul_one] at h
  rw [← h]
  congr 1

/-- Splicing along `s` — take the coordinates in `s` from the first subset and the rest from the
second — is measurable. -/
private theorem measurable_splice (s : Set ι) :
    Measurable (fun q : Set ι × Set ι ↦ (q.1 ∩ s) ∪ (q.2 \ s)) := by
  refine measurable_set_iff.2 fun a ↦ ?_
  exact (((measurable_set_mem a).comp measurable_fst).and measurable_const).or
    (((measurable_set_mem a).comp measurable_snd).and measurable_const)

/-- Splicing two independent `p`-random subsets along `s` is again a `p`-random subset: this is
the independence of the coordinates in `s` from those outside it. -/
private theorem map_splice_eq_setBernoulli [Countable ι] (p : I) (s : Set ι) :
    Measure.map (fun q : Set ι × Set ι ↦ (q.1 ∩ s) ∪ (q.2 \ s))
      ((setBernoulli Set.univ p).prod (setBernoulli Set.univ p))
      = setBernoulli Set.univ p := by
  classical
  refine MeasureTheory.ext_of_generate_finite
    {E : Set (Set ι) | ∃ J : Finset ι, E = {R : Set ι | ↑J ⊆ R}}
    (measurableSpace_set_eq_generateFrom _
      (by rintro E ⟨J, rfl⟩; exact measurableSet_setOf_coe_subset J)
      fun a ↦ ⟨{a}, by ext R; simp⟩)
    ?_ ?_ (by rw [Measure.map_apply (measurable_splice s) MeasurableSet.univ]; simp)
  · rintro E ⟨J, rfl⟩ F ⟨K, rfl⟩ -
    exact ⟨J ∪ K, by ext R; simp [Finset.coe_union, Set.union_subset_iff]⟩
  · rintro E ⟨J, rfl⟩
    rw [Measure.map_apply (measurable_splice s) (measurableSet_setOf_coe_subset J)]
    have hpre : (fun q : Set ι × Set ι ↦ (q.1 ∩ s) ∪ (q.2 \ s)) ⁻¹' {R : Set ι | ↑J ⊆ R}
        = {R : Set ι | ↑(J.filter (· ∈ s)) ⊆ R} ×ˢ {T : Set ι | ↑(J.filter (· ∉ s)) ⊆ T} := by
      ext q
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.subset_def, Finset.mem_coe,
        Finset.mem_filter, Set.mem_prod, Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
      constructor
      · intro h
        exact ⟨fun i hi ↦ ((h i hi.1).resolve_right (fun hc ↦ hc.2 hi.2)).1,
          fun i hi ↦ ((h i hi.1).resolve_left (fun hc ↦ hi.2 hc.2)).1⟩
      · rintro ⟨h1, h2⟩ i hi
        by_cases his : i ∈ s
        · exact Or.inl ⟨h1 i ⟨hi, his⟩, his⟩
        · exact Or.inr ⟨h2 i ⟨hi, his⟩, his⟩
    rw [hpre, Measure.prod_prod, setBernoulli_setOf_coe_subset, setBernoulli_setOf_coe_subset,
      setBernoulli_setOf_coe_subset, ← pow_add, Finset.card_filter_add_card_filter_not]

/-- The conditional probability of `E` given the coordinates in `s` is measurable in those
coordinates. -/
private theorem measurable_setBernoulli_splice [Countable ι] (p : I) (s : Set ι)
    {E : Set (Set ι)} (hE : MeasurableSet E) :
    Measurable fun R : Set ι ↦ setBernoulli Set.univ p {T : Set ι | (R ∩ s) ∪ (T \ s) ∈ E} :=
  measurable_measure_prodMk_left (measurable_splice s hE)

/-- Averaging the conditional probability of `E` given the coordinates in `s` recovers `ℙ E`. -/
private theorem setBernoulli_eq_lintegral_splice [Countable ι] (p : I) (s : Set ι)
    {E : Set (Set ι)} (hE : MeasurableSet E) :
    setBernoulli Set.univ p E
      = ∫⁻ R, setBernoulli Set.univ p {T : Set ι | (R ∩ s) ∪ (T \ s) ∈ E}
          ∂setBernoulli Set.univ p := by
  conv_lhs => rw [← map_splice_eq_setBernoulli p s]
  rw [Measure.map_apply (measurable_splice s) hE, Measure.prod_apply (measurable_splice s hE)]
  rfl

/-- Intersecting with a fixed set is measurable. -/
private theorem measurable_inter_const (s : Set ι) : Measurable fun R : Set ι ↦ R ∩ s :=
  measurable_set_iff.2 fun a ↦ (measurable_set_mem a).and measurable_const

/-- Prescribing the trace of a random subset on a finite set is a measurable event. -/
private theorem measurableSet_setOf_inter_eq [Countable ι] (s t : Finset ι) :
    MeasurableSet {R : Set ι | R ∩ ↑s = ↑t} := by
  have h := measurable_inter_const (↑s : Set ι) (measurableSet_singleton (↑t : Set ι))
  convert h using 1
  ext R
  simp

/-- A function of the trace on a finite set `s` integrates to a finite sum over `s.powerset`. -/
private theorem lintegral_eq_sum_powerset [Countable ι] (p : I) (s : Finset ι) (h : Set ι → ℝ≥0∞)
    (hhc : ∀ R : Set ι, h R = h (R ∩ ↑s)) :
    ∫⁻ R, h R ∂setBernoulli Set.univ p
      = ∑ t ∈ s.powerset, setBernoulli Set.univ p {R : Set ι | R ∩ ↑s = ↑t} * h ↑t := by
  classical
  have key : ∀ R : Set ι, h R
      = ∑ t ∈ s.powerset, Set.indicator {R : Set ι | R ∩ ↑s = ↑t} (fun _ ↦ h ↑t) R := by
    intro R
    have ht0 : R ∩ ↑s = ↑(s.filter (· ∈ R)) := by
      ext i
      simp [and_comm]
    rw [Finset.sum_eq_single (s.filter (· ∈ R))]
    · have hmem : R ∈ {R' : Set ι | R' ∩ ↑s = ↑(s.filter (· ∈ R))} := ht0
      rw [Set.indicator_of_mem hmem, hhc R, ht0]
    · intro t _ hne
      refine Set.indicator_of_notMem ?_ _
      intro hR
      exact hne (Finset.coe_injective (by rw [← hR, ht0]))
    · intro hc
      exact absurd (Finset.mem_powerset.2 (Finset.filter_subset _ _)) hc
  calc ∫⁻ R, h R ∂setBernoulli Set.univ p
      = ∫⁻ R, ∑ t ∈ s.powerset, Set.indicator {R : Set ι | R ∩ ↑s = ↑t} (fun _ ↦ h ↑t) R
          ∂setBernoulli Set.univ p := by
        exact lintegral_congr fun R ↦ key R
    _ = ∑ t ∈ s.powerset, ∫⁻ R, Set.indicator {R : Set ι | R ∩ ↑s = ↑t} (fun _ ↦ h ↑t) R
          ∂setBernoulli Set.univ p :=
        lintegral_finsetSum _ fun t _ ↦
          measurable_const.indicator (measurableSet_setOf_inter_eq s t)
    _ = ∑ t ∈ s.powerset, setBernoulli Set.univ p {R : Set ι | R ∩ ↑s = ↑t} * h ↑t := by
        refine Finset.sum_congr rfl fun t _ ↦ ?_
        rw [lintegral_indicator_const (measurableSet_setOf_inter_eq s t), mul_comm]

/-- The probability that a `p`-random subset has prescribed trace `t` on a finite set `s`. -/
private theorem setBernoulli_setOf_inter_eq [Countable ι] [DecidableEq ι] (p : I) (s t : Finset ι)
    (hts : t ⊆ s) :
    setBernoulli Set.univ p {R : Set ι | R ∩ ↑s = ↑t}
      = (toNNReal p : ℝ≥0∞) ^ t.card * (toNNReal (σ p) : ℝ≥0∞) ^ (s \ t).card := by
  classical
  rw [← setBernoulli_cylinder p t (s \ t) (Finset.disjoint_sdiff)]
  congr 1
  ext R
  simp only [Set.mem_ofPred_eq, Finset.mem_sdiff]
  constructor
  · intro hR
    refine ⟨fun i hi ↦ ?_, fun i hi hiR ↦ ?_⟩
    · have h1 : i ∈ (↑t : Set ι) := Finset.mem_coe.2 hi
      rw [← hR] at h1
      exact h1.1
    · have h1 : i ∈ R ∩ (↑s : Set ι) := ⟨hiR, Finset.mem_coe.2 hi.1⟩
      rw [hR] at h1
      exact hi.2 (Finset.mem_coe.1 h1)
  · rintro ⟨h1, h2⟩
    ext i
    simp only [Set.mem_inter_iff, Finset.mem_coe]
    constructor
    · rintro ⟨hiR, his⟩
      by_contra hit
      exact h2 i ⟨his, hit⟩ hiR
    · intro hit
      exact ⟨h1 i hit, hts hit⟩

/-- A trace that is not contained in `s` is impossible. -/
private theorem setBernoulli_setOf_inter_eq_of_not_subset (p : I) (s t : Finset ι) (hts : ¬ t ⊆ s) :
    setBernoulli Set.univ p {R : Set ι | R ∩ ↑s = ↑t} = 0 := by
  have : {R : Set ι | R ∩ ↑s = ↑t} = ∅ := by
    ext R
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hR
    refine hts fun i hi ↦ ?_
    have h1 : i ∈ (↑t : Set ι) := Finset.mem_coe.2 hi
    rw [← hR] at h1
    exact Finset.mem_coe.1 h1.2
  rw [this, measure_empty]

/-- The trace weights are log-supermodular — log-modular, in fact — which is the hypothesis the
four functions theorem needs. -/
private theorem setBernoulli_trace_mul_le [Countable ι] [DecidableEq ι] (p : I) (s a b : Finset ι) :
    setBernoulli Set.univ p {R : Set ι | R ∩ ↑s = ↑a}
        * setBernoulli Set.univ p {R : Set ι | R ∩ ↑s = ↑b}
      ≤ setBernoulli Set.univ p {R : Set ι | R ∩ ↑s = ↑(a ⊓ b)}
        * setBernoulli Set.univ p {R : Set ι | R ∩ ↑s = ↑(a ⊔ b)} := by
  classical
  rw [Finset.inf_eq_inter, Finset.sup_eq_union]
  by_cases ha : a ⊆ s
  · by_cases hb : b ⊆ s
    · rw [setBernoulli_setOf_inter_eq p s a ha, setBernoulli_setOf_inter_eq p s b hb,
        setBernoulli_setOf_inter_eq p s (a ∩ b) (Finset.inter_subset_left.trans ha),
        setBernoulli_setOf_inter_eq p s (a ∪ b) (Finset.union_subset ha hb),
        mul_mul_mul_comm, mul_mul_mul_comm ((toNNReal p : ℝ≥0∞) ^ (a ∩ b).card),
        ← pow_add, ← pow_add, ← pow_add, ← pow_add]
      have e1 : (a ∩ b).card + (a ∪ b).card = a.card + b.card :=
        Finset.card_inter_add_card_union a b
      have h1 : s \ (a ∩ b) = (s \ a) ∪ (s \ b) := by ext i; simp; tauto
      have h2 : s \ (a ∪ b) = (s \ a) ∩ (s \ b) := by ext i; simp; tauto
      have e2 : (s \ (a ∩ b)).card + (s \ (a ∪ b)).card = (s \ a).card + (s \ b).card := by
        rw [h1, h2, Finset.card_union_add_card_inter]
      rw [e1, e2]
    · rw [setBernoulli_setOf_inter_eq_of_not_subset p s b hb, mul_zero]
      exact zero_le
  · rw [setBernoulli_setOf_inter_eq_of_not_subset p s a ha, zero_mul]
    exact zero_le

/-- **Harris' inequality in finitely many coordinates**: two bounded increasing functions of the
trace on a finite set `s` are positively correlated.

The lattice the four functions theorem is applied to is `Finset ι` cut down to `s.powerset`, not
`Set ι`: `fkg` itself wants a `Fintype`, and `Set ι` is not finite here. -/
private theorem lintegral_mul_lintegral_le_lintegral_mul [Countable ι] [DecidableEq ι] (p : I)
    (s : Finset ι) (f g : Set ι → ℝ≥0∞)
    (hf : Monotone f) (hg : Monotone g) (hf1 : ∀ R, f R ≤ 1) (hg1 : ∀ R, g R ≤ 1)
    (hfc : ∀ R : Set ι, f R = f (R ∩ ↑s)) (hgc : ∀ R : Set ι, g R = g (R ∩ ↑s)) :
    (∫⁻ R, f R ∂setBernoulli Set.univ p) * ∫⁻ R, g R ∂setBernoulli Set.univ p
      ≤ ∫⁻ R, f R * g R ∂setBernoulli Set.univ p := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : Finset ι → NNReal, ∀ t : Finset ι,
      (w t : ℝ≥0∞) = setBernoulli Set.univ p {R : Set ι | R ∩ ↑s = ↑t} :=
    ⟨fun t ↦ (setBernoulli Set.univ p {R : Set ι | R ∩ ↑s = ↑t}).toNNReal,
      fun t ↦ ENNReal.coe_toNNReal (measure_ne_top _ _)⟩
  obtain ⟨F, hF⟩ : ∃ F : Finset ι → NNReal, ∀ t : Finset ι, (F t : ℝ≥0∞) = f ↑t :=
    ⟨fun t ↦ (f ↑t).toNNReal,
      fun t ↦ ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hf1 _))⟩
  obtain ⟨G, hG⟩ : ∃ G : Finset ι → NNReal, ∀ t : Finset ι, (G t : ℝ≥0∞) = g ↑t :=
    ⟨fun t ↦ (g ↑t).toNNReal,
      fun t ↦ ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hg1 _))⟩
  have hFmono : Monotone F := fun a b hab ↦ by
    rw [← ENNReal.coe_le_coe, hF, hF]; exact hf (Finset.coe_subset.2 hab)
  have hGmono : Monotone G := fun a b hab ↦ by
    rw [← ENNReal.coe_le_coe, hG, hG]; exact hg (Finset.coe_subset.2 hab)
  have hwsuper : ∀ a b : Finset ι, w a * w b ≤ w (a ⊓ b) * w (a ⊔ b) := fun a b ↦ by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, ENNReal.coe_mul, hw, hw, hw, hw]
    exact setBernoulli_trace_mul_le p s a b
  have key := four_functions_theorem (fun t : Finset ι ↦ w t * F t) (fun t ↦ w t * G t) w
    (fun t ↦ w t * (F t * G t)) (fun _ ↦ zero_le) (fun _ ↦ zero_le) (fun _ ↦ zero_le)
    (fun _ ↦ zero_le) ?_ s.powerset s.powerset
  · rw [Finset.powerset_infs_powerset_self, Finset.powerset_sups_powerset_self] at key
    have hsumw : (∑ t ∈ s.powerset, w t) = 1 := by
      rw [← ENNReal.coe_inj, ENNReal.ofNNReal_finsetSum, ENNReal.coe_one]
      have h1 := lintegral_eq_sum_powerset p s (fun _ ↦ 1) (fun _ ↦ rfl)
      simp only [mul_one, lintegral_const, measure_univ] at h1
      rw [h1]
      exact Finset.sum_congr rfl fun t _ ↦ hw t
    rw [hsumw, one_mul] at key
    have hsf : ((∑ t ∈ s.powerset, w t * F t : NNReal) : ℝ≥0∞)
        = ∫⁻ R, f R ∂setBernoulli Set.univ p := by
      rw [ENNReal.ofNNReal_finsetSum, lintegral_eq_sum_powerset p s f hfc]
      exact Finset.sum_congr rfl fun t _ ↦ by rw [ENNReal.coe_mul, hw, hF]
    have hsg : ((∑ t ∈ s.powerset, w t * G t : NNReal) : ℝ≥0∞)
        = ∫⁻ R, g R ∂setBernoulli Set.univ p := by
      rw [ENNReal.ofNNReal_finsetSum, lintegral_eq_sum_powerset p s g hgc]
      exact Finset.sum_congr rfl fun t _ ↦ by rw [ENNReal.coe_mul, hw, hG]
    have hsfg : ((∑ t ∈ s.powerset, w t * (F t * G t) : NNReal) : ℝ≥0∞)
        = ∫⁻ R, f R * g R ∂setBernoulli Set.univ p := by
      rw [ENNReal.ofNNReal_finsetSum,
        lintegral_eq_sum_powerset p s (fun R ↦ f R * g R) (fun R ↦ by rw [← hfc, ← hgc])]
      exact Finset.sum_congr rfl fun t _ ↦ by
        rw [ENNReal.coe_mul, ENNReal.coe_mul, hw, hF, hG]
    rw [← hsf, ← hsg, ← hsfg, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    exact key
  · intro a b
    calc w a * F a * (w b * G b) = w a * w b * (F a * G b) := by ring
      _ ≤ w (a ⊓ b) * w (a ⊔ b) * (F (a ⊔ b) * G (a ⊔ b)) :=
          mul_le_mul' (hwsuper a b) (mul_le_mul' (hFmono le_sup_left) (hGmono le_sup_right))
      _ = w (a ⊓ b) * (w (a ⊔ b) * (F (a ⊔ b) * G (a ⊔ b))) := by ring

/-- An event determined by the coordinates in `s₁` is determined by those in any larger `s`. -/
private theorem cylinderOn_of_subset (E : Set (Set ι)) (s₁ s : Finset ι) (hsub : s₁ ⊆ s)
    (hE : ∀ R T : Set ι, R ∩ ↑s₁ = T ∩ ↑s₁ → (R ∈ E ↔ T ∈ E)) :
    ∀ R T : Set ι, R ∩ ↑s = T ∩ ↑s → (R ∈ E ↔ T ∈ E) := by
  intro R T h
  refine hE R T ?_
  have hss : (↑s : Set ι) ∩ ↑s₁ = ↑s₁ := Set.inter_eq_right.2 (Finset.coe_subset.2 hsub)
  calc R ∩ (↑s₁ : Set ι) = R ∩ ((↑s : Set ι) ∩ ↑s₁) := by rw [hss]
    _ = (R ∩ ↑s) ∩ ↑s₁ := by rw [Set.inter_assoc]
    _ = (T ∩ ↑s) ∩ ↑s₁ := by rw [h]
    _ = T ∩ ((↑s : Set ι) ∩ ↑s₁) := by rw [Set.inter_assoc]
    _ = T ∩ ↑s₁ := by rw [hss]

/-- An event determined by finitely many coordinates is measurable: it is a finite union of
traces. -/
private theorem measurableSet_of_cylinderOn [Countable ι] (E : Set (Set ι)) (s : Finset ι)
    (hE : ∀ R T : Set ι, R ∩ ↑s = T ∩ ↑s → (R ∈ E ↔ T ∈ E)) : MeasurableSet E := by
  classical
  have hEeq : E = ⋃ t ∈ s.powerset.filter (fun t : Finset ι ↦ (↑t : Set ι) ∈ E),
      {R : Set ι | R ∩ ↑s = (↑t : Set ι)} := by
    ext R
    simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_powerset, Set.mem_ofPred_eq,
      exists_prop]
    have ht0 : R ∩ (↑s : Set ι) = ↑(s.filter (· ∈ R)) := by ext i; simp [and_comm]
    constructor
    · intro hR
      refine ⟨s.filter (· ∈ R), ⟨Finset.filter_subset _ _, ?_⟩, ht0⟩
      refine (hE R _ ?_).1 hR
      rw [ht0, Set.inter_eq_left.2 (Finset.coe_subset.2 (Finset.filter_subset _ _))]
    · rintro ⟨t, ⟨hts, htE⟩, hRt⟩
      refine (hE R _ ?_).2 htE
      rw [hRt, Set.inter_eq_left.2 (Finset.coe_subset.2 hts)]
  rw [hEeq]
  exact Finset.measurableSet_biUnion _ fun t _ ↦ measurableSet_setOf_inter_eq s t

/-- The events determined by finitely many coordinates form a ring of sets. -/
private theorem isSetRing_cylinderOn [Countable ι] [DecidableEq ι] :
    IsSetRing {E : Set (Set ι) | ∃ s : Finset ι,
      ∀ R T : Set ι, R ∩ ↑s = T ∩ ↑s → (R ∈ E ↔ T ∈ E)} where
  empty_mem := ⟨∅, fun _ _ _ ↦ Iff.rfl⟩
  union_mem := by
    rintro E F ⟨s₁, hE⟩ ⟨s₂, hF⟩
    refine ⟨s₁ ∪ s₂, fun R T h ↦ ?_⟩
    rw [Set.mem_union, Set.mem_union,
      cylinderOn_of_subset E s₁ _ Finset.subset_union_left hE R T h,
      cylinderOn_of_subset F s₂ _ Finset.subset_union_right hF R T h]
  sdiff_mem := by
    rintro E F ⟨s₁, hE⟩ ⟨s₂, hF⟩
    refine ⟨s₁ ∪ s₂, fun R T h ↦ ?_⟩
    rw [Set.mem_sdiff, Set.mem_sdiff,
      cylinderOn_of_subset E s₁ _ Finset.subset_union_left hE R T h,
      cylinderOn_of_subset F s₂ _ Finset.subset_union_right hF R T h]

/-- Every measurable event is approximated in measure by one determined by finitely many
coordinates. -/
private theorem exists_cylinderOn_symmDiff_lt [Countable ι] [DecidableEq ι] (p : I)
    {A : Set (Set ι)} (hA : MeasurableSet A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (s : Finset ι) (E : Set (Set ι)),
      (∀ R T : Set ι, R ∩ ↑s = T ∩ ↑s → (R ∈ E ↔ T ∈ E)) ∧
        setBernoulli Set.univ p (symmDiff E A) < ε := by
  obtain ⟨E, ⟨s, hEs⟩, hE⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (μ := setBernoulli Set.univ p) isSetRing_cylinderOn
    ⟨{Set.univ}, Set.countable_singleton _, by
      rintro F hF
      rw [Set.mem_singleton_iff] at hF
      exact ⟨∅, fun R T _ ↦ by rw [hF]; simp⟩, by simp⟩
    (measurableSpace_set_eq_generateFrom _
      (by rintro F ⟨s, hs⟩; exact measurableSet_of_cylinderOn F s hs)
      fun a ↦ ⟨{a}, fun R T h ↦ by
        simp only [Set.mem_ofPred_eq]
        constructor
        · intro hR
          have : a ∈ R ∩ (↑({a} : Finset ι) : Set ι) := ⟨hR, by simp⟩
          rw [h] at this
          exact this.1
        · intro hT
          have : a ∈ T ∩ (↑({a} : Finset ι) : Set ι) := ⟨hT, by simp⟩
          rw [← h] at this
          exact this.1⟩)
    hA hε
  exact ⟨s, E, hEs, hE⟩

/-- Perturbing the factors of a product of elements of `[0, 1]` perturbs the product by at most
the sum of the perturbations. -/
private theorem mul_le_mul_add_tsub_add_tsub (a b c d : ℝ≥0∞) (hb : b ≤ 1) (hc : c ≤ 1) :
    a * c ≤ b * d + (a - b) + (c - d) := by
  have h1 : a ≤ b + (a - b) := by rw [add_comm]; exact le_tsub_add
  have h2 : c ≤ d + (c - d) := by rw [add_comm]; exact le_tsub_add
  calc a * c ≤ (b + (a - b)) * c := by gcongr
    _ = b * c + (a - b) * c := by ring
    _ ≤ b * (d + (c - d)) + (a - b) * 1 := by gcongr
    _ = b * d + b * (c - d) + (a - b) := by ring
    _ ≤ b * d + 1 * (c - d) + (a - b) := by gcongr
    _ = b * d + (a - b) + (c - d) := by ring

/-- Splicing along `s` does not move an event determined by the coordinates in `s`, so its
conditional probability is its indicator. -/
private theorem setBernoulli_splice_cylinderOn (p : I) (s : Finset ι) (E : Set (Set ι))
    (hE : ∀ R T : Set ι, R ∩ ↑s = T ∩ ↑s → (R ∈ E ↔ T ∈ E)) (R : Set ι) :
    setBernoulli Set.univ p {T : Set ι | (R ∩ ↑s) ∪ (T \ ↑s) ∈ E}
      = Set.indicator E (fun _ ↦ (1 : ℝ≥0∞)) R := by
  have hkey : ∀ T : Set ι, ((R ∩ ↑s) ∪ (T \ ↑s)) ∈ E ↔ R ∈ E := by
    intro T
    refine hE _ R ?_
    rw [Set.union_inter_distrib_right, Set.inter_assoc, Set.inter_self,
      Set.sdiff_inter_self, Set.union_empty]
  by_cases hR : R ∈ E
  · have hu : {T : Set ι | (R ∩ ↑s) ∪ (T \ ↑s) ∈ E} = Set.univ := by
      ext T; simp [hkey T, hR]
    rw [hu, measure_univ, Set.indicator_of_mem hR]
  · have hu : {T : Set ι | (R ∩ ↑s) ∪ (T \ ↑s) ∈ E} = ∅ := by
      ext T; simp [hkey T, hR]
    rw [hu, measure_empty, Set.indicator_of_notMem hR]

/-- The conditional probability of `A` given the coordinates in `s` exceeds the indicator of `A`
by at most the error of a cylinder approximation `E` of `A`. -/
private theorem setBernoulli_splice_tsub_indicator_le [Countable ι] (p : I) (s : Finset ι)
    (A E : Set (Set ι))
    (hE : ∀ R T : Set ι, R ∩ ↑s = T ∩ ↑s → (R ∈ E ↔ T ∈ E)) (R : Set ι) :
    setBernoulli Set.univ p {T : Set ι | (R ∩ ↑s) ∪ (T \ ↑s) ∈ A}
        - Set.indicator A (fun _ ↦ (1 : ℝ≥0∞)) R
      ≤ Set.indicator (E \ A) (fun _ ↦ (1 : ℝ≥0∞)) R
        + setBernoulli Set.univ p {T : Set ι | (R ∩ ↑s) ∪ (T \ ↑s) ∈ A \ E} := by
  set u := Set.indicator E (fun _ ↦ (1 : ℝ≥0∞)) R with hu
  set z := Set.indicator A (fun _ ↦ (1 : ℝ≥0∞)) R with hz
  set v := setBernoulli Set.univ p {T : Set ι | (R ∩ ↑s) ∪ (T \ ↑s) ∈ A \ E} with hv
  have hx : setBernoulli Set.univ p {T : Set ι | (R ∩ ↑s) ∪ (T \ ↑s) ∈ A} ≤ u + v := by
    rw [hu, ← setBernoulli_splice_cylinderOn p s E hE R, hv]
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro T hT
    by_cases h : (R ∩ ↑s) ∪ (T \ ↑s) ∈ E
    · exact Or.inl h
    · exact Or.inr ⟨hT, h⟩
  have hstep : (u + v) - z ≤ (u - z) + v := by
    refine tsub_le_iff_right.2 ?_
    calc u + v ≤ ((u - z) + z) + v := by gcongr; exact le_tsub_add
      _ = (u - z) + v + z := by ring
  have hind : u - z ≤ Set.indicator (E \ A) (fun _ ↦ (1 : ℝ≥0∞)) R := by
    rw [hu, hz]
    by_cases hRE : R ∈ E <;> by_cases hRA : R ∈ A <;> simp [hRE, hRA]
  calc setBernoulli Set.univ p {T : Set ι | (R ∩ ↑s) ∪ (T \ ↑s) ∈ A} - z
      ≤ (u + v) - z := by gcongr
    _ ≤ (u - z) + v := hstep
    _ ≤ Set.indicator (E \ A) (fun _ ↦ (1 : ℝ≥0∞)) R + v := by gcongr

/-- The indicator of an intersection is the product of the indicators. -/
private theorem indicator_one_mul_indicator_one (A B : Set (Set ι)) (R : Set ι) :
    Set.indicator A (fun _ ↦ (1 : ℝ≥0∞)) R * Set.indicator B (fun _ ↦ (1 : ℝ≥0∞)) R
      = Set.indicator (A ∩ B) (fun _ ↦ (1 : ℝ≥0∞)) R := by
  by_cases hRA : R ∈ A <;> by_cases hRB : R ∈ B <;> simp [hRA, hRB]

/-- An indicator is at most `1`. -/
private theorem indicator_one_le_one (A : Set (Set ι)) (R : Set ι) :
    Set.indicator A (fun _ ↦ (1 : ℝ≥0∞)) R ≤ 1 := by
  by_cases hRA : R ∈ A <;> simp [hRA]

/-- Harris' inequality for two increasing events, up to the error of cylinder approximations
`EA` and `EB` of them over a common finite set of coordinates. -/
private theorem setBernoulli_mul_le_inter_add_error [Countable ι] (p : I) (s : Finset ι)
    (A B EA EB : Set (Set ι)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hEA : ∀ R T : Set ι, R ∩ ↑s = T ∩ ↑s → (R ∈ EA ↔ T ∈ EA))
    (hEB : ∀ R T : Set ι, R ∩ ↑s = T ∩ ↑s → (R ∈ EB ↔ T ∈ EB)) :
    setBernoulli Set.univ p A * setBernoulli Set.univ p B
      ≤ setBernoulli Set.univ p (A ∩ B)
        + (setBernoulli Set.univ p (EA \ A) + setBernoulli Set.univ p (A \ EA))
        + (setBernoulli Set.univ p (EB \ B) + setBernoulli Set.univ p (B \ EB)) := by
  classical
  have hEAm : MeasurableSet EA := measurableSet_of_cylinderOn EA s hEA
  have hEBm : MeasurableSet EB := measurableSet_of_cylinderOn EB s hEB
  have hmono : ∀ (C : Set (Set ι)), IsUpperSet C →
      Monotone fun R : Set ι ↦
        setBernoulli Set.univ p {T : Set ι | (R ∩ ↑s) ∪ (T \ ↑s) ∈ C} := by
    intro C hC R R' hRR'
    exact measure_mono fun T hT ↦
      hC (Set.union_subset_union (Set.inter_subset_inter_left _ hRR') (subset_refl _)) hT
  have hcyl : ∀ (C : Set (Set ι)) (R : Set ι),
      setBernoulli Set.univ p {T : Set ι | (R ∩ ↑s) ∪ (T \ ↑s) ∈ C}
        = setBernoulli Set.univ p
            {T : Set ι | ((R ∩ ↑s) ∩ ↑s) ∪ (T \ ↑s) ∈ C} := by
    intro C R
    rw [Set.inter_assoc, Set.inter_self]
  have hpt : ∀ R : Set ι,
      setBernoulli Set.univ p {T : Set ι | (R ∩ ↑s) ∪ (T \ ↑s) ∈ A}
          * setBernoulli Set.univ p {T : Set ι | (R ∩ ↑s) ∪ (T \ ↑s) ∈ B}
        ≤ Set.indicator (A ∩ B) (fun _ ↦ (1 : ℝ≥0∞)) R
          + Set.indicator (EA \ A) (fun _ ↦ (1 : ℝ≥0∞)) R
          + setBernoulli Set.univ p {T : Set ι | (R ∩ ↑s) ∪ (T \ ↑s) ∈ A \ EA}
          + Set.indicator (EB \ B) (fun _ ↦ (1 : ℝ≥0∞)) R
          + setBernoulli Set.univ p {T : Set ι | (R ∩ ↑s) ∪ (T \ ↑s) ∈ B \ EB} := by
    intro R
    calc setBernoulli Set.univ p {T : Set ι | (R ∩ ↑s) ∪ (T \ ↑s) ∈ A}
          * setBernoulli Set.univ p {T : Set ι | (R ∩ ↑s) ∪ (T \ ↑s) ∈ B}
        ≤ Set.indicator A (fun _ ↦ (1 : ℝ≥0∞)) R * Set.indicator B (fun _ ↦ (1 : ℝ≥0∞)) R
            + (setBernoulli Set.univ p {T : Set ι | (R ∩ ↑s) ∪ (T \ ↑s) ∈ A}
              - Set.indicator A (fun _ ↦ (1 : ℝ≥0∞)) R)
            + (setBernoulli Set.univ p {T : Set ι | (R ∩ ↑s) ∪ (T \ ↑s) ∈ B}
              - Set.indicator B (fun _ ↦ (1 : ℝ≥0∞)) R) :=
          mul_le_mul_add_tsub_add_tsub _ _ _ _ (indicator_one_le_one A R) prob_le_one
      _ ≤ Set.indicator (A ∩ B) (fun _ ↦ (1 : ℝ≥0∞)) R
            + (Set.indicator (EA \ A) (fun _ ↦ (1 : ℝ≥0∞)) R
              + setBernoulli Set.univ p {T : Set ι | (R ∩ ↑s) ∪ (T \ ↑s) ∈ A \ EA})
            + (Set.indicator (EB \ B) (fun _ ↦ (1 : ℝ≥0∞)) R
              + setBernoulli Set.univ p {T : Set ι | (R ∩ ↑s) ∪ (T \ ↑s) ∈ B \ EB}) := by
          gcongr
          · exact le_of_eq (indicator_one_mul_indicator_one A B R)
          · exact setBernoulli_splice_tsub_indicator_le p s A EA hEA R
          · exact setBernoulli_splice_tsub_indicator_le p s B EB hEB R
      _ = _ := by ring
  have m1 : Measurable fun R : Set ι ↦ Set.indicator (A ∩ B) (fun _ ↦ (1 : ℝ≥0∞)) R :=
    measurable_const.indicator (hAm.inter hBm)
  have m2 : Measurable fun R : Set ι ↦ Set.indicator (EA \ A) (fun _ ↦ (1 : ℝ≥0∞)) R :=
    measurable_const.indicator (hEAm.diff hAm)
  have m3 : Measurable fun R : Set ι ↦
      setBernoulli Set.univ p {T : Set ι | (R ∩ ↑s) ∪ (T \ ↑s) ∈ A \ EA} :=
    measurable_setBernoulli_splice p (↑s) (hAm.diff hEAm)
  have m4 : Measurable fun R : Set ι ↦ Set.indicator (EB \ B) (fun _ ↦ (1 : ℝ≥0∞)) R :=
    measurable_const.indicator (hEBm.diff hBm)
  have m12 : Measurable fun R : Set ι ↦
      Set.indicator (A ∩ B) (fun _ ↦ (1 : ℝ≥0∞)) R
        + Set.indicator (EA \ A) (fun _ ↦ (1 : ℝ≥0∞)) R := m1.add m2
  have m123 : Measurable fun R : Set ι ↦
      Set.indicator (A ∩ B) (fun _ ↦ (1 : ℝ≥0∞)) R
        + Set.indicator (EA \ A) (fun _ ↦ (1 : ℝ≥0∞)) R
        + setBernoulli Set.univ p {T : Set ι | (R ∩ ↑s) ∪ (T \ ↑s) ∈ A \ EA} := m12.add m3
  have m1234 : Measurable fun R : Set ι ↦
      Set.indicator (A ∩ B) (fun _ ↦ (1 : ℝ≥0∞)) R
        + Set.indicator (EA \ A) (fun _ ↦ (1 : ℝ≥0∞)) R
        + setBernoulli Set.univ p {T : Set ι | (R ∩ ↑s) ∪ (T \ ↑s) ∈ A \ EA}
        + Set.indicator (EB \ B) (fun _ ↦ (1 : ℝ≥0∞)) R := m123.add m4
  rw [setBernoulli_eq_lintegral_splice p (↑s) hAm, setBernoulli_eq_lintegral_splice p (↑s) hBm]
  refine le_trans (lintegral_mul_lintegral_le_lintegral_mul p s _ _ (hmono A hA) (hmono B hB)
    (fun _ ↦ prob_le_one) (fun _ ↦ prob_le_one) (hcyl A) (hcyl B)) ?_
  refine le_trans (lintegral_mono hpt) ?_
  rw [lintegral_add_left m1234, lintegral_add_left m123,
    lintegral_add_left m12, lintegral_add_left m1,
    lintegral_indicator_const (hAm.inter hBm), lintegral_indicator_const (hEAm.diff hAm),
    lintegral_indicator_const (hEBm.diff hBm),
    ← setBernoulli_eq_lintegral_splice p (↑s) (hAm.diff hEAm),
    ← setBernoulli_eq_lintegral_splice p (↑s) (hBm.diff hEBm)]
  simp only [one_mul]
  exact le_of_eq (by ring)

/-- **Harris' inequality for a random subset** (Zhao, Theorem 7.1.1 over an index type): two
increasing events of a random subset are positively correlated.

This is the `setBernoulli` analogue of `binomialRandom_mul_le_inter`.  The index type here is
only countable, so `Set ι` is not a finite lattice and `fkg` does not apply to it directly. -/
theorem setBernoulli_mul_le_inter [Countable ι] (p : I) (A B : Set (Set ι))
    (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    setBernoulli Set.univ p A * setBernoulli Set.univ p B
      ≤ setBernoulli Set.univ p (A ∩ B) := by
  classical
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  have hε0 : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) := by exact_mod_cast hε
  have hδ : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) / 2 / 2 :=
    ENNReal.div_pos (ENNReal.div_pos hε0.ne' (by simp)).ne' (by simp)
  obtain ⟨sA, EA, hEA, hEAlt⟩ := exists_cylinderOn_symmDiff_lt p hAm hδ
  obtain ⟨sB, EB, hEB, hEBlt⟩ := exists_cylinderOn_symmDiff_lt p hBm hδ
  refine le_trans (setBernoulli_mul_le_inter_add_error p (sA ∪ sB) A B EA EB hA hB hAm hBm
    (cylinderOn_of_subset EA sA _ Finset.subset_union_left hEA)
    (cylinderOn_of_subset EB sB _ Finset.subset_union_right hEB)) ?_
  have hA1 : setBernoulli Set.univ p (EA \ A) ≤ (ε : ℝ≥0∞) / 2 / 2 :=
    le_trans (measure_mono le_sup_left) hEAlt.le
  have hA2 : setBernoulli Set.univ p (A \ EA) ≤ (ε : ℝ≥0∞) / 2 / 2 :=
    le_trans (measure_mono le_sup_right) hEAlt.le
  have hB1 : setBernoulli Set.univ p (EB \ B) ≤ (ε : ℝ≥0∞) / 2 / 2 :=
    le_trans (measure_mono le_sup_left) hEBlt.le
  have hB2 : setBernoulli Set.univ p (B \ EB) ≤ (ε : ℝ≥0∞) / 2 / 2 :=
    le_trans (measure_mono le_sup_right) hEBlt.le
  calc setBernoulli Set.univ p (A ∩ B)
        + (setBernoulli Set.univ p (EA \ A) + setBernoulli Set.univ p (A \ EA))
        + (setBernoulli Set.univ p (EB \ B) + setBernoulli Set.univ p (B \ EB))
      ≤ setBernoulli Set.univ p (A ∩ B) + ((ε : ℝ≥0∞) / 2 / 2 + (ε : ℝ≥0∞) / 2 / 2)
          + ((ε : ℝ≥0∞) / 2 / 2 + (ε : ℝ≥0∞) / 2 / 2) := by gcongr
    _ = setBernoulli Set.univ p (A ∩ B) + (ε : ℝ≥0∞) := by
        rw [ENNReal.add_halves ((ε : ℝ≥0∞) / 2), add_assoc, ENNReal.add_halves]

end SetBernoulliHarris

/-! ### The `setBernoulli` forms, for Chapter 8

Janson's inequality lives on `setBernoulli` — a random *subset* of an index type — rather than on
`binomialRandom`.  The two facts below are the shared interface `janson_prob_none_step_le`
consumes, and they are stated here, next to the graph forms, rather than left for a task to
invent.  `[Countable ι]` for the same reason as in `Janson.lean`: off it, the events in question
are not measurable and `setBernoulli` quietly returns an outer measure. -/

section SetBernoulli

variable {ι : Type*} [Countable ι]

/-- **Harris' inequality for a random subset, in the mixed form.**  An increasing event and a
decreasing event are *negatively* correlated.  This is the shape Janson's inequality needs — the
Boppana–Spencer conditioning step pairs "`R` contains `S i`" against "`R` contains none of the
`S j` for `j` in a block" — and it is the `setBernoulli` analogue of
`binomialRandom_mul_le_inter`, which is the same statement for `G(V, p)` with both events
increasing. -/
theorem setBernoulli_inter_le_mul (p : I) (A B : Set (Set ι))
    (hA : IsUpperSet A) (hB : IsLowerSet B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    setBernoulli Set.univ p (A ∩ B) ≤ setBernoulli Set.univ p A * setBernoulli Set.univ p B := by
  -- `a` is the probability of `A`, `b` and `b'` those of `B` and its complement, `c` and `c'`
  -- those of `A ∩ B` and `A \ B`.  The rearrangement is additive: `ℝ≥0∞` subtraction is truncated.
  have arith : ∀ a b b' c c' : ℝ≥0∞, a ≤ 1 → b + b' = 1 → c + c' = a → a * b' ≤ c' →
      c ≤ a * b := by
    intro a b b' c c' ha hb hc h
    have hb' : b' ≤ 1 := by rw [← hb]; exact le_add_self
    have hab' : a * b' ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (by simpa using mul_le_mul' ha hb')
    refine (ENNReal.add_le_add_iff_right hab').mp ?_
    calc c + a * b' ≤ c + c' := by gcongr
      _ = a := hc
      _ = a * (b + b') := by rw [hb, mul_one]
      _ = a * b + a * b' := by ring
  refine arith _ _ (setBernoulli Set.univ p Bᶜ) _ (setBernoulli Set.univ p (A \ B))
    prob_le_one ?_ (measure_inter_add_sdiff A hBm) ?_
  · simpa using measure_add_measure_compl (μ := setBernoulli Set.univ p) hBm
  · rw [Set.sdiff_eq]
    exact setBernoulli_mul_le_inter p A Bᶜ hA hB.compl hAm hBm.compl

omit [Countable ι] in
/-- **Events on disjoint coordinate blocks are independent.**  If membership in `A` is determined
by `R ∩ u` and membership in `B` by `R ∩ v` with `u` and `v` disjoint, the two events multiply.

The hypotheses say "depends only on the block" in the form that is actually usable — invariance
under any change outside the block — rather than by exhibiting a cylinder decomposition.

**No `[Countable ι]`**, unlike its neighbour: the proof goes through `indep_iSup_of_disjoint`,
which takes `Set ι` rather than `Finset ι`, so countability never enters.  The contributor who
proved it found this and reported it rather than silencing the linter, since removing the
instance is a statement change.  Harris above does need it, so the asymmetry between the two is
real. -/
theorem setBernoulli_inter_eq_mul_of_disjoint (p : I) (u v : Set ι) (huv : Disjoint u v)
    (A B : Set (Set ι))
    (hA : ∀ R R' : Set ι, R ∩ u = R' ∩ u → (R ∈ A ↔ R' ∈ A))
    (hB : ∀ R R' : Set ι, R ∩ v = R' ∩ v → (R ∈ B ↔ R' ∈ B))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    setBernoulli Set.univ p (A ∩ B)
      = setBernoulli Set.univ p A * setBernoulli Set.univ p B := by
  classical
  -- Each coordinate of the underlying product measure on `ι → Prop` is a probability measure.
  have hprob : ∀ i : ι, IsProbabilityMeasure
      (toNNReal p • Measure.dirac (i ∈ (Set.univ : Set ι))
        + toNNReal (σ p) • Measure.dirac False) := by
    intro i
    constructor
    simp
  -- The coordinate σ-algebras of that product measure are independent.
  have hindep :
      iIndep (fun i : ι => MeasurableSpace.comap (fun x : ι → Prop => x i) inferInstance)
        (Measure.infinitePi fun i : ι =>
          toNNReal p • Measure.dirac (i ∈ (Set.univ : Set ι))
            + toNNReal (σ p) • Measure.dirac False) :=
    ProbabilityTheory.iIndepFun.iIndep
      (iIndepFun_infinitePi (X := fun _ : ι => id) fun _ => measurable_id)
  have hle : ∀ i : ι,
      MeasurableSpace.comap (fun x : ι → Prop => x i) inferInstance
        ≤ (inferInstance : MeasurableSpace (ι → Prop)) :=
    fun i => (measurable_pi_apply i).comap_le
  -- Invariance of `S` under changes outside `w` makes `S` measurable for the σ-algebra
  -- generated by the coordinates in `w`: the event is fixed by the projection
  -- `x ↦ fun i => x i ∧ i ∈ w`, which reads only those coordinates.
  have key : ∀ (w : Set ι) (S : Set (Set ι)),
      (∀ R R' : Set ι, R ∩ w = R' ∩ w → (R ∈ S ↔ R' ∈ S)) → MeasurableSet S →
      MeasurableSet[⨆ i ∈ w, MeasurableSpace.comap (fun x : ι → Prop => x i) inferInstance]
        ((fun x : ι → Prop => {i | x i}) ⁻¹' S) := by
    intro w S hS hSm
    have hcomap : MeasurableSpace.comap (fun (x : ι → Prop) (i : ι) => x i ∧ i ∈ w)
          (inferInstance : MeasurableSpace (ι → Prop))
        ≤ ⨆ i ∈ w, MeasurableSpace.comap (fun x : ι → Prop => x i) inferInstance := by
      show MeasurableSpace.comap _
          (⨆ i : ι, MeasurableSpace.comap (fun x : ι → Prop => x i) inferInstance) ≤ _
      rw [MeasurableSpace.comap_iSup]
      refine iSup_le fun i => ?_
      rw [MeasurableSpace.comap_comp]
      by_cases hi : i ∈ w
      · have hfun : ((fun x : ι → Prop => x i) ∘
            fun (x : ι → Prop) (i : ι) => x i ∧ i ∈ w) = fun x : ι → Prop => x i := by
          funext x; simp [hi]
        rw [hfun]
        exact le_biSup
          (fun j : ι => MeasurableSpace.comap (fun x : ι → Prop => x j) inferInstance) hi
      · have hfun : ((fun x : ι → Prop => x i) ∘
            fun (x : ι → Prop) (i : ι) => x i ∧ i ∈ w) = fun _ : ι → Prop => False := by
          funext x; simp [hi]
        rw [hfun, MeasurableSpace.comap_const]
        exact bot_le
    have heq : (fun x : ι → Prop => {i | x i}) ⁻¹' S
        = (fun (x : ι → Prop) (i : ι) => x i ∧ i ∈ w) ⁻¹'
            ((fun x : ι → Prop => {i | x i}) ⁻¹' S) := by
      ext x
      simp only [Set.mem_preimage]
      refine hS _ _ ?_
      ext i
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      tauto
    rw [heq]
    exact measurable_iff_comap_le.2 hcomap (measurable_setOfPred hSm)
  -- `setBernoulli` is that product measure read through `x ↦ {i | x i}`.
  rw [setBernoulli_apply' (A ∩ B), setBernoulli_apply' A, setBernoulli_apply' B,
    Set.preimage_inter]
  exact (Indep_iff _ _ _).1 (indep_iSup_of_disjoint hle hindep huv) _ _
    (key u A hA hAm) (key v B hB hBm)

end SetBernoulli

/-! ### A non-uniform Bernoulli on subsets

`setBernoulli u p` keeps every element of `u` with the *same* probability `p`.  Warnke's proof of
the Janson lower tail (Chapter 8, Theorem 8.2.2) thins the index set by an independent Bernoulli
`q`, so the thinned space carries independent inclusion probabilities that differ from one
coordinate to the next — and neither Mathlib nor `setBernoulli` has that.  The contributor who
proved `janson_lower_tail` identified the gap and stopped at it rather than inventing a primitive
inside `Janson.lean`; this is that primitive, authored centrally.

It is a strict generalisation, not a parallel notion: `setBernoulli_eq_setBernoulliPi` below
recovers `setBernoulli` exactly, which is the check that the definition is the right one rather
than merely well-typed. -/

section BernoulliPi

variable {ι : Type*}

/-- The product of Bernoulli distributions with **per-coordinate** parameters: the measure on
`Set ι` under which `i` is kept with probability `f i`, independently across `i`.

`setBernoulli u p` is the special case `f = p` on `u` and `0` off it. -/
noncomputable def setBernoulliPi (f : ι → I) : Measure (Set ι) :=
  .comap (fun s i ↦ i ∈ s) <| Measure.infinitePi fun i : ι ↦
    toNNReal (f i) • Measure.dirac True + toNNReal (σ (f i)) • Measure.dirac False

/-- Registered eagerly: `Measure.infinitePi` is `if h : ∀ i, IsProbabilityMeasure (μ i) then … else
0`, so without this instance in scope the definition above is silently the zero measure and no
`infinitePi` lemma fires.  See the "junk values" note in `skills/conventions.md`. -/
instance (f : ι → I) : IsProbabilityMeasure (setBernoulliPi f) :=
  MeasurableEquiv.setOfPred.symm.measurableEmbedding.isProbabilityMeasure_comap <|
    .of_forall fun P ↦ ⟨{i | P i}, rfl⟩

lemma setBernoulliPi_apply' (f : ι → I) (S : Set (Set ι)) :
    setBernoulliPi f S = (Measure.infinitePi fun i ↦
        toNNReal (f i) • Measure.dirac True + toNNReal (σ (f i)) • Measure.dirac False)
      ((fun p ↦ {i | p i}) ⁻¹' S) := MeasurableEquiv.setOfPred.symm.comap_apply ..

/-- `setBernoulliPi` generalises `setBernoulli`.  Stated with hypotheses rather than
`f = fun i ↦ if i ∈ u then p else 0`, since that spelling would need `Decidable (i ∈ u)` and the
project adds no `Decidable` instances. -/
lemma setBernoulli_eq_setBernoulliPi {u : Set ι} {p : I} {f : ι → I}
    (hin : ∀ i ∈ u, f i = p) (hout : ∀ i ∉ u, f i = 0) :
    setBernoulli u p = setBernoulliPi f := by
  unfold setBernoulli setBernoulliPi
  congr 2
  funext i
  have hsum : toNNReal p + toNNReal (σ p) = 1 := by
    ext; push_cast [unitInterval.coe_symm_eq]
    simp [*]
  by_cases h : i ∈ u
  · simp [hin i h, h]
  · simp only [h, hout i h]
    simp [← add_smul, hsum]

end BernoulliPi

/-! ### §4.3 Thresholds: multiple round exposure

Zhao, Lemma 4.3.7 (`sources/mit18_226_f22_lec_full.pdf`, printed p. 49 = PDF p. 55) — the
quantitative engine behind Bollobás–Thomason (Theorem 4.3.6, every non-trivial monotone property
has a threshold).  It lives in this file rather than in `SecondMoment.lean` because it is a
statement about `setBernoulli` and upper sets, which is this file's subject; Chapter 4's own file
is measure-theoretic but has no random-subset machinery. -/

/-- **Monotonicity of the satisfying probability** (Zhao, Theorem 4.3.5).  For a monotone
property `F`, the probability that `Ω_p` satisfies it is non-decreasing in `p`.

This is what `prob_notMem_le_pow_of_isUpperSet` below consumes, and it is the reason a
"threshold" is a meaningful notion at all: without monotonicity in `p` there would be nothing
for a critical probability to be critical *about*.

**The non-strict form is stated, deliberately.**  The book's Theorem 4.3.5 says *strictly*
increasing, which needs `F` non-trivial — neither empty nor everything.  Strictness is not used
anywhere downstream: Lemma 4.3.7 and the threshold argument both need only `≤`, and dropping
non-triviality makes this usable without side conditions.  If the strict version is ever wanted
it should be a separate node with the non-triviality hypothesis, not a strengthening of this one.

**Route.**  The standard coupling: draw one uniform `t x ∈ [0,1]` per element and read off
`A = {x | t x ≤ p}` and `B = {x | t x ≤ q}`.  Then `A` is distributed as `Ω_p`, `B` as `Ω_q`, and
`p ≤ q` gives `A ⊆ B` pointwise, so `A ∈ F → B ∈ F` because `F` is an upper set.  Mathlib's
`fkg`/`holley` neighbourhood is not what is wanted here; this is a monotone-coupling argument, not
a correlation inequality.

Stated in `ℝ≥0∞` rather than through `.toReal`, since no subtraction is involved and the
coercion would only add noise. -/
theorem prob_mem_mono_of_isUpperSet {ι : Type*} [Countable ι] (F : Set (Set ι))
    (hF : IsUpperSet F) (hFm : MeasurableSet F) {p q : I} (hpq : (p : ℝ) ≤ (q : ℝ)) :
    setBernoulli Set.univ p F ≤ setBernoulli Set.univ q F := by
  sorry

/-- **Multiple round exposure** (Zhao, Lemma 4.3.7).  If a monotone property `F` is missed by
`Ω_p`, then it is missed by each of `m` independent copies of `Ω_q`, so
`ℙ(Ω_p ∉ F) ≤ ℙ(Ω_q ∉ F) ^ m`.

**The hypothesis is stated in its natural general form** rather than as `q = p / m`.  The union
`Y` of `m` independent copies of `Ω_q` keeps each element with probability `1 - (1 - q)^m`, so
the argument needs exactly that this is at most `p` — then `ℙ(Ω_p ∉ F) ≤ ℙ(Y ∉ F)`, because
missing an upper set is a decreasing event, and `ℙ(Y ∉ F) ≤ ℙ(Ω_q ∉ F)^m` because `Y` misses `F`
only if all `m` copies do.

The book's `q = p / m` is the special case, and it satisfies the hypothesis by Bernoulli's
inequality: `(1 - p/m)^m ≥ 1 - p` gives `1 - (1 - p/m)^m ≤ p`.  Checked numerically for
`m ≤ 10` across `p`.  Stating it this way avoids having to produce `p / m` as an element of the
unit interval, and is strictly more general.

`[Countable ι]` for the reason recorded throughout Chapters 7 and 8: off it, the events here are
not measurable and `setBernoulli` silently returns an outer measure. -/
theorem prob_notMem_le_pow_of_isUpperSet {ι : Type*} [Countable ι] (F : Set (Set ι))
    (hF : IsUpperSet F) (hFm : MeasurableSet F) (p q : I) (m : ℕ)
    (hpq : 1 - (1 - (q : ℝ)) ^ m ≤ (p : ℝ)) :
    (setBernoulli Set.univ p Fᶜ).toReal ≤ (setBernoulli Set.univ q Fᶜ).toReal ^ m := by
  sorry

end ProbMethodCombinatorics
