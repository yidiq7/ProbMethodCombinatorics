import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.Order.UpperLower.Basic
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
  sorry

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

end ProbMethodCombinatorics
