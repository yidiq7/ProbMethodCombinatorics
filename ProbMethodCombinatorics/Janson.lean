import ProbMethodCombinatorics.Correlation
import ProbMethodCombinatorics.SecondMoment
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Chapter 8: Janson Inequalities

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Chapter 8.

Janson's inequalities bound the probability that a random subset contains **none** of a
prescribed family of sets, and more generally the lower tail of the count.  Where the second
moment method (Chapter 4) gives polynomial decay, these give exponential decay.

Setup 8.1.1 throughout: `R` is a random subset of `ι`, each element kept independently with
probability `p` — Mathlib's `setBernoulli` — and `A i` is the event `S i ⊆ R`.  The dependency
set `D` is a parameter rather than something computed from `S`, exactly as in
`variance_sum_indicator_le`: any `D` containing every dependent ordered pair is admissible, and
a larger `D` only weakens the bound.

Nothing in this chapter is in Mathlib.

**`[Countable ι]` is load-bearing on every theorem below, and is not boilerplate.**  The
measurable space on `Set ι` is the product σ-algebra, in which a set is measurable only if it
depends on countably many coordinates.  For uncountable `S i` the event `{R | S i ⊆ R}` is
therefore not measurable and `setBernoulli` silently returns an *outer* measure.  At `p = 1`
that breaks the inequality outright: with `ι` uncountable, `κ = Unit` and `S 0 = univ`, the
event `{R | R ≠ univ}` has no measurable superset excluding `univ` — a measurable set depends on
countably many coordinates `J`, so containing any `R ≠ univ` forces it to contain `univ` — hence
its outer measure is `1`, while `μ = 1` and `Δ = 0` put the bound at `exp (-1)`.  Mathlib's own
`SetBernoulli` API draws the same line: everything substantive in `SetBernoulli.lean` lives
inside `section Countable`.  Under `[Countable ι]` every event here is a countable intersection
of cylinders and the arguments are sound.  For `p < 1` the uncountable case is merely null
rather than wrong, but the hypothesis is the honest fix.
-/

namespace ProbMethodCombinatorics

open MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

variable {ι κ : Type*} [Fintype κ]

/-- The expected number of the sets `S i` contained in the random subset: `μ` of Setup 8.1.1. -/
noncomputable def jansonMu (p : I) (S : κ → Set ι) : ℝ :=
  ∑ i, (setBernoulli Set.univ p {R : Set ι | S i ⊆ R}).toReal

/-- The dependency sum `Δ` of Setup 8.1.1, taken over the ordered pairs listed in `D`. -/
noncomputable def jansonDelta (p : I) (S : κ → Set ι) (D : Finset (κ × κ)) : ℝ :=
  ∑ q ∈ D, (setBernoulli Set.univ p {R : Set ι | S q.1 ∪ S q.2 ⊆ R}).toReal

/-- The number of the sets `S i` contained in `R`: the random variable `X` of Setup 8.1.1.

`Set.ncard` rather than `Finset.filter`, because set inclusion on `Set ι` is not decidable and
the project does not introduce `Decidable` instances. -/
noncomputable def jansonCount (S : κ → Set ι) (R : Set ι) : ℝ :=
  ({i | S i ⊆ R} : Set κ).ncard

/-- Containing a fixed set is an increasing property of the random subset: `{R | s ⊆ R}` is an
upper set of `Set ι`.  This is what makes Harris' inequality (Chapter 7) applicable to the events
`A i` of Setup 8.1.1. -/
theorem isUpperSet_setOf_subset (s : Set ι) : IsUpperSet {R : Set ι | s ⊆ R} :=
  fun _ _ hle hmem => hmem.trans hle

/-! ### Restricting the ground set

Every theorem below is stated for `setBernoulli Set.univ p`, a random subset of all of `ι`.  The
random objects the book applies Janson to are not of that shape: `G(n, p)` is
`setBernoulli Sym2.diagSetᶜ p` pulled back along `SimpleGraph.edgeSet`, whose ground set omits the
diagonal.  The lemma below is the transfer, and it is the only thing standing between this chapter
and its applications in §8.1, §8.2 and §8.3.
-/

/-- Intersecting a `setBernoulli` sample with a set `u` gives a `setBernoulli` sample on the
smaller ground set `v ∩ u`.

Coordinatewise this is immediate: an element of `u` is kept exactly when the original sample kept
it, and an element outside `u` is discarded, matching the coordinate of `setBer(v ∩ u, p)`, which
is `dirac False` there.

Specialised at `v = Set.univ` this transfers any event that depends only on the trace on `u` — in
particular `{R | s ⊆ R}` for `s ⊆ u` — from `setBer(u, p)` to the `setBer(Set.univ, p)` of the
statements below. -/
theorem map_inter_setBernoulli (u v : Set ι) (p : I) :
    (setBernoulli v p).map (· ∩ u) = setBernoulli (v ∩ u) p := by
  -- `fun_prop` cannot see through `Inter.inter` on `Set ι`; the membership coordinates can.
  have hinter : Measurable (fun s : Set ι => s ∩ u) :=
    measurable_set_iff.2 fun a => by
      simp only [Set.mem_inter_iff]
      exact (measurable_pi_apply a).and measurable_const
  have hf : ∀ a : ι, Measurable (fun b : Prop => b ∧ a ∈ u) := fun a =>
    measurable_id.and measurable_const
  have hlam : Measurable (fun (x : ι → Prop) (a : ι) => x a ∧ a ∈ u) :=
    measurable_pi_lambda _ fun a => (measurable_pi_apply a).and measurable_const
  -- Along `MeasurableEquiv.setOfPred` the trace map becomes coordinatewise.
  have hcomp : ((fun s : Set ι => s ∩ u) ∘ (fun x : ι → Prop => {i | x i}))
      = (fun x : ι → Prop => {i | x i}) ∘ (fun (x : ι → Prop) (a : ι) => x a ∧ a ∈ u) := by
    funext x; rfl
  -- The single coordinate: an element of `u` is kept as before, one outside `u` is discarded.
  have hcoord : ∀ a : ι,
      Measure.map (fun b : Prop => b ∧ a ∈ u)
          (toNNReal p • Measure.dirac (a ∈ v) + toNNReal (σ p) • Measure.dirac False)
        = toNNReal p • Measure.dirac (a ∈ v ∩ u) + toNNReal (σ p) • Measure.dirac False := by
    intro a
    by_cases hau : a ∈ u
    · have hid : (fun b : Prop => b ∧ a ∈ u) = id := by funext b; simp [hau]
      have hv : (a ∈ v ∩ u) = (a ∈ v) := by simp [hau]
      rw [hid, Measure.map_id, hv]
    · have hc : (fun b : Prop => b ∧ a ∈ u) = (fun _ => False) := by funext b; simp [hau]
      have hv : (a ∈ v ∩ u) = False := by simp [hau]
      rw [hc, Measure.map_const, hv, ← add_smul]
      simp
  rw [setBernoulli_eq_map v p, Measure.map_map hinter measurable_setOfPred, hcomp,
    ← Measure.map_map measurable_setOfPred hlam,
    Measure.infinitePi_map_pi (f := fun (a : ι) (b : Prop) => b ∧ a ∈ u) _ hf,
    setBernoulli_eq_map (v ∩ u) p]
  simp_rw [hcoord]

/-- **Janson's inequalities apply to `G(n, p)`.**  For a family of non-loop pair sets `S i`, the
probability that `G(n, p)` contains none of them is the probability computed by the theorems
below, which are stated over `setBernoulli Set.univ p`.

This is the whole content of the transfer, and every asymptotic application in §8.1–§8.3 goes
through it.  Two steps, neither of which is about Janson:

* `binomialRandom_eq_map` reads `G(n, p)` as `setBer(Sym2.diagSetᶜ, p)` pushed along
  `fromEdgeSet`, and `edgeSet_fromEdgeSet` says the edge set recovered that way is
  `R \ Sym2.diagSet`.  Since no `e ∈ S i` is a loop, `↑(S i) ⊆ R \ Sym2.diagSet` and
  `↑(S i) ⊆ R` say the same thing, so the event is unchanged.
* `map_inter_setBernoulli` moves the ground set from `Sym2.diagSetᶜ` up to `Set.univ`, which is
  legitimate for exactly the same reason: the event depends only on the trace off the diagonal.
-/
theorem binomialRandom_setOf_forall_not_subset {n : ℕ} (p : I)
    (S : κ → Finset (Sym2 (Fin n))) (hS : ∀ i, ∀ e ∈ S i, ¬ e.IsDiag) :
    SimpleGraph.binomialRandom (Fin n) p
        {G : SimpleGraph (Fin n) | ∀ i, ¬ (↑(S i) ⊆ G.edgeSet)}
      = setBernoulli Set.univ p {R : Set (Sym2 (Fin n)) | ∀ i, ¬ (↑(S i) ⊆ R)} := by
  -- `S i` has no loop, so intersecting the sample with the complement of the diagonal
  -- changes neither the events nor their conjunction.
  have hdiag : ∀ (i : κ) (R : Set (Sym2 (Fin n))),
      (↑(S i) ⊆ R ∩ (Sym2.diagSet)ᶜ ↔ ↑(S i) ⊆ R) := fun i R =>
    ⟨fun h => h.trans Set.inter_subset_left, fun h _ hx =>
      ⟨h hx, by simpa using hS i _ (Finset.mem_coe.1 hx)⟩⟩
  have hmeasG : MeasurableSet {G : SimpleGraph (Fin n) | ∀ i, ¬ (↑(S i) ⊆ G.edgeSet)} :=
    (Measurable.forall fun _ =>
      (Measurable.subset measurable_const SimpleGraph.measurable_edgeSet).not).setOf
  have hmeasR : MeasurableSet {R : Set (Sym2 (Fin n)) | ∀ i, ¬ (↑(S i) ⊆ R)} :=
    (Measurable.forall fun _ =>
      (Measurable.subset measurable_const measurable_id).not).setOf
  have hinter : Measurable (fun R : Set (Sym2 (Fin n)) => R ∩ (Sym2.diagSet)ᶜ) :=
    measurable_set_iff.2 fun a => by
      simp only [Set.mem_inter_iff]
      exact (measurable_pi_apply a).and measurable_const
  -- `G(n, p)` is `setBer(Sym2.diagSetᶜ, p)` pushed along `fromEdgeSet`.
  rw [SimpleGraph.binomialRandom_eq_map,
    Measure.map_apply SimpleGraph.measurable_fromEdgeSet hmeasG]
  have hpre : SimpleGraph.fromEdgeSet ⁻¹'
        {G : SimpleGraph (Fin n) | ∀ i, ¬ (↑(S i) ⊆ G.edgeSet)}
      = {R : Set (Sym2 (Fin n)) | ∀ i, ¬ (↑(S i) ⊆ R)} := by
    ext R
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, SimpleGraph.edgeSet_fromEdgeSet,
      Set.sdiff_eq, hdiag]
  -- Raise the ground set from `Sym2.diagSetᶜ` to `Set.univ`.
  rw [hpre, ← Set.univ_inter (Sym2.diagSetᶜ : Set (Sym2 (Fin n))),
    ← map_inter_setBernoulli, Measure.map_apply hinter hmeasR]
  congr 1
  ext R
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hdiag]

/-! ### §8.1.5: the triangle family in `G(n, p)`

Setup 8.1.1 instantiated at the question the chapter keeps returning to.  The ground set is the
non-loop pairs of `Fin n`, the index set is the triples of vertices, and `S T` is the three edges
of the triangle on `T`.  `μ` and `Δ` for this family are what Theorems 8.1.6, 8.1.8 and 8.1.10
are stated against, and `binomialRandom_setOf_forall_not_subset` carries the resulting bounds
over to `G(n, p)`.
-/

/-- **`μ` for the `k`-clique family is `binom(n,k) p^{binom(k,2)}`.**

The general form of `jansonMu_triangleFamily`, which is the case `k = 3`.  Each of the
`binom(n,k)` vertex sets of size `k` contributes the probability that its `binom(k,2)` pairs are
all present, by `setBernoulli_setOf_subset`; `card_offDiagPairs_add` turns `#S = k` into
`#(offDiagPairs S) = binom(k,2)`.

This is what §8.3's chromatic-number argument needs — it runs Janson on cliques of size about
`2 log₂ n`, not on triangles — and it is the `setBernoulli` companion of
`prob_not_cliqueFree_le` in `SecondMoment.lean`, which bounds the same quantity over `G(n, p)` by
a union bound rather than computing it.

`k = 0` and `k = 1` are real cases: `binom(k,2) = 0`, so every index contributes `1` and `μ` is
`binom(n,k)`. -/
theorem jansonMu_cliqueFamily (n k : ℕ) (p : I) :
    jansonMu p (fun S : {S : Finset (Fin n) // S.card = k} =>
        (↑(offDiagPairs (S : Finset (Fin n))) : Set (Sym2 (Fin n))))
      = (n.choose k : ℝ) * (p : ℝ) ^ k.choose 2 := by
  -- A `k`-set spans `binom(k,2)` non-loop pairs: `#(offDiagPairs S) + k = binom(k+1,2)`, and
  -- `binom(k+1,2) = k + binom(k,2)`.
  have hcardk : ∀ S : {S : Finset (Fin n) // S.card = k},
      (offDiagPairs (S : Finset (Fin n))).card = k.choose 2 := by
    intro S
    have h := card_offDiagPairs_add (S : Finset (Fin n))
    rw [S.2] at h
    have hsucc : (k + 1).choose 2 = k + k.choose 2 := by
      rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right]
    rw [hsucc] at h
    omega
  -- The index type is the `k`-element subsets of `Fin n`, of which there are `binom(n,k)`.
  have hcount : Fintype.card {S : Finset (Fin n) // S.card = k} = n.choose k := by
    rw [Fintype.card_subtype]
    have hfilter : {S ∈ (Finset.univ : Finset (Finset (Fin n))) | S.card = k}
        = (Finset.univ : Finset (Fin n)).powersetCard k := by
      ext S
      simp
    rw [hfilter, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  -- Each `k`-set contributes the probability `p ^ binom(k,2)` that all its pairs are present.
  have hterm : ∀ S : {S : Finset (Fin n) // S.card = k},
      (setBernoulli Set.univ p
          {R : Set (Sym2 (Fin n)) | ↑(offDiagPairs (S : Finset (Fin n))) ⊆ R}).toReal
        = (p : ℝ) ^ k.choose 2 := by
    intro S
    rw [setBernoulli_setOf_subset, hcardk S, ENNReal.toReal_pow, ENNReal.coe_toReal,
      unitInterval.coe_toNNReal]
  rw [jansonMu, Finset.sum_congr rfl fun S _ => hterm S, Finset.sum_const, Finset.card_univ,
    hcount, nsmul_eq_mul]

/-- **`μ` for the triangle family is `binom(n,3) p³`.**

Each of the `binom(n,3)` triples contributes the probability that its three edges are all
present, which is `p ³` by `setBernoulli_setOf_subset` — the triple spans exactly three non-loop
pairs, since `card_offDiagPairs_add` gives `#(offDiagPairs T) + 3 = binom(4,2) = 6`.

The same number as `integral_triangleCount` of Chapter 4, reached over a different sample space:
there the count is a random variable on `SimpleGraph (Fin n)`, here it is a sum of event
probabilities on `Set (Sym2 (Fin n))`. -/
theorem jansonMu_triangleFamily (n : ℕ) (p : I) :
    jansonMu p (fun T : {T : Finset (Fin n) // T.card = 3} =>
        (↑(offDiagPairs (T : Finset (Fin n))) : Set (Sym2 (Fin n))))
      = (n.choose 3 : ℝ) * (p : ℝ) ^ 3 := by
  simpa using jansonMu_cliqueFamily n 3 p
/-- The dependency set for the `k`-clique family: two distinct `k`-sets are dependent exactly
when they share an edge, which means sharing at least two vertices.

`triangleDependency` is the `k = 3` case, where "at least two" forces "exactly two"; for larger
`k` the intersection ranges over `2, …, k-1` and the dependency is genuinely graded, which is
what makes `jansonDelta_cliqueFamily` a sum rather than a single term. -/
def cliqueDependency (n k : ℕ) :
    Finset ({S : Finset (Fin n) // S.card = k} × {S : Finset (Fin n) // S.card = k}) :=
  Finset.univ.filter fun q =>
    q.1 ≠ q.2 ∧ 2 ≤ ((q.1 : Finset (Fin n)) ∩ (q.2 : Finset (Fin n))).card

/-- **`Δ` for the `k`-clique family, exactly.**

Grade the dependent pairs by `j = #(A ∩ B)`, which runs over `2, …, k-1`.  There are
`binom(n,k) binom(k,j) binom(n-k,k-j)` ordered pairs at grade `j` — choose `A`, choose which `j`
of its vertices are shared, choose the remaining `k - j` of `B` from outside `A` — and each
spans `2 binom(k,2) - binom(j,2)` distinct pairs, the two cliques' edges minus the shared clique
counted twice.

The `k = 3` case collapses to the single term `3 binom(n,3) (n-3) p⁵` of
`jansonDelta_triangleFamily`, since only `j = 2` survives.

`k ≤ 1` gives an empty sum and no dependent pairs, which agrees. -/
theorem jansonDelta_cliqueFamily (n k : ℕ) (p : I) :
    jansonDelta p
        (fun S : {S : Finset (Fin n) // S.card = k} =>
          (↑(offDiagPairs (S : Finset (Fin n))) : Set (Sym2 (Fin n))))
        (cliqueDependency n k)
      = ∑ j ∈ Finset.Ico 2 k,
          (n.choose k * k.choose j * (n - k).choose (k - j) : ℕ)
            * (p : ℝ) ^ (2 * k.choose 2 - j.choose 2) := by
  sorry

/-- The dependency set for the triangle family: two distinct triples are dependent exactly when
they share an edge, which for triples means sharing two vertices.

Triples meeting in at most one vertex span **disjoint** edge sets, so their events are genuinely
independent and are correctly left out.  This `D` is therefore not merely admissible but minimal,
and `A ≠ B` together with `2 ≤ #(A ∩ B)` forces `#(A ∩ B) = 2` exactly. -/
def triangleDependency (n : ℕ) :
    Finset ({T : Finset (Fin n) // T.card = 3} × {T : Finset (Fin n) // T.card = 3}) :=
  Finset.univ.filter fun q =>
    q.1 ≠ q.2 ∧ 2 ≤ ((q.1 : Finset (Fin n)) ∩ (q.2 : Finset (Fin n))).card

/-- Two distinct triples that share at least two vertices share **exactly** two: a third shared
vertex would exhaust both triples and make them equal. -/
private theorem card_inter_eq_two_of_mem_triangleDependency {n : ℕ}
    (q : {T : Finset (Fin n) // T.card = 3} × {T : Finset (Fin n) // T.card = 3})
    (hq : q ∈ triangleDependency n) :
    ((q.1 : Finset (Fin n)) ∩ (q.2 : Finset (Fin n))).card = 2 := by
  obtain ⟨hne, hge⟩ := (Finset.mem_filter.1 hq).2
  have hne' : (q.1 : Finset (Fin n)) ≠ (q.2 : Finset (Fin n)) := fun h => hne (Subtype.ext h)
  have h3 : ((q.1 : Finset (Fin n)) ∩ (q.2 : Finset (Fin n))).card ≠ 3 := by
    intro h
    exact hne' ((Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      (by rw [q.1.2, h])).symm.trans
      (Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [q.2.2, h])))
  have hle := Finset.card_le_card
    (Finset.inter_subset_left (s₁ := (q.1 : Finset (Fin n))) (s₂ := (q.2 : Finset (Fin n))))
  rw [q.1.2] at hle
  omega

/-- **`Δ` for the triangle family is at most `n⁴p⁵`.**

Two triples sharing an edge span `3 + 3 - 1 = 5` distinct non-loop pairs, so each dependent pair
contributes `p ⁵`, and there are `3 binom(n,3) (n-3)` ordered dependent pairs — choose a triple,
choose which two of its vertices are shared, choose the replacement vertex.  That count is
`n(n-1)(n-2)(n-3)/2`, comfortably below `n⁴`.

The constant is deliberately loose, as in `variance_triangleCount_le`: `Δ ≍ n⁴p⁵` is all the
applications need, and tracking the exact binomial would cost the prover more than it buys. -/
theorem jansonDelta_triangleFamily_le (n : ℕ) (p : I) :
    jansonDelta p
        (fun T : {T : Finset (Fin n) // T.card = 3} =>
          (↑(offDiagPairs (T : Finset (Fin n))) : Set (Sym2 (Fin n))))
        (triangleDependency n)
      ≤ (n : ℝ) ^ 4 * (p : ℝ) ^ 5 := by
  classical
  -- A triple spans exactly three non-loop pairs: `#(offDiagPairs T) + 3 = binom(4,2) = 6`.
  have hcard3 : ∀ T : {T : Finset (Fin n) // T.card = 3},
      (offDiagPairs (T : Finset (Fin n))).card = 3 := by
    intro T
    have hT := T.2
    have h := card_offDiagPairs_add (T : Finset (Fin n))
    rw [hT] at h
    norm_num [Nat.choose] at h
    omega
  have hinter2 := fun q (hq : q ∈ triangleDependency n) =>
    card_inter_eq_two_of_mem_triangleDependency q hq
  -- Two triples sharing an edge span `3 + 3 - 1 = 5` non-loop pairs.
  have hcard5 : ∀ q ∈ triangleDependency n,
      (offDiagPairs (q.1 : Finset (Fin n)) ∪ offDiagPairs (q.2 : Finset (Fin n))).card = 5 := by
    intro q hq
    have h2 := hinter2 q hq
    have hone : (offDiagPairs ((q.1 : Finset (Fin n)) ∩ (q.2 : Finset (Fin n)))).card = 1 := by
      have h := card_offDiagPairs_add ((q.1 : Finset (Fin n)) ∩ (q.2 : Finset (Fin n)))
      rw [h2] at h
      norm_num [Nat.choose] at h
      omega
    have h := Finset.card_union_add_card_inter
      (offDiagPairs (q.1 : Finset (Fin n))) (offDiagPairs (q.2 : Finset (Fin n)))
    rw [offDiagPairs_inter, hcard3 q.1, hcard3 q.2, hone] at h
    omega
  -- Each dependent pair contributes the probability `p ⁵` that its five pairs are all present.
  have hterm : ∀ q ∈ triangleDependency n,
      (setBernoulli Set.univ p {R : Set (Sym2 (Fin n)) |
          (↑(offDiagPairs (q.1 : Finset (Fin n))) : Set (Sym2 (Fin n)))
            ∪ (↑(offDiagPairs (q.2 : Finset (Fin n))) : Set (Sym2 (Fin n))) ⊆ R}).toReal
        = (p : ℝ) ^ 5 := by
    intro q hq
    rw [← Finset.coe_union, setBernoulli_setOf_subset, hcard5 q hq, ENNReal.toReal_pow,
      ENNReal.coe_toReal, unitInterval.coe_toNNReal]
  -- `(a, b, x, y) ↦ ({x, a, b}, {y, a, b})` covers every dependent pair, so `#D ≤ n ⁴`.
  have hDnat : (triangleDependency n).card ≤ n ^ 4 := by
    have hinjimg : Function.Injective
        (fun q : {T : Finset (Fin n) // T.card = 3} × {T : Finset (Fin n) // T.card = 3} =>
          ((q.1 : Finset (Fin n)), (q.2 : Finset (Fin n)))) := by
      intro q r h
      exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
    have hsurj : Set.SurjOn
        (fun v : Fin n × Fin n × Fin n × Fin n =>
          (({v.2.2.1, v.1, v.2.1} : Finset (Fin n)), ({v.2.2.2, v.1, v.2.1} : Finset (Fin n))))
        (↑(Finset.univ : Finset (Fin n × Fin n × Fin n × Fin n)))
        (↑((triangleDependency n).image
          (fun q : {T : Finset (Fin n) // T.card = 3} × {T : Finset (Fin n) // T.card = 3} =>
            ((q.1 : Finset (Fin n)), (q.2 : Finset (Fin n)))))) := by
      intro z hz
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hz
      obtain ⟨q, hq, rfl⟩ := hz
      obtain ⟨a, b, hab, hintereq⟩ := Finset.card_eq_two.1 (hinter2 q hq)
      have hd1 : ((q.1 : Finset (Fin n)) \ (q.2 : Finset (Fin n))).card = 1 := by
        have := Finset.card_sdiff_add_card_inter
          (q.1 : Finset (Fin n)) (q.2 : Finset (Fin n))
        rw [q.1.2, hinter2 q hq] at this
        omega
      have hd2 : ((q.2 : Finset (Fin n)) \ (q.1 : Finset (Fin n))).card = 1 := by
        have := Finset.card_sdiff_add_card_inter
          (q.2 : Finset (Fin n)) (q.1 : Finset (Fin n))
        rw [q.2.2, Finset.inter_comm, hinter2 q hq] at this
        omega
      obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hd1
      obtain ⟨y, hy⟩ := Finset.card_eq_one.1 hd2
      refine ⟨(a, b, x, y), by simp, ?_⟩
      have e1 : (q.1 : Finset (Fin n)) = {x, a, b} := by
        rw [← Finset.sdiff_union_inter (q.1 : Finset (Fin n)) (q.2 : Finset (Fin n)), hx,
          hintereq]
        rfl
      have e2 : (q.2 : Finset (Fin n)) = {y, a, b} := by
        rw [← Finset.sdiff_union_inter (q.2 : Finset (Fin n)) (q.1 : Finset (Fin n)), hy,
          Finset.inter_comm, hintereq]
        rfl
      exact Prod.ext e1.symm e2.symm
    calc (triangleDependency n).card
        = ((triangleDependency n).image
            (fun q : {T : Finset (Fin n) // T.card = 3} × {T : Finset (Fin n) // T.card = 3} =>
              ((q.1 : Finset (Fin n)), (q.2 : Finset (Fin n))))).card :=
          (Finset.card_image_of_injective _ hinjimg).symm
      _ ≤ (Finset.univ : Finset (Fin n × Fin n × Fin n × Fin n)).card :=
          Finset.card_le_card_of_surjOn _ hsurj
      _ = n ^ 4 := by simp [Finset.card_univ]; ring
  have hDc : ((triangleDependency n).card : ℝ) ≤ (n : ℝ) ^ 4 := by
    calc (((triangleDependency n).card : ℕ) : ℝ) ≤ ((n ^ 4 : ℕ) : ℝ) := Nat.cast_le.2 hDnat
      _ = (n : ℝ) ^ 4 := by push_cast; ring
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := p.2.1
  have h5 : (0 : ℝ) ≤ (p : ℝ) ^ 5 := by positivity
  rw [jansonDelta, Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  gcongr

/-- The exact number of ordered dependent pairs of triples: `3 binom(n,3) (n-3)`.

The dependent pairs `(A, B)` are in bijection with the triples `(A, e, x)` where `e` is one of
the three two-element subsets of `A` to be shared and `x ∉ A` is the replacement vertex, via
`B = insert x e`.  Below `n = 4` both sides are `0`: there is no replacement vertex, and `Nat`
truncation of `n - 3` agrees. -/
private theorem card_triangleDependency_exact (n : ℕ) :
    (triangleDependency n).card = 3 * n.choose 3 * (n - 3) := by
  have hinter2 := fun q (hq : q ∈ triangleDependency n) =>
    card_inter_eq_two_of_mem_triangleDependency q hq
  -- The parameter set: a triple `A`, a two-element `e ⊆ A`, and a replacement vertex `x ∉ A`.
  set E : Finset ((_ : {T : Finset (Fin n) // T.card = 3}) × (Finset (Fin n) × Fin n)) :=
    (Finset.univ : Finset {T : Finset (Fin n) // T.card = 3}).sigma
      fun A => ((A : Finset (Fin n)).powersetCard 2) ×ˢ (Finset.univ \ (A : Finset (Fin n)))
    with hEdef
  have hmemE : ∀ a : (_ : {T : Finset (Fin n) // T.card = 3}) × (Finset (Fin n) × Fin n),
      a ∈ E → a.2.1 ⊆ (a.1 : Finset (Fin n)) ∧ a.2.1.card = 2 ∧
        a.2.2 ∉ (a.1 : Finset (Fin n)) := by
    intro a ha
    rw [hEdef, Finset.mem_sigma, Finset.mem_product, Finset.mem_powersetCard,
      Finset.mem_sdiff] at ha
    exact ⟨ha.2.1.1, ha.2.1.2, ha.2.2.2⟩
  -- `A ∩ insert x e = e` whenever `e ⊆ A` and `x ∉ A`.
  have hinterins : ∀ (A e : Finset (Fin n)) (x : Fin n), e ⊆ A → x ∉ A →
      A ∩ insert x e = e := by
    intro A e x hsub hx
    ext y
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hyA, rfl | hye⟩
      · exact absurd hyA hx
      · exact hye
    · intro hye
      exact ⟨hsub hye, Or.inr hye⟩
  -- The map `(A, e, x) ↦ (A, insert x e)` lands in the triples.
  have hins : ∀ a ∈ E, (insert a.2.2 a.2.1).card = 3 := by
    intro a ha
    obtain ⟨hsub, hcard2, hx⟩ := hmemE a ha
    rw [Finset.card_insert_of_notMem fun h => hx (hsub h), hcard2]
  have hcardE : E.card = 3 * n.choose 3 * (n - 3) := by
    have hcount : Fintype.card {T : Finset (Fin n) // T.card = 3} = n.choose 3 := by
      rw [Fintype.card_subtype]
      have hfilter : {T ∈ (Finset.univ : Finset (Finset (Fin n))) | T.card = 3}
          = (Finset.univ : Finset (Fin n)).powersetCard 3 := by
        ext T
        simp
      rw [hfilter, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    have hfib : ∀ A : {T : Finset (Fin n) // T.card = 3},
        (((A : Finset (Fin n)).powersetCard 2) ×ˢ
            (Finset.univ \ (A : Finset (Fin n)) : Finset (Fin n))).card = 3 * (n - 3) := by
      intro A
      rw [Finset.card_product, Finset.card_powersetCard, A.2,
        Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, A.2]
      norm_num [Nat.choose]
    rw [hEdef, Finset.card_sigma, Finset.sum_congr rfl fun A _ => hfib A, Finset.sum_const,
      Finset.card_univ, hcount, smul_eq_mul]
    ring
  rw [← hcardE]
  refine (Finset.card_bij
    (fun a ha => ((a.1, ⟨insert a.2.2 a.2.1, hins a ha⟩) :
      {T : Finset (Fin n) // T.card = 3} × {T : Finset (Fin n) // T.card = 3}))
    ?_ ?_ ?_).symm
  · -- the image is a dependent pair
    intro a ha
    obtain ⟨hsub, hcard2, hx⟩ := hmemE a ha
    have hAe := hinterins (a.1 : Finset (Fin n)) a.2.1 a.2.2 hsub hx
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro h
      exact hx (congrArg (fun T : {T : Finset (Fin n) // T.card = 3} => (T : Finset (Fin n))) h ▸
        Finset.mem_insert_self a.2.2 a.2.1)
    · simp only
      rw [hAe, hcard2]
  · -- injectivity
    intro a₁ ha₁ a₂ ha₂ h
    obtain ⟨hsub₁, hcard₁, hx₁⟩ := hmemE a₁ ha₁
    obtain ⟨hsub₂, hcard₂, hx₂⟩ := hmemE a₂ ha₂
    have hfst : a₁.1 = a₂.1 := congrArg Prod.fst h
    have hsnd : insert a₁.2.2 a₁.2.1 = insert a₂.2.2 a₂.2.1 :=
      congrArg (fun T : {T : Finset (Fin n) // T.card = 3} => (T : Finset (Fin n)))
        (congrArg Prod.snd h)
    have he : a₁.2.1 = a₂.2.1 := by
      rw [← hinterins (a₁.1 : Finset (Fin n)) a₁.2.1 a₁.2.2 hsub₁ hx₁, hsnd, hfst,
        hinterins (a₂.1 : Finset (Fin n)) a₂.2.1 a₂.2.2 hsub₂ hx₂]
    have hxx : a₁.2.2 = a₂.2.2 := by
      have hm : a₁.2.2 ∈ insert a₂.2.2 a₂.2.1 := hsnd ▸ Finset.mem_insert_self _ _
      rcases Finset.mem_insert.1 hm with h' | h'
      · exact h'
      · exact absurd (hsub₁ (he ▸ h')) hx₁
    obtain ⟨A₁, e₁, x₁⟩ := a₁
    obtain ⟨A₂, e₂, x₂⟩ := a₂
    subst hfst
    subst he
    subst hxx
    rfl
  · -- surjectivity
    intro q hq
    have h2 := hinter2 q hq
    have hd2 : ((q.2 : Finset (Fin n)) \ (q.1 : Finset (Fin n))).card = 1 := by
      have := Finset.card_sdiff_add_card_inter
        (q.2 : Finset (Fin n)) (q.1 : Finset (Fin n))
      rw [q.2.2, Finset.inter_comm, h2] at this
      omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hd2
    have hxmem : x ∈ (q.2 : Finset (Fin n)) \ (q.1 : Finset (Fin n)) := by
      rw [hx]
      exact Finset.mem_singleton_self x
    have hxnot : x ∉ (q.1 : Finset (Fin n)) := (Finset.mem_sdiff.1 hxmem).2
    have hBeq : insert x ((q.1 : Finset (Fin n)) ∩ (q.2 : Finset (Fin n)))
        = (q.2 : Finset (Fin n)) := by
      rw [Finset.inter_comm, ← Finset.singleton_union, ← hx,
        Finset.sdiff_union_inter (q.2 : Finset (Fin n)) (q.1 : Finset (Fin n))]
    refine ⟨⟨q.1, ((q.1 : Finset (Fin n)) ∩ (q.2 : Finset (Fin n)), x)⟩, ?_, ?_⟩
    · rw [hEdef, Finset.mem_sigma, Finset.mem_product, Finset.mem_powersetCard,
        Finset.mem_sdiff]
      exact ⟨Finset.mem_univ _, ⟨Finset.inter_subset_left, h2⟩, Finset.mem_univ _, hxnot⟩
    · exact Prod.ext rfl (Subtype.ext hBeq)

/-- **`Δ` for the triangle family, exactly.**  There are `3 binom(n,3) (n-3)` ordered pairs of
distinct triples sharing an edge — choose a triple, choose which two of its vertices are shared,
choose the replacement vertex — and each contributes `p ⁵`.

`jansonDelta_triangleFamily_le` relaxes this to `n⁴p⁵`, which is what the `Δ < μ` regime of
§8.1 wants.  The exact value is what the **other** regime needs: Janson's second inequality
(`janson_prob_none_le_of_mu_le`) is applied when `μ ≤ Δ`, and an upper bound on `Δ` cannot
witness that.  The two forms are used in opposite directions and neither replaces the other.

The formula is correct at every `n`: below `4` the count is `0`, since two distinct triples
sharing two vertices need a fourth vertex, and `Nat` truncation of `n - 3` agrees. -/
theorem jansonDelta_triangleFamily (n : ℕ) (p : I) :
    jansonDelta p
        (fun T : {T : Finset (Fin n) // T.card = 3} =>
          (↑(offDiagPairs (T : Finset (Fin n))) : Set (Sym2 (Fin n))))
        (triangleDependency n)
      = (3 * n.choose 3 * (n - 3) : ℕ) * (p : ℝ) ^ 5 := by
  -- A triple spans exactly three non-loop pairs: `#(offDiagPairs T) + 3 = binom(4,2) = 6`.
  have hcard3 : ∀ T : {T : Finset (Fin n) // T.card = 3},
      (offDiagPairs (T : Finset (Fin n))).card = 3 := by
    intro T
    have hT := T.2
    have h := card_offDiagPairs_add (T : Finset (Fin n))
    rw [hT] at h
    norm_num [Nat.choose] at h
    omega
  have hinter2 := fun q (hq : q ∈ triangleDependency n) =>
    card_inter_eq_two_of_mem_triangleDependency q hq
  -- Two triples sharing an edge span `3 + 3 - 1 = 5` non-loop pairs.
  have hcard5 : ∀ q ∈ triangleDependency n,
      (offDiagPairs (q.1 : Finset (Fin n)) ∪ offDiagPairs (q.2 : Finset (Fin n))).card = 5 := by
    intro q hq
    have h2 := hinter2 q hq
    have hone : (offDiagPairs ((q.1 : Finset (Fin n)) ∩ (q.2 : Finset (Fin n)))).card = 1 := by
      have h := card_offDiagPairs_add ((q.1 : Finset (Fin n)) ∩ (q.2 : Finset (Fin n)))
      rw [h2] at h
      norm_num [Nat.choose] at h
      omega
    have h := Finset.card_union_add_card_inter
      (offDiagPairs (q.1 : Finset (Fin n))) (offDiagPairs (q.2 : Finset (Fin n)))
    rw [offDiagPairs_inter, hcard3 q.1, hcard3 q.2, hone] at h
    omega
  -- Each dependent pair contributes the probability `p ⁵` that its five pairs are all present.
  have hterm : ∀ q ∈ triangleDependency n,
      (setBernoulli Set.univ p {R : Set (Sym2 (Fin n)) |
          (↑(offDiagPairs (q.1 : Finset (Fin n))) : Set (Sym2 (Fin n)))
            ∪ (↑(offDiagPairs (q.2 : Finset (Fin n))) : Set (Sym2 (Fin n))) ⊆ R}).toReal
        = (p : ℝ) ^ 5 := by
    intro q hq
    rw [← Finset.coe_union, setBernoulli_setOf_subset, hcard5 q hq, ENNReal.toReal_pow,
      ENNReal.coe_toReal, unitInterval.coe_toNNReal]
  rw [jansonDelta, Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
    card_triangleDependency_exact]

/-- The conditioning step of the Boppana–Spencer proof of Janson's inequality.

If `i ∉ T` and every `S j` with `j ∈ T` outside `T₁` is disjoint from `S i`, then imposing the
extra event `¬ S i ⊆ R` costs a factor of at most
`1 - ℙ(S i ⊆ R) + ∑_{j ∈ T₁} ℙ(S i ∪ S j ⊆ R)`.

Equivalently, writing `A j` for the event `S j ⊆ R`,

    ℙ(A i ∣ ⋂_{j ∈ T} (A j)ᶜ) ≥ ℙ(A i) - ∑_{j ∈ T₁} ℙ(A i ∩ A j).

The indices of `T` outside `T₁` contribute nothing, `A i` being independent of them; the indices
in `T₁` are handled by Harris' inequality, since `A i ∩ A j` is increasing while
`⋂_{j ∈ T \ T₁} (A j)ᶜ` is decreasing. -/
theorem janson_prob_none_step_le [Countable ι] (p : I) (S : κ → Set ι) (i : κ) (T T₁ : Finset κ)
    (hiT : i ∉ T) (hsub : T₁ ⊆ T) (hindep : ∀ j ∈ T, j ∉ T₁ → Disjoint (S i) (S j)) :
    (setBernoulli Set.univ p {R : Set ι | ¬ S i ⊆ R ∧ ∀ j ∈ T, ¬ S j ⊆ R}).toReal
      ≤ (1 - (setBernoulli Set.univ p {R : Set ι | S i ⊆ R}).toReal
            + ∑ j ∈ T₁, (setBernoulli Set.univ p {R : Set ι | S i ∪ S j ⊆ R}).toReal)
        * (setBernoulli Set.univ p {R : Set ι | ∀ j ∈ T, ¬ S j ⊆ R}).toReal := by
  classical
  simp only [← measureReal_def]
  set μ : Measure (Set ι) := setBernoulli Set.univ p with hμdef
  have hμprob : IsProbabilityMeasure μ := by rw [hμdef]; infer_instance
  have hmeasSub : ∀ s : Set ι, MeasurableSet {R : Set ι | s ⊆ R} := fun s =>
    measurableSet_setOfPred.2 (Measurable.subset measurable_const measurable_id)
  -- `U` indexes the sets disjoint from `S i`, and `v` is the block of coordinates they occupy.
  set U : Set κ := {j | j ∈ T ∧ j ∉ T₁}
  set v : Set ι := ⋃ j ∈ U, S j
  set Ai : Set (Set ι) := {R : Set ι | S i ⊆ R} with hAidef
  set B : Set (Set ι) := {R : Set ι | ∀ j ∈ T, ¬ S j ⊆ R} with hBdef
  set B₀ : Set (Set ι) := {R : Set ι | ∀ j ∈ U, ¬ S j ⊆ R} with hB₀def
  -- `B₀` is a measurable decreasing event containing `B`.
  have hB₀m : MeasurableSet B₀ := by
    have h : B₀ = ⋂ j ∈ U, {R : Set ι | S j ⊆ R}ᶜ := by rw [hB₀def]; ext R; simp
    rw [h]
    exact MeasurableSet.biInter (Set.to_countable U) fun j _ => (hmeasSub (S j)).compl
  have hB₀low : IsLowerSet B₀ := by
    rw [hB₀def]
    intro R R' hle hR j hj hsj
    exact hR j hj (hsj.trans hle)
  have hBsub : B ⊆ B₀ := by
    rw [hBdef, hB₀def]
    exact fun R hR j hj => hR j hj.1
  -- Whether `s ⊆ R` holds depends on `R` only through `R ∩ w`, as soon as `s ⊆ w`.
  have hdep : ∀ w s : Set ι, s ⊆ w → ∀ R R' : Set ι, R ∩ w = R' ∩ w → (s ⊆ R ↔ s ⊆ R') := by
    intro w s hsw
    have key : ∀ X Y : Set ι, X ∩ w = Y ∩ w → s ⊆ X → s ⊆ Y := fun X Y h hX x hx =>
      ((Set.ext_iff.1 h x).1 ⟨hX hx, hsw hx⟩).1
    exact fun R R' h => ⟨key R R' h, key R' R h.symm⟩
  have hSv : ∀ j ∈ U, S j ⊆ v := fun j hj x hx => Set.mem_biUnion hj hx
  have hdisj : Disjoint (S i) v := by
    refine Set.disjoint_left.2 fun x hxi hxv => ?_
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 hxv
    exact Set.disjoint_left.1 (hindep j hj.1 hj.2) hxi hxj
  -- `A i` lives on the block `S i` and `B₀` on the disjoint block `v`, so the two are independent.
  have hind : μ.real (Ai ∩ B₀) = μ.real Ai * μ.real B₀ := by
    have hA : ∀ R R' : Set ι, R ∩ S i = R' ∩ S i → (R ∈ Ai ↔ R' ∈ Ai) := fun R R' h =>
      hdep (S i) (S i) Set.Subset.rfl R R' h
    have hB : ∀ R R' : Set ι, R ∩ v = R' ∩ v → (R ∈ B₀ ↔ R' ∈ B₀) := by
      intro R R' h
      rw [hB₀def]
      exact ⟨fun hR j hj hsj => hR j hj ((hdep v (S j) (hSv j hj) R R' h).2 hsj),
        fun hR j hj hsj => hR j hj ((hdep v (S j) (hSv j hj) R R' h).1 hsj)⟩
    rw [measureReal_def, measureReal_def, measureReal_def,
      setBernoulli_inter_eq_mul_of_disjoint p (S i) v hdisj Ai B₀ hA hB (hAidef ▸ hmeasSub (S i))
        hB₀m, ENNReal.toReal_mul]
  -- Harris, for the increasing event `A i ∩ A j` against the decreasing event `B₀`.
  have harris : ∀ j : κ, μ.real ({R : Set ι | S i ∪ S j ⊆ R} ∩ B₀)
      ≤ μ.real {R : Set ι | S i ∪ S j ⊆ R} * μ.real B₀ := by
    intro j
    have h := setBernoulli_inter_le_mul p {R : Set ι | S i ∪ S j ⊆ R} B₀
      (isUpperSet_setOf_subset _) hB₀low (hmeasSub _) hB₀m
    rw [measureReal_def, measureReal_def, measureReal_def, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (by finiteness) h
  -- Dropping from `B₀` to `B` costs at most one of the events `A j` with `j ∈ T₁`.
  have hcover : Ai ∩ B₀ ⊆ (Ai ∩ B) ∪ ⋃ j ∈ T₁, ({R : Set ι | S i ∪ S j ⊆ R} ∩ B₀) := by
    rintro R ⟨hRi, hRB₀⟩
    by_cases hB₁ : ∀ j ∈ T₁, ¬ S j ⊆ R
    · refine Or.inl ⟨hRi, ?_⟩
      rw [hBdef]
      intro j hjT
      by_cases hj1 : j ∈ T₁
      · exact hB₁ j hj1
      · exact hRB₀ j ⟨hjT, hj1⟩
    · refine Or.inr ?_
      obtain ⟨j, hj, hsj⟩ : ∃ j ∈ T₁, S j ⊆ R := by
        by_contra hcon
        exact hB₁ fun j hj hsj => hcon ⟨j, hj, hsj⟩
      exact Set.mem_biUnion hj ⟨Set.union_subset hRi hsj, hRB₀⟩
  have hmain : μ.real Ai * μ.real B₀
      ≤ μ.real (Ai ∩ B)
        + (∑ j ∈ T₁, μ.real {R : Set ι | S i ∪ S j ⊆ R}) * μ.real B₀ := by
    rw [Finset.sum_mul, ← hind]
    calc μ.real (Ai ∩ B₀)
        ≤ μ.real ((Ai ∩ B) ∪ ⋃ j ∈ T₁, ({R : Set ι | S i ∪ S j ⊆ R} ∩ B₀)) :=
          measureReal_mono hcover
      _ ≤ μ.real (Ai ∩ B) + μ.real (⋃ j ∈ T₁, ({R : Set ι | S i ∪ S j ⊆ R} ∩ B₀)) :=
          measureReal_union_le _ _
      _ ≤ μ.real (Ai ∩ B) + ∑ j ∈ T₁, μ.real ({R : Set ι | S i ∪ S j ⊆ R} ∩ B₀) := by
          gcongr
          exact measureReal_biUnion_finset_le _ _
      _ ≤ μ.real (Ai ∩ B) + ∑ j ∈ T₁, μ.real {R : Set ι | S i ∪ S j ⊆ R} * μ.real B₀ := by
          gcongr with j hj
          exact harris j
  have hLHS : {R : Set ι | ¬ S i ⊆ R ∧ ∀ j ∈ T, ¬ S j ⊆ R} = B \ Ai := by
    rw [hBdef, hAidef]
    ext R
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, and_comm]
  have hAim : MeasurableSet Ai := hAidef ▸ hmeasSub (S i)
  have hdecomp : μ.real (B ∩ Ai) + μ.real (B \ Ai) = μ.real B :=
    measureReal_inter_add_sdiff hAim
  have hq : μ.real B ≤ μ.real B₀ := measureReal_mono hBsub
  -- The bracket may be negative, in which case `B ⊆ B₀` is the wrong way round and unnecessary.
  have hkey : (μ.real Ai - ∑ j ∈ T₁, μ.real {R : Set ι | S i ∪ S j ⊆ R}) * μ.real B
      ≤ μ.real (B ∩ Ai) := by
    rw [Set.inter_comm]
    rcases le_or_gt 0 (μ.real Ai - ∑ j ∈ T₁, μ.real {R : Set ι | S i ∪ S j ⊆ R}) with hc | hc
    · calc (μ.real Ai - ∑ j ∈ T₁, μ.real {R : Set ι | S i ∪ S j ⊆ R}) * μ.real B
          ≤ (μ.real Ai - ∑ j ∈ T₁, μ.real {R : Set ι | S i ∪ S j ⊆ R}) * μ.real B₀ :=
            mul_le_mul_of_nonneg_left hq hc
        _ ≤ μ.real (Ai ∩ B) := by linarith [hmain]
    · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hc.le measureReal_nonneg) measureReal_nonneg
  rw [hLHS]
  linarith [hdecomp, hkey]

/-- The `Δ`-bookkeeping step shared by all three Janson inequalities: adding one index `i` to a
sub-family adds its own `2 ∑_j b i j` over the neighbours of `i`, and the pairs so added are
disjoint from those already counted.

Stated over an explicit `b` and `D` rather than over the local `E` abbreviation that each proof
introduces, so that all three call sites can use it. Extracted after the same block was written
out three times; see `roadmap/janson.md`. -/
private theorem sum_filter_insert_le {κ : Type*} [DecidableEq κ] (D : Finset (κ × κ))
    (b : κ → κ → ℝ) (hb0 : ∀ i j, 0 ≤ b i j) (hbs : ∀ i j, b j i = b i j)
    (i : κ) (T : Finset κ) (hiT : i ∉ T) :
    (∑ z ∈ D.filter fun z => z.1 ∈ T ∧ z.2 ∈ T, b z.1 z.2)
        + 2 * ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j
      ≤ ∑ z ∈ D.filter fun z => z.1 ∈ insert i T ∧ z.2 ∈ insert i T, b z.1 z.2 := by
  have hU : ∑ z ∈ (T.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image
        (fun j => ((i, j) : κ × κ)), b z.1 z.2
      = ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j :=
    Finset.sum_image (fun x _ y _ h => by simpa using h)
  have hV : ∑ z ∈ (T.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image
        (fun j => ((j, i) : κ × κ)), b z.1 z.2
      = ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j := by
    rw [Finset.sum_image (fun x _ y _ h => by simpa using h)]
    exact Finset.sum_congr rfl fun j _ => hbs i j
  have hd1 : Disjoint (D.filter fun z => z.1 ∈ T ∧ z.2 ∈ T)
      ((T.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image fun j => ((i, j) : κ × κ)) := by
    refine Finset.disjoint_left.2 ?_
    rintro z hz hz'
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz'
    exact hiT (Finset.mem_filter.1 hz).2.1
  have hd2 : Disjoint ((D.filter fun z => z.1 ∈ T ∧ z.2 ∈ T) ∪
        (T.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image fun j => ((i, j) : κ × κ))
      ((T.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image fun j => ((j, i) : κ × κ)) := by
    refine Finset.disjoint_left.2 ?_
    rintro z hz hz'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hz'
    rcases Finset.mem_union.1 hz with h | h
    · exact hiT (Finset.mem_filter.1 h).2.2
    · obtain ⟨k, hk, hk'⟩ := Finset.mem_image.1 h
      have : k = i := congrArg Prod.snd hk'
      exact hiT (this ▸ (Finset.mem_filter.1 hk).1)
  have hss : (D.filter fun z => z.1 ∈ T ∧ z.2 ∈ T) ∪
        ((T.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image fun j => ((i, j) : κ × κ)) ∪
        ((T.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image fun j => ((j, i) : κ × κ))
      ⊆ D.filter fun z => z.1 ∈ insert i T ∧ z.2 ∈ insert i T := by
    intro z hz
    rcases Finset.mem_union.1 hz with hz | hz
    · rcases Finset.mem_union.1 hz with hz | hz
      · obtain ⟨hzD, h1, h2⟩ := Finset.mem_filter.1 hz
        exact Finset.mem_filter.2
          ⟨hzD, Finset.mem_insert_of_mem h1, Finset.mem_insert_of_mem h2⟩
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hz
        obtain ⟨hjT, hjD, -⟩ := Finset.mem_filter.1 hj
        exact Finset.mem_filter.2
          ⟨hjD, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hjT⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hz
      obtain ⟨hjT, -, hjD⟩ := Finset.mem_filter.1 hj
      exact Finset.mem_filter.2
        ⟨hjD, Finset.mem_insert_of_mem hjT, Finset.mem_insert_self _ _⟩
  calc (∑ z ∈ D.filter fun z => z.1 ∈ T ∧ z.2 ∈ T, b z.1 z.2)
        + 2 * ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j
      = ∑ z ∈ (D.filter fun z => z.1 ∈ T ∧ z.2 ∈ T) ∪
          ((T.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image fun j => ((i, j) : κ × κ)) ∪
          ((T.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D).image fun j => ((j, i) : κ × κ)),
          b z.1 z.2 := by
        rw [Finset.sum_union hd2, Finset.sum_union hd1, hU, hV]; ring
    _ ≤ ∑ z ∈ D.filter (fun z => z.1 ∈ insert i T ∧ z.2 ∈ insert i T), b z.1 z.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hss fun z _ _ => hb0 _ _

/-- **Janson's inequality I** (Zhao, Theorem 8.1.2): the probability that the random subset
contains none of the `S i` is at most `exp (-μ + Δ/2)`.

Most useful when `Δ = o(μ)`; Harris' inequality (Chapter 7) gives the matching lower bound
`exp (-(1 + o(1)) μ)` in that regime, so the two together pin the probability down. -/
theorem janson_prob_none_le [Countable ι] (p : I) (S : κ → Set ι) (D : Finset (κ × κ))
    (hD : ∀ i j, i ≠ j → (i, j) ∉ D → Disjoint (S i) (S j)) :
    (setBernoulli Set.univ p {R : Set ι | ∀ i, ¬ S i ⊆ R}).toReal
      ≤ Real.exp (-jansonMu p S + jansonDelta p S D / 2) := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : κ → ℝ,
      ∀ i, a i = (setBernoulli Set.univ p {R : Set ι | S i ⊆ R}).toReal := ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : κ → κ → ℝ,
      ∀ i j, b i j = (setBernoulli Set.univ p {R : Set ι | S i ∪ S j ⊆ R}).toReal :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Finset κ → ℝ, ∀ T : Finset κ,
      P T = (setBernoulli Set.univ p {R : Set ι | ∀ j ∈ T, ¬ S j ⊆ R}).toReal :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : Finset κ → ℝ, ∀ T : Finset κ,
      E T = ∑ q ∈ D.filter fun q => q.1 ∈ T ∧ q.2 ∈ T, b q.1 q.2 := ⟨_, fun _ => rfl⟩
  have hb0 : ∀ i j, 0 ≤ b i j := by intro i j; rw [hb]; exact ENNReal.toReal_nonneg
  have hbs : ∀ i j, b j i = b i j := by intro i j; rw [hb, hb, Set.union_comm]
  have hP0 : ∀ T, 0 ≤ P T := by intro T; rw [hP]; exact ENNReal.toReal_nonneg
  have key : ∀ T : Finset κ, P T ≤ Real.exp (-∑ j ∈ T, a j + E T / 2) := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · have h1 : {R : Set ι | ∀ j ∈ (∅ : Finset κ), ¬ S j ⊆ R} = Set.univ := by simp
      rw [hP, h1, hE]
      simp
    · intro i T hiT ih
      have hsub : T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D) ⊆ T := Finset.filter_subset _ _
      have hindep : ∀ j ∈ T, j ∉ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D) →
          Disjoint (S i) (S j) := by
        intro j hj hjn
        have hij : i ≠ j := by rintro rfl; exact hiT hj
        have hnot : ¬ ((i, j) ∈ D ∧ (j, i) ∈ D) := fun h => hjn (Finset.mem_filter.2 ⟨hj, h⟩)
        rcases not_and_or.1 hnot with h | h
        · exact hD i j hij h
        · exact (hD j i hij.symm h).symm
      have hstep := janson_prob_none_step_le p S i T
        (T.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D) hiT hsub hindep
      have hins : {R : Set ι | ∀ j ∈ insert i T, ¬ S j ⊆ R}
          = {R : Set ι | ¬ S i ⊆ R ∧ ∀ j ∈ T, ¬ S j ⊆ R} := by
        ext R; simp
      have hsum : ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j
          = ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D),
              (setBernoulli Set.univ p {R : Set ι | S i ∪ S j ⊆ R}).toReal :=
        Finset.sum_congr rfl fun j _ => hb i j
      have hPins : P (insert i T)
          ≤ (1 - a i + ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j) * P T := by
        rw [hP, hins, hP, ha, hsum]
        exact hstep
      have hEineq : E T + 2 * ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j
          ≤ E (insert i T) := by
        rw [hE, hE]
        exact sum_filter_insert_le D b hb0 hbs i T hiT
      calc P (insert i T)
          ≤ (1 - a i + ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j) * P T := hPins
        _ ≤ Real.exp (-(a i - ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j))
              * P T := by
            refine mul_le_mul_of_nonneg_right ?_ (hP0 T)
            have := Real.add_one_le_exp
              (-(a i - ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j))
            linarith
        _ ≤ Real.exp (-(a i - ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j))
              * Real.exp (-∑ j ∈ T, a j + E T / 2) :=
            mul_le_mul_of_nonneg_left ih (Real.exp_nonneg _)
        _ = Real.exp (-(a i - ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j)
              + (-∑ j ∈ T, a j + E T / 2)) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (-∑ j ∈ insert i T, a j + E (insert i T) / 2) := by
            rw [Finset.sum_insert hiT]
            exact Real.exp_le_exp.2 (by linarith)
  have huniv := key Finset.univ
  have h1 : {R : Set ι | ∀ j ∈ (Finset.univ : Finset κ), ¬ S j ⊆ R}
      = {R : Set ι | ∀ i, ¬ S i ⊆ R} := by simp
  have h2 : ∑ j ∈ (Finset.univ : Finset κ), a j = jansonMu p S :=
    Finset.sum_congr rfl fun j _ => ha j
  have h3 : E (Finset.univ : Finset κ) = jansonDelta p S D := by
    rw [hE, Finset.filter_true_of_mem (fun q _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩)]
    exact Finset.sum_congr rfl fun q _ => hb q.1 q.2
  rw [hP, h1, h2, h3] at huniv
  exact huniv

/-- **Triples off the dependency set span disjoint edge sets.**  This is the hypothesis
`janson_prob_none_le` and `janson_prob_none_le_of_mu_le` both ask for, at the triangle family.

Distinct triples that are not dependent share at most one vertex, and `offDiagPairs` of a set of
size at most one is empty — `card_offDiagPairs_add` gives `binom(1,2) = 0` and `binom(2,2) = 1`.
`offDiagPairs_inter` then turns that emptiness into disjointness without naming any element. -/
private theorem disjoint_offDiagPairs_of_notMem_triangleDependency {n : ℕ}
    (A B : {T : Finset (Fin n) // T.card = 3}) (hne : A ≠ B)
    (hnotD : (A, B) ∉ triangleDependency n) :
    Disjoint (↑(offDiagPairs (A : Finset (Fin n))) : Set (Sym2 (Fin n)))
      (↑(offDiagPairs (B : Finset (Fin n))) : Set (Sym2 (Fin n))) := by
  refine disjoint_offDiagPairs_of_card_inter_le_one _ _ ?_
  have hmem : ((A, B) ∈ triangleDependency n) ↔
      (A ≠ B ∧ 2 ≤ ((A : Finset (Fin n)) ∩ (B : Finset (Fin n))).card) := by
    simp [triangleDependency]
  by_contra hcon
  exact hnotD (hmem.2 ⟨hne, by omega⟩)

/-- **`G(n, p)` is triangle-free with probability at most `exp (-binom(n,3) p³ + n⁴p⁵/2)`**
(Zhao, Question 8.1.5, the finite form behind Theorem 8.1.6).

This is Janson's first inequality run on the triangle family: `μ` is `jansonMu_triangleFamily`
exactly, `Δ` is bounded by `jansonDelta_triangleFamily_le`, and
`binomialRandom_setOf_forall_not_subset` moves the resulting bound from `setBernoulli` to
`G(n, p)`.

Theorem 8.1.6 is the asymptotic reading: when `p = o(n^{-1/2})` the term `n⁴p⁵/2` is `o(n³p³)`,
so the exponent is `-(1 + o(1)) μ`.  That asymptotic form is not stated here; this is the
inequality it is read off. -/
theorem binomialRandom_no_triangle_le (n : ℕ) (p : I) :
    (SimpleGraph.binomialRandom (Fin n) p).real
        {G : SimpleGraph (Fin n) | ∀ T : {T : Finset (Fin n) // T.card = 3},
          ¬ (↑(offDiagPairs (T : Finset (Fin n))) ⊆ G.edgeSet)}
      ≤ Real.exp (-((n.choose 3 : ℝ) * (p : ℝ) ^ 3) + (n : ℝ) ^ 4 * (p : ℝ) ^ 5 / 2) := by
  -- Triples meeting in at most one vertex span disjoint edge sets: a shared edge would put two
  -- shared vertices in the intersection, and `offDiagPairs` of a set of size `≤ 1` is empty.
  have hD := disjoint_offDiagPairs_of_notMem_triangleDependency (n := n)
  -- Janson's inequality on the triangle family, with `μ` substituted exactly.
  have hmain := janson_prob_none_le p
    (fun T : {T : Finset (Fin n) // T.card = 3} =>
      (↑(offDiagPairs (T : Finset (Fin n))) : Set (Sym2 (Fin n))))
    (triangleDependency n) hD
  rw [jansonMu_triangleFamily] at hmain
  -- Cross from `G(n, p)` to `setBernoulli`; the triangle edge sets contain no loop.
  rw [measureReal_def, binomialRandom_setOf_forall_not_subset p
    (fun T : {T : Finset (Fin n) // T.card = 3} => offDiagPairs (T : Finset (Fin n)))
    fun _ _ he => not_isDiag_of_mem_offDiagPairs he]
  -- `Δ` appears positively in the exponent, so relaxing it only weakens the bound.
  refine hmain.trans (Real.exp_le_exp.2 ?_)
  have hDelta := jansonDelta_triangleFamily_le n p
  linarith

/-- **Theorem 8.1.6**: when `p` is `o(n^{-1/2})`, `G(n, p)` is triangle-free with probability
`exp (-(1 + o(1)) μ)`, where `μ = binom(n,3) p³`.

Stated in the project's `ε`–`N` idiom rather than with `o(1)`, and in the upper-bound direction —
the one Janson supplies.  Given `ε > 0` there are `δ > 0` and `N` such that `p √n ≤ δ` and
`N ≤ n` force `ℙ(triangle-free) ≤ exp (-(1 - ε) μ)`.

**The witnesses are `δ = √(ε/6)` and `N = 6`, and both are tight.**  From
`binomialRandom_no_triangle_le` the exponent is `-μ + Δ/2` with `Δ ≤ n⁴p⁵`, so what is needed is
`n⁴p⁵/2 ≤ ε μ`.  Using `n³/12 ≤ binom(n,3)` — which holds from `n = 6` and fails at `n = 5`,
exactly as in `prob_triangle_of_le_mul` — that reduces to `n p² ≤ ε/6`, and `n p² = (p √n)²`.
Sampling the inequality at the boundary leaves no slack: the constant `6` is forced, not chosen. -/
theorem prob_no_triangle_le_of_mul_sqrt_le :
    ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ p : I,
      (p : ℝ) * Real.sqrt n ≤ δ →
        (SimpleGraph.binomialRandom (Fin n) p).real
            {G : SimpleGraph (Fin n) | ∀ T : {T : Finset (Fin n) // T.card = 3},
              ¬ (↑(offDiagPairs (T : Finset (Fin n))) ⊆ G.edgeSet)}
          ≤ Real.exp (-(1 - ε) * ((n.choose 3 : ℝ) * (p : ℝ) ^ 3)) := by
  intro ε hε
  refine ⟨Real.sqrt (ε / 6), by positivity, 6, fun n hn p hp => ?_⟩
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := p.2.1
  have hn6 : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- Squaring `p √n ≤ √(ε/6)` turns the scale hypothesis into `n p² ≤ ε/6`.
  have hnp2 : (n : ℝ) * (p : ℝ) ^ 2 ≤ ε / 6 := by
    have hsq : ((p : ℝ) * Real.sqrt n) ^ 2 ≤ Real.sqrt (ε / 6) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hp 2
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n),
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ε / 6)] at hsq
    linarith only [hsq]
  -- `binom(n,3) = n(n-1)(n-2)/6 ≥ n³/12`, which holds from `n = 6` up.
  have hchoose := cube_div_twelve_le_choose_three hn
  -- `Δ/2 ≤ n⁴p⁵/2 ≤ ε n³p³/12 ≤ ε μ`, the first step being exactly `n p² ≤ ε/6`.
  have hmul : ((n : ℝ) ^ 3 * (p : ℝ) ^ 3) * ((n : ℝ) * (p : ℝ) ^ 2)
      ≤ ((n : ℝ) ^ 3 * (p : ℝ) ^ 3) * (ε / 6) :=
    mul_le_mul_of_nonneg_left hnp2 (by positivity)
  have hstep : (n : ℝ) ^ 3 / 12 * (p : ℝ) ^ 3 ≤ (n.choose 3 : ℝ) * (p : ℝ) ^ 3 :=
    mul_le_mul_of_nonneg_right hchoose (pow_nonneg hp0 3)
  have hmu : ε * ((n : ℝ) ^ 3 / 12 * (p : ℝ) ^ 3) ≤ ε * ((n.choose 3 : ℝ) * (p : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left hstep hε.le
  refine (binomialRandom_no_triangle_le n p).trans (Real.exp_le_exp.2 ?_)
  linarith only [hmul, hmu]

/-- The binomial weight of the subsets of `s` containing a fixed `K` sums to `q ^ #K`. -/
private theorem sum_powerset_weight_eq {α : Type*} [DecidableEq α] (q : ℝ) (s K : Finset α)
    (hK : K ⊆ s) :
    ∑ T ∈ s.powerset, (if K ⊆ T then q ^ T.card * (1 - q) ^ (s \ T).card else 0)
      = q ^ K.card := by
  have h := Finset.prod_add (fun _ : α => q) (fun i => if i ∈ K then (0 : ℝ) else 1 - q) s
  have hL : ∏ i ∈ s, ((fun _ : α => q) i + (fun i => if i ∈ K then (0 : ℝ) else 1 - q) i)
      = q ^ K.card := by
    rw [Finset.prod_congr rfl (g := fun i => if i ∈ K then q else 1) (fun i _ => by
      by_cases hi : i ∈ K <;> simp [hi])]
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.2 hK, Finset.prod_const]
  have hR : ∀ T ∈ s.powerset,
      (∏ i ∈ T, (fun _ : α => q) i) * ∏ i ∈ s \ T, (fun i => if i ∈ K then (0 : ℝ) else 1 - q) i
        = if K ⊆ T then q ^ T.card * (1 - q) ^ (s \ T).card else 0 := by
    intro T hT
    simp only [Finset.mem_powerset] at hT
    by_cases hKT : K ⊆ T
    · simp only [hKT, if_true]
      congr 1
      · exact Finset.prod_const _
      · rw [Finset.prod_congr rfl (g := fun _ => (1 - q : ℝ)) (fun i hi => by
          have : i ∉ K := fun hiK => (Finset.mem_sdiff.1 hi).2 (hKT hiK)
          simp [this]), Finset.prod_const]
    · simp only [hKT, if_false]
      obtain ⟨i, hiK, hiT⟩ : ∃ i ∈ K, i ∉ T := by
        by_contra hc
        exact hKT (fun i hi => by by_contra h2; exact hc ⟨i, hi, h2⟩)
      rw [Finset.prod_eq_zero (i := i) (Finset.mem_sdiff.2 ⟨hK hiK, hiT⟩) (by simp [hiK]), mul_zero]
  rw [← Finset.sum_congr rfl hR, ← h, hL]

/-- Averaging a family of sums against the binomial weights: an index `z` survives exactly when
the whole of `K z` is sampled, which happens with weight `q ^ #(K z)`. -/
private theorem sum_powerset_weight_mul {α β : Type*} [DecidableEq α] [Fintype α]
    (q : ℝ) (B : Finset β) (K : β → Finset α) (c : β → ℝ) :
    ∑ T ∈ (Finset.univ : Finset α).powerset, (q ^ T.card * (1 - q) ^ (Finset.univ \ T).card) *
        (∑ z ∈ B.filter (fun z => K z ⊆ T), c z)
      = ∑ z ∈ B, c z * q ^ (K z).card := by
  have h1 : ∀ T ∈ (Finset.univ : Finset α).powerset,
      (q ^ T.card * (1 - q) ^ (Finset.univ \ T).card) * (∑ z ∈ B.filter (fun z => K z ⊆ T), c z)
        = ∑ z ∈ B,
            (if K z ⊆ T then q ^ T.card * (1 - q) ^ (Finset.univ \ T).card else 0) * c z := by
    intro T _
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    by_cases h : K z ⊆ T <;> simp [h]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [← Finset.sum_mul, sum_powerset_weight_eq q Finset.univ (K z) (Finset.subset_univ _),
    mul_comm]

omit [Fintype κ] in
/-- Janson's first inequality applied to the sub-family indexed by a `Finset T`: the events
outside `T` are simply dropped, which can only increase the probability of containing none. -/
private theorem prob_none_le_subfamily [Countable ι] [DecidableEq κ] (p : I) (S : κ → Set ι)
    (E : Finset (κ × κ)) (hE : ∀ i j, i ≠ j → (i, j) ∉ E → Disjoint (S i) (S j))
    (T : Finset κ) :
    (setBernoulli Set.univ p {R : Set ι | ∀ i, ¬ S i ⊆ R}).toReal
      ≤ Real.exp (-(∑ i ∈ T, (setBernoulli Set.univ p {R : Set ι | S i ⊆ R}).toReal)
        + (∑ z ∈ E.filter (fun z : κ × κ => z.1 ∈ T ∧ z.2 ∈ T),
            (setBernoulli Set.univ p {R : Set ι | S z.1 ∪ S z.2 ⊆ R}).toReal) / 2) := by
  have hfinj : Function.Injective
      (fun z : {x // x ∈ T} × {x // x ∈ T} => ((z.1 : κ), (z.2 : κ))) := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h ⊢
    exact h
  have hErestr : ∀ i j : {x // x ∈ T}, i ≠ j →
      (i, j) ∉ (E.filter (fun z : κ × κ => z.1 ∈ T ∧ z.2 ∈ T)).preimage
        (fun z : {x // x ∈ T} × {x // x ∈ T} => ((z.1 : κ), (z.2 : κ))) hfinj.injOn →
      Disjoint (S i.1) (S j.1) := by
    intro i j hij hnot
    have hne : (i : κ) ≠ (j : κ) := fun h => hij (Subtype.ext h)
    refine hE _ _ hne (fun hmem => hnot ?_)
    exact Finset.mem_preimage.2 (Finset.mem_filter.2 ⟨hmem, i.2, j.2⟩)
  have h2 := janson_prob_none_le p (fun i : {x // x ∈ T} => S i.1) _ hErestr
  have hmu : jansonMu p (fun i : {x // x ∈ T} => S i.1)
      = ∑ i ∈ T, (setBernoulli Set.univ p {R : Set ι | S i ⊆ R}).toReal :=
    Finset.sum_coe_sort T
      (fun i : κ => (setBernoulli Set.univ p {R : Set ι | S i ⊆ R}).toReal)
  have hdel : jansonDelta p (fun i : {x // x ∈ T} => S i.1)
      ((E.filter (fun z : κ × κ => z.1 ∈ T ∧ z.2 ∈ T)).preimage
        (fun z : {x // x ∈ T} × {x // x ∈ T} => ((z.1 : κ), (z.2 : κ))) hfinj.injOn)
      = ∑ z ∈ E.filter (fun z : κ × κ => z.1 ∈ T ∧ z.2 ∈ T),
          (setBernoulli Set.univ p {R : Set ι | S z.1 ∪ S z.2 ⊆ R}).toReal := by
    rw [jansonDelta]
    refine Finset.sum_preimage _ _ _
      (fun z : κ × κ => (setBernoulli Set.univ p {R : Set ι | S z.1 ∪ S z.2 ⊆ R}).toReal) ?_
    intro x hx hxr
    exact absurd
      ⟨(⟨x.1, (Finset.mem_filter.1 hx).2.1⟩, ⟨x.2, (Finset.mem_filter.1 hx).2.2⟩), rfl⟩ hxr
  rw [hmu, hdel] at h2
  refine le_trans ?_ h2
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun R hR i => hR i.1))

/-- **Janson's inequality II** (Zhao, Theorem 8.1.8): in the regime `Δ ≥ μ`, where the first
inequality says nothing, the probability of containing none of the `S i` is at most
`exp (-μ² / (2Δ))`.

Proved from the first inequality by applying it to a random subsample of the events. -/
theorem janson_prob_none_le_of_mu_le [Countable ι] (p : I) (S : κ → Set ι) (D : Finset (κ × κ))
    (hD : ∀ i j, i ≠ j → (i, j) ∉ D → Disjoint (S i) (S j))
    (hΔ : jansonMu p S ≤ jansonDelta p S D) (hΔ0 : 0 < jansonDelta p S D) :
    (setBernoulli Set.univ p {R : Set ι | ∀ i, ¬ S i ⊆ R}).toReal
      ≤ Real.exp (-(jansonMu p S) ^ 2 / (2 * jansonDelta p S D)) := by
  let _ : DecidableEq κ := (Fintype.equivFin κ).decidableEq
  -- `q`, the sampling probability, and the off-diagonal part `E` of the dependency set.
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = jansonMu p S / jansonDelta p S D := ⟨_, rfl⟩
  obtain ⟨Lam, hLam⟩ : ∃ x : ℝ, x = ∑ z ∈ D.filter (fun z : κ × κ => z.1 ≠ z.2),
      (setBernoulli Set.univ p {R : Set ι | S z.1 ∪ S z.2 ⊆ R}).toReal := ⟨_, rfl⟩
  have hμ0 : 0 ≤ jansonMu p S := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hq0 : 0 ≤ q := hq ▸ div_nonneg hμ0 hΔ0.le
  have hq1 : q ≤ 1 := hq ▸ (div_le_one hΔ0).2 hΔ
  have hE : ∀ i j, i ≠ j → (i, j) ∉ D.filter (fun z : κ × κ => z.1 ≠ z.2) →
      Disjoint (S i) (S j) := fun i j hij hnot =>
    hD i j hij fun hmem => hnot (Finset.mem_filter.2 ⟨hmem, hij⟩)
  have hLamΔ : Lam ≤ jansonDelta p S D := hLam ▸
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => ENNReal.toReal_nonneg)
  -- The binomial weights, and the exponent attached to the sub-family indexed by `T`.
  obtain ⟨W, hW⟩ : ∃ W : Finset κ → ℝ,
      ∀ T : Finset κ, W T = q ^ T.card * (1 - q) ^ ((Finset.univ : Finset κ) \ T).card :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : Finset κ → ℝ, ∀ T : Finset κ, F T =
      -(∑ i ∈ T, (setBernoulli Set.univ p {R : Set ι | S i ⊆ R}).toReal)
        + (∑ z ∈ (D.filter (fun z : κ × κ => z.1 ≠ z.2)).filter
              (fun z : κ × κ => z.1 ∈ T ∧ z.2 ∈ T),
            (setBernoulli Set.univ p {R : Set ι | S z.1 ∪ S z.2 ⊆ R}).toReal) / 2 :=
    ⟨_, fun _ => rfl⟩
  have hWnn : ∀ T : Finset κ, 0 ≤ W T := fun T => by
    rw [hW]; exact mul_nonneg (pow_nonneg hq0 _) (pow_nonneg (by linarith) _)
  have hWsum : ∑ T ∈ (Finset.univ : Finset κ).powerset, W T = 1 := by
    have h := sum_powerset_weight_eq q (Finset.univ : Finset κ) ∅ (Finset.empty_subset _)
    simp only [Finset.empty_subset, if_true, Finset.card_empty, pow_zero] at h
    simpa only [hW] using h
  have hWmu : ∑ T ∈ (Finset.univ : Finset κ).powerset,
      W T * (∑ i ∈ T, (setBernoulli Set.univ p {R : Set ι | S i ⊆ R}).toReal)
      = q * jansonMu p S := by
    have h := sum_powerset_weight_mul (α := κ) q (Finset.univ : Finset κ)
      (fun i : κ => ({i} : Finset κ))
      (fun i : κ => (setBernoulli Set.univ p {R : Set ι | S i ⊆ R}).toReal)
    have hfil : ∀ T : Finset κ,
        (Finset.univ : Finset κ).filter (fun i : κ => ({i} : Finset κ) ⊆ T) = T := by
      intro T; ext i; simp [Finset.singleton_subset_iff]
    simp only [hfil] at h
    rw [show (∑ T ∈ (Finset.univ : Finset κ).powerset,
        W T * (∑ i ∈ T, (setBernoulli Set.univ p {R : Set ι | S i ⊆ R}).toReal)) =
        ∑ T ∈ (Finset.univ : Finset κ).powerset,
          (q ^ T.card * (1 - q) ^ ((Finset.univ : Finset κ) \ T).card) *
            (∑ i ∈ T, (setBernoulli Set.univ p {R : Set ι | S i ⊆ R}).toReal) from
      Finset.sum_congr rfl fun T _ => by rw [hW]]
    rw [h, jansonMu, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Finset.card_singleton, pow_one, mul_comm]
  have hWdel : ∑ T ∈ (Finset.univ : Finset κ).powerset,
      W T * (∑ z ∈ (D.filter (fun z : κ × κ => z.1 ≠ z.2)).filter
              (fun z : κ × κ => z.1 ∈ T ∧ z.2 ∈ T),
            (setBernoulli Set.univ p {R : Set ι | S z.1 ∪ S z.2 ⊆ R}).toReal)
      = q ^ 2 * Lam := by
    have h := sum_powerset_weight_mul (α := κ) q (D.filter (fun z : κ × κ => z.1 ≠ z.2))
      (fun z : κ × κ => ({z.1, z.2} : Finset κ))
      (fun z : κ × κ => (setBernoulli Set.univ p {R : Set ι | S z.1 ∪ S z.2 ⊆ R}).toReal)
    have hfil : ∀ T : Finset κ,
        (D.filter (fun z : κ × κ => z.1 ≠ z.2)).filter
            (fun z : κ × κ => ({z.1, z.2} : Finset κ) ⊆ T)
          = (D.filter (fun z : κ × κ => z.1 ≠ z.2)).filter
            (fun z : κ × κ => z.1 ∈ T ∧ z.2 ∈ T) :=
      fun T => Finset.filter_congr fun z _ => by simp [Finset.insert_subset_iff]
    simp only [hfil] at h
    rw [show (∑ T ∈ (Finset.univ : Finset κ).powerset,
        W T * (∑ z ∈ (D.filter (fun z : κ × κ => z.1 ≠ z.2)).filter
              (fun z : κ × κ => z.1 ∈ T ∧ z.2 ∈ T),
            (setBernoulli Set.univ p {R : Set ι | S z.1 ∪ S z.2 ⊆ R}).toReal)) =
        ∑ T ∈ (Finset.univ : Finset κ).powerset,
          (q ^ T.card * (1 - q) ^ ((Finset.univ : Finset κ) \ T).card) *
            (∑ z ∈ (D.filter (fun z : κ × κ => z.1 ≠ z.2)).filter
              (fun z : κ × κ => z.1 ∈ T ∧ z.2 ∈ T),
            (setBernoulli Set.univ p {R : Set ι | S z.1 ∪ S z.2 ⊆ R}).toReal) from
      Finset.sum_congr rfl fun T _ => by rw [hW]]
    rw [h, hLam, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z hz => by
      rw [Finset.card_pair (Finset.mem_filter.1 hz).2, mul_comm]
  -- The weighted average of the sub-family exponents.
  have hFsum : ∑ T ∈ (Finset.univ : Finset κ).powerset, W T * F T
      = -(q * jansonMu p S) + q ^ 2 * Lam / 2 := by
    rw [Finset.sum_congr rfl (g := fun T =>
      -(W T * (∑ i ∈ T, (setBernoulli Set.univ p {R : Set ι | S i ⊆ R}).toReal))
        + W T * (∑ z ∈ (D.filter (fun z : κ × κ => z.1 ≠ z.2)).filter
              (fun z : κ × κ => z.1 ∈ T ∧ z.2 ∈ T),
            (setBernoulli Set.univ p {R : Set ι | S z.1 ∪ S z.2 ⊆ R}).toReal) / 2)
      (fun T _ => by rw [hF]; ring)]
    rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_neg_distrib, hWmu, hWdel]
  -- Some `T` does at least as well as the average.
  obtain ⟨T, hTmem, hT⟩ : ∃ T ∈ (Finset.univ : Finset κ).powerset,
      F T ≤ -(q * jansonMu p S) + q ^ 2 * Lam / 2 := by
    by_contra hcon
    have hlt : ∀ T ∈ (Finset.univ : Finset κ).powerset,
        -(q * jansonMu p S) + q ^ 2 * Lam / 2 < F T := by
      intro T hT
      by_contra h2
      exact hcon ⟨T, hT, not_lt.1 h2⟩
    obtain ⟨T₀, hT₀mem, hT₀ne⟩ : ∃ T ∈ (Finset.univ : Finset κ).powerset, W T ≠ 0 :=
      Finset.exists_ne_zero_of_sum_ne_zero (by rw [hWsum]; exact one_ne_zero)
    have hlt2 : ∑ T ∈ (Finset.univ : Finset κ).powerset,
        W T * (-(q * jansonMu p S) + q ^ 2 * Lam / 2)
        < ∑ T ∈ (Finset.univ : Finset κ).powerset, W T * F T :=
      Finset.sum_lt_sum (fun T hT => mul_le_mul_of_nonneg_left (hlt T hT).le (hWnn T))
        ⟨T₀, hT₀mem, mul_lt_mul_of_pos_left (hlt T₀ hT₀mem)
          (lt_of_le_of_ne (hWnn T₀) (Ne.symm hT₀ne))⟩
    rw [← Finset.sum_mul, hWsum, one_mul, hFsum] at hlt2
    exact lt_irrefl _ hlt2
  -- Janson I for that sub-family, then the choice `q = μ / Δ`.
  have hmain := prob_none_le_subfamily p S (D.filter (fun z : κ × κ => z.1 ≠ z.2)) hE T
  rw [← hF T] at hmain
  refine le_trans hmain (Real.exp_le_exp.2 (le_trans hT ?_))
  rw [hq]
  have hΔne : jansonDelta p S D ≠ 0 := ne_of_gt hΔ0
  have h1 : jansonMu p S / jansonDelta p S D * jansonMu p S
      = 2 * (jansonMu p S ^ 2 / (2 * jansonDelta p S D)) := by
    field_simp
  have h2 : (jansonMu p S / jansonDelta p S D) ^ 2 * jansonDelta p S D / 2
      = jansonMu p S ^ 2 / (2 * jansonDelta p S D) := by
    field_simp
  have h3 : (jansonMu p S / jansonDelta p S D) ^ 2 * Lam / 2
      ≤ (jansonMu p S / jansonDelta p S D) ^ 2 * jansonDelta p S D / 2 := by
    gcongr
  have h4 : -(jansonMu p S) ^ 2 / (2 * jansonDelta p S D)
      = -(jansonMu p S ^ 2 / (2 * jansonDelta p S D)) := by ring
  linarith

section LowerTail

/-- **The dense regime of the triangle-free probability** (Zhao, Theorem 8.1.10's second half),
from Janson's second inequality.

Where `binomialRandom_no_triangle_le` is useful for `Δ < μ`, Janson II covers `μ ≤ Δ`, which for
the triangle family is exactly `1 ≤ 3 (n - 3) p²` — the `p ≫ n^{-1/2}` regime.  There

    μ² / (2Δ) = binom(n,3) p / (6 (n - 3)),

using `jansonDelta_triangleFamily`'s exact value; an upper bound on `Δ` would be useless here,
since `Δ` sits in a denominator and in the hypothesis.

Since `binom(n,3)/(n-3) = n(n-1)(n-2)/(6(n-3))` grows like `n²/6`, the exponent is of order
`n²p`, which is the `exp (-Θ(n²p))` the source reports — and, as Remark 8.1.9 notes, better than
the first inequality can give once `p ≫ n^{-1/2}`.

`4 ≤ n` keeps `n - 3` positive; `p > 0` is not assumed because the regime hypothesis forces
it. -/
theorem binomialRandom_no_triangle_le_of_one_le (n : ℕ) (hn : 4 ≤ n) (p : I)
    (hp : 1 ≤ 3 * ((n : ℝ) - 3) * (p : ℝ) ^ 2) :
    (SimpleGraph.binomialRandom (Fin n) p).real
        {G : SimpleGraph (Fin n) | ∀ T : {T : Finset (Fin n) // T.card = 3},
          ¬ (↑(offDiagPairs (T : Finset (Fin n))) ⊆ G.edgeSet)}
      ≤ Real.exp (-((n.choose 3 : ℝ) * (p : ℝ) / (6 * ((n : ℝ) - 3)))) := by
  -- Triples meeting in at most one vertex span disjoint edge sets: a shared edge would put two
  -- shared vertices in the intersection, and `offDiagPairs` of a set of size `≤ 1` is empty.
  have hD := disjoint_offDiagPairs_of_notMem_triangleDependency (n := n)
  -- Positivity of the three factors that the cancellation divides by.
  have h3n : 3 ≤ n := by omega
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn3 : (0 : ℝ) < (n : ℝ) - 3 := by linarith
  have hC : (0 : ℝ) < (n.choose 3 : ℝ) := by
    exact_mod_cast Nat.choose_pos h3n
  -- The regime hypothesis forces `p > 0`: at `p = 0` it reads `1 ≤ 0`.
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    rcases eq_or_lt_of_le p.2.1 with h | h
    · rw [← h] at hp; norm_num at hp
    · exact h
  -- `Δ`'s exact value carries a `Nat` subtraction; `4 ≤ n` makes it the real one.
  have hcast : ((3 * n.choose 3 * (n - 3) : ℕ) : ℝ)
      = 3 * (n.choose 3 : ℝ) * ((n : ℝ) - 3) := by
    push_cast [Nat.cast_sub h3n]
    ring
  have hDpos : (0 : ℝ) < 3 * (n.choose 3 : ℝ) * ((n : ℝ) - 3) * (p : ℝ) ^ 5 :=
    mul_pos (mul_pos (mul_pos (by norm_num) hC) hn3) (pow_pos hp0 5)
  -- `μ ≤ Δ` is `hp` multiplied through by `binom(n,3) p³ ≥ 0`.
  have hΔ : jansonMu p (fun T : {T : Finset (Fin n) // T.card = 3} =>
        (↑(offDiagPairs (T : Finset (Fin n))) : Set (Sym2 (Fin n))))
      ≤ jansonDelta p (fun T : {T : Finset (Fin n) // T.card = 3} =>
          (↑(offDiagPairs (T : Finset (Fin n))) : Set (Sym2 (Fin n))))
        (triangleDependency n) := by
    rw [jansonMu_triangleFamily, jansonDelta_triangleFamily, hcast]
    have hmul := mul_le_mul_of_nonneg_right hp
      (show (0 : ℝ) ≤ (n.choose 3 : ℝ) * (p : ℝ) ^ 3 by positivity)
    nlinarith only [hmul]
  have hΔ0 : (0 : ℝ) < jansonDelta p (fun T : {T : Finset (Fin n) // T.card = 3} =>
      (↑(offDiagPairs (T : Finset (Fin n))) : Set (Sym2 (Fin n)))) (triangleDependency n) := by
    rw [jansonDelta_triangleFamily, hcast]
    exact hDpos
  -- Janson's second inequality on the triangle family, with `μ` and `Δ` substituted exactly.
  have hmain := janson_prob_none_le_of_mu_le p
    (fun T : {T : Finset (Fin n) // T.card = 3} =>
      (↑(offDiagPairs (T : Finset (Fin n))) : Set (Sym2 (Fin n))))
    (triangleDependency n) hD hΔ hΔ0
  rw [jansonMu_triangleFamily, jansonDelta_triangleFamily, hcast] at hmain
  -- `μ² / (2Δ) = binom(n,3)² p⁶ / (6 binom(n,3) (n - 3) p⁵) = binom(n,3) p / (6 (n - 3))`.
  have hexp : -((n.choose 3 : ℝ) * (p : ℝ) ^ 3) ^ 2
        / (2 * (3 * (n.choose 3 : ℝ) * ((n : ℝ) - 3) * (p : ℝ) ^ 5))
      = -((n.choose 3 : ℝ) * (p : ℝ) / (6 * ((n : ℝ) - 3))) := by
    have hC' : (n.choose 3 : ℝ) ≠ 0 := ne_of_gt hC
    have hp' : (p : ℝ) ≠ 0 := ne_of_gt hp0
    have hn3' : (n : ℝ) - 3 ≠ 0 := ne_of_gt hn3
    field_simp
    ring
  rw [hexp] at hmain
  -- Cross from `G(n, p)` to `setBernoulli`; the triangle edge sets contain no loop.
  rw [measureReal_def, binomialRandom_setOf_forall_not_subset p
    (fun T : {T : Finset (Fin n) // T.card = 3} => offDiagPairs (T : Finset (Fin n)))
    fun _ _ he => not_isDiag_of_mem_offDiagPairs he]
  exact hmain

/-- The elementary bound `exp (-x) ≤ 1 - x + x ^ 2 / 2` for `x ≥ 0`.

It follows from `1 + x + x ^ 2 / 2 ≤ exp x` because
`(1 - x + x ^ 2 / 2) * (1 + x + x ^ 2 / 2) = 1 + x ^ 4 / 4 ≥ 1`. -/
theorem exp_neg_le_one_sub_add_sq_div_two {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have hA : (0 : ℝ) < 1 + x + x ^ 2 / 2 := by nlinarith [sq_nonneg x]
  have hexp : 1 + x + x ^ 2 / 2 ≤ Real.exp x := Real.quadratic_le_exp_of_nonneg hx
  have h1 : Real.exp (-x) * (1 + x + x ^ 2 / 2) ≤ Real.exp (-x) * Real.exp x :=
    mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
  have h2 : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith [sq_nonneg (x ^ 2), h1, h2, hA]

/-- The Chernoff step of Warnke's proof of Janson's third inequality (Zhao, Theorem 8.2.2).

Write `X` for `jansonCount S`, put `q = 1 - exp (-lam)` for `lam ≥ 0`, and thin the events of
Setup 8.1.1 by keeping each index independently with probability `q`.  The probability that the
thinned count vanishes is the moment generating function `𝔼 [exp (-lam * X)]`, which is bounded
by `exp (-q * μ + q ^ 2 * Δ / 2)`; Markov's inequality applied to it gives the bound below.

**The thinning is never a second measure.**  `κ` is a `Fintype`, so a thinned family is a
`Finset κ` and the `q`-average over thinnings is a *finite sum* against the weights
`q ^ #T * (1 - q) ^ #(U \ T)`, carried out entirely inside the existing `p`-space on `Set ι`.
What would otherwise be Fubini is finite additivity.  Two consequences worth knowing before
reading the proof:

* the `q ^ 2` on `Δ` comes from a negative-correlation step that needs no FKG — the increasing
  function is a single coordinate indicator, so pairing `T` with `insert j T` reduces it to the
  termwise monotonicity `P (insert j T) ≤ P T`;
* Markov is a finite disjoint partition `{X ≤ s} = ⋃ EV J` rather than an integral.  That set is
  genuinely measurable — each `EV J` is, and `measure_biUnion_finset` gives an *equality* — so
  the outer-measure hazard this file warns about is discharged, not sidestepped.  `[Countable ι]`
  is load-bearing for it, since Mathlib's `Measurable.subset` lives under `[Countable α]`.

An earlier draft of this docstring described a different route, in which the thinned family again
satisfies Setup 8.1.1 over the off-diagonal pairs of `D` and Janson's first inequality is applied
to it.  That is true as a remark but is not what the proof does, and it is not available as
stated: `janson_prob_none_le` requires its measure to be literally `setBernoulli Set.univ p'`,
which a product over two index types is not. -/
theorem janson_lower_tail_step_le [Countable ι] (p : I) (S : κ → Set ι) (D : Finset (κ × κ))
    (hD : ∀ i j, i ≠ j → (i, j) ∉ D → Disjoint (S i) (S j)) {lam s : ℝ} (hlam : 0 ≤ lam) :
    (setBernoulli Set.univ p {R : Set ι | jansonCount S R ≤ s}).toReal
      ≤ Real.exp (lam * s - (1 - Real.exp (-lam)) * jansonMu p S
          + (1 - Real.exp (-lam)) ^ 2 * jansonDelta p S D / 2) := by
  -- Write `q = 1 - exp (-lam)`, so `1 - q = exp (-lam) > 0`.  The thinning needs no second
  -- measure: `κ` is finite, so a thinned family is a `Finset κ` and the `q`-average over thinnings
  -- is the finite sum `Φ U = ∑ T ⊆ U, q ^ #T * (1 - q) ^ #(U \ T) * P T`, where `P T` is the
  -- probability that the random subset contains none of the `S j` with `j ∈ T`.  `Φ Finset.univ`
  -- is the moment generating function `𝔼 [exp (-lam * X)]`.
  classical
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = 1 - Real.exp (-lam) := ⟨_, rfl⟩
  have hq1 : 1 - q = Real.exp (-lam) := by rw [hqdef]; ring
  have hq1pos : (0 : ℝ) < 1 - q := by rw [hq1]; exact Real.exp_pos _
  have hq0 : (0 : ℝ) ≤ q := by
    have h := Real.exp_le_one_iff.2 (neg_nonpos.2 hlam)
    rw [hqdef]; linarith
  obtain ⟨a, ha⟩ : ∃ a : κ → ℝ,
      ∀ i, a i = (setBernoulli Set.univ p {R : Set ι | S i ⊆ R}).toReal := ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : κ → κ → ℝ,
      ∀ i j, b i j = (setBernoulli Set.univ p {R : Set ι | S i ∪ S j ⊆ R}).toReal :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Finset κ → ℝ, ∀ T : Finset κ,
      P T = (setBernoulli Set.univ p {R : Set ι | ∀ j ∈ T, ¬ S j ⊆ R}).toReal :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : Finset κ → ℝ, ∀ T : Finset κ,
      E T = ∑ z ∈ D.filter fun z => z.1 ∈ T ∧ z.2 ∈ T, b z.1 z.2 := ⟨_, fun _ => rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Finset κ → Finset κ → ℝ,
      ∀ U T : Finset κ, W U T = q ^ T.card * (1 - q) ^ (U \ T).card := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Finset κ → ℝ,
      ∀ U : Finset κ, Φ U = ∑ T ∈ U.powerset, W U T * P T := ⟨_, fun _ => rfl⟩
  have hb0 : ∀ i j, 0 ≤ b i j := fun i j => by rw [hb]; exact ENNReal.toReal_nonneg
  have hbs : ∀ i j, b j i = b i j := fun i j => by rw [hb, hb, Set.union_comm]
  have hP0 : ∀ T, 0 ≤ P T := fun T => by rw [hP]; exact ENNReal.toReal_nonneg
  have hPmono : ∀ T T' : Finset κ, T ⊆ T' → P T' ≤ P T := by
    intro T T' hsub
    rw [hP, hP]
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
    exact fun R hR j hj => hR j (hsub hj)
  have hW0 : ∀ U T : Finset κ, 0 ≤ W U T := fun U T => by
    rw [hW]; exact mul_nonneg (pow_nonneg hq0 _) (pow_nonneg hq1pos.le _)
  have hΦ0 : ∀ U : Finset κ, 0 ≤ Φ U := fun U => by
    rw [hΦ]; exact Finset.sum_nonneg fun T _ => mul_nonneg (hW0 _ _) (hP0 _)
  -- `P` is decreasing, so an index surviving the thinning is negatively correlated with it:
  -- pairing each `T` not containing `j` with `insert j T` compares the two sums termwise.
  have hcorr : ∀ (U : Finset κ) (j : κ), j ∈ U →
      ∑ T ∈ U.powerset, W U T * (if j ∈ T then P T else 0) ≤ q * Φ U := by
    intro U j hj
    obtain ⟨U', hU'⟩ : ∃ U' : Finset κ, U' = U.erase j := ⟨_, rfl⟩
    have hjU' : j ∉ U' := by rw [hU']; exact Finset.notMem_erase j U
    have hUeq : insert j U' = U := by rw [hU']; exact Finset.insert_erase hj
    obtain ⟨V, hV⟩ : ∃ V : Finset κ → ℝ,
        ∀ T : Finset κ, V T = q ^ T.card * (1 - q) ^ (U' \ T).card := ⟨_, fun _ => rfl⟩
    have hV0 : ∀ T, 0 ≤ V T := fun T => by
      rw [hV]; exact mul_nonneg (pow_nonneg hq0 _) (pow_nonneg hq1pos.le _)
    have hsplit : ∀ f : Finset κ → ℝ,
        ∑ T ∈ U.powerset, f T = (∑ T ∈ U'.powerset, f T) + ∑ T ∈ U'.powerset, f (insert j T) := by
      intro f
      rw [← hUeq]
      exact Finset.sum_powerset_insert hjU' f
    have hW1 : ∀ T ∈ U'.powerset, W U T = (1 - q) * V T := by
      intro T hT
      have hTsub : T ⊆ U' := Finset.mem_powerset.1 hT
      have hjT : j ∉ T := fun h => hjU' (hTsub h)
      have hcard : (U \ T).card = (U' \ T).card + 1 := by
        rw [← hUeq, Finset.insert_sdiff_of_notMem _ hjT,
          Finset.card_insert_of_notMem (fun h => hjU' (Finset.mem_sdiff.1 h).1)]
      rw [hW, hV, hcard, pow_succ]; ring
    have hW2 : ∀ T ∈ U'.powerset, W U (insert j T) = q * V T := by
      intro T hT
      have hTsub : T ⊆ U' := Finset.mem_powerset.1 hT
      have hjT : j ∉ T := fun h => hjU' (hTsub h)
      have hset : U \ insert j T = U' \ T := by
        rw [← hUeq]
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨hx, hx2⟩
          refine ⟨hx.resolve_left fun h => hx2 (Or.inl h), fun h => hx2 (Or.inr h)⟩
        · rintro ⟨hx, hx2⟩
          exact ⟨Or.inr hx, fun h => h.elim (fun hh => hjU' (hh ▸ hx)) hx2⟩
      rw [hW, hV, hset, Finset.card_insert_of_notMem hjT, pow_succ]; ring
    have hL : ∑ T ∈ U.powerset, W U T * (if j ∈ T then P T else 0)
        = q * ∑ T ∈ U'.powerset, V T * P (insert j T) := by
      rw [hsplit fun T => W U T * (if j ∈ T then P T else 0)]
      have h1 : ∀ T ∈ U'.powerset, W U T * (if j ∈ T then P T else 0) = 0 := by
        intro T hT
        have : j ∉ T := fun h => hjU' (Finset.mem_powerset.1 hT h)
        simp [this]
      rw [Finset.sum_congr rfl h1, Finset.sum_const_zero, zero_add, Finset.mul_sum]
      refine Finset.sum_congr rfl fun T hT => ?_
      rw [hW2 T hT]
      simp [Finset.mem_insert_self j T]
      ring
    have hΦeq : Φ U = (1 - q) * (∑ T ∈ U'.powerset, V T * P T)
        + q * ∑ T ∈ U'.powerset, V T * P (insert j T) := by
      rw [hΦ, hsplit fun T => W U T * P T, Finset.mul_sum, Finset.mul_sum]
      refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun T hT => ?_)
        (Finset.sum_congr rfl fun T hT => ?_)
      · rw [hW1 T hT]; ring
      · rw [hW2 T hT]; ring
    have hkey : ∑ T ∈ U'.powerset, V T * P (insert j T) ≤ ∑ T ∈ U'.powerset, V T * P T :=
      Finset.sum_le_sum fun T _ =>
        mul_le_mul_of_nonneg_left (hPmono T (insert j T) (Finset.subset_insert j T)) (hV0 T)
    rw [hL, hΦeq]
    nlinarith [mul_nonneg (mul_nonneg hq0 hq1pos.le) (sub_nonneg.2 hkey)]
  -- The weighted Boppana–Spencer induction.
  have hΦmain : ∀ U : Finset κ, Φ U ≤ Real.exp (-q * ∑ j ∈ U, a j + q ^ 2 * E U / 2) := by
    intro U
    refine Finset.induction_on U ?_ ?_
    · have h1 : {R : Set ι | ∀ j ∈ (∅ : Finset κ), ¬ S j ⊆ R} = Set.univ := by simp
      have hΦe : Φ ∅ = P ∅ := by
        rw [hΦ, Finset.powerset_empty, Finset.sum_singleton, hW]
        simp
      rw [hΦe, hP, h1, hE]
      simp
    · intro i U hiU ih
      obtain ⟨K, hK⟩ : ∃ K : Finset κ, K = U.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D := ⟨_, rfl⟩
      have hKU : K ⊆ U := by rw [hK]; exact Finset.filter_subset _ _
      have hPstep : ∀ T ∈ U.powerset,
          P (insert i T) ≤ (1 - a i + ∑ j ∈ K, (if j ∈ T then b i j else 0)) * P T := by
        intro T hT
        have hTU : T ⊆ U := Finset.mem_powerset.1 hT
        have hiT : i ∉ T := fun h => hiU (hTU h)
        have hsub : T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D) ⊆ T := Finset.filter_subset _ _
        have hindep : ∀ j ∈ T, j ∉ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D) →
            Disjoint (S i) (S j) := by
          intro j hjT hjn
          have hij : i ≠ j := by rintro rfl; exact hiT hjT
          have hnot : ¬ ((i, j) ∈ D ∧ (j, i) ∈ D) := fun h => hjn (Finset.mem_filter.2 ⟨hjT, h⟩)
          rcases not_and_or.1 hnot with h | h
          · exact hD i j hij h
          · exact (hD j i hij.symm h).symm
        have hstep := janson_prob_none_step_le p S i T
          (T.filter fun j => (i, j) ∈ D ∧ (j, i) ∈ D) hiT hsub hindep
        have hins : {R : Set ι | ∀ j ∈ insert i T, ¬ S j ⊆ R}
            = {R : Set ι | ¬ S i ⊆ R ∧ ∀ j ∈ T, ¬ S j ⊆ R} := by ext R; simp
        have hsum : ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j
            = ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D),
                (setBernoulli Set.univ p {R : Set ι | S i ∪ S j ⊆ R}).toReal :=
          Finset.sum_congr rfl fun j _ => hb i j
        have hfilter : ∑ j ∈ K, (if j ∈ T then b i j else 0)
            = ∑ j ∈ T.filter (fun j => (i, j) ∈ D ∧ (j, i) ∈ D), b i j := by
          rw [hK, ← Finset.sum_filter]
          refine Finset.sum_congr ?_ fun _ _ => rfl
          ext j
          simp only [Finset.mem_filter]
          exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hTU h.1, h.2⟩, h.1⟩⟩
        rw [hfilter, hP, hins, hP, ha, hsum]
        exact hstep
      have hexpand : Φ (insert i U)
          = ∑ T ∈ U.powerset, W U T * ((1 - q) * P T + q * P (insert i T)) := by
        rw [hΦ, Finset.sum_powerset_insert hiU, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun T hT => ?_
        have hTU : T ⊆ U := Finset.mem_powerset.1 hT
        have hiT : i ∉ T := fun h => hiU (hTU h)
        have hc1 : W (insert i U) T = (1 - q) * W U T := by
          rw [hW, hW, Finset.insert_sdiff_of_notMem _ hiT,
            Finset.card_insert_of_notMem (fun h => hiU (Finset.mem_sdiff.1 h).1), pow_succ]
          ring
        have hc2 : W (insert i U) (insert i T) = q * W U T := by
          have hset : insert i U \ insert i T = U \ T := by
            ext x
            simp only [Finset.mem_sdiff, Finset.mem_insert]
            constructor
            · rintro ⟨hx, hx2⟩
              exact ⟨hx.resolve_left fun h => hx2 (Or.inl h), fun h => hx2 (Or.inr h)⟩
            · rintro ⟨hx, hx2⟩
              exact ⟨Or.inr hx, fun h => h.elim (fun hh => hiU (hh ▸ hx)) hx2⟩
          rw [hW, hW, hset, Finset.card_insert_of_notMem hiT, pow_succ]
          ring
        rw [hc1, hc2]; ring
      have hbound : Φ (insert i U) ≤ (1 - q * a i + q ^ 2 * ∑ j ∈ K, b i j) * Φ U := by
        have h1 : Φ (insert i U)
            ≤ ∑ T ∈ U.powerset, W U T * ((1 - q * a i) * P T
                + q * ((∑ j ∈ K, (if j ∈ T then b i j else 0)) * P T)) := by
          rw [hexpand]
          refine Finset.sum_le_sum fun T hT => ?_
          refine mul_le_mul_of_nonneg_left ?_ (hW0 U T)
          have h2 := mul_le_mul_of_nonneg_left (hPstep T hT) hq0
          nlinarith [h2]
        have hswap : ∑ T ∈ U.powerset, W U T * ((1 - q * a i) * P T
              + q * ((∑ j ∈ K, (if j ∈ T then b i j else 0)) * P T))
            = (1 - q * a i) * Φ U
              + q * ∑ j ∈ K, b i j * ∑ T ∈ U.powerset, W U T * (if j ∈ T then P T else 0) := by
          have e1 : ∀ T : Finset κ, W U T * ((1 - q * a i) * P T
                + q * ((∑ j ∈ K, (if j ∈ T then b i j else 0)) * P T))
              = (1 - q * a i) * (W U T * P T)
                + q * ∑ j ∈ K, (if j ∈ T then b i j else 0) * (W U T * P T) := by
            intro T
            rw [← Finset.sum_mul]
            ring
          rw [Finset.sum_congr rfl (fun T _ => e1 T), Finset.sum_add_distrib, ← Finset.mul_sum,
            ← hΦ, ← Finset.mul_sum, Finset.sum_comm]
          congr 2
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun T _ => ?_
          by_cases h : j ∈ T <;> simp [h]
        have h3 : ∑ j ∈ K, b i j * ∑ T ∈ U.powerset, W U T * (if j ∈ T then P T else 0)
            ≤ (∑ j ∈ K, b i j) * (q * Φ U) := by
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun j hj =>
            mul_le_mul_of_nonneg_left (hcorr U j (hKU hj)) (hb0 i j)
        have h4 := mul_le_mul_of_nonneg_left h3 hq0
        calc Φ (insert i U)
            ≤ ∑ T ∈ U.powerset, W U T * ((1 - q * a i) * P T
                + q * ((∑ j ∈ K, (if j ∈ T then b i j else 0)) * P T)) := h1
          _ = (1 - q * a i) * Φ U
              + q * ∑ j ∈ K, b i j * ∑ T ∈ U.powerset, W U T * (if j ∈ T then P T else 0) := hswap
          _ ≤ (1 - q * a i + q ^ 2 * ∑ j ∈ K, b i j) * Φ U := by nlinarith [h4]
      have hEineq : E U + 2 * ∑ j ∈ K, b i j ≤ E (insert i U) := by
        rw [hK, hE, hE]
        exact sum_filter_insert_le D b hb0 hbs i U hiU
      calc Φ (insert i U)
          ≤ (1 - q * a i + q ^ 2 * ∑ j ∈ K, b i j) * Φ U := hbound
        _ ≤ Real.exp (-q * a i + q ^ 2 * ∑ j ∈ K, b i j) * Φ U := by
            refine mul_le_mul_of_nonneg_right ?_ (hΦ0 U)
            have := Real.add_one_le_exp (-q * a i + q ^ 2 * ∑ j ∈ K, b i j)
            linarith
        _ ≤ Real.exp (-q * a i + q ^ 2 * ∑ j ∈ K, b i j)
              * Real.exp (-q * ∑ j ∈ U, a j + q ^ 2 * E U / 2) :=
            mul_le_mul_of_nonneg_left ih (Real.exp_nonneg _)
        _ = Real.exp ((-q * a i + q ^ 2 * ∑ j ∈ K, b i j)
              + (-q * ∑ j ∈ U, a j + q ^ 2 * E U / 2)) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (-q * ∑ j ∈ insert i U, a j + q ^ 2 * E (insert i U) / 2) := by
            rw [Finset.sum_insert hiU]
            refine Real.exp_le_exp.2 ?_
            have h5 := mul_le_mul_of_nonneg_left hEineq (sq_nonneg q)
            nlinarith [h5]
  -- Markov's inequality, as a partition rather than an integral: `EV J` is the event that the
  -- sets contained in the random subset are exactly those indexed by `J`, and on it the thinning
  -- misses `J` with probability `(1 - q) ^ #J`, which is at least `exp (-lam * s)` once `#J ≤ s`.
  obtain ⟨EV, hEV⟩ : ∃ EV : Finset κ → Set (Set ι),
      ∀ J : Finset κ, EV J = {R : Set ι | ∀ j, (S j ⊆ R ↔ j ∈ J)} := ⟨_, fun _ => rfl⟩
  obtain ⟨e, he⟩ : ∃ e : Finset κ → ℝ,
      ∀ J : Finset κ, e J = (setBernoulli Set.univ p (EV J)).toReal := ⟨_, fun _ => rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : Finset (Finset κ),
      F = Finset.univ.filter fun J : Finset κ => (J.card : ℝ) ≤ s := ⟨_, rfl⟩
  have he0 : ∀ J, 0 ≤ e J := fun J => by rw [he]; exact ENNReal.toReal_nonneg
  have hmemF : ∀ J : Finset κ, J ∈ F ↔ (J.card : ℝ) ≤ s := by
    intro J; rw [hF]; simp
  have hmeasSub : ∀ t : Set ι, MeasurableSet {R : Set ι | t ⊆ R} := fun t =>
    measurableSet_setOfPred.2 (Measurable.subset measurable_const measurable_id)
  have hEVmeas : ∀ J : Finset κ, MeasurableSet (EV J) := by
    intro J
    have heq : EV J = (⋂ j ∈ (J : Set κ), {R : Set ι | S j ⊆ R})
        ∩ ⋂ j ∈ ((J : Set κ)ᶜ), {R : Set ι | S j ⊆ R}ᶜ := by
      rw [hEV]
      ext R
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff, Finset.mem_coe]
      constructor
      · intro h
        exact ⟨fun j hj => (h j).2 hj, fun j hj hR => hj ((h j).1 hR)⟩
      · rintro ⟨h1, h2⟩ j
        exact ⟨fun hR => not_not.1 fun hj => h2 j hj hR, fun hj => h1 j hj⟩
    rw [heq]
    exact (MeasurableSet.biInter (Set.to_countable _) fun j _ => hmeasSub (S j)).inter
      (MeasurableSet.biInter (Set.to_countable _) fun j _ => (hmeasSub (S j)).compl)
  have hEVdisj : ∀ J J' : Finset κ, J ≠ J' → Disjoint (EV J) (EV J') := by
    intro J J' hne
    rw [Set.disjoint_left]
    intro R hR hR'
    rw [hEV] at hR hR'
    exact hne (Finset.ext fun j => (hR j).symm.trans (hR' j))
  have hsumE : ∀ G : Finset (Finset κ),
      ∑ J ∈ G, e J = (setBernoulli Set.univ p (⋃ J ∈ G, EV J)).toReal := by
    intro G
    rw [measure_biUnion_finset (fun J _ J' _ hne => hEVdisj J J' hne) fun J _ => hEVmeas J,
      ENNReal.toReal_sum fun J _ => measure_ne_top _ _]
    exact Finset.sum_congr rfl fun J _ => he J
  have hAeq : {R : Set ι | jansonCount S R ≤ s} = ⋃ J ∈ F, EV J := by
    ext R
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro hR
      refine ⟨Finset.univ.filter fun j => S j ⊆ R, ?_, ?_⟩
      · rw [hmemF]
        have hcoe : ({i | S i ⊆ R} : Set κ) = ↑(Finset.univ.filter fun j => S j ⊆ R) := by
          ext j; simp
        have h2 : jansonCount S R ≤ s := hR
        simp only [jansonCount, hcoe, Set.ncard_coe_finset] at h2
        exact h2
      · rw [hEV]; intro j; simp
    · rintro ⟨J, hJ, hRJ⟩
      rw [hEV] at hRJ
      have hcoe : ({i | S i ⊆ R} : Set κ) = ↑J := by
        ext j; simpa using hRJ j
      show jansonCount S R ≤ s
      simp only [jansonCount, hcoe, Set.ncard_coe_finset]
      exact (hmemF J).1 hJ
  have hPge : ∀ T : Finset κ, ∑ J ∈ F.filter (fun J => Disjoint J T), e J ≤ P T := by
    intro T
    rw [hsumE, hP]
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
    intro R hR
    simp only [Set.mem_iUnion, exists_prop] at hR
    obtain ⟨J, hJ, hRJ⟩ := hR
    rw [hEV] at hRJ
    intro j hj hSj
    exact Finset.disjoint_left.1 (Finset.mem_filter.1 hJ).2 ((hRJ j).1 hSj) hj
  -- The `K = ∅` case of `sum_powerset_weight_eq`; `∅ ⊆ t` collapses the guard.
  have hbinom : ∀ u : Finset κ, ∑ t ∈ u.powerset, q ^ t.card * (1 - q) ^ (u \ t).card = 1 := by
    intro u
    simpa using sum_powerset_weight_eq q u ∅ (Finset.empty_subset u)
  have hWsum : ∀ J : Finset κ,
      ∑ T ∈ (Finset.univ : Finset κ).powerset, (if Disjoint J T then W Finset.univ T else 0)
        = (1 - q) ^ J.card := by
    intro J
    have hset : ((Finset.univ : Finset κ).powerset.filter fun T => Disjoint J T) = Jᶜ.powerset := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
      constructor
      · exact fun h x hx => Finset.mem_compl.2 fun hxJ => Finset.disjoint_left.1 h hxJ hx
      · exact fun h => Finset.disjoint_left.2 fun x hxJ hxT => Finset.mem_compl.1 (h hxT) hxJ
    have hcard : ∀ T ∈ Jᶜ.powerset, (Finset.univ \ T).card = (Jᶜ \ T).card + J.card := by
      intro T hT
      have hTc : T ⊆ Jᶜ := Finset.mem_powerset.1 hT
      have hun : Finset.univ \ T = (Jᶜ \ T) ∪ J := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ, Finset.mem_compl, true_and]
        constructor
        · intro hx
          by_cases hxJ : x ∈ J
          · exact Or.inr hxJ
          · exact Or.inl ⟨hxJ, hx⟩
        · rintro (⟨-, h2⟩ | h)
          · exact h2
          · exact fun hxT => Finset.mem_compl.1 (hTc hxT) h
      have hdisj : Disjoint (Jᶜ \ T) J :=
        Finset.disjoint_left.2 fun x hx => Finset.mem_compl.1 (Finset.mem_sdiff.1 hx).1
      rw [hun, Finset.card_union_of_disjoint hdisj]
    rw [← Finset.sum_filter, hset]
    calc ∑ T ∈ Jᶜ.powerset, W Finset.univ T
        = ∑ T ∈ Jᶜ.powerset, q ^ T.card * (1 - q) ^ (Jᶜ \ T).card * (1 - q) ^ J.card := by
          refine Finset.sum_congr rfl fun T hT => ?_
          rw [hW, hcard T hT, pow_add]; ring
      _ = (∑ T ∈ Jᶜ.powerset, q ^ T.card * (1 - q) ^ (Jᶜ \ T).card) * (1 - q) ^ J.card :=
          (Finset.sum_mul _ _ _).symm
      _ = (1 - q) ^ J.card := by rw [hbinom, one_mul]
  have hPart1 : (setBernoulli Set.univ p {R : Set ι | jansonCount S R ≤ s}).toReal
      ≤ Real.exp (lam * s) * Φ Finset.univ := by
    have hexpJ : ∀ J ∈ F, Real.exp (-(lam * s)) ≤ (1 - q) ^ J.card := by
      intro J hJ
      rw [hq1, ← Real.exp_nat_mul]
      refine Real.exp_le_exp.2 ?_
      have hcard := (hmemF J).1 hJ
      nlinarith [hlam]
    have hkey : Real.exp (-(lam * s)) * (∑ J ∈ F, e J) ≤ Φ Finset.univ := by
      calc Real.exp (-(lam * s)) * ∑ J ∈ F, e J
          = ∑ J ∈ F, e J * Real.exp (-(lam * s)) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
        _ ≤ ∑ J ∈ F, e J * (1 - q) ^ J.card :=
            Finset.sum_le_sum fun J hJ => mul_le_mul_of_nonneg_left (hexpJ J hJ) (he0 J)
        _ = ∑ J ∈ F, ∑ T ∈ (Finset.univ : Finset κ).powerset,
              (if Disjoint J T then W Finset.univ T * e J else 0) := by
            refine Finset.sum_congr rfl fun J _ => ?_
            rw [← hWsum J, Finset.mul_sum]
            refine Finset.sum_congr rfl fun T _ => ?_
            by_cases h : Disjoint J T <;> simp [h, mul_comm]
        _ = ∑ T ∈ (Finset.univ : Finset κ).powerset, ∑ J ∈ F,
              (if Disjoint J T then W Finset.univ T * e J else 0) := Finset.sum_comm
        _ ≤ ∑ T ∈ (Finset.univ : Finset κ).powerset, W Finset.univ T * P T := by
            refine Finset.sum_le_sum fun T _ => ?_
            have h1 : ∑ J ∈ F, (if Disjoint J T then W Finset.univ T * e J else 0)
                = W Finset.univ T * ∑ J ∈ F.filter (fun J => Disjoint J T), e J := by
              rw [Finset.sum_filter, Finset.mul_sum]
              refine Finset.sum_congr rfl fun J _ => ?_
              by_cases h : Disjoint J T <;> simp [h, mul_comm]
            rw [h1]
            exact mul_le_mul_of_nonneg_left (hPge T) (hW0 _ _)
        _ = Φ Finset.univ := (hΦ _).symm
    rw [hAeq, ← hsumE]
    have hmul := mul_le_mul_of_nonneg_left hkey (Real.exp_pos (lam * s)).le
    rw [← mul_assoc, ← Real.exp_add] at hmul
    simpa using hmul
  have h2 : ∑ j ∈ (Finset.univ : Finset κ), a j = jansonMu p S :=
    Finset.sum_congr rfl fun j _ => ha j
  have h3 : E (Finset.univ : Finset κ) = jansonDelta p S D := by
    rw [hE, Finset.filter_true_of_mem fun z _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩]
    exact Finset.sum_congr rfl fun z _ => hb z.1 z.2
  calc (setBernoulli Set.univ p {R : Set ι | jansonCount S R ≤ s}).toReal
      ≤ Real.exp (lam * s) * Φ Finset.univ := hPart1
    _ ≤ Real.exp (lam * s) * Real.exp (-q * jansonMu p S + q ^ 2 * jansonDelta p S D / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
        have hu := hΦmain Finset.univ
        rwa [h2, h3] at hu
    _ = Real.exp (lam * s - q * jansonMu p S + q ^ 2 * jansonDelta p S D / 2) := by
        rw [← Real.exp_add]; congr 1; ring
    _ = Real.exp (lam * s - (1 - Real.exp (-lam)) * jansonMu p S
          + (1 - Real.exp (-lam)) ^ 2 * jansonDelta p S D / 2) := by rw [hqdef]

end LowerTail

/-- **Janson's inequality III** (Zhao, Theorem 8.2.2): the lower tail of the count.  For
`0 ≤ t ≤ μ`,

    ℙ(X ≤ μ - t) ≤ exp (-t² / (2(μ + Δ))).

Taking `t = μ` recovers the first two inequalities up to a constant in the exponent, so this is
the strongest of the three.  There is deliberately no companion for the *upper* tail: Example
8.2.4 shows the analogous bound is false, since planting a clique forces an excess of triangles
at far higher probability than any such bound would allow. -/
theorem janson_lower_tail [Countable ι] (p : I) (S : κ → Set ι) (D : Finset (κ × κ))
    (hD : ∀ i j, i ≠ j → (i, j) ∉ D → Disjoint (S i) (S j))
    {t : ℝ} (ht0 : 0 ≤ t) (htμ : t ≤ jansonMu p S) :
    (setBernoulli Set.univ p
        {R : Set ι | jansonCount S R ≤ jansonMu p S - t}).toReal
      ≤ Real.exp (-t ^ 2 / (2 * (jansonMu p S + jansonDelta p S D))) := by
  have hμ0 : 0 ≤ jansonMu p S := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hΔ0 : 0 ≤ jansonDelta p S D := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  rcases ht0.lt_or_eq with ht | ht
  · have hc : 0 < jansonMu p S + jansonDelta p S D := by linarith
    have hcne : jansonMu p S + jansonDelta p S D ≠ 0 := ne_of_gt hc
    have hlam0 : 0 ≤ t / (jansonMu p S + jansonDelta p S D) := div_nonneg ht0 hc.le
    refine (janson_lower_tail_step_le p S D hD
      (lam := t / (jansonMu p S + jansonDelta p S D)) (s := jansonMu p S - t) hlam0).trans
      (Real.exp_le_exp.2 ?_)
    set lam := t / (jansonMu p S + jansonDelta p S D) with hlamdef
    set q := 1 - Real.exp (-lam) with hqdef
    have hq0 : 0 ≤ q := by
      have h := Real.exp_le_one_iff.2 (neg_nonpos.2 hlam0)
      rw [hqdef]; linarith
    have hq1 : q ≤ lam := by
      have h := Real.add_one_le_exp (-lam)
      rw [hqdef]; linarith
    have hq2 : lam - lam ^ 2 / 2 ≤ q := by
      have h := exp_neg_le_one_sub_add_sq_div_two hlam0
      rw [hqdef]; linarith
    have hq3 : q ^ 2 ≤ lam ^ 2 := by nlinarith
    have hfin : -t ^ 2 / (2 * (jansonMu p S + jansonDelta p S D))
        = -lam * t + lam ^ 2 * (jansonMu p S + jansonDelta p S D) / 2 := by
      rw [hlamdef]; field_simp; ring
    rw [hfin]
    nlinarith [mul_nonneg hμ0 (sub_nonneg.2 hq2), mul_nonneg hΔ0 (sub_nonneg.2 hq3)]
  · have hprob : setBernoulli Set.univ p
        {R : Set ι | jansonCount S R ≤ jansonMu p S - t} ≤ 1 := prob_le_one
    have hone : Real.exp (-t ^ 2 / (2 * (jansonMu p S + jansonDelta p S D))) = 1 := by
      rw [← ht]; norm_num
    rw [hone]
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hprob

end ProbMethodCombinatorics
