import ProbMethodCombinatorics.LocalLemma

/-!
# Section 6.6: satisfiability of sparse `k`-CNF formulas

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Example 6.1.6 and the existence
claim stated in §6.6: the local lemma guarantees a satisfying assignment whenever each clause
shares variables with at most `2 ^ k / e - 1` other clauses, since a uniform random assignment
violates a fixed `k`-clause with probability exactly `2 ^ (-k)`.

**What this file does not contain, and why.**  §6.6's headline results are algorithmic.
Theorem 6.6.3 (Moser–Tardos) is *quoted without proof* in the source — "We won't prove the
general theorem here" — so it is not a target, by the same rule that excludes Theorem 7.2.5.
Theorem 6.6.6, Lemma 6.6.7 and Lemma 6.6.8 concern the expected running time of a recursive
randomized procedure (Algorithm 6.6.5); formalising them needs a model of randomized algorithms
and their runtime, which neither Mathlib nor this project has.  What *is* formalisable from
§6.6 is the existence statement its opening paragraph appeals to, which is this file.

The constant differs from `twoColorable_of_inter_card_le` for a reason: a clause is violated by
exactly **one** assignment of its `k` variables, giving probability `2 ^ (-k)`, whereas an edge
of a hypergraph is monochromatic under **two**, giving `2 ^ (1 - k)`.  So the threshold here is
`2 ^ k` rather than `2 ^ (k - 1)`.
-/

namespace ProbMethodCombinatorics

open Finset

variable {V : Type*}

/-- A literal: a variable together with the sign it must take. -/
abbrev Literal (V : Type*) := V × Bool

/-- A clause is a finite set of literals, read disjunctively. -/
abbrev Clause (V : Type*) := Finset (Literal V)

/-- An assignment satisfies a clause when at least one literal is true under it. -/
def Satisfies (x : V → Bool) (C : Clause V) : Prop := ∃ l ∈ C, x l.1 = l.2

/-- The variables occurring in a clause. -/
def clauseVars [DecidableEq V] (C : Clause V) : Finset V := C.image Prod.fst

section Violation

open MeasureTheory

variable [Fintype V] [DecidableEq V]

/-- A uniform random colouring agrees with a prescribed pattern `f` on a given finite set with
probability `2 ^ -|T|`. -/
private theorem uniformColoring_pattern_eq (T : Finset V) (f : V → Bool) :
    uniformColoring V {x : V → Bool | ∀ u ∈ T, x u = f u} = (2 : ENNReal)⁻¹ ^ T.card := by
  have hset : {x : V → Bool | ∀ u ∈ T, x u = f u}
      = Set.univ.pi (fun a => if a ∈ T then ({f a} : Set Bool) else Set.univ) := by
    ext x
    constructor
    · intro hx a _
      show x a ∈ (if a ∈ T then ({f a} : Set Bool) else Set.univ)
      by_cases ha : a ∈ T
      · rw [if_pos ha]; exact hx a ha
      · rw [if_neg ha]; exact Set.mem_univ _
    · intro hx u hu
      have hxu : x u ∈ (if u ∈ T then ({f u} : Set Bool) else Set.univ) := hx u (Set.mem_univ u)
      rw [if_pos hu] at hxu
      exact hxu
  rw [hset, uniformColoring, Measure.pi_pi]
  have hrew : ∀ a : V, fairCoin (if a ∈ T then ({f a} : Set Bool) else Set.univ)
      = if a ∈ T then (2 : ENNReal)⁻¹ else 1 := by
    intro a
    by_cases ha : a ∈ T
    · rw [if_pos ha, if_pos ha]; exact fairCoin_singleton (f a)
    · rw [if_neg ha, if_neg ha]; exact fairCoin_univ
  rw [Finset.prod_congr rfl (fun a _ => hrew a), Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_const]

/-- A clause on `k` pairwise distinct variables is violated by exactly one assignment of those
variables, so a uniform random assignment violates it with probability `2 ^ -k`. -/
private theorem uniformColoring_violated_eq {k : ℕ} (C : Clause V) (hcard : C.card = k)
    (hdistinct : ∀ l ∈ C, ∀ l' ∈ C, l.1 = l'.1 → l = l') :
    uniformColoring V {x : V → Bool | ∀ l ∈ C, x l.1 = !l.2} = (2 : ENNReal)⁻¹ ^ k := by
  have hgval : ∀ l ∈ C, decide (((l.1, false) : Literal V) ∈ C) = !l.2 := by
    intro l hl
    cases hl2 : l.2 with
    | false =>
      have hmem : ((l.1, false) : Literal V) ∈ C := by
        have heq : ((l.1, false) : Literal V) = l := by rw [← hl2]
        rw [heq]; exact hl
      simp [hmem]
    | true =>
      have hmem : ((l.1, false) : Literal V) ∉ C := by
        intro hcon
        have heq := hdistinct l hl _ hcon rfl
        have h2 : l.2 = false := by rw [heq]
        rw [hl2] at h2
        exact Bool.noConfusion h2
      simp [hmem]
  have hset : {x : V → Bool | ∀ l ∈ C, x l.1 = !l.2}
      = {x : V → Bool | ∀ u ∈ clauseVars C, x u = decide (((u, false) : Literal V) ∈ C)} := by
    ext x
    constructor
    · intro hx u hu
      simp only [clauseVars, Finset.mem_image] at hu
      obtain ⟨l, hl, hlu⟩ := hu
      rw [← hlu, hx l hl, hgval l hl]
    · intro hx l hl
      have hl1 : l.1 ∈ clauseVars C := by
        simp only [clauseVars]
        exact Finset.mem_image_of_mem Prod.fst hl
      rw [hx l.1 hl1, hgval l hl]
  have hcardvars : (clauseVars C).card = k := by
    have hinj : Set.InjOn Prod.fst (↑C : Set (Literal V)) := by
      intro l hl l' hl' hll'
      exact hdistinct l (Finset.mem_coe.1 hl) l' (Finset.mem_coe.1 hl') hll'
    simp only [clauseVars]
    rw [Finset.card_image_of_injOn hinj, hcard]
  rw [hset, uniformColoring_pattern_eq, hcardvars]

/-- The real-valued form of `uniformColoring_violated_eq`, as the local lemma consumes it. -/
private theorem uniformColoring_violated_toReal {k : ℕ} (C : Clause V) (hcard : C.card = k)
    (hdistinct : ∀ l ∈ C, ∀ l' ∈ C, l.1 = l'.1 → l = l') :
    (uniformColoring V {x : V → Bool | ∀ l ∈ C, x l.1 = !l.2}).toReal = 1 / 2 ^ k := by
  rw [uniformColoring_violated_eq C hcard hdistinct, ENNReal.toReal_pow, ENNReal.toReal_inv,
    show ((2 : ENNReal)).toReal = (2 : ℝ) from by norm_num, one_div, ← inv_pow]

end Violation

/-- **Sparse `k`-CNF formulas are satisfiable** (Zhao, §6.6): if every clause has `k` literals
on distinct variables and shares a variable with at most `d` other clauses, and
`e (d + 1) ≤ 2 ^ k`, then the formula has a satisfying assignment.

Equivalently `d ≤ 2 ^ k / e - 1`, which is the form the source states.  Theorem 6.6.6 shows the
same conclusion is reachable *algorithmically* under the slightly stronger `d ≤ 2 ^ (k - 3)`. -/
theorem exists_satisfying_assignment [Fintype V] [DecidableEq V] {k : ℕ}
    (F : Finset (Clause V)) (hcard : ∀ C ∈ F, C.card = k)
    (hdistinct : ∀ C ∈ F, ∀ l ∈ C, ∀ l' ∈ C, l.1 = l'.1 → l = l') {d : ℕ}
    (hd : ∀ C ∈ F,
      ((F.erase C).filter fun D => (clauseVars C ∩ clauseVars D).Nonempty).card ≤ d)
    (h : Real.exp 1 * (d + 1) ≤ 2 ^ k) :
    ∃ x : V → Bool, ∀ C ∈ F, Satisfies x C := by
  -- The bad events and their dependency graph.
  obtain ⟨A, hAdef⟩ : ∃ A : { C // C ∈ F } → Set (V → Bool), ∀ C x,
      (x ∈ A C ↔ ∀ l ∈ (C : Clause V), x l.1 = !l.2) :=
    ⟨_, fun _ _ => Iff.rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : { C // C ∈ F } → Finset { C // C ∈ F }, ∀ C D,
      (D ∈ N C ↔ D ≠ C ∧ (clauseVars (C : Clause V) ∩ clauseVars (D : Clause V)).Nonempty) :=
    ⟨fun C => Finset.univ.filter fun D =>
      D ≠ C ∧ (clauseVars (C : Clause V) ∩ clauseVars (D : Clause V)).Nonempty, by simp⟩
  have hAmeas : ∀ i, MeasurableSet (A i) := fun _ => (Set.toFinite _).measurableSet
  -- Two assignments agreeing on the variables of a clause agree on whether it is violated.
  have hAinv : ∀ (D : { C // C ∈ F }) (x y : V → Bool),
      (∀ a ∈ clauseVars (D : Clause V), x a = y a) → (x ∈ A D ↔ y ∈ A D) := by
    intro D x y hxy
    have hmem : ∀ l ∈ (D : Clause V), x l.1 = y l.1 := by
      intro l hl
      refine hxy l.1 ?_
      simp only [clauseVars]
      exact Finset.mem_image_of_mem Prod.fst hl
    rw [hAdef, hAdef]
    constructor
    · intro hx l hl; rw [← hmem l hl]; exact hx l hl
    · intro hy l hl; rw [hmem l hl]; exact hy l hl
  have hNdep : IsDependencyGraph (uniformColoring V) A N := by
    intro i s hs g
    refine uniformColoring_inter_eq_mul (clauseVars (i : Clause V)) (A i) (pattern A s g)
      (hAinv i) ?_
    intro x y hxy
    have hj : ∀ j ∈ s,
        (x ∈ (if g j then A j else (A j)ᶜ) ↔ y ∈ (if g j then A j else (A j)ᶜ)) := by
      intro j hjs
      obtain ⟨hjne, hjN⟩ := hs j hjs
      have hdisj : Disjoint (clauseVars (i : Clause V)) (clauseVars (j : Clause V)) := by
        by_contra hcon
        exact hjN ((hNdef i j).2 ⟨hjne, Finset.not_disjoint_iff_nonempty_inter.1 hcon⟩)
      have hiff := hAinv j x y fun a ha =>
        hxy a fun hai => (Finset.disjoint_left.1 hdisj hai) ha
      by_cases hg : g j
      · rw [if_pos hg]; exact hiff
      · rw [if_neg hg]; exact not_congr hiff
    simp only [pattern, Set.mem_iInter]
    exact ⟨fun hx j hjs => (hj j hjs).1 (hx j hjs), fun hy j hjs => (hj j hjs).2 (hy j hjs)⟩
  -- Each clause is violated with probability exactly `2 ^ -k`.
  have hp : ∀ i, (uniformColoring V (A i)).toReal ≤ 1 / 2 ^ k := by
    intro i
    have hAeq : A i = {x : V → Bool | ∀ l ∈ (i : Clause V), x l.1 = !l.2} :=
      Set.ext fun x => hAdef i x
    rw [hAeq, uniformColoring_violated_toReal _ (hcard _ i.2) (hdistinct _ i.2)]
  have hdcard : ∀ i, (N i).card ≤ d := by
    intro i
    refine le_trans (Finset.card_le_card_of_injOn (fun D => (D : Clause V)) ?_ ?_) (hd i i.2)
    · intro D hD
      rw [Finset.mem_coe, hNdef] at hD
      exact Finset.mem_coe.2 (Finset.mem_filter.2
        ⟨Finset.mem_erase.2 ⟨fun hh => hD.1 (Subtype.ext hh), D.2⟩, hD.2⟩)
    · intro D _ D' _ hh
      exact Subtype.ext hh
  -- `e · 2 ^ -k · (d + 1) ≤ 1` is the hypothesis `h` divided by `2 ^ k`.
  have hcond : Real.exp 1 * (1 / 2 ^ k) * ((d : ℝ) + 1) ≤ 1 := by
    have h2 : (0 : ℝ) < 2 ^ k := by positivity
    rw [show Real.exp 1 * (1 / 2 ^ k) * ((d : ℝ) + 1)
      = (Real.exp 1 * ((d : ℝ) + 1)) / 2 ^ k from by ring, div_le_one h2]
    exact h
  have hpos := lovasz_local_lemma_symmetric A hAmeas N hNdep hp hdcard hcond
  -- An assignment violating no clause exists, and it satisfies every clause.
  rcases Set.eq_empty_or_nonempty (⋂ i, (A i)ᶜ) with hempty | ⟨x, hx⟩
  · rw [hempty] at hpos; simp at hpos
  · refine ⟨x, fun C hC => ?_⟩
    simp only [Set.mem_iInter, Set.mem_compl_iff] at hx
    have hnot := hx ⟨C, hC⟩
    rw [hAdef] at hnot
    show ∃ l ∈ C, x l.1 = l.2
    by_contra hcon
    refine hnot fun l hl => ?_
    have hne : x l.1 ≠ l.2 := fun hh => hcon ⟨l, hl, hh⟩
    revert hne
    cases x l.1 <;> cases l.2 <;> simp

end ProbMethodCombinatorics
