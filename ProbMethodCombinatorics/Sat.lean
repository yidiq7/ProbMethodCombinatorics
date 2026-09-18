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
  sorry

end ProbMethodCombinatorics
