# Conventions

## Finite averaging, not measure theory

Every argument in Chapters 1–3 of the book is a finite average dressed as a probability.
The statements here are deliberately phrased as counting and existence claims over
`Finset` and `Fintype`, so the intended proof is:

1. sum the statistic over the whole finite family (all colourings, all orderings, all
   tournaments);
2. compare that sum to `card family * target`;
3. conclude some member meets the target (`Finset.exists_le_of_sum_le` and friends).

**Do not reach for `MeasureTheory` or `ProbabilityTheory`** to prove a Chapter 1–2 node.
Nothing in these statements mentions a measure, and introducing a probability space to
prove a counting bound makes the proof longer and harder to review, not shorter.  If you
believe a node genuinely needs one, say so on the issue rather than building it.

## Decidability

The gate runs a `verify-decide-instance` audit that counts `Decidable` instance
declarations and `Classical.*` helpers, and flags any net increase over the base commit.

- Every definition already in the repository is decidable by synthesis.  Keep it that way.
- **Do not write `instance : Decidable …`, `Classical.dec`, `Classical.decide`,
  `Classical.propDecidable`, `Classical.byContradiction`, or `Classical.choice`.**
- `by_contra`, `push_neg`, and `Or.elim` on a decidable proposition are all fine; the
  audit is textual and looks for the `Classical.` prefix.
- If a `Finset.filter` will not elaborate for want of a `DecidablePred`, restate the
  predicate in terms of `Bool` equality rather than declaring an instance.

## Naming and layout

- Everything lives in the `ProbMethodCombinatorics` namespace, one file per section group
  (`Intro.lean`, `Ramsey.lean`, `SetSystems.lean`, `PropertyB.lean`, `Expectation.lean`).
- Mathlib naming: `exists_`, `_le_`, `_of_` in the usual order; `theorem`, not `lemma`,
  for anything another file might use.
- Imports are targeted, not `import Mathlib`.  Add the narrowest module that works.

## Finding lemmas in Mathlib v4.33.0

Three traps that have each cost a contributor real time on this project.

**`grep` does not find derived lemmas.**  `@[to_additive]` and `@[to_dual]` generate
declarations that exist in the environment but appear nowhere in the source.  `grep "theorem
isLowerSet_"` finds nothing; `isLowerSet_iInter₂` is real.  Search for the *other* name —
multiplicative for `to_additive`, the order-dual for `to_dual` — or use `exact?` / `loogle` /
the LSP, which see the environment rather than the text.

**Prefer `gcongr` to named monotonicity lemmas.**  `mul_le_mul_left'` no longer exists in
v4.33.0, and the left/right convention has swapped underneath the names that remain:

    theorem mul_le_mul_right [MulLeftMono α]  (bc : b ≤ c) (a : α) : a * b ≤ a * c
    theorem mul_le_mul_left  [MulRightMono α] (bc : b ≤ c) (a : α) : b * a ≤ c * a

so the old `mul_le_mul_left' h a` is today's `mul_le_mul_right h a`, with
`add_le_add_left`/`add_le_add_right` swapped to match.  `gcongr` is insulated from all of
this and is the project's default for any congruence-shaped inequality step.

**Avoid truncated subtraction in `ℝ≥0∞`.**  `a - b` in `ENNReal` is `tsub`, and every
rearrangement through it drags a `b ≤ a` side condition behind it.  Rearrange *additively*
instead — `ENNReal` is a `CommSemiring`, so `ring` works — and cancel with
`ENNReal.add_le_add_iff_right`, discharging finiteness with `ne_top_of_le_ne_top`.  See
`prod_le_binomialRandom_iInter` in `Correlation.lean` for the pattern.
`open scoped ENNReal` is already in the header of every measure-theoretic file; without it
`ℝ≥0∞` parses as `ℝ ≥ 0 ∞` and fails with `failed to synthesize OfNat Type 0`.

## Docstrings and comments

Write comments in final form.  A docstring says what the declaration says — it is not a
record of how you got there.  Rejected approaches, notes to the reviewer, and commented-out
tactic blocks do not belong in the file; put them in the PR description instead.

## What not to touch

Your PR changes one proof.  Leave every other declaration, import, and docstring alone.

**The statement of your target is fixed.**  Its name, binders, hypotheses, and conclusion
are what the task is; only the body changes.  A PR that edits a statement is rejected by
the gate and by review, even when the new statement is true.  If you think the statement
is wrong, say so on the issue — that is a real and welcome outcome.

Never touch `.github/`, `.choir/`, `gate/`, `pyproject.toml`, `lean-toolchain`,
`lakefile.toml`, or `lake-manifest.json`.

## If you cannot finish

Sorries are blocked: a PR with a net-new `sorry` will not merge.  The way to land partial
progress is a **reduction** — state the intermediate lemmas you need as their own
declarations with real statements, prove your target *from* them, and say clearly in the
PR description which ones are left open.  Named obligations are useful to the project;
an unnamed `sorry` is not.
