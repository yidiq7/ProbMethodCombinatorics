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
