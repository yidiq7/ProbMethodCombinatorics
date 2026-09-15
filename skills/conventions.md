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

## What a `golf` task is, and is not

A `golf` task makes the proof of one pinned declaration shorter, without changing its statement:
name, signature and stated proposition stay **token-identical to base**, down to bound-variable
names and hypothesis order. Only the proof body changes. There is no cosmetic-rewrite exception.

So a `golf` task may **not** delete a declaration, rename one, change a visibility modifier, move
a declaration between sections, or add a new lemma. `statement-immutability` blocks all of those
and is right to.

Consolidation that needs any of them — retiring a duplicate, promoting a `private` helper so
another file can reach it, relocating a lemma above its call sites — is **orchestrator work**,
not a publishable task of any type. If you are a contributor and a task appears to ask you for
one of these, say so on the issue; the task is mis-specified.

## Mathlib returns junk values instead of failing

Three separate defects in this project have come from the same shape: a Mathlib definition that,
when its side condition is unmet, **silently returns a default value rather than failing to
elaborate**. Nothing warns you. The statement type-checks, the proof may even go through, and the
result is wrong or vacuous.

- **A measure applied to a non-measurable set** returns its *outer* measure, not an error. This
  made the Chapter 8 statements false at `p = 1` for uncountable `ι`, because the product
  σ-algebra on `Set ι` only contains sets depending on countably many coordinates.
- **`∫` of a non-integrable function is `0`.** Combined with the above, that put the bounded
  differences inequality's left-hand side at `1` against a right-hand side below `1`.
- **`Measure.infinitePi` is `if h : ∀ i, IsProbabilityMeasure (μ i) then … else 0`.** Without the
  instance in scope it is the zero measure, and no `infinitePi` lemma will fire — the symptom is
  lemmas mysteriously not applying, not an error at the definition.

**What to do.** When a statement rests on a definition with a side condition — measurability,
integrability, a probability-measure instance, summability — check whether the definition
*enforces* it or *defaults* when it fails. If it defaults, the hypothesis belongs in the
statement, and if you are proving rather than stating, supply the instance as a local `have`
before expecting the API to work.

**The tell that generalises:** when Mathlib fences part of an API behind a hypothesis — a
`section Countable`, a `[IsProbabilityMeasure]` argument — a statement built on the unfenced
remainder deserves a second look. That is how the Chapter 8 defect was spotted.

## Check the file before trusting the task's route

A task's `TASK.md` route is a snapshot from the day it was published, and this project's shared
layer grows fast — lemmas that make a task much easier routinely land *after* its prose was
written. Two tasks here were each abandoned twice for exactly this reason.

**Before starting, read the target's file for what now exists**, especially anything added by a
recently merged sibling task. If the route in the prose looks longer than it needs to be, it
probably is; say so on the issue rather than following it.

Nothing checks task prose. Statements are machine-checked and reviewed; routes are not.

## Entropy sums: reach for `log t ≤ t - 1`, not Mathlib's Jensen API

Every inequality between entropy sums proved in this project so far has come out shorter through
`Real.log_le_sub_one_of_pos` than through `ConcaveOn`/Jensen. `entropy_pair_le_add` in
`Entropy.lean` is the worked template: bound each term with `log (x) ≤ x - 1`, sum, and rescale
at the end with

    calc -w * Real.logb 2 w = (-w * Real.log w) * (Real.log 2)⁻¹ := by rw [Real.logb]; ring

Terms where the probability is `0` vanish on both sides, so the `pₛ = 0` case needs no split —
`Real.logb 2 0 = 0` by Mathlib's junk convention, which is also why the shared layer needs no
`support` definition.

Mathlib's concavity lemmas exist (`Real.strictConcaveOn_negMulLog`) but getting a finite weighted
Jensen out of them for these shapes has repeatedly cost more than the elementary route.

## Reductions: two things that trip people up

**A child may be a placeholder that was already there.** `children` in a `choir-reduction` block
names *every* open obligation the proof leans on — both the lemmas you just stated and any
declaration already in the project that still carries a placeholder. Naming a pre-existing one
is free: `sorry-delta` only examines placeholder counts that *rose*, so citing an obligation
that was already sorried at base, and leaving it exactly as sorried, cannot trip it
(`gate/verify/sorry_delta.py`, Rule B).

This matters because of the case that looks like it needs no block at all: **your target is
fully proved, adds no placeholder of its own, but leans on something that is still open.** The
`sorryAx` is in your closure regardless, `comparator` will return `illegal-axiom`, and the block
is the only thing that permits it — `sorryAx` is added to the permitted set exactly when a
reduction is declared (`gate/verify/comparator.py`). "I added no placeholder" is not a reason to
omit the block.

**When two checks seem to contradict each other, read `gate/verify/`.** The gate is in the Choir
checkout and its rules are documented in the module docstrings. Deducing a general rule from one
red run is how you end up removing the thing that would have fixed it.

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
