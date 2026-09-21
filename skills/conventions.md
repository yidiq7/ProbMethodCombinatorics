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
`open scoped ENNReal` is in `Concentration.lean`, `Correlation.lean` and `Janson.lean` — but
**not** in `SecondMoment.lean` or `LocalLemma.lean`, so check your target's header rather than
assuming it.  Without it `ℝ≥0∞` parses as `ℝ ≥ 0 ∞` and fails with
`failed to synthesize OfNat Type 0`.  If your file lacks it, spell out `ENNReal`/`NNReal` in
your proof rather than adding to the header — the header is not yours to change in a `prove`
task.

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

## Check sibling *open* PRs against your target file, not just merged work

Two PRs landed the same 128-line argument in `Alterations.lean` within five minutes of each
other — one as a top-level lemma, one inlined as a `have` inside the parent theorem. Both were
correct, neither contributor did anything wrong, and neither could see the other because both
were pinned to the same base.

`gh pr list --repo <owner/repo> --state open` takes a second and tells you whether someone is
already working the same file. If they are, **say so on your issue** — the orchestrator can
sequence the two, and cannot if nobody mentions it. This is the open-PR companion to the rule
below about lemmas that landed after your task was published.

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

## Test a candidate obligation against extremal instances before committing to it

If you are returning a reduction, the obligations you name become public statements that others
build on — and a false obligation is worse than no progress, because the parent then *looks*
discharged. Four author-side statements in this project have been false, and every one was found
by reading rather than by a gate check. None of the nine checks can see it.

Before you commit to an obligation, instantiate it on the extremal cases of its own hypotheses
and see whether the conclusion survives. For graph and hypergraph statements the two that have
actually killed statements here are:

* **the complete graph / complete hypergraph** — maximal density, `d ≈ n`, very few independent
  sets, so any "budget" of the form `εn/d` or `n/√d` collapses below `1` and forces existentials
  to be empty;
* **a disjoint union of small stars or paths** — minimal density, `d = O(1)`, but a *large*
  independent set (all the leaves), which forces any "container" or "cover" bound to be generous.

A statement that must satisfy both simultaneously is often pinned into a contradiction. That is
exactly how `exists_containers_fingerprint` was refuted: `Kₙ` forced `δ ≥ 1/2`, stars forced
`δ ≤ 1/3`.

**And if the source states a side condition inside a proof sketch rather than in the theorem box,
it probably belongs in the statement.** That is where the missing `d ≤ 2δ|V|` was.

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

**If you change a proof's method, the comments inside it are yours to bring with it.**  This is
the most common defect in golf PRs on this project: the proof becomes correct and shorter while
the prose around it goes on describing the argument that used to be there.  Concretely, before
you push, re-read every comment in the body you touched and check that

* every lemma or technique a comment names is still used by the proof, and
* every variable a comment mentions is still a binder in the body.

A comment naming a `have` you deleted, or crediting a Mathlib lemma you stopped calling, is a
defect even though it compiles — nothing in the gate reads English.

**The target's own docstring is the exception: you may not edit it, so report it instead.**  A
golf that drops the technique the docstring advertises leaves that docstring false, and the rule
above forbids you from fixing it.  **Say so on the issue** — name the claim that went stale and
what the proof does now.  It is a one-line note and it is the only way the orchestrator finds
out; this has already happened three times and was caught in review each time rather than
reported.  The same goes for an import whose last consumer your proof removed.

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

## Name every `instance`, especially one that appears in a statement

`comparator` builds a *challenge* tree from the base with every module renamed under a
`ChoirBase.` prefix, and compares the target's elaborated statement there against the one in
your tree.  An **anonymous** `instance` gets an auto-generated name that does not survive that
renaming, so if the instance appears inside the statement's term the two sides differ as terms
while their bytes are identical — and the gate reports `statement-mismatch` on a statement
nobody touched.

This actually happened: `Derangements.lean` declared
`instance : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤` anonymously, that instance rides inside
every statement mentioning `uniformPerm`, and all five such PRs went red while
`statement-immutability` and `statement-equiv` stayed green.  `Concentration.lean`'s
`instCountableSimpleGraphFin` and friends are named and never had the problem.

So: give instances explicit names.  It costs nothing and it is the difference between a gate
that works and one that rejects correct proofs.

## If `comparator` disagrees with the byte-level checks

`comparator` rebuilds; `statement-immutability` and `statement-equiv` compare bytes.  When the
first is red and the other two are green, **something about elaboration differs, not your
proof.**  Two causes seen so far, in order of likelihood:

1. An anonymous instance in the statement's term — see above.  This is a defect in the
   *statement file* and the orchestrator must fix it; do not work around it.
2. Your branch is far behind `main`.  Merge `origin/main` in and push.

Try (2) first because it is free, but if `comparator` is still red afterwards, **stop and say
so on the thread.**  Do not start editing your proof, and never edit the statement to make a
gate pass.  A second red after a clean re-merge is information the orchestrator needs.

## If your proof inherits `sorryAx` from a dependency

`comparator` checks out GitHub's generated merge ref for the workspace, but empirically an
inherited `sorryAx` has cleared only once the contributor merged `main` in and pushed.  So when your
target calls a lemma that is still a placeholder at your base, the gate sees `sorryAx` in
your closure — and that does **not** clear when the dependency merges into `main`.  The
merge has to happen in your workspace:

```sh
git fetch origin main
git merge --no-edit origin/main     # merge, not rebase: keeps the statement bytes untouched
```

then push, and check `#print axioms` gives `[propext, Classical.choice, Quot.sound]` before
saying the PR is clean.  Wait for the dependency to land first; nothing else is required of
you, and you do not need a `choir-reduction` block — that contract covers *adding* a
placeholder, and filling one in adds none.

## Two traps that cost real time

**`set` makes `linarith` and `omega` atoms syntactic.**  After
`set t := ⌈10 * Real.sqrt n⌉₊`, instantiating a lemma stated in the unfolded form puts
*both* spellings in context, and `linarith` treats them as unrelated atoms.  Fold the
hypothesis back with `rw [← ht_def] at h` before calling the solver.  The same hazard shows
up with any `Nat.choose` or cast expression that appears in two spellings.

**Names that do not exist, and their replacements.**  `Measure.real` is a def, not a rewrite
lemma — use `measureReal_def` (or the alias `Measure.real_def`).  For counting measure on a
`Finset`, `Measure.count_apply_finset` is the one you want; `Measure.count_apply_finite` drags
in `Set.Finite.toFinset` bookkeeping.  When a map is a bijection of the *whole* type,
`Finset.card_equiv` with e.g. `Equiv.mulLeft` beats `Finset.card_nbij'`, which makes you
discharge `MapsTo`/`LeftInvOn`/`RightInvOn`.

**Factorial notation is scoped.**  `n !` only parses where `Nat` is open.  Several files in this
project open only `Finset MeasureTheory ProbabilityTheory`, and there `n !` fails with
`unexpected token ':='; expected term` because `!` is read as boolean negation.  Write
`Nat.factorial n`.

**`measureReal_mono` carries no measurability obligation** — it needs only `s ⊆ t` and
`μ t ≠ ∞`, and the latter is found by instance search whenever the measure is a probability
measure.  Neither do the `measureReal` union bounds.  If a task's suggested route tells you
to establish measurability before applying one of these, the route is wrong and you can skip
it; measurability of graph events is only needed for `Measure.map_apply` and for integrals.

**But check `measureReal_*` is in scope before reaching for it — in a file with narrow
measure-theory imports it will not be.**  `Measure.real` is defined in
`MeasureTheory/Measure/MeasureSpaceDef.lean`, while the whole `measureReal_*` API lives in
`MeasureTheory/Measure/Real.lean`, which is further downstream.  **A statement written in
`μ.real` therefore elaborates in files where nothing can be proved about it**, and the gap
shows up only when you reach for the first lemma.  This has already cost one task
(`ConcentrationEquivalence.lean`, whose header has since been fixed).

If you hit it, the two facts you are most likely to want are one line each from the
`ENNReal`-valued measure, and a `prove` task may **not** add the import to fix it — the header
is not yours:

    have hmono : ∀ s u : Set Ω, s ⊆ u → μ.real s ≤ μ.real u := fun s u hsu =>
      ENNReal.toReal_mono (measure_ne_top μ u) (measure_mono hsu)
    have hcompl : ∀ s : Set Ω, MeasurableSet s → μ.real sᶜ = 1 - μ.real s := by
      intro s hs
      simp only [Measure.real, prob_compl_eq_one_sub hs,
        ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]

Note this also takes `gcongr` off the table for those steps, since the `@[gcongr]`-tagged
lemma is the unreachable one.  **Say so on the issue when it happens** — an unreachable route
in a task's prose is an orchestrator error and it should be fixed at the source rather than
worked around silently by each contributor in turn.
