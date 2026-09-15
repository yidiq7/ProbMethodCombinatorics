# Orchestrator notes

Failure modes and guidance the orchestrator has learned from reviewing this project's
pull requests.  Machine-authored; the overseer may edit, delete, or promote any entry.

## 2026-09-12 — Which convention applies is decided per chapter, not per node

Chapters 1–3 and 5 are stated as **counting** over `Finset`/`Fintype`; Chapters 4 and 6 are
stated over `MeasureTheory.Measure`.  That split is not stylistic and is not yours to
revisit inside a task:

- Chapters 1–3 and 5 end in existence claims about finite objects, and every proof is
  "compute an average / a union bound, then take something at least as good".  A measure
  buys nothing there and costs a great deal.
- Chapter 4's second moment method *is* about a measure, and Mathlib supplies `variance`,
  Chebyshev and `SimpleGraph.binomialRandom`.
- Chapter 6's independence (Definition 6.1.1) is independence from a whole family of
  events, strictly stronger than pairwise, with no counting surrogate.

If a task's statement looks like it is in the wrong idiom, say so on the issue rather than
converting it in your PR — the statement is fixed and a PR that changes it is rejected.

## 2026-09-12 — Tasks pin different base commits, and that is fine

Issues #4–#13 pin `dcaf5da`, #14–#20 pin `22ba93e`, #21–#30 pin `c943f93`.  Each batch added
files without rewriting any existing declaration, so an older pin costs you nothing.  Work
at the commit your task names; do not rebase onto `main` to pick up later chapters.

## 2026-09-13 — Proofs that strengthen the target internally are welcome

Both merged Chapter 1–2 proofs so far worked by proving something stronger inside the proof
and specializing at the end: #33 covered the spoiled colourings by an explicit `Finset`, and
#34 generalized Caro–Wei to an arbitrary vertex subset so the greedy induction closes.  That
is the right instinct.  Keep such generalizations **inside** the proof unless the plan says
otherwise — a new top-level declaration is a statement nobody reviewed when the task was
written, and it is the one thing in a PR the kernel cannot check for you.  If you think a
generalization deserves to be reusable, say so on the issue and it can become its own node.

## 2026-09-13 — Leaning on an unproved sibling means declaring a reduction

**If your proof calls a declaration that still carries a placeholder, your PR will fail
`comparator` with `outcome: illegal-axiom` unless you declare a reduction.**

`sorry-delta` passes in that situation — you added no new placeholder — but comparator
checks the **axiom closure of your target**, and calling a `sorry`-bearing lemma puts
`sorryAx` in it.  Under this project's `sorry = block` policy an ordinary `prove`
submission is refused that axiom, by design: it is what makes a green gate on a prove PR
mean *unconditionally proved*.

The sanctioned route is a `choir-reduction` block in the PR body naming what you leaned on:

    ```choir-reduction
    choir-reduction-version: 1
    parent: <your task's target decl>
    children:
      - decl: <the placeholder-carrying declaration you called>
        blueprint_ref: <its node id, if it has one>
        note: <where the obligation comes from>
    ```

`sorryAx` is permitted for a declared reduction, and comparator degrades to "right
statement, kernel-consistent modulo a named open obligation".  The gate reads the block
from the PR body, but checks only re-run on push — push an empty commit to re-trigger.

Two practical notes:

- Many tasks here name dependencies that are *stated but unproved*.  Using their
  statements is correct and expected; just declare the reduction.  Alternatively wait for
  the dependency to merge, after which the same diff passes as an ordinary proof.
- A child entry is matched by its **last name segment**, and any other declaration in the
  same file with that segment disarms it.  Check for collisions before relying on one.

## 2026-09-13 — Your workspace is pinned; check whether it is stale before submitting

Your workspace is built at the task's **pinned commit**, not at `main`.  As proofs merge,
that pin ages, and a branch built on an old pin still contains the *placeholder* versions
of declarations that have since been proved.  Submitting it would revert them, and
`sorry-delta` rejects the PR for adding placeholders to declarations your diff never
touched — a confusing failure, because the diff looks clean.

Keeping pins current is the orchestrator's job and all open tasks were re-pinned on
2026-09-13.  But if a task sat in your workspace while other work merged:

    git fetch origin main && git rebase origin/main && git push --force-with-lease

Only the target *file* matters — a stale pin is harmless if nothing merged into that file.

When you rebase, **re-check any `choir-reduction` block**: obligations that have since been
proved must be dropped from `children`, or the block claims something untrue.

## 2026-09-13 — Use `lovasz_local_lemma`; do not re-derive it

`lovasz_local_lemma` (the general form) and `measure_inter_biInter_compl_le` (its induction
step) are **proved** as of PR #41.  The symmetric form in PR #44 re-derived the general form
inline, which was correct at the time — that PR was opened 73 seconds before #41 merged, so
calling it would have pulled in `sorryAx`.  It is no longer necessary.

For `lovasz_local_lemma_of_sum_le` and anything else in this group: apply the general form
with the weights your corollary needs (`x = fun _ => t` for a constant weight) rather than
repeating the induction.  If you find yourself writing a second copy of an argument that
already exists in the file, check whether the dependency has merged since your workspace was
pinned.

## 2026-09-13 — If a statement looks unprovable at small `n`, say so; don't grind

Three published statements have been **false at degenerate inputs** (`card_filter_le_exp_mul`,
`card_filter_abs_le_exp_mul`, `exists_nearly_equiangular`), each because a book statement
phrased "for every `n`" was transcribed literally when the mathematics is asymptotic.  All
three are now fixed.

If a task resists and the obstruction is at `n = 0`, `n = 1`, or an empty structure, **that is
worth a comment on the issue rather than more attempts.**  Releasing the lease silently costs
everyone: `metrics struggle` counts only failed *PRs*, so an abandoned claim is invisible and
the defect can sit for hours.  A one-line "this looks false at `n = 0` because …" gets it fixed
quickly and is never held against you.

## 2026-09-15 — Never run `git add -A` while a review subagent is live

**Orchestrator-side incident, recorded so it is not repeated.** Stage-two review is delegated to
a subagent (per Choir's `ORCHESTRATOR.md`). The reviewer applied the PR patch to the *shared*
project checkout to build and check axioms — reasonable, and it restored the tree afterwards —
while the orchestrator concurrently ran `git add -A && git commit` for unrelated roadmap work.

Result: commits `07a2f6b` and `726e414` each swept up 147 lines of PR #140's proof (the first
adding it, the second removing it again). Both were pushed before anyone noticed. The tip was
correct and the PR's diff was unaffected, but two commits on `main` carry changes that contradict
their messages.

**History was not rewritten.** `main` is shared: open tasks pin `project_ref.commit`, and
contributors branch from it. Force-pushing to repair cosmetic history would have broken live
pins — a strictly worse outcome than two odd commits. The fix is procedural:

- **Stage explicit paths, never `git add -A`**, whenever any background agent may be running.
  `git add roadmap/ skills/` is as easy to type and cannot capture someone else's work.
- **Tell review subagents not to mutate the working tree.** Reading a patch (`gh pr diff`),
  `git show`-ing base blobs, and reasoning from those needs no checkout mutation. If a reviewer
  genuinely must build the patched tree, it belongs in a separate clone or `git worktree`, not in
  the checkout the orchestrator is committing from.
- **Re-pin open tasks off any contaminated commit**, so nobody builds from a tree that
  misrepresents what is proved.

The general form: **an orchestrator that delegates work into its own working directory has to
treat that directory as shared state.** The subagent did nothing wrong; the concurrency was mine.
