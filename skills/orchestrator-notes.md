<!-- choir:orchestrator-notes — machine-authored, overseer-curatable -->

# Orchestrator notes

Failure modes this project's pull requests keep running into, written down so the next
worker starts knowing them.  Delivered to every worker's task with the rest of the skill
pack.

**Provenance.** The orchestrator writes only this file; every other file in `skills/` is
the overseer's.  The overseer may edit, delete, or promote any entry.

**Format.** Newest first, each entry dated and pointing at the task or PR that prompted
it.  Active guidance, not a changelog — resolved entries are pruned.

---

## 2026-09-16 — `choir worker heartbeat` never refreshes a lease; `refreshed: false` means nothing

**Reported by a contributor working #99, and verified in the Choir checkout at `0.1.2`.** If you
run the named command on your own live lease you get `{"refreshed": false}` and the thread's
heartbeat comment keeps its original timestamp.

Why: `client/cli.py`'s `cmd_heartbeat` calls `heartbeat(args.repo, args.issue)` and passes no
`session`, so it takes the default `session=""` — the subparser has no `--session` flag and does
not resolve the workspace. `client/heartbeat.py` then checks
`(decision.holder, decision.holder_session) != (login, session)` and returns before writing. Since
claiming and beating are separate invocations, `holder_session` is always a real id, so the pair
never matches. The library path is fine if you pass `session=`; only the named command is broken,
and that is the one `CONTRIBUTOR.md` tells you to use.

**What this means for you, until it is fixed upstream:**

- **`refreshed: false` is not "you lost the lease".** Right now it carries no information at all.
  Do not release a claim or abandon work because of it.
- **A lease can go stale at the 24h mark even though you heartbeated as instructed.** If your
  proof is running long and you see the task reclaimed or double-claimed, that is this bug, not
  someone jumping your claim. Say so on the issue and keep your branch.
- Heartbeat is best-effort by contract, so nothing will surface this to you. Judge your claim by
  the issue thread, not by the command's return.

Reported upstream; not patched here, because `~/.choir/checkout` is shared tooling for every
project on the machine and the fix belongs in Choir.

## 2026-09-16 — Never let a `private` declaration reach a published statement (lean4)

**A `private` declaration referenced by a target's statement silently disables `comparator`.**
PRs #173 and #174 both failed with `outcome: statement-mismatch` while every other check —
`statement-immutability` included — was green, and neither diff touched a statement.

Lean 4 mangles private names with the **module path**: compiling `private def myPrivateFoo` and
printing the environment gives `_private._stdin.0.myPrivateFoo`. Comparator builds the base side
under a `ChoirBase.` module prefix, so the two sides reference different constants and the
statements cannot match as kernel terms, for any diff.

This was the orchestrator's own doing (`IsGreedyRule` was adopted `private` and is now public), so
you are unlikely to hit it from a task's *given* statement. Where it can bite you: **a helper
lemma you author whose statement mentions a `private def` you also added.** Keep anything that
appears in a *statement* public, and reserve `private` for things only proof bodies mention.

**The tell:** `comparator` red, `statement-immutability` green, no statement in your diff. That is
never something to work around — comment on the issue.

## 2026-09-16 — If you flag an obligation as possibly false, say what you tried — and read your own evidence

PR #166 reduced Theorem 11.2.3 to three obligations and flagged one, `exists_dense_fingerprint`,
as neither provable nor refutable, asking that it not be published.  **The obligation is true, and
the proof is about fifteen lines of counting.**  The task is published (#171) with the route in its
prose.

What went wrong is worth copying, because the author did almost everything right.  They probed
clique unions, clique-plus-matching and Hi/Lo degree-sequence constructions for a counterexample,
found that **every one was covered**, and reported honestly that there was "no refutation, but no
proof either".  That report is what let the obstruction be located in minutes — so **flagging was
the right call and is never held against you.**

The misreading: they had fixed one construction (select the largest-degree vertex, kill its
predecessors in *degree* order) and found a window where it fell one vertex short.  The window is a
property of that construction, not of the statement, which only asks for *some* order in which
every vertex has `|N(v) ∪ Pred(v)| ≥ δn`.  Built greedily instead of by degree, it always exists.

Two things to take from it:

- **Repeated failure to refute is evidence the statement is true.**  If your counterexample search
  keeps getting covered, that is a signal to look for a proof, not a signal that the corner is hard.
- **Separate "I cannot prove this" from "this looks false", and say which.**  They are different
  reports and they get different answers (`orchestrator-review.md` makes the same distinction for
  `choir-defect` comments).  "My construction leaves a window of width `(c-1)δ`" is a precise and
  useful thing to say; "the obligation may be false" was an over-reading of it.

## 2026-09-15 — `statement-immutability` caught a branch silently reverting a statement repair

Worth recording because it is the single most valuable red check the project has had, and because
the failure mode is invisible in the PR's own diff view.

`exists_containers` and `exists_containers_fingerprint` were repaired (the missing `d ≤ 2δn`
proviso) at `1e4659a`. PR #146's *head* lacked the hypothesis while its *base* had it — so
merging would have reinstated a statement already proved false. The contributor's workspace
predated the repair even though GitHub computed the merge base as after it: a stale workspace
whose older copy of the declaration wins the merge. Same shape as the stale-pin reverts on #42
and #48, but on a **statement** rather than a proof, which is strictly worse.

Two consequences for how to run the loop:

- **After repairing a statement, expect in-flight branches to revert it.** Any PR against that
  file opened before the repair landed will carry the old text. Re-pinning open *tasks* does not
  help — a branch already exists. The check is the only backstop, so never override
  `statement-immutability` on a file whose statements were recently changed.
- **`sorry-delta` reads the PR body at the moment it runs.** #146's audit reported
  `submission: proof` despite a well-formed `choir-reduction` block, because the body was edited
  one second after the check fired. The tell is the `submission:` line in the audit output: if it
  says `proof` on a PR that declares a reduction, the gate did not see the block, and a re-push
  fixes it. Do not go looking for a defect in the block.

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

## 2026-09-13 — Proofs that strengthen the target internally are welcome

Both merged Chapter 1–2 proofs so far worked by proving something stronger inside the proof
and specializing at the end: #33 covered the spoiled colourings by an explicit `Finset`, and
#34 generalized Caro–Wei to an arbitrary vertex subset so the greedy induction closes.  That
is the right instinct.  Keep such generalizations **inside** the proof unless the plan says
otherwise — a new top-level declaration is a statement nobody reviewed when the task was
written, and it is the one thing in a PR the kernel cannot check for you.  If you think a
generalization deserves to be reusable, say so on the issue and it can become its own node.

## 2026-09-12 — Tasks pin different base commits, and that is fine

Issues #4–#13 pin `dcaf5da`, #14–#20 pin `22ba93e`, #21–#30 pin `c943f93`.  Each batch added
files without rewriting any existing declaration, so an older pin costs you nothing.  Work
at the commit your task names; do not rebase onto `main` to pick up later chapters.

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
