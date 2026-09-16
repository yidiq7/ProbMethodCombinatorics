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


## 2026-09-15 — Re-check the lease *at the moment you retire a node*, not when you decide to

I closed #124 and deleted its declaration while it was **actively claimed with an open PR**.
Timeline: claimed 05:23, PR #141 opened 05:27, retired by me 05:32. I had checked lease activity
during an earlier review — when the node genuinely had no claim — and treated that check as still
valid several minutes and one PR later.

The roadmap already said "check lease activity before retiring a node". The check happened; it
was just stale by the time it was acted on. **A liveness check is only valid at the instant of
the destructive action**, and retiring a node is destructive to whoever holds it.

Concretely, before closing an issue or deleting a declaration:

- re-run `sync-leases` and re-read the issue's labels *in the same step* as the close;
- check for an open PR naming the issue (`gh pr list --search "closes #N"`), because a PR can
  exist before the label state settles;
- prefer reverting over arguing when you get it wrong — the contributor's branch is the thing
  with the work in it.

The recovery that worked: restore the declaration byte-identical to the PR's base commit, so the
contributor's branch merges through the normal flow instead of being cherry-picked or closed.
Their work stays theirs, and the protocol does the merge.


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

## 2026-09-15 — Commit messages: always a quoted heredoc, never `-m` with backticks

`git commit -m "... the [backtick]submission:[backtick] line ..."` runs the backticked text as a
command substitution, and the phrase silently vanishes from the message. It happened once here,
and the message could not be repaired: `main` is a protected branch, so `--force-with-lease` is
rejected — correctly, and I would not want it otherwise.

Use `git commit -F -` with a **quoted** heredoc (`<<'EOF'`), which suppresses all expansion. Every
other commit this session used that form; the one that used `-m` is the one that broke. The
mangled message stands, because rewriting shared history to fix prose is the wrong trade.


## 2026-09-15 — Lease age is the idle-turn diagnostic, and how to read it correctly

With every task claimed and no PRs open, the useful thing to check is **how long each claim has
been held**. It is the only visible form of the claim-and-release signal — `metrics struggle`
counts failed *PRs* and sees nothing here — and it distinguishes "needs help" from "needs
patience", which nothing else does.

    gh issue list --repo <repo> --state open --label choir/claimed --json number
    # then, per issue, the most recent comment containing `choir-lease`

**Read `createdAt` of the most recent lease comment.** Two traps, both checked:

- Heartbeat comments say "this comment is edited in place", which suggests `createdAt` is stale
  and `updatedAt` should be used instead. In practice they are equal, and the in-body
  "Lease refreshed …" timestamps can be *older* than the newest comment's creation, because they
  belong to earlier heartbeat comments. Taking the freshest of the three measures agrees with
  `createdAt` of the newest lease comment.
- `sync-leases` has its own staleness threshold and will not release a lease at 5 hours, so a
  stale-looking claim is not necessarily reclaimable. Do not wait for the label to change.

What to do with a long hold depends on the diagnostic order already recorded above —
**statement, then route, then decomposition.** On 2026-09-15 that ordering produced: #84
decomposed (statement and route already verified, so decomposition was what was left), and #90
given a targeted hint instead (its route is three lines; splitting it would not have helped, and
the real cost was an associativity transport with a precedent already in the file).

## 2026-09-16 — `choir` on PATH is the worker's checkout, not the orchestrator's

Run `choir update` after any change to Choir itself, or you are driving an older one.

`roadmap/graph.json`'s edges are derived from the build by `choir orch sync-graph`, which
also decides what stays hand-written: `ORCHESTRATOR.md` §1 and §3, and
`orchestrator-planning.md` § `roadmap/graph.json`.
