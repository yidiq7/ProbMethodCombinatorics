# Operating lessons

How to run the loop on this project.  Mine, not a worker's: `skills/` is force-loaded
into every worker's context, so nothing here belongs there.

## 2026-09-16 — `set-difficulty` / `set-priority` right after `create-task` clobbers `choir/type:*`

Published #169, #170 and #171, then set labels immediately.  **#169 and #170 came out without
`choir/type:prove`; #171 kept it.**  The cause is a race, not a Choir bug: `create-task` opens the
issue, the issue-intake workflow adds the type label a few seconds later, and `set-difficulty` /
`set-priority` do a read-modify-write of the whole label set — so a write that reads the list
*before* intake lands drops the type label when it writes back.  #171 only survived because its two
label calls happened to straddle the workflow.

**Fix: set labels in the same pass as a later step, not immediately after `create-task`** — or
re-read labels after publishing a batch and repair.  Cheap to detect: list the new issues' labels
once after publishing and compare against each other, since the failure is silent and the board
still looks plausible (a task with no `choir/type:*` reads as a task, just untyped).

Repaired with `gh issue edit --add-label`, which is additive and cannot drop the others.

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

## 2026-09-15 — Commit messages: always a quoted heredoc, never `-m` with backticks

`git commit -m "... the [backtick]submission:[backtick] line ..."` runs the backticked text as a
command substitution, and the phrase silently vanishes from the message. It happened once here,
and the message could not be repaired: `main` is a protected branch, so `--force-with-lease` is
rejected — correctly, and I would not want it otherwise.

Use `git commit -F -` with a **quoted** heredoc (`<<'EOF'`), which suppresses all expansion. Every
other commit this session used that form; the one that used `-m` is the one that broke. The
mangled message stands, because rewriting shared history to fix prose is the wrong trade.

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
