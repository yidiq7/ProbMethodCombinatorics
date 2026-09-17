# Operating lessons

How to run the loop on this project.  Mine, not a worker's: `skills/` is force-loaded
into every worker's context, so nothing here belongs there.

## Publishing against machinery that exists only as a local `have` buys three copies of it

`integral_triangleCount` (#181) and `variance_triangleCount_le` (#182) both need the probability
that a prescribed set of pairs is entirely present in `G(n, p)`.  That computation existed — as an
inline `have hedges` inside `le_binomialRandom_cliqueFree_three` in `Correlation.lean`, where
nothing else can reach it.  I published both tasks pointing at it anyway.

Result: #184 wrote `binomialRandom_forall_mem_edgeSet`, #187 — whose base predates #184's merge —
independently wrote `binomialRandom_setOf_subset_edgeSet` for the same purpose at a different
cardinality, and `Correlation.lean` still has the original.  **Three copies of one lemma**, and a
fourth was coming in Chapter 8.

This is the duplicated-measure-layer mistake of #28–#30 repeated, and the tell was available
before publishing: **the route I wrote named a `have` rather than a declaration.**  If the prose
has to point at a step *inside* another proof, that step is not yet an interface, and publishing
two tasks against it means each one builds it.

- **Before publishing a batch, check that every lemma the route names is a top-level declaration.**
  If it is a local `have`, hoist it first — that is orchestrator work and it is cheaper than the
  consolidation afterwards.
- **Sibling tasks in one file will not see each other's helpers.**  They are pinned to a common
  base, so whichever lands second cannot use the first's work even though both end up in the same
  file.  Either sequence them or supply the shared piece up front.
- Consolidating afterwards is still mine, not a publishable task
  (`skills/conventions.md` is explicit), so the cost of getting this wrong is paid in orchestrator
  time either way.


## "Read its lease and sync the labels" is not the whole instruction — read the comment

**The worst process failure of this session.** A `choir-defect` report landed on #176 at 22:40
saying `exists_container_round` was false, with a kernel-checked counterexample.  The poller
reported `task #176 commented on — read its lease and sync the labels`.  I ran `sync-leases` and
moved on.  **I did not read it until 01:28, two hours and forty-eight minutes later.**

What that cost: two further nodes published on top of a broken interface, a long "correction"
sent to the contributor about an encoding hint they had never reached, and a statement repair
that then had to be threaded back through a *merged* proof.  The contributor had done everything
right — flagged it immediately, in the prescribed form, with a refutation that compiled.

The poller's wording is the trap.  It names the lease because that is the part it can act on,
but `ORCHESTRATOR.md` is explicit that a comment may be a `choir-defect` and that reading those
is part of the loop.  **On every "commented on", read the comment body, not just the lease block.**
It is one `gh issue view --json comments` and it is the difference between a five-minute fix and
three hours of building on sand.

Cheap detector, worth running on every such event:

    gh issue view <n> --repo <repo> --json comments \
      --jq '.comments[-1] | select(.body | test("choir-defect")) | .body'

## Verify the frame, not just the parts

`exists_container_round` was false because its double-count clause rests on
`3|Ae| = ∑_{v ∈ Av} deg_{Ae}(v)`, and that identity is really `∑_{e ∈ Ae} |e|` — equal to `3|Ae|`
only under 3-uniformity, which the clause did not require.  When I sketched satisfiability I
checked the three bounds in the split and never checked the quantity being split.  The bounds
were all correct and bounded the wrong left-hand side.

This is the same shape as the `2c√d` cut and the `degree_fromEdgeSet` form mismatch: **the
individual steps were right and the thing joining them was not.**  When writing a statement,
state the identity the argument turns on explicitly and check *it*, not only the estimates hanging
off it.


## A long hold with no PR: run the diagnostic on your own prose first

`#176` sat 2h47m with no PR while `#180` — a node I had sized as far larger, and which came back
at 788 lines — landed in about forty minutes.  **That asymmetry is the signal**, more than the
absolute hold time, and the operating order (statement, then route, then decomposition) found the
cause on the second step.

The statement was sound.  The *route I wrote in the prose* was not: I told the contributor that
`exists_greedy_rule`'s `ord`/`decode` scaffolding transposes "with `Ae`-degree in place of
`G`-degree".  It does not.  That weight is `n * (n - deg) + u` and depends on a graph degree being
at most `n`; a hypergraph degree reaches `|Ae| ≈ C(n,3)`, so `n - deg` truncates to zero and the
order collapses.  The fix is `n * (Ae.card - deg) + u`, which I verified compiles before sending
it.

Two things to carry forward:

- **When a task stalls, re-derive your own hint before assuming the contributor is stuck on the
  mathematics.**  A hint that names a specific existing proof to copy is exactly the kind that
  goes stale or fails to generalize, and it is the cheapest thing to re-check.
- **Compare hold times across nodes rather than against a threshold.**  `sync-leases` will not
  reclaim at this age and the absolute number said nothing; the comparison with a larger node
  finishing sooner is what made it worth looking.


## "Lemma X bridges this" — check the two forms match *syntactically* before writing it

I proved `degree_fromEdgeSet` in the `univ.filter fun u => s(v, u) ∈ F` form, then stated
`exists_fingerprint_of_dense_pairs`'s degree hypothesis over `F.filter fun e => v ∈ e`, and told
the contributor in the docstring and the task prose that the lemma "bridges the degree hypothesis
to the `SimpleGraph` form §11.2 wants".  The two cardinalities are equal but **not
definitionally**, so it cost them a `card_bij` plus the full handshake — about 28 lines my prose
implied were already done.

The failure is specific and repeatable: I wrote the bridging lemma and the consuming statement in
separate sittings and checked that they were *about* the same quantity rather than that one
`rw`s into the other.  **When prose promises that a named lemma discharges a hypothesis, put the
lemma's conclusion and the hypothesis side by side and confirm the rewrite, or say plainly which
connecting step the contributor still owns.**  Over-promising costs more than saying nothing: a
contributor who is told the bridge exists spends their first hour looking for the one-liner.

This is the same class of defect as the stale `Nat.succ_mul_choose_eq` and the "both ends are
comfortable" claim, except that those were inherited and this one I authored this session while
cataloguing the others.

**When it happens, promote the contributor's connecting lemmas into the file** rather than leaving
them inside one proof, so the next consumer does not pay again.


## `~/.local/bin/choir` is shared state and may point at a worker's clone

The `choir` on PATH is a one-line shim written by whichever Choir setup ran last. On this machine
it points into a **worker's** disposable per-session clone:

    _v="…/ProbMethodCombinatorics/worker-claude-1/choir/.venv/bin/choir"

so orchestrator commands run a worker's copy of Choir, not `~/.choir/checkout`. Two consequences:

- **`choir update` can report a checkout you are not running.** It syncs and prints the SHA of
  `~/.choir/checkout` while the PATH entry point executes something else. The two agreeing is
  luck, not a guarantee.
- **A worker clone is disposable.** If that session's directory is cleaned up, `choir` breaks for
  every role on the machine; the shim's own fallback prints "re-run Choir setup".

To run the checkout you actually maintain, invoke it directly:

    ~/.choir/checkout/.venv/bin/choir orch …

`orchestrator-init.sh` rewrites the shim to point at the orchestrator's checkout, but that is
shared state — it changes what every live worker session executes, so it is not a free fix while
workers are running. Check `head -3 ~/.local/bin/choir` at loop start; it costs nothing and tells
you whose code you are about to run.

## §11.3's held node owns a window of `d` about 10^8 wide

Worth stating with the real number, because "dense corner" understates it by orders of magnitude.
Node 4 of the §11.3 split can only invoke §11.2 while that theorem's own proviso holds. With
`M = max c 1` and `q = √d`: the run leaves `Δ(G) ≤ 2Mq`, the dichotomy's dense branch gives
`d_G ≥ q/(50M)`, so `c_G = 100M²` and `δ_G = 1/(100c_G) = 1/(10⁴M²)`. The obligation's hypothesis
is `d_G ≤ δ_G · n`, and `d_G` can be as large as `2Mq`, so the binding constraint is

    2·10⁴ · M³ · q ≤ n,    i.e.    d ≤ n² / (4·10⁸ · M⁶)

against an a priori bound of only `d < n²/2`. At `M = 1` the unpublished fifth node therefore owns
a range spanning a factor of **2·10⁸**, and it grows as `M⁶`.

**The exponent is `M³`, not `M¹`.** Three powers accumulate: one from `Δ(G) ≤ 2Mq`, one from the
density threshold's `1/(50M)`, and one from `c_G` being quadratic in `M`.

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

## Backticks in any double-quoted shell argument, not just commit messages

The `-m`-with-backticks trap below is not specific to `git commit`.  The same substitution ate a
phrase out of a `choir orch create-task --prose "…"` body: one backtick pair among dozens was
left unescaped, the shell ran `degree_fromEdgeSet` as a command, and the name vanished from the
published task, leaving "the bridge is , proved in the file".

**Use a quoted heredoc for any long prose argument**, the same `<<'EOF'` that commit messages
get, and pass it with `--body-file`/`-F -`.  Escaping backticks one by one across a few hundred
words does not scale, and the failure is silent — the command succeeds and the text is simply
shorter.

**Unlike a commit message, an issue body is repairable**: `gh issue view --json body` then
`gh issue edit --body-file` fixes it in place, and the task record re-parses afterwards.  Check
any long `--prose` for dropped phrases right after publishing; grepping the body for the names
you meant to cite takes seconds.

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
