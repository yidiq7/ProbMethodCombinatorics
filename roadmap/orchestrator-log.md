# Operating lessons

How to run the loop on this project.  Mine, not a worker's: `skills/` is force-loaded
into every worker's context, so nothing here belongs there.

## A `private` lemma in another module is unreachable — pointing at it guarantees re-derivation

`integral_triangleCount` (#181) and `variance_triangleCount_le` (#182) both need the probability
that a prescribed set of pairs is entirely present in `G(n, p)`.  I told both tasks that
`Correlation.lean` "has the `binomialRandom_apply` / `setBernoulli` idiom for reasoning about
these".  It does — as `private theorem measurableSet_setOf_coe_subset`,
`private theorem setBernoulli_setOf_coe_subset` and `private theorem setBernoulli_cylinder`, plus
an inline `have hedges` inside `le_binomialRandom_cliqueFree_three`.

**Every one of those is unreachable from another module.**  So the pointer did not save work; it
guaranteed the work would be done again.  #184 wrote `binomialRandom_forall_mem_edgeSet`, #187 —
based one commit earlier — independently wrote `binomialRandom_setOf_subset_edgeSet` for the same
fact at a different cardinality, and `Correlation.lean` still holds the originals.  **Three copies
of one lemma**, with a fourth due in Chapter 8.

This corrects my own first diagnosis of this, which said the tell was that the route named a
`have` rather than a declaration.  That was too narrow: two of the three *are* top-level
declarations.  **The tell is visibility, not shape** — `private` crosses no module boundary, so a
`private` lemma in another file is exactly as unreachable as a `have` inside a proof.

- **Before pointing a task at a lemma, check it is `public` and in scope from the target's file.**
  `grep "theorem <name>"` is not enough; look for the `private` and for the import.
- **Sibling tasks in one file cannot see each other's helpers** either, being pinned to a common
  base — so whichever lands second re-derives unless the shared piece is supplied up front.
- Consolidation afterwards is orchestrator work and not publishable
  (`skills/conventions.md`), so getting this wrong is paid in orchestrator time either way.

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

## 2026-09-20 — `create-task` races its own intake workflow; set the labels by hand

Publishing #350-#353 with `--label` left all four without `choir/type:golf` and without an intake
acknowledgement.  I first concluded the `--label` flags were the cause and that publishing bare
would fix it.  **It does not.**  Publishing #358-#362 with no extra labels still produced
cancelled intake runs, and three of the five came out without the type label.

`issue-intake.yml` sets `concurrency: group: choir-intake-<issue number>` with
`cancel-in-progress: true`, and its job-level `if` skips `labeled` events for labels other than
`choir/available` / `choir/invalid`.  **A run whose only job skips still occupies the concurrency
group**, so it cancels whatever eligible run is in flight.  `create-task` itself applies
`choir/task` and `choir/available` as label operations after creating the issue, so the `opened`
run and the `labeled` runs race on every publish, with or without extra flags.  It is a coin
flip, which is why some issues get the label and some do not.

The task **record** is unaffected — `choir orch tasks` parses the body, and all five parsed
correctly with the right type and target.  What is lost is the `choir/type:*` label, which
`choir orch metrics` reads, and the intake ack comment.

- **After every `create-task`, read the labels back and set what is missing by hand.**
  `gh issue edit --add-label` is deterministic and costs nothing.  Do not trust publish order.
- Do not bother sequencing publishes to dodge it; the race is inside one issue's own events.
- The ack comment does not come back from a manual label add.  It costs nothing, but know that
  before hunting for it.

`.github/` is a protected path and this is a Choir-wide defect rather than a project one, so it
is not fixed here.  **Escalated to the overseer.**

## 2026-09-20 — Pick golf targets from the style audit, and only publish a nameable edit

Two habits, both of which paid immediately this pass.

**Run the gate's own audit instead of reading for length.**  `gate.verify.style.find_decl_spans`
over the corpus is about ten lines of Python and returns every declaration with its span; it
found 9 over the project's 200-line threshold out of 683, which is the candidate list.  Reading
files to find long proofs would have cost far more and missed some.

**Then refuse to publish anything without a specific edit.**  Of those 9, only 3 survived a read
for a *nameable* collapse; a fourth was the recorded-but-unpublished #350.  Five were skipped —
see the 2026-09-20 entry in `roadmap/README.md` for which and why.  The distinction that decides
it is almost always **can the fix live inside the proof body?**  `skills/conventions.md` forbids
a golf task from adding a declaration, so "extract this block as a private lemma" — which is what
the biggest duplications usually want — is orchestrator work, and a brief that asks for it is
mis-specified.  Split every candidate's findings into in-body and needs-a-declaration before
writing the task, and put the second list in the roadmap instead.

Corollary worth keeping: **the highest-value golf shape in this corpus is a Mathlib lemma
re-derived inline**, not internal repetition.  #351 deletes 36 lines that prove
`Real.cosh_le_exp_half_sq`, which this project already calls elsewhere.  Check candidates against
Mathlib before checking them against themselves.

## 2026-09-20 — "Mathlib has this lemma" is not the same as "the target file can see it"

#351's brief told the contributor to delete 36 lines proving `Real.cosh_le_exp_half_sq` and call
Mathlib's instead, and in the same breath said "leave every import untouched".  Those two
instructions were incompatible: `Concentration.lean` cannot reach
`Mathlib.Analysis.SpecialFunctions.Trigonometric.Series` through any of its six imports, so the
call does not elaborate without a new one.  **The contributor added the import and was right to;
the brief was wrong.**

Two pieces of evidence talked me into it, and neither was worth anything:

- The lemma is *used in this project*, at `Chernoff.lean:90`.  But `Chernoff.lean` imports
  `Trigonometric.Series` **directly**.  A sibling module's use says nothing about the target's
  closure.
- A subagent reported an import-closure BFS confirming it was in scope.  It was not, and I
  repeated the claim without running the check myself.

This is the same shape as the `private`-unreachability lesson at the top of this file — a name
that resolves somewhere in the project is assumed to resolve everywhere.  **The tell there was
visibility; the tell here is the import graph.**

Checking it costs nothing, but note two traps in this repo:

- Mathlib is on the **module system**.  Files open with `module` and `public import`, so a
  scanner matching `^import ` finds **zero** imports in a 45 KB Mathlib file and will report
  "not reachable" for everything.  Match `public import` too.
- Transitivity is not free under that system: follow every import out of the starting file, but
  only `public import` edges after that, since a plain import is not re-exported.

**When a task brief names a Mathlib lemma, say "add the import if it is not already in scope"**
rather than forbidding import changes outright.  The blanket "leave imports untouched" belongs in
a `prove` brief, where the header really is not the contributor's to change.

## 2026-09-20 — an inherited `sorryAx` needs a reduction block; a plain `golf` PR cannot carry one

#353 asked for a golf of `exists_shrunken_containers_of_many_triangles`, one of the four theorems
the README names as inheriting `sorryAx` from the §11.3 corner at `Containers.lean:2548`.  PR
#357 came back correct — eight checks green, three of five collapses landed, reviewed in full —
and `comparator` failed it with `illegal-axiom: 'sorryAx'`.

**Comparator's permitted set is conditional on the submission, not fixed.**
`gate/verify/comparator.py::permitted_axioms` grants `sorryAx` when either the PR declares a
reduction naming this exact target, or the project's sorry policy is `report`.  This project is
on the default `block`, so the reduction block is the only channel.

The same declaration passed comparator before, on **PR #159** (2026-09-15), which logged
`permitted: propext, Quot.sound, Classical.choice, sorryAx` and `outcome: match` — because its
body carried a `choir-reduction` block with
`parent: ProbMethodCombinatorics.exists_shrunken_containers_of_many_triangles` and a child of
`exists_containers_three_uniform`.  A golf PR carries no such block, so the same declaration,
with the same axiom closure, is refused.

**So the target is not unpublishable — an *ordinary* submission against it is.**  The axiom
closure has been unchanged since September; nothing about the golf introduced it, and no policy
was tightened.  What differs is only whether the submission declares the obligation it rests on.

**Before publishing a task, check the target against the inherited-`sorryAx` list**
(`exists_containers_fingerprint_three_uniform` and the four below it:
`exists_containers_three_uniform`, `exists_shrunken_containers_of_many_triangles`,
`exists_containers_triangleFree`, `card_triangleFreeGraphs_le`).  A `prove` task there works,
because the submission declares a reduction.  A `golf` task needs the brief to tell the
contributor to carry the parent's reduction block forward — it is an accurate description of the
submission, since the golfed proof still derives the target from the same open obligation — or it
must not be published at all.

`choir orch inventory scan` reports the `sorry` but not what inherits from it, so the README
table is the list to read.  The other audits do not catch this and are right not to:
`axiom-honesty` is **net-zero against base**, so an inherited axiom passes; `sorry-delta` counts
literal tokens in changed files; `trust-report` never blocks.  Only comparator reads the closure.

**Worth reporting upstream.**  A `golf` task on a legitimately conditional theorem has no clean
channel to say "this target's conditionality was ratified when it was proved".  Re-declaring a
reduction on a golf PR works and is honest, but it is the reduction mechanism used at a moment it
was not designed for.

**What I did about #357, recorded because it was not the submitter's edit.**  I appended the
`choir-reduction` block to the PR body myself, carrying #159's parent and child forward verbatim,
labelled in the body as orchestrator-added, and re-ran the comparator job.  No code was touched
and no check was overridden: comparator re-reads the PR body live
(`comparator_cli.py:302` fetches it from the API rather than the event payload), so the re-run is
a real audit under the policy that should have applied from the start.  The declaration is
accurate — the golfed proof derives the target from the same open obligation #159 named — but
authoring a submitter's reduction claim is the orchestrator reaching into a contributor's
submission, so it is logged rather than done quietly.  **The defect was my brief**, which asked
for a golf of a conditional target without telling the contributor to carry the block.
