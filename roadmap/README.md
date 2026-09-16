# Roadmap

## Goal

Formalize Yufei Zhao's *Probabilistic Methods in Combinatorics* (MIT 18.226, Fall 2022)
in Lean 4 with Mathlib.  The source is committed at
[`sources/mit18_226_f22_lec_full.pdf`](../sources/README.md) — the overseer chose to
redistribute it under MIT OCW's CC BY-NC-SA licence rather than link to it, so every
task can cite theorem numbers that contributors can look up directly.  PDF page numbers
run six ahead of printed page numbers.

## Route

The book is eleven chapters.  We formalize in book order, because the later chapters
genuinely rest on the earlier ones, and because the early chapters are where the
machinery this project needs — finite averaging, union bounds, alteration — gets built.

Groups, in order:

**"Proved" below means every *stated* declaration in the group is `sorry`-free.**  It does not
mean the chapter is exhausted — several groups deliberately leave material unstated, and each
group file has a "planned, not stated" section saying which and why.

| Group | Chapter | Stated declarations | Unstated remainder |
|---|---|---|---|
| [`introduction`](introduction.md) | 1 | **all proved** | — |
| [`expectation`](expectation.md) | 2 | **all proved** | some of §2 |
| [`alterations`](alterations.md) | 3 | **all proved** | — |
| [`second-moment`](second-moment.md) | 4 | **all proved** | asymptotics |
| [`chernoff`](chernoff.md) | 5 | **all proved** | — |
| [`local-lemma`](local-lemma.md) | 6 | **all proved** | — |
| [`correlation`](correlation.md) | 7 | **all proved** | — |
| [`janson`](janson.md) | 8 | **all proved** | — |
| [`concentration`](concentration.md) | 9 | **all proved** | martingales, Talagrand, TSP |
| [`entropy`](entropy.md) | 10 | **all proved** | Sidorenko, Kahn–Zhao, Steiner |
| [`containers`](containers.md) | 11 | 2 open | 11.1.3, 11.1.5, supersaturation |

**Ten of the eleven groups have every stated declaration proved.**  All remaining open work is in
Chapter 11, and the counts in this table are derived from `graph.json` (nodes with
`statement: formalized`, `proof: planned`), which `sync-graph --check` keeps honest:

**§11.2 is closed, kernel-verified.**  Theorems 11.2.1 (`exists_containers`) and 11.2.3
(`exists_containers_fingerprint`) and all three of 11.2.3's obligations depend on nothing but
`[propext, Classical.choice, Quot.sound]` — Mathlib's standard trio, **no `sorryAx`**.  Checked with
`#print axioms`, not inferred from the sorry count.

**The whole project is one obligation from `sorry`-free**, and it is deliberately unpublished:

| Obligation | Task | What rests on it |
|---|---|---|
| `exists_container_round` | [#176](https://github.com/yidiq7/ProbMethodCombinatorics/issues/176) | §11.3's run, and through it Theorem 11.3.1 |
| `exists_containers_fingerprint_three_uniform` | **not published — held** | Theorem 11.3.1, via #172's reduction |

It is 11.3.1's fingerprint form, and by its author's own account it carries all of that theorem's
mathematical content plus an open design question — so it fails the reduction contract's "closable
in one PR?" test.  [`containers.md`](containers.md) has the four-node split that should replace it,
why the fifth node is orchestrator research rather than a task, and the standing caution that the
interface must be **public** from its first commit.  Holding it is an imminent-replan hold, the one
sanctioned kind; do not publish it by reflex.

**Chapter 11 is the only chapter left, and it is the one the source does not prove** —
Theorems 11.2.1 and 11.3.1 are given as an algorithm plus a proof idea, with details deferred to
Morris' 2016 lecture notes.  So the remaining work is not "two more tasks of the usual kind":
these are research-level obligations where reductions, not single-PR proofs, are the honest
expectation ([`containers.md`](containers.md) says so at length, and records the `d ≤ 2δn`
transcription failure that made three statements false before it was caught).

**Everything in Chapter 1 §1.2 except Bollobás' two families theorem is already in
Mathlib** — Sperner (`IsAntichain.sperner`), LYM
(`Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose`) and Erdős–Ko–Rado
(`Finset.erdos_ko_rado`).  Those are upstream nodes, not tasks.  Turán's theorem is in
Mathlib too, but in its extremal-graph form (`SimpleGraph.IsTuranMaximal`), not the
edge-count bound the book proves, so the edge-count bound stays a task.

### Decisions that still bind

- **No measure theory in Chapters 1–3.** Every argument there is finite averaging, and the
  statements are phrased as pure existence/counting claims over `Finset` and `Fintype`
  so that proofs are counting arguments rather than `MeasureTheory` developments.
  **Chapter 4 is where that stops**: the second moment method is about a measure, Mathlib
  supplies `variance`, Chebyshev and `SimpleGraph.binomialRandom`, and a project-local
  re-implementation would be strictly worse. So `second-moment` is stated over
  `MeasureTheory.Measure` — and the line between the two conventions is the chapter
  boundary, not a matter of taste per node.
- **Chapter 4 is stated engine-first.** Its headline results are asymptotic (`whp`, `o(1)`,
  thresholds), which need both a worked `G(n,p)` API and a settled "whp" convention. The
  two finite inequalities everything runs on are stated now; the asymptotic nodes stay
  `planned` so the frontier stays provable. Revisit once both engine nodes have merged.
- **Colourings are `Bool`-valued.** `c : Fin n → Fin n → Bool` with an explicit symmetry
  hypothesis, rather than `Sym2`-indexed functions: it keeps decidability automatic and
  counting arguments direct.
- **Statements avoid new `Decidable` instances.** The gate's `verify-decide-instance`
  audit counts them, so every definition committed here is decidable by synthesis
  (`List.IsChain`, `Sym2.map` into `Sym2 Bool`, `Finset.filter` over `Bool` equalities).
- **`hk : 2 ≤ k` is kept on the Ramsey bounds** even though the arithmetic hypothesis
  makes `k < 2` vacuous, so the task is about the mathematics rather than degenerate
  cases.

## Log

- **2026-09-16 — §11.3's round interface is authored and its first node published (#176).**
  `IsContainerRound` and `exists_container_round` are in the file and build; the chapter's
  decomposition has started rather than remaining a plan.  Three things settled on the way, each
  of which had to be settled *before* publishing anything that mentions the interface:

  **The run's dichotomy is satisfiable in all four halting modes**, which the interface draft could
  not confirm and which was the actual blocker.  `R` is existentially returned and the halting mode
  is a function of the fingerprint through the replay, so `R` may be chosen per mode.  The branch
  that fires is decided uniformly by the handshake bound `|D| < |E|/(c√d)` on vertices deleted for
  forbidden-pair degree: either `E` is dense, or `D` is small and the run either order-retired
  enough vertices or exhausted `I` — and in that last case `I ⊆ S ∪ D`, whose size clears the
  container bound by two orders of magnitude.  Covering needs no case split, because the
  order-retired set is disjoint from `I`.

  **§11.2's headline theorems cannot be called by anything.**  Both bind `δ` existentially, and
  `∃ δ > 0` carries no lower bound, so no hypothesis in `c, d, n` can guarantee their proviso for
  whatever `δ` they return.  The δ-parametric obligations are the usable interface, which also
  makes the stability conjunct added to `exists_fingerprint_of_greedy_rule` load-bearing.

  **Why #176 is safe to publish while the run is unsettled:** `IsContainerRound`'s clause
  hypotheses *are* the run's invariants, passed in rather than assumed globally.  Strengthening the
  run's invariant set therefore cannot change what a rule must provide, so the interface can be
  frozen now.  For the same reason the interface relates `d` and `n` nowhere — that constraint
  belongs to the nodes that call §11.2.

  Two supporting lemmas landed as orchestrator vocabulary rather than inside one task's proof:
  `maxCodegree_mono` (the algorithm deletes edges, so 11.3.1's codegree hypotheses must transport)
  and `degree_fromEdgeSet` (the run accumulates a `Finset (Sym2 _)` because a `DecidableRel`
  instance cannot come from under an existential, while §11.2 takes a `SimpleGraph`).  The second
  also settled a statement question: the dense-branch node can state its degree hypothesis on
  `G.degree` directly.

- **2026-09-16 — the `choir/type:*` label race recurred on #176, as logged.**  Setting difficulty
  and priority straight after `create-task` dropped `choir/type:prove` again.  The logged remedy
  worked as written — `gh issue edit --add-label` is additive and cannot drop the others — and the
  diagnostic held: list the new issue's labels once after publishing, because an untyped task still
  reads as a task.

- **2026-09-16 — §11.2 is closed.  One sorry left in the project, and it is the held node.**
  #174 (`exists_fingerprint_of_greedy_rule`) merged — the last published obligation and the largest.
  **Kernel-checked rather than inferred:** `#print axioms` gives
  `[propext, Classical.choice, Quot.sound]` for `exists_containers`, `exists_containers_fingerprint`
  and all three obligations, with **no `sorryAx`**.  Theorems 11.2.1 and 11.2.3 are unconditional.
  `exists_containers_three_uniform` still carries `sorryAx`, correctly, from the held §11.3 node.

  **The stability conjunct I authored was free, exactly as claimed — and I checked that rather than
  assuming it.**  This was the conjunct most worth doubting, since I added it to the statement myself
  before publishing on the argument that an honest proof yields it.  It is discharged by
  `greedyRun_replay`, a real fuel induction whose step is the argument I had written out: the step's
  pick lies in the final `P ⊆ J`, so `J ∩ A_k` is nonempty and clause 2 of `IsGreedyRule` forces the
  same choice; the halt cases coincide.  Its hypotheses are clauses 1 and 2 verbatim and *not* the
  `kill` clauses — strictly weaker than `IsGreedyRule`, which is the right shape.

  **The check that mattered most was structural, not mathematical.**  A degenerate `S` (constant,
  `≡ ∅`, or `S I = I`) would satisfy stability trivially while gutting the other four conjuncts, and
  `A` secretly depending on `I` would hollow out the fingerprint form entirely.  Both are ruled out
  by *scope*: the `refine` supplies `S` and `A` as functions of `J` **before** `fun I hI => ?_`
  introduces `I`, so `A` is lexically incapable of closing over `I`.  That is worth more than any
  argument about the proof, and it is the kind of thing to look for first on a fingerprint statement.

  Four new declarations, all `private` and all `greedyRun*`; `private` is safe here because none
  appears in a *public* statement — the target's is frozen and mentions only the public
  `IsGreedyRule`, so the `comparator` hazard from earlier today cannot fire.  Budget obtained by a
  case split on `3d ≤ 2δn` rather than the `⌊2B/3⌋ + 1 ≤ B` route in the prose; equivalent, and
  `hdn : d ≤ δ*n` is genuinely spent in the second case.

- **2026-09-16 — the analytic core of 11.2.3 is proved (#173); two sorries left in the project.**
  `exists_greedy_rule` merged, 0 axioms / 2 sorries.  The `private`→public fix was the whole
  blocker: the branch went green on rebase with no content change, which confirms the diagnosis
  rather than leaving it a plausible story.

  **Zero new top-level declarations again** — seven of the nine PRs merged today had none.  The
  witnesses are built as three `obtain … : ∃ …` blocks with explicit witnesses, so the places a
  statement *could* have been smuggled are all discharged rather than assumed.  Two details worth
  keeping:
  - **The double count is honest in the conservative direction.**  Replacing `#(A \ kill A v)` by
    `n` inflates the upper bound on the degree sum and therefore *weakens* the lower bound on `t`;
    the `4` in `d*n - 4*c*d*δ*n` is two genuine losses of `2δn·cd`.  Worked by hand the proof gives
    `t ≳ 0.95*d` against a required `3*d/4` — established with slack, not by absorbing it.
  - **Clause 2 (stability) is proved in full strength**, over all `A T T'`, for the same `ord A`
    that `kill` and the clause-4 minimality argument use, with uniqueness from genuine injectivity
    of the weight.  That matters because #170's replay rests on exactly this clause; a subtly weaker
    version here would have been expensive one task later.
  - `pick`/`kill` are plain total functions rather than the `dite` the task prose suggested, and no
    clause rides on the junk branch.  Better than what was asked for.

- **2026-09-16 — PR bodies over-reported twice today.  Harmless individually; worth naming as a pattern.**
  #166's body miscounted the file's declarations (13 vs 15) and attributed a `sorry` to
  `exists_containers_triangleFree`, which carries none.  #173's body claimed "`c ≥ 1` is derived
  from `hsum` + `hdeg`" when nothing in the diff derives, mentions or uses it — the proof doesn't
  need it, since `δ ≤ 1/(100c)` gives `c·δ ≤ 1/100` for any `c > 0`.  Neither affected the
  mathematics and neither was grounds to withhold a merge.

  **The reason to care is economic.**  Both authors were unusually careful elsewhere, and their
  self-reports are what made these reviews cheap — #173's clause-by-clause account saved most of
  the reading.  A verification claim that turns out not to correspond to anything in the diff
  devalues the whole report, because the next reader has to check the claims they would otherwise
  have taken.  Recorded in `skills/orchestrator-notes.md` as: claim what you did, not what would
  have been reassuring.

- **2026-09-16 — Theorem 11.3.1 proved from one obligation (#172), accepted via *amend*, and its child held unpublished.**
  Both container theorems are now proved; all three remaining sorries are obligations beneath them.
  I merged #172 rather than rejecting it because the ~34 lines of counting assembly are real,
  kernel-checked content that has to exist either way — but I did **not** publish its child, and the
  reasoning is worth keeping.

  **The reduction contract's four questions did not all pass.**  The child says the right thing (its
  hypothesis list is token-identical to the parent's, verified by diffing with the decl names
  normalised away) and the split is formally real (child ⟹ parent by genuine counting, parent ⇏
  child).  But **"is each child closable in one PR?" is a clear no**, and that alone decides
  publication.  An independent review and the PR's own author converged on it separately: the child
  carries all of 11.3.1's mathematical content, plus the open `√d ≳ n` corner, plus — in the corner —
  a *strengthening* over the parent.  Publishing it would hand someone the hardest statement in the
  project with a known-open design question inside it.

  **The corner is now localized, which is the session's most useful piece of new mathematics.**  It
  is not a vibe about `√d ≳ n`; it is `exists_containers`' own proviso failing.  That theorem at
  parameter `c_G` yields `δ_G = 1/(100 · max c_G 1)` and demands `d_G ≤ 2 δ_G n = n/(50 · max c_G 1)`,
  while at termination `d_G = 2e(G)/n = Ω(√d)` — so the subroutine is applicable only for
  `d = O(n²/c_G²)`, against an a priori bound of only `d < n²/2`.  **A `Θ(n²)` window where the
  graph container theorem cannot be applied to `G` at all.**  I verified the δ and the proviso in the
  source.  It is the same `d ≤ 2δn` proviso that made `exists_containers` false before `1e4659a`,
  biting one chapter later — which is the third time that single proviso has driven a design decision
  in this project.

  **Two things I checked rather than assumed, both of which mattered:**
  - **`sync-graph` did not over-record the cross-chapter edge.**  `hypergraph_container`'s
    `proof_uses` came back as the child alone, not `graph_container` — correct, since #172's proof
    calls `exists_containers` nowhere.  Had it recorded that edge, a chapter resting on an open proof
    would compute as complete.  Note this *replaced* a hand-written planned edge to `graph_container`;
    the intended dependency now lives in `containers.md`'s prose and will reappear as node 4 of the
    real split.
  - **`IsGreedyRule` survived the merge public.**  #172's base was two commits behind and one of
    those commits edits the same file, which is the #146 shape exactly.  Confirmed post-merge.

  Amended in the file: the new theorem had been inserted *above* the `### 11.3` header (so 11.3's
  fingerprint form was filed under §11.2), and its docstring asserted "both ends are comfortable",
  conflating "budget never collapses" (proved) with "budget ≥ 2" (false for `n²/4 < d`).  Both fixed.

  **One decision deliberately deferred**, and safe only because the node is unpublished: whether the
  child carries §11.2's stability conjunct.  Nothing needs it today.  Reshaping an unpublished node is
  free; changing a published task's statement is not.

- **2026-09-16 — the dense corner is proved (#175), and publishing it over its author's objection was right.**
  `exists_dense_fingerprint` merged, 0 axioms / 3 sorries.  The contributor followed the greedy-order
  route published in the task prose: `hstep` states the extension lemma with `P` universal and no
  extra side condition, the double count is the honest `P`–`Pᶜ` edge count in `ℕ`
  (`Finset.sum_sdiff` + `card_sdiff_add_card_inter`, with the factor 2 present), `c ≥ 1` is derived
  from `hsum` + `hdeg` rather than assumed, and the `⌈δn⌉` boundary uses `Nat.lt_ceil` in the
  direction that gives the strict real bound at the last step.  **Zero new top-level declarations** —
  the whole argument is inline, so there is no worker-authored statement to audit.

  **Worth stating plainly: the reduction's author believed this obligation might be false and asked
  that it not be published, and they were wrong.**  Verifying the mathematics myself before
  overriding them was the step that made the override legitimate rather than reckless — and the
  contributor then closed it in one PR.  The cost of having deferred to the author's reservation
  would have been an indefinite hold on a provable node.

- **2026-09-16 — `private` in a published statement silently disables `comparator`.  My mistake, and the most expensive one of the session.**
  PRs #173 and #174 both failed `comparator` with `statement-mismatch` while every other check,
  `statement-immutability` included, was green — and neither diff touched a statement.  Cause:
  Lean 4 mangles private names with the **module path** (verified directly — `private def
  myPrivateFoo` compiles to `_private._stdin.0.myPrivateFoo`), and comparator builds the base tree
  under a `ChoirBase.` module prefix, so challenge and solution reference different constants for
  `IsGreedyRule` and the statements cannot match as kernel terms for *any* diff.

  **`gate/verify/comparator.py`'s header states the assumption that fails**: the mapping is argued
  sound because "Renaming modules never renames *declarations* (Lean decl names come from
  namespaces, not file paths)".  True of public declarations only.  Reported to the overseer as an
  upstream Choir bug; not patched locally, since `~/.choir/checkout` is shared by every project on
  this machine.

  **I made this hole this morning**, adopting `IsGreedyRule` as `private` when ratifying #166 on the
  reasoning that both consumers lived in one file.  That reasoning was about namespace tidiness and
  it cost the project its strongest gate on two targets.  Now public (`eda593c`); no proof text
  changed, so both PRs need only a rebase, which they were told.
  **Rule: anything reachable from a published statement is public, however local it looks.**
  The tell, if it recurs: `comparator` red, `statement-immutability` green, no statement in the diff.

- **2026-09-16 — `choir worker heartbeat` is a no-op; a contributor found it and I confirmed it.**
  `cmd_heartbeat` passes no `session`, its subparser has no `--session` and does not resolve the
  workspace, and the holder check compares the `(login, session)` *pair* against a lease whose
  `holder_session` is always a real id — so it returns before writing, every time.  Consequences
  recorded for workers in `skills/orchestrator-notes.md`: **`refreshed: false` carries no
  information**, and a lease goes stale at 24h despite correct heartbeating, so a stale-reclaim can
  land on actively-worked code.  Upstream fix is the overseer's call.

- **2026-09-16 — Theorem 11.2.3 is proved as a three-way reduction (#166); its "unsettled" obligation
  was not unsettled, and I published it.**
  Merged PR #166, which proves `exists_containers_fingerprint` from `exists_greedy_rule`,
  `exists_fingerprint_of_greedy_rule` and `exists_dense_fingerprint`, now tasks #169, #170 and #171.
  Inventory went 2 → 4 sorries, which is the reduction working: one declaration became three, each
  individually claimable, and §11.2's assembly is settled.

  **The author asked me not to publish obligation 3, and I overrode that.**  They flagged
  `exists_dense_fingerprint` as neither provable nor refutable — an open window of relative width
  `(c-1)δ` above `δn` — and said publishing it would risk a contributor's budget on a possibly-false
  statement.  That reservation was well-motivated (two of their earlier reductions were rejected for
  false obligations) but it was wrong.  **The window is an artifact of building the order by degree.**
  The statement only asks for *some* order in which every vertex has `|N(v) ∪ Pred(v)| ≥ δn`; built
  greedily it always exists, because for `j < δn` and `|P| = j` some `v ∉ P` has
  `|N(v) \ P| ≥ δn - j` — otherwise `n(d - δn) < j(2cd + j - n - δn)`, positive on the left and
  `≤ 0` on the right once `c ≥ 1` forces `cd ≤ n/50`.

  **I did not take the reviewer's word for this.**  The algebra identity and the contradiction were
  machine-checked numerically across 300,000 points of the feasible dense regime (the normalized
  quantity `(2cd + j - n - δn)/n` maxes out near `-0.96`), and the construction was checked by hand.
  Only then did I rewrite the docstring, publish the task, and put the route in its prose so the
  contributor transcribes a verified argument rather than searching.

  **The lesson, stated next to its mirror image.**  `roadmap/containers.md` already records three
  statements published *false* and believed true (the `d ≤ 2δn` proviso).  This is the first
  published *true* and believed false.  Both came from reasoning about one construction instead of
  about the statement.  The author's own evidence pointed the right way and they misread it: they had
  probed clique unions, clique-plus-matching and Hi/Lo degree sequences for a counterexample and
  found that every one was covered.  **Repeated failure to refute is evidence the statement is true,
  not evidence the corner is hard.**

  **Also decided rather than deferred:** `IsGreedyRule`, the `private def` the reduction introduced,
  is adopted as orchestrator-owned vocabulary and stays `private` (both consumers are in this file;
  §11.3 needs a hypergraph analogue, not this predicate), and both tasks are told it is frozen.  And
  the stability conjunct `∀ J, S I ⊆ J → J ⊆ I → S J = S I` went onto obligation 2's conclusion
  **before** publishing, not after it lands as the author proposed — I verified it is free from the
  interface, and changing a published task's statement is what invites the stale-workspace reverts
  recorded in `skills/orchestrator-notes.md`.  The parent still composes; 3257 jobs, four expected
  sorries.

- **2026-09-16 — a conflation I introduced and then caught: there are two "dense corners" in Chapter 11.**
  While writing the above I claimed this file had been wrong to call the dense corner "the open design
  question".  It was not.  **§11.2's corner is `δn < d ≤ 2δn`** (graph containers, now closed);
  **§11.3's is `√d ≳ n`** on #99, where the parent's own budget `⌊n/√d⌋₊` is only guaranteed `≥ 1`,
  and that one is still open.  `containers.md` now distinguishes them explicitly at both mentions.
  Worth recording because the two corners have the same name, the same shape, and opposite status.

- **2026-09-16 — Chapter 10 is closed.  Two sorries left in the project, both in Chapter 11.**
  #167 (`entropy_le_logb_card`) and #168 (`shearer_triple`) merged, taking the inventory to
  **2 sorries, 0 axioms**.  `Entropy.lean` now carries none, and **six** Chapter 10 theorems went
  from proved-modulo-`sorryAx` to unconditional in those two merges: #167 released Brégman's
  per-order bound, Brégman–Minc, Shearer's family form and the triangle-intersecting bound, and
  #168 released Loomis–Whitney, which needed both.

  **Both PRs added zero new top-level declarations** — the fifth and sixth of seven this session
  to do so.  #167 is the clearest case yet of a task whose whole content was already in the file:
  the proof is four `have`s restricting the entropy sum from `univ` to the support finset `A` and
  then one `exact` onto the base lemma `sum_negMulLogb_le_logb_card`, which was proved centrally
  long ago.  #168 was 12 lines, exactly the shape `orchestrator-log.md` predicted when it chose a
  hint over decomposition on 2026-09-15 ("its route is three lines … the real cost was an
  associativity transport with a precedent already in the file") — 5 of the 12 lines are that
  transport.  **That prediction being right is the strongest evidence so far that the
  statement-then-route-then-decomposition diagnostic order is the correct one.**

  The multiplicity-2 in `shearer_triple` is worth recording because it is where a wrong-but-
  compiling proof would have come from: it falls out of an *exact* cancellation of `H(Z)` between
  subadditivity (`H(X,Y,Z) ≤ H(X,Y) + H(Z)`) and the file's submodularity lemma
  (`H(X,Y,Z) + H(Z) ≤ H(X,Z) + H(Y,Z)`), not from absorbing a nonnegativity slack.  Neither PR
  instantiated the general `shearer`, and neither re-derived it — the route was sanctioned in the
  task prose precisely so #90 would not wait on it.

- **2026-09-16 — `roadmap/entropy.md` was stale in two ways that would have cost a contributor.**
  Fixed both, and worth generalizing.  It listed `shearer_family`, `bregman_chain_rule` and
  `bregman_greedy_bound` under "Obligations left behind by reductions" — **all three have been
  proved for some time**, so a contributor reading the group file for available work would have
  found three phantom obligations.  It also told them a Mathlib search turns up `measureEntropy`
  (Kolmogorov–Sinai) to be ruled out; at the pinned Mathlib there is **no `measureEntropy` at
  all**.  `Mathlib/InformationTheory/` holds only `Coding/`, `Hamming.lean` and
  `KullbackLeibler/`.

  **A group file's "what's open" section is a second copy of state that `graph.json` already
  holds, and it drifts.**  The counts in this README are now derived from the graph rather than
  written by hand; the per-group prose is not, and that is where to look next time something reads
  wrong.

- **2026-09-16 — all four open tasks re-pinned `fa3909e` → `b338588`; #99 was the one that needed it.**
  The rule in `skills/orchestrator-notes.md` is that a stale pin is harmless unless something merged
  into the *target file*, so I checked rather than re-pinning reflexively.  `Entropy.lean` (#84, #90)
  was untouched — those pins were harmless.  **`Containers.lean` was not**: PR #159 added 587 lines
  to it (proving `exists_shrunken_containers_of_many_triangles`) *after* `fa3909e`, so a worker
  claiming #99 would have built against the placeholder version and had `sorry-delta` reject their
  branch for reverting a declaration their diff never touched — the exact confusing failure the
  notes describe, on the project's hardest task.  Re-pinned all four for consistency; each record
  was re-read through the intake parser afterwards to confirm it still round-trips.

  **Generalization: the pin-staleness check is per *file*, and the file that matters is the one a
  long-lived task targets.**  Chapters 10 and 11 are where tasks sit open longest, so they are
  exactly where pins rot unnoticed while the rest of the project moves.

- **2026-09-16 — five proofs merged; the trust boundary is down to four sorries in two chapters.**
  Reviewed and merged #160 (`prob_notMem_le_pow_of_isUpperSet`), #162 (`card_le_of_tetrahedronFree`),
  #163 (`measure_martingale_sub_ge_le`), #164 (`exists_signs_sum_ge`) and #165
  (`le_card_of_distinctSubsetSums`).  Inventory went **9 sorries → 4, axioms 0 → 0**; the remaining
  four are `exists_containers_fingerprint` and `exists_containers_three_uniform` (Ch. 11) and
  `entropy_le_logb_card` and `shearer_triple` (Ch. 10).  With these, **Chapters 2, 4, 7 and 9 have
  no `sorry` left in any stated declaration** — the README table above claimed that before it was
  true, and is now accurate for those rows.

  **What stage-two review actually turned on, recorded because it generalizes.**  Four of the five
  diffs (#160, #163, #164, #165) added **zero new top-level declarations** — a single `sorry`
  replaced by a proof body whose every auxiliary fact is a local `have`.  That makes the review
  surface *empty* in the one place the kernel cannot help: with the target statement identical to
  base as a kernel term, a clean axiom closure and no net-new sorries, a local `have` cannot smuggle
  anything, because the kernel discharged it against a fixed goal.  **Check the new-declaration
  count first; it tells you how much judgment the PR actually needs.**  #164 was the exception with
  ten new declarations (including `private def signVec`), and the argument that settled it is the
  same one in a different key: all ten are `private` and fully proved, and the target's statement
  never mentions them, so a wrong helper could only be unprovable, not load-bearing.

  Only #162 added helpers with hypotheses, and both take the target's own `h3`/`hfree` verbatim —
  nothing added, and `card_le_card_filter_superset` is a *lower* bound sitting on the low side of
  the double count, so it cannot hide a weakening.

- **2026-09-16 — three prose defects the reviews surfaced; all are orchestrator work, none blocked a merge.**
  Recorded so they are fixed rather than rediscovered:
  - **`Nat.succ_mul_choose_eq` does not exist at this pin.**  It is named in `Expectation.lean`'s
    §2.4 docstring (~line 331) and in the task prose for #157 as "the Mathlib-side lever".  The
    real name is **`Nat.add_one_mul_choose_eq`** (`Mathlib/Data/Nat/Choose/Basic.lean`); it was
    renamed, not removed.  Two contributors independently re-derived it by hand because the
    docstring sent them looking for a name that is not there.
  - **`SecondMoment.lean`'s target docstring now misdescribes its own proof.**  It still gives the
    off-by-one route ("the open interval … contains at most `2n√k` integers") and names
    `prob_eq_zero_le_variance_div_sq` / `variance_sum_indicator_le` as the engine; #165 uses
    neither, applying Chebyshev at `(7/8)n√k` with a `2c+1` count and a `k ≤ 5` pigeonhole branch.
  - **`skills/conventions.md` claims `open scoped ENNReal` is in the header of every
    measure-theoretic file.**  It is not in `SecondMoment.lean`.  The convention doc is the stale
    thing, not the PR.

  The pattern: **every one of these is a stale claim in prose that a worker then paid for.**  Proof
  routes named in a docstring age as fast as the proofs do, and a wrong lemma name costs a
  contributor real budget.

- **2026-09-16 — gate overlay resynced to Choir `258a6d3` (protocol 8 → 8).**
  The overlay was pinned at Choir `253d364` and 27 commits behind; `choir update` had already
  confirmed this machine's checkout was at `origin/main`, which is a *different* artifact — the
  in-repo overlay does not follow it, only `upgrade-project.sh` moves it.  Checked before running
  it that `gate/checks.py` was **byte-identical** across those 27 commits, so `REQUIRED_PRESENT`
  gained nothing and no open PR could be stranded by required-but-absent; the changes were confined
  to `gate/provers/{base,deps,lean4}.py` plus new `orchestrator/graph/`, i.e. **`sync-graph`'s
  dependency-edge derivation, not PR audits.**  That is why the six PRs open at the time needed no
  re-auditing.  `verify-pr.yml` was left untouched (overseer-adapted); branch-protection required
  contexts still match.  Commit `05c9542`.

- **2026-09-16 — the loop is self-driving at AUTO; run the poller in the background, never in the foreground.**
  `choir orch poll` blocks for up to `max_wait_seconds`, and a long-lived *foreground* process is
  what the OOM killer takes first while contributor agents' `lean` builds spike to 1–2 GB each.
  That is an argument against blocking the session on it, not against polling:

      # started with the harness's background mechanism, not left in the foreground
      choir orch --repo yidiq7/ProbMethodCombinatorics --prover lean4 poll

  Backgrounded, the process exiting *is* the wake-up — on a change, on a code-3 quiet timeout, or
  on being killed — and the orchestrator reacts and restarts it.  A killed poller becomes a
  wake-up rather than a silent hang, which is what made the foreground version untenable.

  **Do not read the OOM history as licence to stop and wait for the overseer.**  `ORCHESTRATOR.md`
  § Automation levels is explicit that at AUTO the orchestrator runs the whole loop itself and that
  "stopping to ask permission to keep going is a bug at those levels".  The only escalations are a
  new axiom, a statement that looks wrong, and a policy change — and even then the rest of the work
  continues meanwhile.

  **Confirmed, with one caveat.**  The backgrounded poller was killed for low memory on the first
  run — and the kill arrived as a notification, so the mechanism behaves as claimed: a killed
  poller is a wake-up, not a hang.  The caveat is that it is pointless to hold one open while doing
  memory-heavy work yourself.  Repeated `lake build`s in this checkout are what tightens memory, so
  start the poller when you are otherwise idle and skip it while you are building.

  **When the board is empty, the bottleneck is usually the orchestrator, not the contributors.**
  A poller finds nothing while the next move is authoring an interface or publishing a node, and
  waiting on it looks like patience when it is idleness.  Check what the plan says is ready before
  reaching for `poll`.

- **2026-09-13 — the duplicated measure layer is fully retired.**  Golfs #62, #69 and #70
  removed 148, 65 and 69 lines respectively; `LocalLemma.lean` went from ~1150 to ~866 and
  now contains exactly one construction of the uniform two-colouring measure, used by all
  three applications through `uniformColoring`.  **The sequencing lesson stands**: the need
  for this interface was visible when #28 was written, and publishing #28–#30 against
  machinery none of them had cost three contributors a duplicated construction each plus
  three golf tasks.  Author the interface first.

- **2026-09-13 — the five remaining statements were audited for the degenerate-input defect
  and are sound.**  Done proactively after three corrections rather than waiting for a fourth
  worker to bounce.  `exists_bad_card_lt_and_indepNum_le`, `exists_conflictFree_of_card_le`
  and `exists_nearly_equiangular` are already `∀ n ≥ n₀` / `∀ k ≥ k₀`, so they have no bottom
  end.  `exists_isDominating_card_le` is fine at `V = ∅` (take `U = ∅`; both sides are `0`),
  and its `hdeg` is unsatisfiable when `δ > n - 1`, so those cases are vacuous rather than
  false.  `exists_toSign_abs_sum_le` is vacuous at `n = 0` (only one `Finset (Fin 0)` exists,
  so `2 ≤ F.card` fails) and comfortably true at `n = 1, 2`; note its bound `2√(n log m)`
  exceeds `n` whenever `m = 2ⁿ`, so the content is entirely in the regime `m ≪ 2ⁿ`.

- **2026-09-13 — a third statement was false at degenerate `n`; corrected.**
  `exists_nearly_equiangular` claimed its bound for every `n`.  False at `n = 0` (no unit
  vector exists, yet `2 ^ (c * 0) = 1` forces `S` non-empty — machine-checked) and at `n = 1`
  for small `ε` (only `±1` are unit, inner product `-1`).  Now `∃ c n₀, ∀ n ≥ n₀`.
  **Three of the statements I authored have been false at the bottom end** (both Chernoff
  bounds, now this).  The cause is the same each time: transcribing a book statement that says
  "for every `n`" when the mathematics is asymptotic.  **Rule: when a statement's bound grows
  with `n`, check `n = 0` and `n = 1` before publishing it.**
  The tell was again behavioural — #24 had one claim and one release with no PR, and
  `metrics struggle` reports nothing for abandoned claims.  **Read the statement of any task
  that gets released without a PR.**

- **2026-09-13 — first golf landed; two measure-layer copies left.**  PR #62 rewrote
  `twoColorable_of_regular` through `twoColorable_of_inter_card_le`: **163 lines removed, 15
  added.**  Golf tasks #54 and #55 will take the other two copies through the extracted
  `uniformColoring` layer.
- **2026-09-13 — this machine is memory-constrained.**  The contributor agents build Lean
  locally, several `lean` processes at ~1.3 GB each, and a background poller was killed under
  the pressure.  **Don't run `lake build` in the orchestrator checkout except to verify a
  statement being authored** — CI builds every PR anyway, and the local build competes with the
  workers actually producing proofs.

- **2026-09-13 — the Chernoff diagnosis paid off, and the reduction contract closed itself.**
  #21 had been abandoned twice; correcting the false statement and pointing at Mathlib's
  `Real.cosh_le_exp_half_sq` unblocked it, and PR #61 proved it on the next attempt by exactly
  the route given.  Checked afterwards with `#print axioms`: both
  `card_filter_le_exp_mul` and `card_filter_abs_le_exp_mul` now depend only on
  `propext, Classical.choice, Quot.sound`.  **The two-sided bound merged in #40 as a declared
  reduction and became unconditionally proved automatically when its obligation landed** — no
  resubmission, no bookkeeping.  Worth remembering when weighing whether to accept a reduction.
  (Note: `#print axioms` reads the built olean, so rebuild after pulling before trusting it.)

- **2026-09-13 — two published statements were false; both corrected.**
  `card_filter_le_exp_mul` and `card_filter_abs_le_exp_mul` (Chernoff, one- and two-sided)
  omitted `0 < n`.  At `n = 0` the empty sum is `0` and the threshold `λ √0` is `0`, so the
  single sign sequence satisfies the condition while the bound is below `1`.  **The tell was
  behavioural, not a failed check:** #21 was claimed and released twice with no PR, and
  `metrics struggle` stays empty for abandoned claims, so only reading the statement found it.
  A machine-checked counterexample was built before either statement was touched.
  `card_filter_abs_le_exp_mul` merged earlier (#40) as a *declared reduction* on the false
  lemma, so nothing was ever claimed to be unconditionally proved — the reduction contract did
  its job.  Both statements now carry `0 < n`; #40's merged proof threads it through and the
  build is clean.  **This is an overseer-visible change: the project's Chernoff bounds now say
  slightly less than they did.**  Anything downstream must dispose of `n = 0` itself; #23
  (discrepancy) is unaffected because its `2 ≤ F.card` is unsatisfiable at `n = 0`.

- **2026-09-13 — the uniform two-colouring measure is duplicated, and that is my fault.**
  #49 and #50 each build it from scratch in `LocalLemma.lean` (`Measure.pi` over `Bool`, the
  cylinder probability, disjoint-support independence via `iIndepFun_pi`, the dependency
  graph) — about 100 lines twice, in an 846-line file.  #28's prose said that machinery was
  "worth stating as their own declarations" but left it to contributors; **a definition other
  tasks depend on is an interface and should have been authored centrally before those tasks
  were published.**  Mitigations: golf task #52 rewrites `twoColorable_of_regular` to go
  through `twoColorable_of_inter_card_le`, which removes one copy; #30's prose now points at
  the template and asks its holder to flag rather than write a third copy.  **If #30 needs
  more than the `key` lemma, extract the layer centrally instead.**

- **2026-09-13 — re-pinning is necessary but not sufficient; warn claimed tasks too.**
  Stale-pin reverts hit twice (#42, #48).  Re-pinning an issue does not help a worker whose
  workspace already exists — that tree was cloned at the old pin.  **After merging, comment on
  every open *claimed* task whose `target_file` matches a file the merge touched**, telling the
  holder to rebase.  Cheap to do: `choir orch task <n>` gives `target_file`, and the merge's
  own diff gives the files.  Done for #12, #15, #29 on this pass.

- **2026-09-13 — Chapter 1 §1.1 is closed and the local lemma is proved.**  PRs #41–#44
  landed the general local lemma with its induction step, Ramsey's theorem with the
  off-diagonal Erdős–Szekeres statement, `lt_ramseyNumber`, and the symmetric local lemma.
  Every Ramsey node now has a real proof.
  **Golf candidate:** `lovasz_local_lemma_symmetric` (PR #44) re-derives the general form
  inline as a `have`, duplicating `lovasz_local_lemma`.  That was correct when written — #44
  was opened 73 seconds before #41 merged, so calling the general form would have pulled in
  `sorryAx` — but it should be rewritten to apply `lovasz_local_lemma` at the constant weight
  `1/(d+2)`.  Publish the golf task once Chapter 6 is quiet, not while #27–#30 are in flight.
  Note the weight `1/(d+2)` rather than the book's `1/(d+1)`: the latter is `1` at `d = 0` and
  so inadmissible.  Keep that when golfing.

- **2026-09-13 — open tasks were re-pinned to `f1497a65`, and must be kept current.**
  PR #42 was built at task #7's pin `dcaf5da`, which predates #32 and #33; its branch still
  held the placeholder versions of `RamseyProperty.mono` and
  `exists_coloring_no_isMonochromatic`, so merging it would have reverted two proved
  theorems.  `sorry-delta` caught it (`base 2 → head 3`) and the contributor's diff looked
  clean, which is what makes the failure confusing.  **A worker's workspace is built at the
  pinned commit and workers do not rebase — so keeping pins current is this role's job.**
  All 18 open tasks re-pinned; the two claimed ones were told to rebase.  Re-pin after every
  batch of merges, or at minimum whenever a merge lands in a file some open task targets.
  PR #40 landed as the project's first **reduction**, naming `card_filter_le_exp_mul` (#21)
  as its open obligation — ratified, no new nodes, since the child is already a task.

- **2026-09-13 — a proof that leans on an unproved sibling must declare a reduction.**
  PR #40 (two-sided Chernoff, task #22) was mathematically correct and failed `comparator`
  with `illegal-axiom`: it calls `card_filter_le_exp_mul`, still a placeholder, so `sorryAx`
  entered the target's axiom closure.  `sorry-delta` passed, which makes the failure
  look surprising.  This is **designed** — under `sorry = block` comparator refuses `sorryAx`
  on an ordinary submission precisely so a green gate means *unconditionally proved* —
  and the sanctioned route is a `choir-reduction` block, for which `sorryAx` is permitted.
  Seven open tasks (#7, #23, #26, #27, #28, #29, #30) carried task prose that told
  contributors to use an unproved dependency's statement without mentioning this; all are
  corrected in place, and the rule is in `skills/orchestrator-notes.md`.
  **Do not "fix" this by moving the project to `sorry = report`** — that would permit
  `sorryAx` everywhere and destroy exactly the guarantee the policy buys.
  Planning consequence: when a group's nodes form a chain, publishing them all at once is
  still right, but expect the dependents to land as reductions, or to land after their
  dependency merges.

- **2026-09-12 — overlay resynced to Choir `e8a1d24`.** Protocol still 8; the change touched
  only `scripts/` (iCloud-sync detection and environment relocation in `orchestrator-init.sh`
  and `join.sh`) plus `client/update.py`, so no gate behaviour moved and no open work was
  affected.  Contributors already set up should run `choir worker update` to pick up the new
  `join.sh`.
- **2026-09-12 — the gate is confirmed working end to end (PR #31).** The repo's first pull
  request, a README-only change, ran all nine checks green: `rebuild` 2m17s (the Mathlib
  cache step works), `comparator` 1m12s (the comparator builds at the `v4.33.0` pin and
  runs), `trust-report` 2m23s, and the six string-level audits in about 7s each.  Merged
  through `choir orch merge`, so the preflight is exercised too.  **Still unverified: the
  fork-PR path** — a same-repo branch raises no held workflow runs, so the first genuine
  contributor PR is the first test of the approval sweep.
- **2026-09-12 — overlay upgraded.** Protocol 8 → 8 (unchanged), Choir commit
  `1c85185` → `6b40b47`; `gate/checks.py` and so `REQUIRED_PRESENT` were unchanged, and the
  fingerprint guard passed, so no PR was at risk of the absent-check refusal.
  `verify-pr.yml` was left untouched (it carries this project's Mathlib cache step).
  Branch protection's required contexts were confirmed to match.

- **2026-09-12 — project bootstrapped.** Toolchain pinned to `leanprover/lean4:v4.33.0`
  (Mathlib `v4.33.0`): the newest release the comparator tags, so the kernel statement
  gate runs on every PR.  Lean's own newest is `v4.33.1`, which the comparator does not
  tag; the overseer chose `v4.33.0` knowing the pin cannot change later.
  Policy: automation `auto`, axioms `net_zero`, sorries `block`.
- **2026-09-12 — Ramsey finiteness added to the plan.**  `lt_ramseyNumber` as first stated
  had a hidden dependency: `ramseyNumber k = sInf {n | RamseyProperty n k}` and
  `Nat.sInf ∅ = 0`, so *every* lower bound on `R(k, k)` is false unless the set is known
  non-empty — and Mathlib has no Ramsey theorem to supply that.  `exists_ramseyProperty`
  now states it, and `lt_ramsey_number` depends on it.  Only existence is stated; the
  quantitative Erdős–Szekeres bound is a later refinement.
- **2026-09-12 — first frontier stated and published.** Ten declarations committed with
  `sorry` bodies across five files, and a task published for each (issues #4–#13, all
  pinned to `dcaf5da`; each carries its node id as `blueprint_ref`).  Issues #1–#3 were an
  earlier batch closed unclaimed and republished so the whole frontier shares one base
  commit.  Chapters 3–11 remain unstated by design: the plan stays shallow and deepens as
  reductions come back.
- **2026-09-12 — Chapters 5 and 6 stated and published** as issues #21–#30, pinned to `c943f93`.  The convention question recurred and was settled per chapter, not
  per node: **Chapter 5 is counting**, because both its applications end in existence claims
  about finite objects and its proofs are "Chernoff, then union bound", which is a count;
  **Chapter 6 is measure-theoretic**, because Definition 6.1.1's independence-from-a-family is
  strictly stronger than pairwise independence and has no counting surrogate.  Spencer's
  Ramsey bound (Theorem 1.1.9) is filed under `local-lemma` rather than `introduction`,
  because the local lemma is what proves it.
  Two published issues (#25, #26) carried cross-references to issue numbers predicted before
  publication and off by one; corrected in place.  **Write task prose with placeholder
  references and fill in the numbers after `create-task` returns them**, or publish
  dependency-ordered and reference only already-issued numbers.
- **2026-09-12 — Chapters 3 and 4 stated and published** as issues #14–#20, pinned to
  `22ba93e`.  Issues #4–#13 stay pinned to `dcaf5da`: the new files are additive and rewrite
  no existing declaration, so an older pin costs a worker nothing.  Seven more declarations (five in
  `Alterations.lean`, two in `SecondMoment.lean`). Chapter 4 deliberately stops at the
  engine; see the decision above. Markov (§3.3), Chebyshev (§4.1), Weierstrass (§4.7) and
  `G(V,p)` itself are upstream nodes. `card_filter_le_sum_div` is *not* a restatement of
  upstream Markov — it is the counting form this project's Chapter 1–3 proofs need, which
  Mathlib does not have.
- **2026-09-12 — `choir/type:prove` needed manual repair on nine issues.**  `set-priority`
  and `set-difficulty` immediately after `create-task` dropped the type label on every
  issue but one, presumably a read-modify-write race against label state GitHub had not
  yet settled.  If a future batch shows the same gap, add the label with `gh issue edit`
  rather than re-running `create-task`.  The `issue-intake` workflow reports `skipped` on
  orchestrator-created issues, which is expected — `create-task` round-trips through the
  same parser locally.
- **2026-09-13 — Chapter 10 stated and published** as issues #83–#94, pinned to `f40b890`.
  Twelve declarations in a new `Entropy.lean`, and — the decision worth recording — a
  **shared entropy layer proved by the orchestrator before any task was published**, rather
  than left for the first task to invent.  Mathlib has `Real.negMulLog`, `Real.binEntropy`
  and `Matrix.permanent` but no Shannon entropy of a discrete random variable, so without a
  central layer the chapter's twelve obligations would each have defined their own; that is
  exactly what happened in Chapter 6 with `fairCoin`/`uniformColoring` and cost three golf
  tasks and 311 lines to undo.  Chapter 10 is **counting**, not measure-theoretic: every
  random variable in it lives on a finite sample space and every conclusion is a cardinality.
  `condEntropy` is defined as the book defines it, as an expectation over `y`, so that the
  chain rule stays a theorem — defining it as `H(X,Y) - H(Y)` would have made §10.1's
  content disappear into an unfolding.
  Two statements are not transcriptions of a displayed theorem — the three-coordinate
  Loomis–Whitney bound and the binomial tail bound — and both were **checked numerically
  before publishing**, as were the edge cases of `triangle_intersecting` (`n ≤ 2` forces an
  empty family) and `bregman_minc` (a zero row gives `0 ≤ 1`).  The diagonal-pair hypothesis
  on `triangle_intersecting` is load-bearing: without it the statement is false by `2ⁿ`.
  §10.3 Sidorenko is deliberately **not** stated — it needs homomorphism counts and graphons,
  which the project does not have, and its smallest open case is open mathematics.
  `choir/type:prove` was dropped again on ten of the twelve, the same race recorded on
  2026-09-12; repaired with `gh issue edit` as that entry prescribes.
- **2026-09-13 — `measure_sub_integral_ge_le` was false as stated; measurability added.**
  Issue #81 was claimed and released with no PR — the same silent signal that caught the two
  Chernoff statements and `exists_nearly_equiangular`, and the reason that signal is worth
  watching even though `metrics struggle` cannot see it.  The bounded differences hypothesis
  does **not** imply `f` is measurable; a Mathlib measure applied to a non-measurable set
  returns its *outer* measure, and `∫` of a non-integrable function returns junk `0`.  So a
  non-measurable `f` with range of diameter `c₀` — a Bernstein set indicator, say — puts the
  left-hand side at `1` against a right-hand side below `1`.  `hf : Measurable f` is now a
  hypothesis.  Measurable plus bounded differences gives boundedness and hence integrability,
  so the `∫` needs nothing further.  **When an author-side statement is wrong, the cost lands
  on whoever claimed it first and shows up as a released lease, not as a failed check.**
- **2026-09-13 — Chapter 11 stated and published** as issues #97–#102, pinned to `9362ab6`.
  **The book is now stated end to end**: every chapter has a group file, and `later-chapters.md`
  — which had been carrying whatever was not yet stated since the first frontier — is retired,
  because each chapter file now carries its own "planned, not stated" section with the reason.
  Two decisions worth keeping.  **Vertex sets in Chapter 11 are `Fin n`**, not an arbitrary
  finite type: every theorem there reads "for every `c` there is a `δ` that works for all
  graphs", so `δ` is chosen before the graph and hence before its vertex type, and
  `∃ δ, ∀ {V : Type*} …` cannot be written — the universe cannot be bound under the
  existential.  `Fin n` costs no generality.  **Asymptotics are written out as `ε`–`N`, never
  as `o(1)`**, extending the idiom `exists_nearly_equiangular` established in Chapter 5.
  Chapter 11 differs from every chapter before it in one way that changed how the tasks are
  written: **the source does not prove its main theorems.**  Theorems 11.2.1 and 11.3.1 come
  with an algorithm and a proof idea and defer to Morris' lecture notes.  So those tasks
  invite a decomposition proposal on the issue rather than a proof, and name the missing
  prerequisite — triangle supersaturation — instead of letting a contributor discover it
  halfway in.  `IsTriangleFreeEdgeSet` is an `abbrev` rather than a `def` so that `Decidable`
  resolution sees through it; that keeps the no-`Decidable`-instances rule intact without
  making the statements uglier.
- **2026-09-13 — re-pinning a *claimed* issue re-adds `choir/available`.** Editing an issue
  body re-triggers the `issue-intake` workflow, which labels the task available; on a task
  someone is actively holding, the result is both labels at once and a task two workers can
  claim. Seen on #86 immediately after the batch re-pin to `a8b6e79`. **After re-pinning, list
  the issues carrying both labels and strip `choir/available` from them** — `sync-leases` does
  not fix this, because the lease comment is still valid and it sees nothing wrong.
- **2026-09-13 — fifteen PRs merged in one batch; 11 unconditional, 4 reductions.**  Chapter 10
  went from stated to almost entirely proved in a single round: `entropy_nonneg`,
  `condEntropy_eq_sub`, `entropy_pair_le_add`, `condEntropy_le_entropy`, `entropy_pi_le_sum`,
  **`shearer`**, `sum_choose_le_exp_binEntropy`, plus `le_card_triangleFreeGraphs`,
  `measure_sub_integral_ge_le`, `le_binomialRandom_cliqueFree_three` and
  `exists_conflictFree_of_union_bound_lt_one`.  `card_sq_le_prod_card_image`,
  `card_lt_of_triangleIntersecting`, `permanent_le_prod_factorial` and `janson_prob_none_le`
  landed as declared reductions.  `inventory scan`: **17 sorries, zero custom axioms.**
  Ten of the fifteen touched `Entropy.lean`.  Before merging any of them I checked that every
  diff was a single hunk deleting one `sorry` — no statement edits, no reverts — and that no two
  PRs added a declaration of the same name, which the gate cannot see because each PR is checked
  against its own base and not against its siblings.  **That cross-PR name check is the thing to
  repeat on any future parallel batch**; `axiom-honesty` and `statement-immutability` are
  per-PR by construction.
- **2026-09-13 — the Janson statements were false without `[Countable ι]`.**  Found and reported
  by the contributor proving `janson_prob_none_le`, who filed it on the issue rather than
  working around it — the intended path, and the second author-side statement defect this week.
  The measurable space on `Set ι` is the product σ-algebra, so `{R | S i ⊆ R}` is non-measurable
  for uncountable `S i` and `setBernoulli` silently returns an outer measure; at `p = 1` that
  makes the bound false outright.  Reproduced before acting.  **The generalisable tell: Mathlib
  gated everything substantive in `SetBernoulli.lean` behind `section Countable`, and the
  statement was built on the ungated part.  When upstream fences part of an API, a statement
  resting on the unfenced remainder deserves a second look.**
  The same report asked for two `setBernoulli` facts as shared interface.  Both are now stated
  in `Correlation.lean` (#119, #120), deliberately **without** `MeasurableSpace ι` /
  `MeasurableSingletonClass ι` binders — `setBernoulli` needs neither, and requiring them would
  have made the lemmas unusable from `Janson.lean`.  My first draft had them; it type-checked in
  isolation and would have been useless.  **Check a new interface lemma by applying it from its
  intended call site, not by checking that it elaborates.**
- **2026-09-14 — `illegal-axiom` on #122, and the rule that was misread.**  A target can be
  *fully proved*, add no placeholder of its own, and still fail `comparator`: Janson II is proved
  from Janson I, which is itself proved modulo `janson_prob_none_step_le`, so `sorryAx` is in the
  closure either way.  The contributor removed their `choir-reduction` block on the theory that
  "a placeholder on a declaration the base already had is disallowed" — which is not the rule.
  `children` may name **any declaration already in the project that carries a placeholder**, and
  `sorry-delta` Rule B only examines counts that *rose*, so citing a pre-existing obligation is
  free.  `comparator` permits `sorryAx` exactly when a reduction is declared.  Their earlier red
  run was almost certainly the stale pin they diagnose elsewhere in the same PR.
  **Read `gate/verify/` when two checks appear to contradict each other** — the rules are in the
  module docstrings, and deducing a general rule from one red run is how the fix gets deleted.
  Recorded in `skills/conventions.md`.
- **2026-09-14 — the published route for Janson II was wrong; the statement was not.**  It
  prescribed `𝔼 Δ_T = q²Δ` under independent `q`-sampling, but `D` may contain diagonal pairs,
  which survive with probability `q`.  The averaging breaks exactly in the `Λ ≫ μ` regime the
  theorem covers.  Restricting to the off-diagonal `E` fixes it and removes the need for a case
  split entirely.  Corrected argument in `janson.md`.  **Task prose is not checked by anything** —
  statements get `statement-equiv` and numerical sanity checks, routes get nothing, and this is
  the second time a prescribed route has been wrong where the statement was fine.
- **2026-09-14 — `janson_prob_none_step_le` had a graph node but no task** since #103 merged,
  published now as #123.  When accepting a reduction, the playbook's "publish a `prove` task per
  node" is a separate step from adding the node and is easy to drop when several land at once.
- **2026-09-14 — #15 and #60 decomposed after five abandoned claims between them.**  Both
  statements check out, so this was a shape problem, not a soundness one: each bundled a
  probabilistic/counting argument together with a piece of pure analysis.  Split along that
  seam into #124/#125 and #126/#127, with the analytic child in each pair mentioning no graphs
  at all and the counting child carrying no asymptotics.  `card_filter_indepNum_le` was
  brute-forced over all `n ≤ 4`, `M ≤ 4` before publishing.  **Diagnostic order that works:
  check the statement first — three author-side statements have been false — and only once it
  survives, read repeated abandonment as a request to decompose.**
- **2026-09-14 — Chapter 11's first two theorems were in the wrong order, and a contributor
  caught it.**  `exists_containers` (11.2.1) is a counting corollary of
  `exists_containers_fingerprint` (11.2.3), so publishing them in the book's order made the
  corollary unprovable: Lean has no forward references.  The contributor proposed three fixes,
  recommended the right one, released the claim and changed nothing — rather than adding a
  near-duplicate of 11.2.3 above the target, which the reduction contract would have permitted.
  File reordered, graph edge reversed.
  **Generalisable: the source's presentation order can encode a dependency backwards.**  A
  textbook may state a weaker result first and strengthen it later; a Lean file cannot.  §11.1
  has the same shape (11.0.2 depends on 11.1.1) and already happens to be ordered correctly,
  but this is worth checking whenever a chapter is stated from a linear reading.
- **2026-09-14 — `setBernoulli_inter_eq_mul_of_disjoint` does not need `[Countable ι]`.**  Its
  proof goes through `indep_iSup_of_disjoint`, which takes `Set ι` rather than `Finset ι`, so
  countability never enters; the contributor found this via the `unusedSectionVars` linter and
  **reported it instead of writing `omit`**, correctly treating a binder removal as a statement
  change.  Binder dropped here, after their PR merged rather than before — removing it first
  would have made their branch read as *adding* the instance and tripped
  `statement-immutability` on a PR that changed nothing.  **Sequencing matters when acting on a
  contributor's finding about the statement they are working against.**  `setBernoulli_inter_le_mul`
  keeps the instance; Harris genuinely needs it, so the asymmetry is real.
- **2026-09-14 — six PRs merged; Erdős 1959 and Janson I are both unconditional.**
  `exists_girth_gt_and_chromaticNumber_gt` (Theorem 3.4.1) and `janson_prob_none_le` with its
  conditioning step are now free of `sorryAx`, checked with `#print axioms` rather than inferred
  from green merges.  `Correlation.lean` reached zero `sorry`.  **12 sorries, zero custom
  axioms**, down from 26 two batches ago.
  The cross-PR name-collision check ran again on the two file-sharing pairs and found nothing —
  worth keeping as a habit, since the gate checks each PR against its own base and never against
  its siblings.
- **2026-09-14 — a decomposition I published was superseded while it was being published.**
  #60 had been abandoned four times, so it was split into #126/#127; a contributor was
  simultaneously proving it directly, landed that as #130, **flagged the overlap themselves**,
  and offered to re-route their finished proof through my two nodes.  Declined and both nodes
  retired.  A direct proof that exists beats a two-part proof that does not, and asking someone
  to restructure green work through orchestrator scaffolding protects the plan at their expense.
  **Check for lease activity before retiring a node** — both were unclaimed, so nothing was lost.
- **2026-09-14 — `setBernoulli` is uniform-`p` only, and Janson's lower tail is not.**  Warnke's
  proof thins the index set by an independent Bernoulli `q`, leaving per-coordinate inclusion
  probabilities that `setBernoulli` cannot express.  The contributor found this and **stopped at
  the boundary** instead of inventing a primitive inside `Janson.lean`.  `setBernoulliPi` is now
  in `Correlation.lean`, with `setBernoulli_eq_setBernoulliPi` proving it a faithful
  generalisation — **that specialisation lemma is the point; a definition that merely elaborates
  demonstrates nothing.**  A non-uniform Janson I is deliberately *not* stated: it would mean
  generalising `jansonMu`/`jansonDelta` in place, under three already-proved theorems, and that
  call is better made by whoever holds the proof.  The task asks for a proposal rather than
  handing down an interface.
- **2026-09-14 — I published an impossible task, and the gate caught it.**  #121 was filed as a
  `golf` task but asked for a deletion and a `private` → public promotion.  The golf spec is
  explicit that a golfed declaration's statement must stay **token-identical to base** and only
  the proof body may change, so no correct implementation could have passed
  `statement-immutability`, and PR #136 was blocked for doing exactly what the task asked.
  **`merge-override` was considered and rejected**: the check was not misfiring, it was enforcing
  the rule it exists for, and overriding a correct check to cover an orchestrator
  mis-specification is how a gate becomes decorative.  The contributor's commit was cherry-picked
  onto `main` unchanged (`6c32d17`), the PR closed **without deleting its branch**, and the
  declaration-level claims verified rather than taken from the PR's table.
  **Rule now in `conventions.md`: consolidation that deletes, renames, changes visibility, or
  relocates is orchestrator work, never a task.**  `golf` means "same statement, shorter proof"
  and nothing else.
- **2026-09-15 — Chapter 8 is complete; all three Janson inequalities are unconditional.**
  `janson_prob_none_le_of_mu_le` (#122) took `Janson.lean` to zero `sorry`s.  **9 sorries,
  zero custom axioms** project-wide.
  Both PRs this round went through the playbook's new **stage-two subagent review**, which earned
  its keep twice: on #139 it verified that the finite-sum `Φ` really is the MGF (both bounds meet,
  so it cannot be a degenerate surrogate) and that Markov-as-partition *discharges* the
  outer-measure hazard rather than sidestepping it; on #122 it showed `hK : K ⊆ s` is load-bearing
  by exhibiting a counterexample without it — a hypothesis that is necessary being the opposite of
  a smuggled one.  Neither reading would have happened under batch load if it had stayed in my
  context, which is precisely the argument the playbook makes.
- **2026-09-15 — the duplicated `Δ`-bookkeeping is extracted** as `sum_filter_insert_le`, net
  −40 lines.  Deliberately sequenced *after* Janson II landed: doing it earlier would have
  invalidated a finished proof in flight, and doing it per-PR would have meant the same surgery
  twice.  **Three contributors independently wrote the same binomial-weight identity** before a
  top-level lemma existed — the recurring cost of parallel work against a pinned base, and
  something only the orchestrator can fix.
  The remaining shape issue — Janson I is stated at `univ`, so a sub-family needs subtype
  gymnastics — is **recorded and not built**, because nothing needs it yet.  That is the
  discipline `setBernoulliPi` failed.
- **2026-09-15 — two of the project's abandonments trace to my route prose, not to difficulty.**
  `entropy_le_logb_card` (#84) had been claimed and released twice with no note.  The statement is
  sound; the prose pointed at Mathlib's `ConcaveOn` Jensen API and named
  `Finset.inner_le_nnorm_mul_nnorm`, **which is Cauchy–Schwarz, not Jensen** — a wrong pointer I
  wrote.  Meanwhile `entropy_pair_le_add`, proved in the same file, does the job with
  `Real.log_le_sub_one_of_pos` in a few lines.  Corrected on the issue and generalised into
  `skills/conventions.md`.
  **Task prose is checked by nothing.**  Statements get `statement-equiv`, numerical sanity checks
  and now a stage-two reading; routes get no scrutiny at all, and this is the third time a
  published route has been wrong where the statement was fine.  When a task is abandoned with no
  note, **re-read the route before concluding the task is hard** — the diagnostic order is
  statement, then route, then decomposition.
- **2026-09-15 — Chapter 3 is complete.**  `exists_isDominating_card_le` (#140) proved Theorem
  3.1.1 directly, and `Alterations.lean` is at zero `sorry`s.  **7 sorries project-wide, zero
  custom axioms**, all in Chapters 10 and 11.
  #124 retired as superseded — the same pattern as #126/#127, and for the same reason.  Its
  content was reproved inline as a `have`, in full generality, by the PR that proved the parent.
  **The decisive check before retiring is lease activity**: no claim, no lease comments, so no
  work was lost.  The declaration was removed rather than left as a `sorry` nothing uses, since
  leaving a published node open while its proof sits unreachable inside another theorem would
  have guaranteed the next claimant redid 131 lines.
- **2026-09-15 — I corrupted two commits by running `git add -A` while a review subagent held a
  patch in the shared checkout.**  `07a2f6b` and `726e414` each carry 147 lines of PR #140's
  proof, added then removed, contradicting their own commit messages.  The tip was correct and
  the PR diff unaffected.  **History was deliberately not rewritten** — `main` is shared, open
  tasks pin commits on it, and breaking live pins to tidy cosmetic history is the worse trade.
  Procedure fixed in `skills/orchestrator-notes.md`: stage explicit paths, and review subagents
  must not mutate the working tree.  **Delegating work into your own working directory makes that
  directory shared state.**
- **2026-09-15 — I retired a node that was actively claimed, with an open PR.**  #124 was closed
  and its declaration deleted at 05:32; it had been claimed at 05:23 and PR #141 opened at 05:27.
  The lease check that justified retiring it was run during an earlier review and was **stale by
  the time I acted on it** — a liveness check is only valid at the instant of the destructive
  action.  Reverted: the declaration is restored byte-identical to the PR's base so #141 merges
  through the normal flow, and #124 is reopened.
  **The contributor's version is also the better architecture.**  #140 proved the parent by
  reproducing this lemma inline as an anonymous `have`, ~131 lines unreachable from any other
  file; with it named and top-level, the parent becomes a short derivation and the duplication
  goes away.  So the retirement was wrong on the merits too, not just on process — which is what
  the rule about not re-routing finished work was trying to protect in the first place, applied
  in the wrong direction.
- **2026-09-15 — #141 and #142 merged; 6 sorries left, zero custom axioms.**  Chapter 3 is
  complete again (`Alterations.lean` at zero), and the remaining work is entirely Chapters 10 and
  11: `entropy_le_logb_card`, `shearer_triple`, and the four Containers nodes.
  **`entropy_le_logb_card` (#84) is now the sole open obligation beneath five merged theorems** —
  `card_sq_le_prod_card_image`, `card_lt_of_triangleIntersecting`, `permanent_le_prod_factorial`,
  `card_pow_le_prod_card_image_inter` and `condEntropy_le_expected_logb_availCount`. Proving it
  makes Brégman–Minc and the triangle-intersecting bound unconditional at a stroke.
- **2026-09-15 — two contributors independently produced the same 128-line proof.**  #140 inlined
  the averaging argument of Theorem 3.1.1 as an anonymous `have`; #141 proved it as the top-level
  lemma. Character-for-character identical bodies, committed five minutes apart, neither able to
  see the other.  Nobody erred — this is the structural cost of pinning parallel tasks to one
  base.  Collapsed via **golf task #145** rather than by hand: replacing an inline `have` with a
  call to an identical lemma is a body-only change to a pinned declaration, which is exactly what
  `golf` is for.  Contributors are now asked to check sibling *open* PRs against their target
  file, not only merged work.
- **2026-09-15 — a reduction body said "fully proved" when the closure still carried `sorryAx`.**
  #142's `choir-reduction` block was accurate and declared `entropy_le_logb_card` correctly, but a
  bolded line earlier in the same body invited the opposite reading.  Harmless to the contract,
  but the graph node must not be marked closed on the strength of prose.  **Read the reduction
  block, not the summary.**
- **2026-09-15 — two of my Chapter 11 statements were FALSE, one of them already merged.**
  `exists_containers_fingerprint` (#98) and `exists_containers` were both false for every
  `c ≥ 3/2`; `Kₙ` forces `δ ≥ 1/2` and a disjoint union of 3-vertex paths forces `δ ≤ 1/3`.  I
  verified both numerically before touching anything.  The missing hypothesis is **Zhao's own
  proviso**, `d ≤ 2δ|V|`, which the book states on printed p. 207 *inside the proof idea* and
  omits from the theorem box.  **A textbook's theorem box is not always the whole hypothesis
  list.**  Added to both at `1e4659a`, with the counterexamples in the docstrings.
  `exists_containers` had merged as a declared reduction onto the false lemma, so it was
  proved-modulo-a-false-statement, not unsound — the kernel was never deceived, and threading the
  new hypothesis through cost one binder.
  **Found by the stage-two review of PR #143**, which had inherited the defect into two new public
  statements.  That PR was closed without deleting its branch: its assembly was genuine
  machine-checked content, but the repair is not local, since the parent's own budget `⌊n/√d⌋₊` is
  only guaranteed `≥ 1`.  **A PR that surfaces a false statement two levels upstream of itself is
  worth more than one that merges** — and this is the fourth author-side false statement, all four
  found by reading rather than by any gate check.
  `Kₙ` and "disjoint union of stars" are now the standing test pair for Chapter 11 statements.
- **2026-09-15 — #144 merged; 5 sorries left, all in Chapters 10 and 11.**  The
  Erdős–Kleitman–Rothschild upper bound is proved modulo `exists_containers_triangleFree` alone.
  The PR is the model for a reduction return: one declared child, everything downstream
  unconditional, and a body precise enough that the analysis could be checked independently
  before reading the Lean.  It also **avoided routing through `exists_containers_fingerprint` on
  its own judgement** — vindicated hours later when that statement turned out to be false.
  Notable: it reached for `Real.log_le_sub_one_of_pos` rather than Mathlib's concavity API, which
  is the idiom added to `skills/conventions.md` after my own route prose had been sending people
  at `ConcaveOn`.  The conventions file is being read.
- **2026-09-15 — `statement-immutability` caught a branch reverting the Chapter 11 statement
  repair.**  PR #146's head lacked the `d ≤ 2δn` hypothesis its own base carried: a stale
  workspace whose older copy of the declaration won the merge.  Merging would have silently
  reinstated a statement already proved false.  **After repairing a statement, expect in-flight
  branches to revert it** — re-pinning open tasks does not help, because the branch already
  exists, so the check is the only backstop.  Never override `statement-immutability` on a file
  whose statements were recently changed.
  Its companion red, `sorry-delta`, was a false alarm: the audit reported `submission: proof`
  despite a well-formed reduction block, because the body was edited **one second** after the
  check fired.  The `submission:` line is the tell.
- **2026-09-15 — triangle supersaturation is reachable from Mathlib after all.**  #146 points out
  that `SimpleGraph.CliqueFree.card_edgeFinset_le` at `r = 2` gives Mantel,
  `SimpleGraph.farFromTriangleFree_iff` converts it, and
  `SimpleGraph.FarFromTriangleFree.le_card_cliqueFinset` — the triangle removal lemma — supplies
  the count with `c = SimpleGraph.triangleRemovalBound ε`.  `containers.md` had it recorded as
  **missing from Mathlib and the most useful thing anyone could add**; it is instead a
  transcription away.  Correcting that entry.
- **2026-09-15 — #147 merged: the project's first `golf` task to land.**  One line in, 135 out,
  collapsing the duplicated averaging argument so that `exists_isDominating_card_le` calls
  `exists_isDominating_card_le_of_mem_Icc` instead of inlining it.  The earlier golf attempt
  (#136) was blocked by `statement-immutability`, correctly — I had mis-published it, asking for
  a deletion and a visibility change, neither of which is a proof-body edit.  This one is the
  genuine article, and the contrast is the clearest statement of what `golf` means:
  **same pinned statement, shorter body, nothing else moved.**
- **2026-09-15 — #146 merged: Theorem 11.1.1 reduced honestly, and the obligations are true.**
  `exists_containers_triangleFree` is now proved modulo two new nodes, **#148** (triangle
  supersaturation) and **#149** (one step of the Remark 11.2.2 iteration).  Unlike #143's
  obligations, I checked these against the pair that killed that attempt and **both survive**:
  `n ≤ 2` is vacuous, `n = 3` and `Kₙ` impose only *upper* bounds on `δ`, and a smaller `δ` is a
  weaker claim — so there is no budget that can collapse below `1` and force an existential
  empty.  **That collapse is the failure mode to test for in this chapter**, and a statement
  whose constraints are all one-directional cannot exhibit it.
  The iteration is the real one: `K` rounds with `(1-δ)^K ≤ 1/4` from the `n²` starting bound
  lands under `(1/4+ε)n²`, with the count accumulating to `n^((K+1)C₀·n^{3/2})` — Remark 11.2.2
  rather than a single application passed off as the iterated one.
- **2026-09-15 — triangle supersaturation verified reachable from Mathlib**, correcting this
  file's earlier claim that it was missing and "the most useful thing anyone could add".  All
  four names checked against the pinned Mathlib: `CliqueFree.card_edgeFinset_le`
  (`Extremal/Turan.lean:422`), `farFromTriangleFree_iff` (`Triangle/Basic.lean:192`),
  `FarFromTriangleFree.le_card_cliqueFinset` (`Triangle/Removal.lean:137`) and
  `triangleRemovalBound` (`Triangle/Removal.lean:41`) — with `triangleRemovalBound_pos` at line
  44 supplying exactly the positivity the `∃ c > 0` needs.  **A "not in Mathlib" note in a
  roadmap is a claim with a shelf life; this one was wrong.**
- **2026-09-15 — Chapter 4's first application stated.**  With every open task claimed and no
  PRs to review, the remaining orchestrator work is the material each group file lists under
  "planned, not stated" — that is real book content, and stating it is my job rather than
  something to wait on.  `le_card_of_distinctSubsetSums` (Theorem 4.6.3, task #151) is the most
  tractable of Chapter 4's five: **no random graphs**, and an explicit constant, so it needs no
  `o(1)` idiom.  Checked against the Conway–Guy minimal witnesses for `k ≤ 8` before publishing.
  Erdős's Conjecture 4.6.2 is open mathematics and is deliberately not stated — the standing
  rule that a conjecture in the source must never be transcribed as a theorem.
- **2026-09-15 — Hardy–Ramanujan (§4.5) is blocked on Mertens, which Mathlib lacks.**  The
  roadmap had recorded it as the most tractable of Chapter 4 because
  `ArithmeticFunction.cardDistinctFactors` exists and the statement is expressible.  **That
  inference was wrong: expressible is not tractable.**  Turán's proof needs
  `∑_{p ≤ n} 1/p = log log n + O(1)` to compute the mean, and `Mathlib/NumberTheory/` has no
  Mertens estimate in any form.  Corrected rather than published — handing out a task whose
  analytic input does not exist would cost a contributor a day to discover.
  This is the mirror of the supersaturation correction earlier today: one roadmap note was
  **too pessimistic** about Mathlib (triangle removal was there all along), this one **too
  optimistic**.  Both were written from a search for the *statement's* vocabulary rather than
  for the *proof's* inputs.  Search for what the proof needs.
- **2026-09-15 — #150 merged: triangle supersaturation is proved.**  Unconditional, via the
  Mathlib route the contributor identified on #146 and I verified before publishing.  **The
  normalisation trap I flagged did not bite**: Mathlib's `FarFromTriangleFree ε` is measured
  against `ε · card²`, so `(1/4 + ε)n² − n²/4 = εn²` lines up with no rescaling.  The factor of
  six between ordered triples and 3-cliques is handled by *not needing it* — a surjection from
  triples onto cliques gives the lower bound the statement wants, and the overcount only helps.
  `exists_containers_triangleFree` is now down to a single obligation, #149.
- **2026-09-15 — Lemma 4.3.7 stated and published (#152).**  Reversed my earlier judgment that
  the board did not need more tasks: that reasoning would leave the statement layer permanently
  incomplete, and the statement layer is the orchestrator's responsibility regardless of queue
  depth.  An unclaimed task costs nothing; an unstated theorem is never proved.
  Stated with the general hypothesis `1 - (1-q)^m ≤ p` in place of the book's `q = p/m` — it is
  what the argument needs, it is strictly more general, and it avoids producing `p/m` in
  `unitInterval`.  **The direction was checked numerically before committing**, because it
  inverts easily: the union of `m` copies of `Ω_q` has density *at most* `p`, not at least.
  Placed in `Correlation.lean` rather than `SecondMoment.lean`.  **Roadmap chapter boundaries
  need not match file boundaries** — this is a `setBernoulli`-and-upper-sets statement, which is
  Chapter 7's subject, and forcing it into Chapter 4's file would have meant duplicating that
  layer.
- **2026-09-15 — Theorem 4.3.5 stated as #153, because #152's prose asked for it.**  That is the
  "request the node, don't bury it" loop working for the fourth time (after triangle
  supersaturation, the Janson conditioning step, and Corollary 10.4.7).  Stated **non-strictly**:
  the book's 4.3.5 is strictly increasing and needs `F` non-trivial, but nothing downstream uses
  strictness and dropping non-triviality makes it a side-condition-free shared-layer fact.  **A
  strengthening nobody consumes is a liability, not a bonus** — it would have forced every caller
  to discharge non-triviality.

## The unstated remainder, audited (2026-09-15)

Four chapters carry unstated book content.  Each item below was checked against **what its proof
needs**, not what its statement mentions — the distinction that produced two wrong notes in this
file earlier today, one in each direction.  Three categories, and they call for different
responses:

**(a) Everything present — state it.**  Done this session: §4.6 distinct sums (#151), §4.3
multiple round exposure (#152), §4.3 monotonicity (#153).

**(b) Blocked on Mathlib infrastructure that does not exist.**  Do not publish these; a task
whose analytic input is absent costs a contributor a day to discover.
- §4.5 Hardy–Ramanujan, §4.5 Erdős–Kac — **no Mertens theorem** (`∑_{p≤n} 1/p = log log n + O(1)`);
  nothing in `Mathlib/NumberTheory/`.
- §2.2 large sum-free subsets — **no `IsSumFree`** (`ThreeAPFree` is a different notion) *and*
  **no primes in arithmetic progressions** (`PrimesCongruentOne` is `≡ 1 mod k` only; no
  Dirichlet).
- §2.5 unbalancing lights — needs a central limit estimate.
- §2.6 crossing number — needs Euler's formula for planar graphs.
- §10.3 Sidorenko — needs homomorphism counts and graphons; and its general case is **open
  mathematics**, so only the proved special case could ever be stated.

**(c) Real work on infrastructure that does exist.**  Statable whenever there is capacity; these
are the honest growth path.
- §9.2 Azuma — `Martingale`, `Filtration` and `condExp` are all present; Azuma itself is not.
  Everything in §9.3–§9.6 is downstream of it.
- §10.2 Kahn–Lovász — needs two orchestrator-authored definitions first (a count of perfect
  matchings, and the bipartite double cover; note `boxProd` is the **Cartesian** product and
  would silently build the wrong graph).
- §4.3 Bollobás–Thomason, §4.1/§4.2 thresholds, §4.4 clique number — all need an `ε`–`N` or
  `whp` idiom plus, for §4.2, a definition of `m(H)`.
- §11.1.3 / §11.1.5 — need `ex(n, H)` and a `whp` idiom.
- §2.4 hypergraph Turán sampling — not yet assessed; the most likely of Chapter 2's four to be
  tractable.

**The standing rule this audit enforces:** a "not in Mathlib" note has a shelf life, and a
"Mathlib has the vocabulary" note is not evidence of tractability.  Re-check before publishing,
and search for the proof's inputs.
- **2026-09-15 — #84 decomposed after two silent releases; Gibbs' inequality is now #154.**
  Lease ages made the case: #84 and #90 had each been held **5+ hours with no PR**, and #98 has
  now been claimed **four times**.  For #84 the diagnostic order was already exhausted —
  statement verified, route corrected — so decomposition was the remaining lever.
  `sum_negMulLogb_le_logb_card` carries all the mathematics with **no `probOf`, no `entropy`, no
  measure**: finitely many nonnegative reals summing to `1`.  Verified on 20000 random
  weightings, and *tight* at the uniform weighting, so no shortcut exists.  What remains in #84
  is `Finset.sum_subset` plus `sum_probOf` — a handful of lines.
  **Checking lease age is the cheap diagnostic I should run every idle turn.**  It is the only
  visible form of the claim-and-release signal, which `metrics struggle` cannot see, and it is
  what told me which of the five claimed nodes needed help rather than patience.

## Source page map (read the TOC once, 2026-09-15)

**`PDF page = printed page + 6`.**  Recorded because locating a statement by trial-and-error
cost four wasted PDF reads in one session; the table of contents is at PDF pp. 5–6 and settles it
in one.

| § | topic | printed | § | topic | printed |
|---|---|---|---|---|---|
| 1.1–1.4 | Ramsey, set systems, 2-colouring, list chromatic | 1, 7, 10, 12 | 7.1–7.2 | Harris–FKG, applications | 107, 110 |
| 2.1–2.6 | Hamiltonian paths, sum-free, Turán, sampling, unbalancing lights, crossing number | 17, 18, 19, 21, 23, 25 | 8.1–8.3 | non-existence, lower tails, chromatic number | 115, 121, 124 |
| 3.1–3.5 | dominating set, Heilbronn, Markov, girth+chromatic, greedy colouring | 29, 30, 31, 32, 33 | 9.1–9.6 | bounded differences, **martingales 130**, chromatic 135, isoperimetry 139, Talagrand 152, TSP 162 | 129 |
| 4.1–4.7 | triangle 37, subgraph thresholds 42, thresholds 46, clique number 55, Hardy–Ramanujan 57, distinct sums 61, Weierstrass 63 | 37 | 10.1–10.4 | basics 173, permanent/Steiner 178, Sidorenko 185, Shearer 190 | 173 |
| 5.1–5.3 | discrepancy, equiangular, Hajós | 71, 73, 75 | 11.1–11.3 | triangle-free containers 203, graph containers 206, hypergraph 208 | 201 |
| 6.1–6.6 | LLL, colouring, transversals, cycles, lopsided, algorithmic | 79, 83, 89, 90, 92, 97 | | | |

**Chapter starts (printed):** 1 · 17 · 29 · 37 · 69 · 79 · 107 · 115 · 129 · 173 · 201.
- **2026-09-15 — #156 merged: Gibbs' inequality is proved, one hour after the decomposition.**
  #84 had been claimed and released twice; splitting its mathematics into `gibbs_inequality`
  (#154) produced a claim within minutes and a correct PR within the hour.  **That is the
  decomposition diagnostic earning its keep** — the statement and route had already been
  checked, so the shape of the task was the only remaining variable.
  The proof used `Real.log_le_sub_one_of_pos` rather than Mathlib's `ConcaveOn` API, which is
  the convention added after my original #84 prose pointed at `ConcaveOn` and named
  `Finset.inner_le_nnorm_mul_nnorm` — Cauchy–Schwarz, not Jensen.  A convention written down
  after a mistake was followed by the next contributor to touch the area.
  **#84 is now `Finset.sum_subset` plus `sum_probOf` away from closing**, and with it Brégman–Minc
  and the triangle-intersecting bound go unconditional.
- **2026-09-15 — #158 merged: monotonicity of the satisfying probability.**  Landed within the
  hour, via Zhao's **Proof 2** (two-round exposure) — the route the task prose flagged as likely
  easier because it stays inside `setBernoulli` rather than needing a `[0,1]`-valued coupling
  field.  It unblocks #152, whose step 2 is exactly this.
  The contributor found **`setBernoulli_cylinder`**, which I did not know existed when writing
  the task and which computes cylinder measures in one step.  Recorded in `correlation.md`;
  this project has written that computation out longhand more than once.
  Pattern worth noting across #150, #156 and #158, all merged within about an hour of
  publication: each landed on a node whose prose had done real work — correcting a wrong route,
  choosing between the source's two proofs, or separating mathematics from bookkeeping.  The
  nodes that sat for five hours were the ones where I had given a bad route (#84) or bundled two
  kinds of work (#15, #60).  **Prose quality tracks throughput about as closely as statement
  quality does.**
