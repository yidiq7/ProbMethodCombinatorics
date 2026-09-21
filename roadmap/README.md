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
| [`concentration`](concentration.md) | 9 | **all proved** | Talagrand, TSP |
| [`entropy`](entropy.md) | 10 | **all proved** | Sidorenko, Steiner |
| [`containers`](containers.md) | 11 | 1 open | 11.1.3, 11.1.5, supersaturation |

**Chapter 11's held corner is the only open node again.**  Three more were stated on 2026-09-21
from a re-sweep of the source — #377 Kahn–Lovász, #378 Theorem 5.0.5, #379 Theorem 9.4.8 — and
**all three were claimed, proved and merged the same day** (#380–#382), each unconditional.  Each
was given its own file so that filling it would not re-pin the golf tasks open against
`Chernoff.lean`, `Concentration.lean` and `Entropy.lean`; that worked, and is the pattern to
repeat.
The fourth is Chapter 11's held corner.  The counts in this table are derived from `graph.json`
(nodes with `statement: formalized`, `proof: planned`), which `sync-graph --check` keeps
honest:

**§11.2 is closed, kernel-verified.**  Theorems 11.2.1 (`exists_containers`) and 11.2.3
(`exists_containers_fingerprint`) and all three of 11.2.3's obligations depend on nothing but
`[propext, Classical.choice, Quot.sound]` — Mathlib's standard trio, **no `sorryAx`**.  Checked with
`#print axioms`, not inferred from the sorry count.

**Chapter 11 rests on one obligation, and it is deliberately unpublished:**

| Obligation | Task | What rests on it |
|---|---|---|
| `exists_containers_fingerprint_three_uniform` | **not published — held** | Theorem 11.3.1, via #172's reduction |

(`exists_container_round`, #176, was the other and is closed.)

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

- **`whp` is written out, never as a filter or an `o(1)`** — *for every `ε > 0` there is a
  threshold making the probability at least `1 - ε`*.  A hypothesis like `p ≪ 1/n` becomes a `δ`
  bounding `p · n`, so no sequence of graphs and no limit appears in any statement.  This extends
  the `ε`–`N` convention Chapters 5 and 11 already use to the probabilistic setting, and
  `prob_no_triangle_of_mul_le` in `SecondMoment.lean` is the reference instance to copy.
  **Prefer the form with no `N`** where the estimate is uniform in `n`, as Markov's is; reach for
  `∃ N, ∀ n ≥ N` only when the argument genuinely needs `n` large, as Chebyshev's does.
  **Write the probability as `(μ).real S`, not `(μ S).toReal`** — Mathlib's probability API
  (`probReal_compl_eq_one_sub`, `probReal_univ`) is stated in `Measure.real`, and the reference
  node had to end with a `measureReal_def` conversion because its statement used `.toReal`.  The
  rest of `SecondMoment.lean` predates that API and is not worth churning, but new nodes should
  use `Measure.real`.

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

- **2026-09-21 — the golf queue was ordered by the wrong number: two proofs were within 5% of failing to compile at all.**
  #386's author reported that `exists_bad_card_lt_and_indepNum_le` elaborated at **196,187 of the
  200,000 default `maxHeartbeats`** — 2% of headroom — and their golf took it to **9,420**, a 95%
  cut, purely by replacing eight bare `nlinarith` with `linarith only` given explicit product
  hints and `clear`ing spent context.  **That proof was going to break on the next Mathlib bump**,
  and nothing in the project would have predicted it.

  I swept the whole corpus rather than take the single data point: for each file,
  `lake env lean -DmaxHeartbeats=L` at `L = 150000, 175000, 190000`, and see which fail.  One
  build per file per level, no edits, no tokens.  Two files came back hot, and I published a task
  against each:

  | Declaration | File | Task | Outcome |
  |---|---|---|---|
  | `exists_sum_shortCycleSupport_card_lt` | `Alterations.lean` | #387 | 191,952 → 12,337 (#390) |
  | `exists_fingerprint_of_dense_pairs` | `Containers.lean` | #392 | 192,623, open |

  **The second row is a correction: I named the wrong declaration first, and a contributor caught
  it.**  #388 was published against `card_le_compl_mul_choose_two_aux` — which costs about
  **1,000** heartbeats, not 190,000.  The expensive declaration is its neighbour
  `exists_fingerprint_of_dense_pairs`, whose proof *ends* at line 2275, four lines above the
  target's statement.

  **The mechanism is worth more than the mistake.**  A file-level sweep tells you a *file* is hot
  and nothing else; naming the declaration means mapping the reported error line to a declaration,
  and a timeout is reported **where elaboration ran out, which is the tail of the expensive
  proof**.  For `Alterations.lean` I walked *backward* from the error line to the nearest preceding
  declaration — correct.  For `Containers.lean` I searched *forward* from an arbitrary window start
  and got the first declaration at or after it — the neighbour.  **Forward search is systematically
  wrong at exactly the boundary that matters.**  Always walk backward from the error line.

  **The lesson is about how this queue was chosen.**  Every golf batch so far was ranked by
  *line count*, because that is what is cheap to measure by reading.  Line count and elaboration
  cost are close to uncorrelated here: #386 cut two lines and 95% of the heartbeats, while the
  #385 golf cut 22 lines off a proof that was never near the ceiling.  **Lines are a readability
  metric; heartbeats are a "does this still compile next month" metric**, and only the second
  one can fail the build.  Rank future golf batches by the sweep above, then by length.  The
  sweep is also the cheapest health check the project has and nothing else surfaces it:
  `rebuild` is green at 200,000 right up until it is not, so a proof at 98% of the ceiling and
  one at 5% are indistinguishable from CI.  **Worth re-running after any Mathlib bump**, and
  before concluding a chapter is finished.

- **2026-09-21 — Kahn–Lovász closed (#380), 24 minutes from publication to merge, and the turnaround is the argument for publishing assembly nodes.**
  Corollary 10.2.2 was stated at 08:05, claimed at 08:22, submitted at 08:37 and merged
  unconditional.  Nothing about it was hard — both halves had been proved for days and the
  roadmap said so — but **no node named the chain that joins them**, so it sat undone while the
  file recorded it as understood.  A result whose pieces are all present is not finished, and the
  gap between "the pieces exist" and "a declaration says so" is invisible in a status table.
  Look for it deliberately: it is the cheapest work in the project.

  Two things the gate could not have caught, both clean on inspection:
  * **The square root is real.**  Brégman gives exponent `(d_v)⁻¹` and the target needs
    `(2 d_v)⁻¹`; the gap closes only by squaring the matching count through the double cover
    first.  A proof that reached the conclusion without going through `doubleCover`, or that
    leaned on an `rpow` junk value, would compile and be wrong.  This one applies
    `Real.rpow_le_rpow` and `Real.rpow_mul` with the nonnegativity side conditions discharged.
  * **Degree zero is handled, not excluded.**  No case split: at `d = 0` both the target factor
    and the Brégman factor are `1`, and the scalar step `(d)⁻¹ * 2⁻¹ = (2 * d)⁻¹` is `mul_inv`,
    unconditional in ℝ.  The statement carries no hypothesis on degrees and must not acquire one.

  **The adjacency matrix is built inline rather than imported**, because `Entropy.lean` reaches
  only `SimpleGraph.Finite` and `SimpleGraph.Matching`, and a `prove` task does not own the
  header.  Recorded because it reads like a missed reuse of `SimpleGraph.adjMatrix` and is not:
  **check scope before calling an inline construction duplication.**

- **2026-09-21 — the frontier re-derived from the source, not from this file: three nodes published (#377–#379), and §9.4's "blocked" was a scoping error.**
  With Chapter 11's one corner held and every other stated declaration proved, the board was
  about to empty, so the remainder was re-swept: all eleven group files against the chapters
  themselves, every claimed Mathlib gap re-checked at the pinned toolchain, and `#print axioms`
  run on 36 candidate dependencies rather than trusting the sorry count.

  Published, each in its own file so a task filling it does not re-pin the golf tasks open
  against `Chernoff.lean`, `Concentration.lean` and `Entropy.lean`:

  | Node | Source | Why it was reachable |
  |---|---|---|
  | `perfectMatchingCount_le_prod_factorial` (#377) | Cor. 10.2.2, p. 180 | Both halves proved since #216/#254; only the four-step assembly was missing |
  | `measure_sum_ge_le_of_mem_Icc` (#378) | Thm 5.0.5, p. 70 | Mathlib's sub-Gaussian API now gives it with the source's exact constant |
  | `measure_infDist_le_iff_measure_lt_le` (#379) | Thm 9.4.8, p. 143 | Quotes nothing; needs neither isoperimetry nor this project |

  **The §9.4 correction is the one worth keeping.**  `concentration.md` said "every consequence
  runs through a quoted input", and that was true of every numbered result I had *listed* — but
  9.4.8 is not a consequence of the isoperimetric inputs at all.  It sits **upstream** of them:
  it is the statement of what the section's two languages have to do with each other.  I had
  audited my own list instead of the section.  **When a section is blocked by a quoted input,
  look for what sits upstream of that input, not only at what survives downstream of it.**

  **Confirmed still blocked, so this is not re-derived a third time**: §2.6 (no planarity,
  Euler or crossing number in Mathlib), §4.5 (no Mertens — the new `NumberTheory/Chebyshev.lean`
  has θ, ψ and π asymptotics but no sum of prime reciprocals), §9.5/§9.6 (Talagrand absent and
  omitted by the source), §4.4 and §8.3.3 and §9.3.3 (the source marks the key step "omitted"),
  §4.6.6 and §9.4.1/9.4.3/9.4.22 (route through a quoted geometric input), §6.6 Moser–Tardos
  (needs a model of the resampling process — the chapter's largest item, not a node).

  **Viable, held back with a named reason** — in rough order of readiness:
  * **Theorem 6.4.1's regular corollary** (p. 90) — a two-step consequence of the proved
    `exists_directed_cycle_length_dvd`, supplying `d` from `Real.isLittleO_log_id_atTop`.  Easy,
    and the best warm-up task on the board when one is next wanted.
  * **Corollary 8.1.7**, the Poisson limit for triangle-freeness at `p = c/n` (p. 118) — squeezes
    Janson's upper bound against Harris's lower bound, the one place in the corpus where the two
    pin a probability exactly.  **Held:** the two halves spell "triangle-free" differently
    (`¬(offDiagPairs T ⊆ edgeSet)` vs `CliqueFree 3`) and the bridging lemma does not exist.  That
    is a second declaration, so it is orchestrator work to author first.
  * **Corollary 10.4.6**, Loomis–Whitney in `n` coordinates (p. 192) — a near-clone of
    `card_sq_le_prod_card_image` with `shearer` for `shearer_triple`.  **Held:** it wants a
    dependent `∀ i, α i` where the 3-coordinate version has a flat product, and that spelling is
    a statement-level choice to settle centrally, not in a task.
  * **§5.2's exactly-equiangular bound** (p. 74, unnumbered) — `#S ≤ n` for unit vectors with all
    pairwise inner products equal to `α ≥ 0`, by linear independence rather than the source's
    Gram-matrix route.  **Held:** the source states the `n + 1` form for `α ∈ [-1, 1)`, which the
    linear-independence argument does not reach; publish the `α ≥ 0` form deliberately or not at
    all.
  * **Theorem 1.1.6**, Ramsey via alteration (p. 4) — §1.1 gives three successively better
    bounds and this project has the first and third (`lt_ramseyNumber`,
    `lt_ramseyNumber_of_local_lemma`) and not the middle.  **It appears in no roadmap file, in
    either direction**, which is the more useful finding: the group files track what the source
    defers, and they do not track what the source proves and nobody noticed.
  * **Theorem 10.3.3 (Blakey–Roy)** — `entropy.md` calls §10.3 blocked on hom counts and graphons;
    that is wrong for 10.3.3, whose conclusion is `hom(P₄, G) · n² ≥ (2 e(G))³`, entirely in ℕ and
    expressible with walk counts.  **Held for a real reason:** the entropy proof needs
    `H(Z | X, Y) = H(Z | Y)`, and `Entropy.lean` has no conditional-independence lemma at all.
    So the honest package is three nodes, not one.
  * **Theorem 1.3.3** (`m(k) = O(k² 2ᵏ)`, p. 11) — would sandwich §1.4 against the proved
    `not_isKChoosable_completeBipartiteGraph`.  **Held:** needs convexity of `a ↦ Nat.choose a k`,
    which I could not find in Mathlib; scope that before publishing.

  **`local-lemma.md`'s "§6.5's Latin transversal application — assessed, not yet stated" is
  stale**: `LatinTransversal.lean` has `exists_latin_transversal`, Setup 6.5.4 and Theorem 6.5.5.
  Same decay pattern the 2026-09-17 entry recorded, and the same cheap fix — grep the corpus
  before trusting a status line in this file.

- **2026-09-21 — the golf annealing pass, round two: five merged (#363–#367), 428 lines net removed, every one still axiom-clean.**
  `exists_conflictFree_of_card_le` 186→135, `exists_independent_transversal` 218→162,
  `janson_lower_tail_step_le` 391→254, `card_lt_of_triangleIntersecting` 208→135,
  `le_card_of_distinctSubsetSums` 242→130.  `#print axioms` on all five gives
  `[propext, Classical.choice, Quot.sound]` — checked after merging, not inferred from the gate.

  **The yield came from three shapes, and the ranking is stable enough to put in the task prose.**
  Largest first: (1) a lemma re-derived inline that already existed — Janson's 40-line binomial
  weight identity was the file's own `sum_powerset_weight_eq`, LocalLemma's 22-line measure
  argument was `measure_inter_conull` plus `prob_compl_eq_zero_iff`; (2) one argument spelled out
  twice, factored into a single in-body `have` — this is where the *structural* wins were, not
  just the line count; (3) `nlinarith` given an explicit product hint becoming `linarith`, which
  is strictly faster and more predictable.  Round one's prose named only (1); (2) and (3) are new
  and are now in #368–#375.

  **My own line-count estimates were badly wrong, in the same direction every time.**  This file
  had sized `le_card_of_distinctSubsetSums` at "~25 lines" and `card_lt_of_triangleIntersecting`
  at "~8 safe lines"; they came back at 112 and 73.  The cause is that I estimated *tidying* and
  the contributors changed *method* — the subset-sums proof dropped `Measure.pi`, `MemLp` and
  `IndepFun.variance_sum` for one induction over the powerset plus counting-form Chebyshev.
  **An estimate made by reading a proof prices the proof you can see, not the one that replaces
  it.**  Stop publishing per-target line estimates; publish the profile (`have` count, automation
  counts, repeated `have` names) and let the contributor find the method.

- **2026-09-21 — a golf that changes the method silently falsifies the docstring, and no gate check looks.**
  #365's docstring said "the engine is Mathlib's `meas_ge_le_variance_div_sq` (Chebyshev) with
  `IndepFun.variance_sum`; the `εᵢ` are a genuine product-Bernoulli family (`Measure.pi`)".  After
  the golf the proof uses none of the three, and `Mathlib.Probability.Distributions.Bernoulli` and
  `Mathlib.MeasureTheory.Integral.Pi` had no consumer left in the file.  Fixed in `36b41e1`.

  **The contributor could not have fixed it and should not have tried** — `skills/conventions.md`
  forbids a golf from touching the docstring, which is the right rule, because a docstring edit is
  exactly what `statement-immutability` cannot distinguish from a statement edit on a body-less
  declaration.  So this is structural, not a lapse: **every method-changing golf leaves an
  orchestrator debt, and it is invisible to the gate.**  `rebuild` is happy, `comparator` is happy
  — the statement really is kernel-identical — and the prose above it is now false.  Added to the
  post-merge routine: on any golf whose diff removes a named Mathlib lemma from the proof, grep
  the target's docstring for that lemma before recording the merge.

- **2026-09-17 — the project has exactly one unresolved mathematical question, and a `sorry` count hides which one.**
  `#print axioms` over every public theorem in the build, not a `grep` for `sorry`.  The tainted
  declarations form one chain, rooted at the held §11.3 corner:

      exists_containers_fingerprint_three_uniform   (the §11.3 hold — the sorry itself)
        → exists_containers_three_uniform
          → exists_shrunken_containers_of_many_triangles
            → exists_containers_triangleFree
              → card_triangleFreeGraphs_le          (§11.1's Erdős–Kleitman–Rothschild bound)

  **So the held §11.3 corner is load-bearing for Chapter 11's headline theorem** — invisible in a
  summary where "two sorries, one deliberate" reads as under control.  Resolving it is the
  highest-value open item, ahead of any new authoring, and **`δ` is no lever**: `n/√d` is
  `δ`-independent, so the corner cannot be dodged by shrinking `δ`.  By contrast
  `exists_container_round`'s `sorry` was **isolated**, because `exists_run_of_container_round`
  takes `IsContainerRound` as a *hypothesis* rather than citing the existence theorem — the right
  way to build on an open node.  **Standing check: report `sorryAx` reach, not `sorry` count**; a
  `sorry` in a leaf costs nothing, a `sorry` under a chapter's main theorem is the chapter, and
  the two look identical in a `grep`.  (`#print axioms` reads the built olean — rebuild first.)

- **2026-09-17 — I pushed a non-compiling commit, because my build check inverted on failure.**
  The cause was not the Lean error — a section that opened `SimpleGraph` but not `unitInterval` —
  but the shell: `lake build 2>&1 | grep -E "^error|✖" | head -3; echo "build ok"; git commit`.
  **`grep` exits 0 when it *finds* errors**, so the chain proceeded exactly when the build was
  broken, and I then reported "build ok" in my own output — asserting success from a command whose
  output I had misread.  **Rule: verification keys on the exit code, never on a grep that succeeds
  when things break** — `if lake build >/tmp/b.log 2>&1; then echo OK; else echo FAILED; fi`.
  And the standalone probe that passed beforehand is not evidence: it had `open unitInterval`,
  which the target section does not.  **A probe file's context is not the file's context** — an
  `import Mathlib` scratch file cannot tell you a name is in scope in a narrow one.  Typecheck in
  place before committing, not just in `/tmp`.

- **2026-09-17 — never add a declaration to a file that has an open task pinned to it, and the rest of the pin discipline.**
  #234 was pinned to `bb591afb` in `SecondMoment.lean`; I then pushed `8053d5b`, adding three
  declarations to the same file for #235.  `statement-immutability` compares the PR head against
  **current base**, not against the pinned commit, so it read the contributor's older file as
  having *deleted* three declarations their diff never touches, with `git merge-tree` clean.
  **This is deterministic, not a race**, and it fires however disjoint the edits are.  **Land all
  of a file's new statements before pinning any task to it, or publish successive tasks in
  different files.**  The rest, learned in pieces and all still binding:
  * **A worker's workspace is built at the pinned commit and workers do not rebase**, so keeping
    pins current is this role's job.  PR #42, built at a pin predating #32/#33, still held
    placeholder versions of two proved theorems; `sorry-delta` caught the revert (`base 2 → head
    3`) while the diff looked clean, which is what makes the failure confusing (2026-09-13).
  * **Re-pinning does not help a worker whose workspace already exists** — comment on every open
    *claimed* task whose `target_file` the merge touched.  **The check is per *file***, and
    Chapters 10 and 11 are where tasks sit open longest, so that is where pins rot (2026-09-16).
  * **Re-pinning a *claimed* issue re-adds `choir/available`**, since editing the body re-triggers
    `issue-intake`; strip it afterwards — `sync-leases` sees nothing wrong (2026-09-13).
  * **After repairing a statement, expect in-flight branches to revert it.**  PR #146's head
    lacked the `d ≤ 2δn` hypothesis its own base carried.  Re-pinning cannot help, so
    `statement-immutability` is the only backstop: never override it on a recently repaired file.
  * **After changing a file, re-test the mergeability of every open PR against it before pinging
    anyone** — I sent three nudges for a rebase my own consolidation had already made unnecessary.

- **2026-09-17 — a blocker note is a claim with an expiry date, and the only way to read one safely is to re-derive it.**
  Seven recorded blockers have been found stale, in both directions, each having cost weeks
  against the minutes a re-derivation costs:
  * **§2.2 "no Dirichlet"** — Mathlib has it, and **Theorem 2.2.1 never needed Dirichlet**: the
    finite proof takes a prime above `2 max |a|` and averages over `ZMod p`, wanting only
    `Nat.exists_infinite_primes`.
  * **§11.1 "needs `ex(n, H)`"** — `SimpleGraph.extremalNumber`, `Turan`, `TuranDensity`,
    `ErdosStoneSimonovits`, `Zarankiewicz` all exist; Theorem 11.1.2 is closer to a citation.
  * **§9.2 "Azuma is not in Mathlib; §9.3–§9.6 are downstream of it"** — Mathlib has grown
    `measure_sum_ge_le_of_hasCondSubgaussianMGF`, and **this project had already proved Azuma** as
    `measure_martingale_sub_ge_le`: six sections blocked behind a sorry-free theorem of our own.
  * **Triangle supersaturation, "missing, the most useful thing anyone could add"** —
    `CliqueFree.card_edgeFinset_le`, `farFromTriangleFree_iff`,
    `FarFromTriangleFree.le_card_cliqueFinset`, `triangleRemovalBound` and
    `triangleRemovalBound_pos` were all at the pin (2026-09-15).
  * **Hardy–Ramanujan (§4.5), "the most tractable of Chapter 4"** — wrong the other way.  Turán's
    proof needs `∑_{p ≤ n} 1/p = log log n + O(1)`, and Mathlib has no Mertens estimate in any
    form.  **Expressible is not tractable** (2026-09-15).
  * **`entropy.md`'s three "obligations left behind by reductions"** were all proved, its warning
    about `measureEntropy` named something that does not exist at the pin, and `local-lemma.md`'s
    Latin-transversal line and §2.4's "not yet assessed" were stale the same way.

  Both Mathlib misses were written from a search for the *statement's* vocabulary rather than the
  *proof's* inputs.  **Search for what the proof needs.**  Audit bullets now carry the date they
  were resolved rather than being deleted, so the staleness stays visible.  And **a written status
  list decays faster than the repository**: per-file theorem counts and an axiom sweep are the
  cheap ground truth, the prose audit is not.

- **2026-09-17 — Chapter 8's real blocker was a ground set, not a missing API (#193).**
  `janson.md` had priced five unstated asymptotic results as needing "a worked `G(n,p)` API".
  There was nothing to build: Mathlib *defines*
  `SimpleGraph.binomialRandom V p = setBer(Sym2.diagSetᶜ, p).comap edgeSet`, so `G(n,p)` already
  is a `setBernoulli`.  The obstruction is one type-level mismatch — Chapter 8's statements are
  fixed at `setBernoulli Set.univ p` and `G(n,p)`'s ground set omits the diagonal.
  `map_inter_setBernoulli` (`(setBer(v,p)).map (· ∩ u) = setBer(v ∩ u, p)`) is the whole transfer
  and unblocks Theorems 8.1.6, 8.1.10, 8.2.5, Corollary 8.1.7 and §8.3.2 at once, via
  `measurable_set_iff` (`fun_prop` does not do `Inter.inter` on `Set ι`), `setBernoulli_eq_map`
  and `Measure.infinitePi_map_pi` — which carries no countability hypothesis, so neither does the
  statement.  Brute-forced over all subsets of a 4-element ground set against 400 random
  `(p, u, v)` triples, 400/400.  **A blocker written at the wrong level of abstraction is worse
  than no note at all, because a note stops people from looking again.**

- **2026-09-17 — before publishing, confirm every lemma the route names appears earlier in the target file than the target.**
  I published `binomialRandom_no_triangle_le` above `janson_prob_none_le`, the theorem its route
  depends on, so as published it could not have been proved without a forward reference.
  `containers.md` already recorded the same failure for §11.2 — 11.2.1 is a corollary of 11.2.3,
  so the book's order put the dependency backwards — and I wrote that note before repeating the
  mistake in another chapter.  **The source's presentation order can encode a dependency
  backwards**: a textbook may state a weaker result first and strengthen it later, a Lean file
  cannot.  Being right about the order once does not transfer.

- **2026-09-17 — Shamir–Spencer needs `2 ≤ n`, and §6.3's docstring was wrong on three counts.**
  `measure_abs_sub_integral_chromaticNumber_ge_le` (Theorem 9.3.1) needs **`2 ≤ n`, which the
  source omits**: at `n = 1` the radius `λ √(n-1)` is zero, the event is everything, and the bound
  falls below `1` from `λ = 1`.  Third source hypothesis added in one session, after §6.3's
  `≤`→`<` and §2.4.4's `n ≥ 4`→`n ≥ 5`.  §6.3 corrected: the strictness is free because `2eΔ` is
  **irrational** for `Δ ≥ 1` (so `≤` and `<` coincide except at `Δ = 0`, where the non-strict form
  is false) rather than because of slack against Haxell; equalizing to a common part size is
  load-bearing, since heterogeneous parts break `e·p·(d+1) ≤ 1`; and the `- 1` in `d = 2mΔ - 1` is
  load-bearing, failing at `Δ = 2, m = 11` without it.

  **On four of the last five PRs the contributor found a better route than the one I published.**
  The prose earned its keep where it *verified facts and named traps* — brute-forced tightness
  checks, `ℕ∞.toNat ⊤ = 0`, "`omega` cannot evaluate `Nat.choose`" — and was dead weight where it
  prescribed tactics.  **Write down what is true and what will bite; stop short of choosing the
  proof.**

- **2026-09-17 — Proposition 2.4.4 is false as the source prints it, and two independent routes found the same off-by-one.**
  Zhao states it for `n ≥ 4`: a tetrahedron-free 3-graph has at most `(7/10) binom(n,3)` edges.
  At `n = 4` that is false — the 3-graph missing exactly one triple is tetrahedron-free with `3`
  edges against a bound of `2.8` — and the hypothesis has to be `5 ≤ n`.  Exhaustive search over
  all 3-graphs on `n ≤ 6` gives maxima `3, 7, 14`: false at `4`, tight at `5` and `6`.  The
  contributor found the same off-by-one **without computing anything**: the hypothesis is spent at
  `Nat.choose_pos (2 ≤ n - 3)`, because at `n = 4` the factor `binom(1,2)` is zero and the
  cancellation is invalid.  **This is the second source erratum, after §6.3's `≤` versus `<`, and
  both were found the same way: compute the small cases before stating the theorem.**  Neither
  would have surfaced by reading the proof — in both the proof is right and only the quantifier
  range is wrong.  **Publishing a dependent node only after its input lands was the right call**:
  a contributor proving 2.4.4 against a `sorry` would have produced a green PR whose theorem
  transitively depended on an unproved lemma — visible in `#print axioms`, misleading in the
  trust report.

- **2026-09-17 — the `whp` idiom, and why only one half of a threshold needs an `N`.**
  Written-out `∀ ε > 0, ∃ δ > 0, ∀ n p, p·n ≤ δ → …` rather than a `Whp` predicate, which would
  have to quantify over probability spaces whose type varies with `n` (`SimpleGraph (Fin n)`).
  The quantifiers cost one line and make `δ`'s independence from `n` and `p` *structurally
  visible* — it is supplied in the same `refine` line that binds them.  **The asymmetry between
  the two halves is the part worth keeping.**  Markov's error on the subcritical side is
  `(p·n)³/6`, uniform in `n`, so `δ` depends on `ε` alone; Chebyshev's on the supercritical side
  is `144/(p·n)³ + 144/(n·(p·n))`, whose two terms vanish for *different reasons* — the first once
  `p·n` is large, the second only once `n` is large as well — so no choice of scale alone controls
  it and that half needs its `N`.  **The shape of the estimate decides whether the idiom needs its
  `N`.**  Verified before stating: `binom(n,3) ≤ n³/6` without exception, `binom(n,3) ≥ n³/12` for
  `n ≥ 6`.  Alongside: **write `(μ).real S`, not `(μ S).toReal`**, since Mathlib's probability
  lemmas are stated in `Measure.real`; and `triangleCount` uses `Set.indicator` over a set of
  graphs rather than a filter on a clique predicate, because the measure ranges over *all* graphs
  on `Fin n` and no `DecidableRel G.Adj` is available there.

- **2026-09-17 — `card_sumFreeWindow` needs `3 ∤ p`, found by computing rather than reading.**
  The middle third of `ZMod p` is sum-free for every `p`, but `p - 1 ≤ 3|C|` **fails at every
  multiple of 3** — at `p = 3` the window is empty against `p - 1 = 2`, because the strict
  inequalities drop the two boundary residues.  Under `3 ∤ p` it holds and is tight for every
  `p ≡ 1 mod 3`.  Fourth hypothesis in one session that the source or my first draft omitted.

- **2026-09-16 — `private` in a published statement silently disables `comparator`.  The most expensive mistake of the session, and mine.**
  PRs #173 and #174 both failed `comparator` with `statement-mismatch` while every other check,
  `statement-immutability` included, was green — and neither diff touched a statement.  Lean 4
  mangles private names with the **module path** (`private def myPrivateFoo` compiles to
  `_private._stdin.0.myPrivateFoo`), and comparator builds the base tree under a `ChoirBase.`
  module prefix, so challenge and solution reference different constants and the statements cannot
  match as kernel terms for *any* diff.  `gate/verify/comparator.py`'s header states the
  assumption that fails — "Renaming modules never renames *declarations*" — true of public
  declarations only.  Reported upstream, not patched locally, since `~/.choir/checkout` is shared
  by every project on this machine.  I made the hole myself, adopting `IsGreedyRule` as `private`
  because both consumers lived in one file: namespace tidiness, at the cost of the project's
  strongest gate on two targets.  **Rule: anything reachable from a published statement is public,
  however local it looks** — `private` helpers stay safe only when no *public* statement mentions
  them.  The tell, if it recurs: `comparator` red, `statement-immutability` green, no statement in
  the diff.

- **2026-09-16 — `exists_container_round` was FALSE as I stated it; repaired, #176 re-pinned to `348f7d3`.**
  The contributor holding it refuted it with a kernel-checked counterexample rather than grinding
  on an impossible task.  The double-count clause rests on `3|Ae| = ∑_{v ∈ Av} deg_{Ae}(v)`, which
  is really `∑_{e ∈ Ae} |e|` and equals `3|Ae|` only under 3-uniformity; at `n = 1`, `c = d = 1`,
  `Ae = {∅}` the other clauses pin everything and the clause demands `3 ≤ 1`.  I reproduced the
  refutation against `main` first, then added `(∀ e ∈ Ae, e.card = 3)` to that clause alone and
  verified both directions.  **Fourth false statement this chapter produced, and the first I
  authored from scratch rather than transcribed** — same cause as the `2c√d` cut and the
  `degree_fromEdgeSet` mismatch: the individual estimates were right and the identity joining them
  was never checked.  *Verify the frame, not just the parts.*  **The process failure was the more
  expensive half**: filed at 22:40, read at 01:28, because the poller said "task #176 commented on
  — read its lease and sync the labels" and I synced the labels only, publishing two more nodes on
  the broken interface meanwhile.  **On every "commented on", read the comment body.**

- **2026-09-16 — §11.3's decomposition: the round (#176), the dense branch (#178) and the run (#180).**
  Three things settled *before* anything mentioning the interface was published.  **The run's
  dichotomy is satisfiable in all four halting modes** — `R` is existentially returned and the
  halting mode is a function of the fingerprint through the replay, so `R` may be chosen per mode;
  the branch that fires is decided uniformly by the handshake bound `|D| < |E|/(c√d)` on vertices
  deleted for forbidden-pair degree.  **§11.2's headline theorems cannot be called by anything**:
  both bind `δ` existentially, and `∃ δ > 0` carries no lower bound, so no hypothesis in `c, d, n`
  can guarantee their proviso — the δ-parametric obligations are the usable interface.  **#176 was
  safe to publish while the run was unsettled** because `IsContainerRound`'s clause hypotheses
  *are* the run's invariants, passed in rather than assumed globally, so strengthening the run
  cannot change what a rule must provide.  Published as one node rather than pre-split, because
  splitting would force the run's internal state into a public statement: **split when the
  interface is forced, not when the node is merely large.**  Composability was machine-verified —
  a scratch `example` applying the run's last four conjuncts to `exists_fingerprint_of_dense_pairs`
  at `F := E (S I)`.

  **The review found a real error in the docstring I authored.**  I wrote that vertices of
  `E`-degree above `2c√d` leave the alive set; with that cut the degree conjunct is **false**,
  because a survivor at the threshold still gains a round's worth of pairs (`Δ₂ ≤ c√d`) and
  reaches `3c√d`.  The cut has to sit a full `c√d` below the conjunct — at `c√d` — and the
  handshake is then the factor-2-weaker `|D| < 2|E|/(c√d)`, costing nothing against two orders of
  magnitude of slack.  **The statement was fine; only the prose was wrong**, as in all three of
  the session's defects: **a statement is checked by the kernel and by `comparator`; the prose
  around it is checked by nobody.**

  Two cautions downstream.  The covering conjunct is nearly free on its own (`R := ∅` satisfies
  it) and in the `E`-heavy mode this proof's `R` can be small, so **the container is near-`univ`
  there** — the content is in covering *conjoined with* the first disjunct.  And #178's obligation
  returns `(1 - 1/(10⁴M²))n` while the statement claims only `(1 - 1/(10¹⁰M⁴))n`: the sharper
  constant is proved and currently discarded.

- **2026-09-16 — §11.2 is closed, and the stability conjunct I added to the statement was free.**
  `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `exists_containers`,
  `exists_containers_fingerprint` and all three obligations, with **no `sorryAx`**.  Stability is
  discharged by `greedyRun_replay`, a fuel induction whose hypotheses are clauses 1 and 2 of
  `IsGreedyRule` verbatim and *not* the `kill` clauses — strictly weaker, the right shape.
  **The check that mattered most was structural, not mathematical.**  A degenerate `S` (constant,
  `≡ ∅`, or `S I = I`) would satisfy stability trivially while gutting the other four conjuncts,
  and an `A` secretly depending on `I` would hollow out the fingerprint form entirely.  Both are
  ruled out by *scope*: the `refine` supplies `S` and `A` as functions of `J` **before**
  `fun I hI => ?_` introduces `I`, so `A` is lexically incapable of closing over `I`.  **That is
  the first thing to look for on a fingerprint statement.**

- **2026-09-16 — the §11.3 corner is `exists_containers`' own proviso failing, and that localizes it exactly.**
  Theorem 11.3.1 is proved from one obligation (#172), and I did **not** publish its child.  The
  reduction contract's four questions did not all pass: the child says the right thing and the
  split is formally real, but **"is each child closable in one PR?" is a clear no** — it carries
  all of 11.3.1's mathematical content, plus the open `√d ≳ n` corner, plus a *strengthening* over
  the parent in that corner.

  **The corner is not a vibe about `√d ≳ n`.**  `exists_containers` at parameter `c_G` yields
  `δ_G = 1/(100 · max c_G 1)` and demands `d_G ≤ 2 δ_G n = n/(50 · max c_G 1)`, while at
  termination `d_G = 2e(G)/n = Ω(√d)` — so the subroutine is applicable only for `d = O(n²/c_G²)`,
  against an a priori bound of only `d < n²/2`.  **A `Θ(n²)` window where the graph container
  theorem cannot be applied to `G` at all.**  I verified the `δ` and the proviso in the source.
  It is the same `d ≤ 2δn` proviso that made `exists_containers` false before `1e4659a`, biting
  one chapter later — the third time that one proviso has driven a design decision here.  The
  composite is held for exactly this reason and no other: **the frozen 11.3.1 fingerprint form
  carries no regime hypothesis**, so proving it needs the whole range of `d`, and the range above
  `√d > n/(2·10⁴M³)` is precisely what node 5 owns.  **The composite is unblockable only by
  settling node 5, not by any amount of glue.**

  Checked rather than assumed: **`sync-graph` did not over-record the cross-chapter edge** —
  `hypergraph_container`'s `proof_uses` came back as the child alone, not `graph_container`; had
  it recorded that edge, a chapter resting on an open proof would compute as complete.  Amended in
  the file: the theorem had been inserted *above* the `### 11.3` header, and its docstring
  conflated "budget never collapses" (proved) with "budget ≥ 2" (false for `n²/4 < d`).

- **2026-09-16 — there are two "dense corners" in Chapter 11, and I conflated them before catching it.**
  **§11.2's corner is `δn < d ≤ 2δn`** (graph containers, now closed); **§11.3's is `√d ≳ n`** on
  #99, where the parent's own budget `⌊n/√d⌋₊` is only guaranteed `≥ 1`, and that one is still
  open.  `containers.md` distinguishes them explicitly at both mentions.  Worth recording because
  the two have the same name, the same shape, and opposite status.

- **2026-09-16 — I published an obligation its own author asked me to withhold, and the statement was true.**
  The author of #166 flagged `exists_dense_fingerprint` as neither provable nor refutable — an
  open window of relative width `(c-1)δ` above `δn`.  Well-motivated and wrong: **the window is an
  artifact of building the order by degree.**  The statement asks only for *some* order in which
  every vertex has `|N(v) ∪ Pred(v)| ≥ δn`; built greedily it always exists, because for `j < δn`
  and `|P| = j` some `v ∉ P` has `|N(v) \ P| ≥ δn - j` — otherwise
  `n(d - δn) < j(2cd + j - n - δn)`, positive on the left and `≤ 0` on the right once `c ≥ 1`
  forces `cd ≤ n/50`.  Machine-checked across 300,000 points of the feasible dense regime (the
  normalized `(2cd + j - n - δn)/n` maxes out near `-0.96`) before publishing.  **The lesson,
  stated next to its mirror image:** `containers.md` records three statements published *false*
  and believed true (the `d ≤ 2δn` proviso); this is the first published *true* and believed
  false, and both came from reasoning about one construction instead of about the statement.  The
  author had probed clique unions, clique-plus-matching and Hi/Lo degree sequences and found every
  one covered.  **Repeated failure to refute is evidence the statement is true, not evidence the
  corner is hard.**

- **2026-09-16 — `choir worker heartbeat` is a no-op, and the loop runs itself at AUTO.**
  `cmd_heartbeat` passes no `session`, its subparser has no `--session` and does not resolve the
  workspace, and the holder check compares the `(login, session)` *pair* against a lease whose
  `holder_session` is always a real id — so it returns before writing, every time.  **`refreshed:
  false` carries no information**, and a lease goes stale at 24h despite correct heartbeating, so
  a stale-reclaim can land on actively-worked code.  Run `choir orch poll` **backgrounded, never
  in the foreground**: it blocks for up to `max_wait_seconds`, and a long-lived foreground process
  is what the OOM killer takes first while contributors' `lean` builds spike to 1–2 GB each.
  Backgrounded, the process exiting *is* the wake-up, so repeated kills degrade the cycle into a
  periodic check rather than a hang.  **Do not read the OOM history as licence to stop and wait
  for the overseer** — at AUTO the orchestrator runs the whole loop, and the only escalations are
  a new axiom, a statement that looks wrong, and a policy change.  This machine is
  memory-constrained: **don't run `lake build` in the orchestrator checkout except to verify a
  statement being authored** (2026-09-13).  **When the board is empty, the bottleneck is usually
  the orchestrator, not the contributors** — both §11.3 tasks were claimed within five minutes.

- **2026-09-16 — check the new-declaration count first; it tells you how much judgment a PR needs.**
  Four of five diffs in one batch added **zero new top-level declarations** — a single `sorry`
  replaced by a body whose every auxiliary fact is a local `have`.  That empties the review
  surface in the one place the kernel cannot help: with the target statement kernel-identical to
  base, a clean axiom closure and no net-new sorries, a local `have` cannot smuggle anything.
  Two PR bodies over-reported the same day — a miscount, and a claimed derivation nothing in the
  diff performs.  Neither affected the mathematics, but **the reason to care is economic**: their
  self-reports are what made the reviews cheap, and a verification claim corresponding to nothing
  devalues the whole report.  Claim what you did, not what would have been reassuring.

- **2026-09-16 — the in-repo gate overlay does not follow `choir update`; only `upgrade-project.sh` moves it.**
  Resynced to Choir `258a6d3` (`05c9542`) after checking that `gate/checks.py` was
  **byte-identical** across those 27 commits, so `REQUIRED_PRESENT` gained nothing and no open PR
  could be stranded by required-but-absent.  That is why six open PRs needed no re-auditing.

- **2026-09-12 → 2026-09-16 — `set-priority`/`set-difficulty` immediately after `create-task` drops `choir/type:prove`.**
  Seen on nine of nine, ten of twelve, and again on #176 — a read-modify-write race against label
  state GitHub has not settled.  `gh issue edit --add-label` is additive and cannot drop the
  others.  **List the new issue's labels once after publishing, because an untyped task still
  reads as a task.**  Same batch hazard: write task prose with placeholder cross-references and
  fill the issue numbers in after `create-task` returns them.

- **2026-09-15 — two of my Chapter 11 statements were FALSE, one already merged: Zhao's own proviso is missing from his theorem box.**
  `exists_containers_fingerprint` (#98) and `exists_containers` were both false for every
  `c ≥ 3/2`; `Kₙ` forces `δ ≥ 1/2` and a disjoint union of 3-vertex paths forces `δ ≤ 1/3`, both
  verified numerically before anything was touched.  The missing hypothesis is **`d ≤ 2δ|V|`,
  which the book states on printed p. 207 *inside the proof idea* and omits from the theorem
  box** — **a textbook's theorem box is not always the whole hypothesis list.**  Added at
  `1e4659a` with the counterexamples in the docstrings; `exists_containers` had merged as a
  declared reduction onto the false lemma, so it was proved-modulo-a-false-statement, not unsound.
  Found by the stage-two review of PR #143, which had inherited the defect into two new public
  statements and was closed without deleting its branch, the repair not being local.  **A PR that
  surfaces a false statement two levels upstream of itself is worth more than one that merges** —
  the fourth author-side false statement, all four found by reading rather than by any gate check.
  **`Kₙ` and "disjoint union of stars" are the standing test pair for Chapter 11 statements**;
  #146's two obligations were checked against them and survive, since `n ≤ 2` is vacuous and
  `n = 3` and `Kₙ` impose only *upper* bounds on `δ`, a smaller `δ` being a weaker claim.  **A
  collapsing budget — an existential forced empty — is the failure mode to test for in this
  chapter**, and a statement whose constraints are all one-directional cannot exhibit it.

- **2026-09-14 → 2026-09-16 — task prose is checked by nothing; the diagnostic order is statement, then route, then decomposition.**
  Three published routes have been wrong where the statement was fine.  `entropy_le_logb_card`
  (#84) was pointed at Mathlib's `ConcaveOn` Jensen API and at `Finset.inner_le_nnorm_mul_nnorm`,
  **which is Cauchy–Schwarz, not Jensen**, when `Real.log_le_sub_one_of_pos` does it in a few
  lines.  Janson II's route prescribed `𝔼 Δ_T = q²Δ` under independent `q`-sampling, which breaks
  because `D` may contain diagonal pairs surviving with probability `q` — restricting to the
  off-diagonal `E` fixes it and removes a case split.  And `Nat.succ_mul_choose_eq`, named as "the
  Mathlib-side lever" in a docstring and a task, **does not exist at this pin**; it was renamed to
  `Nat.add_one_mul_choose_eq`, and two contributors re-derived it by hand.  Statements get
  `statement-equiv`, numerical checks and a stage-two reading; routes get nothing.  **When a task
  is abandoned with no note, re-read the route before concluding the task is hard** — and only
  once statement and route survive does repeated abandonment mean "decompose", as #15 and #60
  did, split along the seam where each bundled a probabilistic argument with pure analysis.

- **2026-09-15 — a liveness check is only valid at the instant of the destructive action, and your working directory is shared state.**
  I closed #124 and deleted its declaration at 05:32; it had been claimed at 05:23 with PR #141
  opened at 05:27, and the lease check justifying it had been run during an earlier review.
  Reverted byte-identical to the PR's base — and **the contributor's version was the better
  architecture**, so the retirement was wrong on the merits too.  The mirror case: a decomposition
  I published was superseded while being published, and the contributor offered to re-route their
  finished proof through my two nodes — declined, both nodes retired.  **A direct proof that
  exists beats a two-part proof that does not.**  Separately, `git add -A` while a review subagent
  held a patch in the shared checkout put 147 lines of PR #140's proof into two commits that
  contradict their own messages; **history was deliberately not rewritten**, because `main` is
  shared and open tasks pin commits on it.  Stage explicit paths; review subagents must not mutate
  the working tree.

- **2026-09-15 — `golf` means same pinned statement, shorter body, nothing else moved.**
  #121 was published as a `golf` task but asked for a deletion and a `private` → public promotion,
  so no correct implementation could have passed `statement-immutability`, and PR #136 was blocked
  for doing exactly what the task asked.  **`merge-override` was considered and rejected**: the
  check was enforcing the rule it exists for, and overriding a correct check to cover an
  orchestrator mis-specification is how a gate becomes decorative.  **Consolidation that deletes,
  renames, changes visibility, or relocates is orchestrator work, never a task.**

- **2026-09-15 — the statement layer is the orchestrator's responsibility regardless of queue depth.**
  An unclaimed task costs nothing; an unstated theorem is never proved.  **A strengthening nobody
  consumes is a liability, not a bonus** — Theorem 4.3.5 is stated non-strictly and without the
  book's non-triviality hypothesis, which would have forced every caller to discharge it, and
  Lemma 4.3.7 uses the general `1 - (1-q)^m ≤ p` rather than the book's `q = p/m` (direction
  checked numerically, because it inverts easily).  **Roadmap chapter boundaries need not match
  file boundaries**: 4.3.7 lives in `Correlation.lean` because it is a `setBernoulli`-and-upper-
  sets statement.  A conjecture in the source is never transcribed as a theorem.

- **2026-09-13/14 — the Janson statements were false without `[Countable ι]`, and the tell generalises.**
  The measurable space on `Set ι` is the product σ-algebra, so `{R | S i ⊆ R}` is non-measurable
  for uncountable `S i` and `setBernoulli` silently returns an *outer* measure; at `p = 1` the
  bound is false outright.  **The generalisable tell: Mathlib gated everything substantive in
  `SetBernoulli.lean` behind `section Countable`, and the statement was built on the ungated part.
  When upstream fences part of an API, a statement resting on the unfenced remainder deserves a
  second look.**  The converse also bit: `setBernoulli_inter_eq_mul_of_disjoint` does **not** need
  the instance, its proof going through `indep_iSup_of_disjoint`, which takes `Set ι`.  I dropped
  the binder *after* the reporting contributor's PR merged — removing it first would have made
  their branch read as *adding* the instance and tripped `statement-immutability` on a PR that
  changed nothing.  **Sequencing matters when acting on a contributor's finding about the
  statement they are working against.**  (`setBernoulli_inter_le_mul` keeps the instance; Harris
  needs it.)  My first draft of the two shared interface lemmas carried `MeasurableSpace ι` /
  `MeasurableSingletonClass ι` binders: it type-checked in isolation and would have been unusable
  from `Janson.lean`.  **Check a new interface lemma by applying it from its intended call site,
  not by checking that it elaborates.**  And `setBernoulli` is uniform-`p` only, which Janson's
  lower tail is not — `setBernoulliPi` is in `Correlation.lean` with
  `setBernoulli_eq_setBernoulliPi` proving it a faithful generalisation.  **That specialisation
  lemma is the point; a definition that merely elaborates demonstrates nothing.**

- **2026-09-13/14 — the reduction contract, and the two ways it is misread.**
  A proof that leans on an unproved sibling must declare one: PR #40 was mathematically correct
  and failed `comparator` with `illegal-axiom` because it calls a placeholder, so `sorryAx` enters
  the target's closure while `sorry-delta` passes.  This is **designed** — under `sorry = block`
  comparator refuses `sorryAx` on an ordinary submission precisely so a green gate means
  *unconditionally proved*.  **Do not "fix" this by moving the project to `sorry = report`.**  The
  second misreading, on #122: a target can be fully proved, add no placeholder of its own, and
  still fail, because its dependency's own obligation is in the closure.  `children` may name
  **any declaration already in the project that carries a placeholder**, and `sorry-delta` Rule B
  only examines counts that *rose*, so citing a pre-existing obligation is free.  **Read
  `gate/verify/` when two checks appear to contradict each other** — deducing a general rule from
  one red run is how the fix gets deleted.  Three more: a declared reduction **becomes
  unconditionally proved automatically when its obligation lands**, no resubmission needed;
  **read the reduction block, not the summary** (one body's bolded line said "fully proved" while
  the block correctly declared an open child); and publishing a `prove` task per new node is a
  *separate* step from adding the node, easy to drop when several land at once.

- **2026-09-13 — three author-side statements were false at degenerate `n`, and the tell was behavioural every time.**
  Both Chernoff bounds (`card_filter_le_exp_mul`, `card_filter_abs_le_exp_mul`) omitted `0 < n`:
  at `n = 0` the empty sum is `0` and the threshold `λ √0` is `0`, so the single sign sequence
  satisfies the condition while the bound is below `1`.  `exists_nearly_equiangular` claimed its
  bound for every `n`: false at `n = 0` (no unit vector exists, yet `2 ^ (c · 0) = 1` forces `S`
  non-empty) and at `n = 1` for small `ε` (only `±1` are unit, inner product `-1`); now
  `∃ c n₀, ∀ n ≥ n₀`.  And `measure_sub_integral_ge_le` was false without `hf : Measurable f` —
  bounded differences does not imply measurability, a Mathlib measure applied to a non-measurable
  set returns its *outer* measure, and a Bernstein-set indicator puts the left side at `1`.
  Machine-checked counterexamples were built before any statement was touched.  **Rule: when a
  statement's bound grows with `n`, check `n = 0` and `n = 1` before publishing it** — the cause
  is the same each time, transcribing a book statement that says "for every `n`" when the
  mathematics is asymptotic.  **And the tell was never a failed check**: each issue was claimed
  and released with no PR, and `metrics struggle` reports nothing for abandoned claims.  **Read
  the statement of any task that gets released without a PR.**  The remaining five statements were
  then audited proactively for the same defect and are sound.

- **2026-09-13 → 2026-09-15 — author the shared interface before publishing tasks against it.**
  Chapter 6's tasks each built their own uniform two-colouring measure; retiring the duplication
  cost three golf tasks and ~284 lines, and the need for the interface was visible when the first
  of those tasks was written.  Chapter 10 was done the other way — a **shared entropy layer proved
  by the orchestrator before any task was published**, because Mathlib has `Real.negMulLog`,
  `Real.binEntropy` and `Matrix.permanent` but no Shannon entropy of a discrete random variable.
  Parallel work against one pinned base reproduces this structurally: three contributors
  independently wrote the same binomial-weight identity, and two independently produced the same
  128-line averaging proof, character-for-character, five minutes apart.  Nobody erred.  **The
  post-merge duplication sweep is a standing duty, not an occasional one** — a contributor cannot
  see the other consumers from inside one task — and the collapse is a `golf` task, sequenced
  *after* the proofs in flight land.  A shape issue that nothing needs yet is **recorded and not
  built**.  Relatedly, before merging a parallel batch, confirm no two PRs add a declaration of
  the same name and that each diff is a single hunk deleting one `sorry`: **the gate cannot see
  this**, since `axiom-honesty` and `statement-immutability` check each PR against its own base
  and never against its siblings.

- **2026-09-13 — statement-level decisions in Chapters 10 and 11 that the files do not explain.**
  Chapter 10 is **counting**, not measure-theoretic, and `condEntropy` is defined as the book
  defines it, as an expectation over `y`, **so that the chain rule stays a theorem** rather than
  disappearing into an unfolding.  **`triangle_intersecting`'s diagonal-pair hypothesis is
  load-bearing: without it the statement is false by `2ⁿ`.**  **Vertex sets in Chapter 11 are
  `Fin n`**, not an arbitrary finite type: every theorem reads "for every `c` there is a `δ` that
  works for all graphs", so `δ` is chosen before the graph and hence before its vertex type, and
  `∃ δ, ∀ {V : Type*} …` cannot be written — the universe cannot be bound under the existential.
  `IsTriangleFreeEdgeSet` is an `abbrev`, not a `def`, so `Decidable` resolution sees through it.
  And **Chapter 11 differs from every chapter before it: the source does not prove its main
  theorems**, deferring to Morris' lecture notes, so its tasks invite a decomposition proposal
  rather than a proof.

- **2026-09-12 — bootstrap facts that cannot be re-derived.**  Toolchain pinned to
  `leanprover/lean4:v4.33.0` (Mathlib `v4.33.0`): the newest release the comparator tags, so the
  kernel statement gate runs on every PR.  Lean's own newest is `v4.33.1`, which the comparator
  does not tag; the overseer chose `v4.33.0` knowing **the pin cannot change later**.  Policy:
  automation `auto`, axioms `net_zero`, sorries `block`.  Two traps from the same period:
  `ramseyNumber k = sInf {n | RamseyProperty n k}` and `Nat.sInf ∅ = 0`, so **every lower bound on
  `R(k, k)` is false unless the set is known non-empty** (hence `exists_ramseyProperty`, since
  Mathlib has no Ramsey theorem to supply it); and the symmetric local lemma is instantiated at
  weight **`1/(d+2)`, not the book's `1/(d+1)`**, which is `1` at `d = 0` and so inadmissible.

- **2026-09-12 / 2026-09-17 — two definitional choices, both checked rather than assumed, both of the kind that gets re-litigated.**

  **§4.2's `m(H)` maximises over vertex *subsets*, not over `SimpleGraph.Subgraph`** — an equality,
  not a weakening: within a fixed vertex set the densest subgraph is the induced one, and every
  subgraph has a vertex set.  It also keeps the definition free of `Subgraph` finiteness instances
  and of any `Decidable` hypothesis, since `Set.ncard` needs neither.  Checked against Example
  4.2.8 (`ρ = 7/5`, `m = 3/2`), and `integral_copyCount` brute-forced over all graphs on `n ≤ 4`
  against five shapes for `H`: 80/80.

  **The Chapter 5 / Chapter 6 convention split has a reason, and it is not taste.**  `Decisions
  that still bind` records the Chapters 1–3 rule; this is the boundary further up.  Chapter 5 is
  **counting**, because both its applications end in existence claims about finite objects and its
  proofs are "Chernoff, then union bound", which is a count.  Chapter 6 is **measure-theoretic**,
  because Definition 6.1.1's independence-from-a-family is strictly stronger than pairwise
  independence and has **no counting surrogate**.  Spencer's Ramsey bound (Theorem 1.1.9) is filed
  under `local-lemma` rather than `introduction`, because the local lemma is what proves it.

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
- §2.2 large sum-free subsets — *both halves of this note were wrong, corrected 2026-09-17.*
  Mathlib **does** have Dirichlet's theorem, in `NumberTheory/LSeries/PrimesInAP.lean`
  (`Nat.forall_exists_prime_gt_and_eq_mod`).  And more to the point **Theorem 2.2.1 does not need
  it**: the finite proof picks a prime above `2 max |a|` and averages over `x ∈ ZMod p`, needing
  only `Nat.exists_infinite_primes`.  `IsSumFree` was a one-line orchestrator debt, now paid, with
  the middle-third window and its two facts published as #225.
- §2.5 unbalancing lights — needs a central limit estimate.
- §2.6 crossing number — needs Euler's formula for planar graphs.
- §10.3 Sidorenko — needs homomorphism counts and graphons; and its general case is **open
  mathematics**, so only the proved special case could ever be stated.

**(c) Real work on infrastructure that does exist.**  Statable whenever there is capacity; these
are the honest growth path.
- §9.2 Azuma — *stale note, resolved 2026-09-17*: Azuma **is** proved here, as
  `measure_martingale_sub_ge_le` in `Concentration.lean`, and that file has no `sorry`.  The
  conditional sub-Gaussian step its own docstring calls "the work" was done.  §9.3–§9.6 are
  therefore **not blocked**, and §9.3 (chromatic number of `G(n,1/2)`) is the next node in
  Chapter 9 — it needs a vertex-exposure martingale, not new analysis.
- Chapter 8's five asymptotic results — *resolved 2026-09-17*: the blocker was never a missing
  `G(n,p)` API but the ground-set mismatch now isolated as `map_inter_setBernoulli` (#193).
- §10.2 Kahn–Lovász — needs two orchestrator-authored definitions first (a count of perfect
  matchings, and the bipartite double cover; note `boxProd` is the **Cartesian** product and
  would silently build the wrong graph).
- §4.3 Bollobás–Thomason, §4.1/§4.2 thresholds, §4.4 clique number — all need an `ε`–`N` or
  `whp` idiom plus, for §4.2, a definition of `m(H)`.  *(The `whp` idiom was settled 2026-09-17;
  what remains of this bullet is `m(H)` and `ρ`.)*
- §11.1.3 / §11.1.5 — *both halves resolved 2026-09-17*: `whp` is settled, and `ex(n, H)` is
  Mathlib's `SimpleGraph.extremalNumber`.  11.1.3's lower bound is stated as #203.
- §2.4 hypergraph Turán sampling — *stale note, resolved*: assessed and stated 2026-09-15 as
  `card_le_of_tetrahedronFree`, with Lemma 2.4.3 and Proposition 2.4.4 stated 2026-09-17.

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


# Status, 2026-09-18: one `sorry` remains, and it is open mathematics

`lake build` is green, the board is empty, no PR is open, and the corpus is **276 theorems /
350 public declarations** with exactly **one** `sorry`: `Containers.lean:2548`,
`exists_containers_fingerprint_three_uniform` — the §11.3 corner, which is an open
mathematical problem and not unfinished formalization.

**Chapter 6 was completed today, end to end.**  §6.1–§6.2 (all three local-lemma forms,
2-colourability, Ramsey), §6.2.6 (infinite vertex sets, via Tychonoff), §6.2.10
(Erdős–Lovász multicoloured translates), §6.2.11 (Beck), §6.3 (independent transversals),
§6.4 (Alon–Linial directed cycles), §6.5 (lopsided local lemma, derangement bound,
Erdős–Spencer Latin transversals), §6.6 (sparse `k`-CNF satisfiability).  Also completed:
§5.3 (Hajós) and §9.3.4 (Shamir–Spencer four-value concentration) with its Lemma 9.3.5.
Every headline theorem was axiom-audited to `[propext, Classical.choice, Quot.sound]`.

## What is left, and why — the four blockers are not interchangeable

| Section | Blocker | Clearable by Mathlib work? |
|---|---|---|
| §2.6 crossing number | no planarity, Euler's formula or `crossingNumber` in Mathlib | yes |
| §7.2.6 | no FKG for *continuous* product measures (Mathlib's is finite-lattice only) | yes |
| §9.4–9.6 | no Hamming-cube isoperimetry, Talagrand convex distance, subadditive Euclidean functionals | yes |
| §11.1.5 | inherits `sorryAx` from the §11.3 corner | **no** — needs the mathematics settled |

Never targets, for a different reason: Theorem 6.6.3, Theorem 7.2.5 and Proposition 7.2.6 are
**quoted or sketched** rather than proved by the source, and Lemma 9.3.3's second half says
"details again omitted".  Question 2.4.1, Conjecture 11.1.4 and Conjectures 6.5.8/6.5.9
(Ryser, Ryser–Brualdi–Stein) are **open problems** and must never be stated as theorems.

## Two habits that did the most work

**Re-derive a recorded blocker before trusting it.**  Seven were checked; five were wholly
stale (Chapter 8's G(n,p) API, §9.2's Azuma, §11.1's `ex(n,H)`, §2.2's Dirichlet, §7.1.5's
function form), one was half-stale (§7.2.6 — Mathlib *does* have Gaussians), and one was
confirmed real (§2.6).  The same disease runs the other way: §2.3's "planned, not stated"
headings described work finished long ago, and `lake build` caught me restating Caro–Wei.
**Grep the source tree — and Mathlib — before believing any roadmap heading in either
direction.**  That check caught `CliqueFree.card_edgeFinset_le` one step before I duplicated it.

**Instantiate a copied numeric hypothesis at small parameters before publishing.**  §6.4's
constant was transcribed from the source and is *wrong for the dependency count the argument
establishes* — `(1+d)(1+D)-1`, not `dD`; it fails at `k=5, d=21, D=1`.  Caught before any
worker saw it, unlike the four source errata in §2.4.4, §9.3.1, §6.3 and §6.5.6, which were
the source's own.


# Final state, 2026-09-18 (end of session)

**281 theorems, 24,965 lines, 27 files, one `sorry`.**  `lake build` green, board empty, no PR
open.  The single `sorry` is `Containers.lean:2548`,
`exists_containers_fingerprint_three_uniform` — the §11.3 corner, an **open mathematical
problem**, not unfinished formalization.

Completed today: §1.4, §2.5, §5.3, all of Chapter 6, §7.2's Harris remark, §9.3.4.  38 PRs
merged.

## Coverage of all 47 sections

Every section of the book is now formalized, staged, or blocked with a re-derived and named
cause.  The three real blockers are:

| Section | Missing | Clearable by Mathlib work? |
|---|---|---|
| §2.6 | planarity, Euler's formula, `crossingNumber` | yes |
| §9.4 | Brunn–Minkowski, Harper, Johnson–Lindenstrauss, sphere concentration | yes |
| §9.5–9.6 | Talagrand's inequality (also *omitted by the source*) | yes |
| §11.1.5 | inherits `sorryAx` from the §11.3 corner | **no** |

Quoted or sketched by the source, therefore never targets: Theorems 6.6.3, 7.2.5, 9.4.1,
9.4.3, Proposition 7.2.6, Talagrand's inequality, and the second half of Lemma 9.3.3.
**Open problems, which must never be stated as theorems**: Question 2.4.1, Conjecture 4.6.2
(Erdős, $300), Conjectures 6.5.8 and 6.5.9 (Ryser, Ryser–Brualdi–Stein), Conjecture 11.1.4,
and Question 1.4.1.

## The three habits that produced the last stretch

1. **Re-derive a recorded blocker before trusting it.**  Nine checked: five wholly stale, one
   half-stale, three real.  Two more were stale in the opposite direction — a heading claiming
   "planned, not stated" for work finished long ago, which `lake build` caught only when the
   duplicate declaration collided.
2. **Sweep the table of contents against the corpus.**  With the board empty and one `sorry`
   left, extracting all 47 section headings and grepping each against the code found §1.4,
   which had been sitting unstated behind a roadmap line that said exactly that.  Nothing else
   had surfaced it in months.
3. **Instantiate a copied numeric hypothesis at its smallest case.**  §6.4's constant was
   transcribed from the source and was wrong for the dependency count the argument supports;
   Theorem 2.5.2 was outright false at `n = 0`.  Both were caught before a worker saw them.
   This is also how the five source errata were found.

# Annealing pass, 2026-09-20: four golf tasks published

The board was empty — no open tasks, no open PRs, no axioms, one `sorry`, `sync-graph --check`
clean.  With the corpus stable in every chapter, the ready frontier is `golf`, which on this
toolchain (`v4.33.0`) is also the best-verified task type the project has: the target exists in
base, so `verify-comparator` binds the statement at the kernel level over its whole dependency
closure.

**Targets were chosen from the gate's own style audit, not by eye.**  `gate.verify.style`'s
`find_decl_spans` over all 29 files: 683 declarations, 16 at or above 150 lines, 9 above the
project's 200-line threshold.  Each candidate was then read for a *nameable* collapse, because
this project's golf tasks specify the exact edit (#145 named the block to delete, the line to
replace it with, and predicted −134 to within one).  A task that only says "this is long" is
below that bar and produces churn.

Published, all `choir/priority:low`:

| # | target | lines | expected | difficulty |
|---|---|---|---|---|
| 350 | `lovasz_local_lemma_symmetric` | 175 | −120 | easy |
| 351 | `measure_martingale_sub_ge_le` | 209 | −40 to −55 | easy |
| 352 | `uniformWeights_heaviest_lightest_le` | 321 | −45 to −70 | medium |
| 353 | `exists_shrunken_containers_of_many_triangles` | 595 | −100 to −170 | hard |

#350 is the candidate recorded on 2026-09-13 and never published: the inline re-derivation of
the general local lemma, which was correct when written (PR #44 opened 73 seconds before #41
merged) and has been redundant ever since.  Verified still present at HEAD, lines 252–368, and
`lovasz_local_lemma`'s signature does discharge it at the constant weight `1/(d+2)`.

#351 and #352 rest on **Mathlib lemmas re-derived inline** — `Real.cosh_le_exp_half_sq` (36
lines of two-point-measure construction proving a statement Mathlib states verbatim, and which
this project already calls at `Chernoff.lean:90`) and `abs_pow_sub_pow_le`.  Both were confirmed
present in the pinned Mathlib and in scope from the target's file before publishing.

**One target stays skipped, and the reason is invalidation risk rather than low reward:**

- `exists_run_of_container_round` (221) — **has no consumer anywhere in the repo.**  It exists
  to be fed to the `sorry` at `Containers.lean:2548`.  Until that closes, its intermediate shape
  may still be revised, which would invalidate the golf.  Revisit only if 2548 ever closes.

**The rest of the skip list was wrong and is deleted.**  It held `janson_lower_tail_step_le`
("~40 real lines out of 391"), `le_card_of_distinctSubsetSums` ("~25"),
`exists_independent_transversal` ("~12"), `card_lt_of_triangleIntersecting` ("~8 safe lines")
and `exists_dense_fingerprint` ("most of the win needs shared private lemmas, so is not
available to a golf task").  Four were published in round two anyway and returned 137, 112, 56
and 73 lines; the fifth is #368.  **Every estimate was low, and low by the same mechanism** —
each priced a tidy-up of the proof as written, and each contributor instead changed the method
(see the 2026-09-21 log entry).  The two "calibrated spots a golfer would be tempted to clean"
in the subset-sums entry were a real risk and were correctly left alone by the contributor, so
that warning belongs in the task prose; the line estimate attached to it did not.

**Do not price a golf target by reading its proof.**  Publish the profile instead — `have`
count, automation counts, which `have` names recur — and let the contributor find the method.

**Duplication is largely already annealed.**  A 10-significant-line window scan across the whole
corpus found only 7 cross-declaration duplicate groups, and most are the LocalLemma/Lopsided
mirror, which is mathematically expected.  The shape that produced #147 is close to exhausted;
remaining golf value is per-proof length and inlined Mathlib, not de-duplication.

## Orchestrator work queued, not publishable as tasks

Each of these needs a deletion, a visibility change, or a new shared declaration, all of which
`skills/conventions.md` puts outside a `golf` task.  **Do these before the next golf batch, not
after** — committing to a target file re-pins every open task against it.

1. `Alterations.lean` 1756–1797 duplicates 1452–1478 (find `j < N` with `t j ≤ w v ≤ t (j+1)`
   via `min ⌊y⌋₊ (N-1)`, including the `hcast` sub-block) across `uniformWeights_eq_null` and
   `uniformWeights_heaviest_lightest_le`.  A shared private lemma cuts ~40 and ~25.  #352's brief
   tells its contributor explicitly to leave this alone.
2. `Entropy.lean` — extract the intersecting-family bound from `card_lt_of_triangleIntersecting`
   (1331–1370) as `two_mul_card_le_two_pow_of_intersecting`.  Mathlib's `Finset.Intersecting.card_le`
   does **not** apply off the shelf: it is over `univ` in a BooleanAlgebra, while here the ground
   set is `powerset (A S)` and `{X // X ⊆ A S}` carries no BooleanAlgebra instance.
3. `Containers.lean` — the ord/decode weight encoding at 212–235 inside `exists_greedy_rule` is a
   near-verbatim specialization of `exists_degree_order` (1189–1215).  A generalized private lemma
   serves both (−20 and −27).  Note the doc comments at 1181–1183 and 1361–1367 deliberately
   explain why the graph and hypergraph weights differ: generalize, do not "unify".
