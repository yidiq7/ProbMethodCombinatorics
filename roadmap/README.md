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

| Group | Chapter | State |
|---|---|---|
| [`introduction`](introduction.md) | 1 | stated, in progress |
| [`expectation`](expectation.md) | 2 | partly stated, in progress |
| [`alterations`](alterations.md) | 3 | stated, in progress |
| [`second-moment`](second-moment.md) | 4 | engine stated; asymptotics planned |
| [`chernoff`](chernoff.md) | 5 | stated, in progress |
| [`local-lemma`](local-lemma.md) | 6 | stated, in progress |
| [`correlation`](correlation.md) | 7 | stated, in progress |
| [`janson`](janson.md) | 8 | stated, in progress |
| [`later-chapters`](later-chapters.md) | 9–11 | planned, not yet stated |

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

- **2026-09-13 — the blocking poller cannot survive on this machine; use `poll --once`.**
  `choir orch poll` blocks for up to `max_wait_seconds`, and a long-lived process is what the
  OOM killer takes first while the contributor agents' `lean` builds spike to 1–2 GB each.  It
  was killed six times.  **`poll --once` does one check and exits**, which survives, but it
  gives no wake-up — so on a memory-constrained machine the loop is overseer-driven rather
  than self-driving: check with `poll --once`, act, stop.  Nothing is lost either way, because
  the loop keeps no state in the process; it all lives in this repo.

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
