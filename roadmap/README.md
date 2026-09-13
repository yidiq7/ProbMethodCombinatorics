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
| [`later-chapters`](later-chapters.md) | 7–11 | planned, not yet stated |

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
