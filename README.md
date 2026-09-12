# ProbMethodCombinatorics

A [Choir](https://github.com/Weber-GeoML/Choir)-managed formalization, in Lean 4 with
Mathlib, of Yufei Zhao's lecture notes *Probabilistic Methods in Combinatorics*
(MIT 18.226, Fall 2022).

The source is in [`sources/`](sources/README.md); the plan is in
[`roadmap/`](roadmap/README.md); project conventions contributors should follow are in
[`skills/`](skills/conventions.md).

## Contributing

Work is published as issues labelled `choir/available`.  Claim one and submit a pull
request from a fork; every submission is verified by the gate before a human reviews it.
Ask the project's overseer for the joining prompt, which points your agent at the
contributor playbook.

## Layout

| Path | Contents |
|---|---|
| `ProbMethodCombinatorics/Intro.lean` | §1.0 — large bipartite subgraph |
| `ProbMethodCombinatorics/Ramsey.lean` | §1.1 — lower bounds to Ramsey numbers |
| `ProbMethodCombinatorics/SetSystems.lean` | §1.2 — Bollobás' two families theorem |
| `ProbMethodCombinatorics/PropertyB.lean` | §1.3 — 2-colourable hypergraphs |
| `ProbMethodCombinatorics/Expectation.lean` | §2.1, §2.3 — Szele, Caro–Wei, Turán |
