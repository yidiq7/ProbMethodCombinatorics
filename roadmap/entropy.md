# Group: `entropy` — Chapter 10

What the chapter establishes: Shannon entropy as a **counting tool**. Every application has the
same shape — put a uniform measure on the objects you want to count, so that `H = log₂ (number
of objects)`, then bound `H` above by an entropy inequality. The inequality is always
subadditivity or its refinement, Shearer's lemma.

**Almost nothing here is in Mathlib.** It has `Real.negMulLog` and `Real.binEntropy` (the binary
entropy function on `[0,1]`, with concavity and monotonicity), and `Matrix.permanent`. It has
**no** Shannon entropy of a discrete random variable, no conditional entropy, no chain rule, no
Shearer, no Brégman–Minc, no Sidorenko, no Loomis–Whitney. The `measureEntropy` that turns up in
a search is Kolmogorov–Sinai entropy of a dynamical system and is unrelated.

## Convention

**Counting, not measure** — the `Finset`/`Fintype` convention of Chapters 1–3 and 5. The chapter
never needs a general measure: every random variable in it is a function on a finite sample
space, every distribution is either uniform or a conditioned uniform, and every conclusion is a
statement about the cardinality of a finite set. Using `MeasureTheory.Measure` here would buy
nothing and would make `probOf` an `ENNReal`-valued nuisance.

## The shared layer

Authored centrally in `Entropy.lean`, **proved, not left to tasks**, and every Chapter 10 task
is told to build on it. This is the lesson from Chapter 6, where `fairCoin`/`uniformColoring`
had to be extracted after three tasks had each rebuilt it:

- `probOf p X s` — `ℙ(X = s)`, the mass of the fibre;
- `entropy p X` — `∑ s, -pₛ log₂ pₛ`, Definition 10.1.1. The book's convention "if `pₛ = 0` the
  summand is zero" is automatic, since `Real.logb 2 0 = 0`;
- `condEntropy p X Y` — Definition 10.1.6, written as the book writes it, as an expectation over
  `y`. **Deliberately not defined as `H(X,Y) - H(Y)`**: that would make the chain rule an
  unfolding instead of a theorem, and the chain rule is the content of §10.1;
- `uniformPMF A` — the uniform mass function, which is the distribution every application uses;
- and five proved lemmas: `probOf_nonneg`, `probOf_le_one`, `sum_probOf`, `uniformPMF_nonneg`,
  `sum_uniformPMF`.

Joint entropy needs no definition of its own. `H(X, Y)` is `entropy p fun ω => (X ω, Y ω)` and
`H(X₁, …, Xₙ)` is `entropy p fun ω i => X i ω`; `Prod` and `Pi` types over finite index types
carry the `Fintype`/`DecidableEq` instances the definition needs.

`triangleEdges a b c` is also defined here, for the statement of Theorem 10.4.9.

## §10.1 Basic properties

The five nodes below are the interface the rest of the chapter consumes, so they are the
priority. `entropy_chain_rule` and `entropy_subadditive` are marked high: everything downstream
of them is blocked on them, and they are the only two that carry real content
(`condEntropy_le_entropy` is three lines given the other two).

- `entropy_nonneg` — `0 ≤ H(X)`. Easy.
- `entropy_uniform_bound` — Lemma 10.1.4, `H(X) ≤ log₂ |support X|`, the bound that converts
  entropy back into a count. The support is passed as a containing finset rather than formed
  with `Finset.filter`, because filtering on `probOf p X s ≠ 0` would need a `Decidable`
  instance on `ℝ` and **the project does not add `Decidable` instances**.
- `entropy_chain_rule` — `condEntropy_eq_sub`, i.e. `H(X ∣ Y) = H(X,Y) - H(Y)`, which is
  Lemma 10.1.7 rearranged.
- `entropy_subadditive` — Lemma 10.1.8 for two variables. The one analytic step in the section;
  `Real.log_le_sub_one_of_pos` is likely shorter in Lean than a Jensen argument.
- `entropy_drop_conditioning` — Lemma 10.1.10, `H(X ∣ Y) ≤ H(X)`.
- `entropy_subadditive_general` — Lemma 10.1.8 for `n` variables, by induction over a
  `Finset` of coordinates rather than over `n`.

Mutual information (Remark 10.1.9) and the data processing inequality (Remark 10.1.11) are
remarks in the notes and are not stated.

## §10.4 Shearer's lemma

- `shearer` — Theorem 10.4.5. **The engine of the chapter**; three of the four applications
  reduce to it, so it is the highest-leverage open task in Chapter 10. The proof is the chain
  rule along a fixed order of the coordinates, plus dropping conditioning, plus the covering
  hypothesis. It needs `H(X ∣ Y, Z) ≤ H(X ∣ Z)` — the *conditioned* form of dropping
  conditioning, which is **not yet stated**; the task tells the worker to ask for it rather than
  bury it.
- `shearer_triple` — Theorem 10.4.1, the `s = 3, k = 2` case. Stated separately because the
  direct four-line proof does not wait on `shearer`, and because `loomis_whitney_discrete`
  consumes exactly this form.

Corollary 10.4.7, the restriction form `|ℱ|^k ≤ ∏ |ℱ|_{A_j}|`, is **not yet stated**; it is the
natural intermediate for `triangle_intersecting`, and that task is told to ask for it.

## Applications

- `loomis_whitney_discrete` — Theorem 10.4.3, `|S|² ≤ |π_{xy}S| |π_{xz}S| |π_{yz}S|`. Stated for
  a finset in a product of three arbitrary types: nothing in it is about `ℝ`. Corollary 10.4.4,
  the continuous statement about volumes and areas, is the limiting version and is **not
  stated** — it needs a measure-theoretic approximation argument that has nothing to do with the
  chapter's method.
- `triangle_intersecting` — Theorem 10.4.9, `|𝒢| < 2^(binom(n,2) - 2)`, the theorem Shearer's
  lemma was invented for. Graphs are recorded as edge sets in `Finset (Sym2 (Fin n))`, with an
  explicit hypothesis excluding diagonal pairs; **without that hypothesis the statement is
  false** by a factor of `2ⁿ`.
- `bregman_minc` — Theorem 10.2.1. The hardest task in the chapter. Radhakrishnan's proof turns
  on revealing the entries of a random permutation in a *random* order, and on the step the
  notes leave as "Why?" — that for fixed `σ`, the greedy count `Nᵢ` is uniform on `[dᵢ]`.
- `binomial_tail_entropy` — Theorem 10.1.12. Filed here for bookkeeping, but the shortest proof
  is the moment-generating-function one, which touches no entropy at all; the task says so.

## Planned, not stated

- **§10.3 Sidorenko's inequality** (Theorems 10.3.3 and 10.3.7, Conlon–Fox–Sudakov). Blocked on
  infrastructure the project does not have: homomorphism counts `hom(F, G)` and graphons. The
  entropy argument itself is short, but stating the conclusion is not. Revisit once a
  `hom`-counting definition exists — and note that the Möbius graph case (Remark 10.3.8) is
  **open mathematics**, so any statement here must be the proved special case, not the
  conjecture.
- **Corollary 10.2.2 (Kahn–Lovász)**, `pm(G) ≤ ∏ (d_v!)^(1/2d_v)`. Reduces to `bregman_minc`
  via the bipartite double cover, but the notes leave the reduction as an exercise.
- **Steiner triple systems** (§10.2) and the **Kahn–Zhao** bound `i(G) ≤ i(K_{d,d})^{n/2d}`
  (Theorem 10.4.12) and **Galvin–Tetali** (Theorem 10.4.14). All are real formalization
  projects on their own; they are the right place to expect reductions rather than single PRs.
