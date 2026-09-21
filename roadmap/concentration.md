# Group: `concentration` — Chapter 9

What the chapter establishes: **a Lipschitz function of many independent random variables is
concentrated.** Chapter 5's Chernoff bound is the case where the function is a sum; the point
here is that no sum structure is needed.

This is the longest chapter in the book (44 pages) and the frontier stated for it is
deliberately one node. The rest is planned, for reasons given below.

## Already upstream

- **`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`** — Hoeffding's lemma (Lemma 9.2.12):
  a mean-zero variable in an interval of length `ℓ` has `𝔼[e^{tX}] ≤ e^{t²ℓ²/8}`. This is the
  analytic engine of the whole chapter.
- **`measure_sum_ge_le_of_iIndepFun`** — Hoeffding's inequality for sums of independent
  sub-Gaussian variables, plus the surrounding `ProbabilityTheory.HasSubgaussianMGF` API.

Mathlib has **no** Azuma inequality and **no** bounded differences inequality; a search for
`azuma` and `mcdiarmid` returns nothing.

## `bounded_differences` — `measure_sub_integral_ge_le`

Theorem 9.1.3: if changing coordinate `i` alone moves `f` by at most `c i`, then

    ℙ(f - 𝔼f ≥ λ) ≤ exp(-2λ² / ∑ᵢ cᵢ²).

Stated over `Measure.pi`, so independence is structural rather than hypothesised, and with no
martingale in the statement — the martingale is an artefact of the *proof*, not of the claim.
That matters for formalisation: a contributor may take the source's route (Doob martingale plus
Azuma) or go directly through Mathlib's sub-Gaussian machinery, and the statement does not
prejudge it.

Note the constant: `exp(-2λ²/∑cᵢ²)`, not `exp(-λ²/(2∑cᵢ²))`. The source is careful about this
— Theorem 9.2.8's form of Azuma gives the weaker constant, and recovering the sharp one needs
Theorem 9.2.9, the Doob-martingale refinement. Remark 9.2.13 explains why 9.2.9 is genuinely
more versatile: the `cᵢ` there can be smaller than a worst-case Lipschitz bound.

## Planned, not stated

- ~~**Azuma's inequality** (Theorems 9.2.7–9.2.9)~~ — **proved**, as
  `measure_martingale_sub_ge_le`; this bullet was stale from 2026-09-15 to 2026-09-17.  Original
  note kept below for its reasoning. Stating it needs martingales with filtrations,
  which Mathlib has (`MeasureTheory.Martingale`) but which is a heavier commitment than the
  applications require. Worth stating if a contributor wants the source's route to the node
  above; ask first.
- ~~**Theorem 9.3.1** (Shamir–Spencer)~~ — **stated 2026-09-17** as
  `measure_abs_sub_integral_chromaticNumber_ge_le` (#209), on the back of three pieces landed the
  same day: `binomialRandom_eq_map_graphOfExposure` (#201), `abs_sub_chromaticNumber_le_one`
  (#207), and the already-proved `measure_sub_integral_ge_le`.  The "small amount of interface"
  the old note asked for turned out to be the **vertex-exposure product**, and which exposure is
  chosen is not a detail: `n - 1` nonempty vertex blocks give `exp (-2 λ²)`, where `C(n,2)` edge
  coordinates would give only `exp (-2 λ² / C(n,2))`.  That gap is the content of the theorem.

  **It needs `2 ≤ n`, which the source does not state.**  At `n = 1` the radius `λ √(n-1)` is
  zero, the event is everything and the left side is `1`, while the right side falls below `1`
  from `λ = 1` (about `0.0007` at `λ = 2`).  Zhao's interest is asymptotic; the finite form needs
  the hypothesis, and it is also what makes `0 < ∑ cᵢ²` true.
- **Lemma 9.3.3** and the clique-number route to Bollobás' theorem, which the source gives as
  an alternative to the Janson route of §8.3.
- **§9.4 isoperimetry, §9.5 Talagrand's inequality, §9.6 the Euclidean travelling salesman
  problem.** These are research-level and each needs substantial machinery Mathlib lacks —
  a concentration function on the Hamming cube, Talagrand's convex distance, and a
  subadditive-Euclidean-functional framework respectively. They are listed so the plan is
  honest about the chapter's extent, not because they are close.


## Mathlib audit for the unstated remainder (2026-09-15)

Checked what each blocked item's *proof* needs, not just its statement's vocabulary — the
distinction that has now produced two wrong roadmap notes elsewhere in this project.

- **Azuma (9.2.7–9.2.9).** **Stated 2026-09-15** as `measure_martingale_sub_ge_le` (Theorem
  9.2.8), task in the board.  9.2.7 is the `cᵢ = 1` case and is not stated separately.
  Mathlib **has** `Martingale` with `Filtration`
  (`Probability/Martingale/Basic.lean:53`) and conditional expectation, and it **has** Hoeffding
  for sums of *independent* sub-Gaussians (`measure_sum_ge_le_of_iIndepFun`,
  `Moments/SubGaussian.lean:780`) — which is what this project's already-proved
  `measure_sub_integral_ge_le` runs on. What it does **not** have is Azuma itself: the
  martingale-difference version. So this is **real work on existing infrastructure**, not a
  missing-infrastructure block like §4.5's Mertens. Statable whenever someone wants it.

  *Search warning:* grepping Mathlib for "Azuma" returns `Mathlib/Algebra/Azumaya/*` — Azumaya
  algebras, entirely unrelated. A name-substring hit is not evidence the result exists.

- **9.3.1 Shamir–Spencer, §9.4 isoperimetry, §9.5 Talagrand, §9.6 Euclidean TSP.** ~~All still
  research-level, and all downstream of Azuma.~~ **Corrected 2026-09-17: this was wrong twice
  over.**  Azuma has been proved here since 2026-09-15 (`measure_martingale_sub_ge_le`,
  sorry-free), so nothing was downstream of a gap; and 9.3.1 does not go through Azuma at all —
  it runs on the bounded differences inequality, which was proved even earlier.  9.3.1 is now
  stated (#209).  §9.4–§9.6 remain genuinely out of reach, but for their own reasons, not this
  one.

Note the project already has the chapter's headline result — the bounded differences inequality
— proved via the *independent* route rather than through martingales, so nothing here blocks
Chapter 9's existing content.


## §9.4 re-derived 2026-09-18: blocked, and the blocker is deeper than recorded

The old entry said §9.4 "needs a concentration function on the Hamming cube".  Re-checking
against Mathlib turns up more than that, and nothing that has since appeared:

- **Brunn–Minkowski**: absent.  The only occurrence of "Brunn" anywhere in Mathlib is a
  bibliography line in `Analysis/Convex/Intrinsic.lean`'s docstring.  Theorem 9.4.1
  (Euclidean isoperimetry) is the source's first tool and it *cites* Brunn–Minkowski rather
  than proving it, so 9.4.1 is not a target either way.
- **Harper 1966** (isoperimetry in the Hamming cube, Theorem 9.4.3): absent, and quoted by
  the source rather than proved.
- **Johnson–Lindenstrauss** (Theorem 9.4.22): absent.
- **Concentration of measure on the sphere** (Corollaries 9.4.12, 9.4.14): absent, and
  derived in the source from the quoted isoperimetry.

So the shape of §9.4 is: two quoted geometric inputs, then consequences drawn from them.  The
consequences are the interesting mathematics but they are not reachable without the inputs,
and the inputs are not in Mathlib and are not proved by the source.  **Blocked, confirmed by
re-derivation rather than assumed** — unlike five of the other blockers in this roadmap, which
turned out stale when checked.

Note the contrast with §7.2, checked the same day.  There the *headline* results were equally
out of reach (Theorem 7.2.5 quoted, Proposition 7.2.6 sketched with a Laplace-method constant),
but the source's Harris remark alongside them **was** reachable once restated for
`binomialRandom` instead of the Gaussian surrogate — it is now
`prod_le_binomialRandom_forall_ncard_neighborSet_le`.

**§9.4 has the same salvageable remark, and this file said it did not.**  The sentence that
stood here — "every consequence runs through a quoted input" — was wrong about **Theorem
9.4.8**, the equivalence of the geometric and functional formulations of concentration of
measure.  It quotes nothing, uses no isoperimetry, needs no input from this project, and its
proof is two substitutions: `A ↦ {f ≤ m}` one way, `f ↦ Metric.infDist · A` with median `0`
the other.  It is stated as `measure_infDist_le_iff_measure_lt_le` in
`ConcentrationEquivalence.lean` and published as #379.

The error was a scoping one rather than a factual one: every *numbered consequence I had
listed* runs through a quoted input, and I checked the list rather than the section.  9.4.8 is
not a consequence of the isoperimetric inputs — it is the definition-level statement that says
what the section's two languages have to do with each other, and it sits **before** them in the
dependency order.  **When a section is blocked by a quoted input, check whether anything in it
sits upstream of that input** rather than downstream.


## §9.5 and §9.6 re-derived 2026-09-18: blocked twice over

**§9.5 (Talagrand).**  The source is explicit: *"We omit the proof of Talagrand's inequality
(see the Alon–Spencer textbook or Tao's blog post) and instead focus on examples."*  So the
central theorem of the section is **quoted, not proved** — the same category as Theorem 6.6.3,
Theorem 7.2.5 and Proposition 7.2.6, and therefore not a target regardless of Mathlib.  It is
*also* absent from Mathlib (no `Talagrand`, no convex distance).  The section's applications
all run through it.

**§9.6 (Euclidean travelling salesman).**  No subadditive-Euclidean-functional framework in
Mathlib, and the section's method is Talagrand's inequality, so it inherits §9.5's blocker.

This completes the re-derivation of every blocker in this project.  The final tally over
nine checked: **five wholly stale** (Chapter 8's G(n,p) API, §9.2's Azuma, §11.1's `ex(n,H)`,
§2.2's Dirichlet, §7.1.5's function form), **one half-stale** (§7.2.6 — Mathlib does have
Gaussians, but FKG for continuous product measures is genuinely missing), and **three
confirmed real** (§2.6, §9.4, §9.5–9.6).  Two further entries turned out stale in the
opposite direction — §2.3's "planned, not stated" headings described work finished long ago,
and §2.5's "harder, a compactness argument" was Lemma 2.5.3, four lines in the source and now
task #332.

The habit that produced all of this is cheap: before trusting any roadmap entry, grep the
source tree for the declaration, grep Mathlib for the upstream result, and read what the
source actually claims to prove.  Three greps and a page of the PDF.


## §9.4 refinement, 2026-09-18: the proof machinery exists even though the theorem does not

Re-checking §9.4 once more turned up something the earlier note missed.  Harper's theorem is
absent from Mathlib, but **its standard proof technique is present**:

- `Mathlib/Combinatorics/SetFamily/Compression/UV.lean` — UV-compression, with
  `UV.card_compression` (compression preserves size) and
  `UV.card_shadow_compression_le` (compression does not increase the shadow).
- `Mathlib/Combinatorics/SetFamily/Compression/Down.lean` — down-compression.
- `Mathlib/Combinatorics/SetFamily/KruskalKatona.lean` and `Mathlib/Combinatorics/Colex.lean`.
- `Mathlib/InformationTheory/Hamming.lean` — `hammingDist`.

So "no Hamming-cube isoperimetry" is true of the *theorem* and misleading about the *route*.
Anyone resuming should start from `UV.compression`.

**But the gap is real and larger than it looks.**  Mathlib's compression results are aimed at
the **shadow** of a `k`-uniform family, which is what Kruskal–Katona needs.  Harper's
vertex-isoperimetric inequality concerns the `t`-neighbourhood of an *arbitrary* subset of the
cube and needs compressions toward initial segments of the **simplicial order** — a related
but distinct argument, with the simplicial order, the neighbourhood-monotonicity of
compression, and the initial-segment characterisation all still to be built.

**And it is out of scope for this project anyway**: the source *quotes* Harper (Theorem 9.4.3)
rather than proving it, exactly as it quotes Euclidean isoperimetry (9.4.1) and omits
Talagrand outright.  Formalising them extends past the book rather than completing it.  That
is a separate undertaking of research scale — three major theorems — and should be scoped as
its own project, not smuggled in as a task here.


## A startable plan for Harper, should §9.4 ever be taken on

Recorded because "blocked" is not actionable and this is the only one of the four missing
inputs that is pure combinatorics and in this corpus's domain.  **It is a separate project,
not a task for this board** — the estimate below is weeks, not hours.

*Statement.*  For `A ⊆ {0,1}ⁿ` and `B` a Hamming ball with `|A| ≥ |B|`, `|Aₜ| ≥ |Bₜ|` for all
`t`.  It suffices to prove `t = 1` and iterate.

*Vocabulary to author* (none of it in Mathlib): the `t`-neighbourhood of a subset of the cube,
the Hamming ball, and the **simplicial order** — sort by Hamming weight, break ties
lexicographically.  `Mathlib/InformationTheory/Hamming.lean` supplies `hammingDist`;
`Mathlib/Combinatorics/Colex.lean` supplies the colex order, which is the tie-break, so the
simplicial order should be assembled from `Colex` rather than defined from scratch.

*Proposed decomposition.*

1. `nbhd` and `hammingBall`, plus `card_nbhd_mono` and the value of `|hammingBall c r|` as a
   partial sum of binomials.  Routine.
2. The **slice decomposition**: writing `A = A₀ ∪ A₁` by the last coordinate,
   `(A₁-neighbourhood)₀ ⊇ (A₀)₁ ∪ A₁` and symmetrically.  Routine and self-contained; this is
   the inductive engine.
3. `compress i A` (down-compression in coordinate `i`) with `card_compress` and
   `card_nbhd_compress_le` — compression preserves size and does not increase the
   neighbourhood.  `Mathlib/Combinatorics/SetFamily/Compression/Down.lean` is the closest
   existing analogue and should be read first, but **it is not reusable as-is**: Mathlib's
   compression lemmas bound the *shadow* of a `k`-uniform family, and Harper needs the
   `t`-neighbourhood of an arbitrary subset.
4. Iterated compression terminates (a decreasing integer potential, e.g. the sum over `A` of
   the position in the simplicial order).
5. **The delicate step**, and the one to scope before committing to the project: a set fixed
   by every `compress i` need *not* be an initial segment of the simplicial order.  Harper's
   proof needs a further argument at this point, and a formalisation that does not plan for it
   will stall here.  Budget most of the effort for step 5.
6. Assemble, then iterate `t = 1` to general `t`.

*Why it is not on the board.*  Steps 1–4 are routable today; step 5 is not, and this project's
standing rule is not to publish a node whose route cannot be supplied.  Publishing 1–4 alone
would leave four merged lemmas pointing at a theorem nobody can finish — the same shape as
stating a definition that makes every downstream result true and useless.

## §9.4 scoped properly, 2026-09-20: step 5 is routable, and the plan above names the wrong compression

The plan above was scoped on the overseer's instruction, with the specific question "is step 5
routable, and at what cost".  **It is — but not for the operation the plan names, and the plan's
own status claims are stale.**

**The down-compression route is dead, and step 5 is genuinely unfixable on it.**  `cubeCompress`
is fixed by `A` exactly when `A` is a down-set, and down-sets are not close to initial segments.
Counted by brute force over every subset of `Qₙ`:

| n | down-sets | of those, not initial segments | of those, **strictly worse than the ball** |
|---|---|---|---|
| 2 | 6 | 1 | 0 |
| 3 | 20 | 11 | 3 |
| 4 | 168 | 151 | 85 |

The 2-face `{∅, 1, 2, 12} ⊂ Q₃` is a down-set with `|N| = 8` against `7` for the ball of the same
size.  There is no classification to appeal to, and the bad cases are the generic ones, not a
residue to mop up.

**Harper's actual proof uses the codimension-1 compression `Cᵢ`**: replace each `i`-section by
the initial segment of the simplicial order of the same size.  There the characterisation is
complete — a set fixed by every `Cᵢ` is an initial segment, **or** one explicitly described
exception per `n`, dispatched by a set inclusion.  Verified by brute force here, independently of
the source:

- `|N(Cᵢ A)| ≤ |N(A)|` for every `A` and every `i`, `n ≤ 4`.
- `N(initial segment)` is an initial segment, `n ≤ 6`.
- For each `n ≤ 4` there is **exactly one** fully-compressed non-initial-segment, and it is
  Leader's: `{1}`, `{∅, 2}`, `{∅, 1, 2, 12}`, `{∅, 1, 2, 3, 4, 12, 13, 23}`.  Each has
  `|B| = 2ⁿ⁻¹`, and none beats the initial segment.

Source: Imre Leader, *Extremal Combinatorics* (Cambridge, Michaelmas 2004),
`https://www.dpmms.cam.ac.uk/~par31/notes/extcomb.pdf`, Theorem 1 / Lemma 2 / Corollary 3; the
same text appears in his *Intersecting Families* notes (PCMI/IAS, July 2025).  Frankl–Füredi,
*A short proof for a theorem of Harper about Hamming-spheres*, Discrete Math. 34 (1981) 311–313,
is the alternative route and the first place to look if this one stalls.

**The slice decomposition does not let you avoid the characterisation.**  A pure slice induction
reduces Harper to a numerical claim about `νₙ(m) = |N(Iⁿₘ)|` that is tight almost everywhere and
needs the structure of `νₙ` — which is what the characterisation pays for.  Nor does the weaker
ball form that §9.4's corollary actually needs close inductively: in the case `a₀ < |B_r|` the
induction yields only `|N(A)| ≥ a₁ + |B_r|`, and `a₁` can sit barely above `|B_{r-1}|`.  Exact
Harper is required.

**Mathlib's `Colex`/`KruskalKatona` do not transfer.**  Harper needs weight-then-**lex** with the
**upper** shadow; Mathlib has colex with the lower shadow.  A colex tie-break makes the theorem
false — at `n = 4`, `|A| = 8`, lex gives `|N| = 14` and colex `15`.

### What `HammingCube.lean` actually supplies, against the six steps above

| Step | Status |
|---|---|
| 1. `nbhd`, `hammingBall`, monotonicity, `\|ball\|` | partial — `cubeNbhd`, `cubeBall`, `cubeNbhd_mono` exist; `cubeBall` has no lemmas at all |
| 2. slice decomposition | partial — `cubeNbhd_one_slice_superset` is `⊇` only, and only for the last coordinate; the route needs the equality and an arbitrary coordinate |
| 3. compression | complete, **off-route** — the three `cubeCompress` results are correct but Harper's proof never uses down-compression |
| 4. termination | untouched |
| 5. characterisation | untouched |
| 6. assemble, iterate `t` | untouched |
| the simplicial order itself | untouched, and the largest missing piece — `cubeCompressAt` cannot be stated without it |

So about one and a half of six steps, with a third built on the wrong operation.  **The earlier
claim that "what remains is one identified step" was wrong** and the README has been corrected.

### Cost, and the decision that comes first

**18 nodes** as decomposed — the simplicial order and rank, initial segments nested,
`N(initSeg)` is an initSeg (the hard one), sections respect the order, `cubeCompressAt`,
compression does not increase `N`, the rank-sum potential, existence of a fully compressed set,
inversion implies a complementary pair, structure of the exception, the top-coordinate lemma,
the exception inclusion, Harper at `t = 1`, ball = initial segment, general `t`.  Realistically
**22–26 tasks, 2–4 of them hard**, once node 6 splits under contact.

**Settle the representation before publishing node 1.**  The file is a leaf — nothing imports it
— so switching is cheap now and expensive later.  The `lexMinDown` monotonicity that node 6 turns
on is awkward in `Fin n → Bool` and natural over `Finset (Fin n)`, where `min (x ∆ y) ∈ x`
characterises the lex order directly; nodes 1, 2, 12 and 14 also shorten there.  Against it:
`hammingDist` and the existing 270 lines are in `Fin n → Bool`.

One refinement on the textbook: Leader dispatches the odd and even exceptions by separate
computation, but the inclusion `N(C) ⊆ N(B)` holds in **both** parities for a uniform reason —
every up-neighbour `w = x₀ ∪ {j}` has the witness `v = w \ {max x₀}`, which needs only
`max x₀ = n`, true for all `n ≥ 3`.  So the endgame is one inclusion lemma, not two counts.
`n ≤ 2` is `decide`.

**Still not published.**  Whether to take Harper on at all is the overseer's call, and so is the
representation.  Nothing here is on the board.
