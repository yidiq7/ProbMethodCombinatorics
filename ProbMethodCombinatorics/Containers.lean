import ProbMethodCombinatorics.Entropy
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Chapter 11: Containers

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Chapter 11.

The container method replaces a hopeless union bound over all independent sets of a hypergraph
with an efficient one over a small family of **containers**: sets that are not much larger than a
maximum independent set, few in number, and between them covering every independent set.

**Nothing in this chapter is in Mathlib**, and unlike Chapters 7–10 the source does not supply
complete proofs: Theorems 11.2.1 and 11.3.1 are given as algorithms plus a proof *idea*, with the
details delegated to Morris' lecture notes. So the obligations here are genuinely research-level,
and the honest expectation is reductions rather than single-PR proofs.

## Two decisions about how the statements are written

**Vertex sets are `Fin n`, not an arbitrary finite type.** Every theorem in the chapter has the
shape "for every `c` there is a `δ` that works for *all* graphs", so the `δ` must be chosen before
the graph — and hence before its vertex type. Quantifying over a universe-polymorphic `V` inside
an `∃ δ` is not expressible; `Fin n` costs no generality, since every finite graph is isomorphic
to one on `Fin n`, and keeps the cardinality arithmetic in `ℕ` where it belongs.

**Asymptotics are written out, never as `o(1)`.** `2^(n²/4 + o(n²))` becomes "for every `ε > 0`
there is an `N` such that for all `n ≥ N`, …", the idiom already used by
`exists_nearly_equiangular` in Chapter 5. The `≫` of Theorem 11.1.5 would need the same
treatment.

Graphs are recorded as edge sets in `Finset (Sym2 (Fin n))`, as in Chapter 10's
`card_lt_of_triangleIntersecting`, and `triangleEdges` is imported from `Entropy.lean` rather
than restated.
-/

namespace ProbMethodCombinatorics

open Finset

/-- A set of unordered pairs is the edge set of a triangle-free simple graph: no pair is
degenerate, and no three vertices have all three of their pairs present.

An `abbrev` rather than a `def` so that `Decidable` resolution sees through it: the project does
not declare `Decidable` instances, and the predicate is decidable componentwise. -/
abbrev IsTriangleFreeEdgeSet {n : ℕ} (G : Finset (Sym2 (Fin n))) : Prop :=
  (∀ e ∈ G, ¬ e.IsDiag) ∧ ∀ a b c : Fin n, ¬ triangleEdges a b c ⊆ G

/-- `maxCodegree k H` is `Δ_k(H)` of §11.3: the largest number of edges of the hypergraph `H`
containing a fixed set of `k` vertices. -/
def maxCodegree {α : Type*} [Fintype α] [DecidableEq α] (k : ℕ) (H : Finset (Finset α)) : ℕ :=
  (univ.filter fun A : Finset α => A.card = k).sup fun A => (H.filter fun e => A ⊆ e).card

/-- Codegrees only shrink when edges are removed.

§11.3's algorithm deletes edges from its working hypergraph, so the codegree hypotheses of
Theorem 11.3.1 — stated for `H` — have to be transported to every intermediate hypergraph the run
reaches.  That is what this is for. -/
theorem maxCodegree_mono {α : Type*} [Fintype α] [DecidableEq α] (k : ℕ)
    {A B : Finset (Finset α)} (h : A ⊆ B) : maxCodegree k A ≤ maxCodegree k B := by
  unfold maxCodegree
  refine Finset.sup_mono_fun ?_
  intro s _
  exact Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- A non-diagonal `Sym2` element has exactly two vertices. -/
theorem card_filter_mem_eq_two {n : ℕ} (e : Sym2 (Fin n)) (he : ¬ e.IsDiag) :
    (univ.filter fun v : Fin n => v ∈ e).card = 2 := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [Sym2.mk_isDiag_iff] at he
    have hset : (univ.filter fun v : Fin n => v ∈ s(a, b)) = {a, b} := by
      ext v
      simp [Sym2.mem_iff]
    rw [hset, Finset.card_insert_of_notMem (by simpa using he), Finset.card_singleton]

/-- **The handshake identity** for a diagonal-free edge set: summing each vertex's incident-edge
count over all vertices counts every edge twice. -/
theorem sum_card_incident {n : ℕ} (F : Finset (Sym2 (Fin n)))
    (hdiag : ∀ e ∈ F, ¬ e.IsDiag) :
    ∑ v : Fin n, (F.filter fun e => v ∈ e).card = 2 * F.card := by
  have hswap : ∑ v : Fin n, (F.filter fun e => v ∈ e).card
      = ∑ e ∈ F, (univ.filter fun v : Fin n => v ∈ e).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap, Finset.sum_congr rfl fun e he => card_filter_mem_eq_two e (hdiag e he),
    Finset.sum_const, smul_eq_mul, mul_comm]

/-- A vertex's degree in the graph a diagonal-free edge set spans, counted in the edge set.

§11.3's algorithm accumulates forbidden pairs as a `Finset (Sym2 (Fin n))`, because a
`DecidableRel` instance cannot be produced from under an existential, while §11.2's theorems take
a `SimpleGraph`.  This is the bridge between the two: it lets a degree bound proved about the
accumulated edge set be handed to those theorems as a hypothesis about `G.degree`. -/
theorem degree_fromEdgeSet {n : ℕ} (F : Finset (Sym2 (Fin n)))
    (hdiag : ∀ e ∈ F, ¬ e.IsDiag) (v : Fin n)
    [DecidableRel (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))).Adj] :
    (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))).degree v
      = (univ.filter fun u => s(v, u) ∈ F).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext u
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    SimpleGraph.fromEdgeSet_adj, Finset.mem_coe]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  intro huv
  exact hdiag _ h (by simp [huv])

/-- The same degree, counted as incident edges of `F`.

This is the form the chapter's statements use, so it is the one to reach for: a hypothesis stated
over `F.filter (v ∈ ·)` rewrites through this in one step, where `degree_fromEdgeSet` alone would
leave a `card_bij` to do. -/
theorem degree_fromEdgeSet_eq_card_incident {n : ℕ} (F : Finset (Sym2 (Fin n)))
    (hdiag : ∀ e ∈ F, ¬ e.IsDiag) (v : Fin n)
    [DecidableRel (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))).Adj] :
    (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))).degree v
      = (F.filter fun e => v ∈ e).card := by
  rw [degree_fromEdgeSet F hdiag v]
  refine Finset.card_bij (fun u _ => s(v, u)) ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact ⟨hu, Sym2.mem_mk_left v u⟩
  · intro u _ u' _ he
    exact Sym2.congr_right.mp he
  · intro e he
    simp only [Finset.mem_filter] at he
    obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp he.2
    exact ⟨u, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact he.1, rfl⟩

/-- The `n`-vertex triangle-free graphs, as a finset of edge sets. -/
noncomputable def triangleFreeGraphs (n : ℕ) : Finset (Finset (Sym2 (Fin n))) :=
  univ.filter IsTriangleFreeEdgeSet

/-! ### 11.2 Graph containers -/

/-- The interface the greedy step of the container algorithm is asked to satisfy on a graph `G`
of average degree `d`, with shrinking parameter `δ`.

`pick A T` is the vertex selected out of a candidate set `T` while `A` is the set of still-alive
vertices, and `kill A v` is the set of vertices retired from `A` when `v` is selected.

* `pick A T ∈ T` for nonempty `T`, and `pick A` is **stable**: shrinking `T` to a subset that still
  contains the selected vertex does not change the selection.  This is what lets the run be
  replayed from the fingerprint alone, because the fingerprint records exactly the vertices that
  are still to be selected.
* `kill A v ⊆ A` and `v ∉ kill A v`, so the selected vertex is retired separately from the
  vertices its selection retires.
* As long as fewer than `2 * δ * n` vertices have been retired, selecting from an independent set
  `I` retires at least `3 * d / 4` vertices, none of them in `I`.

**This is public, and must stay public, even though only this file uses it.**  It appears in the
*statements* of `exists_greedy_rule` and `exists_fingerprint_of_greedy_rule`, and `comparator`
cannot verify a target whose statement reaches a `private` declaration: Lean mangles private names
with the module path (`_private.<Module>.0.<name>`), while comparator builds the base tree under a
`ChoirBase.` module prefix, so the two sides cannot hold such a declaration under one name.  Making
it private costs both targets their kernel-level statement check. -/
def IsGreedyRule {n : ℕ} (G : SimpleGraph (Fin n)) (d δ : ℝ)
    (pick : Finset (Fin n) → Finset (Fin n) → Fin n)
    (kill : Finset (Fin n) → Fin n → Finset (Fin n)) : Prop :=
  (∀ A T : Finset (Fin n), T.Nonempty → pick A T ∈ T) ∧
  (∀ A T T' : Finset (Fin n), T' ⊆ T → pick A T ∈ T' → pick A T' = pick A T) ∧
  (∀ (A : Finset (Fin n)) (v : Fin n), kill A v ⊆ A ∧ v ∉ kill A v) ∧
  (∀ A : Finset (Fin n), ((Aᶜ).card : ℝ) ≤ 2 * δ * n →
    ∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) → (I ∩ A).Nonempty →
      Disjoint (kill A (pick A (I ∩ A))) I ∧
      3 * d / 4 ≤ ((kill A (pick A (I ∩ A))).card : ℝ))

/-- **The greedy step of the container algorithm** (Zhao, the algorithm on printed p. 206).  On a
graph whose average degree `d` is small compared with `δ * n`, selecting from the alive set `A`
the vertex of `I ∩ A` that comes first in the order of decreasing degree in `G[A]` retires at
least `3 * d / 4` vertices of `A` outside `I`: its predecessors in that order, which cannot lie
in `I`, together with its neighbours, which cannot lie in `I` either.

The count is the degree count of the proof idea.  Writing `v` for the selected vertex, `P` for
its predecessors and `t` for the number of vertices retired, every vertex of `A` outside
`P ∪ {v}` has degree in `G[A]` at most that of `v`, so

    d * n - 4 * c * d * (δ * n) ≤ ∑ u ∈ A, degree_{G[A]} u ≤ t * (c * d) + n * t,

and `d ≤ δ * n` with `δ ≤ 1 / (100 * c)` turns this into `t ≥ (1 - 4 * c * δ) / (1 + c * δ) * d`,
comfortably above `3 * d / 4`.  It is the hypothesis `d ≤ δ * n` that makes `c * d` negligible
against `n`; Zhao's `d / 2` is what the same count gives without it. -/
theorem exists_greedy_rule (c d δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) (hδc : δ ≤ 1 / (100 * c))
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hd : 0 < d) (hdn : d ≤ δ * n)
    (hsum : (∑ v, (G.degree v : ℝ)) = d * n) (hdeg : ∀ v, (G.degree v : ℝ) ≤ c * d) :
    ∃ (pick : Finset (Fin n) → Finset (Fin n) → Fin n)
      (kill : Finset (Fin n) → Fin n → Finset (Fin n)), IsGreedyRule G d δ pick kill := by
  -- `n` is positive: otherwise `0 < d ≤ δ * 0 = 0`.
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnR : (0 : ℝ) < (n : ℝ) := by
    rcases eq_or_lt_of_le hn0 with h | h
    · rw [← h] at hdn; nlinarith
    · exact h
  have hn : 0 < n := by exact_mod_cast hnR
  -- `δ ≤ 1 / (100 * c)` says exactly that `c * δ ≤ 1 / 100`, and `d ≤ δ * n` then makes the
  -- maximum degree `c * d` negligible against `n`.
  have hcδ : c * δ ≤ 1 / 100 := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 100 * c)).mp hδc
    nlinarith
  have hcd : c * d ≤ (n : ℝ) / 100 := by
    nlinarith [mul_le_mul_of_nonneg_left hdn hc.le, mul_le_mul_of_nonneg_right hcδ hn0]
  -- The order in which the vertices of `A` are selected: decreasing degree in `G[A]`, ties
  -- broken by index.  It is encoded as an injective weight `ord A : Fin n → ℕ`, with `decode`
  -- recovering the vertex from its weight; only these two properties and the monotonicity in
  -- the degree are used below.
  obtain ⟨ord, decode, hdecode, hord_mono⟩ :
      ∃ (ord : Finset (Fin n) → Fin n → ℕ) (decode : ℕ → Fin n),
        (∀ (A : Finset (Fin n)) (u : Fin n), decode (ord A u) = u) ∧
        ∀ (A : Finset (Fin n)) (u w : Fin n), ord A u ≤ ord A w →
          #{x ∈ A | G.Adj w x} ≤ #{x ∈ A | G.Adj u x} := by
    refine ⟨fun A u => n * (n - #{x ∈ A | G.Adj u x}) + (u : ℕ),
      fun m => ⟨m % n, Nat.mod_lt _ hn⟩, ?_, ?_⟩
    · intro A u
      refine Fin.ext ?_
      show (n * (n - #{x ∈ A | G.Adj u x}) + (u : ℕ)) % n = (u : ℕ)
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt u.isLt]
    · intro A u w huw
      have huw' : n * (n - #{x ∈ A | G.Adj u x}) + (u : ℕ)
          ≤ n * (n - #{x ∈ A | G.Adj w x}) + (w : ℕ) := huw
      by_contra hcon
      rw [not_le] at hcon
      have hwn : #{x ∈ A | G.Adj w x} ≤ n :=
        le_trans (Finset.card_filter_le _ _) (by simpa using Finset.card_le_univ A)
      have hstep : n - #{x ∈ A | G.Adj w x} + 1 ≤ n - #{x ∈ A | G.Adj u x} := by omega
      have hmul : n * (n - #{x ∈ A | G.Adj w x}) + n ≤ n * (n - #{x ∈ A | G.Adj u x}) := by
        calc n * (n - #{x ∈ A | G.Adj w x}) + n = n * (n - #{x ∈ A | G.Adj w x} + 1) := by ring
          _ ≤ n * (n - #{x ∈ A | G.Adj u x}) := Nat.mul_le_mul le_rfl hstep
      have hwlt : (w : ℕ) < n := w.isLt
      omega
  have hord_inj : ∀ (A : Finset (Fin n)) (u w : Fin n), ord A u = ord A w → u = w := by
    intro A u w h
    rw [← hdecode A u, ← hdecode A w, h]
  -- `pick A T` is the vertex of `T` of least weight, hence of largest degree in `G[A]`.
  obtain ⟨pick, hpick_mem, hpick_min⟩ :
      ∃ pick : Finset (Fin n) → Finset (Fin n) → Fin n,
        (∀ A T : Finset (Fin n), T.Nonempty → pick A T ∈ T) ∧
        ∀ (A T : Finset (Fin n)) (u : Fin n), u ∈ T → ord A (pick A T) ≤ ord A u := by
    refine ⟨fun A T => decode (sInf {m | ∃ u ∈ T, ord A u = m}), ?_, ?_⟩
    · intro A T hT
      obtain ⟨u, hu, hum⟩ := Nat.sInf_mem (s := {m | ∃ u ∈ T, ord A u = m})
        (by obtain ⟨u, hu⟩ := hT; exact ⟨ord A u, u, hu, rfl⟩)
      show decode (sInf {m | ∃ u ∈ T, ord A u = m}) ∈ T
      rw [← hum, hdecode]
      exact hu
    · intro A T u hu
      obtain ⟨w, hw, hwm⟩ := Nat.sInf_mem (s := {m | ∃ u ∈ T, ord A u = m}) ⟨ord A u, u, hu, rfl⟩
      show ord A (decode (sInf {m | ∃ u ∈ T, ord A u = m})) ≤ ord A u
      rw [← hwm, hdecode, hwm]
      exact Nat.sInf_le ⟨u, hu, rfl⟩
  -- Being the vertex of least weight determines `pick A T`.
  have hpick_eq : ∀ (A T : Finset (Fin n)) (v : Fin n), v ∈ T →
      (∀ u ∈ T, ord A v ≤ ord A u) → pick A T = v := fun A T v hv hmin =>
    hord_inj A _ _ (le_antisymm (hpick_min A T v hv) (hmin _ (hpick_mem A T ⟨v, hv⟩)))
  -- `kill A v` retires the predecessors of `v` in `A` together with its neighbours in `A`.
  obtain ⟨kill, hkill⟩ :
      ∃ kill : Finset (Fin n) → Fin n → Finset (Fin n),
        ∀ (A : Finset (Fin n)) (v : Fin n),
          kill A v = {x ∈ A | ord A x < ord A v ∨ G.Adj v x} :=
    ⟨fun A v => {x ∈ A | ord A x < ord A v ∨ G.Adj v x}, fun _ _ => rfl⟩
  -- The degree of a vertex inside `G[A]` never exceeds its degree in `G`.
  have hdA_deg : ∀ (A : Finset (Fin n)) (u : Fin n),
      (#{x ∈ A | G.Adj u x} : ℝ) ≤ (G.degree u : ℝ) := by
    intro A u
    refine Nat.cast_le.2 ?_
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    refine Finset.card_le_card fun w hw => ?_
    exact (SimpleGraph.mem_neighborFinset _ _ _).2 (Finset.mem_filter.1 hw).2
  have hdA_le : ∀ (A : Finset (Fin n)) (u : Fin n), (#{x ∈ A | G.Adj u x} : ℝ) ≤ c * d :=
    fun A u => le_trans (hdA_deg A u) (hdeg u)
  -- Double counting the edges meeting `A`: summing the number of neighbours inside `A` over
  -- all vertices gives the sum over `A` of the degrees in `G`.
  have hswap : ∀ A : Finset (Fin n),
      ∑ u : Fin n, (#{x ∈ A | G.Adj u x} : ℝ) = ∑ w ∈ A, (G.degree w : ℝ) := by
    intro A
    have hfil : ∀ x : Fin n, ({u | G.Adj u x} : Finset (Fin n)) = G.neighborFinset x := by
      intro x
      ext u
      simp [SimpleGraph.adj_comm]
    simp only [Finset.natCast_card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.natCast_card_filter, hfil w, SimpleGraph.card_neighborFinset_eq_degree]
  refine ⟨pick, kill, hpick_mem, ?_, ?_, ?_⟩
  · intro A T T' hsub hmem
    exact hpick_eq A T' (pick A T) hmem fun u hu => hpick_min A T u (hsub hu)
  · intro A v
    refine ⟨by rw [hkill]; exact Finset.filter_subset _ _, ?_⟩
    rw [hkill, Finset.mem_filter]
    simp
  · intro A hA I hI hIA
    set v := pick A (I ∩ A) with hvdef
    have hvIA : v ∈ I ∩ A := hpick_mem A (I ∩ A) hIA
    have hvI : v ∈ I := (Finset.mem_inter.1 hvIA).1
    have hvmin : ∀ u ∈ I ∩ A, ord A v ≤ ord A u := fun u hu => hpick_min A (I ∩ A) u hu
    have hsubA : kill A v ⊆ A := by rw [hkill]; exact Finset.filter_subset _ _
    refine ⟨?_, ?_⟩
    · -- The retired vertices avoid `I`: a predecessor of `v` lying in `I ∩ A` would contradict
      -- the minimality of `v`, and a neighbour of `v` cannot lie in the independent set `I`.
      rw [Finset.disjoint_left]
      intro u hu huI
      rw [hkill, Finset.mem_filter] at hu
      rcases hu.2 with hlt | hadj
      · exact absurd (hvmin u (Finset.mem_inter.2 ⟨huI, hu.1⟩)) (not_le.2 hlt)
      · exact hI (Finset.mem_coe.2 hvI) (Finset.mem_coe.2 huI) hadj.ne hadj
    · -- The retirement count, from the two-sided estimate of `∑ u ∈ A, deg_{G[A]} u`.
      have hnbr : {x ∈ A | G.Adj v x} ⊆ kill A v := by
        intro u hu
        rw [hkill, Finset.mem_filter]
        exact ⟨(Finset.mem_filter.1 hu).1, Or.inr (Finset.mem_filter.1 hu).2⟩
      have hdegv : (#{x ∈ A | G.Adj v x} : ℝ) ≤ (#(kill A v) : ℝ) :=
        Nat.cast_le.2 (Finset.card_le_card hnbr)
      have hsurv : ∀ u ∈ A \ kill A v,
          (#{x ∈ A | G.Adj u x} : ℝ) ≤ (#{x ∈ A | G.Adj v x} : ℝ) := by
        intro u hu
        rw [Finset.mem_sdiff] at hu
        have hnot : ¬(ord A u < ord A v ∨ G.Adj v u) := fun h =>
          hu.2 (by rw [hkill, Finset.mem_filter]; exact ⟨hu.1, h⟩)
        exact Nat.cast_le.2 (hord_mono A v u (not_lt.1 (not_or.1 hnot).1))
      -- Every vertex of `A` either is retired, and then has degree at most `c * d`, or survives,
      -- and then has degree at most that of `v`, which is at most the number retired.
      have hupper : ∑ u ∈ A, (#{x ∈ A | G.Adj u x} : ℝ)
          ≤ (#(kill A v) : ℝ) * (c * d) + (n : ℝ) * (#(kill A v) : ℝ) := by
        have hsplit : ∑ u ∈ A \ kill A v, (#{x ∈ A | G.Adj u x} : ℝ)
            + ∑ u ∈ kill A v, (#{x ∈ A | G.Adj u x} : ℝ)
            = ∑ u ∈ A, (#{x ∈ A | G.Adj u x} : ℝ) := Finset.sum_sdiff hsubA
        have h1 : ∑ u ∈ kill A v, (#{x ∈ A | G.Adj u x} : ℝ) ≤ (#(kill A v) : ℝ) * (c * d) := by
          calc ∑ u ∈ kill A v, (#{x ∈ A | G.Adj u x} : ℝ)
              ≤ ∑ _u ∈ kill A v, c * d := Finset.sum_le_sum fun u _ => hdA_le A u
            _ = (#(kill A v) : ℝ) * (c * d) := by rw [Finset.sum_const, nsmul_eq_mul]
        have h2 : ∑ u ∈ A \ kill A v, (#{x ∈ A | G.Adj u x} : ℝ)
            ≤ (n : ℝ) * (#(kill A v) : ℝ) := by
          have hcard : (#(A \ kill A v) : ℝ) ≤ (n : ℝ) := by
            have h := Finset.card_le_univ (A \ kill A v)
            simp only [Fintype.card_fin] at h
            exact Nat.cast_le.2 h
          calc ∑ u ∈ A \ kill A v, (#{x ∈ A | G.Adj u x} : ℝ)
              ≤ ∑ _u ∈ A \ kill A v, (#(kill A v) : ℝ) :=
                Finset.sum_le_sum fun u hu => le_trans (hsurv u hu) hdegv
            _ = (#(A \ kill A v) : ℝ) * (#(kill A v) : ℝ) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (n : ℝ) * (#(kill A v) : ℝ) := mul_le_mul_of_nonneg_right hcard (by positivity)
        linarith
      -- At most `2 * δ * n` vertices are missing from `A`, so at most `2 * δ * n * (c * d)`
      -- of the degree sum is lost, twice over.
      have hlower : d * n - 4 * c * d * δ * n ≤ ∑ u ∈ A, (#{x ∈ A | G.Adj u x} : ℝ) := by
        have hcompl : ∑ w ∈ Aᶜ, (G.degree w : ℝ) ≤ 2 * δ * n * (c * d) := by
          calc ∑ w ∈ Aᶜ, (G.degree w : ℝ) ≤ ∑ _w ∈ Aᶜ, c * d :=
                Finset.sum_le_sum fun w _ => hdeg w
            _ = (#(Aᶜ) : ℝ) * (c * d) := by rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ 2 * δ * n * (c * d) := mul_le_mul_of_nonneg_right hA (by positivity)
        have hall : ∑ w ∈ A, (G.degree w : ℝ) + ∑ w ∈ Aᶜ, (G.degree w : ℝ)
            = ∑ w, (G.degree w : ℝ) := Finset.sum_add_sum_compl A _
        have hsplit2 : ∑ u ∈ A, (#{x ∈ A | G.Adj u x} : ℝ)
            + ∑ u ∈ Aᶜ, (#{x ∈ A | G.Adj u x} : ℝ)
            = ∑ u : Fin n, (#{x ∈ A | G.Adj u x} : ℝ) := Finset.sum_add_sum_compl A _
        have hout : ∑ u ∈ Aᶜ, (#{x ∈ A | G.Adj u x} : ℝ) ≤ ∑ w ∈ Aᶜ, (G.degree w : ℝ) :=
          Finset.sum_le_sum fun u _ => hdA_deg A u
        have hsw := hswap A
        linarith
      -- `(3 * d / 4) * (c * d + n) ≤ d * n - 4 * c * d * δ * n ≤ #(kill A v) * (c * d + n)`.
      have hpos : (0 : ℝ) < c * d + n := by positivity
      refine le_of_mul_le_mul_right ?_ hpos
      nlinarith [mul_le_mul_of_nonneg_left hcd hd.le,
        mul_le_mul_of_nonneg_left hcδ (mul_nonneg hd.le hn0)]

/-- One run of the greedy container algorithm on the target set `T`.  The state is the pair
`(X, P)` of retired and selected vertices, the alive set being `(X ∪ P)ᶜ`; a step selects `pick`
of the alive part of `T`, adds it to `P` and its `kill` set to `X`.  The run halts once `b`
vertices are retired or nothing of `T` is alive, and `fuel` bounds the number of steps. -/
private def greedyRun {n : ℕ} (pick : Finset (Fin n) → Finset (Fin n) → Fin n)
    (kill : Finset (Fin n) → Fin n → Finset (Fin n)) (b : ℕ) (T : Finset (Fin n)) :
    ℕ → Finset (Fin n) → Finset (Fin n) → Finset (Fin n) × Finset (Fin n)
  | 0, X, P => (X, P)
  | fuel + 1, X, P =>
    if b ≤ X.card then (X, P)
    else if (T ∩ (X ∪ P)ᶜ).Nonempty then
      greedyRun pick kill b T fuel
        (X ∪ kill (X ∪ P)ᶜ (pick (X ∪ P)ᶜ (T ∩ (X ∪ P)ᶜ)))
        (insert (pick (X ∪ P)ᶜ (T ∩ (X ∪ P)ᶜ)) P)
    else (X, P)

/-- Both components of the state of `greedyRun` only ever grow. -/
private theorem greedyRun_grows {n : ℕ} (pick : Finset (Fin n) → Finset (Fin n) → Fin n)
    (kill : Finset (Fin n) → Fin n → Finset (Fin n)) (b : ℕ) (T : Finset (Fin n)) (fuel : ℕ) :
    ∀ X P : Finset (Fin n), X ⊆ (greedyRun pick kill b T fuel X P).1 ∧
      P ⊆ (greedyRun pick kill b T fuel X P).2 := by
  induction fuel with
  | zero => exact fun X P => ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  | succ fuel ih =>
    intro X P
    rw [greedyRun]
    split_ifs with h1 h2
    · exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
    · exact ⟨Finset.subset_union_left.trans (ih _ _).1,
        (Finset.subset_insert _ _).trans (ih _ _).2⟩
    · exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩

/-- **The run is replayed by the set of vertices it selects.**  Shrinking the target to any `J`
that still contains every selected vertex leaves the run unchanged: stability of `pick` forces
the same selection at every step, and the two runs halt together. -/
private theorem greedyRun_replay {n : ℕ} (pick : Finset (Fin n) → Finset (Fin n) → Fin n)
    (kill : Finset (Fin n) → Fin n → Finset (Fin n))
    (hpick : ∀ A T : Finset (Fin n), T.Nonempty → pick A T ∈ T)
    (hstab : ∀ A T T' : Finset (Fin n), T' ⊆ T → pick A T ∈ T' → pick A T' = pick A T)
    (b fuel : ℕ) :
    ∀ T J X P : Finset (Fin n), (greedyRun pick kill b T fuel X P).2 ⊆ J → J ⊆ T →
      greedyRun pick kill b J fuel X P = greedyRun pick kill b T fuel X P := by
  induction fuel with
  | zero => exact fun T J X P _ _ => rfl
  | succ fuel ih =>
    intro T J X P hSJ hJT
    have hstep : ∀ T' : Finset (Fin n),
        greedyRun pick kill b T' (fuel + 1) X P =
          if b ≤ X.card then (X, P)
          else if (T' ∩ (X ∪ P)ᶜ).Nonempty then
            greedyRun pick kill b T' fuel
              (X ∪ kill (X ∪ P)ᶜ (pick (X ∪ P)ᶜ (T' ∩ (X ∪ P)ᶜ)))
              (insert (pick (X ∪ P)ᶜ (T' ∩ (X ∪ P)ᶜ)) P)
          else (X, P) := fun T' => by rw [greedyRun]
    rw [hstep T] at hSJ
    rw [hstep J, hstep T]
    by_cases h1 : b ≤ X.card
    · simp only [if_pos h1]
    simp only [if_neg h1] at hSJ ⊢
    by_cases h2 : (T ∩ (X ∪ P)ᶜ).Nonempty
    · simp only [if_pos h2] at hSJ ⊢
      have hvT : pick (X ∪ P)ᶜ (T ∩ (X ∪ P)ᶜ) ∈ T ∩ (X ∪ P)ᶜ := hpick _ _ h2
      have hvJ : pick (X ∪ P)ᶜ (T ∩ (X ∪ P)ᶜ) ∈ J :=
        hSJ ((greedyRun_grows pick kill b T fuel _ _).2 (Finset.mem_insert_self _ _))
      have hvJA : pick (X ∪ P)ᶜ (T ∩ (X ∪ P)ᶜ) ∈ J ∩ (X ∪ P)ᶜ :=
        Finset.mem_inter.mpr ⟨hvJ, (Finset.mem_inter.mp hvT).2⟩
      have h2J : (J ∩ (X ∪ P)ᶜ).Nonempty := ⟨_, hvJA⟩
      rw [if_pos h2J, hstab (X ∪ P)ᶜ (T ∩ (X ∪ P)ᶜ) (J ∩ (X ∪ P)ᶜ)
        (Finset.inter_subset_inter_right hJT) hvJA]
      exact ih T J _ _ hSJ hJT
    · have h2J : ¬ (J ∩ (X ∪ P)ᶜ).Nonempty := by
        rintro ⟨x, hx⟩
        rw [Finset.mem_inter] at hx
        exact h2 ⟨x, Finset.mem_inter.mpr ⟨hJT hx.1, hx.2⟩⟩
      simp only [if_neg h2, if_neg h2J]

/-- **The invariants carried by one run of the greedy algorithm on an independent set `I`.**
Along the run the retired set `X` misses `I` (so the selected vertices are all that `I` can
have inside `X ∪ P`), the fingerprint `P` stays inside `I` and disjoint from `X`, at least one
and indeed at least `3 * d / 4` vertices are retired per selection, and the selections made
before the last cost at most the budget `b - 1`.  The run halts either with the budget spent or
with nothing of `I` left alive, never for want of fuel, because `b ≤ fuel + X.card` is an
invariant too. -/
private theorem greedyRun_invariants {n : ℕ} {G : SimpleGraph (Fin n)} {d δ : ℝ}
    {pick : Finset (Fin n) → Finset (Fin n) → Fin n}
    {kill : Finset (Fin n) → Fin n → Finset (Fin n)}
    (hrule : IsGreedyRule G d δ pick kill) (hd : 0 < d) {b : ℕ}
    (hb : (b : ℝ) - 1 < δ * n) {I : Finset (Fin n)}
    (hI : G.IsIndepSet (I : Set (Fin n))) (fuel : ℕ) :
    ∀ X P Y Q : Finset (Fin n), greedyRun pick kill b I fuel X P = (Y, Q) →
      Disjoint X I → P ⊆ I → Disjoint X P → P.card ≤ X.card →
      3 * d / 4 * (P.card : ℝ) ≤ X.card →
      (P.card = 0 ∨ 3 * d / 4 * ((P.card : ℝ) - 1) ≤ (b : ℝ) - 1) →
      b ≤ fuel + X.card →
      Disjoint Y I ∧ P ⊆ Q ∧ Q ⊆ I ∧ Disjoint Y Q ∧ Q.card ≤ Y.card ∧
        3 * d / 4 * (Q.card : ℝ) ≤ Y.card ∧
        (Q.card = 0 ∨ 3 * d / 4 * ((Q.card : ℝ) - 1) ≤ (b : ℝ) - 1) ∧
        (b ≤ Y.card ∨ I ⊆ Y ∪ Q) := by
  obtain ⟨hmem, -, hkill, hstep⟩ := hrule
  induction fuel with
  | zero =>
    intro X P Y Q hrun hXI hPI hXP hle hinv hbud hfuel
    rw [greedyRun, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨hXI, Finset.Subset.refl _, hPI, hXP, hle, hinv, hbud, Or.inl (by omega)⟩
  | succ fuel ih =>
    intro X P Y Q hrun hXI hPI hXP hle hinv hbud hfuel
    rw [greedyRun] at hrun
    by_cases h1 : b ≤ X.card
    · rw [if_pos h1, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact ⟨hXI, Finset.Subset.refl _, hPI, hXP, hle, hinv, hbud, Or.inl h1⟩
    rw [if_neg h1] at hrun
    by_cases h2 : (I ∩ (X ∪ P)ᶜ).Nonempty
    · rw [if_pos h2] at hrun
      set A : Finset (Fin n) := (X ∪ P)ᶜ with hA
      set v : Fin n := pick A (I ∩ A) with hv
      have hvIA : v ∈ I ∩ A := hmem _ _ h2
      have hvI : v ∈ I := (Finset.mem_inter.mp hvIA).1
      have hvXP : v ∉ X ∪ P := Finset.mem_compl.mp (hA ▸ (Finset.mem_inter.mp hvIA).2)
      have hvX : v ∉ X := fun h => hvXP (Finset.mem_union_left _ h)
      have hvP : v ∉ P := fun h => hvXP (Finset.mem_union_right _ h)
      have hkXP : Disjoint (kill A v) (X ∪ P) :=
        Finset.disjoint_left.mpr fun a ha hb' => Finset.mem_compl.mp (hA ▸ (hkill A v).1 ha) hb'
      obtain ⟨hkX, hkP⟩ := Finset.disjoint_union_right.mp hkXP
      -- the entry condition turns the budget test into the hypothesis `IsGreedyRule` wants
      have hXb : (X.card : ℝ) ≤ (b : ℝ) - 1 := by
        have h : (X.card : ℝ) + 1 ≤ (b : ℝ) := by
          have : X.card + 1 ≤ b := by omega
          exact_mod_cast this
        linarith
      have hAc : ((Aᶜ).card : ℝ) ≤ 2 * δ * n := by
        rw [hA, compl_compl]
        have h : (X ∪ P).card ≤ X.card + P.card := Finset.card_union_le _ _
        have h' : ((X ∪ P).card : ℝ) ≤ (X.card : ℝ) + (P.card : ℝ) := by exact_mod_cast h
        have h'' : ((P.card : ℝ)) ≤ (X.card : ℝ) := by exact_mod_cast hle
        linarith
      obtain ⟨hdisj, hcard34⟩ := hstep A hAc I hI h2
      have hkpos : 1 ≤ (kill A v).card := by
        rcases Nat.eq_zero_or_pos (kill A v).card with h | h
        · rw [h] at hcard34; norm_num at hcard34; linarith
        · exact h
      have hcX : (X ∪ kill A v).card = X.card + (kill A v).card :=
        Finset.card_union_of_disjoint (Finset.disjoint_left.mpr
          fun a ha hb' => Finset.disjoint_left.mp hkX hb' ha)
      have hcP : (insert v P).card = P.card + 1 := Finset.card_insert_of_notMem hvP
      have hk34 : 3 * d / 4 ≤ ((kill A v).card : ℝ) := hcard34
      obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ :=
        ih (X ∪ kill A v) (insert v P) Y Q hrun
          (Finset.disjoint_union_left.mpr ⟨hXI, hdisj⟩)
          (Finset.insert_subset hvI hPI)
          (Finset.disjoint_union_left.mpr
            ⟨Finset.disjoint_insert_right.mpr ⟨hvX, hXP⟩,
             Finset.disjoint_insert_right.mpr ⟨(hkill A v).2, hkP⟩⟩)
          (by rw [hcX, hcP]; omega)
          (by
            rw [hcX, hcP]
            push_cast
            linarith)
          (Or.inr (by
            rw [hcP]
            push_cast
            linarith))
          (by rw [hcX]; omega)
      exact ⟨g1, (Finset.subset_insert _ _).trans g2, g3, g4, g5, g6, g7, g8⟩
    · rw [if_neg h2, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      refine ⟨hXI, Finset.Subset.refl _, hPI, hXP, hle, hinv, hbud, Or.inr fun x hx => ?_⟩
      by_contra hxc
      exact h2 ⟨x, Finset.mem_inter.mpr ⟨hx, Finset.mem_compl.mpr hxc⟩⟩

/-- **The container algorithm assembled from its greedy step.**  Running a greedy rule from the
alive set `Finset.univ` and the empty fingerprint produces the fingerprint function `S` and the
container function `A` of Theorem 11.2.3 in the regime `d ≤ δ * n`.

The run selects vertices `v₁, …, v_m` out of `I`, retiring `kill` sets into a set `X` of retired
vertices, and stops when either `δ * n` vertices have been retired or nothing of `I` is left
alive.  Three facts make it work.

* `X` never meets `I`, so `I ⊆ S ∪ A` with `S = {v₁, …, v_m}` the vertices selected and `A` the
  alive set at the halt: the selected vertex is first in `I ∩ A`, so its predecessors miss `I`,
  and its neighbours miss `I` by independence.
* **`A` is recovered from `S` alone.**  Replaying the run with `I` replaced by the *set* `S`
  selects the same vertices, because at step `k` the fingerprint restricted to the alive set is
  `{v_{k+1}, …, v_m} ⊆ I ∩ A_k` and still contains `v_{k+1}`, so stability of `pick` gives the
  same selection.  Halting for want of alive vertices is also visible from `S`, and there `I` is
  forced to equal `S`, which is what makes `A := ∅` consistent on that branch.
* The budget.  Each of the first `m - 1` steps retires at least `3 * d / 4` vertices while fewer
  than `δ * n` are retired, so `m - 1 < 4 * δ * n / (3 * d) = (2 / 3) * (2 * δ * n / d)`, and
  `d ≤ δ * n` makes `2 * δ * n / d ≥ 2`, which is exactly enough for the integer `m` to satisfy
  `m ≤ 2 * δ * n / d`.  On the branch that halts for want of alive vertices the container is `S`
  itself, and `∑ v, degree v = d * n` with `degree ≤ c * d` bounds every independent set by
  `(1 - 1 / (2 * c)) * n ≤ (1 - δ) * n`.

**The last conjunct, `S J = S I` for `S I ⊆ J ⊆ I`, is the stability property, and it is stated
here deliberately rather than left to be rediscovered.**  PR #143 established while reducing
Theorem 11.3.1 that a two-phase fingerprint needs it for *both* phases, so that the composite
`F = S I ∪ S' (S I) I` satisfies `S F = S I`; the source states the corresponding bullet for one
phase only, and it **cannot be recovered from the conclusion of 11.2.3**, whose `S` is an
arbitrary function.  It is free inside any honest proof of this obligation, by the same replay the
second bullet above describes: for `k < m` the pick `v_{k+1}` lies in `S I ⊆ J` and in `A_k`, so
`J ∩ A_k` is nonempty and stability of `pick` (`T' ⊆ T` with `pick A T ∈ T'`) forces the same
choice; and if `I ∩ A_m = ∅` then `J ∩ A_m = ∅` too, so the two runs halt together.  Do not prove
it separately at the end — it should fall out of the run's invariants. -/
theorem exists_fingerprint_of_greedy_rule (c d δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (hδc : δ ≤ 1 / (100 * c)) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hd : 0 < d) (hdn : d ≤ δ * n) (hsum : (∑ v, (G.degree v : ℝ)) = d * n)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ c * d)
    (pick : Finset (Fin n) → Finset (Fin n) → Fin n)
    (kill : Finset (Fin n) → Fin n → Finset (Fin n)) (hrule : IsGreedyRule G d δ pick kill) :
    ∃ S A : Finset (Fin n) → Finset (Fin n),
      ∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) →
        S I ⊆ I ∧ I ⊆ S I ∪ A (S I) ∧
        ((S I).card : ℝ) ≤ 2 * δ * n / d ∧
        ((S I ∪ A (S I)).card : ℝ) ≤ (1 - δ) * n ∧
        ∀ J : Finset (Fin n), S I ⊆ J → J ⊆ I → S J = S I := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hδn0 : (0 : ℝ) ≤ δ * n := by positivity
  -- the budget: a natural number squeezed against `δ * n` from both sides
  obtain ⟨b, hb, hbge⟩ : ∃ b : ℕ, (b : ℝ) - 1 < δ * n ∧ δ * (n : ℝ) ≤ (b : ℝ) :=
    ⟨⌈δ * (n : ℝ)⌉₊, by linarith [Nat.ceil_lt_add_one hδn0], Nat.le_ceil _⟩
  have hmem := hrule.1
  have hstab := hrule.2.1
  refine ⟨fun J => (greedyRun pick kill b J b ∅ ∅).2,
    fun J => if b ≤ (greedyRun pick kill b J b ∅ ∅).1.card then
      ((greedyRun pick kill b J b ∅ ∅).1 ∪ (greedyRun pick kill b J b ∅ ∅).2)ᶜ else ∅,
    fun I hI => ?_⟩
  obtain ⟨X, P, hXP⟩ : ∃ X P, greedyRun pick kill b I b ∅ ∅ = (X, P) := ⟨_, _, rfl⟩
  obtain ⟨hXI, -, hPI, hdXP, hle, hinv1, hinv2, hhalt⟩ :=
    greedyRun_invariants hrule hd hb hI b ∅ ∅ X P hXP (by simp) (by simp) (by simp)
      (by simp) (by simp) (Or.inl (by simp)) (by simp)
  -- replaying the run on the fingerprint reproduces it, which is both how `A` sees the
  -- container and how the stability conjunct is discharged
  have hRP : greedyRun pick kill b P b ∅ ∅ = (X, P) :=
    (greedyRun_replay pick kill hmem hstab b b I P ∅ ∅
      (by rw [hXP]) hPI).trans hXP
  have hlast : ∀ J : Finset (Fin n), P ⊆ J → J ⊆ I →
      (greedyRun pick kill b J b ∅ ∅).2 = P := fun J hPJ hJI => by
    rw [greedyRun_replay pick kill hmem hstab b b I J ∅ ∅
      (by rw [hXP]; exact hPJ) hJI, hXP]
  have hPX : (P.card : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast hle
  have hXn : X.card ≤ n := by simpa using Finset.card_le_univ X
  -- the budget arithmetic: `m - 1` selections cost `3 * d / 4` each out of `δ * n`
  have hcardS : (P.card : ℝ) ≤ 2 * δ * n / d := by
    rw [le_div_iff₀ hd]
    rcases hinv2 with h0 | h2
    · rw [h0]; push_cast; nlinarith
    · rcases le_or_gt (3 * d) (2 * (δ * n)) with h3 | h3
      · nlinarith
      · have hlt3 : (P.card : ℝ) < 3 := by nlinarith
        have hlt3' : (P.card : ℝ) ≤ 2 := by
          have h' : P.card < 3 := by exact_mod_cast hlt3
          have h'' : P.card ≤ 2 := by omega
          exact_mod_cast h''
        nlinarith
  simp only [hXP, hRP]
  by_cases hhX : b ≤ X.card
  · -- the budget was spent: the container is the complement of the retired set
    rw [if_pos hhX]
    have hcont : P ∪ (X ∪ P)ᶜ = Xᶜ := by
      ext x
      have hdx : x ∈ X → x ∉ P := fun h => Finset.disjoint_left.mp hdXP h
      simp only [Finset.mem_union, Finset.mem_compl]
      tauto
    have hccard : ((Xᶜ).card : ℝ) = (n : ℝ) - X.card := by
      have h : (Xᶜ).card = n - X.card := by rw [Finset.card_compl]; simp
      rw [h, Nat.cast_sub hXn]
    have hδX : δ * (n : ℝ) ≤ (X.card : ℝ) := hbge.trans (by exact_mod_cast hhX)
    refine ⟨hPI, ?_, hcardS, ?_, hlast⟩
    · rw [hcont]
      exact fun x hx => Finset.mem_compl.mpr fun hX => Finset.disjoint_left.mp hXI hX hx
    · rw [hcont, hccard]; linarith
  · -- the run ran out of alive vertices of `I`, so `I` is its own fingerprint
    rw [if_neg hhX]
    have hIP : I ⊆ P := by
      rcases hhalt with h | h
      · exact absurd h hhX
      · exact fun x hx => (Finset.mem_union.mp (h hx)).elim
          (fun h' => absurd hx (Finset.disjoint_left.mp hXI h')) id
    have hb1 : (1 : ℝ) ≤ (b : ℝ) := by
      have : 1 ≤ b := by omega
      exact_mod_cast this
    have hδnpos : (0 : ℝ) < δ * n := by linarith
    have hnne : (n : ℝ) ≠ 0 := fun h => by
      rw [h, mul_zero] at hδnpos; exact absurd hδnpos (lt_irrefl 0)
    have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_le_of_ne hn0 (Ne.symm hnne)
    -- the maximum degree bound forces `c ≥ 1`, hence `δ ≤ 1 / 100`
    have hc1 : (1 : ℝ) ≤ c := by
      have h1 : (∑ v : Fin n, (G.degree v : ℝ)) ≤ ∑ _v : Fin n, c * d :=
        Finset.sum_le_sum fun v _ => hdeg v
      rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
      nlinarith [mul_pos hnpos hd]
    have hδ100 : δ ≤ 1 / 100 := by
      have h : 1 / (100 * c) ≤ 1 / 100 := by
        refine one_div_le_one_div_of_le (by norm_num) ?_
        nlinarith
      linarith
    have hXb : (X.card : ℝ) ≤ (b : ℝ) - 1 := by
      have h : X.card + 1 ≤ b := by omega
      have h' : (X.card : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast h
      linarith
    refine ⟨hPI, by simpa using hIP, hcardS, ?_, hlast⟩
    rw [Finset.union_empty]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * δ) hnpos.le]

/-- **Containers from a single-vertex fingerprint, in the dense corner `δ * n < d`.**  When the
average degree exceeds `δ * n` the fingerprint budget `2 * δ * n / d` of Theorem 11.2.3 is below
`2`, so a fingerprint may hold at most one vertex, and the conclusion takes the form: a selection
`s I ∈ I` and a set `K v` depending only on the selected vertex, with `I ⊆ insert (s I) (K (s I))`
and that container missing at least `δ * n` vertices.

`d ≤ 2 * δ * n` is what keeps the budget at least `1`, so that a one-vertex fingerprint is
permitted at all.

**Route.**  Build the order greedily rather than by degree.  Write `Z v = N(v) ∪ {u | u ≺ v}`;
the statement is equivalent to producing an order in which every `v` has `|Z v| ≥ δ * n`, since
`K v := V \ insert v (Z v)` then gives `insert (s I) (K (s I)) = V \ Z (s I)` of card
`n - |Z (s I)|`, and taking `s I` to be the `≺`-least element of `I` makes `I ∩ Z (s I) = ∅`
(independence kills `N`, minimality kills the predecessors).

The one lemma needed is a **greedy extension step**: for every `j < δ * n` and every `P` with
`|P| = j` there is `v ∉ P` with `|N(v) \ P| ≥ δ * n - j`.  If not, then summing degrees and
bounding the `P`–`Pᶜ` edges from the `P` side twice,

    d * n < 2 * j * (c * d) + (n - j) * (δ * n - j),

which rearranges to `n * (d - δ * n) < j * (2 * c * d + j - n - δ * n)`.  The left side is
positive by `hlo`.  On the right, `c ≥ 1` (the average degree is `d` and the maximum is `≤ c * d`),
so `δ ≤ 1 / 100` and `c * d ≤ 2 * c * δ * n ≤ n / 50`; hence `2 * c * d + j - n - δ * n ≤ -0.95 * n`
and the right side is `≤ 0`.  Contradiction.  Applying the step for `j = 0, 1, …, ⌈δ * n⌉ - 1`
yields distinct `v₁ ≺ ⋯ ≺ v_m` with `|Z vᵢ| ≥ (i - 1) + (δ * n - (i - 1)) = δ * n`, and every
later vertex has `≥ ⌈δ * n⌉` predecessors.

**Why the order must be greedy rather than by degree.**  Selecting the largest-degree vertex
leaves a window of relative width `(c - 1) * δ` above `δ * n` uncovered: the sharpened count
`d * n ≤ t * (c * d + n - t)` is a bound on what the largest-degree vertex can guarantee, and in
that window a tiny high-degree set can leave the chosen vertex one short.  The window is a
property of that construction, not of this statement — nothing here forces the order to be by
degree, and the greedy order above is unconditional in these hypotheses, using no lower bound on
`d - δ * n` beyond positivity. -/
theorem exists_dense_fingerprint (c d δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) (hδc : δ ≤ 1 / (100 * c))
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hd : 0 < d) (hlo : δ * n < d)
    (hhi : d ≤ 2 * δ * n) (hsum : (∑ v, (G.degree v : ℝ)) = d * n)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ c * d) :
    ∃ (s : Finset (Fin n) → Fin n) (K : Fin n → Finset (Fin n)),
      ∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) → I.Nonempty →
        s I ∈ I ∧ I ⊆ insert (s I) (K (s I)) ∧
        ((insert (s I) (K (s I))).card : ℝ) ≤ (1 - δ) * n := by
  -- the vertex set is nonempty
  have hnR : (0 : ℝ) < n := by
    rcases (Nat.cast_nonneg n : (0 : ℝ) ≤ n).lt_or_eq with h | h
    · exact h
    · rw [← h] at hhi
      linarith
  have hn : 0 < n := by exact_mod_cast hnR
  -- `c ≥ 1`: the maximum degree is at least the average
  have hc1 : (1 : ℝ) ≤ c := by
    have h := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hdeg v)
    rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    nlinarith [mul_pos hd hnR]
  have hδc' : δ * (100 * c) ≤ 1 := by
    have h : δ * (100 * c) ≤ (1 / (100 * c)) * (100 * c) :=
      mul_le_mul_of_nonneg_right hδc (by positivity)
    rwa [one_div, inv_mul_cancel₀ (by positivity : (100 * c) ≠ 0)] at h
  have hcδ : c * δ ≤ 1 / 100 := by linarith
  have hδ100 : δ ≤ 1 / 100 := by nlinarith
  -- **the greedy extension step**
  have hstep : ∀ P : Finset (Fin n), ((P.card : ℝ) < δ * n) →
      ∃ v, v ∉ P ∧ δ * n - P.card ≤ ((G.neighborFinset v \ P).card : ℝ) := by
    intro P hP
    by_contra hcon0
    have hcon : ∀ v : Fin n, v ∉ P →
        ((G.neighborFinset v \ P).card : ℝ) < δ * n - P.card := by
      intro v hvP
      by_contra h
      exact hcon0 ⟨v, hvP, not_lt.mp h⟩
    have hjn : P.card ≤ n := by simpa [Finset.card_univ] using Finset.card_le_univ P
    have hQcard : (Finset.univ \ P).card = n - P.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ P), Finset.card_univ,
        Fintype.card_fin]
    -- count the edges between `P` and its complement from the `P` side
    have hcross : (∑ v ∈ Finset.univ \ P, (G.neighborFinset v ∩ P).card)
        ≤ ∑ u ∈ P, G.degree u := by
      have e1 : ∀ v : Fin n, (G.neighborFinset v ∩ P).card
          = ∑ u ∈ P, if G.Adj v u then 1 else 0 := by
        intro v
        rw [← Finset.card_filter]
        congr 1
        ext u
        simp [and_comm]
      calc (∑ v ∈ Finset.univ \ P, (G.neighborFinset v ∩ P).card)
          = ∑ v ∈ Finset.univ \ P, ∑ u ∈ P, if G.Adj v u then 1 else 0 :=
            Finset.sum_congr rfl fun v _ => e1 v
        _ = ∑ u ∈ P, ∑ v ∈ Finset.univ \ P, if G.Adj v u then 1 else 0 := Finset.sum_comm
        _ ≤ ∑ u ∈ P, G.degree u := by
            refine Finset.sum_le_sum fun u _ => ?_
            rw [← Finset.card_filter]
            refine Finset.card_le_card ?_
            intro v hv
            simp only [Finset.mem_filter] at hv
            exact (SimpleGraph.mem_neighborFinset _ _ _).mpr hv.2.symm
    have hmain : ∑ v, G.degree v
        ≤ (∑ v ∈ Finset.univ \ P, (G.neighborFinset v \ P).card)
          + 2 * ∑ u ∈ P, G.degree u := by
      have h1 : (∑ v ∈ Finset.univ \ P, G.degree v) + ∑ u ∈ P, G.degree u
          = ∑ v, G.degree v :=
        Finset.sum_sdiff (Finset.subset_univ P)
      have h2 : (∑ v ∈ Finset.univ \ P, G.degree v)
          = (∑ v ∈ Finset.univ \ P, (G.neighborFinset v \ P).card)
            + ∑ v ∈ Finset.univ \ P, (G.neighborFinset v ∩ P).card := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun v _ =>
          (Finset.card_sdiff_add_card_inter _ _).symm
      omega
    have hmainR : (d * n : ℝ)
        ≤ (∑ v ∈ Finset.univ \ P, ((G.neighborFinset v \ P).card : ℝ))
          + 2 * ∑ u ∈ P, (G.degree u : ℝ) := by
      rw [← hsum]
      have := (Nat.cast_le (α := ℝ)).mpr hmain
      push_cast at this
      exact this
    have hAsum : (∑ v ∈ Finset.univ \ P, ((G.neighborFinset v \ P).card : ℝ))
        ≤ ((n : ℝ) - P.card) * (δ * n - P.card) := by
      calc (∑ v ∈ Finset.univ \ P, ((G.neighborFinset v \ P).card : ℝ))
          ≤ ∑ _v ∈ Finset.univ \ P, (δ * n - (P.card : ℝ)) := by
            refine Finset.sum_le_sum fun v hv => le_of_lt (hcon v ?_)
            exact (Finset.mem_sdiff.mp hv).2
        _ = (((Finset.univ \ P).card : ℝ)) * (δ * n - P.card) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = ((n : ℝ) - P.card) * (δ * n - P.card) := by
            rw [hQcard, Nat.cast_sub hjn]
    have hBsum : (∑ u ∈ P, (G.degree u : ℝ)) ≤ (P.card : ℝ) * (c * d) := by
      calc (∑ u ∈ P, (G.degree u : ℝ)) ≤ ∑ _u ∈ P, c * d :=
            Finset.sum_le_sum fun u _ => hdeg u
        _ = (P.card : ℝ) * (c * d) := by rw [Finset.sum_const, nsmul_eq_mul]
    have h2cd : 2 * (c * d) ≤ 4 * (c * δ) * (n : ℝ) := by nlinarith
    have hδn : δ * n ≤ (1 / 100) * (n : ℝ) := by nlinarith
    have h4 : 4 * (c * δ) * (n : ℝ) ≤ 4 * (1 / 100) * (n : ℝ) := by nlinarith
    have hneg : 2 * (c * d) + (P.card : ℝ) - n - δ * n ≤ 0 := by nlinarith
    have hRHS : (P.card : ℝ) * (2 * (c * d) + (P.card : ℝ) - n - δ * n) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hneg
    nlinarith [hmainR, hAsum, hBsum, hRHS]
  -- iterate the greedy step: a sequence of distinct vertices, each with a large `Z`
  have hseq : ∀ k : ℕ, k ≤ ⌈δ * n⌉₊ → ∃ w : ℕ → Fin n,
      (∀ i < k, ∀ j < k, w i = w j → i = j) ∧
      (∀ i < k, δ * n
        ≤ ((G.neighborFinset (w i) ∪ (Finset.range i).image w).card : ℝ)) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨fun _ => ⟨0, hn⟩, by omega, by omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨w, hinj, hprop⟩ := ih (by omega)
      have hPcard : ((Finset.range k).image w).card = k := by
        rw [Finset.card_image_of_injOn, Finset.card_range]
        intro a ha b hb hab
        exact hinj a (Finset.mem_range.mp ha) b (Finset.mem_range.mp hb) hab
      have hPlt : ((((Finset.range k).image w).card : ℝ)) < δ * n := by
        rw [hPcard]; exact Nat.lt_ceil.mp (by omega)
      obtain ⟨v, hvP, hv⟩ := hstep _ hPlt
      have himg : ∀ l : ℕ, l ≤ k →
          (Finset.range l).image (fun j => if j = k then v else w j)
            = (Finset.range l).image w := by
        intro l hl
        refine Finset.image_congr ?_
        intro a ha
        simp only [Finset.coe_range, Set.mem_Iio] at ha
        exact if_neg (by omega)
      have hgen : ∀ (u : Fin n) (l : ℕ), u = v → l = k →
          δ * n ≤ ((G.neighborFinset u ∪ (Finset.range l).image w).card : ℝ) := by
        intro u l hu hl
        subst hu
        subst hl
        have hsplit : ((G.neighborFinset u \ (Finset.range l).image w).card : ℝ)
            + ((((Finset.range l).image w).card : ℝ))
            = ((G.neighborFinset u ∪ (Finset.range l).image w).card : ℝ) := by
          rw [← Nat.cast_add, Finset.card_sdiff_add_card]
        rw [hPcard] at hv hsplit
        linarith
      refine ⟨fun i => if i = k then v else w i, ?_, ?_⟩
      · intro i hi j hj hij
        dsimp only at hij
        by_cases hik : i = k <;> by_cases hjk : j = k
        · omega
        · rw [if_pos hik, if_neg hjk] at hij
          exact absurd (hij ▸ Finset.mem_image_of_mem w (Finset.mem_range.mpr (by omega))) hvP
        · rw [if_neg hik, if_pos hjk] at hij
          exact absurd
            (hij.symm ▸ Finset.mem_image_of_mem w (Finset.mem_range.mpr (by omega))) hvP
        · rw [if_neg hik, if_neg hjk] at hij
          exact hinj i (by omega) j (by omega) hij
      · intro i hi
        by_cases hik : i = k
        · rw [himg i (by omega)]
          exact hgen _ i (if_pos hik) hik
        · rw [himg i (by omega)]
          have hwi : (fun j => if j = k then v else w j) i = w i := if_neg hik
          rw [hwi]
          exact hprop i (by omega)
  obtain ⟨w, hinj, hprop⟩ := hseq ⌈δ * n⌉₊ le_rfl
  have himgcard : ((Finset.range ⌈δ * n⌉₊).image w).card = ⌈δ * n⌉₊ := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    exact hinj a (Finset.mem_range.mp ha) b (Finset.mem_range.mp hb) hab
  -- the rank function: the greedily chosen vertices first, in order, then everything else
  obtain ⟨key, hkey_img, hkey_out⟩ : ∃ key : Fin n → ℕ,
      (∀ i, i < ⌈δ * n⌉₊ → key (w i) = i + 1) ∧
      (∀ v, v ∉ (Finset.range ⌈δ * n⌉₊).image w →
        key v = ⌈δ * n⌉₊ + 1 + (v : ℕ)) := by
    refine ⟨fun v =>
      if (∑ i ∈ Finset.range ⌈δ * n⌉₊, if w i = v then i + 1 else 0) = 0
        then ⌈δ * n⌉₊ + 1 + (v : ℕ)
        else (∑ i ∈ Finset.range ⌈δ * n⌉₊, if w i = v then i + 1 else 0), ?_, ?_⟩
    · intro i hi
      dsimp only
      have hs : (∑ j ∈ Finset.range ⌈δ * n⌉₊, if w j = w i then j + 1 else 0)
          = i + 1 := by
        refine (Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr hi) ?_).trans (if_pos rfl)
        intro b hb hbi
        exact if_neg fun h => hbi (hinj b (Finset.mem_range.mp hb) i hi h)
      rw [if_neg (by rw [hs]; omega)]
      exact hs
    · intro v hv
      dsimp only
      have hs : (∑ i ∈ Finset.range ⌈δ * n⌉₊, if w i = v then i + 1 else 0) = 0 :=
        Finset.sum_eq_zero fun i hi =>
          if_neg fun h => hv (by rw [← h]; exact Finset.mem_image_of_mem w hi)
      exact if_pos hs
  -- no vertex precedes itself, and no vertex is its own neighbour
  have hZv : ∀ v : Fin n,
      v ∉ G.neighborFinset v ∪ Finset.univ.filter (fun u => key u < key v) := by
    intro v hv
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset] at hv
    rcases hv with h | h
    · exact G.ne_of_adj h rfl
    · exact absurd h (lt_irrefl _)
  -- **every** vertex has at least `δ * n` neighbours-or-predecessors
  have hZ : ∀ v : Fin n,
      δ * n
        ≤ ((G.neighborFinset v ∪ Finset.univ.filter (fun u => key u < key v)).card : ℝ) := by
    intro v
    by_cases hv : v ∈ (Finset.range ⌈δ * n⌉₊).image w
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      have hi' := Finset.mem_range.mp hi
      refine le_trans (hprop i hi') (Nat.cast_le.mpr (Finset.card_le_card ?_))
      refine Finset.union_subset_union (Finset.Subset.refl _) ?_
      intro u hu
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hkey_img j (by have := Finset.mem_range.mp hj; omega), hkey_img i hi']
      have := Finset.mem_range.mp hj
      omega
    · have hsub : (Finset.range ⌈δ * n⌉₊).image w
          ⊆ Finset.univ.filter (fun u => key u < key v) := by
        intro u hu
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [hkey_img i (Finset.mem_range.mp hi), hkey_out v hv]
        have := Finset.mem_range.mp hi
        omega
      have hcard : ⌈δ * n⌉₊
          ≤ (G.neighborFinset v ∪ Finset.univ.filter (fun u => key u < key v)).card := by
        calc ⌈δ * n⌉₊ = ((Finset.range ⌈δ * n⌉₊).image w).card := himgcard.symm
          _ ≤ (Finset.univ.filter (fun u => key u < key v)).card := Finset.card_le_card hsub
          _ ≤ _ := Finset.card_le_card Finset.subset_union_right
      exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hcard)
  -- the container attached to the `≺`-least vertex of an independent set
  have hcont : ∀ (v₀ : Fin n) (J : Finset (Fin n)),
      G.IsIndepSet (J : Set (Fin n)) → v₀ ∈ J →
      (∀ u ∈ J, key v₀ ≤ key u) →
      v₀ ∈ J ∧
      J ⊆ insert v₀ (Finset.univ \ insert v₀
        (G.neighborFinset v₀ ∪ Finset.univ.filter (fun u => key u < key v₀))) ∧
      ((insert v₀ (Finset.univ \ insert v₀
        (G.neighborFinset v₀ ∪ Finset.univ.filter (fun u => key u < key v₀)))).card : ℝ)
        ≤ (1 - δ) * n := by
    intro v₀ J hJ hv₀ hminv
    have hins : insert v₀ (Finset.univ \ insert v₀
        (G.neighborFinset v₀ ∪ Finset.univ.filter (fun u => key u < key v₀)))
        = Finset.univ
          \ (G.neighborFinset v₀ ∪ Finset.univ.filter (fun u => key u < key v₀)) := by
      ext u
      by_cases h : u = v₀
      · subst h; simp [hZv]
      · simp [h]
    refine ⟨hv₀, ?_, ?_⟩
    · intro u hu
      rw [hins]
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hcon
      rcases Finset.mem_union.mp hcon with hcn | hcn
      · have hadj : G.Adj v₀ u := (SimpleGraph.mem_neighborFinset _ _ _).mp hcn
        exact hJ (by simpa using hv₀) (by simpa using hu) hadj.ne hadj
      · have := (Finset.mem_filter.mp hcn).2
        have := hminv u hu
        omega
    · rw [hins, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin]
      have h2 :
          (G.neighborFinset v₀ ∪ Finset.univ.filter (fun u => key u < key v₀)).card
            ≤ n := by
        simpa [Finset.card_univ] using Finset.card_le_univ
          (G.neighborFinset v₀ ∪ Finset.univ.filter (fun u => key u < key v₀))
      rw [Nat.cast_sub h2]
      have := hZ v₀
      nlinarith
  obtain ⟨sel, hsel⟩ : ∃ sel : Finset (Fin n) → Fin n,
      ∀ I : Finset (Fin n), I.Nonempty →
        sel I ∈ I ∧ ∀ u ∈ I, key (sel I) ≤ key u := by
    refine ⟨fun I => if h : (I.filter (fun v => ∀ u ∈ I, key v ≤ key u)).Nonempty then
      (I.filter (fun v => ∀ u ∈ I, key v ≤ key u)).min' h else ⟨0, hn⟩, ?_⟩
    intro I hIne
    have hfne : (I.filter (fun v => ∀ u ∈ I, key v ≤ key u)).Nonempty := by
      obtain ⟨v, hv, hvmin⟩ := I.exists_min_image key hIne
      exact ⟨v, Finset.mem_filter.mpr ⟨hv, hvmin⟩⟩
    dsimp only
    rw [dif_pos hfne]
    exact Finset.mem_filter.mp (Finset.min'_mem _ hfne)
  refine ⟨sel, fun v => Finset.univ \ insert v
      (G.neighborFinset v ∪ Finset.univ.filter (fun u => key u < key v)), ?_⟩
  intro I hI hIne
  obtain ⟨h1, h2⟩ := hsel I hIne
  exact hcont _ I hI h1 h2

/-- **The graph container theorem, with fingerprints** (Zhao, Theorem 11.2.3).  The refinement of
Theorem 11.2.1 that the applications actually need, and — despite the numbering — **the
statement the container algorithm actually produces.**  The container assigned to an independent
set `I` is not merely *some* member of a small family, but `S I ∪ A (S I)`, a function of a
fingerprint `S I ⊆ I`.  That `A` depends only on `S I` — and not otherwise on `I` — is the whole
content; it is what lets a union bound range over fingerprints.

It is stated **before** `exists_containers` because that is the direction the dependency runs:
11.2.1 is a counting corollary of this, obtained by taking `𝒞` to be the image of `A ∘ S` over
the small fingerprints.  The file originally had them in the book's order, which made the
corollary unprovable without a forward reference; a contributor working 11.2.1 found that and
reported it rather than duplicating the statement.

**`d ≤ 2 * δ * n` is load-bearing and was missing.**  It is Zhao's own proviso — stated on
printed p. 207 inside the proof idea ("provided that `d ≤ 2δ|V|`") and omitted from the theorem —
and without it the statement is **false** for every `c ≥ 3/2`.  Two instances refute it together:

* `G = Kₙ`, where `d = n - 1` and the only independent sets are `∅` and singletons.  If
  `δ < 1/2` then `2δn/d < 1`, so every fingerprint is forced empty, so the single container
  `A ∅` must contain every vertex and `n ≤ (1 - δ) n` fails.  Hence `δ ≥ 1/2`.
* `G` a disjoint union of `m` paths on three vertices, where `d = 4/3`, the maximum degree is
  `2 ≤ c d`, and the `2m` leaves are independent of size `2n/3`.  Any container holding them
  needs `(1 - δ) n ≥ 2n/3`.  Hence `δ ≤ 1/3`.

The hypothesis excludes the first family (`n - 1 ≤ 2δn` fails for `δ < 1/2`) while keeping the
second (`4/3 ≤ 2δn` for `n` large), which is exactly its role: it says the fingerprint budget
`2δn/d` is at least `1`, so that a fingerprint can be nonempty at all. -/
theorem exists_containers_fingerprint (c : ℝ) (hc : 0 < c) :
    ∃ δ > 0, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (d : ℝ), 0 < d →
      d ≤ 2 * δ * n →
      (∑ v, (G.degree v : ℝ)) = d * n → (∀ v, (G.degree v : ℝ) ≤ c * d) →
      ∃ S A : Finset (Fin n) → Finset (Fin n),
        ∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) →
          S I ⊆ I ∧ I ⊆ S I ∪ A (S I) ∧
          ((S I).card : ℝ) ≤ 2 * δ * n / d ∧
          ((S I ∪ A (S I)).card : ℝ) ≤ (1 - δ) * n := by
  have hm1 : (1 : ℝ) ≤ max c 1 := le_max_right _ _
  have hmc : c ≤ max c 1 := le_max_left _ _
  have hmpos : (0 : ℝ) < 100 * max c 1 := by linarith
  refine ⟨1 / (100 * max c 1), by positivity, fun n G _ d hd hdn hsum hdeg => ?_⟩
  set δ : ℝ := 1 / (100 * max c 1) with hδdef
  have hδ : (0 : ℝ) < δ := by rw [hδdef]; positivity
  have hδc : δ ≤ 1 / (100 * c) := by
    rw [hδdef]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hδ1 : δ ≤ 1 / 100 := by
    rw [hδdef]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  by_cases hcase : d ≤ δ * n
  · obtain ⟨pick, kill, hrule⟩ := exists_greedy_rule c d δ hc hδ hδc n G hd hcase hsum hdeg
    -- The obligation additionally yields stability of `S`, which this theorem does not expose.
    obtain ⟨S, A, hSA⟩ :=
      exists_fingerprint_of_greedy_rule c d δ hc hδ hδc n G hd hcase hsum hdeg pick kill hrule
    refine ⟨S, A, fun I hI => ?_⟩
    obtain ⟨h1, h2, h3, h4, -⟩ := hSA I hI
    exact ⟨h1, h2, h3, h4⟩
  · obtain ⟨s, K, hsK⟩ :=
      exists_dense_fingerprint c d δ hc hδ hδc n G hd (lt_of_not_ge hcase) hdn hsum hdeg
    refine ⟨fun I => if I = ∅ then ∅ else {s I}, fun T => T.biUnion K, fun I hI => ?_⟩
    by_cases hIe : I = ∅
    · subst hIe
      have hn : (0 : ℝ) ≤ (n : ℕ) := Nat.cast_nonneg n
      simp only [reduceIte, Finset.biUnion_empty, Finset.union_empty, Finset.card_empty,
        Nat.cast_zero, Finset.Subset.refl, true_and]
      exact ⟨by positivity, mul_nonneg (by linarith) hn⟩
    · have hne : I.Nonempty := Finset.nonempty_iff_ne_empty.mpr hIe
      obtain ⟨hsI, hcov, hcard⟩ := hsK I hI hne
      simp only [if_neg hIe, Finset.singleton_biUnion, Finset.singleton_union]
      refine ⟨Finset.singleton_subset_iff.mpr hsI, hcov, ?_, hcard⟩
      rw [Finset.card_singleton, Nat.cast_one, le_div_iff₀ hd]
      linarith

/-- **The graph container theorem** (Zhao, Theorem 11.2.1).  In a graph whose maximum degree is
within a constant factor of its average degree `d`, the independent sets are covered by a family
of containers indexed by "fingerprints" of size `≤ 2δ|V|/d`, each container missing at least a
`δ` fraction of the vertices.

The bound on `|𝒞|` is the book's `binom(|V|, ≤ 2δ|V|/d)`, written as the partial sum of binomial
coefficients it abbreviates.

**A corollary of `exists_containers_fingerprint` above**, not an independent theorem: take `𝒞`
to be the image of `T ↦ T ∪ A T` over the fingerprints `T` small enough and with `T ∪ A T` small
enough.  The second condition is load-bearing — without it the fingerprint theorem says nothing
about a `T` that is not some `S I`.

Carries the same `d ≤ 2 * δ * n` proviso as `exists_containers_fingerprint`, and for the same
reason — see the counterexamples in that docstring. -/
theorem exists_containers (c : ℝ) (hc : 0 < c) :
    ∃ δ > 0, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (d : ℝ), 0 < d →
      d ≤ 2 * δ * n →
      (∑ v, (G.degree v : ℝ)) = d * n → (∀ v, (G.degree v : ℝ) ≤ c * d) →
      ∃ 𝒞 : Finset (Finset (Fin n)),
        (𝒞.card : ℝ) ≤ ∑ i ∈ range (⌊2 * δ * n / d⌋₊ + 1), (n.choose i : ℝ) ∧
        (∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) → ∃ C ∈ 𝒞, I ⊆ C) ∧
        (∀ C ∈ 𝒞, (C.card : ℝ) ≤ (1 - δ) * n) := by
  obtain ⟨δ, hδ, hfp⟩ := exists_containers_fingerprint c hc
  refine ⟨δ, hδ, fun n G _ d hd hdn hsum hdeg => ?_⟩
  obtain ⟨S, A, hSA⟩ := hfp n G d hd hdn hsum hdeg
  -- The fingerprints that are both small and have a small container.  The second condition is
  -- needed because the fingerprint theorem says nothing about a `T` that is not some `S I`.
  set F : Finset (Finset (Fin n)) :=
    univ.powerset.filter fun T : Finset (Fin n) =>
      (T.card : ℝ) ≤ 2 * δ * n / d ∧ ((T ∪ A T).card : ℝ) ≤ (1 - δ) * n with hF
  refine ⟨F.image fun T => T ∪ A T, ?_, ?_, ?_⟩
  · have hsub : F ⊆ (range (⌊2 * δ * n / d⌋₊ + 1)).biUnion
        fun i => powersetCard i (univ : Finset (Fin n)) := by
      intro T hT
      rw [hF, mem_filter] at hT
      exact mem_biUnion.mpr ⟨T.card, mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hT.2.1)),
        mem_powersetCard.mpr ⟨subset_univ _, rfl⟩⟩
    have hcount : ((range (⌊2 * δ * n / d⌋₊ + 1)).biUnion
        fun i => powersetCard i (univ : Finset (Fin n))).card
        = ∑ i ∈ range (⌊2 * δ * n / d⌋₊ + 1), n.choose i := by
      rw [card_biUnion ((pairwise_disjoint_powersetCard (univ : Finset (Fin n))).set_pairwise _)]
      simp
    have hnat : (F.image fun T => T ∪ A T).card
        ≤ ∑ i ∈ range (⌊2 * δ * n / d⌋₊ + 1), n.choose i :=
      card_image_le.trans (hcount ▸ card_le_card hsub)
    calc ((F.image fun T => T ∪ A T).card : ℝ)
        ≤ ((∑ i ∈ range (⌊2 * δ * n / d⌋₊ + 1), n.choose i : ℕ) : ℝ) := Nat.cast_le.mpr hnat
      _ = ∑ i ∈ range (⌊2 * δ * n / d⌋₊ + 1), (n.choose i : ℝ) := by push_cast; ring
  · intro I hI
    obtain ⟨-, hcov, hsmall, hcont⟩ := hSA I hI
    exact ⟨S I ∪ A (S I), mem_image_of_mem _
      (mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), hsmall, hcont⟩), hcov⟩
  · intro C hC
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hC
    exact (mem_filter.mp hT).2.2

/-! ### 11.3 The hypergraph container theorem -/

/-- **One round of the hypergraph container algorithm** (Zhao, the algorithm on printed p. 209),
as an interface on the pick/kill pair, in the shape `IsGreedyRule` has for §11.2.

The state a round sees is an alive vertex set `Av` together with an alive hypergraph `Ae`.
`pick Av Ae T` selects from `T` the vertex of largest `Ae`-degree (ties by index), and
`kill Av Ae v` retires the vertices of `Av` that precede `v` in that order.  The five clauses:

* `pick` lands in `T` whenever there is anything to pick;
* **stability** — shrinking `T` to any `T'` still containing the selection does not change it.
  This is what lets the run be replayed from the fingerprint alone, exactly as in §11.2;
* `kill` retires only alive vertices, and never the selected one;
* the retired set is **disjoint from `T`**, with no independence hypothesis.  §11.2's analogue
  needs one because its `kill` also takes a neighbourhood; here `kill` holds only order
  predecessors, and the selection is order-first in `T`, so disjointness is immediate;
* the **double count**, stated raw rather than solved for the selected vertex's degree:
  summing `Ae`-degrees over `Av` counts each edge three times, the retired vertices and the
  selection contribute at most `(|kill| + 1) * Δ₁(Ae)`, and every surviving vertex has degree at
  most the selection's.  **Its 3-uniformity hypothesis is load-bearing**: the identity it rests on
  is `∑_{v ∈ Av} deg_{Ae}(v) = ∑_{e ∈ Ae} |e|`, which is `3|Ae|` only when every edge has three
  vertices and undershoots otherwise.  Without it the clause is false — `Ae = {∅}` on one vertex
  pins every other quantity to zero and demands `3 ≤ c * d`.

The forbidden-pair graph does not appear here.  Zhao's round also adds pairs to it and deletes
edges meeting one, but those actions are determined by the state rather than chosen, so they
belong to the run and not to this interface.

**The clause hypotheses are the run's invariants**, passed in rather than assumed globally, which
is what keeps this interface stable: strengthening the run's invariant set does not change what a
rule has to provide.  It is also why this carries no relation between `d` and `n` — that
constraint belongs to the nodes that call §11.2, not to the round.

Public because it appears in the statements of published tasks. -/
def IsContainerRound {n : ℕ} (c d : ℝ)
    (pick : Finset (Fin n) → Finset (Finset (Fin n)) → Finset (Fin n) → Fin n)
    (kill : Finset (Fin n) → Finset (Finset (Fin n)) → Fin n → Finset (Fin n)) : Prop :=
  (∀ (Av : Finset (Fin n)) (Ae : Finset (Finset (Fin n))) (T : Finset (Fin n)),
      T.Nonempty → pick Av Ae T ∈ T) ∧
  (∀ (Av : Finset (Fin n)) (Ae : Finset (Finset (Fin n))) (T T' : Finset (Fin n)),
      T' ⊆ T → pick Av Ae T ∈ T' → pick Av Ae T' = pick Av Ae T) ∧
  (∀ (Av : Finset (Fin n)) (Ae : Finset (Finset (Fin n))) (v : Fin n),
      kill Av Ae v ⊆ Av ∧ v ∉ kill Av Ae v) ∧
  (∀ (Av : Finset (Fin n)) (Ae : Finset (Finset (Fin n))) (T : Finset (Fin n)),
      T.Nonempty → Disjoint (kill Av Ae (pick Av Ae T)) T) ∧
  (∀ (Av : Finset (Fin n)) (Ae : Finset (Finset (Fin n))) (T : Finset (Fin n)),
      T ⊆ Av → T.Nonempty → (∀ e ∈ Ae, e ⊆ Av) → (∀ e ∈ Ae, e.card = 3) →
      (maxCodegree 1 Ae : ℝ) ≤ c * d →
      3 * (Ae.card : ℝ)
        ≤ (n : ℝ) * ((Ae.filter fun e => pick Av Ae T ∈ e).card : ℝ)
          + (((kill Av Ae (pick Av Ae T)).card : ℝ) + 1) * (c * d))

/-- **Such a round exists** — the hypergraph analogue of `exists_greedy_rule`.

Take the order on `Av` given by decreasing `Ae`-degree with ties by vertex index, let
`pick Av Ae T` be the order-first element of `T`, and let `kill Av Ae v` be
`{u ∈ Av | u ≺ v}`.  Stability holds for any order-first selection over an order depending only
on the state, disjointness because the selection is order-first in `T`, and the double count by
splitting the degree sum over `Av` at the retired set.

`pick` and `kill` must be total; `exists_greedy_rule` encodes its order as an injective `ℕ` weight
and selects with `Nat.sInf`, which keeps everything total without a `Decidable` instance.

**The weight does not transpose unchanged.**  `exists_greedy_rule` uses
`n * (n - deg) + u`, which relies on a *graph* degree being at most `n`.  A hypergraph degree
`#{e ∈ Ae | u ∈ e}` can reach `|Ae|`, so `n - deg` would truncate to `0` and the order would
collapse.  Take the subtraction bound from `Ae` instead — `n * (Ae.card - deg) + u` — and the
`% n` decode still works because `u < n`.  The monotonicity step is nonlinear in `n`, so it needs
`by_contra` plus a `Nat.mul_le_mul` rather than a bare `omega`, exactly as in
`exists_greedy_rule`.

**`0 < n` is required, and without it the theorem is false.**  At `n = 0` the clauses are all
vacuous, but the *witnesses* cannot be built: `pick`'s domain `Finset (Fin 0)` is inhabited — it
contains `∅` — while its codomain `Fin 0` is empty, so no function of that type exists and the
existential fails outright.  No strengthening of the clause bodies can rescue it:

    rintro ⟨pick, kill, -⟩; exact (pick ∅ ∅ ∅).elim0

`exists_greedy_rule` avoids this by accident: its `hdn : d ≤ δ * n` with `0 < d` forces `0 < n`.
This statement inherited the shape without the hypothesis that made it sound. -/
theorem exists_container_round (c d : ℝ) (hc : 0 < c) (hd : 0 < d) (n : ℕ) (hn : 0 < n) :
    ∃ (pick : Finset (Fin n) → Finset (Finset (Fin n)) → Finset (Fin n) → Fin n)
      (kill : Finset (Fin n) → Finset (Finset (Fin n)) → Fin n → Finset (Fin n)),
      IsContainerRound c d pick kill := by
  sorry

/-- The two vertices of an unordered pair, as a `Finset`. -/
private def pairVerts {n : ℕ} (p : Sym2 (Fin n)) : Finset (Fin n) :=
  {x ∈ (univ : Finset (Fin n)) | x ∈ p}

private theorem mem_pairVerts {n : ℕ} {p : Sym2 (Fin n)} {v : Fin n} :
    v ∈ pairVerts p ↔ v ∈ p := by simp [pairVerts]

private theorem pairVerts_mk {n : ℕ} (x y : Fin n) : pairVerts s(x, y) = {x, y} := by
  ext v
  simp [pairVerts, Sym2.mem_iff]

/-- The vertices whose forbidden-pair degree has passed the threshold `K`. -/
private def highPairDeg {n : ℕ} (K : ℕ) (E : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
  {v ∈ (univ : Finset (Fin n)) | K < #{e ∈ E | v ∈ e}}

/-- The alive vertex set of a run state: everything neither retired, nor selected, nor deleted
for forbidden-pair degree. -/
private def roundAliveV {n : ℕ} (K : ℕ) (X S : Finset (Fin n))
    (E : Finset (Sym2 (Fin n))) : Finset (Fin n) := (X ∪ S ∪ highPairDeg K E)ᶜ

/-- The alive hypergraph of a run state: the edges of `H` that lie inside the alive vertex set
and contain no forbidden pair. -/
private def roundAliveE {n : ℕ} (K : ℕ) (H : Finset (Finset (Fin n))) (X S : Finset (Fin n))
    (E : Finset (Sym2 (Fin n))) : Finset (Finset (Fin n)) :=
  {e ∈ H | e ⊆ roundAliveV K X S E ∧ ∀ x ∈ e, ∀ y ∈ e, s(x, y) ∉ E}

/-- The forbidden pairs created by selecting `u`: the pairs `xy` for which `uxy` is an edge of the
alive hypergraph. -/
private def roundNewPairs {n : ℕ} (Ae : Finset (Finset (Fin n))) (u : Fin n) :
    Finset (Sym2 (Fin n)) :=
  {p ∈ (univ : Finset (Sym2 (Fin n))) | ¬ p.IsDiag ∧ u ∉ p ∧ insert u (pairVerts p) ∈ Ae}

private theorem mem_roundNewPairs {n : ℕ} {Ae : Finset (Finset (Fin n))} {u : Fin n}
    {p : Sym2 (Fin n)} : p ∈ roundNewPairs Ae u ↔
      ¬ p.IsDiag ∧ u ∉ p ∧ insert u (pairVerts p) ∈ Ae := by
  simp [roundNewPairs]

/-- One round applied to a run state: select from the alive part of the target `T`, retire the
round's `kill` set, record the selection, and add the forbidden pairs the selection creates. -/
private def roundStep {n : ℕ} (K : ℕ) (H : Finset (Finset (Fin n)))
    (pick : Finset (Fin n) → Finset (Finset (Fin n)) → Finset (Fin n) → Fin n)
    (kill : Finset (Fin n) → Finset (Finset (Fin n)) → Fin n → Finset (Fin n))
    (T X S : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) :
    Finset (Fin n) × Finset (Fin n) × Finset (Sym2 (Fin n)) :=
  (X ∪ kill (roundAliveV K X S E) (roundAliveE K H X S E)
      (pick (roundAliveV K X S E) (roundAliveE K H X S E) (T ∩ roundAliveV K X S E)),
    insert (pick (roundAliveV K X S E) (roundAliveE K H X S E) (T ∩ roundAliveV K X S E)) S,
    E ∪ roundNewPairs (roundAliveE K H X S E)
      (pick (roundAliveV K X S E) (roundAliveE K H X S E) (T ∩ roundAliveV K X S E)))

/-- The run of §11.3: iterate `roundStep` on the target `T` from the state `(X, S, E)`, halting
once `bX` vertices are retired, once `bE` forbidden pairs are recorded, or once nothing of `T` is
alive; `fuel` caps the number of rounds. -/
private def roundRun {n : ℕ} (K bX bE : ℕ) (H : Finset (Finset (Fin n)))
    (pick : Finset (Fin n) → Finset (Finset (Fin n)) → Finset (Fin n) → Fin n)
    (kill : Finset (Fin n) → Finset (Finset (Fin n)) → Fin n → Finset (Fin n))
    (T : Finset (Fin n)) :
    ℕ → Finset (Fin n) → Finset (Fin n) → Finset (Sym2 (Fin n)) →
      Finset (Fin n) × Finset (Fin n) × Finset (Sym2 (Fin n))
  | 0, X, S, E => (X, S, E)
  | fuel + 1, X, S, E =>
    if bX ≤ X.card then (X, S, E)
    else if bE ≤ E.card then (X, S, E)
    else if (T ∩ roundAliveV K X S E).Nonempty then
      roundRun K bX bE H pick kill T fuel (roundStep K H pick kill T X S E).1
        (roundStep K H pick kill T X S E).2.1 (roundStep K H pick kill T X S E).2.2
    else (X, S, E)

/-- Every component of the run's state only ever grows. -/
private theorem roundRun_grows {n : ℕ} (K bX bE : ℕ) (H : Finset (Finset (Fin n)))
    (pick : Finset (Fin n) → Finset (Finset (Fin n)) → Finset (Fin n) → Fin n)
    (kill : Finset (Fin n) → Finset (Finset (Fin n)) → Fin n → Finset (Fin n))
    (T : Finset (Fin n)) (fuel : ℕ) :
    ∀ (X S : Finset (Fin n)) (E : Finset (Sym2 (Fin n))),
      X ⊆ (roundRun K bX bE H pick kill T fuel X S E).1 ∧
      S ⊆ (roundRun K bX bE H pick kill T fuel X S E).2.1 ∧
      E ⊆ (roundRun K bX bE H pick kill T fuel X S E).2.2 := by
  induction fuel with
  | zero => exact fun X S E => ⟨Subset.refl _, Subset.refl _, Subset.refl _⟩
  | succ fuel ih =>
    intro X S E
    rw [roundRun]
    split_ifs with h1 h2 h3
    · exact ⟨Subset.refl _, Subset.refl _, Subset.refl _⟩
    · exact ⟨Subset.refl _, Subset.refl _, Subset.refl _⟩
    · exact ⟨Finset.subset_union_left.trans (ih _ _ _).1,
        (Finset.subset_insert _ _).trans (ih _ _ _).2.1,
        Finset.subset_union_left.trans (ih _ _ _).2.2⟩
    · exact ⟨Subset.refl _, Subset.refl _, Subset.refl _⟩

/-- **The run is replayed by the set of vertices it selects.**  Shrinking the target to any `J`
that still contains every selected vertex leaves the run unchanged: the state, and hence the
alive vertex set and the alive hypergraph, agree step by step, and stability of `pick` forces the
same selection. -/
private theorem roundRun_replay {n : ℕ} (K bX bE : ℕ) (H : Finset (Finset (Fin n)))
    (pick : Finset (Fin n) → Finset (Finset (Fin n)) → Finset (Fin n) → Fin n)
    (kill : Finset (Fin n) → Finset (Finset (Fin n)) → Fin n → Finset (Fin n))
    (hpick : ∀ (Av : Finset (Fin n)) (Ae : Finset (Finset (Fin n))) (T : Finset (Fin n)),
      T.Nonempty → pick Av Ae T ∈ T)
    (hstab : ∀ (Av : Finset (Fin n)) (Ae : Finset (Finset (Fin n))) (T T' : Finset (Fin n)),
      T' ⊆ T → pick Av Ae T ∈ T' → pick Av Ae T' = pick Av Ae T)
    (fuel : ℕ) :
    ∀ (T J X S : Finset (Fin n)) (E : Finset (Sym2 (Fin n))),
      (roundRun K bX bE H pick kill T fuel X S E).2.1 ⊆ J → J ⊆ T →
        roundRun K bX bE H pick kill J fuel X S E
          = roundRun K bX bE H pick kill T fuel X S E := by
  induction fuel with
  | zero => exact fun T J X S E _ _ => rfl
  | succ fuel ih =>
    intro T J X S E hSJ hJT
    have hstep : ∀ T' : Finset (Fin n),
        roundRun K bX bE H pick kill T' (fuel + 1) X S E =
          if bX ≤ X.card then (X, S, E)
          else if bE ≤ E.card then (X, S, E)
          else if (T' ∩ roundAliveV K X S E).Nonempty then
            roundRun K bX bE H pick kill T' fuel (roundStep K H pick kill T' X S E).1
              (roundStep K H pick kill T' X S E).2.1 (roundStep K H pick kill T' X S E).2.2
          else (X, S, E) := fun T' => by rw [roundRun]
    rw [hstep T] at hSJ
    rw [hstep J, hstep T]
    by_cases h1 : bX ≤ X.card
    · simp only [if_pos h1]
    simp only [if_neg h1] at hSJ ⊢
    by_cases h2 : bE ≤ E.card
    · simp only [if_pos h2]
    simp only [if_neg h2] at hSJ ⊢
    set Av : Finset (Fin n) := roundAliveV K X S E with hAv
    set Ae : Finset (Finset (Fin n)) := roundAliveE K H X S E with hAe
    by_cases h3 : (T ∩ Av).Nonempty
    · simp only [if_pos h3] at hSJ ⊢
      have hvT : pick Av Ae (T ∩ Av) ∈ T ∩ Av := hpick _ _ _ h3
      have hvJ : pick Av Ae (T ∩ Av) ∈ J :=
        hSJ ((roundRun_grows K bX bE H pick kill T fuel _ _ _).2.1
          (Finset.mem_insert_self _ _))
      have hvJA : pick Av Ae (T ∩ Av) ∈ J ∩ Av :=
        Finset.mem_inter.mpr ⟨hvJ, (Finset.mem_inter.mp hvT).2⟩
      have h3J : (J ∩ Av).Nonempty := ⟨_, hvJA⟩
      have hsel : pick Av Ae (J ∩ Av) = pick Av Ae (T ∩ Av) :=
        hstab Av Ae (T ∩ Av) (J ∩ Av) (Finset.inter_subset_inter_right hJT) hvJA
      simp only [if_pos h3J, roundStep, ← hAv, ← hAe, hsel]
      exact ih T J _ _ _ hSJ hJT
    · have h3J : ¬ (J ∩ Av).Nonempty := by
        rintro ⟨x, hx⟩
        rw [Finset.mem_inter] at hx
        exact h3 ⟨x, Finset.mem_inter.mpr ⟨hJT hx.1, hx.2⟩⟩
      simp only [if_neg h3, if_neg h3J]

private theorem pairVerts_inj {n : ℕ} {p q : Sym2 (Fin n)} (h : pairVerts p = pairVerts q) :
    p = q :=
  Sym2.ext fun x => by
    rw [← mem_pairVerts, ← mem_pairVerts, h]

/-- A vertex's hypergraph degree is at most `Δ₁`. -/
private theorem card_filter_mem_le_codegree {n : ℕ} (H : Finset (Finset (Fin n))) (v : Fin n) :
    #{e ∈ H | v ∈ e} ≤ maxCodegree 1 H := by
  unfold maxCodegree
  have hmem : ({v} : Finset (Fin n)) ∈
      Finset.filter (fun A : Finset (Fin n) => A.card = 1) univ := by simp
  refine le_trans (le_of_eq (congrArg Finset.card ?_))
    (Finset.le_sup (f := fun A : Finset (Fin n) => #{e ∈ H | A ⊆ e}) hmem)
  ext e
  simp [Finset.singleton_subset_iff]

/-- A pair's hypergraph codegree is at most `Δ₂`. -/
private theorem card_filter_pairVerts_le_codegree {n : ℕ} (H : Finset (Finset (Fin n)))
    {p : Sym2 (Fin n)} (hp : ¬ p.IsDiag) :
    #{e ∈ H | pairVerts p ⊆ e} ≤ maxCodegree 2 H := by
  unfold maxCodegree
  have hmem : pairVerts p ∈ Finset.filter (fun A : Finset (Fin n) => A.card = 2) univ := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact card_filter_mem_eq_two p hp
  exact Finset.le_sup (f := fun A : Finset (Fin n) => #{e ∈ H | A ⊆ e}) hmem

/-- **Union bound on the edges a vertex set meets.** -/
private theorem card_filter_meets_le {n : ℕ} (H : Finset (Finset (Fin n)))
    (W : Finset (Fin n)) :
    #{e ∈ H | ∃ v ∈ W, v ∈ e} ≤ W.card * maxCodegree 1 H := by
  classical
  calc #{e ∈ H | ∃ v ∈ W, v ∈ e}
      ≤ #(W.biUnion fun v => {e ∈ H | v ∈ e}) := by
        refine Finset.card_le_card fun e he => ?_
        simp only [Finset.mem_filter] at he
        obtain ⟨heH, v, hvW, hve⟩ := he
        exact Finset.mem_biUnion.mpr ⟨v, hvW, Finset.mem_filter.mpr ⟨heH, hve⟩⟩
    _ ≤ ∑ v ∈ W, #{e ∈ H | v ∈ e} := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ W, maxCodegree 1 H :=
        Finset.sum_le_sum fun v _ => card_filter_mem_le_codegree H v
    _ = W.card * maxCodegree 1 H := by rw [Finset.sum_const, smul_eq_mul]

/-- **Union bound on the edges a set of forbidden pairs meets.** -/
private theorem card_filter_pairs_le {n : ℕ} (H : Finset (Finset (Fin n)))
    (E : Finset (Sym2 (Fin n))) (hdiag : ∀ e ∈ E, ¬ e.IsDiag) :
    #{e ∈ H | ∃ x ∈ e, ∃ y ∈ e, s(x, y) ∈ E} ≤ E.card * maxCodegree 2 H := by
  classical
  calc #{e ∈ H | ∃ x ∈ e, ∃ y ∈ e, s(x, y) ∈ E}
      ≤ #(E.biUnion fun p => {e ∈ H | pairVerts p ⊆ e}) := by
        refine Finset.card_le_card fun e he => ?_
        simp only [Finset.mem_filter] at he
        obtain ⟨heH, x, hxe, y, hye, hxy⟩ := he
        refine Finset.mem_biUnion.mpr ⟨s(x, y), hxy, Finset.mem_filter.mpr ⟨heH, ?_⟩⟩
        rw [pairVerts_mk]
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz'
        · exact hxe
        · rw [Finset.mem_singleton] at hz'; exact hz' ▸ hye
    _ ≤ ∑ p ∈ E, #{e ∈ H | pairVerts p ⊆ e} := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ E, maxCodegree 2 H :=
        Finset.sum_le_sum fun p hp => card_filter_pairVerts_le_codegree H (hdiag p hp)
    _ = E.card * maxCodegree 2 H := by rw [Finset.sum_const, smul_eq_mul]

/-- **The handshake bound on the vertices deleted for forbidden-pair degree.** -/
private theorem card_highPairDeg_mul_le {n : ℕ} (K : ℕ) (E : Finset (Sym2 (Fin n)))
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) :
    (highPairDeg K E).card * (K + 1) ≤ 2 * E.card := by
  have hlow : (highPairDeg K E).card * (K + 1)
      ≤ ∑ v ∈ highPairDeg K E, #{e ∈ E | v ∈ e} := by
    refine le_trans (le_of_eq ?_) (Finset.card_nsmul_le_sum _ _ (K + 1) ?_)
    · rw [smul_eq_mul]
    · intro v hv
      simp only [highPairDeg, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      omega
  refine hlow.trans ?_
  rw [← sum_card_incident E hdiag]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

private theorem roundNewPairs_not_isDiag {n : ℕ} {Ae : Finset (Finset (Fin n))} {u : Fin n}
    {p : Sym2 (Fin n)} (hp : p ∈ roundNewPairs Ae u) : ¬ p.IsDiag :=
  (mem_roundNewPairs.mp hp).1

/-- **Selecting `u` creates one forbidden pair per alive edge at `u`.** -/
private theorem card_filter_le_card_roundNewPairs {n : ℕ} (Ae : Finset (Finset (Fin n)))
    (h3 : ∀ e ∈ Ae, e.card = 3) (u : Fin n) :
    #{e ∈ Ae | u ∈ e} ≤ (roundNewPairs Ae u).card := by
  refine Finset.card_le_card_of_surjOn (fun p => insert u (pairVerts p)) ?_
  intro e he
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at he
  obtain ⟨heAe, hue⟩ := he
  have hcard : (e.erase u).card = 2 := by rw [Finset.card_erase_of_mem hue, h3 e heAe]
  obtain ⟨x, y, hxy, hxyeq⟩ := Finset.card_eq_two.mp hcard
  have hue' : u ∉ ({x, y} : Finset (Fin n)) := by
    rw [← hxyeq]; exact Finset.notMem_erase u e
  have heq : insert u ({x, y} : Finset (Fin n)) = e := by
    rw [← hxyeq, Finset.insert_erase hue]
  refine ⟨s(x, y), ?_, by simpa only [pairVerts_mk] using heq⟩
  simp only [Finset.mem_coe, mem_roundNewPairs, pairVerts_mk, heq]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hue'
  refine ⟨by simpa [Sym2.mk_isDiag_iff] using hxy, ?_, heAe⟩
  simp only [Sym2.mem_iff]
  tauto

/-- **The forbidden pairs a selection creates are new**: an alive edge contains no pair of `E`. -/
private theorem roundNewPairs_disjoint {n : ℕ} (K : ℕ) (H : Finset (Finset (Fin n)))
    (X S : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) (u : Fin n) :
    Disjoint E (roundNewPairs (roundAliveE K H X S E) u) := by
  rw [Finset.disjoint_right]
  intro p
  induction p using Sym2.ind with
  | _ x y =>
    intro hp hpE
    rw [mem_roundNewPairs] at hp
    have hAe := hp.2.2
    rw [roundAliveE, Finset.mem_filter, pairVerts_mk] at hAe
    exact hAe.2.2 x (Finset.mem_insert_of_mem (Finset.mem_insert_self x {y})) y
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))) hpE

/-- **Each vertex gains at most `Δ₂` forbidden-pair neighbours per round.** -/
private theorem card_filter_mem_roundNewPairs_le {n : ℕ} (H : Finset (Finset (Fin n)))
    {Ae : Finset (Finset (Fin n))} (hsub : Ae ⊆ H) {u v : Fin n} (huv : u ≠ v) :
    #{p ∈ roundNewPairs Ae u | v ∈ p} ≤ maxCodegree 2 H := by
  refine le_trans (Finset.card_le_card_of_injOn (fun p => insert u (pairVerts p)) ?_ ?_)
    (card_filter_pairVerts_le_codegree H (p := s(u, v))
      (by simpa [Sym2.mk_isDiag_iff] using huv))
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp
    obtain ⟨hpn, hvp⟩ := hp
    rw [mem_roundNewPairs] at hpn
    simp only [Finset.coe_filter, Set.mem_ofPred_eq]
    refine ⟨hsub hpn.2.2, ?_⟩
    rw [pairVerts_mk]
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz'
    · exact Finset.mem_insert_self _ _
    · rw [Finset.mem_singleton] at hz'
      subst hz'
      exact Finset.mem_insert_of_mem (mem_pairVerts.mpr hvp)
  · intro p hp q hq heq
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp hq
    have hup : u ∉ pairVerts p := fun h => (mem_roundNewPairs.mp hp.1).2.1 (mem_pairVerts.mp h)
    have huq : u ∉ pairVerts q := fun h => (mem_roundNewPairs.mp hq.1).2.1 (mem_pairVerts.mp h)
    refine pairVerts_inj ?_
    simp only at heq
    rw [← Finset.erase_insert hup, ← Finset.erase_insert huq, heq]

/-- **A selection creates no pair at a vertex already past the deletion threshold**, because the
alive hypergraph lives inside the alive vertex set. -/
private theorem filter_mem_roundNewPairs_eq_empty {n : ℕ} (K : ℕ) (H : Finset (Finset (Fin n)))
    (X S : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) (u : Fin n) {v : Fin n}
    (hv : K < #{e ∈ E | v ∈ e}) :
    {p ∈ roundNewPairs (roundAliveE K H X S E) u | v ∈ p} = ∅ := by
  refine Finset.filter_eq_empty_iff.mpr ?_
  intro p hp hvp
  rw [mem_roundNewPairs] at hp
  have hAe := hp.2.2
  rw [roundAliveE, Finset.mem_filter] at hAe
  have halive : v ∈ roundAliveV K X S E :=
    hAe.2.1 (Finset.mem_insert_of_mem (mem_pairVerts.mpr hvp))
  rw [roundAliveV, Finset.mem_compl] at halive
  refine halive (Finset.mem_union_right _ ?_)
  simp only [highPairDeg, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hv

/-- **The pairs a selection creates meet no independent set**, since each comes from an edge
of `H` on the selected vertex and the pair. -/
private theorem notMem_roundNewPairs_of_indep {n : ℕ} {H Ae : Finset (Finset (Fin n))}
    (hsub : Ae ⊆ H) {I : Finset (Fin n)} (hI : ∀ e ∈ H, ¬ e ⊆ I) {u : Fin n} (hu : u ∈ I)
    {a b : Fin n} (ha : a ∈ I) (hb : b ∈ I) : s(a, b) ∉ roundNewPairs Ae u := by
  intro hmem
  rw [mem_roundNewPairs, pairVerts_mk] at hmem
  refine hI _ (hsub hmem.2.2) ?_
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz'
  · exact hu
  · rcases Finset.mem_insert.mp hz' with rfl | hz''
    · exact ha
    · rw [Finset.mem_singleton] at hz''
      exact hz'' ▸ hb

/-- **The forbidden-pair degree invariant survives a round.**  A vertex already past the deletion
threshold gains nothing, and a vertex below it gains at most `Δ₂ ≤ c * √d`. -/
private theorem roundStep_degree {n : ℕ} {c d : ℝ} {H : Finset (Finset (Fin n))}
    (hcod2 : (maxCodegree 2 H : ℝ) ≤ c * Real.sqrt d)
    {K : ℕ} (hKle : (K : ℝ) ≤ c * Real.sqrt d)
    (X S : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) (u : Fin n)
    (hEdeg : ∀ v : Fin n, (#{e ∈ E | v ∈ e} : ℝ) ≤ 2 * c * Real.sqrt d) (v : Fin n) :
    (#{e ∈ E ∪ roundNewPairs (roundAliveE K H X S E) u | v ∈ e} : ℝ)
      ≤ 2 * c * Real.sqrt d := by
  have hAeH : roundAliveE K H X S E ⊆ H := by rw [roundAliveE]; exact Finset.filter_subset _ _
  have hle : #{e ∈ E ∪ roundNewPairs (roundAliveE K H X S E) u | v ∈ e}
      ≤ #{e ∈ E | v ∈ e} + #{e ∈ roundNewPairs (roundAliveE K H X S E) u | v ∈ e} := by
    rw [Finset.filter_union]
    exact Finset.card_union_le _ _
  by_cases hvhigh : K < #{e ∈ E | v ∈ e}
  · rw [filter_mem_roundNewPairs_eq_empty K H X S E u hvhigh, Finset.card_empty,
      Nat.add_zero] at hle
    exact le_trans (Nat.cast_le.mpr hle) (hEdeg v)
  · have hnew : #{e ∈ roundNewPairs (roundAliveE K H X S E) u | v ∈ e} ≤ maxCodegree 2 H := by
      by_cases huv : u = v
      · subst huv
        have hempty : {e ∈ roundNewPairs (roundAliveE K H X S E) u | u ∈ e} = ∅ :=
          Finset.filter_eq_empty_iff.mpr fun p hp => (mem_roundNewPairs.mp hp).2.1
        simp [hempty]
      · exact card_filter_mem_roundNewPairs_le H hAeH huv
    have hb1 : (#{e ∈ E | v ∈ e} : ℝ) ≤ c * Real.sqrt d :=
      le_trans (Nat.cast_le.mpr (Nat.le_of_not_lt hvhigh)) hKle
    have hb2 : (#{e ∈ roundNewPairs (roundAliveE K H X S E) u | v ∈ e} : ℝ)
        ≤ c * Real.sqrt d := le_trans (Nat.cast_le.mpr hnew) hcod2
    have hb3 : (#{e ∈ E ∪ roundNewPairs (roundAliveE K H X S E) u | v ∈ e} : ℝ)
        ≤ (#{e ∈ E | v ∈ e} : ℝ)
          + (#{e ∈ roundNewPairs (roundAliveE K H X S E) u | v ∈ e} : ℝ) := by
      exact_mod_cast hle
    linarith

/-- **The forbidden-pair count grows by the alive degree of the selected vertex.** -/
private theorem card_union_roundNewPairs {n : ℕ} {H : Finset (Finset (Fin n))}
    (h3 : ∀ e ∈ H, e.card = 3) (K : ℕ) (X S : Finset (Fin n))
    (E : Finset (Sym2 (Fin n))) (u : Fin n) :
    E.card + #{e ∈ roundAliveE K H X S E | u ∈ e}
      ≤ (E ∪ roundNewPairs (roundAliveE K H X S E) u).card := by
  have hAeH : roundAliveE K H X S E ⊆ H := by rw [roundAliveE]; exact Finset.filter_subset _ _
  rw [Finset.card_union_of_disjoint (roundNewPairs_disjoint K H X S E u)]
  exact Nat.add_le_add_left
    (card_filter_le_card_roundNewPairs _ (fun e he => h3 e (hAeH he)) u) _

/-- **One round yields `4 * n * d / 5`, split between forbidden pairs and retired vertices.**

Few enough edges of `H` have been deleted — at most `|W| Δ₁` for meeting a dead vertex and
`|E| Δ₂` for containing a forbidden pair — that the round's raw double count, which is stated
against the alive hypergraph, becomes a bound against `d * n`. -/
private theorem round_yield {n : ℕ} {c d : ℝ} {H : Finset (Finset (Fin n))}
    (hHsum : 3 * (H.card : ℝ) = d * n)
    (hcod1 : (maxCodegree 1 H : ℝ) ≤ c * d) (hcod2 : (maxCodegree 2 H : ℝ) ≤ c * Real.sqrt d)
    {K : ℕ} {X S : Finset (Fin n)} {E : Finset (Sym2 (Fin n))}
    (hEd : ∀ e ∈ E, ¬ e.IsDiag)
    (hslackv : 3 * ((X.card : ℝ) + S.card + (highPairDeg K E).card) * (c * d)
        + 3 * (E.card : ℝ) * (c * Real.sqrt d) ≤ 1 / 5 * (n : ℝ) * d)
    {t k : ℕ}
    (hdbl : 3 * ((roundAliveE K H X S E).card : ℝ)
      ≤ (n : ℝ) * (t : ℝ) + ((k : ℝ) + 1) * (c * d)) :
    4 / 5 * (n : ℝ) * d ≤ (n : ℝ) * (t : ℝ) + ((k : ℝ) + 1) * (c * d) := by
  have hsub : H ⊆ roundAliveE K H X S E ∪
      ({e ∈ H | ∃ v ∈ X ∪ S ∪ highPairDeg K E, v ∈ e}
        ∪ {e ∈ H | ∃ x ∈ e, ∃ y ∈ e, s(x, y) ∈ E}) := by
    intro e he
    by_cases hin : e ⊆ roundAliveV K X S E ∧ ∀ x ∈ e, ∀ y ∈ e, s(x, y) ∉ E
    · exact Finset.mem_union_left _ (by rw [roundAliveE, Finset.mem_filter]; exact ⟨he, hin⟩)
    · refine Finset.mem_union_right _ ?_
      rw [not_and_or] at hin
      rcases hin with hin | hin
      · obtain ⟨v, hv, hvn⟩ := Finset.not_subset.mp hin
        refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, v, ?_, hv⟩)
        rw [roundAliveV, Finset.mem_compl, not_not] at hvn
        exact hvn
      · push Not at hin
        obtain ⟨x, hx, y, hy, hxy⟩ := hin
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, x, hx, y, hy, hxy⟩)
  have hcardH : H.card ≤ (roundAliveE K H X S E).card
      + ((X ∪ S ∪ highPairDeg K E).card * maxCodegree 1 H + E.card * maxCodegree 2 H) := by
    refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_union_le _ _) ?_)
    refine Nat.add_le_add_left (le_trans (Finset.card_union_le _ _) ?_) _
    exact Nat.add_le_add (card_filter_meets_le H _) (card_filter_pairs_le H E hEd)
  have hWcard : ((X ∪ S ∪ highPairDeg K E).card : ℝ)
      ≤ (X.card : ℝ) + S.card + (highPairDeg K E).card := by
    have h := le_trans (Finset.card_union_le (X ∪ S) (highPairDeg K E))
      (Nat.add_le_add_right (Finset.card_union_le X S) _)
    exact_mod_cast h
  have h1 : ((X ∪ S ∪ highPairDeg K E).card : ℝ) * (maxCodegree 1 H : ℝ)
      ≤ ((X.card : ℝ) + S.card + (highPairDeg K E).card) * (c * d) :=
    mul_le_mul hWcard hcod1 (Nat.cast_nonneg _) (by positivity)
  have h2 : ((E.card : ℝ)) * (maxCodegree 2 H : ℝ) ≤ (E.card : ℝ) * (c * Real.sqrt d) :=
    mul_le_mul_of_nonneg_left hcod2 (Nat.cast_nonneg _)
  have h0 : (H.card : ℝ) ≤ ((roundAliveE K H X S E).card : ℝ)
      + (((X ∪ S ∪ highPairDeg K E).card : ℝ) * (maxCodegree 1 H : ℝ)
        + (E.card : ℝ) * (maxCodegree 2 H : ℝ)) := by
    exact_mod_cast hcardH
  have hcomm : d * (n : ℝ) = (n : ℝ) * d := mul_comm _ _
  linarith

/-- **The invariants carried by one run of the container algorithm on an independent set `I`.**

Along the run the retired set misses `I`, the selected vertices stay inside `I`, the forbidden
pairs stay diagonal-free, of degree at most `2 * c * √d`, and absent from `I`; the number of
selections never exceeds the round budget `B`; and the run halts either with the retirement
threshold met, with the forbidden-pair threshold met, with nothing of `I` left alive, or — only
if the round budget is spent — with the accumulated yield `4 * n * d * B / 5`. -/
private theorem roundRun_invariants {n : ℕ} {c d : ℝ}
    {H : Finset (Finset (Fin n))} (h3 : ∀ e ∈ H, e.card = 3)
    (hHsum : 3 * (H.card : ℝ) = d * n)
    (hcod1 : (maxCodegree 1 H : ℝ) ≤ c * d) (hcod2 : (maxCodegree 2 H : ℝ) ≤ c * Real.sqrt d)
    {K bX bE B : ℕ} (hKle : (K : ℝ) ≤ c * Real.sqrt d)
    (hslack : ∀ aX aS aD aE : ℕ, aX < bX → aS ≤ B → aE < bE → aD * (K + 1) ≤ 2 * aE →
      3 * ((aX : ℝ) + aS + aD) * (c * d) + 3 * (aE : ℝ) * (c * Real.sqrt d)
        ≤ 1 / 5 * (n : ℝ) * d)
    {pick : Finset (Fin n) → Finset (Finset (Fin n)) → Finset (Fin n) → Fin n}
    {kill : Finset (Fin n) → Finset (Finset (Fin n)) → Fin n → Finset (Fin n)}
    (hrule : IsContainerRound c d pick kill)
    {I : Finset (Fin n)} (hI : ∀ e ∈ H, ¬ e ⊆ I) (fuel : ℕ) :
    ∀ (X S Y Q : Finset (Fin n)) (E F : Finset (Sym2 (Fin n))),
      roundRun K bX bE H pick kill I fuel X S E = (Y, Q, F) →
      Disjoint X I → S ⊆ I → (∀ e ∈ E, ¬ e.IsDiag) →
      (∀ v : Fin n, (#{e ∈ E | v ∈ e} : ℝ) ≤ 2 * c * Real.sqrt d) →
      (∀ a ∈ I, ∀ b ∈ I, s(a, b) ∉ E) →
      4 / 5 * (n : ℝ) * d * (S.card : ℝ)
        ≤ (n : ℝ) * (E.card : ℝ) + ((X.card : ℝ) + (S.card : ℝ)) * (c * d) →
      S.card + fuel = B →
      Disjoint Y I ∧ Q ⊆ I ∧ (∀ e ∈ F, ¬ e.IsDiag) ∧
        (∀ v : Fin n, (#{e ∈ F | v ∈ e} : ℝ) ≤ 2 * c * Real.sqrt d) ∧
        (∀ a ∈ I, ∀ b ∈ I, s(a, b) ∉ F) ∧ Q.card ≤ B ∧
        (bX ≤ Y.card ∨ bE ≤ F.card ∨ I ⊆ Q ∪ highPairDeg K F ∨
          4 / 5 * (n : ℝ) * d * (B : ℝ)
            ≤ (n : ℝ) * (F.card : ℝ) + ((Y.card : ℝ) + (Q.card : ℝ)) * (c * d)) := by
  obtain ⟨hmem, -, hkill, hdsj, hcount⟩ := hrule
  induction fuel with
  | zero =>
    intro X S Y Q E F hrun hXI hSI hEd hEdeg hEI hpot hfuel
    simp only [roundRun, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl, rfl⟩ := hrun
    refine ⟨hXI, hSI, hEd, hEdeg, hEI, by omega, Or.inr (Or.inr (Or.inr ?_))⟩
    have hSB : (S.card : ℝ) = (B : ℝ) := by
      have h : S.card = B := by omega
      exact_mod_cast h
    rw [← hSB]
    exact hpot
  | succ fuel ih =>
    intro X S Y Q E F hrun hXI hSI hEd hEdeg hEI hpot hfuel
    rw [roundRun] at hrun
    by_cases h1 : bX ≤ X.card
    · rw [if_pos h1] at hrun
      simp only [Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl, rfl⟩ := hrun
      exact ⟨hXI, hSI, hEd, hEdeg, hEI, by omega, Or.inl h1⟩
    rw [if_neg h1] at hrun
    by_cases h2 : bE ≤ E.card
    · rw [if_pos h2] at hrun
      simp only [Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl, rfl⟩ := hrun
      exact ⟨hXI, hSI, hEd, hEdeg, hEI, by omega, Or.inr (Or.inl h2)⟩
    rw [if_neg h2] at hrun
    by_cases h4 : (I ∩ roundAliveV K X S E).Nonempty
    swap
    · rw [if_neg h4] at hrun
      simp only [Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl, rfl⟩ := hrun
      refine ⟨hXI, hSI, hEd, hEdeg, hEI, by omega, Or.inr (Or.inr (Or.inl ?_))⟩
      intro x hx
      by_contra hxc
      refine h4 ⟨x, Finset.mem_inter.mpr ⟨hx, ?_⟩⟩
      rw [roundAliveV, Finset.mem_compl]
      intro hmemW
      rcases Finset.mem_union.mp hmemW with hW | hW
      · rcases Finset.mem_union.mp hW with hW' | hW'
        · exact Finset.disjoint_left.mp hXI hW' hx
        · exact hxc (Finset.mem_union_left _ hW')
      · exact hxc (Finset.mem_union_right _ hW)
    rw [if_pos h4] at hrun
    simp only [roundStep] at hrun
    obtain ⟨u, hudef⟩ : ∃ u, u = pick (roundAliveV K X S E) (roundAliveE K H X S E)
        (I ∩ roundAliveV K X S E) := ⟨_, rfl⟩
    rw [← hudef] at hrun
    have hAeH : roundAliveE K H X S E ⊆ H := by
      rw [roundAliveE]; exact Finset.filter_subset _ _
    have hAesub : ∀ e ∈ roundAliveE K H X S E, e ⊆ roundAliveV K X S E := by
      intro e he
      rw [roundAliveE, Finset.mem_filter] at he
      exact he.2.1
    have huIAv : u ∈ I ∩ roundAliveV K X S E := by
      rw [hudef]; exact hmem _ _ _ h4
    have huI : u ∈ I := (Finset.mem_inter.mp huIAv).1
    have huW : u ∉ X ∪ S ∪ highPairDeg K E := by
      have h := (Finset.mem_inter.mp huIAv).2
      rw [roundAliveV, Finset.mem_compl] at h
      exact h
    have huS : u ∉ S := fun h => huW (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    obtain ⟨hkillsub, hkillu⟩ := hkill (roundAliveV K X S E) (roundAliveE K H X S E) u
    have hkillI : Disjoint (kill (roundAliveV K X S E) (roundAliveE K H X S E) u) I := by
      have hd0 := hdsj (roundAliveV K X S E) (roundAliveE K H X S E)
        (I ∩ roundAliveV K X S E) h4
      rw [← hudef] at hd0
      rw [Finset.disjoint_left]
      intro a ha haI
      exact Finset.disjoint_left.mp hd0 ha (Finset.mem_inter.mpr ⟨haI, hkillsub ha⟩)
    have hkillX : Disjoint X (kill (roundAliveV K X S E) (roundAliveE K H X S E) u) := by
      rw [Finset.disjoint_right]
      intro a ha
      have h := hkillsub ha
      rw [roundAliveV, Finset.mem_compl] at h
      exact fun haX => h (Finset.mem_union_left _ (Finset.mem_union_left _ haX))
    have hcod1Ae : (maxCodegree 1 (roundAliveE K H X S E) : ℝ) ≤ c * d :=
      le_trans (Nat.cast_le.mpr (maxCodegree_mono 1 hAeH)) hcod1
    have hdbl : 3 * ((roundAliveE K H X S E).card : ℝ)
        ≤ (n : ℝ) * (#{e ∈ roundAliveE K H X S E | u ∈ e} : ℝ)
          + ((#(kill (roundAliveV K X S E) (roundAliveE K H X S E) u) : ℝ) + 1) * (c * d) := by
      have h := hcount (roundAliveV K X S E) (roundAliveE K H X S E)
        (I ∩ roundAliveV K X S E) Finset.inter_subset_right h4 hAesub
        (fun e he => h3 e (hAeH he)) hcod1Ae
      rw [← hudef] at h
      exact h
    have hyield : 4 / 5 * (n : ℝ) * d
        ≤ (n : ℝ) * (#{e ∈ roundAliveE K H X S E | u ∈ e} : ℝ)
          + ((#(kill (roundAliveV K X S E) (roundAliveE K H X S E) u) : ℝ) + 1) * (c * d) :=
      round_yield hHsum hcod1 hcod2 hEd
        (hslack X.card S.card (highPairDeg K E).card E.card (by omega) (by omega) (by omega)
          (card_highPairDeg_mul_le K E hEd)) hdbl
    refine ih _ _ Y Q _ F hrun (Finset.disjoint_union_left.mpr ⟨hXI, hkillI⟩)
      (Finset.insert_subset huI hSI) ?_ (roundStep_degree hcod2 hKle X S E u hEdeg) ?_ ?_ ?_
    · intro e he
      rcases Finset.mem_union.mp he with h | h
      · exact hEd e h
      · exact roundNewPairs_not_isDiag h
    · intro a ha b hb hmem'
      rcases Finset.mem_union.mp hmem' with h | h
      · exact hEI a ha b hb h
      · exact notMem_roundNewPairs_of_indep hAeH hI huI ha hb h
    · have hcX : (X ∪ kill (roundAliveV K X S E) (roundAliveE K H X S E) u).card
          = X.card + (kill (roundAliveV K X S E) (roundAliveE K H X S E) u).card :=
        Finset.card_union_of_disjoint hkillX
      have hcS : (insert u S).card = S.card + 1 := Finset.card_insert_of_notMem huS
      have hcE : (E.card : ℝ) + (#{e ∈ roundAliveE K H X S E | u ∈ e} : ℝ)
          ≤ ((E ∪ roundNewPairs (roundAliveE K H X S E) u).card : ℝ) := by
        exact_mod_cast card_union_roundNewPairs h3 K X S E u
      have hmul : (n : ℝ) * ((E.card : ℝ) + (#{e ∈ roundAliveE K H X S E | u ∈ e} : ℝ))
          ≤ (n : ℝ) * ((E ∪ roundNewPairs (roundAliveE K H X S E) u).card : ℝ) :=
        mul_le_mul_of_nonneg_left hcE (Nat.cast_nonneg n)
      rw [hcX, hcS]
      push_cast
      linarith
    · rw [Finset.card_insert_of_notMem huS]
      omega













/-- **The run: iterate the round and deliver the first phase's fingerprint.**

The largest of §11.3's nodes, and the analogue of `exists_fingerprint_of_greedy_rule`.  Given a
round satisfying `IsContainerRound`, iterate it at most `⌊n / (2√d)⌋` times from `Av = univ`,
`Ae = H`, accumulating the selected vertices into `S`, the vertices retired by `kill` into the
set whose complement `R` names, and the forbidden pairs into `E`: on selecting `u`, every pair
`xy` with `uxy` an edge of the **alive** hypergraph joins `E`, vertices of `E`-degree above
`c√d` leave the alive set, and edges meeting a pair of `E` leave `Ae`.

**The deletion threshold is `c√d`, one factor of `c√d` below the degree conjunct, and it has to
be.**  A survivor sitting at the threshold can still gain a whole round's worth of new pairs, and
a round adds at most `Δ₂ ≤ c√d` at any one vertex.  Cutting at `K` therefore leaves survivors at
`K + c√d`, so the conjunct `deg_E ≤ 2c√d` forces `K ≤ c√d`.  Cutting at `2c√d` instead would make
that conjunct false.

**Read `u x y ∈ E(A)`, not `E(H)`.**  The source's algorithm box says `E(H)`; with `E(H)` the
degree invariant below is false, since a vertex would accumulate up to `|S| · Δ₂ = Θ(c · n)`
forbidden-pair neighbours.

**The budget is on rounds, not on retired vertices**, which is this run's main simplification over
§11.2's.  There the budget was on retired vertices and recovering `m ≤ B` from
`(m-1)·yield < budget` forced the retirement guarantee up from `d/2` to `3d/4`; here the round
count is capped directly and no sharpening is needed.

**`R` is not "the retired set", and reading it that way is the trap.**  It is whatever set the
run chooses to exclude from the container, and the choice differs by halting mode — the run can
stop because either threshold fired, because `I` ran out of alive vertices, or because the round
budget ran out.  `R` is existentially returned and the halting mode is a function of the
fingerprint through the same replay that gives stability, so a mode-dependent choice is still a
well-defined function.

**The dichotomy follows from one handshake bound, in every mode.**  Writing `D` for the vertices
deleted for forbidden-pair degree, summing degrees gives `|D| · c√d < 2|E|`, so
`|D| < 2|E|/(c√d)`.  Then either `|E| ≥ n√d/(100M)` and the second disjunct holds, or `D` is small
and the first does: either enough vertices were retired, or `I` was exhausted, in which case
`I ⊆ S ∪ D` and the complement of that container clears `n/(100M)` comfortably.  Covering needs no
case split at all, because the retired vertices are disjoint from `I`.

The last four conjuncts are exactly the hypotheses of `exists_fingerprint_of_dense_pairs` at
`F := E (S I)`; that they compose with no bridging step is machine-checked.  The budget `n/(2√d)`
is half the composite's, the dense branch supplying the other half.

A `private` definition for the run is expected and welcome, as is a further `choir-reduction` if
the recursion and its invariants are more than one PR's worth. -/
theorem exists_run_of_container_round (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (n : ℕ) (H : Finset (Finset (Fin n)))
    (h3 : ∀ e ∈ H, e.card = 3)
    (hsum : 3 * (H.card : ℝ) = d * n)
    (hcod1 : (maxCodegree 1 H : ℝ) ≤ c * d)
    (hcod2 : (maxCodegree 2 H : ℝ) ≤ c * Real.sqrt d)
    (hn : 10 ^ 5 * (max c 1) ^ 2 ≤ Real.sqrt d)
    (hqn : 4 * Real.sqrt d ≤ (n : ℝ))
    (pick : Finset (Fin n) → Finset (Finset (Fin n)) → Finset (Fin n) → Fin n)
    (kill : Finset (Fin n) → Finset (Finset (Fin n)) → Fin n → Finset (Fin n))
    (hrule : IsContainerRound c d pick kill) :
    ∃ (S R : Finset (Fin n) → Finset (Fin n))
      (E : Finset (Fin n) → Finset (Sym2 (Fin n))),
      ∀ I : Finset (Fin n), (∀ e ∈ H, ¬ e ⊆ I) →
        S I ⊆ I ∧
        ((S I).card : ℝ) ≤ (n : ℝ) / (2 * Real.sqrt d) ∧
        (∀ J : Finset (Fin n), S I ⊆ J → J ⊆ I → S J = S I) ∧
        I ⊆ S I ∪ (R (S I))ᶜ ∧
        (∀ e ∈ E (S I), ¬ e.IsDiag) ∧
        (∀ v : Fin n, (((E (S I)).filter fun e => v ∈ e).card : ℝ)
            ≤ 2 * c * Real.sqrt d) ∧
        (∀ u ∈ I, ∀ v ∈ I, s(u, v) ∉ E (S I)) ∧
        ((n : ℝ) / (100 * max c 1) ≤ ((R (S I)).card : ℝ) ∨
          (n : ℝ) * Real.sqrt d / (100 * max c 1) ≤ ((E (S I)).card : ℝ)) := by
  -- `n` and `√d` are positive
  have hq0 : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have hnR : (0 : ℝ) < n := lt_of_lt_of_le (by linarith) hqn
  -- the hypergraph handshake identity: summing degrees counts each edge three times
  have hhand : ∑ v : Fin n, (#{e ∈ H | v ∈ e} : ℝ) = 3 * (H.card : ℝ) := by
    have hnat : ∑ v : Fin n, #{e ∈ H | v ∈ e} = 3 * H.card := by
      have hswap : ∑ v : Fin n, #{e ∈ H | v ∈ e}
          = ∑ e ∈ H, #{v ∈ (univ : Finset (Fin n)) | v ∈ e} := by
        simp only [Finset.card_filter]
        exact Finset.sum_comm
      have hfil : ∀ e ∈ H, #{v ∈ (univ : Finset (Fin n)) | v ∈ e} = 3 := by
        intro e he
        rw [show {v ∈ (univ : Finset (Fin n)) | v ∈ e} = e by ext v; simp]
        exact h3 e he
      rw [hswap, Finset.sum_congr rfl hfil, Finset.sum_const, smul_eq_mul, mul_comm]
    exact_mod_cast hnat
  -- the maximum degree bound forces `c ≥ 1`, hence `max c 1 = c`
  have hc1 : (1 : ℝ) ≤ c := by
    have hub : ∑ v : Fin n, (#{e ∈ H | v ∈ e} : ℝ) ≤ (n : ℝ) * (c * d) := by
      calc ∑ v : Fin n, (#{e ∈ H | v ∈ e} : ℝ) ≤ ∑ _v : Fin n, c * d :=
            Finset.sum_le_sum fun v _ =>
              le_trans (Nat.cast_le.mpr (card_filter_mem_le_codegree H v)) hcod1
        _ = (n : ℝ) * (c * d) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hhand, hsum] at hub
    nlinarith only [hub, mul_pos hnR hd]
  have hM : max c 1 = c := max_eq_left hc1
  rw [hM] at hn
  simp only [hM]
  set q : ℝ := Real.sqrt d with hqdef
  have hdq : d = q ^ 2 := by rw [hqdef, Real.sq_sqrt hd.le]
  have h5c : 10 ^ 5 * c ≤ q := by
    linarith only [hn, mul_nonneg hc.le (sub_nonneg.mpr hc1)]
  have hq5 : (10 : ℝ) ^ 5 ≤ q := by linarith only [h5c, hc1]
  have hcsq : (1 : ℝ) ≤ c ^ 2 := by nlinarith only [hc1]
  -- the thresholds: the forbidden-pair degree cut `K`, the two halting budgets, the round budget
  set K : ℕ := ⌊c * q⌋₊ with hKdef
  set bX : ℕ := ⌈(n : ℝ) / (100 * c)⌉₊ with hbXdef
  set bE : ℕ := ⌈(n : ℝ) * q / (100 * c)⌉₊ with hbEdef
  set B : ℕ := ⌊(n : ℝ) / (2 * q)⌋₊ with hBdef
  have hKle : (K : ℝ) ≤ c * q := by rw [hKdef]; exact Nat.floor_le (by positivity)
  have hKgt : c * q < (K : ℝ) + 1 := by rw [hKdef]; exact Nat.lt_floor_add_one _
  have hbXle : (n : ℝ) / (100 * c) ≤ (bX : ℝ) := by rw [hbXdef]; exact Nat.le_ceil _
  have hbEle : (n : ℝ) * q / (100 * c) ≤ (bE : ℝ) := by rw [hbEdef]; exact Nat.le_ceil _
  have hBle : (B : ℝ) ≤ (n : ℝ) / (2 * q) := by rw [hBdef]; exact Nat.floor_le (by positivity)
  have hBgt : (n : ℝ) / (2 * q) < (B : ℝ) + 1 := by rw [hBdef]; exact Nat.lt_floor_add_one _
  -- the slack that makes each round yield `4 * n * d / 5`
  have hslack : ∀ aX aS aD aE : ℕ, aX < bX → aS ≤ B → aE < bE → aD * (K + 1) ≤ 2 * aE →
      3 * ((aX : ℝ) + aS + aD) * (c * d) + 3 * (aE : ℝ) * (c * q) ≤ 1 / 5 * (n : ℝ) * d := by
    intro aX aS aD aE haX haS haE haD
    have hXlt : (aX : ℝ) * (100 * c) < (n : ℝ) := by
      rw [hbXdef] at haX
      exact (lt_div_iff₀ (by positivity)).mp (Nat.lt_ceil.mp haX)
    have hElt : (aE : ℝ) * (100 * c) < (n : ℝ) * q := by
      rw [hbEdef] at haE
      exact (lt_div_iff₀ (by positivity)).mp (Nat.lt_ceil.mp haE)
    have hSle : (aS : ℝ) * (2 * q) ≤ (n : ℝ) :=
      (le_div_iff₀ (by positivity)).mp (le_trans (by exact_mod_cast haS) hBle)
    have hDle : (aD : ℝ) * (c * q) ≤ 2 * (aE : ℝ) := by
      have hcast : (aD : ℝ) * ((K : ℝ) + 1) ≤ 2 * (aE : ℝ) := by exact_mod_cast haD
      linarith only [hcast,
        mul_le_mul_of_nonneg_left hKgt.le (Nat.cast_nonneg aD : (0 : ℝ) ≤ aD)]
    rw [hdq]
    have e1 : 3 * (aX : ℝ) * (c * q ^ 2) ≤ 3 / 100 * ((n : ℝ) * q ^ 2) := by
      linarith only [mul_le_mul_of_nonneg_right hXlt.le (sq_nonneg q)]
    have e2 : 3 * (aS : ℝ) * (c * q ^ 2) ≤ 3 / 2 * ((n : ℝ) * (c * q)) := by
      linarith only [mul_le_mul_of_nonneg_right hSle (by positivity : (0 : ℝ) ≤ c * q)]
    have e3 : 3 * (aD : ℝ) * (c * q ^ 2) ≤ 6 * q * (aE : ℝ) := by
      linarith only [mul_le_mul_of_nonneg_right hDle hq0.le]
    have e4 : 6 * q * (aE : ℝ) ≤ 6 / 100 * ((n : ℝ) * q ^ 2) := by
      have h1 : (aE : ℝ) * 100 ≤ (n : ℝ) * q := by
        linarith only [hElt,
          mul_nonneg (Nat.cast_nonneg aE : (0 : ℝ) ≤ aE) (sub_nonneg.mpr hc1)]
      linarith only [mul_le_mul_of_nonneg_right h1 hq0.le]
    have e5 : 3 * (aE : ℝ) * (c * q) ≤ 3 / 100 * ((n : ℝ) * q ^ 2) := by
      linarith only [mul_le_mul_of_nonneg_right hElt.le hq0.le]
    have e6 : 3 / 2 * ((n : ℝ) * (c * q)) ≤ 3 / (2 * 10 ^ 5) * ((n : ℝ) * q ^ 2) := by
      linarith only [mul_le_mul_of_nonneg_right h5c (mul_nonneg hnR.le hq0.le)]
    linarith only [e1, e2, e3, e4, e5, e6, mul_nonneg hnR.le (sq_nonneg q)]
  -- the fingerprint is the set of selected vertices; the excluded set is chosen by halting mode
  have hmem := hrule.1
  have hstab := hrule.2.1
  refine ⟨fun J => (roundRun K bX bE H pick kill J B ∅ ∅ ∅).2.1,
    fun J => if bX ≤ (roundRun K bX bE H pick kill J B ∅ ∅ ∅).1.card ∨
        bE ≤ (roundRun K bX bE H pick kill J B ∅ ∅ ∅).2.2.card then
      (roundRun K bX bE H pick kill J B ∅ ∅ ∅).1
      else ((roundRun K bX bE H pick kill J B ∅ ∅ ∅).2.1
        ∪ highPairDeg K (roundRun K bX bE H pick kill J B ∅ ∅ ∅).2.2)ᶜ,
    fun J => (roundRun K bX bE H pick kill J B ∅ ∅ ∅).2.2, fun I hI => ?_⟩
  obtain ⟨Y, Q, F, hYQF⟩ : ∃ Y Q F, roundRun K bX bE H pick kill I B ∅ ∅ ∅ = (Y, Q, F) :=
    ⟨_, _, _, rfl⟩
  obtain ⟨hYI, hQI, hFd, hFdeg, hFI, hQB, hhalt⟩ :=
    roundRun_invariants h3 hsum hcod1 hcod2 hKle hslack hrule hI
      B ∅ ∅ Y Q ∅ F hYQF (by simp) (by simp) (by simp)
      (fun v => by
        simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
        positivity)
      (by simp) (by simp) (by simp)
  -- replaying on the fingerprint reproduces the run, which is both stability and how `R` and
  -- `E` are recovered from `S I`
  have hreplay : ∀ J : Finset (Fin n), Q ⊆ J → J ⊆ I →
      roundRun K bX bE H pick kill J B ∅ ∅ ∅ = (Y, Q, F) := fun J hQJ hJI => by
    rw [roundRun_replay K bX bE H pick kill hmem hstab B I J ∅ ∅ ∅
      (by rw [hYQF]; exact hQJ) hJI, hYQF]
  have hQQ : roundRun K bX bE H pick kill Q B ∅ ∅ ∅ = (Y, Q, F) :=
    hreplay Q (Finset.Subset.refl _) hQI
  simp only [hYQF, hQQ]
  have hQcard : (Q.card : ℝ) ≤ (n : ℝ) / (2 * q) := le_trans (by exact_mod_cast hQB) hBle
  have hQb : (Q.card : ℝ) * (2 * q) ≤ (n : ℝ) := (le_div_iff₀ (by positivity)).mp hQcard
  have hBn : (n : ℝ) < ((B : ℝ) + 1) * (2 * q) := (div_lt_iff₀ (by positivity)).mp hBgt
  have hstabfin : ∀ J : Finset (Fin n), Q ⊆ J → J ⊆ I →
      (roundRun K bX bE H pick kill J B ∅ ∅ ∅).2.1 = Q := fun J hQJ hJI => by
    rw [hreplay J hQJ hJI]
  by_cases hcase : bX ≤ Y.card ∨ bE ≤ F.card
  · -- a threshold fired: the excluded set is the retired set, which misses `I`
    rw [if_pos hcase]
    refine ⟨hQI, hQcard, hstabfin, ?_, hFd, hFdeg, hFI, ?_⟩
    · intro x hx
      exact Finset.mem_union_right _
        (Finset.mem_compl.mpr fun hxY => Finset.disjoint_left.mp hYI hxY hx)
    · rcases hcase with hX | hE
      · exact Or.inl (le_trans hbXle (by exact_mod_cast hX))
      · exact Or.inr (le_trans hbEle (by exact_mod_cast hE))
  · -- no threshold fired, so the run exhausted the alive vertices of `I`
    rw [if_neg hcase]
    rw [not_or] at hcase
    have hXlt : Y.card < bX := Nat.lt_of_not_le hcase.1
    have hElt : F.card < bE := Nat.lt_of_not_le hcase.2
    have hYb : (Y.card : ℝ) * (100 * c) < (n : ℝ) := by
      rw [hbXdef] at hXlt
      exact (lt_div_iff₀ (by positivity)).mp (Nat.lt_ceil.mp hXlt)
    have hFb : (F.card : ℝ) * (100 * c) < (n : ℝ) * q := by
      rw [hbEdef] at hElt
      exact (lt_div_iff₀ (by positivity)).mp (Nat.lt_ceil.mp hElt)
    have hIcov : I ⊆ Q ∪ highPairDeg K F := by
      rcases hhalt with h | h | h | h
      · exact absurd h hcase.1
      · exact absurd h hcase.2
      · exact h
      · -- the round budget cannot run out while both thresholds are unmet
        exfalso
        rw [hdq] at h
        have hlhs : 2 / 5 * ((n : ℝ) * q) * ((n : ℝ) - 2 * q)
            ≤ 4 / 5 * (n : ℝ) * q ^ 2 * (B : ℝ) := by
          linarith only [mul_le_mul_of_nonneg_left
            (by linarith only [hBn] : (n : ℝ) - 2 * q ≤ (B : ℝ) * (2 * q))
            (by positivity : (0 : ℝ) ≤ 2 / 5 * ((n : ℝ) * q))]
        have p1 : (n : ℝ) * (F.card : ℝ) ≤ 1 / 100 * ((n : ℝ) * (n : ℝ) * q) := by
          have h1 : (F.card : ℝ) * 100 ≤ (n : ℝ) * q := by
            linarith only [hFb, mul_nonneg
              (Nat.cast_nonneg F.card : (0 : ℝ) ≤ (F.card : ℝ)) (sub_nonneg.mpr hc1)]
          linarith only [mul_le_mul_of_nonneg_left h1 hnR.le]
        have p2 : (Y.card : ℝ) * (c * q ^ 2) ≤ 1 / 100 * ((n : ℝ) * q ^ 2) := by
          linarith only [mul_le_mul_of_nonneg_right hYb.le (sq_nonneg q)]
        have p3 : (Q.card : ℝ) * (c * q ^ 2) ≤ 1 / (2 * 10 ^ 5) * ((n : ℝ) * q ^ 2) := by
          linarith only [mul_le_mul_of_nonneg_right hQb (by positivity : (0 : ℝ) ≤ c * q),
            mul_le_mul_of_nonneg_right h5c (mul_nonneg hnR.le hq0.le)]
        have p4 : (n : ℝ) * q ^ 2 ≤ 1 / 4 * ((n : ℝ) * (n : ℝ) * q) := by
          linarith only [mul_le_mul_of_nonneg_left hqn (mul_nonneg hnR.le hq0.le)]
        have hpos : (0 : ℝ) < (n : ℝ) * (n : ℝ) * q := by positivity
        linarith only [h, hlhs, p1, p2, p3, p4, hpos]
    refine ⟨hQI, hQcard, hstabfin, ?_, hFd, hFdeg, hFI, ?_⟩
    · intro x hx
      rw [compl_compl]
      exact Finset.mem_union_right _ (hIcov hx)
    · -- the container `S I ∪ D` leaves out all but a `1/50` fraction of the vertices
      refine Or.inl ?_
      have hcompl : (((Q ∪ highPairDeg K F)ᶜ).card : ℝ)
          = (n : ℝ) - ((Q ∪ highPairDeg K F).card : ℝ) := by
        rw [Finset.card_compl, Fintype.card_fin,
          Nat.cast_sub (by simpa using Finset.card_le_univ (Q ∪ highPairDeg K F))]
      rw [hcompl]
      have hUc : ((Q ∪ highPairDeg K F).card : ℝ)
          ≤ (Q.card : ℝ) + ((highPairDeg K F).card : ℝ) := by
        exact_mod_cast Finset.card_union_le Q (highPairDeg K F)
      have hD1 : ((highPairDeg K F).card : ℝ) * ((K : ℝ) + 1) ≤ 2 * (F.card : ℝ) := by
        exact_mod_cast card_highPairDeg_mul_le K F hFd
      have hD2 : ((highPairDeg K F).card : ℝ) * (c * q) ≤ 2 * (F.card : ℝ) := by
        linarith only [hD1, mul_le_mul_of_nonneg_left hKgt.le
          (Nat.cast_nonneg (highPairDeg K F).card :
            (0 : ℝ) ≤ ((highPairDeg K F).card : ℝ))]
      have hD3 : 100 * ((highPairDeg K F).card : ℝ) * c ^ 2 * q < 2 * ((n : ℝ) * q) := by
        linarith only [mul_le_mul_of_nonneg_right hD2 (by positivity : (0 : ℝ) ≤ 100 * c), hFb]
      have hD4 : 100 * ((highPairDeg K F).card : ℝ) * c ^ 2 < 2 * (n : ℝ) :=
        lt_of_mul_lt_mul_right (by linarith only [hD3]) hq0.le
      have hD0 : (0 : ℝ) ≤ ((highPairDeg K F).card : ℝ) := Nat.cast_nonneg _
      have hQ0 : (0 : ℝ) ≤ (Q.card : ℝ) := Nat.cast_nonneg _
      have hD5 : ((highPairDeg K F).card : ℝ) * 100 < 2 * (n : ℝ) := by
        linarith only [hD4, mul_le_mul_of_nonneg_left hcsq
          (by linarith only [hD0] : (0 : ℝ) ≤ 100 * ((highPairDeg K F).card : ℝ))]
      have hQ5 : (Q.card : ℝ) * (2 * 10 ^ 5) ≤ (n : ℝ) := by
        linarith only [hQb, mul_le_mul_of_nonneg_left hq5
          (by linarith only [hQ0] : (0 : ℝ) ≤ 2 * (Q.card : ℝ))]
      have hdivc : (n : ℝ) / (100 * c) ≤ (n : ℝ) / 100 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith only [hc1, hnR]
      linarith only [hdivc, hUc, hD5, hQ5, hnR]



/-- **The dense branch of §11.3: containers from a dense graph of forbidden pairs.**

When the hypergraph algorithm terminates without having retired many vertices, the graph `F` of
forbidden pairs it accumulated is dense and of bounded degree, and the *graph* container theorem
applies to it.  This node is that application, and it is the chapter's only cross-chapter
dependency.

**It is stated on the edge set alone and mentions no run**, so it does not wait on the run node:
what the dense branch supplies is four properties of `F` — diagonal-free, degrees at most
`2 * c * √d`, at least `n√d/(100 * max c 1)` edges, and the applicability bound `happ` — together
with a set `I` containing no pair of `F`.  `degree_fromEdgeSet` bridges the degree hypothesis to
the `SimpleGraph` form §11.2 wants.

**`happ` is what keeps the call legal, and it is not slack.**  Writing `M = max c 1` and
`q = √d`, the accumulated graph has average degree `d_G = 2|F|/n`, which `hdense` puts at
`≥ q/(50M)` and `hdeg` at `≤ 2cq`.  So §11.2 must be invoked at `c_G = 100M²` and
`δ_G = 1/(100 c_G) = 1/(10⁴M²)`, and its hypothesis `d_G ≤ δ_G * n` becomes `2cq ≤ n/(10⁴M²)`.
`happ` supplies that with a factor of five to spare.  **Outside `happ` the graph container theorem
cannot be applied to `F` at all** — that regime is §11.3's open question and is deliberately not
a task.

Call the **δ-parametric** obligations `exists_greedy_rule` and `exists_fingerprint_of_greedy_rule`,
not `exists_containers` or `exists_containers_fingerprint`: those bind `δ` existentially, so their
`δ` cannot be named in a hypothesis here and no bound on `c, d, n` can guarantee their proviso.
The obligations take `δ` as an argument, so this node chooses it.

The two conclusions §11.2 returns sit inside what is claimed here with room: its budget
`2 δ_G n / d_G` is at most `n/(100 M q)`, against the `n/(2q)` below, and its container bound
`(1 - δ_G) n` is stronger than the `(1 - δ) n` below, since `δ_G ≥ δ`.  The final conjunct is the
stability property, which the obligation provides and the composite fingerprint of §11.3
needs. -/
theorem exists_fingerprint_of_dense_pairs (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (n : ℕ) (F : Finset (Sym2 (Fin n)))
    (hdiag : ∀ e ∈ F, ¬ e.IsDiag)
    (hdeg : ∀ v : Fin n, ((F.filter fun e => v ∈ e).card : ℝ) ≤ 2 * c * Real.sqrt d)
    (hdense : (n : ℝ) * Real.sqrt d / (100 * max c 1) ≤ (F.card : ℝ))
    (happ : 10 ^ 5 * (max c 1) ^ 3 * Real.sqrt d ≤ (n : ℝ)) :
    ∃ S A : Finset (Fin n) → Finset (Fin n),
      ∀ I : Finset (Fin n), (∀ u ∈ I, ∀ v ∈ I, s(u, v) ∉ F) →
        S I ⊆ I ∧ I ⊆ S I ∪ A (S I) ∧
        ((S I).card : ℝ) ≤ (n : ℝ) / (2 * Real.sqrt d) ∧
        ((S I ∪ A (S I)).card : ℝ) ≤ (1 - 1 / (10 ^ 10 * (max c 1) ^ 4)) * n ∧
        ∀ J : Finset (Fin n), S I ⊆ J → J ⊆ I → S J = S I := by
  have hM1 : (1 : ℝ) ≤ max c 1 := le_max_right _ _
  have hcM : c ≤ max c 1 := le_max_left _ _
  have hq : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  set M : ℝ := max c 1 with hMdef
  set q : ℝ := Real.sqrt d with hqdef
  have hM0 : (0 : ℝ) < M := by linarith
  have hnR : (0 : ℝ) < (n : ℝ) :=
    lt_of_lt_of_le (mul_pos (mul_pos (by norm_num) (pow_pos hM0 3)) hq) happ
  -- the forbidden-pair graph, with its adjacency decided by membership in `F`
  let instAdj : DecidableRel (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))).Adj :=
    fun x y => decidable_of_iff (s(x, y) ∈ F ∧ x ≠ y) (by simp [SimpleGraph.fromEdgeSet_adj])
  -- a degree in the graph is the number of pairs of `F` at the vertex
  have hdegcard : ∀ v : Fin n,
      (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))).degree v
        = (F.filter fun e => v ∈ e).card :=
    fun v => degree_fromEdgeSet_eq_card_incident F hdiag v
  -- the handshake identity
  have hhand : ∑ v : Fin n, ((F.filter fun e => v ∈ e).card : ℝ) = 2 * (F.card : ℝ) := by
    exact_mod_cast sum_card_incident F hdiag
  -- the average degree of the forbidden-pair graph
  have hFpos : (0 : ℝ) < (F.card : ℝ) :=
    lt_of_lt_of_le (div_pos (mul_pos hnR hq) (by linarith)) hdense
  set dG : ℝ := 2 * (F.card : ℝ) / n with hdGdef
  have hdGn : dG * (n : ℝ) = 2 * (F.card : ℝ) := by
    rw [hdGdef]; field_simp
  have hdG : (0 : ℝ) < dG := by
    rw [hdGdef]; exact div_pos (by linarith) hnR
  have hdGlow : q ≤ 50 * M * dG := by
    have h1 : (n : ℝ) * q ≤ (F.card : ℝ) * (100 * M) := (div_le_iff₀ (by linarith)).mp hdense
    nlinarith [hnR, hdGn]
  have hdGup : dG ≤ 2 * M * q := by
    have h2 : ∑ v : Fin n, ((F.filter fun e => v ∈ e).card : ℝ) ≤ (n : ℝ) * (2 * M * q) := by
      calc ∑ v : Fin n, ((F.filter fun e => v ∈ e).card : ℝ)
          ≤ ∑ _v : Fin n, 2 * M * q :=
            Finset.sum_le_sum fun v _ => (hdeg v).trans (by nlinarith [hq.le])
        _ = (n : ℝ) * (2 * M * q) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hhand] at h2
    nlinarith [hnR, hdGn]
  -- §11.2 is invoked at `c_G = 100 M²` and `δ_G = 1/(10⁴M²) = 1/(100 c_G)`
  have hcGpos : (0 : ℝ) < 100 * M ^ 2 := by positivity
  have h4pos : (0 : ℝ) < 10 ^ 4 * M ^ 2 := by positivity
  have hδGpos : (0 : ℝ) < 1 / (10 ^ 4 * M ^ 2) := by positivity
  have hδc : 1 / (10 ^ 4 * M ^ 2) ≤ 1 / (100 * (100 * M ^ 2)) := by
    rw [show (100 : ℝ) * (100 * M ^ 2) = 10 ^ 4 * M ^ 2 by ring]
  have hsumG : (∑ v, ((SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))).degree v : ℝ))
      = dG * n := by
    rw [hdGn]
    simp only [hdegcard]
    exact hhand
  have hdegG : ∀ v, ((SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))).degree v : ℝ)
      ≤ 100 * M ^ 2 * dG := by
    intro v
    rw [hdegcard v]
    refine (hdeg v).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hdGlow (by positivity : (0 : ℝ) ≤ 2 * M), hq.le, hM1]
  have hdnG : dG ≤ 1 / (10 ^ 4 * M ^ 2) * (n : ℝ) := by
    rw [show (1 : ℝ) / (10 ^ 4 * M ^ 2) * (n : ℝ) = (n : ℝ) / (10 ^ 4 * M ^ 2) by ring,
      le_div_iff₀ h4pos]
    nlinarith [mul_le_mul_of_nonneg_right hdGup (le_of_lt h4pos), happ, hq.le, hM1,
      mul_nonneg (pow_nonneg hM0.le 3) hq.le]
  obtain ⟨pick, kill, hrule⟩ :=
    exists_greedy_rule (100 * M ^ 2) dG (1 / (10 ^ 4 * M ^ 2)) hcGpos hδGpos hδc n
      (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))) hdG hdnG hsumG hdegG
  obtain ⟨S, A, hSA⟩ :=
    exists_fingerprint_of_greedy_rule (100 * M ^ 2) dG (1 / (10 ^ 4 * M ^ 2)) hcGpos hδGpos hδc n
      (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))) hdG hdnG hsumG hdegG pick kill hrule
  refine ⟨S, A, fun I hI => ?_⟩
  have hIind : (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))).IsIndepSet (I : Set (Fin n)) := by
    intro u hu v hv _ hadj
    rw [SimpleGraph.fromEdgeSet_adj] at hadj
    exact hI u (by simpa using hu) v (by simpa using hv) hadj.1
  obtain ⟨h1, h2, h3, h4, h5⟩ := hSA I hIind
  refine ⟨h1, h2, ?_, ?_, h5⟩
  · refine h3.trans ?_
    rw [div_le_div_iff₀ hdG (by positivity : (0 : ℝ) < 2 * q),
      show 2 * (1 / (10 ^ 4 * M ^ 2)) * (n : ℝ) * (2 * q) = 4 * (n : ℝ) * q / (10 ^ 4 * M ^ 2) by
        ring,
      div_le_iff₀ h4pos]
    nlinarith [mul_le_mul_of_nonneg_left hdGlow hnR.le,
      mul_le_mul_of_nonneg_left (show (200 : ℝ) * M ≤ 10 ^ 4 * M ^ 2 by nlinarith [hM1])
        (mul_pos hnR hdG).le]
  · refine h4.trans ?_
    have hMsq : (1 : ℝ) ≤ M ^ 2 := by nlinarith [hM1]
    have hM24 : M ^ 2 ≤ M ^ 4 := by nlinarith [hMsq, sq_nonneg M]
    have hle : 1 / (10 ^ 10 * M ^ 4) ≤ 1 / (10 ^ 4 * M ^ 2) :=
      one_div_le_one_div_of_le h4pos (by nlinarith [hM24, sq_nonneg M])
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) hnR.le]

/-- **A dense 3-uniform hypergraph has no large independent set**: every `I` containing no edge of
`H` satisfies `|I| ≤ n - 2d/(3n)`, where `d` is the average degree, `3|H| = d·n`.

Every edge meets `Fin n \ I`, and a set of size `k` lies in at most `k · binom(n-1,2)` triples, so
`d·n/3 = |H| ≤ (n - |I|) · n²/2`.

**This is the necessary half of §11.3's open corner.**  The held
`exists_containers_fingerprint_three_uniform` asks for containers missing a `δ` fraction of the
vertices, and a container has to hold an entire independent set, so its conclusion is possible
only if every independent set already misses `δn` vertices.  Read against this bound that is
exactly `d ≥ (3/2) δ n²`, which the dense regime `d > n²/4` satisfies for every `δ ≤ 1/6`.

So the corner's conclusion is **not** obstructed by some maximal independent set being too large,
which was the first thing to rule out.  What remains is the *assignment* problem: with a
one-vertex fingerprint budget the `n + 1` containers must be chosen so that each still misses
`δn` vertices, and that is a degree-balancing question about the maximal independent sets rather
than a counting one.  Checked by hand on two families — complete 3-uniform `H`, and all triples
inside a half-sized set — and in both a regular tournament orientation of the conflicts works.
Still open in general.

At `n = 0` both sides are `0`. -/
theorem card_le_of_forall_not_subset {n : ℕ} (H : Finset (Finset (Fin n))) (d : ℝ)
    (h3 : ∀ e ∈ H, e.card = 3) (hd : 3 * (H.card : ℝ) = d * n)
    (I : Finset (Fin n)) (hI : ∀ e ∈ H, ¬ e ⊆ I) :
    (I.card : ℝ) ≤ (n : ℝ) - 2 * d / (3 * n) := by
  sorry

/-- **The container theorem for 3-uniform hypergraphs, with fingerprints** (the fingerprint form
of Zhao, Theorem 11.3.1).  This is to Theorem 11.3.1 what `exists_containers_fingerprint` is to
`exists_containers`: the refinement that the applications actually need, and — despite being
stated as a separate theorem — **the statement the container algorithm actually produces.**  The
container assigned to an independent set `I` is not merely *some* member of a small family, but
`S I ∪ A (S I)`, a function of a fingerprint `S I ⊆ I`.  That `A` depends only on `S I` — and not
otherwise on `I` — is the whole content; it is what lets a union bound range over fingerprints.

What it claims: for every `c > 0` there is a `δ > 0` such that for every 3-uniform hypergraph `H`
on `Fin n` whose average degree `d` satisfies `δ⁻¹ ≤ d` and whose codegrees satisfy `Δ₁ ≤ c * d`
and `Δ₂ ≤ c * √d`, there are functions `S` and `A` on subsets of the vertex set such that every
independent set `I` — one containing no edge of `H` — has `S I ⊆ I ⊆ S I ∪ A (S I)`, with the
fingerprint `S I` of size at most `n / √d` and the container `S I ∪ A (S I)` missing at least a
`δ` fraction of the `n` vertices.

The degree hypotheses are token-identical to those of `exists_containers_three_uniform`, which is
proved from this statement below — the fingerprint budget `n / √d` is exactly the index of the
binomial sum there.

**This statement inherits §11.3's open design question, and is strictly stronger than
`exists_containers_three_uniform` in exactly the regime where that question bites.  Read this
before claiming it.**

Two separate things are true and must not be confused:

* *The fingerprint budget never collapses.*  `3|H| = d·n` with all edges of card `3` gives
  `|H| ≤ C(n,3)`, so `d < n²/2` and `n/√d > √2`.  A one-vertex fingerprint always fits.  This is
  why §11.3 needs no analogue of §11.2's `d ≤ 2δn` proviso, and it is **proved**.
* *Budget `≥ 1` is not budget `≥ 2`.*  For `n²/4 < d` the budget is in `[√2, 2)`, so a fingerprint
  holds exactly one vertex.  The `n+1` fingerprints of size `≤ 1` then *exactly exhaust* the
  parent's count budget `∑_{i<2} C(n,i)`, with no slack — and this statement additionally demands
  that every independent `I` be covered by a container indexed by one of `I`'s own vertices, with
  `A` a function of that vertex alone.  The parent demands neither.  So in that corner this
  obligation is **strictly stronger** than the theorem it was cut from, and `δ` is no lever, since
  `n/√d` is `δ`-independent.

**Where the corner comes from: the subroutine's own proviso failing.**  The source's algorithm
applies the *graph* container theorem to the accumulated forbidden-pair graph `G`.
`exists_containers` at parameter `c_G` produces `δ_G = 1/(100 · max c_G 1)` and demands
`d_G ≤ 2 δ_G n = n/(50 · max c_G 1)`.  At termination `d_G = 2e(G)/n = Ω(√d)`, so applicability
requires `d = O(n²/c_G²)` — while the only a priori bound is `d < n²/2`.  That leaves a real
constant-factor window of `d = Θ(n²)` in which **the graph container theorem cannot be applied to
`G` at all**, because `G`'s own average degree violates the very proviso §11.2 had to acquire at
`1e4659a`.  The same proviso, biting one chapter later.

At complete 3-uniform `H` the corner is satisfiable — a regular tournament orientation works, with
containers of size `(n+1)/2` — but that is **one family checked by hand, not a proof**, and no
refutation is known either.  Treat the corner as open. -/
theorem exists_containers_fingerprint_three_uniform (c : ℝ) (hc : 0 < c) :
    ∃ δ > 0, ∀ (n : ℕ) (H : Finset (Finset (Fin n))) (d : ℝ),
      (∀ e ∈ H, e.card = 3) → δ⁻¹ ≤ d → 3 * (H.card : ℝ) = d * n →
      (maxCodegree 1 H : ℝ) ≤ c * d → (maxCodegree 2 H : ℝ) ≤ c * Real.sqrt d →
      ∃ S A : Finset (Fin n) → Finset (Fin n),
        ∀ I : Finset (Fin n), (∀ e ∈ H, ¬ e ⊆ I) →
          S I ⊆ I ∧ I ⊆ S I ∪ A (S I) ∧
          ((S I).card : ℝ) ≤ (n : ℝ) / Real.sqrt d ∧
          ((S I ∪ A (S I)).card : ℝ) ≤ (1 - δ) * n := by
  sorry

/-- **The container theorem for 3-uniform hypergraphs** (Zhao, Theorem 11.3.1; Balogh–Morris–
Samotij and Saxton–Thomason, independently, 2015).  The degree conditions are on `Δ₁ ≤ cd` and
`Δ₂ ≤ c√d`, and the fingerprints now have size `≤ v(H)/√d`.

The source's proof calls the graph container algorithm as a subroutine, so `exists_containers` is
a genuine dependency rather than merely an analogue. -/
theorem exists_containers_three_uniform (c : ℝ) (hc : 0 < c) :
    ∃ δ > 0, ∀ (n : ℕ) (H : Finset (Finset (Fin n))) (d : ℝ),
      (∀ e ∈ H, e.card = 3) → δ⁻¹ ≤ d → 3 * (H.card : ℝ) = d * n →
      (maxCodegree 1 H : ℝ) ≤ c * d → (maxCodegree 2 H : ℝ) ≤ c * Real.sqrt d →
      ∃ 𝒞 : Finset (Finset (Fin n)),
        (𝒞.card : ℝ) ≤ ∑ i ∈ range (⌊(n : ℝ) / Real.sqrt d⌋₊ + 1), (n.choose i : ℝ) ∧
        (∀ I : Finset (Fin n), (∀ e ∈ H, ¬ e ⊆ I) → ∃ C ∈ 𝒞, I ⊆ C) ∧
        (∀ C ∈ 𝒞, (C.card : ℝ) ≤ (1 - δ) * n) := by
  obtain ⟨δ, hδ, hfp⟩ := exists_containers_fingerprint_three_uniform c hc
  refine ⟨δ, hδ, fun n H d hcard hd hsum h1 h2 => ?_⟩
  obtain ⟨S, A, hSA⟩ := hfp n H d hcard hd hsum h1 h2
  -- The fingerprints that are both small and have a small container.  The second condition is
  -- needed because the fingerprint theorem says nothing about a `T` that is not some `S I`.
  set F : Finset (Finset (Fin n)) :=
    univ.powerset.filter fun T : Finset (Fin n) =>
      (T.card : ℝ) ≤ (n : ℝ) / Real.sqrt d ∧ ((T ∪ A T).card : ℝ) ≤ (1 - δ) * n with hF
  refine ⟨F.image fun T => T ∪ A T, ?_, ?_, ?_⟩
  · have hsub : F ⊆ (range (⌊(n : ℝ) / Real.sqrt d⌋₊ + 1)).biUnion
        fun i => powersetCard i (univ : Finset (Fin n)) := by
      intro T hT
      rw [hF, mem_filter] at hT
      exact mem_biUnion.mpr ⟨T.card, mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hT.2.1)),
        mem_powersetCard.mpr ⟨subset_univ _, rfl⟩⟩
    have hcount : ((range (⌊(n : ℝ) / Real.sqrt d⌋₊ + 1)).biUnion
        fun i => powersetCard i (univ : Finset (Fin n))).card
        = ∑ i ∈ range (⌊(n : ℝ) / Real.sqrt d⌋₊ + 1), n.choose i := by
      rw [card_biUnion ((pairwise_disjoint_powersetCard (univ : Finset (Fin n))).set_pairwise _)]
      simp
    have hnat : (F.image fun T => T ∪ A T).card
        ≤ ∑ i ∈ range (⌊(n : ℝ) / Real.sqrt d⌋₊ + 1), n.choose i :=
      card_image_le.trans (hcount ▸ card_le_card hsub)
    calc ((F.image fun T => T ∪ A T).card : ℝ)
        ≤ ((∑ i ∈ range (⌊(n : ℝ) / Real.sqrt d⌋₊ + 1), n.choose i : ℕ) : ℝ) :=
          Nat.cast_le.mpr hnat
      _ = ∑ i ∈ range (⌊(n : ℝ) / Real.sqrt d⌋₊ + 1), (n.choose i : ℝ) := by push_cast; ring
  · intro I hI
    obtain ⟨-, hcov, hsmall, hcont⟩ := hSA I hI
    exact ⟨S I ∪ A (S I), mem_image_of_mem _
      (mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), hsmall, hcont⟩), hcov⟩
  · intro C hC
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hC
    exact (mem_filter.mp hT).2.2

/-! ### 11.1 Containers for triangle-free graphs -/

/-- **Triangle supersaturation**, the input the iteration of Remark 11.2.2 needs.  A graph on
`n` vertices with at least `(1/4 + ε) n²` edges — just past Mantel's bound — does not merely
contain a triangle: it contains at least `c n³` of them, for a `c` depending only on `ε`.

Triangles are counted as ordered triples of distinct vertices, so the count is six times the
number of triangles and that factor is absorbed into `c`.  The hypothesis that no pair of `F` is
diagonal says `F` really is the edge set of a simple graph, and it is what makes the statement
hold at every `n` rather than only for `n` large: a diagonal-free set of pairs on at most two
vertices cannot reach `(1/4 + ε) n²` at all, so the small cases are vacuous instead of false. -/
theorem exists_triangle_supersaturation (ε : ℝ) (hε : 0 < ε) :
    ∃ c > 0, ∀ (n : ℕ) (F : Finset (Sym2 (Fin n))), (∀ e ∈ F, ¬ e.IsDiag) →
      (1 / 4 + ε) * (n : ℝ) ^ 2 ≤ (F.card : ℝ) →
      c * (n : ℝ) ^ 3 ≤ ((univ.filter fun t : Fin n × Fin n × Fin n =>
        t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧
          triangleEdges t.1 t.2.1 t.2.2 ⊆ F).card : ℝ) := by
  refine ⟨SimpleGraph.triangleRemovalBound ε, SimpleGraph.triangleRemovalBound_pos hε, ?_⟩
  intro n F hdiag hcard
  let instAdj : DecidableRel (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))).Adj :=
    fun x y => decidable_of_iff (s(x, y) ∈ F ∧ x ≠ y) (by simp [SimpleGraph.fromEdgeSet_adj])
  have hadj : ∀ x y : Fin n,
      (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))).Adj x y ↔ s(x, y) ∈ F ∧ x ≠ y := by
    intro x y; simp [SimpleGraph.fromEdgeSet_adj]
  have hEF : ∀ inst : Fintype (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))).edgeSet,
      @SimpleGraph.edgeFinset _ _ inst = F := by
    intro inst
    ext e
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_fromEdgeSet]
    simp only [Set.mem_sdiff, Finset.mem_coe, Sym2.mem_diagSet]
    exact ⟨fun h => h.1, fun h => ⟨h, hdiag e h⟩⟩
  have hfar : (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))).FarFromTriangleFree ε := by
    rw [SimpleGraph.farFromTriangleFree_iff]
    intro H _ _ hH3
    have hm : H.edgeFinset.card ≤
        ((Fintype.card (Fin n)) ^ 2 - ((Fintype.card (Fin n)) % 2) ^ 2) * (2 - 1) / (2 * 2)
          + ((Fintype.card (Fin n)) % 2).choose 2 :=
      SimpleGraph.CliqueFree.card_edgeFinset_le (r := 2) hH3
    have hchoose : ((Fintype.card (Fin n)) % 2).choose 2 = 0 :=
      Nat.choose_eq_zero_of_lt (Nat.mod_lt _ (by norm_num))
    have hle : ((Fintype.card (Fin n)) % 2) ^ 2 ≤ (Fintype.card (Fin n)) ^ 2 :=
      Nat.pow_le_pow_left (Nat.mod_le _ _) 2
    rw [hchoose] at hm
    have hm4 : 4 * H.edgeFinset.card ≤ (Fintype.card (Fin n)) ^ 2 := by omega
    rw [hEF]
    have hH : (H.edgeFinset.card : ℝ) ≤ (n : ℝ) ^ 2 / 4 := by
      have h4 := (Nat.cast_le (α := ℝ)).2 hm4
      simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h4
      linarith
    have hcard2 : Fintype.card (Fin n) ^ 2 = n ^ 2 := by simp
    rw [hcard2]
    push_cast
    linarith
  have hrem := hfar.le_card_cliqueFinset
  have hsurj : ((SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))).cliqueFinset 3).card ≤
      (univ.filter fun t : Fin n × Fin n × Fin n =>
        t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧
          triangleEdges t.1 t.2.1 t.2.2 ⊆ F).card := by
    refine Finset.card_le_card_of_surjOn
      (fun t : Fin n × Fin n × Fin n => ({t.1, t.2.1, t.2.2} : Finset (Fin n))) ?_
    intro s hs
    rw [Finset.mem_coe, SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.is3Clique_iff] at hs
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := hs
    rw [hadj] at hab hac hbc
    refine ⟨(a, b, c), ?_, rfl⟩
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and]
    refine ⟨hab.2, hac.2, hbc.2, ?_⟩
    intro e he
    simp only [triangleEdges, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact hab.1
    · exact hac.1
    · exact hbc.1
  calc SimpleGraph.triangleRemovalBound ε * (n : ℝ) ^ 3
      = SimpleGraph.triangleRemovalBound ε * (Fintype.card (Fin n) : ℝ) ^ 3 := by
        simp
    _ ≤ (((SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))).cliqueFinset 3).card : ℝ) := hrem
    _ ≤ _ := by exact_mod_cast hsurj

set_option maxHeartbeats 1200000 in
/-- **One step of the container iteration for triangle-free graphs.**  A set `F` of pairs from
`[n]` spanning at least `c n³` ordered triangles admits a small family of subsets of `F`, each a
definite fraction smaller than `F`, covering between them every triangle-free graph inside `F`.

This is `exists_containers_three_uniform` applied to the 3-uniform hypergraph whose vertices are
the pairs in `F` and whose edges are the triangles spanned by `F`; its independent sets are
exactly the triangle-free graphs contained in `F`.  The triangle count is what supplies the
average degree `d`, of order `n` once the count is of order `n³`, and the codegree hypotheses
hold because one pair lies in at most `n` triangles and two distinct pairs in at most one. -/
theorem exists_shrunken_containers_of_many_triangles (c : ℝ) (hc : 0 < c) :
    ∃ δ C : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < C ∧ ∀ (n : ℕ) (F : Finset (Sym2 (Fin n))),
      c * (n : ℝ) ^ 3 ≤ ((univ.filter fun t : Fin n × Fin n × Fin n =>
        t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧
          triangleEdges t.1 t.2.1 t.2.2 ⊆ F).card : ℝ) →
      ∃ 𝒟 : Finset (Finset (Sym2 (Fin n))),
        (𝒟.card : ℝ) ≤ (n : ℝ) ^ (C * (n : ℝ) ^ ((3 : ℝ) / 2)) ∧
        (∀ D ∈ 𝒟, D ⊆ F ∧ (D.card : ℝ) ≤ (1 - δ) * (F.card : ℝ)) ∧
        (∀ G : Finset (Sym2 (Fin n)), IsTriangleFreeEdgeSet G → G ⊆ F → ∃ D ∈ 𝒟, G ⊆ D) := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hc3 : (0:ℝ) < c / 3 := by linarith
  have hsc3 : 0 < Real.sqrt (c / 3) := Real.sqrt_pos.mpr hc3
  have h108 : (0:ℝ) < 108 / c := div_pos (by norm_num) hc
  have h64 : (0:ℝ) < 64 / Real.sqrt (c / 3) := div_pos (by norm_num) hsc3
  -- The degree constant handed to Theorem 11.3.1.  Once the triangle count forces the average
  -- degree `d ≥ c n / 9`, the two codegree bounds `Δ₁ ≤ 12 n` and `Δ₂ ≤ 64` proved below read
  -- `Δ₁ ≤ (108 / c) d` and `Δ₂ ≤ (64 / √(c/3)) √d`.
  obtain ⟨δ₀, hδ₀, hcont⟩ :=
    exists_containers_three_uniform (108 / c + 64 / Real.sqrt (c / 3) + 1) (by linarith)
  -- Above `n₀` the average degree clears both `δ₀⁻¹` and `1`, so Theorem 11.3.1 applies; below it
  -- the theorem is met by hand, and `δ` is cut down far enough for the crude family to qualify.
  set n₀ : ℕ := max 3 (max ⌈9 / (c * δ₀)⌉₊ ⌈9 / c⌉₊) with hn₀def
  have hn₀3 : 3 ≤ n₀ := le_max_left _ _
  have hn₀a : (9 / (c * δ₀) : ℝ) ≤ (n₀ : ℝ) := by
    refine (Nat.le_ceil _).trans ?_
    exact_mod_cast (le_max_left _ _).trans (le_max_right 3 _)
  have hn₀b : (9 / c : ℝ) ≤ (n₀ : ℝ) := by
    refine (Nat.le_ceil _).trans ?_
    exact_mod_cast (le_max_right _ _).trans (le_max_right 3 _)
  have hn₀pos : (0:ℝ) < (n₀ : ℝ) := by positivity
  clear_value n₀
  have hsmallpos : (0:ℝ) < 1 / ((n₀ : ℝ) ^ 2 + 1) := by positivity
  refine ⟨min δ₀ (1 / ((n₀ : ℝ) ^ 2 + 1)), 6 / Real.sqrt c + 3 + (n₀ : ℝ),
    lt_min hδ₀ hsmallpos, ?_, by positivity, ?_⟩
  · refine lt_of_le_of_lt (min_le_right _ _) ?_
    rw [div_lt_one (by positivity)]
    nlinarith [hn₀3, hn₀pos]
  intro n F hT
  set δ : ℝ := min δ₀ (1 / ((n₀ : ℝ) ^ 2 + 1)) with hδdef
  have hδpos : 0 < δ := lt_min hδ₀ hsmallpos
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  set C : ℝ := 6 / Real.sqrt c + 3 + (n₀ : ℝ) with hCdef
  set Tset : Finset (Fin n × Fin n × Fin n) :=
    univ.filter (fun t : Fin n × Fin n × Fin n =>
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧
        triangleEdges t.1 t.2.1 t.2.2 ⊆ F) with hTsetdef
  have hTcard : c * (n : ℝ) ^ 3 ≤ (Tset.card : ℝ) := hT
  have hTmem : ∀ t ∈ Tset, t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧
      triangleEdges t.1 t.2.1 t.2.2 ⊆ F := by
    intro t ht
    rw [hTsetdef, mem_filter] at ht
    exact ht.2
  clear_value Tset
  -- `n = 0` is not excluded by the hypothesis, since `c * 0 ^ 3 ≤ 0` holds; `{∅}` witnesses it,
  -- `(0 : ℝ) ^ (C * 0 ^ (3 / 2))` being `0 ^ (0 : ℝ) = 1`.
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · have hFe : ∀ e : Sym2 (Fin 0), False := fun e => Sym2.ind (fun a _ => a.elim0) e
    have hF : F = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun e _ => hFe e
    refine ⟨{∅}, ?_, ?_, ?_⟩
    · simp [Real.zero_rpow]
    · intro D hD
      rw [mem_singleton] at hD
      subst hD
      simp [hF]
    · intro G _ hGF
      refine ⟨∅, mem_singleton_self _, ?_⟩
      rw [hF] at hGF
      exact hGF
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  have hTpos : 0 < Tset.card := by
    have hnpos : (0:ℝ) < (n:ℝ) := by linarith
    have h1 : (0:ℝ) < c * (n:ℝ)^3 := mul_pos hc (pow_pos hnpos 3)
    have : (0:ℝ) < (Tset.card : ℝ) := lt_of_lt_of_le h1 hTcard
    exact_mod_cast this
  -- For `n ≥ 1` the count is positive, so `F` really does span a triangle: hence `3 ≤ n` and
  -- `3 ≤ |F|`, and `n ∈ {1, 2}` is vacuous.
  obtain ⟨t₀, ht₀⟩ : Tset.Nonempty := Finset.card_pos.mp hTpos
  obtain ⟨hab, haz, hbz, hsub0⟩ := hTmem t₀ ht₀
  have hcard3 : ∀ x y z : Fin n, x ≠ y → x ≠ z → y ≠ z →
      (triangleEdges x y z).card = 3 := by
    intro x y z hxy hxz hyz
    rw [triangleEdges, card_insert_of_notMem (by simp; tauto),
      card_insert_of_notMem (by simp; tauto), card_singleton]
  have hn3 : 3 ≤ n := by
    have hv : ({t₀.1, t₀.2.1, t₀.2.2} : Finset (Fin n)).card = 3 := by
      rw [card_insert_of_notMem (by simp [hab, haz]),
        card_insert_of_notMem (by simp [hbz]), card_singleton]
    have := Finset.card_le_univ ({t₀.1, t₀.2.1, t₀.2.2} : Finset (Fin n))
    simpa [hv] using this
  have hN3 : 3 ≤ F.card := by
    have := Finset.card_le_card hsub0
    rwa [hcard3 _ _ _ hab haz hbz] at this
  have htri : ∀ (e : Sym2 (Fin n)) (p q r : Fin n),
      e ∈ triangleEdges p q r ↔ (e = s(p, q) ∨ e = s(p, r) ∨ e = s(q, r)) := by
    intro e p q r
    rw [triangleEdges]
    simp only [mem_insert, mem_singleton]
  have hpair : ∀ x y u v : Fin n, s(x, y) = s(u, v) → (x = u ∨ x = v) ∧ (y = u ∨ y = v) := by
    intro x y u v h
    rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨Or.inl rfl, Or.inr rfl⟩
    · exact ⟨Or.inr rfl, Or.inl rfl⟩
  have hend : ∀ x y p q r : Fin n, s(x, y) ∈ triangleEdges p q r →
      (x = p ∨ x = q ∨ x = r) ∧ (y = p ∨ y = q ∨ y = r) := by
    intro x y p q r h
    rcases (htri _ _ _ _).mp h with h' | h' | h' <;>
      [exact (fun h => ⟨by tauto, by tauto⟩) (hpair x y p q h');
       exact (fun h => ⟨by tauto, by tauto⟩) (hpair x y p r h');
       exact (fun h => ⟨by tauto, by tauto⟩) (hpair x y q r h')]
  have hSym2 : ∀ z : Sym2 (Fin n), ∃ x y : Fin n, z = s(x, y) :=
    fun z => Sym2.ind (fun x y => ⟨x, y, rfl⟩) z
  have hle3 : ∀ x y z : Fin n, ({x, y, z} : Finset (Fin n)).card ≤ 3 := by
    intro x y z
    calc ({x, y, z} : Finset (Fin n)).card ≤ ({y, z} : Finset (Fin n)).card + 1 :=
          card_insert_le _ _
      _ ≤ (({z} : Finset (Fin n)).card + 1) + 1 := by gcongr; exact card_insert_le _ _
      _ = 3 := by simp
  have hle4 : ∀ w x y z : Fin n, ({w, x, y, z} : Finset (Fin n)).card ≤ 4 := by
    intro w x y z
    calc ({w, x, y, z} : Finset (Fin n)).card ≤ ({x, y, z} : Finset (Fin n)).card + 1 :=
          card_insert_le _ _
      _ ≤ 3 + 1 := by gcongr; exact hle3 x y z
      _ = 4 := by norm_num
  have hδsmall : δ ≤ 1 / ((n₀:ℝ)^2 + 1) := by rw [hδdef]; exact min_le_right _ _
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast le_trans (by norm_num) hn3
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  have hFn2 : (F.card : ℝ) ≤ (n:ℝ) * (n:ℝ) := by
    have h0 : F.card ≤ n * n := by
      refine le_trans (Finset.card_le_univ F) ?_
      have h := Fintype.card_le_of_surjective
        (Function.uncurry (Sym2.mk (α := Fin n))) Sym2.mk_surjective
      simpa [Fintype.card_prod] using h
    exact_mod_cast h0
  have h6c : (0:ℝ) < 6 / Real.sqrt c := by positivity
  by_cases hbig : n₀ ≤ n
  · set N : ℕ := F.card with hNdef
    have hNpos : 0 < N := by omega
    -- Theorem 11.3.1 is stated for hypergraphs on `Fin N`, so the pairs of `F` are transported
    -- there by an arbitrary bijection: `ψ` enumerates `F`, `push` carries a subset of `F` to its
    -- index set and `pull` carries it back, and the two are mutually inverse on subsets of `F`.
    obtain ⟨ψ, hψF, hψinj, hψsurj⟩ : ∃ ψ : Fin N → Sym2 (Fin n),
        (∀ i, ψ i ∈ F) ∧ Function.Injective ψ ∧ ∀ p ∈ F, ∃ i, ψ i = p := by
      refine ⟨fun i => ((F.equivFin.symm i : {x // x ∈ F}) : Sym2 (Fin n)),
        fun i => (F.equivFin.symm i).2, ?_, ?_⟩
      · intro i j h
        exact F.equivFin.symm.injective (Subtype.coe_injective h)
      · intro p hp
        refine ⟨F.equivFin ⟨p, hp⟩, ?_⟩
        show ((F.equivFin.symm (F.equivFin ⟨p, hp⟩) : {x // x ∈ F}) : Sym2 (Fin n)) = p
        rw [Equiv.symm_apply_apply]
    clear_value N
    set pull : Finset (Fin N) → Finset (Sym2 (Fin n)) := fun A => A.image ψ with hpulldef
    set push : Finset (Sym2 (Fin n)) → Finset (Fin N) :=
      fun D => univ.filter (fun i => ψ i ∈ D) with hpushdef
    have hmempush : ∀ (D : Finset (Sym2 (Fin n))) (i : Fin N), i ∈ push D ↔ ψ i ∈ D := by
      intro D i; rw [hpushdef]; simp
    have hmempull : ∀ (A : Finset (Fin N)) (p : Sym2 (Fin n)),
        p ∈ pull A ↔ ∃ i ∈ A, ψ i = p := by
      intro A p; rw [hpulldef]; simp
    have hpullF : ∀ A : Finset (Fin N), pull A ⊆ F := by
      intro A p hp
      obtain ⟨i, -, rfl⟩ := (hmempull A p).mp hp
      exact hψF i
    have hpullpush : ∀ D : Finset (Sym2 (Fin n)), D ⊆ F → pull (push D) = D := by
      intro D hD
      ext p
      rw [hmempull]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact (hmempush D i).mp hi
      · intro hp
        obtain ⟨i, rfl⟩ := hψsurj p (hD hp)
        exact ⟨i, (hmempush D i).mpr hp, rfl⟩
    have hcardpull : ∀ A : Finset (Fin N), (pull A).card = A.card := by
      intro A; rw [hpulldef]; exact card_image_of_injective A hψinj
    have hcardpush : ∀ D : Finset (Sym2 (Fin n)), D ⊆ F → (push D).card = D.card := by
      intro D hD
      rw [← hcardpull (push D), hpullpush D hD]
    have hpushmono : ∀ D E : Finset (Sym2 (Fin n)), D ⊆ E → push D ⊆ push E := by
      intro D E hDE i hi
      exact (hmempush E i).mpr (hDE ((hmempush D i).mp hi))
    have hpullmono : ∀ A B : Finset (Fin N), A ⊆ B → pull A ⊆ pull B := by
      intro A B hAB p hp
      obtain ⟨i, hi, rfl⟩ := (hmempull A p).mp hp
      exact (hmempull B _).mpr ⟨i, hAB hi, rfl⟩
    clear_value pull push
    set g : Fin n × Fin n × Fin n → Finset (Fin N) :=
      fun t => push (triangleEdges t.1 t.2.1 t.2.2) with hgdef
    set H : Finset (Finset (Fin N)) := Tset.image g with hHdef
    have hgapp : ∀ t : Fin n × Fin n × Fin n, g t = push (triangleEdges t.1 t.2.1 t.2.2) :=
      fun _ => rfl
    clear_value g H
    -- At most `27` ordered triples give the same hyperedge: an edge set determines the triangle's
    -- three vertices, and each coordinate is one of them.  So the hypergraph has at least
    -- `|Tset| / 27` edges, which is what turns `c n³` triangles into `d ≥ c n / 9`.
    have hfiber : Tset.card ≤ 27 * H.card := by
      rw [hHdef]
      refine Finset.card_le_mul_card_image Tset 27 ?_
      intro A hA
      obtain ⟨t₁, ht₁, hgt₁⟩ := mem_image.mp hA
      obtain ⟨-, -, -, h4⟩ := hTmem t₁ ht₁
      have hsubset : (Tset.filter (fun t => g t = A)) ⊆
          ({t₁.1, t₁.2.1, t₁.2.2} : Finset (Fin n)) ×ˢ
            ((({t₁.1, t₁.2.1, t₁.2.2} : Finset (Fin n))) ×ˢ
              (({t₁.1, t₁.2.1, t₁.2.2} : Finset (Fin n)))) := by
        intro t ht
        rw [mem_filter] at ht
        obtain ⟨htT, htA⟩ := ht
        obtain ⟨-, -, -, hsubt⟩ := hTmem t htT
        have heq : triangleEdges t.1 t.2.1 t.2.2 = triangleEdges t₁.1 t₁.2.1 t₁.2.2 := by
          rw [← hpullpush _ hsubt, ← hpullpush _ h4, ← hgapp, ← hgapp, htA, hgt₁]
        have e1 : s(t.1, t.2.1) ∈ triangleEdges t₁.1 t₁.2.1 t₁.2.2 := by
          rw [← heq, htri]; exact Or.inl rfl
        have e2 : s(t.1, t.2.2) ∈ triangleEdges t₁.1 t₁.2.1 t₁.2.2 := by
          rw [← heq, htri]; exact Or.inr (Or.inl rfl)
        obtain ⟨ha, hb⟩ := hend _ _ _ _ _ e1
        obtain ⟨-, hz⟩ := hend _ _ _ _ _ e2
        simp only [mem_product, mem_insert, mem_singleton]
        exact ⟨ha, hb, hz⟩
      refine le_trans (Finset.card_le_card hsubset) ?_
      rw [card_product, card_product]
      have h3 := hle3 t₁.1 t₁.2.1 t₁.2.2
      calc ({t₁.1, t₁.2.1, t₁.2.2} : Finset (Fin n)).card *
            (({t₁.1, t₁.2.1, t₁.2.2} : Finset (Fin n)).card *
              ({t₁.1, t₁.2.1, t₁.2.2} : Finset (Fin n)).card)
          ≤ 3 * (3 * 3) := Nat.mul_le_mul h3 (Nat.mul_le_mul h3 h3)
        _ = 27 := by norm_num
    have hHpos : 0 < H.card := by
      rcases Nat.eq_zero_or_pos H.card with h | h
      · rw [h] at hfiber; omega
      · exact h
    have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
    set d : ℝ := 3 * (H.card : ℝ) / (N : ℝ) with hddef
    have hdeq : 3 * (H.card : ℝ) = d * (N:ℝ) := by
      rw [hddef]; field_simp
    have hdlb0 : c * (n:ℝ) / 9 ≤ d := by
      rw [hddef, div_le_div_iff₀ (by norm_num) hNR]
      have h1 : (Tset.card : ℝ) ≤ 27 * (H.card : ℝ) := by exact_mod_cast hfiber
      have h2 : c * (n:ℝ) * (N:ℝ) ≤ c * (n:ℝ) * ((n:ℝ) * (n:ℝ)) :=
        mul_le_mul_of_nonneg_left hFn2 (by positivity)
      nlinarith [hTcard]
    clear_value d
    have hdlb : c * (n:ℝ) / 9 ≤ d := hdlb0
    have hdpos : 0 < d := lt_of_lt_of_le (by positivity) hdlb
    have hnn₀ : (n₀:ℝ) ≤ (n:ℝ) := by exact_mod_cast hbig
    have hd1 : (1:ℝ) ≤ d := by
      refine le_trans ?_ hdlb
      have h9 : (9:ℝ) / c ≤ (n:ℝ) := le_trans hn₀b hnn₀
      rw [div_le_iff₀ hc] at h9
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 9)]
      linarith
    have hdinv : δ₀⁻¹ ≤ d := by
      refine le_trans ?_ hdlb
      have h9 : (9:ℝ) / (c * δ₀) ≤ (n:ℝ) := le_trans hn₀a hnn₀
      rw [div_le_iff₀ (mul_pos hc hδ₀)] at h9
      rw [inv_eq_one_div, div_le_div_iff₀ hδ₀ (by norm_num : (0:ℝ) < 9)]
      nlinarith
    have hH3 : ∀ e ∈ H, e.card = 3 := by
      intro e he
      rw [hHdef, mem_image] at he
      obtain ⟨t, ht, rfl⟩ := he
      obtain ⟨h1, h2, h3, h4⟩ := hTmem t ht
      rw [hgapp, hcardpush _ h4, hcard3 _ _ _ h1 h2 h3]
    have hS2 : ∀ x y : Fin n, ({x, y} : Finset (Fin n)).card ≤ 2 := by
      intro x y
      calc ({x, y} : Finset (Fin n)).card ≤ ({y} : Finset (Fin n)).card + 1 := card_insert_le _ _
        _ = 2 := by simp
    have hU : (univ : Finset (Fin n)).card = n := by simp
    -- `Δ₁ ≤ 12 n`: an ordered triple spanning a given pair has two of its three coordinates
    -- pinned to that pair's endpoints, leaving one free.
    have hΔ1 : maxCodegree 1 H ≤ 12 * n := by
      simp only [maxCodegree]
      refine Finset.sup_le ?_
      intro A hA
      rw [mem_filter] at hA
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hA.2
      obtain ⟨x, y, hxy⟩ := hSym2 (ψ i)
      have hsub : H.filter (fun e => {i} ⊆ e) ⊆
          (Tset.filter (fun t => ψ i ∈ triangleEdges t.1 t.2.1 t.2.2)).image g := by
        intro e he
        rw [mem_filter, hHdef, mem_image] at he
        obtain ⟨⟨t, ht, rfl⟩, hi⟩ := he
        refine mem_image_of_mem g (mem_filter.mpr ⟨ht, ?_⟩)
        have hig : i ∈ g t := hi (mem_singleton_self i)
        rw [hgapp] at hig
        exact (hmempush _ i).mp hig
      refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le ?_)
      have hsub2 : Tset.filter (fun t => ψ i ∈ triangleEdges t.1 t.2.1 t.2.2) ⊆
          (({x, y} : Finset (Fin n)) ×ˢ (({x, y} : Finset (Fin n)) ×ˢ (univ : Finset (Fin n)))) ∪
          ((({x, y} : Finset (Fin n)) ×ˢ ((univ : Finset (Fin n)) ×ˢ ({x, y} : Finset (Fin n)))) ∪
            ((univ : Finset (Fin n)) ×ˢ
              (({x, y} : Finset (Fin n)) ×ˢ ({x, y} : Finset (Fin n))))) := by
        intro t ht
        rw [mem_filter] at ht
        obtain ⟨-, hmem⟩ := ht
        rw [hxy, htri] at hmem
        have hVxy : ∀ w : Fin n, (w = x ∨ w = y) → w ∈ ({x, y} : Finset (Fin n)) := by
          intro w hw
          rcases hw with rfl | rfl <;> simp
        rcases hmem with h | h | h
        · obtain ⟨h1, h2⟩ := hpair t.1 t.2.1 x y h.symm
          exact mem_union_left _
            (mem_product.mpr ⟨hVxy _ h1, mem_product.mpr ⟨hVxy _ h2, mem_univ _⟩⟩)
        · obtain ⟨h1, h2⟩ := hpair t.1 t.2.2 x y h.symm
          exact mem_union_right _ (mem_union_left _
            (mem_product.mpr ⟨hVxy _ h1, mem_product.mpr ⟨mem_univ _, hVxy _ h2⟩⟩))
        · obtain ⟨h1, h2⟩ := hpair t.2.1 t.2.2 x y h.symm
          exact mem_union_right _ (mem_union_right _
            (mem_product.mpr ⟨mem_univ _, mem_product.mpr ⟨hVxy _ h1, hVxy _ h2⟩⟩))
      refine le_trans (Finset.card_le_card hsub2) ?_
      have hB1 : ((({x, y} : Finset (Fin n)) ×ˢ
          (({x, y} : Finset (Fin n)) ×ˢ (univ : Finset (Fin n))))).card ≤ 4 * n := by
        rw [card_product, card_product, hU]
        calc ({x, y} : Finset (Fin n)).card * (({x, y} : Finset (Fin n)).card * n)
            ≤ 2 * (2 * n) := Nat.mul_le_mul (hS2 x y) (Nat.mul_le_mul (hS2 x y) le_rfl)
          _ = 4 * n := by ring
      have hB2 : ((({x, y} : Finset (Fin n)) ×ˢ
          ((univ : Finset (Fin n)) ×ˢ ({x, y} : Finset (Fin n))))).card ≤ 4 * n := by
        rw [card_product, card_product, hU]
        calc ({x, y} : Finset (Fin n)).card * (n * ({x, y} : Finset (Fin n)).card)
            ≤ 2 * (n * 2) := Nat.mul_le_mul (hS2 x y) (Nat.mul_le_mul le_rfl (hS2 x y))
          _ = 4 * n := by ring
      have hB3 : (((univ : Finset (Fin n)) ×ˢ
          (({x, y} : Finset (Fin n)) ×ˢ ({x, y} : Finset (Fin n))))).card ≤ 4 * n := by
        rw [card_product, card_product, hU]
        calc n * (({x, y} : Finset (Fin n)).card * ({x, y} : Finset (Fin n)).card)
            ≤ n * (2 * 2) := Nat.mul_le_mul le_rfl (Nat.mul_le_mul (hS2 x y) (hS2 x y))
          _ = 4 * n := by ring
      have hu1 := Finset.card_union_le
        (((({x, y} : Finset (Fin n)) ×ˢ
          (({x, y} : Finset (Fin n)) ×ˢ (univ : Finset (Fin n))))))
        (((({x, y} : Finset (Fin n)) ×ˢ
          ((univ : Finset (Fin n)) ×ˢ ({x, y} : Finset (Fin n))))) ∪
            (((univ : Finset (Fin n)) ×ˢ
              (({x, y} : Finset (Fin n)) ×ˢ ({x, y} : Finset (Fin n))))))
      have hu2 := Finset.card_union_le
        (((({x, y} : Finset (Fin n)) ×ˢ
          ((univ : Finset (Fin n)) ×ˢ ({x, y} : Finset (Fin n))))))
        (((univ : Finset (Fin n)) ×ˢ
          (({x, y} : Finset (Fin n)) ×ˢ ({x, y} : Finset (Fin n)))))
      omega
    -- `Δ₂ ≤ 64`: two *distinct* pairs of a triangle are two distinct edges of it, so between them
    -- they cover all three vertices and every coordinate is one of their four endpoints.
    have hΔ2 : maxCodegree 2 H ≤ 64 := by
      simp only [maxCodegree]
      refine Finset.sup_le ?_
      intro A hA
      rw [mem_filter] at hA
      obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hA.2
      obtain ⟨x, y, hxy⟩ := hSym2 (ψ i)
      obtain ⟨u, v, huv⟩ := hSym2 (ψ j)
      have hxyuv : s(x, y) ≠ s(u, v) := by
        rw [← hxy, ← huv]
        exact fun h => hij (hψinj h)
      have hsub : H.filter (fun e => {i, j} ⊆ e) ⊆
          (Tset.filter (fun t => ψ i ∈ triangleEdges t.1 t.2.1 t.2.2 ∧
            ψ j ∈ triangleEdges t.1 t.2.1 t.2.2)).image g := by
        intro e he
        rw [mem_filter, hHdef, mem_image] at he
        obtain ⟨⟨t, ht, rfl⟩, hsubij⟩ := he
        refine mem_image_of_mem g (mem_filter.mpr ⟨ht, ?_, ?_⟩)
        · have hh : i ∈ g t := hsubij (mem_insert_self i {j})
          rw [hgapp] at hh
          exact (hmempush _ i).mp hh
        · have hh : j ∈ g t := hsubij (mem_insert_of_mem (mem_singleton_self j))
          rw [hgapp] at hh
          exact (hmempush _ j).mp hh
      refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le ?_)
      have hsub2 : Tset.filter (fun t => ψ i ∈ triangleEdges t.1 t.2.1 t.2.2 ∧
            ψ j ∈ triangleEdges t.1 t.2.1 t.2.2) ⊆
          ({x, y, u, v} : Finset (Fin n)) ×ˢ
            (({x, y, u, v} : Finset (Fin n)) ×ˢ ({x, y, u, v} : Finset (Fin n))) := by
        intro t ht
        rw [mem_filter] at ht
        obtain ⟨-, hi1, hj1⟩ := ht
        rw [hxy, htri] at hi1
        rw [huv, htri] at hj1
        have hVxy : ∀ w : Fin n, (w = x ∨ w = y) → w ∈ ({x, y, u, v} : Finset (Fin n)) := by
          intro w hw
          rcases hw with rfl | rfl <;> simp
        have hVuv : ∀ w : Fin n, (w = u ∨ w = v) → w ∈ ({x, y, u, v} : Finset (Fin n)) := by
          intro w hw
          rcases hw with rfl | rfl <;> simp
        have hmk : t.1 ∈ ({x, y, u, v} : Finset (Fin n)) →
            t.2.1 ∈ ({x, y, u, v} : Finset (Fin n)) → t.2.2 ∈ ({x, y, u, v} : Finset (Fin n)) →
            t ∈ ({x, y, u, v} : Finset (Fin n)) ×ˢ
              (({x, y, u, v} : Finset (Fin n)) ×ˢ ({x, y, u, v} : Finset (Fin n))) :=
          fun h1 h2 h3 => mem_product.mpr ⟨h1, mem_product.mpr ⟨h2, h3⟩⟩
        rcases hi1 with a | a | a
        · obtain ⟨p1, p2⟩ := hpair t.1 t.2.1 x y a.symm
          rcases hj1 with b | b | b
          · exact absurd (a.trans b.symm) hxyuv
          · exact hmk (hVxy _ p1) (hVxy _ p2) (hVuv _ (hpair t.1 t.2.2 u v b.symm).2)
          · exact hmk (hVxy _ p1) (hVxy _ p2) (hVuv _ (hpair t.2.1 t.2.2 u v b.symm).2)
        · obtain ⟨p1, p2⟩ := hpair t.1 t.2.2 x y a.symm
          rcases hj1 with b | b | b
          · exact hmk (hVxy _ p1) (hVuv _ (hpair t.1 t.2.1 u v b.symm).2) (hVxy _ p2)
          · exact absurd (a.trans b.symm) hxyuv
          · exact hmk (hVxy _ p1) (hVuv _ (hpair t.2.1 t.2.2 u v b.symm).1) (hVxy _ p2)
        · obtain ⟨p1, p2⟩ := hpair t.2.1 t.2.2 x y a.symm
          rcases hj1 with b | b | b
          · exact hmk (hVuv _ (hpair t.1 t.2.1 u v b.symm).1) (hVxy _ p1) (hVxy _ p2)
          · exact hmk (hVuv _ (hpair t.1 t.2.2 u v b.symm).1) (hVxy _ p1) (hVxy _ p2)
          · exact absurd (a.trans b.symm) hxyuv
      refine le_trans (Finset.card_le_card hsub2) ?_
      rw [card_product, card_product]
      have h4 := hle4 x y u v
      calc ({x, y, u, v} : Finset (Fin n)).card *
            (({x, y, u, v} : Finset (Fin n)).card * ({x, y, u, v} : Finset (Fin n)).card)
          ≤ 4 * (4 * 4) := Nat.mul_le_mul h4 (Nat.mul_le_mul h4 h4)
        _ = 64 := by norm_num
    have hmax1 : (maxCodegree 1 H : ℝ) ≤ (108 / c + 64 / Real.sqrt (c / 3) + 1) * d := by
      have h1 : (maxCodegree 1 H : ℝ) ≤ 12 * (n:ℝ) := by exact_mod_cast hΔ1
      refine h1.trans ?_
      calc 12 * (n:ℝ) = (108 / c) * (c * (n:ℝ) / 9) := by field_simp; ring
        _ ≤ (108 / c) * d := mul_le_mul_of_nonneg_left hdlb h108.le
        _ ≤ (108 / c + 64 / Real.sqrt (c / 3) + 1) * d := by
            have hz : (0:ℝ) ≤ (64 / Real.sqrt (c / 3) + 1) * d :=
              mul_nonneg (by linarith) hdpos.le
            nlinarith
    have hmax2 : (maxCodegree 2 H : ℝ)
        ≤ (108 / c + 64 / Real.sqrt (c / 3) + 1) * Real.sqrt d := by
      have h1 : (maxCodegree 2 H : ℝ) ≤ 64 := by exact_mod_cast hΔ2
      refine h1.trans ?_
      have hn3R : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn3
      have hdc3 : c / 3 ≤ d := by
        refine le_trans ?_ hdlb
        nlinarith
      have hs : Real.sqrt (c / 3) ≤ Real.sqrt d := Real.sqrt_le_sqrt hdc3
      have hsdnn : (0:ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg d
      calc (64:ℝ) = (64 / Real.sqrt (c / 3)) * Real.sqrt (c / 3) := by field_simp
        _ ≤ (64 / Real.sqrt (c / 3)) * Real.sqrt d := mul_le_mul_of_nonneg_left hs h64.le
        _ ≤ (108 / c + 64 / Real.sqrt (c / 3) + 1) * Real.sqrt d := by
            nlinarith [mul_nonneg (show (0:ℝ) ≤ 108 / c + 1 by linarith) hsdnn]
    obtain ⟨𝒞, hcard𝒞, hcov𝒞, hsize𝒞⟩ := hcont N H d hH3 hdinv hdeq hmax1 hmax2
    refine ⟨𝒞.image pull, ?_, ?_, ?_⟩
    · have hcard1 : (((𝒞.image pull)).card : ℝ) ≤ (𝒞.card : ℝ) := by
        exact_mod_cast Finset.card_image_le
      refine hcard1.trans (hcard𝒞.trans ?_)
      -- `∑_{i ≤ M} binom(N, i) ≤ (M + 1) N ^ M ≤ n ^ (2M + 3)`, and the fingerprint budget
      -- `M = ⌊N / √d⌋₊` is at most `(3 / √c) n ^ (3/2)` because `N ≤ n²` and `d ≥ c n / 9`.
      set M' : ℕ := ⌊(N:ℝ) / Real.sqrt d⌋₊ with hM'def
      have hsdpos : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr hdpos
      have hsd1 : (1:ℝ) ≤ Real.sqrt d := by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt hd1
      have hNn : N ≤ n * n := by exact_mod_cast hFn2
      have hM'N : M' ≤ N := by
        rw [hM'def]
        have h1 : (N:ℝ) / Real.sqrt d ≤ (N:ℝ) := by
          rw [div_le_iff₀ hsdpos]
          nlinarith [hNR.le]
        calc ⌊(N:ℝ) / Real.sqrt d⌋₊ ≤ ⌊((N:ℕ):ℝ)⌋₊ := Nat.floor_le_floor h1
          _ = N := Nat.floor_natCast N
      have hsum1 : ∑ i ∈ range (M' + 1), N.choose i ≤ (M' + 1) * N ^ M' := by
        calc ∑ i ∈ range (M' + 1), N.choose i ≤ ∑ _i ∈ range (M' + 1), N ^ M' := by
              refine Finset.sum_le_sum (fun i hi => ?_)
              exact le_trans (Nat.choose_le_pow N i)
                (Nat.pow_le_pow_right hNpos (by have := mem_range.mp hi; omega))
          _ = (M' + 1) * N ^ M' := by
              rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      have hnat : (M' + 1) * N ^ M' ≤ n ^ (2 * M' + 3) := by
        have h3 : 1 ≤ n := by omega
        have hA : M' + 1 ≤ n ^ 3 := by
          have h1 : M' ≤ n * n := le_trans hM'N hNn
          have hm1 : 1 * 1 ≤ n * n := Nat.mul_le_mul h3 h3
          have h5 : 3 * (n * n) ≤ n * (n * n) := Nat.mul_le_mul_right _ hn3
          linarith
        have hB : N ^ M' ≤ n ^ (2 * M') := by
          calc N ^ M' ≤ (n * n) ^ M' := Nat.pow_le_pow_left hNn M'
            _ = n ^ (2 * M') := by rw [pow_mul]; ring
        calc (M' + 1) * N ^ M' ≤ n ^ 3 * n ^ (2 * M') := Nat.mul_le_mul hA hB
          _ = n ^ (2 * M' + 3) := by ring
      have hscne : Real.sqrt c ≠ 0 := ne_of_gt hsc
      have hns : (n:ℝ) ^ ((3:ℝ)/2) * Real.sqrt (n:ℝ) = (n:ℝ) * (n:ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnpos, show (3:ℝ)/2 + 1/2 = 2 by norm_num,
          show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
        ring
      have hsqd : Real.sqrt c * Real.sqrt (n:ℝ) / 3 ≤ Real.sqrt d := by
        rw [show Real.sqrt c * Real.sqrt (n:ℝ) / 3 = Real.sqrt (c * (n:ℝ) / 9) by
          rw [Real.sqrt_div (by positivity), Real.sqrt_mul hc.le,
            show (9:ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt hdlb
      have hn32pos : (0:ℝ) < (n:ℝ) ^ ((3:ℝ)/2) := Real.rpow_pos_of_pos hnpos _
      have hn321 : (1:ℝ) ≤ (n:ℝ) ^ ((3:ℝ)/2) := by
        have h := Real.rpow_le_rpow_of_exponent_le hnR (show (0:ℝ) ≤ 3/2 by norm_num)
        rwa [Real.rpow_zero] at h
      have hkey : (M':ℝ) ≤ 3 / Real.sqrt c * (n:ℝ) ^ ((3:ℝ)/2) := by
        rw [hM'def]
        refine le_trans (Nat.floor_le (by positivity)) ?_
        rw [div_le_iff₀ hsdpos]
        have hX : (0:ℝ) ≤ 3 / Real.sqrt c * (n:ℝ) ^ ((3:ℝ)/2) := by positivity
        calc (N:ℝ) ≤ (n:ℝ) * (n:ℝ) := hFn2
          _ = (n:ℝ) ^ ((3:ℝ)/2) * Real.sqrt (n:ℝ) := hns.symm
          _ = 3 / Real.sqrt c * (n:ℝ) ^ ((3:ℝ)/2) * (Real.sqrt c * Real.sqrt (n:ℝ) / 3) := by
              field_simp
          _ ≤ 3 / Real.sqrt c * (n:ℝ) ^ ((3:ℝ)/2) * Real.sqrt d :=
              mul_le_mul_of_nonneg_left hsqd hX
      have hexp : ((2 * M' + 3 : ℕ) : ℝ) ≤ C * (n:ℝ) ^ ((3:ℝ)/2) := by
        have hA : 2 * (M':ℝ) ≤ 6 / Real.sqrt c * (n:ℝ) ^ ((3:ℝ)/2) := by
          calc 2 * (M':ℝ) ≤ 2 * (3 / Real.sqrt c * (n:ℝ) ^ ((3:ℝ)/2)) := by linarith
            _ = 6 / Real.sqrt c * (n:ℝ) ^ ((3:ℝ)/2) := by ring
        have hB : (3:ℝ) ≤ 3 * (n:ℝ) ^ ((3:ℝ)/2) := by linarith
        have hC0 : (0:ℝ) ≤ (n₀:ℝ) * (n:ℝ) ^ ((3:ℝ)/2) := mul_nonneg hn₀pos.le hn32pos.le
        have hD : C * (n:ℝ) ^ ((3:ℝ)/2)
            = 6 / Real.sqrt c * (n:ℝ) ^ ((3:ℝ)/2) + 3 * (n:ℝ) ^ ((3:ℝ)/2)
              + (n₀:ℝ) * (n:ℝ) ^ ((3:ℝ)/2) := by rw [hCdef]; ring
        push_cast
        rw [hD]
        linarith
      calc ∑ i ∈ range (M' + 1), (N.choose i : ℝ)
          = ((∑ i ∈ range (M' + 1), N.choose i : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((n ^ (2 * M' + 3) : ℕ) : ℝ) := by exact_mod_cast le_trans hsum1 hnat
        _ = (n:ℝ) ^ (((2 * M' + 3 : ℕ)) : ℝ) := by rw [Real.rpow_natCast]; push_cast; ring
        _ ≤ (n:ℝ) ^ (C * (n:ℝ) ^ ((3:ℝ)/2)) := Real.rpow_le_rpow_of_exponent_le hnR hexp
    · intro D hD
      obtain ⟨A, hA, rfl⟩ := mem_image.mp hD
      refine ⟨hpullF A, ?_⟩
      rw [hcardpull A]
      have hAs := hsize𝒞 A hA
      nlinarith [mul_nonneg (sub_nonneg.mpr hδδ₀) hNR.le]
    · intro G hGtf hGF
      have hindep : ∀ e ∈ H, ¬ e ⊆ push G := by
        intro e he hsube
        rw [hHdef, mem_image] at he
        obtain ⟨t, ht, rfl⟩ := he
        obtain ⟨-, -, -, h4⟩ := hTmem t ht
        rw [hgapp] at hsube
        have hGsub : triangleEdges t.1 t.2.1 t.2.2 ⊆ G := by
          have h5 := hpullmono _ _ hsube
          rwa [hpullpush _ h4, hpullpush _ hGF] at h5
        exact hGtf.2 t.1 t.2.1 t.2.2 hGsub
      obtain ⟨A, hA, hGA⟩ := hcov𝒞 (push G) hindep
      refine ⟨pull A, mem_image_of_mem _ hA, ?_⟩
      have h6 := hpullmono _ _ hGA
      rwa [hpullpush _ hGF] at h6
  · -- Below the threshold every triangle-free subgraph of `F` is taken as its own container.
    -- `F` spans a triangle, so each of them misses an edge of `F`, and `δ ≤ 1 / (n₀² + 1)` is
    -- small enough that `|F| - 1 ≤ (1 - δ) |F|`; the family has at most `2 ^ (n²)` members.
    rw [not_le] at hbig
    have hnn₀ : (n:ℝ) ≤ (n₀:ℝ) := by exact_mod_cast hbig.le
    refine ⟨F.powerset.filter (fun D => IsTriangleFreeEdgeSet D), ?_, ?_, ?_⟩
    · have h1 : ((F.powerset.filter (fun D => IsTriangleFreeEdgeSet D)).card : ℝ)
          ≤ (2:ℝ) ^ ((F.card : ℝ)) := by
        have h2 := Finset.card_filter_le F.powerset (fun D => IsTriangleFreeEdgeSet D)
        rw [Finset.card_powerset] at h2
        calc ((F.powerset.filter (fun D => IsTriangleFreeEdgeSet D)).card : ℝ)
            ≤ ((2 ^ F.card : ℕ) : ℝ) := by exact_mod_cast h2
          _ = (2:ℝ) ^ ((F.card : ℝ)) := by
              rw [Real.rpow_natCast]; push_cast; ring
      refine h1.trans ?_
      have hsplit : (n:ℝ) * (n:ℝ) = (n:ℝ) ^ ((1:ℝ)/2) * (n:ℝ) ^ ((3:ℝ)/2) := by
        rw [← Real.rpow_add hnpos, show (1:ℝ)/2 + 3/2 = 2 by norm_num,
          show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
        ring
      have hhalf : (n:ℝ) ^ ((1:ℝ)/2) ≤ (n:ℝ) := by
        calc (n:ℝ) ^ ((1:ℝ)/2) ≤ (n:ℝ) ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
          _ = (n:ℝ) := Real.rpow_one _
      have hexp : (F.card : ℝ) ≤ C * (n:ℝ) ^ ((3:ℝ)/2) := by
        refine hFn2.trans ?_
        rw [hsplit]
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hnpos.le _)
        rw [hCdef]
        linarith
      calc (2:ℝ) ^ ((F.card : ℝ)) ≤ (2:ℝ) ^ (C * (n:ℝ) ^ ((3:ℝ)/2)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
        _ ≤ (n:ℝ) ^ (C * (n:ℝ) ^ ((3:ℝ)/2)) := by
            refine Real.rpow_le_rpow (by norm_num) hn2 ?_
            have : (0:ℝ) ≤ (n:ℝ) ^ ((3:ℝ)/2) := Real.rpow_nonneg hnpos.le _
            rw [hCdef]
            nlinarith
    · intro D hD
      rw [mem_filter, mem_powerset] at hD
      obtain ⟨hDF, hDtf⟩ := hD
      refine ⟨hDF, ?_⟩
      have hne : D ≠ F := by
        rintro rfl
        exact hDtf.2 t₀.1 t₀.2.1 t₀.2.2 hsub0
      have hlt : D.card + 1 ≤ F.card := Finset.card_lt_card (lt_of_le_of_ne hDF hne)
      have hltR : (D.card : ℝ) ≤ (F.card : ℝ) - 1 := by
        have : ((D.card + 1 : ℕ) : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast hlt
        push_cast at this
        linarith
      have hFn₀ : (F.card : ℝ) ≤ (n₀:ℝ)^2 := by nlinarith
      have hδF : δ * (F.card : ℝ) ≤ 1 := by
        have h1 : δ * (F.card:ℝ) ≤ (1/((n₀:ℝ)^2+1)) * (n₀:ℝ)^2 :=
          mul_le_mul hδsmall hFn₀ (by positivity) (by positivity)
        have h2 : (1/((n₀:ℝ)^2+1)) * (n₀:ℝ)^2 ≤ 1 := by
          rw [div_mul_eq_mul_div, div_le_one (by positivity)]
          nlinarith
        linarith
      linarith
    · intro G hGtf hGF
      exact ⟨G, mem_filter.mpr ⟨mem_powerset.mpr hGF, hGtf⟩, subset_rfl⟩

/-- **Containers for triangle-free graphs** (Zhao, Theorem 11.1.1).  Every triangle-free graph on
`n` vertices sits inside one of at most `n ^ (C n^{3/2})` graphs, each with at most
`(1/4 + ε) n²` edges — Mantel's bound, up to `ε`.

Obtained from `exists_containers_three_uniform` applied to the hypergraph whose vertices are the
pairs from `[n]` and whose edges are the triangles, then iterated: one application only shrinks a
container by a factor `1 - δ`, so the theorem's near-optimal `1/4 + ε` needs the iteration of
Remark 11.2.2 together with a supersaturation input. -/
theorem exists_containers_triangleFree (ε : ℝ) (hε : 0 < ε) :
    ∃ C > 0, ∀ n : ℕ, ∃ 𝒞 : Finset (Finset (Sym2 (Fin n))),
      (𝒞.card : ℝ) ≤ (n : ℝ) ^ (C * (n : ℝ) ^ ((3 : ℝ) / 2)) ∧
      (∀ F ∈ 𝒞, (F.card : ℝ) ≤ (1 / 4 + ε) * (n : ℝ) ^ 2) ∧
      (∀ G ∈ triangleFreeGraphs n, ∃ F ∈ 𝒞, G ⊆ F) := by
  obtain ⟨c, hc, hsat⟩ := exists_triangle_supersaturation ε hε
  obtain ⟨δ, C₀, hδ0, hδ1, hC₀, hshrink⟩ := exists_shrunken_containers_of_many_triangles c hc
  obtain ⟨K, hK⟩ : ∃ K : ℕ, (1 - δ) ^ K ≤ 1 / 4 :=
    (exists_pow_lt_of_lt_one (by norm_num) (by linarith)).imp fun _ h => h.le
  refine ⟨((K : ℝ) + 1) * C₀, mul_pos (by positivity) hC₀, fun n => ?_⟩
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmem : ∀ G : Finset (Sym2 (Fin n)), G ∈ triangleFreeGraphs n →
      IsTriangleFreeEdgeSet G := by
    intro G hG
    simpa [triangleFreeGraphs] using hG
  -- Raising `n` to a larger multiple of `n ^ (3/2)` only increases the bound, `n = 0` included.
  have hrpow : ∀ a b : ℝ, a ≤ b →
      (n : ℝ) ^ (a * (n : ℝ) ^ ((3 : ℝ) / 2)) ≤ (n : ℝ) ^ (b * (n : ℝ) ^ ((3 : ℝ) / 2)) := by
    intro a b hab
    rcases eq_or_lt_of_le hn with h0 | hpos
    · rw [← h0, Real.zero_rpow (by norm_num : (3 : ℝ) / 2 ≠ 0), mul_zero, mul_zero]
    · have hn1 : 1 ≤ n := Nat.cast_pos.mp hpos
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1)
        (mul_le_mul_of_nonneg_right hab (Real.rpow_nonneg hn _))
  set Q : ℝ := (n : ℝ) ^ (C₀ * (n : ℝ) ^ ((3 : ℝ) / 2)) with hQdef
  have hQ1 : (1 : ℝ) ≤ Q := by
    have h := hrpow 0 C₀ hC₀.le
    rwa [zero_mul, Real.rpow_zero] at h
  have hQ0 : (0 : ℝ) ≤ Q := le_trans zero_le_one hQ1
  have htot : (((univ : Finset (Sym2 (Fin n)))).card : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h := Fintype.card_le_of_surjective (Function.uncurry (Sym2.mk (α := Fin n)))
      Sym2.mk_surjective
    simp only [Fintype.card_prod, Fintype.card_fin] at h
    rw [Finset.card_univ]
    calc (Fintype.card (Sym2 (Fin n)) : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast h
      _ = (n : ℝ) ^ 2 := by push_cast; ring
  -- After `k` rounds of the iteration: at most `Q ^ k` containers, none of them carrying a
  -- diagonal pair, and each either already past Mantel's bound or shrunk by `(1 - δ) ^ k`.
  have key : ∀ k : ℕ, ∃ 𝒞 : Finset (Finset (Sym2 (Fin n))),
      (𝒞.card : ℝ) ≤ Q ^ k ∧
      (∀ F ∈ 𝒞, (∀ e ∈ F, ¬ e.IsDiag) ∧
        (F.card : ℝ) ≤ max ((1 / 4 + ε) * (n : ℝ) ^ 2) ((1 - δ) ^ k * (n : ℝ) ^ 2)) ∧
      (∀ G ∈ triangleFreeGraphs n, ∃ F ∈ 𝒞, G ⊆ F) := by
    intro k
    induction k with
    | zero =>
      refine ⟨{univ.filter fun e : Sym2 (Fin n) => ¬ e.IsDiag}, by simp, ?_, ?_⟩
      · intro F hF
        rw [mem_singleton] at hF
        subst hF
        refine ⟨fun e he => (mem_filter.mp he).2, le_trans ?_ (le_max_right _ _)⟩
        rw [pow_zero, one_mul]
        exact le_trans (by exact_mod_cast card_filter_le _ _) htot
      · intro G hG
        refine ⟨_, mem_singleton_self _, fun e he => mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
        exact (hmem G hG).1 e he
    | succ k ih =>
      obtain ⟨𝒞, hcard, hprop, hcov⟩ := ih
      have hex : ∀ F : Finset (Sym2 (Fin n)), ∃ 𝒟 : Finset (Finset (Sym2 (Fin n))), F ∈ 𝒞 →
          ((𝒟.card : ℝ) ≤ Q ∧
            (∀ D ∈ 𝒟, (∀ e ∈ D, ¬ e.IsDiag) ∧ (D.card : ℝ) ≤
              max ((1 / 4 + ε) * (n : ℝ) ^ 2) ((1 - δ) ^ (k + 1) * (n : ℝ) ^ 2)) ∧
            (∀ G : Finset (Sym2 (Fin n)), IsTriangleFreeEdgeSet G → G ⊆ F →
              ∃ D ∈ 𝒟, G ⊆ D)) := by
        intro F
        by_cases hF : F ∈ 𝒞
        · obtain ⟨hdiag, hFcard⟩ := hprop F hF
          by_cases hsmall : (F.card : ℝ) ≤ (1 / 4 + ε) * (n : ℝ) ^ 2
          · exact ⟨{F}, fun _ => ⟨by simpa using hQ1, fun D hD => by
              rw [mem_singleton] at hD
              subst hD
              exact ⟨hdiag, le_trans hsmall (le_max_left _ _)⟩,
              fun G _ hGF => ⟨F, mem_singleton_self F, hGF⟩⟩⟩
          · rw [not_le] at hsmall
            have hFk : (F.card : ℝ) ≤ (1 - δ) ^ k * (n : ℝ) ^ 2 :=
              (le_max_iff.mp hFcard).resolve_left (not_le.mpr hsmall)
            obtain ⟨𝒟, hDcard, hDsub, hDcov⟩ := hshrink n F (hsat n F hdiag hsmall.le)
            refine ⟨𝒟, fun _ => ⟨hDcard, fun D hD => ?_, hDcov⟩⟩
            obtain ⟨hsub, hle⟩ := hDsub D hD
            refine ⟨fun e he => hdiag e (hsub he), le_trans hle (le_trans ?_ (le_max_right _ _))⟩
            calc (1 - δ) * (F.card : ℝ)
                ≤ (1 - δ) * ((1 - δ) ^ k * (n : ℝ) ^ 2) :=
                  mul_le_mul_of_nonneg_left hFk (by linarith)
              _ = (1 - δ) ^ (k + 1) * (n : ℝ) ^ 2 := by ring
        · exact ⟨∅, fun h => absurd h hF⟩
      choose 𝒟 h𝒟 using hex
      refine ⟨𝒞.biUnion 𝒟, ?_, ?_, ?_⟩
      · calc ((𝒞.biUnion 𝒟).card : ℝ) ≤ ((∑ F ∈ 𝒞, (𝒟 F).card : ℕ) : ℝ) := by
              exact_mod_cast card_biUnion_le
          _ = ∑ F ∈ 𝒞, ((𝒟 F).card : ℝ) := by push_cast; ring
          _ ≤ ∑ F ∈ 𝒞, Q := Finset.sum_le_sum fun F hF => (h𝒟 F hF).1
          _ = (𝒞.card : ℝ) * Q := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ Q ^ k * Q := mul_le_mul_of_nonneg_right hcard hQ0
          _ = Q ^ (k + 1) := by ring
      · intro D hD
        obtain ⟨F, hF, hDF⟩ := mem_biUnion.mp hD
        exact (h𝒟 F hF).2.1 D hDF
      · intro G hG
        obtain ⟨F, hF, hGF⟩ := hcov G hG
        obtain ⟨D, hD, hGD⟩ := (h𝒟 F hF).2.2 G (hmem G hG) hGF
        exact ⟨D, mem_biUnion.mpr ⟨F, hF, hD⟩, hGD⟩
  obtain ⟨𝒞, hcard, hprop, hcov⟩ := key K
  refine ⟨𝒞, ?_, fun F hF => ?_, hcov⟩
  · refine hcard.trans ?_
    rw [hQdef, ← Real.rpow_natCast ((n : ℝ) ^ (C₀ * (n : ℝ) ^ ((3 : ℝ) / 2))) K,
      ← Real.rpow_mul hn, mul_comm C₀ ((n : ℝ) ^ ((3 : ℝ) / 2)), mul_assoc,
      mul_comm ((n : ℝ) ^ ((3 : ℝ) / 2)) (C₀ * (K : ℝ))]
    exact hrpow (C₀ * (K : ℝ)) (((K : ℝ) + 1) * C₀) (by nlinarith)
  · refine le_trans (hprop F hF).2 (max_le le_rfl ?_)
    have hsq : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
    nlinarith

/-- **Erdős–Kleitman–Rothschild** (Zhao, Theorem 11.0.2), upper bound: there are at most
`2 ^ ((1/4 + ε) n²)` triangle-free graphs on `n` vertices, for every `ε > 0` and `n` large.

Together with `le_card_triangleFreeGraphs` this is the asymptotic `2^(n²/4 + o(n²))`.  The union
bound is over the containers: each of the `n^(C n^{3/2})` of them has at most `(1/4 + ε) n²`
edges and so at most `2^((1/4+ε)n²)` subgraphs, and `n^(C n^{3/2}) = 2^(o(n²))` absorbs the
factor. -/
theorem card_triangleFreeGraphs_le (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N,
      ((triangleFreeGraphs n).card : ℝ) ≤ (2 : ℝ) ^ ((1 / 4 + ε) * (n : ℝ) ^ 2) := by
  obtain ⟨C, hC, hcont⟩ := exists_containers_triangleFree (ε / 2) (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hscale : 0 < Real.log 2 * (ε / 2) := mul_pos hlog2 (by linarith)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 4 * C / (Real.log 2 * (ε / 2)) := ⟨_, rfl⟩
  have hK : 0 < K := hKdef ▸ div_pos (by linarith) hscale
  have hLK : Real.log 2 * (ε / 2) * K = 4 * C := by
    rw [hKdef]
    field_simp
  refine ⟨⌈K ^ 4⌉₊ + 1, fun n hn => ?_⟩
  obtain ⟨𝒞, hcard, hsize, hcover⟩ := hcont n
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have h : 1 ≤ n := le_trans (Nat.le_add_left 1 _) hn
    exact_mod_cast h
  have hpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  have h32 : (0 : ℝ) < (n : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hpos _
  have h14 : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hpos _
  have h74 : (0 : ℝ) < (n : ℝ) ^ ((7 : ℝ) / 4) := Real.rpow_pos_of_pos hpos _
  have e1 : (n : ℝ) ^ ((3 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 4) = (n : ℝ) ^ ((7 : ℝ) / 4) := by
    rw [← Real.rpow_add hpos]
    norm_num
  have e2 : (n : ℝ) ^ ((7 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4) = (n : ℝ) ^ 2 := by
    rw [← Real.rpow_add hpos, ← Real.rpow_natCast (n : ℝ) 2]
    norm_num
  -- `log t ≤ t - 1` applied at `t = n ^ (1/4)` gives `log n ≤ 4 n ^ (1/4)`.
  have hlogn : Real.log (n : ℝ) ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
    have h := Real.log_le_sub_one_of_pos h14
    rw [Real.log_rpow hpos] at h
    linarith
  have hKn : K ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := by
    have hce : K ^ 4 ≤ (n : ℝ) := by
      refine le_trans (Nat.le_ceil _) ?_
      have h : (⌈K ^ 4⌉₊ : ℕ) ≤ n := le_trans (Nat.le_add_right _ 1) hn
      exact_mod_cast h
    have hrw : K = (K ^ 4) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_natCast K 4, ← Real.rpow_mul hK.le]
      norm_num
    rw [hrw]
    exact Real.rpow_le_rpow (by positivity) hce (by norm_num)
  -- The container count `n ^ (C n ^ (3/2))` is at most `2 ^ ((ε/2) n²)`.
  have hanal : (n : ℝ) ^ (C * (n : ℝ) ^ ((3 : ℝ) / 2)) ≤ (2 : ℝ) ^ (ε / 2 * (n : ℝ) ^ 2) := by
    have hCm : (0 : ℝ) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2) := mul_nonneg hC.le h32.le
    have hineq : Real.log (n : ℝ) * (C * (n : ℝ) ^ ((3 : ℝ) / 2))
        ≤ Real.log 2 * (ε / 2 * (n : ℝ) ^ 2) := by
      calc Real.log (n : ℝ) * (C * (n : ℝ) ^ ((3 : ℝ) / 2))
          ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 4) * (C * (n : ℝ) ^ ((3 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_right hlogn hCm
        _ = 4 * C * ((n : ℝ) ^ ((3 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 4)) := by ring
        _ = Real.log 2 * (ε / 2) * K * (n : ℝ) ^ ((7 : ℝ) / 4) := by rw [hLK, e1]
        _ ≤ Real.log 2 * (ε / 2) * (n : ℝ) ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((7 : ℝ) / 4) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hKn hscale.le) h74.le
        _ = Real.log 2 * (ε / 2 * ((n : ℝ) ^ ((7 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4))) := by
            ring
        _ = Real.log 2 * (ε / 2 * (n : ℝ) ^ 2) := by rw [e2]
    have hl : (n : ℝ) ^ (C * (n : ℝ) ^ ((3 : ℝ) / 2))
        = Real.exp (Real.log (n : ℝ) * (C * (n : ℝ) ^ ((3 : ℝ) / 2))) :=
      Real.rpow_def_of_pos hpos _
    have hr : (2 : ℝ) ^ (ε / 2 * (n : ℝ) ^ 2)
        = Real.exp (Real.log 2 * (ε / 2 * (n : ℝ) ^ 2)) :=
      Real.rpow_def_of_pos (by norm_num) _
    rw [hl, hr]
    exact Real.exp_le_exp.mpr hineq
  -- Every triangle-free graph is a subgraph of a container, and a container with `m` edges has
  -- `2 ^ m` subgraphs.
  have hsub : triangleFreeGraphs n ⊆ 𝒞.biUnion fun F => F.powerset := by
    intro G hG
    obtain ⟨F, hF, hGF⟩ := hcover G hG
    exact Finset.mem_biUnion.mpr ⟨F, hF, Finset.mem_powerset.mpr hGF⟩
  have hnat : (triangleFreeGraphs n).card ≤ ∑ F ∈ 𝒞, 2 ^ F.card :=
    calc (triangleFreeGraphs n).card ≤ (𝒞.biUnion fun F => F.powerset).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ F ∈ 𝒞, F.powerset.card := Finset.card_biUnion_le
      _ = ∑ F ∈ 𝒞, 2 ^ F.card := by simp [Finset.card_powerset]
  have hterm : ∀ F ∈ 𝒞, (2 : ℝ) ^ F.card ≤ (2 : ℝ) ^ ((1 / 4 + ε / 2) * (n : ℝ) ^ 2) := by
    intro F hF
    rw [← Real.rpow_natCast (2 : ℝ) F.card]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two (hsize F hF)
  calc ((triangleFreeGraphs n).card : ℝ)
      ≤ ((∑ F ∈ 𝒞, 2 ^ F.card : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = ∑ F ∈ 𝒞, (2 : ℝ) ^ F.card := by push_cast; ring
    _ ≤ 𝒞.card • (2 : ℝ) ^ ((1 / 4 + ε / 2) * (n : ℝ) ^ 2) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = (𝒞.card : ℝ) * (2 : ℝ) ^ ((1 / 4 + ε / 2) * (n : ℝ) ^ 2) := by
        rw [nsmul_eq_mul]
    _ ≤ (n : ℝ) ^ (C * (n : ℝ) ^ ((3 : ℝ) / 2)) * (2 : ℝ) ^ ((1 / 4 + ε / 2) * (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg (by norm_num) _)
    _ ≤ (2 : ℝ) ^ (ε / 2 * (n : ℝ) ^ 2) * (2 : ℝ) ^ ((1 / 4 + ε / 2) * (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hanal (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ ((1 / 4 + ε) * (n : ℝ) ^ 2) := by
        rw [← Real.rpow_add (by norm_num)]
        ring_nf

/-- **Erdős–Kleitman–Rothschild**, lower bound: every subgraph of the complete bipartite graph
`K_{⌊n/2⌋, ⌈n/2⌉}` is triangle-free, and there are `2 ^ (⌊n/2⌋⌈n/2⌉)` of them.

The easy half, and the one that fixes the constant `1/4`.  No containers involved. -/
theorem le_card_triangleFreeGraphs (n : ℕ) :
    2 ^ (n / 2 * ((n + 1) / 2)) ≤ (triangleFreeGraphs n).card := by
  set L : Finset (Fin n) := univ.map (Fin.castLEEmb (Nat.div_le_self n 2)) with hLdef
  set f : Fin n × Fin n → Sym2 (Fin n) := fun p => s(p.1, p.2) with hfdef
  have hLcard : L.card = n / 2 := by simp [hLdef]
  have hLccard : Lᶜ.card = (n + 1) / 2 := by
    have h : Lᶜ.card = n - n / 2 := by rw [Finset.card_compl, hLcard, Fintype.card_fin]
    omega
  have hsides : ∀ F : Finset (Fin n × Fin n), F ⊆ L ×ˢ Lᶜ → ∀ x y : Fin n,
      s(x, y) ∈ F.image f → (x ∈ L ↔ y ∉ L) := by
    intro F hF x y hxy
    obtain ⟨⟨a, b⟩, hab, hE⟩ := Finset.mem_image.mp hxy
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp (hF hab)
    rw [Finset.mem_compl] at hb
    rcases Sym2.eq_iff.mp hE with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [ha, hb]
    · simp [ha, hb]
  have hmaps : ∀ F ∈ (L ×ˢ Lᶜ).powerset, F.image f ∈ triangleFreeGraphs n := by
    intro F hF
    rw [Finset.mem_powerset] at hF
    rw [triangleFreeGraphs, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro e he
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp (hF hab)
      rw [Finset.mem_compl] at hb
      simp only [hfdef, Sym2.mk_isDiag_iff]
      rintro rfl
      exact hb ha
    · intro a b c hsub
      have hab := hsides F hF a b (hsub (by simp [triangleEdges]))
      have hac := hsides F hF a c (hsub (by simp [triangleEdges]))
      have hbc := hsides F hF b c (hsub (by simp [triangleEdges]))
      tauto
  have hsub : ∀ A B : Finset (Fin n × Fin n), A ⊆ L ×ˢ Lᶜ → B ⊆ L ×ˢ Lᶜ →
      A.image f = B.image f → A ⊆ B := by
    intro A B hA hB h p hp
    have hpB : f p ∈ B.image f := by rw [← h]; exact Finset.mem_image_of_mem f hp
    obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hpB
    obtain ⟨hq1, -⟩ := Finset.mem_product.mp (hB hq)
    obtain ⟨-, hp2⟩ := Finset.mem_product.mp (hA hp)
    rw [Finset.mem_compl] at hp2
    rcases Sym2.eq_iff.mp hqp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rwa [show p = q from Prod.ext h1.symm h2.symm]
    · exact absurd (h1 ▸ hq1) hp2
  have hcard : ((L ×ˢ Lᶜ).powerset).card ≤ (triangleFreeGraphs n).card := by
    refine Finset.card_le_card_of_injOn (fun F => F.image f) (fun F hF => hmaps F hF) ?_
    intro A hA B hB h
    rw [Finset.mem_coe, Finset.mem_powerset] at hA hB
    exact Finset.Subset.antisymm (hsub A B hA hB h) (hsub B A hB hA h.symm)
  rwa [Finset.card_powerset, Finset.card_product, hLcard, hLccard] at hcard

/-- **Counting `H`-free graphs, lower bound** (Zhao, Theorem 11.1.3, the easy half): there are at
least `2 ^ ex(n, H)` graphs on `n` labelled vertices containing no copy of `H`.

`le_card_triangleFreeGraphs` is this statement for `H = K₃`, where the extremal graph is named
explicitly and the count is `2 ^ (⌊n/2⌋⌈n/2⌉)`.  Here the extremal graph is supplied abstractly
by Mathlib's `SimpleGraph.exists_isExtremal_free`, which is why no construction appears.

`H ≠ ⊥` is not boilerplate.  `extremalNumber` is a `sup` over the `H`-free graphs and is `0` when
there are none, so without the hypothesis the claim would read `1 ≤ 0` whenever every graph
contains `H`.  With it, `⊥` is itself `H`-free and the supremum is attained.

The matching upper bound, `2 ^ ((1 + o(1)) ex(n, H))`, is the container theorem's payoff and is
not stated: the source quotes it rather than proving it, and for `H = K₃` it is
`card_triangleFreeGraphs_le`, which took §11.2 in full. -/
theorem le_card_free_graphs (n : ℕ) {W : Type*} {H : SimpleGraph W} (hH : H ≠ ⊥) :
    2 ^ SimpleGraph.extremalNumber n H ≤ Nat.card {G : SimpleGraph (Fin n) // H.Free G} := by
  obtain ⟨G₀, hdec, hG₀⟩ := SimpleGraph.exists_isExtremal_free (V := Fin n) hH
  have hsub : ∀ F ∈ G₀.edgeFinset.powerset, (↑F : Set (Sym2 (Fin n))) ⊆ G₀.edgeSet := by
    intro F hF e he
    exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_powerset.mp hF he)
  -- no member of `G₀.edgeFinset` is a loop, so `fromEdgeSet` returns a subset unchanged
  have hdiag : ∀ F ∈ G₀.edgeFinset.powerset,
      (↑F : Set (Sym2 (Fin n))) \ Sym2.diagSet = ↑F := by
    intro F hF
    refine Set.ext fun e => ⟨fun he => he.1, fun he => ⟨he, ?_⟩⟩
    simp only [Sym2.mem_diagSet]
    exact G₀.not_isDiag_of_mem_edgeSet (hsub F hF he)
  -- freeness is downward closed, and each such graph is a subgraph of the extremal `G₀`
  have hfree : ∀ F ∈ G₀.edgeFinset.powerset,
      H.Free (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 (Fin n)))) := by
    intro F hF hcon
    refine hG₀.prop (hcon.mono_right ?_)
    rw [SimpleGraph.fromEdgeSet_le, hdiag F hF]
    exact hsub F hF
  have hinj : Function.Injective fun F : G₀.edgeFinset.powerset =>
      (⟨SimpleGraph.fromEdgeSet (↑(F : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))),
        hfree _ F.2⟩ : {G : SimpleGraph (Fin n) // H.Free G}) := by
    intro F₁ F₂ h
    have he := congrArg SimpleGraph.edgeSet (congrArg Subtype.val h)
    rw [SimpleGraph.edgeSet_fromEdgeSet, SimpleGraph.edgeSet_fromEdgeSet,
      hdiag _ F₁.2, hdiag _ F₂.2] at he
    exact Subtype.ext (Finset.coe_injective he)
  have hcount := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_finsetCard, Finset.card_powerset,
    SimpleGraph.card_edgeFinset_of_isExtremal_free hG₀, Fintype.card_fin] at hcount

end ProbMethodCombinatorics
