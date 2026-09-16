import ProbMethodCombinatorics.Entropy
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
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
  `I` retires at least `3 * d / 4` vertices, none of them in `I`. -/
private def IsGreedyRule {n : ℕ} (G : SimpleGraph (Fin n)) (d δ : ℝ)
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
  sorry

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

**This docstring claimed until 2026-09-16 that a window of relative width `(c - 1) * δ` above
`δ * n` was left open, and PR #166 flagged the obligation as possibly false.  That was wrong, and
the error is instructive: the window is an artifact of the *degree* order, not of the statement.**
The sharpened count `d * n ≤ t * (c * d + n - t)` is correct, but it is a bound on what the
largest-degree vertex can guarantee, and in the window a tiny high-degree set can leave the
chosen vertex one short.  Nothing forces the order to be by degree, and the greedy order above is
unconditional in these hypotheses — no lower bound on `d - δ * n` is used beyond positivity. -/
theorem exists_dense_fingerprint (c d δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) (hδc : δ ≤ 1 / (100 * c))
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hd : 0 < d) (hlo : δ * n < d)
    (hhi : d ≤ 2 * δ * n) (hsum : (∑ v, (G.degree v : ℝ)) = d * n)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ c * d) :
    ∃ (s : Finset (Fin n) → Fin n) (K : Fin n → Finset (Fin n)),
      ∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) → I.Nonempty →
        s I ∈ I ∧ I ⊆ insert (s I) (K (s I)) ∧
        ((insert (s I) (K (s I))).card : ℝ) ≤ (1 - δ) * n := by
  sorry

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
  sorry

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

end ProbMethodCombinatorics
