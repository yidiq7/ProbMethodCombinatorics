import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.FinRange
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Chapter 2: Linearity of expectations

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Sections 2.1 and 2.3.
-/

namespace ProbMethodCombinatorics

open Finset

section Tournament

variable {n : ℕ}

/-- The Hamilton paths of the tournament `T` on `Fin n`, viewed as the orderings
`σ 0, σ 1, …, σ (n - 1)` of the vertices in which every vertex beats its successor. -/
def hamiltonPaths (T : Fin n → Fin n → Bool) : Finset (Equiv.Perm (Fin n)) :=
  univ.filter fun σ => ((List.finRange n).map σ).IsChain fun a b => T a b = true

/-- **Szele 1943** (Zhao, Theorem 2.1.2): some tournament on `n` vertices has at least
`n! / 2 ^ (n - 1)` Hamilton paths. -/
theorem exists_tournament_card_hamiltonPaths (n : ℕ) :
    ∃ T : Fin n → Fin n → Bool, (∀ a b, a ≠ b → T a b = !T b a) ∧
      (n.factorial : ℝ) / 2 ^ (n - 1) ≤ (hamiltonPaths T).card := by
  -- Average over the `2 ^ (n * n)` tournaments `orient g` obtained by orienting the edge
  -- `{a, b}` according to the bit `g` assigns to the ordered pair `req a b`.  Summing the
  -- number of Hamilton paths over all `g` and exchanging the order of summation counts, for
  -- each ordering `σ`, the `g` satisfying the `n - 1` constraints that make `σ` a Hamilton
  -- path; there are `2 ^ (n * n) / 2 ^ (n - 1)` of those.
  obtain ⟨req, hreq⟩ :
      ∃ req : Fin n → Fin n → Fin n × Fin n,
        ∀ a b, req a b = if a < b then (a, b) else (b, a) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨orient, horient⟩ :
      ∃ orient : (Fin n × Fin n → Bool) → Fin n → Fin n → Bool,
        ∀ g a b, orient g a b = if a < b then g (a, b) else !g (b, a) := ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨nx, hnx⟩ :
      ∃ nx : Fin n → Fin n, ∀ i, nx i = if h : (i : ℕ) + 1 < n then ⟨(i : ℕ) + 1, h⟩ else i :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨val, hval⟩ :
      ∃ val : Equiv.Perm (Fin n) → Fin n × Fin n → Bool,
        ∀ σ p, val σ p = decide (σ.symm p.1 < σ.symm p.2) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨E, hE⟩ :
      ∃ E : Equiv.Perm (Fin n) → Finset (Fin n × Fin n),
        ∀ σ, E σ = (univ.filter fun i : Fin n => (i : ℕ) + 1 < n).image
          fun i => req (σ i) (σ (nx i)) := ⟨_, fun _ => rfl⟩
  -- `orient g` is a tournament.
  have htourn : ∀ g a b, a ≠ b → orient g a b = !orient g b a := by
    intro g a b hab
    rcases lt_trichotomy a b with h | h | h
    · simp [horient, h, asymm h]
    · exact absurd h hab
    · simp [horient, h, asymm h]
  have hnxlt : ∀ i : Fin n, (i : ℕ) + 1 < n → i < nx i := by
    intro i hi
    rw [hnx, dif_pos hi]
    exact Fin.lt_def.2 (by simp)
  have hstep : ∀ (σ : Equiv.Perm (Fin n)) (g : Fin n × Fin n → Bool) (a b : Fin n),
      σ.symm a < σ.symm b → (orient g a b = true ↔ g (req a b) = val σ (req a b)) := by
    intro σ g a b h
    rcases lt_trichotomy a b with hab | hab | hab
    · simp [horient, hreq, hval, hab, h]
    · subst hab; exact absurd h (lt_irrefl _)
    · simp [horient, hreq, hval, asymm hab, asymm h]
  -- `σ` is a Hamilton path of `orient g` exactly when `g` takes the value `val σ p` on each
  -- of the edges `p` joining two vertices adjacent in `σ`.
  have hchain : ∀ (σ : Equiv.Perm (Fin n)) (g : Fin n × Fin n → Bool),
      (((List.finRange n).map σ).IsChain fun a b => orient g a b = true)
        ↔ ∀ p ∈ E σ, g p = val σ p := by
    intro σ g
    rw [List.isChain_iff_getElem]
    simp only [List.length_map, List.length_finRange, List.getElem_map, List.getElem_finRange,
      Fin.cast_mk]
    rw [hE, Finset.forall_mem_image]
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro h i hi
      refine (hstep σ g _ _ (by simpa using hnxlt i hi)).1 ?_
      simpa [hnx, hi] using h (i : ℕ) hi
    · intro h i hi
      have hi' : ((⟨i, Nat.lt_of_succ_lt hi⟩ : Fin n) : ℕ) + 1 < n := by simpa using hi
      have hh := (hstep σ g _ _ (by simpa using hnxlt ⟨i, Nat.lt_of_succ_lt hi⟩ hi')).2
        (h hi')
      simpa [hnx, hi] using hh
  -- Prescribing `g` on a set `s` of edges leaves `2 ^ (n * n) / 2 ^ #s` choices.
  have hcard : ∀ (s : Finset (Fin n × Fin n)) (v : Fin n × Fin n → Bool),
      (univ.filter fun g : Fin n × Fin n → Bool => ∀ p ∈ s, g p = v p).card * 2 ^ s.card
        = 2 ^ (n * n) := by
    intro s v
    have hpi : (univ.filter fun g : Fin n × Fin n → Bool => ∀ p ∈ s, g p = v p)
        = Fintype.piFinset (fun p => if p ∈ s then {v p} else univ) := by
      ext g
      simp only [Fintype.mem_piFinset, mem_filter, mem_univ, true_and]
      constructor
      · intro h p
        by_cases hp : p ∈ s
        · simp [hp, h p hp]
        · simp [hp]
      · intro h p hp
        have := h p
        simpa [hp] using this
    rw [hpi, Fintype.card_piFinset]
    have h1 : ∀ p : Fin n × Fin n, (if p ∈ s then ({v p} : Finset Bool) else univ).card
        = if p ∈ s then 1 else 2 := by
      intro p; by_cases h : p ∈ s <;> simp [h]
    simp_rw [h1]
    have h2 : (2 : ℕ) ^ s.card = ∏ _p ∈ (univ : Finset (Fin n × Fin n)) ∩ s, 2 := by
      rw [Finset.prod_const, Finset.univ_inter]
    rw [h2, ← Finset.prod_ite_mem, ← Finset.prod_mul_distrib]
    have h3 : ∀ p : Fin n × Fin n,
        (if p ∈ s then (1 : ℕ) else 2) * (if p ∈ s then 2 else 1) = 2 := by
      intro p; by_cases h : p ∈ s <;> simp [h]
    simp_rw [h3]
    rw [Finset.prod_const, Finset.card_univ]
    simp
  have hEcard : ∀ σ : Equiv.Perm (Fin n), (E σ).card ≤ n - 1 := by
    intro σ
    rw [hE]
    refine Finset.card_image_le.trans ?_
    have : (univ.filter fun i : Fin n => (i : ℕ) + 1 < n).card ≤ (Finset.range (n - 1)).card := by
      refine Finset.card_le_card_of_injOn (fun i : Fin n => (i : ℕ)) ?_ ?_
      · intro i hi
        simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hi
        simp only [Finset.mem_coe, Finset.mem_range]
        omega
      · exact fun a _ b _ h => Fin.val_injective h
    simpa using this
  have main : ∀ σ : Equiv.Perm (Fin n),
      2 ^ (n * n) ≤ (univ.filter fun g : Fin n × Fin n → Bool =>
          ((List.finRange n).map σ).IsChain fun a b => orient g a b = true).card * 2 ^ (n - 1) := by
    intro σ
    rw [Finset.filter_congr fun g _ => hchain σ g]
    calc (2 : ℕ) ^ (n * n)
        = (univ.filter fun g : Fin n × Fin n → Bool => ∀ p ∈ E σ, g p = val σ p).card
            * 2 ^ (E σ).card := (hcard (E σ) (val σ)).symm
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (hEcard σ))
  -- The double count of the pairs `(g, σ)` with `σ` a Hamilton path of `orient g`.
  have hdouble : n.factorial * 2 ^ (n * n) ≤
      (∑ g : Fin n × Fin n → Bool, (hamiltonPaths (orient g)).card) * 2 ^ (n - 1) := by
    have hswap : ∑ g : Fin n × Fin n → Bool, (hamiltonPaths (orient g)).card
        = ∑ σ : Equiv.Perm (Fin n), (univ.filter fun g : Fin n × Fin n → Bool =>
            ((List.finRange n).map σ).IsChain fun a b => orient g a b = true).card := by
      simp only [hamiltonPaths, Finset.card_filter]
      exact Finset.sum_comm
    rw [hswap, Finset.sum_mul]
    calc n.factorial * 2 ^ (n * n) = ∑ _σ : Equiv.Perm (Fin n), 2 ^ (n * n) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
            smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun σ _ => main σ
  obtain ⟨g, -, hg⟩ := Finset.exists_le_of_sum_le
    (s := (univ : Finset (Fin n × Fin n → Bool)))
    (f := fun _ => n.factorial)
    (g := fun g => (hamiltonPaths (orient g)).card * 2 ^ (n - 1))
    Finset.univ_nonempty (by
      rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
      calc 2 ^ (n * n) * n.factorial = n.factorial * 2 ^ (n * n) := Nat.mul_comm _ _
        _ ≤ _ := hdouble)
  refine ⟨orient g, htourn g, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  exact_mod_cast hg

end Tournament

section IndependentSets

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Caro–Wei** (Zhao, Theorem 2.3.2): every graph has an independent set of size at least
`∑ v, 1 / (d v + 1)`. -/
theorem exists_isIndepSet_caro_wei (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ S : Finset V, G.IsIndepSet (S : Set V) ∧
      ∑ v : V, ((G.degree v : ℝ) + 1)⁻¹ ≤ S.card := by
  -- Greedy form: every vertex subset `A` contains an independent set of size at least
  -- `∑ v ∈ A, 1 / (d v + 1)`.  Taking `A = univ` gives the theorem.
  suffices h : ∀ A : Finset V, ∃ S ⊆ A, G.IsIndepSet (S : Set V) ∧
      ∑ v ∈ A, ((G.degree v : ℝ) + 1)⁻¹ ≤ S.card by
    obtain ⟨S, -, hind, hcard⟩ := h univ
    exact ⟨S, hind, hcard⟩
  intro A
  induction A using Finset.strongInduction with
  | _ A ih =>
    rcases A.eq_empty_or_nonempty with rfl | hA
    · exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
    -- Remove a vertex `v` of minimum degree in the graph induced on `A`, along with its
    -- neighbours inside `A`.
    obtain ⟨v, hvA, hvmin⟩ := A.exists_min_image (fun u => (A.filter (G.Adj u)).card) hA
    have hvN : v ∉ A.filter (G.Adj v) := by simp
    have hBA : insert v (A.filter (G.Adj v)) ⊆ A :=
      Finset.insert_subset hvA (Finset.filter_subset _ _)
    obtain ⟨S, hSsub, hSind, hScard⟩ :=
      ih _ (Finset.sdiff_ssubset hBA ⟨v, Finset.mem_insert_self _ _⟩)
    have hSA : ∀ u ∈ S, u ∈ A ∧ u ∉ insert v (A.filter (G.Adj v)) :=
      fun u hu => Finset.mem_sdiff.1 (hSsub hu)
    have hvS : v ∉ S := fun hv => (hSA v hv).2 (Finset.mem_insert_self _ _)
    have hadj : ∀ u ∈ S, ¬G.Adj v u := fun u hu hvu =>
      (hSA u hu).2 (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨(hSA u hu).1, hvu⟩))
    -- Every vertex of `A` has degree at least the induced degree of `v`.
    have hdeg : ∀ u ∈ A, ((A.filter (G.Adj v)).card : ℝ) + 1 ≤ (G.degree u : ℝ) + 1 := by
      intro u hu
      have h2 : (A.filter (G.Adj u)).card ≤ G.degree u := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        exact Finset.card_le_card fun x hx =>
          (SimpleGraph.mem_neighborFinset _ _ _).2 (Finset.mem_filter.1 hx).2
      have : ((A.filter (G.Adj v)).card : ℝ) ≤ (G.degree u : ℝ) :=
        Nat.cast_le.2 ((hvmin u hu).trans h2)
      linarith
    -- The removed set carries total weight at most `1`.
    have hsumB : ∑ u ∈ insert v (A.filter (G.Adj v)), ((G.degree u : ℝ) + 1)⁻¹ ≤ 1 := by
      have hpos : (0 : ℝ) < ((A.filter (G.Adj v)).card : ℝ) + 1 := by positivity
      calc ∑ u ∈ insert v (A.filter (G.Adj v)), ((G.degree u : ℝ) + 1)⁻¹
          ≤ (insert v (A.filter (G.Adj v))).card •
              (((A.filter (G.Adj v)).card : ℝ) + 1)⁻¹ :=
            Finset.sum_le_card_nsmul _ _ _ fun u hu => inv_anti₀ hpos (hdeg u (hBA hu))
        _ = 1 := by
            rw [Finset.card_insert_of_notMem hvN, nsmul_eq_mul]
            push_cast
            field_simp
    refine ⟨insert v S, Finset.insert_subset hvA (hSsub.trans Finset.sdiff_subset), ?_, ?_⟩
    · rw [Finset.coe_insert]
      intro x hx y hy hxy
      simp only [Set.mem_insert_iff, Finset.mem_coe] at hx hy
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · exact absurd rfl hxy
        · exact hadj y hy
      · rcases hy with rfl | hy
        · exact fun h => hadj x hx h.symm
        · exact hSind hx hy hxy
    · have hsplit := Finset.sum_sdiff (f := fun u => ((G.degree u : ℝ) + 1)⁻¹) hBA
      rw [Finset.card_insert_of_notMem hvS]
      push_cast
      linarith

/-- **Turán's theorem** (Zhao, Theorem 2.3.6) in its edge-count form: an `n`-vertex
`K (r + 1)`-free graph has at most `(1 - 1 / r) * n ^ 2 / 2` edges. -/
theorem card_edgeFinset_le_of_cliqueFree (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : ℕ} (hr : 1 ≤ r) (h : G.CliqueFree (r + 1)) :
    (G.edgeFinset.card : ℝ) ≤ (1 - 1 / r) * (Fintype.card V : ℝ) ^ 2 / 2 := by
  sorry

end IndependentSets

end ProbMethodCombinatorics
