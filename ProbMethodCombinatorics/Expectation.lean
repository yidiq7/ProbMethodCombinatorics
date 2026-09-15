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
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hV | hV
  · have : IsEmpty V := Fintype.card_eq_zero_iff.1 hV
    have hE : G.edgeFinset.card = 0 := by
      have h2 := SimpleGraph.sum_degrees_eq_twice_card_edges G
      rw [Finset.univ_eq_empty, Finset.sum_empty] at h2
      omega
    rw [hE, hV]
    norm_num
  have : Nonempty V := Fintype.card_pos_iff.1 hV
  have hdeg : ∀ v : V, (G.degree v : ℝ) < (Fintype.card V : ℝ) := fun v => by
    exact_mod_cast G.degree_lt_card_verts v
  -- Caro–Wei in the complement produces a clique of `G`.
  obtain ⟨S, hS, hScard⟩ := exists_isIndepSet_caro_wei Gᶜ
  rw [SimpleGraph.isIndepSet_compl] at hS
  -- `K (r + 1)`-freeness caps the size of that clique by `r`.
  have hSr : (S.card : ℝ) ≤ r := by
    have hn : S.card ≤ r := by
      by_contra hc
      obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (not_le.1 hc)
      exact h T ⟨hS.subset (Finset.coe_subset.2 hTS), hTcard⟩
    exact_mod_cast hn
  -- In the complement, `dᶜ v + 1 = n - d v`.
  have hcompl : ∀ v : V, ((Gᶜ.degree v : ℝ) + 1) = (Fintype.card V : ℝ) - G.degree v := by
    intro v
    have h1 : Gᶜ.degree v + G.degree v + 1 = Fintype.card V := by
      have h2 := SimpleGraph.degree_compl (G := G) (v := v)
      have h3 : G.degree v < Fintype.card V := G.degree_lt_card_verts v
      omega
    have h4 : ((Gᶜ.degree v + G.degree v + 1 : ℕ) : ℝ) = (Fintype.card V : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h1
    push_cast at h4
    linarith
  have hfpos : ∀ v : V, (0 : ℝ) < (Fintype.card V : ℝ) - G.degree v := fun v => by
    have := hdeg v; linarith
  have hsum : ∑ v : V, ((Fintype.card V : ℝ) - G.degree v)⁻¹ ≤ r := by
    refine le_trans (le_of_eq ?_) (hScard.trans hSr)
    exact Finset.sum_congr rfl fun v _ => by rw [hcompl v]
  -- The handshake lemma evaluates `∑ v, (n - d v)`.
  have hsumf : ∑ v : V, ((Fintype.card V : ℝ) - G.degree v)
      = (Fintype.card V : ℝ) ^ 2 - 2 * G.edgeFinset.card := by
    have hd : ((∑ v : V, G.degree v : ℕ) : ℝ) = 2 * G.edgeFinset.card := by
      rw [SimpleGraph.sum_degrees_eq_twice_card_edges]; push_cast; ring
    push_cast at hd
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hd]
    ring
  have hsfpos : (0 : ℝ) < (Fintype.card V : ℝ) ^ 2 - 2 * G.edgeFinset.card := by
    rw [← hsumf]
    exact Finset.sum_pos (fun v _ => hfpos v) Finset.univ_nonempty
  -- Cauchy–Schwarz in Engel form against the constant sequence `1`.
  have htitu := Finset.sq_sum_div_le_sum_sq_div (g := fun v : V => (Fintype.card V : ℝ) - G.degree v)
    Finset.univ (fun _ => (1 : ℝ)) (fun v _ => hfpos v)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, one_pow, one_div] at htitu
  rw [hsumf] at htitu
  have h9 : (Fintype.card V : ℝ) ^ 2
      ≤ r * ((Fintype.card V : ℝ) ^ 2 - 2 * G.edgeFinset.card) :=
    (div_le_iff₀ hsfpos).1 (htitu.trans hsum)
  have hsplit : (1 - 1 / (r : ℝ)) * (Fintype.card V : ℝ) ^ 2 / 2
      = ((r : ℝ) * (Fintype.card V : ℝ) ^ 2 - (Fintype.card V : ℝ) ^ 2) / (2 * r) := by
    field_simp
  rw [hsplit, le_div_iff₀ (by linarith : (0 : ℝ) < 2 * r)]
  nlinarith [h9]

end IndependentSets

/-! ### §2.4 Bounding by sampling -/

/-- Every 3-element `e` lies in at least `n - 3` of the 4-element subsets of `Fin n`:
adjoining any vertex outside `e` gives one, and distinct vertices give distinct sets. -/
private theorem card_le_card_filter_superset {n : ℕ} {e : Finset (Fin n)} (he : e.card = 3) :
    n - 3 ≤ ((Finset.univ.powersetCard 4).filter (fun S => e ⊆ S)).card := by
  have hcard : (Finset.univ \ e).card = n - 3 := by
    rw [Finset.card_sdiff, Finset.inter_univ, he, Finset.card_univ, Fintype.card_fin]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun v => insert v e) ?_ ?_
  · intro v hv
    simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and] at hv
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨Finset.subset_univ _, ?_⟩, Finset.subset_insert _ _⟩
    rw [Finset.card_insert_of_notMem hv, he]
  · intro v hv w hw hvw
    simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and] at hv hw
    have hvw' : insert v e = insert w e := hvw
    have hmem : v ∈ insert w e := hvw' ▸ Finset.mem_insert_self v e
    rcases Finset.mem_insert.1 hmem with h | h
    · exact h
    · exact absurd h hv

/-- A 4-element `S` carries exactly four triples, and tetrahedron-freeness keeps one of them
out of `H`, so at most three edges of `H` sit inside `S`. -/
private theorem card_filter_subset_le_three {n : ℕ} {H : Finset (Finset (Fin n))}
    (h3 : ∀ e ∈ H, e.card = 3)
    (hfree : ∀ S : Finset (Fin n), S.card = 4 → ∃ e ⊆ S, e.card = 3 ∧ e ∉ H)
    {S : Finset (Fin n)} (hS : S.card = 4) :
    (H.filter (fun e => e ⊆ S)).card ≤ 3 := by
  obtain ⟨e₀, he₀S, he₀card, he₀H⟩ := hfree S hS
  have hmem : e₀ ∈ S.powersetCard 3 := Finset.mem_powersetCard.2 ⟨he₀S, he₀card⟩
  have hsub : H.filter (fun e => e ⊆ S) ⊆ (S.powersetCard 3).erase e₀ := by
    intro e he
    rw [Finset.mem_filter] at he
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_powersetCard.2 ⟨he.2, h3 e he.1⟩⟩
    intro h
    exact he₀H (h ▸ he.1)
  have hle := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hmem, Finset.card_powersetCard, hS] at hle
  simpa using hle

/-- **A cheap sampling bound** (Zhao, Proposition 2.4.2; `sources/mit18_226_f22_lec_full.pdf`,
printed p. 22 = PDF p. 28).  A tetrahedron-free 3-uniform hypergraph on `n ≥ 4` vertices has at
most `(3/4) binom(n,3)` edges — stated as `4 |H| ≤ 3 binom(n,3)` so that everything stays in `ℕ`.

`K₄⁽³⁾`, the tetrahedron, is the complete 3-graph on four vertices, so "tetrahedron-free" says
that no four vertices carry all four of their triples.  The hypothesis is phrased as "every
4-set has a triple outside `H`", which is the same thing and is what the proof consumes.

**Route — this is linearity of expectation over a sampled 4-set, and it is short.**  Sample
`S` uniformly among the 4-subsets.  If `|H| = p · binom(n,3)` then the expected number of edges
inside `S` is `4p`; tetrahedron-freeness bounds that count by `3` pointwise, so `4p ≤ 3`.

Equivalently, and this is the form to use in Lean, **double count** the pairs `(S, e)` with
`|S| = 4`, `e ⊆ S`, `e ∈ H`:

* each `e ∈ H` extends to exactly `n - 3` such `S`, giving `|H| (n-3)` pairs;
* each `S` contributes at most `3`, giving at most `3 binom(n,4)`.

So `|H| (n-3) ≤ 3 binom(n,4)`, and `4 binom(n,4) = binom(n,3) (n-3)` — the standard identity —
turns that into the claim.  `Nat.succ_mul_choose_eq` or `Nat.choose_mul_succ_eq` is the
Mathlib-side lever; the identity was verified for `n ≤ 11` before publication.

**The bound is tight at `n = 4`** (it gives `|H| ≤ 3`, and three of the four triples is
achievable), which is worth knowing because it rules out any proof that throws away a constant.
Brute force also confirms `n = 5` gives `|H| ≤ 7`, matching Zhao's Lemma 2.4.3 exactly — that
lemma is **not** stated here, and improving this proposition by sampling five vertices instead of
four is a separate and better node.

Chapter 2 is finite averaging throughout, with no measure theory; see `skills/conventions.md`. -/
theorem card_le_of_tetrahedronFree {n : ℕ} (hn : 4 ≤ n) (H : Finset (Finset (Fin n)))
    (h3 : ∀ e ∈ H, e.card = 3)
    (hfree : ∀ S : Finset (Fin n), S.card = 4 → ∃ e ⊆ S, e.card = 3 ∧ e ∉ H) :
    4 * H.card ≤ 3 * n.choose 3 := by
  have hPcard : (Finset.univ.powersetCard 4 : Finset (Finset (Fin n))).card = n.choose 4 := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  -- Double count the pairs `(S, e)` with `|S| = 4`, `e ⊆ S`, `e ∈ H`.
  have hswap : ∑ e ∈ H, ((Finset.univ.powersetCard 4).filter (fun S => e ⊆ S)).card
      = ∑ S ∈ (Finset.univ.powersetCard 4 : Finset (Finset (Fin n))),
          (H.filter (fun e => e ⊆ S)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hlow : H.card * (n - 3)
      ≤ ∑ e ∈ H, ((Finset.univ.powersetCard 4).filter (fun S => e ⊆ S)).card := by
    have := Finset.card_nsmul_le_sum H
      (fun e => ((Finset.univ.powersetCard 4).filter (fun S => e ⊆ S)).card) (n - 3)
      (fun e he => card_le_card_filter_superset (h3 e he))
    simpa [smul_eq_mul] using this
  have hhigh : ∑ S ∈ (Finset.univ.powersetCard 4 : Finset (Finset (Fin n))),
      (H.filter (fun e => e ⊆ S)).card ≤ 3 * n.choose 4 := by
    have := Finset.sum_le_card_nsmul (Finset.univ.powersetCard 4 : Finset (Finset (Fin n)))
      (fun S => (H.filter (fun e => e ⊆ S)).card) 3
      (fun S hS => card_filter_subset_le_three h3 hfree (Finset.mem_powersetCard.1 hS).2)
    rw [hPcard, smul_eq_mul] at this
    omega
  have hkey : H.card * (n - 3) ≤ 3 * n.choose 4 := by
    rw [hswap] at hlow
    exact hlow.trans hhigh
  -- `4 binom(n,4) = binom(n,3) (n-3)`, and `n - 3 ≥ 1` cancels.
  have hid : n.choose 4 * 4 = n.choose 3 * (n - 3) := Nat.choose_succ_right_eq n 3
  refine Nat.le_of_mul_le_mul_right ?_ (by omega : 0 < n - 3)
  calc 4 * H.card * (n - 3) = 4 * (H.card * (n - 3)) := by ring
    _ ≤ 4 * (3 * n.choose 4) := Nat.mul_le_mul le_rfl hkey
    _ = 3 * (n.choose 4 * 4) := by ring
    _ = 3 * (n.choose 3 * (n - 3)) := by rw [hid]
    _ = 3 * n.choose 3 * (n - 3) := by ring

/-! ### §2.5 Unbalancing lights -/

/-- **Unbalancing lights** (Zhao, Theorem 2.5.1; `sources/mit18_226_f22_lec_full.pdf`, printed
p. 23 = PDF p. 29).  For any `±1` matrix there are sign vectors `x`, `y` with

    ∑ᵢⱼ aᵢⱼ xᵢ yⱼ ≥ n² · binom(n-1, ⌊(n-1)/2⌋) / 2^(n-1).

**Stated exactly, with no `o(1)` and no central limit theorem.**  The book's form is
`(√(2/π) + o(1)) n^{3/2}`, proved by computing `𝔼|Sₙ|` for a sum of `n` iid uniform signs via
the CLT — but Zhao notes in passing that `𝔼|Sₙ| = n 2^{1-n} binom(n-1, ⌊(n-1)/2⌋)` exactly, and
that identity is what is stated here.  It is strictly more informative than the asymptotic form,
which it implies since the right-hand side is `~ √(2/π) n^{3/2}`.

Mathlib does have a central limit theorem (`Probability/CentralLimitTheorem.lean`), so the
book's route is not blocked — the exact route is simply better, and avoids needing
`𝔼|X|` for a standard Gaussian.

**Route.**  The half-random argument: choose the `yⱼ` uniformly and independently, set
`Rᵢ = ∑ⱼ aᵢⱼ yⱼ`, and take `xᵢ` to be the sign of `Rᵢ` (either sign when `Rᵢ = 0`).  Then
`∑ᵢⱼ aᵢⱼ xᵢ yⱼ = ∑ᵢ |Rᵢ|`.  Each `Rᵢ` is distributed as `Sₙ` — a sum of `n` iid uniform signs,
because the `aᵢⱼ` are `±1` — so `𝔼 ∑ᵢ |Rᵢ| = n · 𝔼|Sₙ|`, and averaging gives one choice of `y`
at least that good.  **The `Rᵢ` are not independent of each other, and the proof does not need
them to be**; only the marginal distribution of each is used.

The exact expectation is a binomial identity: `∑ₖ |2k - n| binom(n,k) = n · 2 binom(n-1, ⌊(n-1)/2⌋)`,
which telescopes.  Verified against the direct sum for `n ≤ 14` before publication.

**Tight at `n = 1` and `n = 2`** — brute force over all sign matrices gives worst-case values of
exactly `1` and `2`, matching the bound — so no proof that loses a constant factor will do.
`n = 0` is fine and needs no hypothesis: `ℕ` subtraction makes the bound `0`, and the empty sum
is `0`.

Chapter 2 is finite averaging throughout; no measure theory is needed, and the "random `y`" is a
sum over `Finset` sign vectors. -/
theorem exists_signs_sum_ge {n : ℕ} (a : Fin n → Fin n → ℝ)
    (ha : ∀ i j, a i j = 1 ∨ a i j = -1) :
    ∃ x y : Fin n → ℝ, (∀ i, x i = 1 ∨ x i = -1) ∧ (∀ j, y j = 1 ∨ y j = -1) ∧
      (n : ℝ) ^ 2 * ((n - 1).choose ((n - 1) / 2) : ℝ) / 2 ^ (n - 1)
        ≤ ∑ i, ∑ j, a i j * x i * y j := by
  sorry

end ProbMethodCombinatorics
