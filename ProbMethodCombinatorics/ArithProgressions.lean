import ProbMethodCombinatorics.LocalLemma

/-!
# Section 6.2.11: colouring the integers with no long monochromatic progression

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Theorem 6.2.11 (Beck 1980): for
every `ε > 0` there is a `k₀` and a 2-colouring of `ℤ` with no monochromatic `k`-term
arithmetic progression of common difference below `2 ^ ((1 - ε) k)`, for any `k ≥ k₀`.

The route is the asymmetric local lemma (`lovasz_local_lemma`) on finite subfamilies followed
by `exists_forall_notMem_of_forall_finset`.  A `k`-AP is monochromatic with probability
`2 ^ (1 - k)`, which depends on `k`, so the symmetric form cannot see it; the source takes
weights `x = 2 ^ (-(1 - ε/2) k)`.  Two inputs to that estimate are isolated here: how many
progressions can meet a fixed one, and the convergence of the resulting tail.
-/

namespace ProbMethodCombinatorics

open Finset

/-- The `k`-term arithmetic progression with first term `a` and common difference `d`. -/
def apSet (a d : ℤ) (k : ℕ) : Finset ℤ :=
  (Finset.range k).image fun i : ℕ => a + (i : ℤ) * d

/-- **Tails of `∑ n rⁿ` are eventually small.**  This is the convergence input to Beck's
estimate, where `r = 2 ^ (-ε/2)`: the source needs `∑_{ℓ ≥ k₀} ℓ 2 ^ (1 - εℓ/2) < ε/4`, which
is this bound with the constant absorbed. -/
theorem exists_tail_sum_coe_mul_geometric_lt {r c : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (hc : 0 < c) :
    ∃ N : ℕ, ∑' m : ℕ, ((m + N : ℕ) : ℝ) * r ^ (m + N) < c := by
  -- `∑ n rⁿ` converges for `‖r‖ < 1`, so its tails are the total minus the finite sums
  -- over `range N`, which tend to `0`; any `N` past the threshold for `c` works.
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr₀]
  have hsum : Summable fun n : ℕ => (n : ℝ) * r ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
  have htail : ∀ N : ℕ, ∑' m : ℕ, ((m + N : ℕ) : ℝ) * r ^ (m + N)
      = (∑' n : ℕ, (n : ℝ) * r ^ n) - ∑ j ∈ Finset.range N, (j : ℝ) * r ^ j := by
    intro N
    rw [eq_sub_iff_add_eq, add_comm]
    exact hsum.sum_add_tsum_nat_add N
  have hconst : Filter.Tendsto (fun _ : ℕ => ∑' n : ℕ, (n : ℝ) * r ^ n) Filter.atTop
      (nhds (∑' n : ℕ, (n : ℝ) * r ^ n)) := tendsto_const_nhds
  have key : Filter.Tendsto (fun N : ℕ => ∑' m : ℕ, ((m + N : ℕ) : ℝ) * r ^ (m + N))
      Filter.atTop (nhds 0) := by
    simp only [htail]
    simpa using hconst.sub hsum.hasSum.tendsto_sum_nat
  exact (key.eventually_lt_const hc).exists

/-- **How many progressions can meet a fixed one.**  An `ℓ`-AP of common difference at most `D`
meeting a fixed `k`-AP is determined by the element where they meet, the position of that
element in the `ℓ`-AP, and the common difference — so there are at most `k * ℓ * D` of them.

Stated for an arbitrary finite family of `(first term, common difference)` pairs rather than
for a Finset of progressions, because the progressions live in `ℤ` and there is no finite
ambient to filter. -/
theorem card_le_of_forall_apSet_inter_nonempty {k l : ℕ} {a d : ℤ} {D : ℕ}
    (T : Finset (ℤ × ℤ))
    (hT : ∀ p ∈ T, 0 < p.2 ∧ p.2 ≤ (D : ℤ) ∧ (apSet p.1 p.2 l ∩ apSet a d k).Nonempty) :
    T.card ≤ k * l * D := by
  classical
  -- For each `p = (b, e) ∈ T`, pick a meeting point `F p ∈ apSet a d k` together with its
  -- position `G p < l` inside the `l`-AP, so that `b + (G p) * e = F p`.
  have key : ∀ p ∈ T, ∃ (v : ℤ) (i : ℕ), v ∈ apSet a d k ∧ i < l ∧ p.1 + (i : ℤ) * p.2 = v := by
    intro p hp
    obtain ⟨-, -, v, hv⟩ := hT p hp
    rw [Finset.mem_inter] at hv
    obtain ⟨hv₁, hv₂⟩ := hv
    rw [apSet, Finset.mem_image] at hv₁
    obtain ⟨i, hi, hiv⟩ := hv₁
    exact ⟨v, i, hv₂, Finset.mem_range.mp hi, hiv⟩
  choose! F G hF hG hFG using key
  have hmaps : Set.MapsTo (fun p : ℤ × ℤ => (F p, G p, p.2)) (T : Set (ℤ × ℤ))
      ((apSet a d k ×ˢ Finset.range l ×ˢ Finset.Icc (1 : ℤ) (D : ℤ) : Finset (ℤ × ℕ × ℤ)) :
        Set (ℤ × ℕ × ℤ)) := by
    intro p hp
    have hp : p ∈ T := hp
    obtain ⟨h₁, h₂, -⟩ := hT p hp
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range,
      Finset.mem_Icc]
    exact ⟨hF p hp, hG p hp, by omega, h₂⟩
  have hinj : Set.InjOn (fun p : ℤ × ℤ => (F p, G p, p.2)) (T : Set (ℤ × ℤ)) := by
    intro p hp q hq hpq
    have hp : p ∈ T := hp
    have hq : q ∈ T := hq
    simp only [Prod.mk.injEq] at hpq
    obtain ⟨hv, hi, he⟩ := hpq
    have e₁ := hFG p hp
    have e₂ := hFG q hq
    rw [← hv, ← hi, ← he] at e₂
    exact Prod.ext (add_right_cancel (e₁.trans e₂.symm)) he
  have hk : (apSet a d k).card ≤ k := by
    rw [apSet]
    exact Finset.card_image_le.trans_eq (Finset.card_range k)
  calc T.card
      ≤ (apSet a d k ×ˢ Finset.range l ×ˢ Finset.Icc (1 : ℤ) (D : ℤ)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = (apSet a d k).card * (l * D) := by
        rw [Finset.card_product, Finset.card_product, Finset.card_range, Int.card_Icc]
        simp
    _ ≤ k * (l * D) := Nat.mul_le_mul_right _ hk
    _ = k * l * D := (mul_assoc _ _ _).symm

section Beck

open MeasureTheory

private theorem card_apSet {a d : ℤ} (hd : d ≠ 0) (k : ℕ) : (apSet a d k).card = k := by
  rw [apSet, Finset.card_image_of_injOn, Finset.card_range]
  intro i _ j _ h
  have h' : (i : ℤ) * d = (j : ℤ) * d := by
    simpa using h
  exact_mod_cast mul_right_cancel₀ hd h'

/-- A uniform random two-colouring makes a nonempty set `e` monochromatic with probability at
most `2 ^ (1 - |e|)`.  A deliberate copy of the `private` lemma of the same purpose in
`LocalLemma`, which module-scoped privacy puts out of reach here. -/
private theorem uniformColoring_monochromatic_toReal_le' {α : Type*} [Fintype α] [DecidableEq α]
    (e : Finset α) (he : 1 ≤ e.card) :
    (uniformColoring α {x : α → Bool | ∀ u ∈ e, ∀ v ∈ e, x u = x v}).toReal
      ≤ 1 / 2 ^ (e.card - 1) := by
  obtain ⟨u₀, hu₀⟩ : e.Nonempty := Finset.card_pos.1 he
  have hsub : {x : α → Bool | ∀ u ∈ e, ∀ v ∈ e, x u = x v}
      ⊆ {x : α → Bool | ∀ u ∈ e, x u = true} ∪ {x : α → Bool | ∀ u ∈ e, x u = false} := by
    intro x hx
    cases hb : x u₀
    · right; intro u hu; rw [hx u hu u₀ hu₀, hb]
    · left; intro u hu; rw [hx u hu u₀ hu₀, hb]
  have hle : uniformColoring α {x : α → Bool | ∀ u ∈ e, ∀ v ∈ e, x u = x v}
      ≤ 2 * (2 : ENNReal)⁻¹ ^ e.card :=
    calc uniformColoring α {x : α → Bool | ∀ u ∈ e, ∀ v ∈ e, x u = x v}
        ≤ uniformColoring α ({x : α → Bool | ∀ u ∈ e, x u = true}
            ∪ {x : α → Bool | ∀ u ∈ e, x u = false}) := measure_mono hsub
      _ ≤ uniformColoring α {x : α → Bool | ∀ u ∈ e, x u = true}
            + uniformColoring α {x : α → Bool | ∀ u ∈ e, x u = false} := measure_union_le _ _
      _ = 2 * (2 : ENNReal)⁻¹ ^ e.card := by
          rw [uniformColoring_const _ true, uniformColoring_const _ false]; ring
  have htop : (2 : ENNReal) * (2 : ENNReal)⁻¹ ^ e.card ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (by norm_num))
  have hreal : (uniformColoring α {x : α → Bool | ∀ u ∈ e, ∀ v ∈ e, x u = x v}).toReal
      ≤ 2 * ((2 : ℝ)⁻¹) ^ e.card := by simpa using ENNReal.toReal_mono htop hle
  have hsplit : (2 : ℝ) ^ e.card = 2 ^ (e.card - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  have hval : 2 * ((2 : ℝ)⁻¹) ^ e.card = 1 / 2 ^ (e.card - 1) := by
    have hpos : (0 : ℝ) < 2 ^ (e.card - 1) := by positivity
    rw [inv_pow, hsplit]
    field_simp
  rwa [hval] at hreal

/-- The monochromatic events of a family of finite sets have the meeting relation as a
dependency graph. -/
private theorem isDependencyGraph_monochromatic {γ ι : Type*} [Fintype γ] [DecidableEq γ]
    [DecidableEq ι] (T : ι → Finset γ) (A : ι → Set (γ → Bool))
    (hA : ∀ i x, x ∈ A i ↔ ∀ u ∈ T i, ∀ v ∈ T i, x u = x v)
    (N : ι → Finset ι) (hN : ∀ i q, q ∈ N i ↔ q ≠ i ∧ (T i ∩ T q).Nonempty) :
    IsDependencyGraph (uniformColoring γ) A N := by
  have hAinv : ∀ (j : ι) (x y : γ → Bool),
      (∀ a ∈ T j, x a = y a) → (x ∈ A j ↔ y ∈ A j) := by
    intro j x y hxy
    rw [hA, hA]
    constructor
    · intro hx u hu v hv; rw [← hxy u hu, ← hxy v hv]; exact hx u hu v hv
    · intro hy u hu v hv; rw [hxy u hu, hxy v hv]; exact hy u hu v hv
  intro i s hs g
  refine uniformColoring_inter_eq_mul (T i) (A i) (pattern A s g) (hAinv i) ?_
  intro x y hxy
  have hj : ∀ j ∈ s,
      (x ∈ (if g j then A j else (A j)ᶜ) ↔ y ∈ (if g j then A j else (A j)ᶜ)) := by
    intro j hjs
    obtain ⟨hjne, hjN⟩ := hs j hjs
    have hdisj : Disjoint (T i) (T j) := by
      by_contra hcon
      exact hjN ((hN i j).2 ⟨hjne, Finset.not_disjoint_iff_nonempty_inter.1 hcon⟩)
    have hiff := hAinv j x y fun a ha =>
      hxy a fun hai => (Finset.disjoint_left.1 hdisj hai) ha
    by_cases hg : g j
    · rw [if_pos hg]; exact hiff
    · rw [if_neg hg]; exact not_congr hiff
  simp only [pattern, Set.mem_iInter]
  exact ⟨fun h j hjs => (hj j hjs).1 (h j hjs), fun h j hjs => (hj j hjs).2 (h j hjs)⟩

/-- The local lemma packaged for the monochromatic events of a family of finite sets: weights
dominating `2 ^ (1 - |T i|)` against the meeting neighbourhoods give a colouring in which no
`T i` is monochromatic. -/
private theorem exists_coloring_not_monochromatic {γ ι : Type*} [Fintype γ] [DecidableEq γ]
    [Fintype ι] [DecidableEq ι] (T : ι → Finset γ) (x : ι → ℝ)
    (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1) (hcard : ∀ i, 1 ≤ (T i).card)
    (hbound : ∀ i, 1 / 2 ^ ((T i).card - 1) ≤ x i *
      ∏ q ∈ Finset.univ.filter (fun q => q ≠ i ∧ (T i ∩ T q).Nonempty), (1 - x q)) :
    ∃ c : γ → Bool, ∀ i, ∃ u ∈ T i, ∃ v ∈ T i, c u ≠ c v := by
  classical
  set A : ι → Set (γ → Bool) := fun i => {y : γ → Bool | ∀ u ∈ T i, ∀ v ∈ T i, y u = y v}
  set N : ι → Finset ι :=
    fun i => Finset.univ.filter (fun q => q ≠ i ∧ (T i ∩ T q).Nonempty) with hNdef
  have hAmeas : ∀ i, MeasurableSet (A i) := fun _ => (Set.toFinite _).measurableSet
  have hNdep : IsDependencyGraph (uniformColoring γ) A N :=
    isDependencyGraph_monochromatic T A (fun _ _ => Iff.rfl) N (by simp [hNdef])
  have hp : ∀ i, (uniformColoring γ (A i)).toReal ≤ x i * ∏ q ∈ N i, (1 - x q) := fun i =>
    le_trans (uniformColoring_monochromatic_toReal_le' (T i) (hcard i)) (hbound i)
  have hpos := lovasz_local_lemma A hAmeas N hNdep x hx₀ hx₁ hp
  have hprodpos : 0 < ∏ i, (1 - x i) :=
    Finset.prod_pos fun i _ => by linarith [hx₁ i]
  rcases Set.eq_empty_or_nonempty (⋂ i, (A i)ᶜ) with hempty | ⟨y, hy⟩
  · rw [hempty] at hpos
    simp only [measure_empty, ENNReal.toReal_zero] at hpos
    linarith
  · refine ⟨y, fun i => ?_⟩
    simp only [Set.mem_iInter, Set.mem_compl_iff] at hy
    by_contra hcon
    refine hy i ?_
    show ∀ u ∈ T i, ∀ v ∈ T i, y u = y v
    intro u hu v hv
    by_contra hne
    exact hcon ⟨u, hu, v, hv, hne⟩

private theorem exp_neg_two_mul_le_one_sub {t : ℝ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1 / 2) :
    Real.exp (-(2 * t)) ≤ 1 - t := by
  have hexp : 2 * t + 1 ≤ Real.exp (2 * t) := Real.add_one_le_exp _
  have hone : (0 : ℝ) < 2 * t + 1 := by linarith
  have hinv : Real.exp (-(2 * t)) ≤ 1 / (2 * t + 1) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le hone hexp
  have hmul : 1 / (2 * t + 1) ≤ 1 - t := by
    rw [div_le_iff₀ hone]
    nlinarith
  linarith

private theorem two_rpow_weight_le_half {ε : ℝ} (hε1 : ε ≤ 1) {l : ℕ} (hl : 2 ≤ l) :
    (2 : ℝ) ^ (-(1 - ε / 2) * (l : ℝ)) ≤ 1 / 2 := by
  have hl' : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hexp : -(1 - ε / 2) * (l : ℝ) ≤ -1 := by nlinarith
  calc (2 : ℝ) ^ (-(1 - ε / 2) * (l : ℝ))
      ≤ (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num

private theorem two_rpow_mul_two_rpow {ε : ℝ} (l : ℕ) :
    (2 : ℝ) ^ ((1 - ε) * (l : ℝ)) * (2 : ℝ) ^ (-(1 - ε / 2) * (l : ℝ))
      = ((2 : ℝ) ^ (-ε / 2)) ^ l := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (-ε / 2)) l, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_add (by norm_num)]
  congr 1
  ring

/-- A finite sum of `ℓ rᶫ` over lengths past the threshold `Nt` is below the tail bound. -/
private theorem sum_coe_mul_pow_lt {r c : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) {Nt : ℕ}
    (htail : ∑' m : ℕ, ((m + Nt : ℕ) : ℝ) * r ^ (m + Nt) < c)
    (L : Finset ℕ) (hL : ∀ l ∈ L, Nt ≤ l) :
    ∑ l ∈ L, (l : ℝ) * r ^ l < c := by
  have hnonneg : ∀ l : ℕ, (0 : ℝ) ≤ (l : ℝ) * r ^ l := fun l =>
    mul_nonneg (Nat.cast_nonneg l) (pow_nonneg hr₀ l)
  have hsum : Summable fun n : ℕ => (n : ℝ) * r ^ n := by
    have hnorm : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr₀]
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
  have hshift : Summable fun m : ℕ => ((m + Nt : ℕ) : ℝ) * r ^ (m + Nt) :=
    (summable_nat_add_iff Nt).2 hsum
  set M := L.sup id + 1
  have hsub : L ⊆ Finset.Ico Nt M := by
    intro l hl
    rw [Finset.mem_Ico]
    exact ⟨hL l hl, Nat.lt_succ_of_le (Finset.le_sup (f := id) hl)⟩
  have h1 : ∑ l ∈ L, (l : ℝ) * r ^ l ≤ ∑ l ∈ Finset.Ico Nt M, (l : ℝ) * r ^ l :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => hnonneg i
  have h2 : ∑ l ∈ Finset.Ico Nt M, (l : ℝ) * r ^ l
      = ∑ m ∈ Finset.range (M - Nt), ((m + Nt : ℕ) : ℝ) * r ^ (m + Nt) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [add_comm Nt m]
  have h3 : ∑ m ∈ Finset.range (M - Nt), ((m + Nt : ℕ) : ℝ) * r ^ (m + Nt)
      ≤ ∑' m : ℕ, ((m + Nt : ℕ) : ℝ) * r ^ (m + Nt) :=
    hshift.sum_le_tsum _ (fun i _ => hnonneg (i + Nt))
  linarith

/-- Progressions of a fixed length `l` meeting a fixed `k`-AP, with common difference at most
`D`: there are at most `k * l * D` of them.  A repackaging of
`card_le_of_forall_apSet_inter_nonempty` for families of `(first term, difference, length)`
triples. -/
private theorem card_le_of_length_eq (a d : ℤ) {k l D : ℕ} (G : Finset (ℤ × ℤ × ℕ))
    (hG : ∀ q ∈ G, q.2.2 = l ∧ 0 < q.2.1 ∧ q.2.1 ≤ (D : ℤ) ∧
        (apSet q.1 q.2.1 q.2.2 ∩ apSet a d k).Nonempty) :
    G.card ≤ k * l * D := by
  classical
  have hinj : Set.InjOn (fun q : ℤ × ℤ × ℕ => (q.1, q.2.1)) (G : Set (ℤ × ℤ × ℕ)) := by
    intro p hp q hq hpq
    have hp' : p ∈ G := hp
    have hq' : q ∈ G := hq
    obtain ⟨hl₁, -⟩ := hG p hp'
    obtain ⟨hl₂, -⟩ := hG q hq'
    simp only [Prod.mk.injEq] at hpq
    exact Prod.ext hpq.1 (Prod.ext hpq.2 (hl₁.trans hl₂.symm))
  rw [← Finset.card_image_of_injOn hinj]
  refine card_le_of_forall_apSet_inter_nonempty (a := a) (d := d) _ ?_
  intro t ht
  rw [Finset.mem_image] at ht
  obtain ⟨q, hq, rfl⟩ := ht
  obtain ⟨hl, hpos, hle, hne⟩ := hG q hq
  refine ⟨hpos, hle, ?_⟩
  rwa [hl] at hne

/-- **The weight sum over a neighbourhood.**  The progressions meeting a fixed `k`-AP carry
total weight at most `ε k / 8`: grouping them by length `l` there are at most
`k * l * 2 ^ ((1 - ε) l)` of each length, and the resulting series is the geometric tail. -/
private theorem sum_weight_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {Nt : ℕ} (k₀ : ℕ)
    (htail : ∑' m : ℕ, ((m + Nt : ℕ) : ℝ) * ((2 : ℝ) ^ (-ε / 2)) ^ (m + Nt) < ε / 16)
    (hNt : Nt ≤ k₀) (a d : ℤ) {k : ℕ} (G : Finset (ℤ × ℤ × ℕ))
    (hG : ∀ q ∈ G, k₀ ≤ q.2.2 ∧ 0 < q.2.1 ∧ (q.2.1 : ℝ) < (2 : ℝ) ^ ((1 - ε) * (q.2.2 : ℝ)) ∧
        (apSet q.1 q.2.1 q.2.2 ∩ apSet a d k).Nonempty) :
    ∑ q ∈ G, (2 : ℝ) ^ (-(1 - ε / 2) * (q.2.2 : ℝ)) ≤ ε * k / 8 := by
  classical
  set r : ℝ := (2 : ℝ) ^ (-ε / 2)
  have hr₀ : (0 : ℝ) ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr₁ : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set L : Finset ℕ := G.image (fun q => q.2.2) with hLdef
  have hgroup : ∑ q ∈ G, (2 : ℝ) ^ (-(1 - ε / 2) * (q.2.2 : ℝ))
      = ∑ l ∈ L, ∑ q ∈ G.filter (fun q => q.2.2 = l),
          (2 : ℝ) ^ (-(1 - ε / 2) * (q.2.2 : ℝ)) :=
    (Finset.sum_fiberwise_of_maps_to (fun q hq => Finset.mem_image_of_mem _ hq) _).symm
  have hkey : ∀ l ∈ L, ∑ q ∈ G.filter (fun q => q.2.2 = l),
      (2 : ℝ) ^ (-(1 - ε / 2) * (q.2.2 : ℝ)) ≤ 2 * (k : ℝ) * ((l : ℝ) * r ^ l) := by
    intro l _
    set w : ℝ := (2 : ℝ) ^ (-(1 - ε / 2) * (l : ℝ)) with hwdef
    have hw₀ : (0 : ℝ) < w := Real.rpow_pos_of_pos (by norm_num) _
    set t : ℝ := (2 : ℝ) ^ ((1 - ε) * (l : ℝ)) with htdef
    have ht₁ : (1 : ℝ) ≤ t := by
      have hnn : (0 : ℝ) ≤ (1 - ε) * (l : ℝ) :=
        mul_nonneg (by linarith) (Nat.cast_nonneg l)
      calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := by rw [Real.rpow_zero]
        _ ≤ t := Real.rpow_le_rpow_of_exponent_le (by norm_num) hnn
    have hD : ((⌈t⌉₊ : ℕ) : ℝ) ≤ 2 * t := by
      have := Nat.ceil_lt_add_one (le_trans zero_le_one ht₁)
      linarith
    have hcard : (G.filter (fun q => q.2.2 = l)).card ≤ k * l * ⌈t⌉₊ := by
      refine card_le_of_length_eq a d _ fun q hq => ?_
      rw [Finset.mem_filter] at hq
      obtain ⟨hqG, hql⟩ := hq
      obtain ⟨-, hpos, hlt, hint⟩ := hG q hqG
      refine ⟨hql, hpos, ?_, hint⟩
      have hlt' : (q.2.1 : ℝ) ≤ ((⌈t⌉₊ : ℕ) : ℝ) := by
        rw [htdef, ← hql]
        exact le_trans hlt.le (Nat.le_ceil _)
      exact_mod_cast hlt'
    have hcard' : ((G.filter (fun q => q.2.2 = l)).card : ℝ) ≤ (k : ℝ) * (l : ℝ) * (2 * t) := by
      have h1 : ((G.filter (fun q => q.2.2 = l)).card : ℝ)
          ≤ (k : ℝ) * (l : ℝ) * ((⌈t⌉₊ : ℕ) : ℝ) := by
        have := hcard
        push_cast [← Nat.cast_le (α := ℝ)] at this
        linarith [this]
      have hkl : (0 : ℝ) ≤ (k : ℝ) * (l : ℝ) := by positivity
      have hmul : (k : ℝ) * (l : ℝ) * ((⌈t⌉₊ : ℕ) : ℝ) ≤ (k : ℝ) * (l : ℝ) * (2 * t) :=
        mul_le_mul_of_nonneg_left hD hkl
      linarith
    calc ∑ q ∈ G.filter (fun q => q.2.2 = l), (2 : ℝ) ^ (-(1 - ε / 2) * (q.2.2 : ℝ))
        = ∑ _q ∈ G.filter (fun q => q.2.2 = l), w := by
          refine Finset.sum_congr rfl fun q hq => ?_
          rw [hwdef, (Finset.mem_filter.mp hq).2]
      _ = ((G.filter (fun q => q.2.2 = l)).card : ℝ) * w := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((k : ℝ) * (l : ℝ) * (2 * t)) * w := by
          exact mul_le_mul_of_nonneg_right hcard' hw₀.le
      _ = 2 * (k : ℝ) * ((l : ℝ) * (t * w)) := by ring
      _ = 2 * (k : ℝ) * ((l : ℝ) * r ^ l) := by rw [htdef, hwdef, two_rpow_mul_two_rpow]
  have hLbound : ∑ l ∈ L, (l : ℝ) * r ^ l < ε / 16 := by
    refine sum_coe_mul_pow_lt hr₀ hr₁ htail L fun l hl => ?_
    rw [hLdef, Finset.mem_image] at hl
    obtain ⟨q, hqG, rfl⟩ := hl
    exact le_trans hNt (hG q hqG).1
  calc ∑ q ∈ G, (2 : ℝ) ^ (-(1 - ε / 2) * (q.2.2 : ℝ))
      = ∑ l ∈ L, ∑ q ∈ G.filter (fun q => q.2.2 = l),
          (2 : ℝ) ^ (-(1 - ε / 2) * (q.2.2 : ℝ)) := hgroup
    _ ≤ ∑ l ∈ L, 2 * (k : ℝ) * ((l : ℝ) * r ^ l) := Finset.sum_le_sum hkey
    _ = 2 * (k : ℝ) * ∑ l ∈ L, (l : ℝ) * r ^ l := by rw [Finset.mul_sum]
    _ ≤ 2 * (k : ℝ) * (ε / 16) := by
        have hknn : (0 : ℝ) ≤ 2 * (k : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left hLbound.le hknn
    _ = ε * k / 8 := by ring

/-- **The numeric heart of the estimate.**  With `ε k ≥ 16` the monochromatic probability
`2 ^ (1 - k)` fits under the weight `2 ^ (-(1 - ε/2) k)` times the exponential loss
`exp (-ε k / 4)` coming from the neighbourhood product. -/
private theorem two_pow_le_weight_mul_exp {ε : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (h16 : 16 ≤ ε * (k : ℝ)) :
    1 / 2 ^ (k - 1) ≤ (2 : ℝ) ^ (-(1 - ε / 2) * (k : ℝ)) * Real.exp (-(ε * (k : ℝ) / 4)) := by
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    have : (1 : ℕ) ≤ k := hk
    push_cast [Nat.cast_sub this]
    ring
  have hL₁ : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hL₂ : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hleft : (1 : ℝ) / 2 ^ (k - 1) = Real.exp (-(Real.log 2 * ((k : ℝ) - 1))) := by
    rw [← Real.rpow_natCast (2 : ℝ) (k - 1), hcast,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.exp_neg, one_div]
  have hright : (2 : ℝ) ^ (-(1 - ε / 2) * (k : ℝ)) * Real.exp (-(ε * (k : ℝ) / 4))
      = Real.exp (Real.log 2 * (-(1 - ε / 2) * (k : ℝ)) + -(ε * (k : ℝ) / 4)) := by
    rw [Real.exp_add, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [hleft, hright]
  refine Real.exp_le_exp.2 ?_
  have hprod : (0 : ℝ) ≤ (Real.log 2 - 0.6931471803) * (ε * (k : ℝ)) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [hprod]

/-- Beck's theorem for a finite family, for `ε ≤ 1`.  The general case reduces to this one, and
`ε ≤ 1` is what makes the weights `2 ^ (-(1 - ε/2) k)` lie below `1/2` and the count of
progressions of a given length grow slower than the weights decay. -/
private theorem exists_twoColoring_of_le_one {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ k₀ : ℕ, ∀ F : Finset (ℤ × ℤ × ℕ),
      (∀ p ∈ F, k₀ ≤ p.2.2 ∧ 0 < p.2.1 ∧ (p.2.1 : ℝ) < (2 : ℝ) ^ ((1 - ε) * (p.2.2 : ℝ))) →
      ∃ c : ℤ → Bool, ∀ p ∈ F,
        ∃ u ∈ apSet p.1 p.2.1 p.2.2, ∃ v ∈ apSet p.1 p.2.1 p.2.2, c u ≠ c v := by
  classical
  have hr₀ : (0 : ℝ) ≤ (2 : ℝ) ^ (-ε / 2) := Real.rpow_nonneg (by norm_num) _
  have hr₁ : (2 : ℝ) ^ (-ε / 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨Nt, htail⟩ :=
    exists_tail_sum_coe_mul_geometric_lt hr₀ hr₁ (show (0 : ℝ) < ε / 16 by linarith)
  refine ⟨max Nt ⌈16 / ε⌉₊, fun F hF => ?_⟩
  set V : Finset ℤ := F.biUnion (fun p => apSet p.1 p.2.1 p.2.2)
  set T : {p // p ∈ F} → Finset {z // z ∈ V} :=
    fun i => (apSet i.1.1 i.1.2.1 i.1.2.2).subtype (fun z => z ∈ V) with hTdef
  set y : {p // p ∈ F} → ℝ := fun i => (2 : ℝ) ^ (-(1 - ε / 2) * (i.1.2.2 : ℝ))
  -- Every progression of the family lies inside the vertex set `V`.
  have hsubV : ∀ i : {p // p ∈ F}, apSet i.1.1 i.1.2.1 i.1.2.2 ⊆ V := fun i =>
    Finset.subset_biUnion_of_mem (fun p => apSet p.1 p.2.1 p.2.2) i.2
  have hmemT : ∀ (i : {p // p ∈ F}) (z : {z // z ∈ V}),
      z ∈ T i ↔ (z : ℤ) ∈ apSet i.1.1 i.1.2.1 i.1.2.2 := by
    intro i z
    rw [hTdef]
    exact Finset.mem_subtype
  -- `ε k ≥ 16`, hence `k ≥ 16`, for every length in the family.
  have h16 : ∀ i : {p // p ∈ F}, 16 ≤ ε * (i.1.2.2 : ℝ) := by
    intro i
    have hceil : (⌈16 / ε⌉₊ : ℝ) ≤ (i.1.2.2 : ℝ) := by
      have : ⌈16 / ε⌉₊ ≤ i.1.2.2 := le_trans (le_max_right _ _) (hF i.1 i.2).1
      exact_mod_cast this
    have hdiv : 16 / ε ≤ (i.1.2.2 : ℝ) := le_trans (Nat.le_ceil _) hceil
    rw [div_le_iff₀ hε] at hdiv
    linarith
  have hlen : ∀ i : {p // p ∈ F}, 16 ≤ i.1.2.2 := by
    intro i
    have h := h16 i
    have : (16 : ℝ) ≤ (i.1.2.2 : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) i.1.2.2]
    exact_mod_cast this
  have hTcard : ∀ i : {p // p ∈ F}, (T i).card = i.1.2.2 := by
    intro i
    rw [hTdef]
    rw [Finset.card_subtype, Finset.filter_true_of_mem (fun z hz => hsubV i hz)]
    exact card_apSet (ne_of_gt (hF i.1 i.2).2.1) _
  have hy₀ : ∀ i, 0 ≤ y i := fun i => Real.rpow_nonneg (by norm_num) _
  have hyhalf : ∀ i, y i ≤ 1 / 2 := fun i =>
    two_rpow_weight_le_half hε1 (le_trans (by norm_num) (hlen i))
  have hy₁ : ∀ i, y i < 1 := fun i => lt_of_le_of_lt (hyhalf i) (by norm_num)
  -- The local-lemma hypothesis.
  have hbound : ∀ i : {p // p ∈ F}, 1 / 2 ^ ((T i).card - 1) ≤ y i *
      ∏ q ∈ Finset.univ.filter (fun q => q ≠ i ∧ (T i ∩ T q).Nonempty), (1 - y q) := by
    intro i
    set W : Finset {p // p ∈ F} :=
      Finset.univ.filter (fun q => q ≠ i ∧ (T i ∩ T q).Nonempty) with hWdef
    have hinjval : Set.InjOn (fun q : {p // p ∈ F} => (q : ℤ × ℤ × ℕ)) (W : Set {p // p ∈ F}) :=
      Function.Injective.injOn fun a b h => Subtype.ext h
    -- the neighbourhood weight sum
    have hsumW : ∑ q ∈ W, y q ≤ ε * (i.1.2.2 : ℝ) / 8 := by
      have hrw : ∑ q ∈ W, y q
          = ∑ q ∈ W.image (fun q : {p // p ∈ F} => (q : ℤ × ℤ × ℕ)),
              (2 : ℝ) ^ (-(1 - ε / 2) * (q.2.2 : ℝ)) := by
        rw [Finset.sum_image hinjval]
      rw [hrw]
      refine sum_weight_le hε hε1 (max Nt ⌈16 / ε⌉₊) htail (le_max_left _ _)
        i.1.1 i.1.2.1 _ fun q hq => ?_
      rw [Finset.mem_image] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      rw [hWdef, Finset.mem_filter] at hq'
      obtain ⟨-, -, z, hz⟩ := hq'
      rw [Finset.mem_inter] at hz
      refine ⟨(hF q'.1 q'.2).1, (hF q'.1 q'.2).2.1, (hF q'.1 q'.2).2.2, z, ?_⟩
      rw [Finset.mem_inter]
      exact ⟨(hmemT q' z).1 hz.2, (hmemT i z).1 hz.1⟩
    -- the neighbourhood product
    have hprodW : Real.exp (-(ε * (i.1.2.2 : ℝ) / 4)) ≤ ∏ q ∈ W, (1 - y q) := by
      have hstep : ∏ q ∈ W, Real.exp (-(2 * y q)) ≤ ∏ q ∈ W, (1 - y q) :=
        Finset.prod_le_prod (fun q _ => (Real.exp_pos _).le)
          (fun q _ => exp_neg_two_mul_le_one_sub (hy₀ q) (hyhalf q))
      have hexp : ∏ q ∈ W, Real.exp (-(2 * y q)) = Real.exp (-(2 * ∑ q ∈ W, y q)) := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      rw [hexp] at hstep
      refine le_trans (Real.exp_le_exp.2 ?_) hstep
      linarith
    -- combine
    have hnum : 1 / 2 ^ (i.1.2.2 - 1)
        ≤ y i * Real.exp (-(ε * (i.1.2.2 : ℝ) / 4)) :=
      two_pow_le_weight_mul_exp (le_trans (by norm_num) (hlen i)) (h16 i)
    rw [hTcard i]
    exact le_trans hnum (mul_le_mul_of_nonneg_left hprodW (hy₀ i))
  obtain ⟨c₀, hc₀⟩ := exists_coloring_not_monochromatic T y hy₀ hy₁
    (fun i => by rw [hTcard i]; exact le_trans (by norm_num) (hlen i)) hbound
  refine ⟨fun z => if h : z ∈ V then c₀ ⟨z, h⟩ else false, fun p hp => ?_⟩
  obtain ⟨u, hu, v, hv, huv⟩ := hc₀ ⟨p, hp⟩
  refine ⟨(u : ℤ), (hmemT ⟨p, hp⟩ u).1 hu, (v : ℤ), (hmemT ⟨p, hp⟩ v).1 hv, ?_⟩
  show (if h : (u : ℤ) ∈ V then c₀ ⟨(u : ℤ), h⟩ else false)
      ≠ (if h : (v : ℤ) ∈ V then c₀ ⟨(v : ℤ), h⟩ else false)
  rw [dif_pos u.2, dif_pos v.2]
  exact huv

end Beck

/-- **Beck's theorem for finitely many progressions.**  The asymmetric local lemma reaches
exactly this far; `exists_forall_notMem_of_forall_finset` carries it to all of `ℤ` below.

A progression is named by its first term, its common difference, and its length, so the
family is a `Finset (ℤ × ℤ × ℕ)`.  Note `k₀` is chosen before the family, which is what the
compactness step needs. -/
theorem exists_twoColoring_forall_mem_not_monochromatic {ε : ℝ} (hε : 0 < ε) :
    ∃ k₀ : ℕ, ∀ F : Finset (ℤ × ℤ × ℕ),
      (∀ p ∈ F, k₀ ≤ p.2.2 ∧ 0 < p.2.1 ∧ (p.2.1 : ℝ) < (2 : ℝ) ^ ((1 - ε) * (p.2.2 : ℝ))) →
      ∃ c : ℤ → Bool, ∀ p ∈ F,
        ∃ u ∈ apSet p.1 p.2.1 p.2.2, ∃ v ∈ apSet p.1 p.2.1 p.2.2, c u ≠ c v := by
  obtain ⟨k₀, hk₀⟩ :=
    exists_twoColoring_of_le_one (ε := min ε 1) (lt_min hε one_pos) (min_le_right _ _)
  refine ⟨k₀, fun F hF => hk₀ F fun p hp => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := hF p hp
  refine ⟨h₁, h₂, lt_of_lt_of_le h₃ ?_⟩
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hmin : min ε 1 ≤ ε := min_le_left _ _
  nlinarith [Nat.cast_nonneg (α := ℝ) p.2.2]

/-- **Theorem 6.2.11** (Beck 1980): for every `ε > 0` there is a `k₀` and a 2-colouring of `ℤ`
with no monochromatic `k`-term arithmetic progression of common difference below
`2 ^ ((1 - ε) k)`, for any `k ≥ k₀`. -/
theorem exists_twoColoring_no_monochromatic_ap {ε : ℝ} (hε : 0 < ε) :
    ∃ k₀ : ℕ, ∃ c : ℤ → Bool, ∀ (a d : ℤ) (k : ℕ), k₀ ≤ k → 0 < d →
      (d : ℝ) < (2 : ℝ) ^ ((1 - ε) * (k : ℝ)) →
      ∃ u ∈ apSet a d k, ∃ v ∈ apSet a d k, c u ≠ c v := by
  classical
  obtain ⟨k₀, hk₀⟩ := exists_twoColoring_forall_mem_not_monochromatic hε
  refine ⟨k₀, ?_⟩
  -- Index the bad events by the progressions the statement constrains: those of length at
  -- least `k₀` whose common difference is positive and below the bound.
  set E : {p : ℤ × ℤ × ℕ //
      k₀ ≤ p.2.2 ∧ 0 < p.2.1 ∧ (p.2.1 : ℝ) < (2 : ℝ) ^ ((1 - ε) * (p.2.2 : ℝ))} →
        Set (ℤ → Bool) :=
    fun j => {c : ℤ → Bool | ∀ u ∈ apSet j.1.1 j.1.2.1 j.1.2.2,
      ∀ v ∈ apSet j.1.1 j.1.2.1 j.1.2.2, c u = c v} with hEdef
  -- Whether a progression is monochromatic only depends on the colours of its terms.
  have hdet : ∀ (j : {p : ℤ × ℤ × ℕ //
      k₀ ≤ p.2.2 ∧ 0 < p.2.1 ∧ (p.2.1 : ℝ) < (2 : ℝ) ^ ((1 - ε) * (p.2.2 : ℝ))})
      (x y : ℤ → Bool),
      (∀ i ∈ apSet j.1.1 j.1.2.1 j.1.2.2, x i = y i) → (x ∈ E j ↔ y ∈ E j) := by
    intro j x y hxy
    simp only [hEdef, Set.mem_ofPred_eq]
    constructor
    · intro hx u hu v hv; rw [← hxy u hu, ← hxy v hv]; exact hx u hu v hv
    · intro hy u hu v hv; rw [hxy u hu, hxy v hv]; exact hy u hu v hv
  -- Finitely many progressions at a time is exactly the previous theorem.
  have hfin : ∀ F : Finset {p : ℤ × ℤ × ℕ //
      k₀ ≤ p.2.2 ∧ 0 < p.2.1 ∧ (p.2.1 : ℝ) < (2 : ℝ) ^ ((1 - ε) * (p.2.2 : ℝ))},
      ∃ x : ℤ → Bool, ∀ j ∈ F, x ∉ E j := by
    intro F
    obtain ⟨c, hc⟩ := hk₀ (F.image Subtype.val) (by
      intro p hp
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hp
      exact j.2)
    refine ⟨c, fun j hj => ?_⟩
    obtain ⟨u, hu, v, hv, huv⟩ := hc j.1 (Finset.mem_image_of_mem _ hj)
    intro hmono
    exact huv (hmono u hu v hv)
  -- Compactness glues the finite colourings into a single colouring of all of `ℤ`.
  obtain ⟨c, hc⟩ := exists_forall_notMem_of_forall_finset (α := fun _ : ℤ => Bool) E
    (fun j => apSet j.1.1 j.1.2.1 j.1.2.2) hdet hfin
  refine ⟨c, fun a d k hk hd hlt => ?_⟩
  have hcj := hc ⟨(a, d, k), hk, hd, hlt⟩
  simp only [hEdef, Set.mem_ofPred_eq] at hcj
  push Not at hcj
  exact hcj

end ProbMethodCombinatorics
