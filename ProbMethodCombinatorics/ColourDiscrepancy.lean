import ProbMethodCombinatorics.PolyLowerBound

/-!
# Theorem 2.5.2: red/blue discrepancy in a `k`-partite colouring

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Theorem 2.5.2.

`V` is split into `k` parts of size `n`, the `k`-subsets of `V` are coloured red or blue, and
every *transversal* `k`-set — one vertex from each part — is blue.  Then some `S ⊆ V` has its
red and blue counts differing by more than `c k · nᵏ`, with `c k > 0` depending only on `k`.

The proof picks `S` by keeping each vertex of part `i` independently with probability `pᵢ`.
The expected red/blue difference is then a polynomial in `p₁, …, p_k` whose `p₁p₂⋯p_k`
coefficient is `nᵏ` (that is exactly the transversal hypothesis) and whose other coefficients
are bounded by `nᵏ` in absolute value.  Dividing through by `nᵏ` puts it in the family
`exists_pos_forall_exists_abs_eval_ge` handles, and the constant that lemma supplies is
uniform in the colouring — which is why `c k` does not depend on it.

The vertex set is modelled as `Fin k × Fin n`, so part `i` is the fibre over `i` and a
transversal edge is a `k`-set meeting every fibre exactly once.
-/

namespace ProbMethodCombinatorics

open Finset

variable {k n : ℕ}

/-- A `k`-set meeting every part exactly once. -/
def IsTransversalEdge (e : Finset (Fin k × Fin n)) : Prop :=
  ∀ i : Fin k, (e.filter fun v => v.1 = i).card = 1

section Discrepancy

open MvPolynomial

variable {k n : ℕ}

/-- The exponent vector `∑ v ∈ e, single v.1 1` records how many vertices of `e` lie in each
part. -/
private lemma profile_apply (e : Finset (Fin k × Fin n)) (i : Fin k) :
    (∑ v ∈ e, Finsupp.single v.1 1 : Fin k →₀ ℕ) i = (e.filter fun v => v.1 = i).card := by
  rw [Finset.sum_apply', Finset.card_filter]
  exact Finset.sum_congr rfl fun v _ => by simp [Finsupp.single_apply]

private lemma allOnes_apply' (i : Fin k) : allOnes k i = 1 := rfl

/-- The product of the part variables over `e` is the monomial with exponent vector the
profile of `e`. -/
private lemma prod_X_eq_monomial (e : Finset (Fin k × Fin n)) :
    (∏ v ∈ e, X v.1 : MvPolynomial (Fin k) ℝ)
      = monomial (∑ v ∈ e, Finsupp.single v.1 1) 1 := by
  induction e using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, monomial_single_add, pow_one]

/-- A vertex of part `i` lies in `e` exactly when its second coordinate is one of the second
coordinates `e` has in part `i`. -/
private lemma mem_iff_mem_image (e : Finset (Fin k × Fin n)) (i : Fin k) (x : Fin n) :
    x ∈ (e.filter fun v => v.1 = i).image Prod.snd ↔ (i, x) ∈ e := by
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨v, ⟨hv, rfl⟩, rfl⟩
    exact hv
  · intro h
    exact ⟨(i, x), ⟨h, rfl⟩, rfl⟩

/-- The weights of the random subset sum to `1`. -/
private lemma sum_weight_eq_one (p : Fin k → ℝ) :
    ∑ S : Finset (Fin k × Fin n),
        (∏ v ∈ S, p v.1) * ∏ v ∈ univ \ S, (1 - p v.1) = 1 := by
  have h := Finset.prod_add (fun v : Fin k × Fin n => p v.1)
    (fun v : Fin k × Fin n => 1 - p v.1) univ
  rw [Finset.powerset_univ] at h
  rw [← h]
  simp

/-- The total weight of the subsets containing a fixed `e` is `∏ v ∈ e, p v.1`. -/
private lemma sum_weight_superset (p : Fin k → ℝ) (e : Finset (Fin k × Fin n)) :
    ∑ S : Finset (Fin k × Fin n),
        (if e ⊆ S then (∏ v ∈ S, p v.1) * ∏ v ∈ univ \ S, (1 - p v.1) else 0)
      = ∏ v ∈ e, p v.1 := by
  have h1 : ∀ S ∈ (univ : Finset (Finset (Fin k × Fin n))),
      (if e ⊆ S then (∏ v ∈ S, p v.1) * ∏ v ∈ univ \ S, (1 - p v.1) else 0)
        = (∏ v ∈ S, p v.1) * ∏ v ∈ univ \ S, (if v ∈ e then (0 : ℝ) else 1 - p v.1) := by
    intro S _
    by_cases hS : e ⊆ S
    · rw [if_pos hS]
      congr 1
      refine Finset.prod_congr rfl fun v hv => ?_
      rw [if_neg fun hve => (Finset.mem_sdiff.mp hv).2 (hS hve)]
    · rw [if_neg hS]
      obtain ⟨v, hve, hvS⟩ := Finset.not_subset.mp hS
      rw [Finset.prod_eq_zero (f := fun w : Fin k × Fin n => if w ∈ e then (0 : ℝ) else 1 - p w.1)
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvS⟩) (if_pos hve), mul_zero]
  calc ∑ S : Finset (Fin k × Fin n),
          (if e ⊆ S then (∏ v ∈ S, p v.1) * ∏ v ∈ univ \ S, (1 - p v.1) else 0)
      = ∑ S ∈ (univ : Finset (Fin k × Fin n)).powerset,
          (∏ v ∈ S, p v.1) * ∏ v ∈ univ \ S, (if v ∈ e then (0 : ℝ) else 1 - p v.1) := by
        rw [Finset.powerset_univ]
        exact Finset.sum_congr rfl h1
    _ = ∏ v : Fin k × Fin n, (p v.1 + if v ∈ e then (0 : ℝ) else 1 - p v.1) :=
        (Finset.prod_add (fun v : Fin k × Fin n => p v.1)
          (fun v : Fin k × Fin n => if v ∈ e then (0 : ℝ) else 1 - p v.1) univ).symm
    _ = ∏ v : Fin k × Fin n, (if v ∈ e then p v.1 else 1) := by
        refine Finset.prod_congr rfl fun v _ => ?_
        by_cases hv : v ∈ e <;> simp [hv]
    _ = ∏ v ∈ e, p v.1 := by rw [Finset.prod_ite_mem, Finset.univ_inter]

/-- The difference of the blue and the red count of `k`-subsets of `S` as a signed sum. -/
private lemma disc_eq_sum (col : Finset (Fin k × Fin n) → Bool) (S : Finset (Fin k × Fin n)) :
    (((S.powersetCard k).filter fun e => col e = true).card : ℝ)
        - (((S.powersetCard k).filter fun e => col e = false).card : ℝ)
      = ∑ e ∈ S.powersetCard k, (if col e then (1 : ℝ) else -1) := by
  have hfil : ((S.powersetCard k).filter fun e => col e = false)
      = ((S.powersetCard k).filter fun e => ¬ (col e = true)) := by
    refine Finset.filter_congr fun e _ => ?_
    simp
  have h1 : ∀ e ∈ (S.powersetCard k).filter (fun e => col e = true),
      (if col e then (1 : ℝ) else -1) = 1 := fun e he => if_pos (Finset.mem_filter.mp he).2
  have h2 : ∀ e ∈ (S.powersetCard k).filter (fun e => ¬ (col e = true)),
      (if col e then (1 : ℝ) else -1) = -1 := fun e he => if_neg (Finset.mem_filter.mp he).2
  rw [hfil, ← Finset.sum_filter_add_sum_filter_not (S.powersetCard k) (fun e => col e = true)
      (fun e => if col e then (1 : ℝ) else -1), Finset.sum_congr rfl h1,
    Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  ring

/-- The weighted average of the signed counts is the expectation polynomial evaluated at `p`. -/
private lemma sum_weight_mul_disc (p : Fin k → ℝ) (col : Finset (Fin k × Fin n) → Bool) :
    ∑ S : Finset (Fin k × Fin n),
        ((∏ v ∈ S, p v.1) * ∏ v ∈ univ \ S, (1 - p v.1)) *
          ∑ e ∈ S.powersetCard k, (if col e then (1 : ℝ) else -1)
      = ∑ e ∈ (univ : Finset (Fin k × Fin n)).powersetCard k,
          (if col e then (1 : ℝ) else -1) * ∏ v ∈ e, p v.1 := by
  have hps : ∀ S : Finset (Fin k × Fin n),
      S.powersetCard k = ((univ : Finset (Fin k × Fin n)).powersetCard k).filter
        (fun e => e ⊆ S) := by
    intro S
    ext e
    simp only [Finset.mem_powersetCard, Finset.mem_filter, Finset.subset_univ, true_and]
    tauto
  have step : ∀ S : Finset (Fin k × Fin n),
      ((∏ v ∈ S, p v.1) * ∏ v ∈ univ \ S, (1 - p v.1)) *
          (∑ e ∈ S.powersetCard k, (if col e then (1 : ℝ) else -1))
        = ∑ e ∈ (univ : Finset (Fin k × Fin n)).powersetCard k,
            (if col e then (1 : ℝ) else -1) *
              (if e ⊆ S then (∏ v ∈ S, p v.1) * ∏ v ∈ univ \ S, (1 - p v.1) else 0) := by
    intro S
    rw [hps S, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : e ⊆ S <;> simp [h]
  rw [Finset.sum_congr rfl fun S _ => step S, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Finset.mul_sum, sum_weight_superset]

private lemma pair_fst_snd {v : Fin k × Fin n} {i : Fin k} (h : v.1 = i) : (i, v.2) = v := by
  cases v
  cases h
  rfl

/-- A finite set of vertices is determined by the second coordinates it has in each part. -/
private lemma image_filter_injective :
    Function.Injective (fun (e : Finset (Fin k × Fin n)) (i : Fin k) =>
      (e.filter fun v => v.1 = i).image Prod.snd) := by
  intro e₁ e₂ hEq
  ext ⟨i, x⟩
  have h : (e₁.filter fun v => v.1 = i).image Prod.snd
      = (e₂.filter fun v => v.1 = i).image Prod.snd := congrFun hEq i
  rw [← mem_iff_mem_image e₁ i x, ← mem_iff_mem_image e₂ i x, h]

/-- At most `n ^ k` of the `k`-sets have a given profile. -/
private lemma card_profile_le (m : Fin k →₀ ℕ) :
    ((((univ : Finset (Fin k × Fin n)).powersetCard k).filter
        fun e => (∑ v ∈ e, Finsupp.single v.1 1) = m).card) ≤ n ^ k := by
  rcases Finset.eq_empty_or_nonempty ((((univ : Finset (Fin k × Fin n)).powersetCard k).filter
      fun e => (∑ v ∈ e, Finsupp.single v.1 1) = m)) with hE | ⟨e₀, he₀⟩
  · simp [hE]
  rw [Finset.mem_filter, Finset.mem_powersetCard] at he₀
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun v : Fin k × Fin n => v.1) (s := e₀) (t := univ)
    (fun v _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  have hsum : ∑ i : Fin k, m i = k := by
    have h2 : ∑ i : Fin k, m i = ∑ i : Fin k, (e₀.filter fun v => v.1 = i).card :=
      Finset.sum_congr rfl fun i _ => by rw [← profile_apply, he₀.2]
    rw [h2, ← hfib, he₀.1.2]
  have hmaps : Set.MapsTo (fun (e : Finset (Fin k × Fin n)) (i : Fin k) =>
        (e.filter fun v => v.1 = i).image Prod.snd)
      ↑((((univ : Finset (Fin k × Fin n)).powersetCard k).filter
        fun e => (∑ v ∈ e, Finsupp.single v.1 1) = m))
      ↑(Fintype.piFinset fun i : Fin k => (univ : Finset (Fin n)).powersetCard (m i)) := by
    intro e he
    rw [Finset.mem_coe, Finset.mem_filter] at he
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_image_of_injOn, ← profile_apply, he.2]
    intro v hv w hw hvw
    rw [Finset.mem_coe, Finset.mem_filter] at hv hw
    exact Prod.ext (hv.2.trans hw.2.symm) hvw
  calc ((((univ : Finset (Fin k × Fin n)).powersetCard k).filter
        fun e => (∑ v ∈ e, Finsupp.single v.1 1) = m).card)
      ≤ (Fintype.piFinset fun i : Fin k => (univ : Finset (Fin n)).powersetCard (m i)).card :=
        Finset.card_le_card_of_injOn _ hmaps fun e₁ _ e₂ _ h => image_filter_injective h
    _ = ∏ i : Fin k, ((univ : Finset (Fin n)).powersetCard (m i)).card := Fintype.card_piFinset _
    _ = ∏ i : Fin k, n.choose (m i) := by simp [Finset.card_powersetCard]
    _ ≤ ∏ i : Fin k, n ^ m i := Finset.prod_le_prod' fun i _ => Nat.choose_le_pow n (m i)
    _ = n ^ ∑ i : Fin k, m i := Finset.prod_pow_eq_pow_sum _ _ _
    _ = n ^ k := by rw [hsum]

/-- The part-`j` fibre of the `k`-set built from a function `g` is the single vertex
`(j, g j)`. -/
private lemma filter_image_fun (g : Fin k → Fin n) (j : Fin k) :
    (((univ : Finset (Fin k)).image fun i => (i, g i)).filter fun v => v.1 = j)
      = {(j, g j)} := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨i, rfl⟩, hj⟩
    cases hj
    rfl
  · rintro rfl
    exact ⟨⟨j, rfl⟩, rfl⟩

/-- The `k`-set built from a function has `k` elements. -/
private lemma card_image_fun (g : Fin k → Fin n) :
    ((univ : Finset (Fin k)).image fun i => (i, g i)).card = k := by
  rw [Finset.card_image_of_injective _ fun i j h => congrArg Prod.fst h, Finset.card_univ,
    Fintype.card_fin]

/-- The `k`-sets of profile `allOnes k` are exactly the transversal edges, and there are
`n ^ k` of them. -/
private lemma card_profile_allOnes :
    ((((univ : Finset (Fin k × Fin n)).powersetCard k).filter
        fun e => (∑ v ∈ e, Finsupp.single v.1 1) = allOnes k).card) = n ^ k := by
  have key : (univ : Finset (Fin k → Fin n)).card
      = ((((univ : Finset (Fin k × Fin n)).powersetCard k).filter
        fun e => (∑ v ∈ e, Finsupp.single v.1 1) = allOnes k).card) := by
    refine Finset.card_bij (fun g _ => (univ : Finset (Fin k)).image fun i => (i, g i))
      ?_ ?_ ?_
    · intro g _
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.subset_univ _, card_image_fun g⟩, ?_⟩
      ext i
      rw [profile_apply, filter_image_fun, Finset.card_singleton, allOnes_apply']
    · intro g₁ _ g₂ _ hEq
      have h : ((univ : Finset (Fin k)).image fun i => (i, g₁ i))
          = ((univ : Finset (Fin k)).image fun i => (i, g₂ i)) := hEq
      funext i
      have hi : (((univ : Finset (Fin k)).image fun j => (j, g₁ j)).filter fun v => v.1 = i)
          = (((univ : Finset (Fin k)).image fun j => (j, g₂ j)).filter fun v => v.1 = i) := by
        rw [h]
      rw [filter_image_fun, filter_image_fun] at hi
      exact congrArg Prod.snd (Finset.singleton_injective hi)
    · intro e he
      rw [Finset.mem_filter, Finset.mem_powersetCard] at he
      have hfib : ∀ i : Fin k, ∃ v : Fin k × Fin n, (e.filter fun w => w.1 = i) = {v} := by
        intro i
        rw [← Finset.card_eq_one, ← profile_apply, he.2]
        rfl
      choose a ha using hfib
      have hmem : ∀ i : Fin k, a i ∈ e.filter fun w => w.1 = i := by
        intro i
        rw [ha i]
        exact Finset.mem_singleton_self _
      have ha1 : ∀ i, (a i).1 = i := fun i => (Finset.mem_filter.mp (hmem i)).2
      refine ⟨fun i => (a i).2, Finset.mem_univ _, ?_⟩
      ext v
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        rw [pair_fst_snd (ha1 i)]
        exact (Finset.mem_filter.mp (hmem i)).1
      · intro hv
        refine ⟨v.1, ?_⟩
        have hv' : v ∈ e.filter fun w => w.1 = v.1 := Finset.mem_filter.mpr ⟨hv, rfl⟩
        rw [ha v.1, Finset.mem_singleton] at hv'
        rw [← hv']
  rw [← key, Finset.card_univ]
  simp

/-- The coefficients of the expectation polynomial are the signed counts of the `k`-sets of
each profile. -/
private lemma coeff_disc_poly (col : Finset (Fin k × Fin n) → Bool) (m : Fin k →₀ ℕ) :
    coeff m (∑ e ∈ (univ : Finset (Fin k × Fin n)).powersetCard k,
        C (if col e then (1 : ℝ) else -1) * ∏ v ∈ e, X v.1)
      = ∑ e ∈ ((univ : Finset (Fin k × Fin n)).powersetCard k).filter
          (fun e => (∑ v ∈ e, Finsupp.single v.1 1) = m), (if col e then (1 : ℝ) else -1) := by
  rw [coeff_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [prod_X_eq_monomial, C_mul_monomial, mul_one, coeff_monomial]

/-- The expectation polynomial has total degree at most `k`. -/
private lemma totalDegree_disc_poly (col : Finset (Fin k × Fin n) → Bool) :
    (∑ e ∈ (univ : Finset (Fin k × Fin n)).powersetCard k,
        C (if col e then (1 : ℝ) else -1) * ∏ v ∈ e, X v.1).totalDegree ≤ k := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun e he => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  rw [Finset.sum_congr rfl fun v (_ : v ∈ e) => totalDegree_X (R := ℝ) v.1, Finset.sum_const,
    smul_eq_mul, mul_one]
  exact le_of_eq (Finset.mem_powersetCard.mp he).2

/-- Evaluating the expectation polynomial at `p`. -/
private lemma eval_disc_poly (col : Finset (Fin k × Fin n) → Bool) (p : Fin k → ℝ) :
    eval p (∑ e ∈ (univ : Finset (Fin k × Fin n)).powersetCard k,
        C (if col e then (1 : ℝ) else -1) * ∏ v ∈ e, X v.1)
      = ∑ e ∈ (univ : Finset (Fin k × Fin n)).powersetCard k,
          (if col e then (1 : ℝ) else -1) * ∏ v ∈ e, p v.1 := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_mul, eval_C, eval_prod]
  simp only [eval_X]

/-- Every coefficient of the expectation polynomial is at most `n ^ k` in absolute value. -/
private lemma abs_coeff_disc_poly_le (col : Finset (Fin k × Fin n) → Bool) (m : Fin k →₀ ℕ) :
    |coeff m (∑ e ∈ (univ : Finset (Fin k × Fin n)).powersetCard k,
        C (if col e then (1 : ℝ) else -1) * ∏ v ∈ e, X v.1)| ≤ (n : ℝ) ^ k := by
  rw [coeff_disc_poly]
  calc |∑ e ∈ ((univ : Finset (Fin k × Fin n)).powersetCard k).filter
          (fun e => (∑ v ∈ e, Finsupp.single v.1 1) = m), (if col e then (1 : ℝ) else -1)|
      ≤ ∑ e ∈ ((univ : Finset (Fin k × Fin n)).powersetCard k).filter
          (fun e => (∑ v ∈ e, Finsupp.single v.1 1) = m), |if col e then (1 : ℝ) else -1| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ _e ∈ ((univ : Finset (Fin k × Fin n)).powersetCard k).filter
          (fun e => (∑ v ∈ e, Finsupp.single v.1 1) = m), (1 : ℝ) :=
        Finset.sum_congr rfl fun e _ => by by_cases h : col e = true <;> simp [h]
    _ = ((((univ : Finset (Fin k × Fin n)).powersetCard k).filter
          (fun e => (∑ v ∈ e, Finsupp.single v.1 1) = m)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (n : ℝ) ^ k := by
        rw [← Nat.cast_pow]
        exact_mod_cast card_profile_le m

/-- The `allOnes` coefficient is `n ^ k`: the transversal edges all count `+1`. -/
private lemma coeff_allOnes_disc_poly (col : Finset (Fin k × Fin n) → Bool)
    (hcol : ∀ e : Finset (Fin k × Fin n), e.card = k → IsTransversalEdge e → col e = true) :
    coeff (allOnes k) (∑ e ∈ (univ : Finset (Fin k × Fin n)).powersetCard k,
        C (if col e then (1 : ℝ) else -1) * ∏ v ∈ e, X v.1) = (n : ℝ) ^ k := by
  rw [coeff_disc_poly]
  have h1 : ∀ e ∈ ((univ : Finset (Fin k × Fin n)).powersetCard k).filter
      (fun e => (∑ v ∈ e, Finsupp.single v.1 1) = allOnes k),
      (if col e then (1 : ℝ) else -1) = 1 := by
    intro e he
    rw [Finset.mem_filter, Finset.mem_powersetCard] at he
    refine if_pos (hcol e he.1.2 fun i => ?_)
    rw [← profile_apply, he.2, allOnes_apply']
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one, card_profile_allOnes,
    Nat.cast_pow]

/-- The weights are nonnegative, since `p` takes values in `[0, 1]`. -/
private lemma weight_nonneg {p : Fin k → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (Fin k × Fin n)) :
    0 ≤ (∏ v ∈ S, p v.1) * ∏ v ∈ univ \ S, (1 - p v.1) :=
  mul_nonneg (Finset.prod_nonneg fun v _ => (Set.mem_Icc.mp (hp v.1)).1)
    (Finset.prod_nonneg fun v _ => by linarith [(Set.mem_Icc.mp (hp v.1)).2])

/-- **Step 4.**  Lemma 2.5.3, applied to the expectation polynomial divided by `n ^ k`,
produces a point of the cube at which the expectation is at least `c * n ^ k`. -/
private lemma exists_point_abs_eval_ge {c : ℝ} (hn : 0 < n)
    (hc : ∀ g : MvPolynomial (Fin k) ℝ, g.totalDegree ≤ k →
      (∀ m : Fin k →₀ ℕ, |coeff m g| ≤ 1) → coeff (allOnes k) g = 1 →
      ∃ p : Fin k → ℝ, (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) ∧ c ≤ |eval p g|)
    (col : Finset (Fin k × Fin n) → Bool)
    (hcol : ∀ e : Finset (Fin k × Fin n), e.card = k → IsTransversalEdge e → col e = true) :
    ∃ p : Fin k → ℝ, (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) ∧
      c * (n : ℝ) ^ k ≤ |∑ e ∈ (univ : Finset (Fin k × Fin n)).powersetCard k,
        (if col e then (1 : ℝ) else -1) * ∏ v ∈ e, p v.1| := by
  have hnk : (0 : ℝ) < (n : ℝ) ^ k := pow_pos (by exact_mod_cast hn) k
  have hne : ((n : ℝ) ^ k) ≠ 0 := ne_of_gt hnk
  set F : MvPolynomial (Fin k) ℝ := ∑ e ∈ (univ : Finset (Fin k × Fin n)).powersetCard k,
    C (if col e then (1 : ℝ) else -1) * ∏ v ∈ e, X v.1 with hF
  have hdeg : (C ((n : ℝ) ^ k)⁻¹ * F).totalDegree ≤ k := by
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add, hF]
    exact totalDegree_disc_poly col
  have hbdd : ∀ m : Fin k →₀ ℕ, |coeff m (C ((n : ℝ) ^ k)⁻¹ * F)| ≤ 1 := by
    intro m
    rw [coeff_C_mul, abs_mul, abs_of_pos (inv_pos.mpr hnk), inv_mul_eq_div, div_le_one hnk, hF]
    exact abs_coeff_disc_poly_le col m
  have hone : coeff (allOnes k) (C ((n : ℝ) ^ k)⁻¹ * F) = 1 := by
    rw [coeff_C_mul, hF, coeff_allOnes_disc_poly col hcol, inv_mul_cancel₀ hne]
  obtain ⟨p, hp, hpge⟩ := hc _ hdeg hbdd hone
  refine ⟨p, hp, ?_⟩
  rw [map_mul, eval_C, hF, eval_disc_poly, abs_mul, abs_of_pos (inv_pos.mpr hnk)] at hpge
  calc c * (n : ℝ) ^ k
      ≤ (((n : ℝ) ^ k)⁻¹ * |∑ e ∈ (univ : Finset (Fin k × Fin n)).powersetCard k,
          (if col e then (1 : ℝ) else -1) * ∏ v ∈ e, p v.1|) * (n : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right hpge (le_of_lt hnk)
    _ = |∑ e ∈ (univ : Finset (Fin k × Fin n)).powersetCard k,
          (if col e then (1 : ℝ) else -1) * ∏ v ∈ e, p v.1| := by
        field_simp

end Discrepancy

/-- **Theorem 2.5.2.**  The constant is uniform in `n` and in the colouring; that uniformity
is inherited from `exists_pos_forall_exists_abs_eval_ge` and is the substance of the result.

**`0 < n` is required, and without it the statement is false.**  At `n = 0` the vertex set is
empty, the only `S` is `∅`, both colour counts are `0`, and the claim reads `c * 0 ^ k < 0`.
The source states the theorem for parts "of size `n`" without comment, as it does elsewhere;
this is the same kind of unstated hypothesis as §2.4.4's `5 ≤ n` and §9.3.1's `2 ≤ n`. -/
theorem exists_subset_colour_discrepancy {k : ℕ} (hk : 2 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ), 0 < n → ∀ col : Finset (Fin k × Fin n) → Bool,
      (∀ e : Finset (Fin k × Fin n), e.card = k → IsTransversalEdge e → col e = true) →
      ∃ S : Finset (Fin k × Fin n),
        c * (n : ℝ) ^ k <
          |(((S.powersetCard k).filter fun e => col e = true).card : ℝ)
            - (((S.powersetCard k).filter fun e => col e = false).card : ℝ)| := by
  obtain ⟨c, hcpos, hc⟩ := exists_pos_forall_exists_abs_eval_ge k (by omega)
  refine ⟨c / 2, by linarith, ?_⟩
  intro n hn col hcol
  have hnk : (0 : ℝ) < (n : ℝ) ^ k := pow_pos (by exact_mod_cast hn) k
  obtain ⟨p, hp, hpge⟩ := exists_point_abs_eval_ge hn hc col hcol
  by_contra hcon
  have hle : ∀ S : Finset (Fin k × Fin n),
      |∑ e ∈ S.powersetCard k, (if col e then (1 : ℝ) else -1)| ≤ c / 2 * (n : ℝ) ^ k := by
    intro S
    rw [← disc_eq_sum col S]
    exact not_lt.mp fun h => hcon ⟨S, h⟩
  have hbound : |∑ e ∈ (univ : Finset (Fin k × Fin n)).powersetCard k,
      (if col e then (1 : ℝ) else -1) * ∏ v ∈ e, p v.1| ≤ c / 2 * (n : ℝ) ^ k := by
    rw [← sum_weight_mul_disc p col]
    calc |∑ S : Finset (Fin k × Fin n),
            ((∏ v ∈ S, p v.1) * ∏ v ∈ univ \ S, (1 - p v.1)) *
              ∑ e ∈ S.powersetCard k, (if col e then (1 : ℝ) else -1)|
        ≤ ∑ S : Finset (Fin k × Fin n),
            |((∏ v ∈ S, p v.1) * ∏ v ∈ univ \ S, (1 - p v.1)) *
              ∑ e ∈ S.powersetCard k, (if col e then (1 : ℝ) else -1)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ S : Finset (Fin k × Fin n),
            ((∏ v ∈ S, p v.1) * ∏ v ∈ univ \ S, (1 - p v.1)) * (c / 2 * (n : ℝ) ^ k) :=
          Finset.sum_le_sum fun S _ => by
            rw [abs_mul, abs_of_nonneg (weight_nonneg hp S)]
            exact mul_le_mul_of_nonneg_left (hle S) (weight_nonneg hp S)
      _ = (∑ S : Finset (Fin k × Fin n),
            (∏ v ∈ S, p v.1) * ∏ v ∈ univ \ S, (1 - p v.1)) * (c / 2 * (n : ℝ) ^ k) :=
          (Finset.sum_mul _ _ _).symm
      _ = c / 2 * (n : ℝ) ^ k := by rw [sum_weight_eq_one, one_mul]
  linarith [hpge.trans hbound, mul_pos (half_pos hcpos) hnk]

end ProbMethodCombinatorics
