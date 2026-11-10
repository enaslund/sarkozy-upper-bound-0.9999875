module

public import Sarkozy.SecondOrder.OrderedStar
public import Sarkozy.SecondOrder.StarTrace
public import Sarkozy.Spectral.Stars

/-!
# The complete-star mean (`lem:star-mean`)

`paper/sections/15_second_order.tex`. The star function of `eq:star-function` is WP-A's
`Sarkozy.Spectral.starFunction N c`:
`h_⋆(x) = ∑_k ∑_{∅ ≠ J ⊆ N(k)} c_{k,J} w_J(x)`. Here `k` ranges over the centres, `N(k) ⊆ U⁺`, and
`c_{k,J} = ∏_{j∈J} χ(ς_jk)` in the paper (the identity below holds for any coefficients). Put
`a_T = ∑_{k : T ⊆ N(k)} c_{k,T}` (`starCoeff`) and `B_even = ∑_{|T| even ≥ 2} a_T` (`starBEven`).
The pivot groups are over the supports `T` with `|T| ≥ 3` (`supports3`), each with its greatest
vertex as pivot.

* `starFunction_eq`: on injective labellings, `h_⋆ = ∑_i F_i - B_even/p`, by `lem:star-trace`.
* `star_mean`: for a pinned half law `μ` (`def:pinned-law`), from Weil and H5,
  `E_μ(h_⋆ - E_μ h_⋆)² ≤ M_⋆²` with `M_⋆² = r²[∑_i D_i² + 2r ∑_i K_i ∑_{j<i} D_j]` (the
  ordered-star bound, `prop:advance:ordered-star`), and
  `|E_μ h_⋆| ≤ z_⋆ = r²(∑_i K_i + |B_even|)`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.SecondOrder

open Sarkozy.Target

variable {p : ℕ} [hp : Fact p.Prime] {U K : Type*} [Fintype U] [DecidableEq U] [Fintype K]

omit [Fintype U] [DecidableEq U] in
theorem starTrace_eq_starW {x : U → ZMod p} (hx : Function.Injective x) (J : Finset U) :
    Spectral.starTrace (F := ZMod p) (J.image x) = starW x J := by
  unfold Spectral.starTrace starW
  rw [ZMod.card]
  congr 1
  refine sum_congr rfl fun t _ => ?_
  rw [prod_chi_eq, prod_image (fun a _ b _ h => hx h)]

/-- `a_T = ∑_{k : T ⊆ N(k)} c_{k,T}`. -/
noncomputable def starCoeff (N : K → Finset U) (c : K → Finset U → ℝ) (T : Finset U) : ℝ :=
  ∑ k, if T ⊆ N k then c k T else 0

/-- `B_even = ∑_{|T| even ≥ 2} a_T`. -/
noncomputable def starBEven (N : K → Finset U) (c : K → Finset U → ℝ) : ℝ :=
  ∑ T ∈ (univ : Finset (Finset U)).filter (fun T => 2 ≤ T.card ∧ Even T.card), starCoeff N c T

/-- The supports with at least three vertices. -/
def supports3 : Finset (Finset U) := (univ : Finset (Finset U)).filter fun T => 3 ≤ T.card

omit [DecidableEq U] [Fintype K] in
theorem supports3_card {T : Finset U} (hT : T ∈ supports3 (U := U)) : 3 ≤ T.card :=
  (mem_filter.mp hT).2

/-- Exchange of the centre and support sums. -/
theorem sum_centres_eq (N : K → Finset U) (f : K → Finset U → ℝ) :
    ∑ k, ∑ J ∈ (N k).powerset.filter (fun J => J.Nonempty), f k J =
      ∑ T ∈ (univ : Finset (Finset U)).filter (fun T => T.Nonempty),
        ∑ k, if T ⊆ N k then f k T else 0 := by
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_filter, sum_filter]
  have h : ∀ T : Finset U, (if T.Nonempty then (if T ⊆ N k then f k T else 0) else 0) =
      if T ∈ (N k).powerset then (if T.Nonempty then f k T else 0) else 0 := by
    intro T
    by_cases h1 : T ⊆ N k
    · have h2 : T ∈ (N k).powerset := mem_powerset.mpr h1
      simp only [h1, h2, ↓reduceIte]
    · have h2 : T ∉ (N k).powerset := fun h => h1 (mem_powerset.mp h)
      simp only [h1, h2, ↓reduceIte, ite_self]
  rw [sum_congr rfl fun T _ => h T, sum_ite_mem, univ_inter]

omit [Fintype U] [DecidableEq U] in
/-- The even part of a sign product: `∑_{T ⊆ N, |T| even} ∏_{j∈T} σ_j = ½[∏(1 + σ) + ∏(1 - σ)]`. -/
theorem sum_even_prod (N : Finset U) (σ : U → ℝ) :
    ∑ T ∈ N.powerset.filter (fun T => Even T.card), ∏ j ∈ T, σ j =
      (1 / 2) * (∏ j ∈ N, (1 + σ j) + ∏ j ∈ N, (1 - σ j)) := by
  have h1 : ∏ j ∈ N, (1 - σ j) = ∑ T ∈ N.powerset, (-1) ^ T.card * ∏ j ∈ T, σ j := by
    have : ∏ j ∈ N, (1 - σ j) = ∏ j ∈ N, (1 + (-σ j)) := prod_congr rfl fun j _ => by ring
    rw [this, prod_one_add]
    exact sum_congr rfl fun T _ => by rw [prod_neg]
  rw [prod_one_add, h1, ← sum_add_distrib, mul_sum, sum_filter]
  refine sum_congr rfl fun T _ => ?_
  rcases Nat.even_or_odd T.card with he | ho
  · simp only [he, ↓reduceIte, he.neg_one_pow]; ring
  · have hne : ¬ Even T.card := Nat.not_even_iff_odd.mpr ho
    simp only [hne, ↓reduceIte, ho.neg_one_pow]; ring

/-- **`lem:star-mean`, the product formula for `B_even`**: with the paper's coefficients
`c_{k,J} = ∏_{j∈J} χ(ς_jk)`,
`B_even = ∑_k (½[∏_{j∈N(k)}(1 + χ(ς_jk)) + ∏_{j∈N(k)}(1 - χ(ς_jk))] - 1)`. -/
theorem starBEven_eq_prod (N : K → Finset U) (σ : K → U → ℝ) :
    starBEven N (fun k J => ∏ j ∈ J, σ k j) =
      ∑ k, ((1 / 2) * (∏ j ∈ N k, (1 + σ k j) + ∏ j ∈ N k, (1 - σ k j)) - 1) := by
  unfold starBEven starCoeff
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [← sum_even_prod]
  -- restrict to the subsets of `N k`
  have h : ∑ T ∈ (univ : Finset (Finset U)).filter (fun T => 2 ≤ T.card ∧ Even T.card),
      (if T ⊆ N k then ∏ j ∈ T, σ k j else 0) =
      ∑ T ∈ (N k).powerset.filter (fun T => 2 ≤ T.card ∧ Even T.card), ∏ j ∈ T, σ k j := by
    rw [sum_filter, sum_filter]
    have e : ∀ T : Finset U, (if 2 ≤ T.card ∧ Even T.card then
        (if T ⊆ N k then ∏ j ∈ T, σ k j else 0) else 0) =
        if T ∈ (N k).powerset then (if 2 ≤ T.card ∧ Even T.card then ∏ j ∈ T, σ k j else 0)
          else 0 := by
      intro T
      by_cases h1 : T ⊆ N k
      · have h2 : T ∈ (N k).powerset := mem_powerset.mpr h1
        simp only [h1, h2, ↓reduceIte]
      · have h2 : T ∉ (N k).powerset := fun h => h1 (mem_powerset.mp h)
        simp only [h1, h2, ↓reduceIte, ite_self]
    rw [sum_congr rfl fun T _ => e T, sum_ite_mem, univ_inter]
  rw [h]
  -- the empty set is the only even subset with fewer than two elements
  have hsplit : (N k).powerset.filter (fun T => Even T.card) =
      insert ∅ ((N k).powerset.filter (fun T => 2 ≤ T.card ∧ Even T.card)) := by
    ext T
    simp only [mem_filter, mem_powerset, mem_insert]
    constructor
    · rintro ⟨hT, he⟩
      by_cases h0 : T = ∅
      · exact Or.inl h0
      · have hpos : 0 < T.card := card_pos.mpr (nonempty_iff_ne_empty.mpr h0)
        have h2 : 2 ≤ T.card := by
          obtain ⟨m, hm⟩ := he; omega
        exact Or.inr ⟨hT, h2, he⟩
    · rintro (rfl | ⟨hT, _, he⟩)
      · exact ⟨empty_subset _, by simp⟩
      · exact ⟨hT, he⟩
  have hnot : ∅ ∉ (N k).powerset.filter (fun T => 2 ≤ T.card ∧ Even T.card) := by
    simp
  rw [hsplit, sum_insert hnot, prod_empty]
  ring

variable [LinearOrder U]

omit [Fintype K] in
/-- Grouping a sum over the supports by their pivots. -/
theorem sum_pivotGroups (𝒯 : Finset (Finset U)) (h𝒯 : ∀ T ∈ 𝒯, T.Nonempty) (f : Finset U → ℝ) :
    ∑ i, ∑ T ∈ pivotGroup 𝒯 i, f T = ∑ T ∈ 𝒯, f T := by
  unfold pivotGroup
  simp_rw [sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun T hT => ?_
  have hne := h𝒯 T hT
  have hiff : ∀ i : U, T.max = (i : WithBot U) ↔ T.max' hne = i := by
    intro i
    rw [← coe_max' hne, WithBot.coe_inj]
  simp_rw [hiff]
  rw [sum_ite_eq]
  simp

/-- **`lem:star-mean`, the identity**: on injective labellings, `h_⋆ = ∑_i F_i - B_even/p`. -/
theorem starFunction_eq (hp2 : p ≠ 2) (N : K → Finset U) (c : K → Finset U → ℝ)
    {x : U → ZMod p} (hx : Function.Injective x) :
    Spectral.starFunction (F := ZMod p) N c x =
      ∑ i, pivotF supports3 (starCoeff N c) i x - starBEven N c / p := by
  set a := starCoeff N c with ha
  -- 1. expand into supports
  have h1 : Spectral.starFunction (F := ZMod p) N c x =
      ∑ T ∈ (univ : Finset (Finset U)).filter (fun T => T.Nonempty), a T * starW x T := by
    unfold Spectral.starFunction
    simp_rw [starTrace_eq_starW hx]
    rw [sum_centres_eq N (fun k J => c k J * starW x J)]
    refine sum_congr rfl fun T _ => ?_
    simp only [a, starCoeff, sum_mul]
    exact sum_congr rfl fun k _ => by split_ifs <;> simp
  -- 2. the value of `w_T` by size
  have h2 : ∀ T ∈ (univ : Finset (Finset U)).filter (fun T => T.Nonempty),
      a T * starW x T = (if 3 ≤ T.card then a T * starW x T else 0) -
        (if T.card = 2 then a T / p else 0) := by
    intro T hT
    have hne := (mem_filter.mp hT).2
    have hpos : 0 < T.card := card_pos.mpr hne
    rcases Nat.lt_or_ge T.card 3 with h3 | h3
    · have h3' : ¬ 3 ≤ T.card := by omega
      rcases (by omega : T.card = 1 ∨ T.card = 2) with h | h
      · obtain ⟨j, rfl⟩ := card_eq_one.mp h
        rw [starW_singleton hp2]
        simp
      · obtain ⟨j, k, hjk, rfl⟩ := card_eq_two.mp h
        have e1 : (if 3 ≤ ({j, k} : Finset U).card then a {j, k} * starW x {j, k} else 0) = 0 := by
          simp [h]
        have e2 : (if ({j, k} : Finset U).card = 2 then a {j, k} / p else 0) = a {j, k} / p := by
          simp [h]
        rw [e1, e2, starW_pair hp2 hx hjk]
        ring
    · have h2' : T.card ≠ 2 := by omega
      simp only [h3, h2', ↓reduceIte, sub_zero]
  rw [h1, sum_congr rfl h2, sum_sub_distrib, sum_filter, sum_filter]
  -- 3. the supports with `|T| ≥ 3`, grouped by pivot
  have h3 : ∑ T : Finset U, (if T.Nonempty then (if 3 ≤ T.card then a T * starW x T else 0)
      else 0) =
      ∑ T ∈ supports3, a T * starW x T := by
    unfold supports3
    rw [sum_filter]
    refine sum_congr rfl fun T _ => ?_
    by_cases h : 3 ≤ T.card
    · have hne : T.Nonempty := card_pos.mp (by omega)
      simp only [hne, h, ↓reduceIte]
    · simp only [h, ↓reduceIte, ite_self]
  have h4 : ∑ T ∈ supports3, a T * starW x T = ∑ i, pivotF supports3 a i x -
      (1 / (p : ℝ)) * ∑ T ∈ supports3, (if Even T.card then a T else 0) := by
    rw [← sum_pivotGroups supports3 (fun T hT => card_pos.mp (by
      have := supports3_card hT; omega)) (fun T => a T * starW x T)]
    rw [← sum_pivotGroups supports3 (fun T hT => card_pos.mp (by
      have := supports3_card hT; omega)) (fun T => if Even T.card then a T else 0), mul_sum,
      ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    unfold pivotF
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun T hT => ?_
    rw [starW_eq_tau hx (pivot_mem hT)]
    split_ifs <;> ring
  have h5 : ∑ T : Finset U, (if T.Nonempty then (if T.card = 2 then a T / p else 0) else 0) =
      (1 / (p : ℝ)) * ∑ T ∈ (univ : Finset (Finset U)).filter (fun T => T.card = 2), a T := by
    rw [mul_sum, sum_filter]
    refine sum_congr rfl fun T _ => ?_
    by_cases h : T.card = 2
    · have hne : T.Nonempty := card_pos.mp (by omega)
      simp only [hne, h, ↓reduceIte]
      ring
    · simp only [h, ↓reduceIte, ite_self]
  have h6 : starBEven N c = ∑ T ∈ (univ : Finset (Finset U)).filter (fun T => T.card = 2), a T +
      ∑ T ∈ supports3, (if Even T.card then a T else 0) := by
    unfold starBEven supports3
    rw [← ha, sum_filter, sum_filter, sum_filter, ← sum_add_distrib]
    refine sum_congr rfl fun T _ => ?_
    by_cases h2 : T.card = 2
    · have h3 : ¬ 3 ≤ T.card := by omega
      have he : Even T.card := by rw [h2]; exact even_two
      have h2' : 2 ≤ T.card ∧ Even T.card := ⟨by omega, he⟩
      simp only [eq_true h2', eq_true h2, h3, ↓reduceIte, add_zero]
    · by_cases h3 : 3 ≤ T.card
      · have h2' : 2 ≤ T.card := by omega
        simp only [h2, h3, h2', true_and, ↓reduceIte, zero_add]
      · have h2' : ¬ (2 ≤ T.card ∧ Even T.card) := fun h => by omega
        simp only [h2, h3, h2', ↓reduceIte, add_zero]
  rw [h3, h4, h5, h6]
  ring

/-- **`lem:star-mean`**: for a pinned half law, `E_μ(h_⋆ - E_μ h_⋆)² ≤ M_⋆²` and
`|E_μ h_⋆| ≤ z_⋆ = r²(∑_i K_i + |B_even|)`, from Weil and H5. -/
theorem star_mean (hW : Target.Weil) (hM : Target.MovingRoot) (hp2 : p ≠ 2)
    (L : PinnedHalfLaw p U) (N : K → Finset U) (c : K → Finset U → ℝ) :
    ∑ x, L.μ x * (Spectral.starFunction (F := ZMod p) N c x -
        ∑ y, L.μ y * Spectral.starFunction (F := ZMod p) N c y) ^ 2 ≤
        (1 / Real.sqrt p) ^ 2 * (∑ i, pivotD2 L supports3 (starCoeff N c) i +
          2 * (1 / Real.sqrt p) * ∑ i, pivotK L supports3 (starCoeff N c) i *
            ∑ j ∈ univ.filter (· < i), Real.sqrt (pivotD2 L supports3 (starCoeff N c) j)) ∧
      |∑ x, L.μ x * Spectral.starFunction (F := ZMod p) N c x| ≤
        (1 / Real.sqrt p) ^ 2 * (∑ i, pivotK L supports3 (starCoeff N c) i +
          |starBEven N c|) := by
  set h := fun x : U → ZMod p => Spectral.starFunction (F := ZMod p) N c x with hh
  set G := fun x : U → ZMod p => ∑ i, pivotF supports3 (starCoeff N c) i x with hG
  set B := starBEven N c with hB
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hr2 : (1 / Real.sqrt p) ^ 2 = 1 / (p : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt hp0.le]
  obtain ⟨hstar, hfirst⟩ := ordered_star hW hM hp2 L supports3
    (fun T hT => supports3_card hT) (starCoeff N c)
  -- on the support, `h = G - B/p`
  have hsupp : ∀ x, L.μ x * h x = L.μ x * (G x - B / p) := by
    intro x
    rcases (L.μ_nonneg x).lt_or_eq with hpos | hzero
    · simp only [hh, hG, hB]; rw [starFunction_eq hp2 N c (L.μ_inj x hpos)]
    · rw [← hzero, zero_mul, zero_mul]
  have hmean : ∑ x, L.μ x * h x = ∑ x, L.μ x * G x - B / p := by
    rw [sum_congr rfl fun x _ => hsupp x]
    simp_rw [mul_sub]
    rw [sum_sub_distrib, ← sum_mul, L.μ_sum, one_mul]
  constructor
  · -- the variance
    have hsupp2 : ∀ x, L.μ x * (h x - ∑ y, L.μ y * h y) ^ 2 =
        L.μ x * (G x - ∑ y, L.μ y * G y) ^ 2 := by
      intro x
      rcases (L.μ_nonneg x).lt_or_eq with hpos | hzero
      · have hx : h x = G x - B / p := by
          simp only [hh, hG, hB]; rw [starFunction_eq hp2 N c (L.μ_inj x hpos)]
        rw [hx, hmean]
        ring
      · rw [← hzero, zero_mul, zero_mul]
    rw [sum_congr rfl fun x _ => hsupp2 x]
    have hvar : ∑ x, L.μ x * (G x - ∑ y, L.μ y * G y) ^ 2 =
        ∑ x, L.μ x * G x ^ 2 - (∑ y, L.μ y * G y) ^ 2 := by
      have e : ∀ x, L.μ x * (G x - ∑ y, L.μ y * G y) ^ 2 =
          L.μ x * G x ^ 2 - 2 * (∑ y, L.μ y * G y) * (L.μ x * G x) +
            (∑ y, L.μ y * G y) ^ 2 * L.μ x := fun x => by ring
      rw [sum_congr rfl fun x _ => e x, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum,
        L.μ_sum]
      ring
    rw [hvar]
    have := sq_nonneg (∑ y, L.μ y * G y)
    exact (sub_le_self _ this).trans hstar
  · -- the mean
    rw [hmean]
    have hEG : ∑ x, L.μ x * G x = ∑ i, ∑ x, L.μ x * pivotF supports3 (starCoeff N c) i x := by
      simp only [hG, mul_sum]
      exact sum_comm
    rw [hEG]
    calc |∑ i, ∑ x, L.μ x * pivotF supports3 (starCoeff N c) i x - B / p|
        ≤ ∑ i, |∑ x, L.μ x * pivotF supports3 (starCoeff N c) i x| + |B| / p := by
          refine (abs_sub _ _).trans ?_
          rw [abs_div, abs_of_pos hp0]
          have := abs_sum_le_sum_abs
            (fun i => ∑ x, L.μ x * pivotF supports3 (starCoeff N c) i x) univ
          linarith
      _ ≤ ∑ i, (1 / Real.sqrt p) ^ 2 * pivotK L supports3 (starCoeff N c) i + |B| / p := by
          have := sum_le_sum (s := univ) fun i (_ : i ∈ univ) => hfirst i
          linarith
      _ = (1 / Real.sqrt p) ^ 2 * (∑ i, pivotK L supports3 (starCoeff N c) i + |B|) := by
          rw [mul_add, ← mul_sum, hr2]
          ring

end Sarkozy.SecondOrder
