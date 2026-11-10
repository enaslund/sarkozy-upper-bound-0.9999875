module

public import Sarkozy.SecondOrder.PivotSums

/-!
# Conditional moments of traces on a pinned fibre, with the exact brackets

`paper/sections/15_second_order.tex`, the two computations in the proof of `lem:pivot-moments`.
A fibre is given by distinct pinned labels `y_j` (`j ∈ κ`, `d = |κ|`), nonzero signs `ς_j`, an
excluded set `E` and `Φ = {x ∉ E : χ(ς_j(x - y_j)) = 1 ∀ j}`, with `γ = p 2^{-d}/|Φ|`. For root
sets `S_l` (`|S_l| = s_l ≥ 2`) and real `b_l`, `F = ∑_l b_l τ_{S_l}`, `r = p^{-1/2}`:

* `fibre_second_moment` (part (a)): for distinct `S_l`, from H5 (`eq:advance:rank-second`),
  `E_Φ F² ≤ γ (r² A + r³ E)` with `A`, `E` the pivot sums of `eq:pivot-sums`;
* `fibre_first_moment` (part (b)): if `E ⊇ {y_j}`, from Weil and H5 (`eq:advance:rank-first` and
  `lem:moving-root-trace`(b)), `|E_Φ F| ≤ γ r² 2^d [V + (d/2)U + r(X + (d/2 + |E|)W)]`.

Here `E_Φ` is the uniform average over `Φ`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.SecondOrder

open Sarkozy.Target

variable {p : ℕ} [hp : Fact p.Prime]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
theorem pin_prod_le (y ς : κ → ZMod p) (x : ZMod p) :
    ∏ j, (1 + ((quadraticChar (ZMod p) (ς j * (x - y j)) : ℤ) : ℝ)) ≤ 2 ^ Fintype.card κ := by
  calc ∏ j, (1 + ((quadraticChar (ZMod p) (ς j * (x - y j)) : ℤ) : ℝ))
      ≤ ∏ _j : κ, (2 : ℝ) := by
        refine prod_le_prod₀ (fun j _ => one_add_chi_nonneg _) fun j _ => ?_
        rcases quadraticChar_isQuadratic (ZMod p) (ς j * (x - y j)) with h | h | h <;>
          rw [h] <;> norm_num
    _ = 2 ^ Fintype.card κ := by rw [prod_const, card_univ]

omit [DecidableEq κ] in
/-- The pin product expands over the subsets of pins. -/
theorem pin_prod_expand (y : κ → ZMod p) (hy : Function.Injective y) (ς : κ → ZMod p)
    (x : ZMod p) :
    ∏ j, (1 + ((quadraticChar (ZMod p) (ς j * (x - y j)) : ℤ) : ℝ)) =
      ∑ J ∈ (univ : Finset κ).powerset,
        (∏ j ∈ J, ((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ)) * chiA p (J.image y) x := by
  rw [prod_one_add]
  refine sum_congr rfl fun J _ => ?_
  unfold chiA
  rw [prod_image (fun i _ j _ h => hy h), map_prod, Int.cast_prod, ← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  rw [map_mul, Int.cast_mul]

omit [Fintype κ] [DecidableEq κ] in
theorem abs_sign_prod_le (ς : κ → ZMod p) (J : Finset κ) :
    |∏ j ∈ J, ((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ)| ≤ 1 := by
  rw [abs_prod]
  refine prod_le_one₀ (fun j _ => abs_nonneg _) fun j _ => ?_
  rcases quadraticChar_isQuadratic (ZMod p) (ς j) with h | h | h <;> rw [h] <;> norm_num

/-- **`lem:pivot-moments`(a), on a fibre**: `E_Φ F² ≤ γ (r² A + r³ E)`, from H5. -/
theorem fibre_second_moment (hM : Target.MovingRoot) (hp2 : p ≠ 2)
    (y : κ → ZMod p) (hy : Function.Injective y) (ς : κ → ZMod p) (E : Finset (ZMod p))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ι → Finset (ZMod p)) (hS : Function.Injective S)
    (hS2 : ∀ l, 2 ≤ (S l).card) (b : ι → ℝ) (Φ : Finset (ZMod p))
    (hΦ : Φ = univ.filter fun x => x ∉ E ∧ ∀ j, quadraticChar (ZMod p) (ς j * (x - y j)) = 1)
    (hΦne : Φ.Nonempty) :
    (1 / (Φ.card : ℝ)) * ∑ x ∈ Φ, (∑ l, b l * tau p (S l) x) ^ 2 ≤
      ((p : ℝ) / 2 ^ Fintype.card κ / Φ.card) * ((1 / Real.sqrt p) ^ 2 * pivA b +
        (1 / Real.sqrt p) ^ 3 *
          pivE (1 / Real.sqrt p) (Fintype.card κ) b (fun l => (S l).card)) := by
  classical
  set r := 1 / Real.sqrt p with hr
  set F : ZMod p → ℝ := fun x => ∑ l, b l * tau p (S l) x with hF
  set P : ZMod p → ℝ := fun x => ∏ j, (1 + ((quadraticChar (ZMod p) (ς j * (x - y j)) : ℤ) : ℝ))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hΦpos : (0 : ℝ) < Φ.card := by exact_mod_cast card_pos.mpr hΦne
  have hr2 : r ^ 2 = 1 / (p : ℝ) := by
    simp only [hr, div_pow, one_pow, Real.sq_sqrt hp0.le]
  -- 1. the density of the uniform law on `Φ` is at most `γ P`
  have hP0 : ∀ x, 0 ≤ P x := fun x => prod_nonneg fun j _ => one_add_chi_nonneg _
  have hPΦ : ∀ x ∈ Φ, P x = 2 ^ Fintype.card κ := by
    intro x hx
    rw [hΦ, mem_filter] at hx
    simp only [P]
    rw [prod_congr rfl fun j _ => by rw [hx.2.2 j]]
    simp only [Int.cast_one]
    rw [prod_const, card_univ]
    norm_num
  have hdens : (1 / (Φ.card : ℝ)) * ∑ x ∈ Φ, F x ^ 2 ≤
      ((p : ℝ) / 2 ^ Fintype.card κ / Φ.card) * ((1 / (p : ℝ)) * ∑ x, P x * F x ^ 2) := by
    have hsub : ∑ x ∈ Φ, P x * F x ^ 2 ≤ ∑ x, P x * F x ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ =>
        mul_nonneg (hP0 x) (sq_nonneg _)
    have heq : ∑ x ∈ Φ, P x * F x ^ 2 = 2 ^ Fintype.card κ * ∑ x ∈ Φ, F x ^ 2 := by
      rw [mul_sum]; exact sum_congr rfl fun x hx => by rw [hPΦ x hx]
    have h2d : (0 : ℝ) < 2 ^ Fintype.card κ := by positivity
    calc (1 / (Φ.card : ℝ)) * ∑ x ∈ Φ, F x ^ 2
        = ((p : ℝ) / 2 ^ Fintype.card κ / Φ.card) *
            ((1 / (p : ℝ)) * ∑ x ∈ Φ, P x * F x ^ 2) := by
          rw [heq]; field_simp
      _ ≤ ((p : ℝ) / 2 ^ Fintype.card κ / Φ.card) * ((1 / (p : ℝ)) * ∑ x, P x * F x ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hsub (by positivity)
  -- 2. expand `P` over subsets and `F²` over pairs
  have hFsq : ∀ x, F x ^ 2 = ∑ l, ∑ l', b l * b l' * (tau p (S l) x * tau p (S l') x) := by
    intro x
    simp only [F, sq, sum_mul, mul_sum]
    exact sum_congr rfl fun l _ => sum_congr rfl fun l' _ => by ring
  -- 3. the moment of each triple
  set X : Finset κ → ι → ι → ℝ := fun J l l' =>
    (1 / (p : ℝ)) * ∑ x, chiA p (J.image y) x * tau p (S l) x * tau p (S l') x
  have hmain : (1 / (p : ℝ)) * ∑ x, P x * F x ^ 2 = ∑ J ∈ (univ : Finset κ).powerset,
      (∏ j ∈ J, ((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ)) * ∑ l, ∑ l', b l * b l' * X J l l' := by
    have e1 : (1 / (p : ℝ)) * ∑ x, P x * F x ^ 2 = ∑ x, ∑ J ∈ (univ : Finset κ).powerset,
        ∑ l, ∑ l', (1 / (p : ℝ)) * ((∏ j ∈ J, ((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ)) *
          chiA p (J.image y) x) * (b l * b l' * (tau p (S l) x * tau p (S l') x)) := by
      rw [mul_sum]
      refine sum_congr rfl fun x _ => ?_
      rw [show P x = _ from pin_prod_expand y hy ς x, hFsq, sum_mul, mul_sum]
      refine sum_congr rfl fun J _ => ?_
      rw [mul_sum, mul_sum]
      refine sum_congr rfl fun l _ => ?_
      rw [mul_sum, mul_sum]
      exact sum_congr rfl fun l' _ => by ring
    have e2 : ∑ J ∈ (univ : Finset κ).powerset,
        (∏ j ∈ J, ((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ)) * ∑ l, ∑ l', b l * b l' * X J l l' =
        ∑ J ∈ (univ : Finset κ).powerset, ∑ l, ∑ l', ∑ x, (1 / (p : ℝ)) *
          ((∏ j ∈ J, ((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ)) * chiA p (J.image y) x) *
            (b l * b l' * (tau p (S l) x * tau p (S l') x)) := by
      refine sum_congr rfl fun J _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun l _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun l' _ => ?_
      simp only [X]
      rw [mul_sum, mul_sum, mul_sum]
      exact sum_congr rfl fun x _ => by ring
    rw [e1, e2, sum_comm]
    refine sum_congr rfl fun J _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun l _ => ?_
    rw [sum_comm]
  have hXbound : ∀ J ∈ (univ : Finset κ).powerset, ∀ l l',
      |X J l l' - (if S l = S l' ∧ J.image y = ∅ then 1 / (p : ℝ) else 0)| ≤
        r ^ 3 * bracketTwo r (S l).card (S l').card J.card := by
    intro J _ l l'
    have h := (hM p hp2 (S l) (S l') (J.image y) (hS2 l) (hS2 l')).1
    have hcard : (J.image y).card = J.card := card_image_of_injective _ hy
    simp only [hcard] at h
    simp only [X, bracketTwo]
    exact h
  -- 4. main term and error
  set M : Finset κ → ι → ι → ℝ := fun J l l' =>
    if S l = S l' ∧ J.image y = ∅ then 1 / (p : ℝ) else 0
  have hMsum : ∑ J ∈ (univ : Finset κ).powerset,
      (∏ j ∈ J, ((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ)) * ∑ l, ∑ l', b l * b l' * M J l l' =
      (1 / (p : ℝ)) * ∑ l, b l ^ 2 := by
    rw [sum_eq_single (∅ : Finset κ)]
    · simp only [prod_empty, one_mul, image_empty, and_true, M]
      rw [mul_sum]
      refine sum_congr rfl fun l _ => ?_
      rw [sum_eq_single l]
      · simp only [↓reduceIte]; ring
      · intro l' _ hl'
        have : S l ≠ S l' := fun h => hl' (hS h).symm
        simp only [this, ↓reduceIte, mul_zero]
      · intro h'; exact absurd (mem_univ _) h'
    · intro J _ hJ
      have : J.image y ≠ ∅ := by
        intro h; exact hJ (image_eq_empty.mp h)
      simp only [M, this, and_false, ↓reduceIte, mul_zero, sum_const_zero]
    · intro h'; exact absurd (empty_mem_powerset _) h'
  have herr : |∑ J ∈ (univ : Finset κ).powerset,
      (∏ j ∈ J, ((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ)) *
        ∑ l, ∑ l', b l * b l' * (X J l l' - M J l l')| ≤
      r ^ 3 * ∑ J ∈ (univ : Finset κ).powerset, ∑ l, ∑ l',
        |b l| * |b l'| * bracketTwo r (S l).card (S l').card J.card := by
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun J hJ => ?_)
    rw [abs_mul]
    refine (mul_le_of_le_one_left (abs_nonneg _) (abs_sign_prod_le ς J)).trans ?_
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l _ => ?_)
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l' _ => ?_)
    rw [abs_mul, abs_mul]
    calc |b l| * |b l'| * |X J l l' - M J l l'|
        ≤ |b l| * |b l'| * (r ^ 3 * bracketTwo r (S l).card (S l').card J.card) :=
          mul_le_mul_of_nonneg_left (hXbound J hJ l l') (by positivity)
      _ = r ^ 3 * (|b l| * |b l'| * bracketTwo r (S l).card (S l').card J.card) := by ring
  have hsplitX : ∀ J ∈ (univ : Finset κ).powerset,
      ∑ l, ∑ l', b l * b l' * X J l l' =
        ∑ l, ∑ l', b l * b l' * M J l l' + ∑ l, ∑ l', b l * b l' * (X J l l' - M J l l') := by
    intro J _
    rw [← sum_add_distrib]
    exact sum_congr rfl fun l _ => by
      rw [← sum_add_distrib]; exact sum_congr rfl fun l' _ => by ring
  have hkey : (1 / (p : ℝ)) * ∑ x, P x * F x ^ 2 ≤
      r ^ 2 * pivA b + r ^ 3 * pivE r (Fintype.card κ) b (fun l => (S l).card) := by
    rw [hmain]
    rw [sum_congr rfl fun J hJ => by rw [hsplitX J hJ, mul_add]]
    rw [sum_add_distrib, hMsum]
    have := (abs_le.mp herr).2
    rw [sum_bracketTwo_family] at this
    rw [hr2]
    unfold pivA
    linarith
  calc (1 / (Φ.card : ℝ)) * ∑ x ∈ Φ, F x ^ 2
      ≤ ((p : ℝ) / 2 ^ Fintype.card κ / Φ.card) * ((1 / (p : ℝ)) * ∑ x, P x * F x ^ 2) := hdens
    _ ≤ ((p : ℝ) / 2 ^ Fintype.card κ / Φ.card) *
          (r ^ 2 * pivA b + r ^ 3 * pivE r (Fintype.card κ) b (fun l => (S l).card)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)

/-- **`lem:pivot-moments`(b), on a fibre**: if the excluded set contains the pins,
`|E_Φ F| ≤ γ r² 2^d [V + (d/2)U + r(X + (d/2 + |E|)W)]`, from Weil and H5. -/
theorem fibre_first_moment (hW : Target.Weil) (hM : Target.MovingRoot) (hp2 : p ≠ 2)
    (y : κ → ZMod p) (hy : Function.Injective y) (ς : κ → ZMod p) (hς : ∀ j, ς j ≠ 0)
    (E : Finset (ZMod p)) (hE : ∀ j, y j ∈ E)
    {ι : Type*} [Fintype ι] (S : ι → Finset (ZMod p)) (hS2 : ∀ l, 2 ≤ (S l).card) (b : ι → ℝ)
    (Φ : Finset (ZMod p))
    (hΦ : Φ = univ.filter fun x => x ∉ E ∧ ∀ j, quadraticChar (ZMod p) (ς j * (x - y j)) = 1)
    (hΦne : Φ.Nonempty) :
    |(1 / (Φ.card : ℝ)) * ∑ x ∈ Φ, ∑ l, b l * tau p (S l) x| ≤
      ((p : ℝ) / 2 ^ Fintype.card κ / Φ.card) * ((1 / Real.sqrt p) ^ 2 * 2 ^ Fintype.card κ *
        (pivV b (fun l => (S l).card) + (Fintype.card κ : ℝ) / 2 * pivU b (fun l => (S l).card) +
          (1 / Real.sqrt p) * (pivX b (fun l => (S l).card) +
            ((Fintype.card κ : ℝ) / 2 + E.card) * pivW b (fun l => (S l).card)))) := by
  classical
  set r := 1 / Real.sqrt p with hr
  set F : ZMod p → ℝ := fun x => ∑ l, b l * tau p (S l) x with hF
  set P : ZMod p → ℝ := fun x => ∏ j, (1 + ((quadraticChar (ZMod p) (ς j * (x - y j)) : ℤ) : ℝ))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hΦpos : (0 : ℝ) < Φ.card := by exact_mod_cast card_pos.mpr hΦne
  have hr0 : 0 ≤ r := by positivity
  have hr2 : r ^ 2 = 1 / (p : ℝ) := by
    simp only [hr, div_pow, one_pow, Real.sq_sqrt hp0.le]
  have h2d : (0 : ℝ) < 2 ^ Fintype.card κ := by positivity
  have hP0 : ∀ x, 0 ≤ P x := fun x => prod_nonneg fun j _ => one_add_chi_nonneg _
  have hPle : ∀ x, P x ≤ 2 ^ Fintype.card κ := fun x => pin_prod_le y ς x
  -- 1. the indicator of `Φ` off `E`
  have hPout : ∀ x, x ∉ E → P x = if x ∈ Φ then 2 ^ Fintype.card κ else 0 := by
    intro x hxE
    by_cases hx : x ∈ Φ
    · simp only [hx, ↓reduceIte]
      have hx' := hx
      rw [hΦ, mem_filter] at hx'
      simp only [P]
      rw [prod_congr rfl fun j _ => by rw [hx'.2.2 j]]
      simp only [Int.cast_one]
      rw [prod_const, card_univ]
      norm_num
    · simp only [hx, ↓reduceIte]
      have hex : ∃ j, quadraticChar (ZMod p) (ς j * (x - y j)) ≠ 1 := by
        by_contra hcon
        simp only [not_exists, not_not] at hcon
        exact hx (by rw [hΦ, mem_filter]; exact ⟨mem_univ _, hxE, hcon⟩)
      obtain ⟨j, hj⟩ := hex
      have hne : ς j * (x - y j) ≠ 0 :=
        mul_ne_zero (hς j) (sub_ne_zero.mpr fun h => hxE (h ▸ hE j))
      have hm1 : quadraticChar (ZMod p) (ς j * (x - y j)) = -1 := by
        rcases quadraticChar_dichotomy hne with h | h
        · exact absurd h hj
        · exact h
      exact prod_eq_zero (mem_univ j) (by rw [hm1]; norm_num)
  have hind : ∀ x, (if x ∈ Φ then (2 : ℝ) ^ Fintype.card κ * F x else 0) =
      P x * F x - (if x ∈ E then P x * F x else 0) := by
    intro x
    by_cases hxE : x ∈ E
    · have hxΦ : x ∉ Φ := by
        rw [hΦ, mem_filter]; exact fun h => h.2.1 hxE
      simp only [hxΦ, hxE, ↓reduceIte, sub_self]
    · rw [hPout x hxE]
      by_cases hxΦ : x ∈ Φ
      · simp only [hxΦ, hxE, ↓reduceIte, sub_zero]
      · simp only [hxΦ, hxE, ↓reduceIte, zero_mul, sub_zero]
  have hsumΦ : (2 : ℝ) ^ Fintype.card κ * ∑ x ∈ Φ, F x =
      ∑ x, P x * F x - ∑ x ∈ E, P x * F x := by
    have h1 : ∑ x, (if x ∈ Φ then (2 : ℝ) ^ Fintype.card κ * F x else 0) =
        (2 : ℝ) ^ Fintype.card κ * ∑ x ∈ Φ, F x := by
      rw [sum_ite_mem, univ_inter, mul_sum]
    have h2 : ∑ x, (if x ∈ E then P x * F x else 0) = ∑ x ∈ E, P x * F x := by
      rw [sum_ite_mem, univ_inter]
    rw [← h1, ← h2, ← sum_sub_distrib]
    exact sum_congr rfl fun x _ => hind x
  have hform : (1 / (Φ.card : ℝ)) * ∑ x ∈ Φ, F x =
      ((p : ℝ) / 2 ^ Fintype.card κ / Φ.card) *
        ((1 / (p : ℝ)) * ∑ x, P x * F x - (1 / (p : ℝ)) * ∑ x ∈ E, P x * F x) := by
    have : ∑ x ∈ Φ, F x = (∑ x, P x * F x - ∑ x ∈ E, P x * F x) / 2 ^ Fintype.card κ := by
      rw [← hsumΦ]; field_simp
    rw [this]
    field_simp
  -- 2. the complete sum, by `eq:advance:rank-first`
  have hexp1 : (1 / (p : ℝ)) * ∑ x, P x * F x = ∑ J ∈ (univ : Finset κ).powerset,
      (∏ j ∈ J, ((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ)) *
        ∑ l, b l * ((1 / (p : ℝ)) * ∑ x, chiA p (J.image y) x * tau p (S l) x) := by
    have e1 : (1 / (p : ℝ)) * ∑ x, P x * F x = ∑ x, ∑ J ∈ (univ : Finset κ).powerset,
        ∑ l, (1 / (p : ℝ)) * ((∏ j ∈ J, ((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ)) *
          chiA p (J.image y) x) * (b l * tau p (S l) x) := by
      rw [mul_sum]
      refine sum_congr rfl fun x _ => ?_
      rw [show P x = _ from pin_prod_expand y hy ς x, sum_mul, mul_sum]
      refine sum_congr rfl fun J _ => ?_
      simp only [F]
      rw [mul_sum, mul_sum]
      exact sum_congr rfl fun l _ => by ring
    have e2 : ∑ J ∈ (univ : Finset κ).powerset,
        (∏ j ∈ J, ((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ)) *
          ∑ l, b l * ((1 / (p : ℝ)) * ∑ x, chiA p (J.image y) x * tau p (S l) x) =
        ∑ J ∈ (univ : Finset κ).powerset, ∑ l, ∑ x, (1 / (p : ℝ)) *
          ((∏ j ∈ J, ((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ)) * chiA p (J.image y) x) *
            (b l * tau p (S l) x) := by
      refine sum_congr rfl fun J _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun l _ => ?_
      rw [mul_sum, mul_sum, mul_sum]
      exact sum_congr rfl fun x _ => by ring
    rw [e1, e2, sum_comm]
    refine sum_congr rfl fun J _ => ?_
    rw [sum_comm]
  have hY : ∀ J ∈ (univ : Finset κ).powerset, ∀ l,
      |(1 / (p : ℝ)) * ∑ x, chiA p (J.image y) x * tau p (S l) x| ≤
        r ^ 2 * bracketOne r (S l).card J.card := by
    intro J _ l
    have h := (hM p hp2 (S l) (S l) (J.image y) (hS2 l) (hS2 l)).2
    have hcard : (J.image y).card = J.card := card_image_of_injective _ hy
    simp only [hcard] at h
    simp only [bracketOne]
    exact h
  have hfull : |(1 / (p : ℝ)) * ∑ x, P x * F x| ≤
      r ^ 2 * ∑ J ∈ (univ : Finset κ).powerset, ∑ l, |b l| * bracketOne r (S l).card J.card := by
    rw [hexp1, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun J hJ => ?_)
    rw [abs_mul]
    refine (mul_le_of_le_one_left (abs_nonneg _) (abs_sign_prod_le ς J)).trans ?_
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l _ => ?_)
    rw [abs_mul]
    calc |b l| * |(1 / (p : ℝ)) * ∑ x, chiA p (J.image y) x * tau p (S l) x|
        ≤ |b l| * (r ^ 2 * bracketOne r (S l).card J.card) :=
          mul_le_mul_of_nonneg_left (hY J hJ l) (abs_nonneg _)
      _ = r ^ 2 * (|b l| * bracketOne r (S l).card J.card) := by ring
  -- 3. the excluded labels, by `lem:moving-root-trace`(b)
  have hFabs : ∀ x, |F x| ≤ r * pivW b (fun l => (S l).card) := by
    intro x
    simp only [F, pivW]
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l _ => ?_)
    rw [abs_mul]
    calc |b l| * |tau p (S l) x| ≤ |b l| * ((S l).card * r) :=
          mul_le_mul_of_nonneg_left (abs_tau_le hW hp2 (S l) (hS2 l) x) (abs_nonneg _)
      _ = r * (|b l| * (S l).card) := by ring
  have hexcl : |(1 / (p : ℝ)) * ∑ x ∈ E, P x * F x| ≤
      r ^ 2 * (E.card * (2 ^ Fintype.card κ * (r * pivW b (fun l => (S l).card)))) := by
    rw [hr2, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / p)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ x ∈ E, |P x * F x| ≤ ∑ _x ∈ E, 2 ^ Fintype.card κ * (r * pivW b (fun l => (S l).card)) := by
          refine sum_le_sum fun x _ => ?_
          rw [abs_mul, abs_of_nonneg (hP0 x)]
          exact mul_le_mul (hPle x) (hFabs x) (abs_nonneg _) h2d.le
      _ = E.card * (2 ^ Fintype.card κ * (r * pivW b (fun l => (S l).card))) := by
          rw [sum_const, nsmul_eq_mul]
  -- 4. assemble
  rw [hform, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (p : ℝ) / 2 ^ Fintype.card κ / Φ.card)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hsplit := abs_sub ((1 / (p : ℝ)) * ∑ x, P x * F x) ((1 / (p : ℝ)) * ∑ x ∈ E, P x * F x)
  rw [sum_bracketOne_family] at hfull
  have hW0 : 0 ≤ pivW b (fun l => (S l).card) :=
    sum_nonneg fun l _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
  calc |(1 / (p : ℝ)) * ∑ x, P x * F x - (1 / (p : ℝ)) * ∑ x ∈ E, P x * F x|
      ≤ r ^ 2 * (2 ^ Fintype.card κ * (pivV b (fun l => (S l).card) +
            (Fintype.card κ : ℝ) / 2 * pivU b (fun l => (S l).card) +
            r * (pivX b (fun l => (S l).card) +
              (Fintype.card κ : ℝ) / 2 * pivW b (fun l => (S l).card)))) +
        r ^ 2 * (E.card * (2 ^ Fintype.card κ * (r * pivW b (fun l => (S l).card)))) := by
        linarith
    _ = r ^ 2 * 2 ^ Fintype.card κ * (pivV b (fun l => (S l).card) +
          (Fintype.card κ : ℝ) / 2 * pivU b (fun l => (S l).card) +
          r * (pivX b (fun l => (S l).card) +
            ((Fintype.card κ : ℝ) / 2 + E.card) * pivW b (fun l => (S l).card))) := by
        ring

end Sarkozy.SecondOrder
