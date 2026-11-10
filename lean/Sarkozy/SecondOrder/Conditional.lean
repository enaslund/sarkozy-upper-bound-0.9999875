module

public import Sarkozy.SecondOrder.MovingRoot

/-!
# The conditional `L²` bound for moving-root traces (`cor:moving-root-conditional`)

`paper/sections/15_second_order.tex`. Fix distinct labels `y_1, …, y_d`, signs `ς_j = ±1`, an
excluded set `E ⊇ {y_j}`, and let `Φ = {x ∉ E : χ(ς_j(x - y_j)) = 1 ∀ j}` with the uniform law
`ν` on `Φ` and `γ = p 2^{-d} / |Φ|`. For distinct root sets `S_l` of sizes in `[2, 11]`, `d ≤ 10`
and real coefficients `b_l`, from the moving-root moments (H5, `Target.MovingRoot`):

`E_ν (∑_l b_l τ_{S_l})² ≤ γ r² [∑_l b_l² + 2^d · 6000 · r (∑_l |b_l|)²]` (`moving_root_conditional`),

the square of the paper's bound with `C = 6000`. The paper's hypothesis `E ⊇ {y_j}` is not
needed (on `Φ`, `χ(ς_j(x - y_j)) = 1` already forces `x ≠ y_j`), nor is `|Φ| ≥ (1 - e)p2^{-d}`,
which only serves to bound `γ`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.SecondOrder

open Sarkozy.Target

variable {p : ℕ} [hp : Fact p.Prime]

theorem chiR_target (a : ZMod p) : ((quadraticChar (ZMod p) a : ℤ) : ℝ) ^ 2 ≤ 1 := by
  rcases eq_or_ne a 0 with h | h
  · rw [h, quadraticChar_zero]; norm_num
  · rcases quadraticChar_dichotomy h with h' | h' <;> rw [h'] <;> norm_num

/-- The factor `1 + χ(ς(x - y))` is `2` when `χ(ς(x - y)) = 1` and lies in `[0, 2]`. -/
theorem one_add_chi_nonneg (a : ZMod p) : 0 ≤ 1 + ((quadraticChar (ZMod p) a : ℤ) : ℝ) := by
  rcases eq_or_ne a 0 with h | h
  · rw [h, quadraticChar_zero]; norm_num
  · rcases quadraticChar_dichotomy h with h' | h' <;> rw [h'] <;> norm_num

/-- **`cor:moving-root-conditional`** (squared form, `C = 6000`), from H5. -/
theorem moving_root_conditional (hM : Target.MovingRoot) (hp2 : p ≠ 2) {d : ℕ} (hd : d ≤ 10)
    (y : Fin d → ZMod p) (hy : Function.Injective y) (ς : Fin d → ZMod p)
    (E : Finset (ZMod p))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ι → Finset (ZMod p)) (hS : Function.Injective S)
    (hS2 : ∀ l, 2 ≤ (S l).card) (hS11 : ∀ l, (S l).card ≤ 11) (b : ι → ℝ)
    (Φ : Finset (ZMod p))
    (hΦ : Φ = univ.filter fun x => x ∉ E ∧ ∀ j, quadraticChar (ZMod p) (ς j * (x - y j)) = 1)
    (hΦne : Φ.Nonempty) :
    (1 / (Φ.card : ℝ)) * ∑ x ∈ Φ, (∑ l, b l * tau p (S l) x) ^ 2 ≤
      ((p : ℝ) / 2 ^ d / Φ.card) * (1 / Real.sqrt p) ^ 2 *
        (∑ l, b l ^ 2 + 2 ^ d * 6000 * (1 / Real.sqrt p) * (∑ l, |b l|) ^ 2) := by
  classical
  set r := 1 / Real.sqrt p with hr
  set F : ZMod p → ℝ := fun x => ∑ l, b l * tau p (S l) x with hF
  set P : ZMod p → ℝ := fun x => ∏ j, (1 + ((quadraticChar (ZMod p) (ς j * (x - y j)) : ℤ) : ℝ))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hΦpos : (0 : ℝ) < Φ.card := by exact_mod_cast card_pos.mpr hΦne
  have hr2 : r ^ 2 = 1 / (p : ℝ) := by
    simp only [hr, div_pow, one_pow, Real.sq_sqrt hp0.le]
  -- 1. the density of `ν` is at most `γ P / p`
  have hP0 : ∀ x, 0 ≤ P x := fun x => prod_nonneg fun j _ => one_add_chi_nonneg _
  have hPΦ : ∀ x ∈ Φ, P x = 2 ^ d := by
    intro x hx
    rw [hΦ, mem_filter] at hx
    simp only [P]
    rw [prod_congr rfl fun j _ => by rw [hx.2.2 j]]
    simp only [Int.cast_one]
    rw [prod_const, card_univ, Fintype.card_fin]
    norm_num
  have hdens : (1 / (Φ.card : ℝ)) * ∑ x ∈ Φ, F x ^ 2 ≤
      ((p : ℝ) / 2 ^ d / Φ.card) * ((1 / (p : ℝ)) * ∑ x, P x * F x ^ 2) := by
    have hsub : ∑ x ∈ Φ, P x * F x ^ 2 ≤ ∑ x, P x * F x ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ =>
        mul_nonneg (hP0 x) (sq_nonneg _)
    have heq : ∑ x ∈ Φ, P x * F x ^ 2 = 2 ^ d * ∑ x ∈ Φ, F x ^ 2 := by
      rw [mul_sum]; exact sum_congr rfl fun x hx => by rw [hPΦ x hx]
    have h2d : (0 : ℝ) < 2 ^ d := by positivity
    calc (1 / (Φ.card : ℝ)) * ∑ x ∈ Φ, F x ^ 2
        = ((p : ℝ) / 2 ^ d / Φ.card) * ((1 / (p : ℝ)) * ∑ x ∈ Φ, P x * F x ^ 2) := by
          rw [heq]; field_simp
      _ ≤ ((p : ℝ) / 2 ^ d / Φ.card) * ((1 / (p : ℝ)) * ∑ x, P x * F x ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hsub (by positivity)
  -- 2. expand `P` over subsets and `F²` over pairs
  have hPexp : ∀ x, P x = ∑ J ∈ (univ : Finset (Fin d)).powerset,
      (∏ j ∈ J, ((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ)) * chiA p (J.image y) x := by
    intro x
    simp only [P]
    rw [prod_one_add]
    refine sum_congr rfl fun J _ => ?_
    unfold chiA
    rw [prod_image (fun i _ j _ h => hy h), map_prod, Int.cast_prod, ← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    rw [map_mul, Int.cast_mul]
  have hFsq : ∀ x, F x ^ 2 = ∑ l, ∑ l', b l * b l' * (tau p (S l) x * tau p (S l') x) := by
    intro x
    simp only [F, sq, sum_mul, mul_sum]
    exact sum_congr rfl fun l _ => sum_congr rfl fun l' _ => by ring
  -- 3. the moment of each triple
  set X : Finset (Fin d) → ι → ι → ℝ := fun J l l' =>
    (1 / (p : ℝ)) * ∑ x, chiA p (J.image y) x * tau p (S l) x * tau p (S l') x
  have hmain : (1 / (p : ℝ)) * ∑ x, P x * F x ^ 2 = ∑ J ∈ (univ : Finset (Fin d)).powerset,
      (∏ j ∈ J, ((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ)) * ∑ l, ∑ l', b l * b l' * X J l l' := by
    have e1 : (1 / (p : ℝ)) * ∑ x, P x * F x ^ 2 = ∑ x, ∑ J ∈ (univ : Finset (Fin d)).powerset,
        ∑ l, ∑ l', (1 / (p : ℝ)) * ((∏ j ∈ J, ((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ)) *
          chiA p (J.image y) x) * (b l * b l' * (tau p (S l) x * tau p (S l') x)) := by
      rw [mul_sum]
      refine sum_congr rfl fun x _ => ?_
      rw [hPexp, hFsq, sum_mul, mul_sum]
      refine sum_congr rfl fun J _ => ?_
      rw [mul_sum, mul_sum]
      refine sum_congr rfl fun l _ => ?_
      rw [mul_sum, mul_sum]
      exact sum_congr rfl fun l' _ => by ring
    have e2 : ∑ J ∈ (univ : Finset (Fin d)).powerset,
        (∏ j ∈ J, ((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ)) * ∑ l, ∑ l', b l * b l' * X J l l' =
        ∑ J ∈ (univ : Finset (Fin d)).powerset, ∑ l, ∑ l', ∑ x, (1 / (p : ℝ)) *
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
  have hXbound : ∀ J ∈ (univ : Finset (Fin d)).powerset, ∀ l l',
      |X J l l' - (if S l = S l' ∧ J.image y = ∅ then 1 / (p : ℝ) else 0)| ≤ 6000 * r ^ 3 := by
    intro J _ l l'
    have hJ : (J.image y).card ≤ 10 := (card_image_le).trans ((card_le_univ J).trans
      (by rw [Fintype.card_fin]; exact hd))
    exact moving_root_uniform hM hp2 (S l) (S l') (J.image y) (hS2 l) (hS11 l) (hS2 l')
      (hS11 l') hJ
  -- 4. main term and error
  have hsign : ∀ J : Finset (Fin d), |∏ j ∈ J, ((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ)| ≤ 1 := by
    intro J
    rw [abs_prod]
    exact prod_le_one₀ (fun j _ => abs_nonneg _) fun j _ => by
      have := chiR_target (p := p) (ς j)
      nlinarith [abs_nonneg (((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ)),
        sq_abs (((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ))]
  set M : Finset (Fin d) → ι → ι → ℝ := fun J l l' =>
    if S l = S l' ∧ J.image y = ∅ then 1 / (p : ℝ) else 0
  have hMsum : ∑ J ∈ (univ : Finset (Fin d)).powerset,
      (∏ j ∈ J, ((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ)) * ∑ l, ∑ l', b l * b l' * M J l l' =
      (1 / (p : ℝ)) * ∑ l, b l ^ 2 := by
    rw [sum_eq_single (∅ : Finset (Fin d))]
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
  have herr : |∑ J ∈ (univ : Finset (Fin d)).powerset,
      (∏ j ∈ J, ((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ)) *
        ∑ l, ∑ l', b l * b l' * (X J l l' - M J l l')| ≤
      2 ^ d * 6000 * r ^ 3 * (∑ l, |b l|) ^ 2 := by
    calc _ ≤ ∑ J ∈ (univ : Finset (Fin d)).powerset, ∑ l, ∑ l', |b l| * |b l'| * (6000 * r ^ 3) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun J hJ => ?_)
          rw [abs_mul]
          refine (mul_le_of_le_one_left (abs_nonneg _) (hsign J)).trans ?_
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l _ => ?_)
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l' _ => ?_)
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left (hXbound J hJ l l') (by positivity)
      _ = 2 ^ d * 6000 * r ^ 3 * (∑ l, |b l|) ^ 2 := by
          have hinner : ∑ l, ∑ l', |b l| * |b l'| * (6000 * r ^ 3) =
              6000 * r ^ 3 * (∑ l, |b l|) ^ 2 := by
            rw [sq, sum_mul_sum, mul_sum]
            refine sum_congr rfl fun l _ => ?_
            rw [mul_sum]
            exact sum_congr rfl fun l' _ => by ring
          rw [sum_const, card_powerset, card_univ, Fintype.card_fin, nsmul_eq_mul, hinner]
          push_cast
          ring
  have hsplitX : ∀ J ∈ (univ : Finset (Fin d)).powerset,
      ∑ l, ∑ l', b l * b l' * X J l l' =
        ∑ l, ∑ l', b l * b l' * M J l l' + ∑ l, ∑ l', b l * b l' * (X J l l' - M J l l') := by
    intro J _
    rw [← sum_add_distrib]
    exact sum_congr rfl fun l _ => by rw [← sum_add_distrib]; exact sum_congr rfl fun l' _ => by ring
  have hkey : (1 / (p : ℝ)) * ∑ x, P x * F x ^ 2 ≤
      r ^ 2 * (∑ l, b l ^ 2 + 2 ^ d * 6000 * r * (∑ l, |b l|) ^ 2) := by
    rw [hmain]
    rw [sum_congr rfl fun J hJ => by rw [hsplitX J hJ, mul_add]]
    rw [sum_add_distrib, hMsum]
    have := (abs_le.mp herr).2
    have hr3 : r ^ 3 = r ^ 2 * r := by ring
    rw [hr3] at this
    rw [hr2] at this ⊢
    nlinarith [this]
  calc (1 / (Φ.card : ℝ)) * ∑ x ∈ Φ, F x ^ 2
      ≤ ((p : ℝ) / 2 ^ d / Φ.card) * ((1 / (p : ℝ)) * ∑ x, P x * F x ^ 2) := hdens
    _ ≤ ((p : ℝ) / 2 ^ d / Φ.card) * (r ^ 2 * (∑ l, b l ^ 2 + 2 ^ d * 6000 * r * (∑ l, |b l|) ^ 2)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = ((p : ℝ) / 2 ^ d / Φ.card) * r ^ 2 * (∑ l, b l ^ 2 + 2 ^ d * 6000 * r * (∑ l, |b l|) ^ 2) := by
        ring

end Sarkozy.SecondOrder
