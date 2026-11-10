module

public import Sarkozy.SpectralD.CollisionNumerics

/-!
# A uniform collision coefficient for the root cuts

For a 36-vertex half with internal degree at most 10 and cross degree at most
12, the natural collision bound is at most 2^35/q for every q ≥ 2^64.
No numerical collision certificate is assumed.
-/

@[expose] public section

namespace Sarkozy.SpectralD

open Finset Sarkozy.Labellings Sarkozy.Extraction

variable {U : Type*} [Fintype U] [DecidableEq U]

theorem collision_weight_bound (G : OrientedGraph U) (ς : U → U → ℤ)
    (hd : ∀ i, rowsDeg0 G i ≤ 10) (hr : ∀ i, collisionR ς i ≤ 12) (i j : U) :
    collisionA G ς i j ≤ 2 ^ 22 := by
  have hm : rowsMg G ς j i ≤ 10 := (card_filter_le _ _).trans (hd i)
  unfold collisionA
  apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  have := hr i
  omega

theorem collision_weight_sum (G : OrientedGraph U) (ς : U → U → ℤ)
    (hn : Fintype.card U = 36) (hd : ∀ i, rowsDeg0 G i ≤ 10)
    (hr : ∀ i, collisionR ς i ≤ 12) :
    ∑ i, ∑ j, collisionA G ς i j ≤ 2 ^ 33 := by
  calc ∑ i, ∑ j, collisionA G ς i j ≤ ∑ _i : U, ∑ _j : U, (2 : ℝ) ^ 22 :=
        sum_le_sum fun i _ => sum_le_sum fun j _ => collision_weight_bound G ς hd hr i j
    _ ≤ 2 ^ 33 := by simp only [sum_const, card_univ, hn, nsmul_eq_mul]; norm_num

theorem collisionXi_uniform (G : OrientedGraph U) (ς : U → U → ℤ)
    (hn : Fintype.card U = 36) (hd : ∀ i, rowsDeg0 G i ≤ 10)
    (hr : ∀ i, collisionR ς i ≤ 12) {q : ℝ} (hq : 0 < q) :
    0 ≤ collisionXi G ς q ∧ collisionXi G ς q ≤ 2 ^ 43 / q := by
  have hA : 0 ≤ ∑ i, ∑ j, collisionA G ς i j :=
    sum_nonneg fun i _ => sum_nonneg fun j _ => by unfold collisionA; positivity
  have hΔ : collisionDeltaPlus G ≤ 10 := Finset.sup_le fun i _ => hd i
  have hs : Real.sqrt 2 ^ collisionDeltaPlus G ≤ (2 : ℝ) ^ 10 :=
    (pow_le_pow_left₀ (Real.sqrt_nonneg _) (by norm_num : Real.sqrt 2 ≤ (2 : ℝ)) _).trans
      (pow_le_pow_right₀ (by norm_num) hΔ)
  constructor
  · unfold collisionXi
    exact mul_nonneg (mul_nonneg (by positivity) (inv_nonneg.mpr hq.le)) hA
  · unfold collisionXi
    calc Real.sqrt 2 ^ collisionDeltaPlus G * q⁻¹ * ∑ i, ∑ j, collisionA G ς i j
        ≤ 2 ^ 10 * q⁻¹ * (2 ^ 33 : ℝ) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hs (inv_nonneg.mpr hq.le))
            (collision_weight_sum G ς hn hd hr) hA (by positivity)
      _ = 2 ^ 43 / q := by norm_num [div_eq_mul_inv]; ring

theorem collision_exp_uniform (G : OrientedGraph U) (ς : U → U → ℤ)
    (hn : Fintype.card U = 36) (hd : ∀ i, rowsDeg0 G i ≤ 10)
    (hr : ∀ i, collisionR ς i ≤ 12) {q : ℝ} (hq : 2 ^ 64 ≤ q) :
    Real.exp (collisionXi G ς q) - 1 - collisionXi G ς q ≤ 2 ^ 33 / q := by
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  obtain ⟨hX0, hX⟩ := collisionXi_uniform G ς hn hd hr hq0
  have hX1 : collisionXi G ς q ≤ 1 := hX.trans ((div_le_one hq0).mpr (by
    norm_num at hq ⊢
    linarith))
  refine (exp_remainder_le_square hX0 hX1).trans
    ((pow_le_pow_left₀ hX0 hX 2).trans ?_)
  have hnum : ((2 : ℝ) ^ 43) ^ 2 ≤ 2 ^ 33 * q := by
    norm_num at hq ⊢
    linarith
  rw [div_pow]
  calc ((2 : ℝ) ^ 43) ^ 2 / q ^ 2 ≤ (2 ^ 33 * q) / q ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ = 2 ^ 33 / q := by field_simp

theorem collisionDnat_uniform (G : OrientedGraph U) (ς : U → U → ℤ)
    (hn : Fintype.card U = 36) (hd : ∀ i, rowsDeg0 G i ≤ 10)
    (hr : ∀ i, collisionR ς i ≤ 12) {q : ℝ} (hq : 2 ^ 64 ≤ q) :
    collisionDnat G ς q 36 ≤ 2 ^ 35 / q := by
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  have hsum : q⁻¹ * ∑ i, ∑ j, collisionA G ς i j ≤ 2 ^ 33 / q := by
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (collision_weight_sum G ς hn hd hr)
      (inv_nonneg.mpr hq0.le)
  have hsum0 : 0 ≤ q⁻¹ * ∑ i, ∑ j, collisionA G ς i j :=
    mul_nonneg (inv_nonneg.mpr hq0.le)
      (sum_nonneg fun i _ => sum_nonneg fun j _ => by unfold collisionA; positivity)
  have hexp0 : 0 ≤ Real.exp (collisionXi G ς q) - 1 - collisionXi G ς q := by
    linarith [Real.add_one_le_exp (collisionXi G ς q)]
  unfold collisionDnat
  calc _ ≤ 2 * (2 ^ 33 / q + 2 ^ 33 / q) :=
        mul_le_mul (collision_count_ratio G ς hn hd hr hq)
          (add_le_add hsum (collision_exp_uniform G ς hn hd hr hq))
          (add_nonneg hsum0 hexp0) (by norm_num)
    _ = 2 ^ 35 / q := by norm_num; ring

end Sarkozy.SpectralD
