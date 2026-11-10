module

public import Sarkozy.L20Cap.RectangleCertificate.Data
public import Sarkozy.F3Kernel.WeightBounds

/-! Uniform rational factor bounds for the rectangle at p = 2^40. -/

@[expose] public section

namespace Sarkozy.L20Cap.RectangleCertificate

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

noncomputable def anchor : ℝ := 2 ^ 40

theorem anchor_pos : 0 < anchor := by norm_num [anchor]

theorem sqrt_anchor : Real.sqrt anchor = 1048576 := by
  rw [show anchor = (1048576 : ℝ) ^ 2 by norm_num [anchor], Real.sqrt_sq_eq_abs]
  norm_num

theorem coarse_error_small (s n : ℕ) (hs : s ≤ 2) (hn : n ≤ 12) :
    coarseError s anchor n ≤ (1 / 1000000 : ℝ) := by
  have hn' : (n : ℝ) ≤ 12 := by exact_mod_cast hn
  interval_cases s <;> norm_num [coarseError, coarseH, sqrt_anchor] <;> linarith

theorem half_degree : ∀ i : Fin 6, rowsDeg0 G6 i ≤ 2 := by decide +kernel

theorem half_max_degree : univ.sup (rowsDeg0 G6) = 2 := by decide +kernel

theorem ehat_small : leafEhat G6 anchor 6 ≤ (1 / 1000000 : ℝ) := by
  rw [leafEhat, half_max_degree]
  exact coarse_error_small 2 6 (by decide) (by decide)

theorem ehat_lt_one : leafEhat G6 anchor 6 < 1 := ehat_small.trans_lt (by norm_num)

theorem weights_m_small : ∀ i j : Fin 6, weightM G6 D20Z i j ≤ 4 := by
  have hc : ∀ i j : Fin 6, rowsCU G6 D20Z i j ≤ 2 := by decide +kernel
  intro i j
  unfold weightM
  exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (hc i j)).trans_eq (by norm_num)

theorem weights_rho_small : ∀ i j : Fin 6, weightRho G6 D20Z i j ≤ 16 := by
  have hc : ∀ i j : Fin 6, rowsMg G6 D20Z j i + rowsCU G6 D20Z j i ≤ 4 := by
    decide +kernel
  intro i j
  unfold weightRho
  exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (hc i j)).trans_eq (by norm_num)

theorem special_m_small (s : ℕ) : leafS G6 D20Z (weightM G6 D20Z) s ≤ 24 := by
  apply F3Kernel.leafS_le_row_bound G6 D20Z _ (weightM_nonneg G6 D20Z) (by norm_num)
  intro i
  calc
    _ ≤ ∑ _j : Fin 6, (4 : ℝ) := sum_le_sum fun j _ => weights_m_small i j
    _ = 24 := by norm_num

theorem special_rho_small (s : ℕ) : leafS G6 D20Z (weightRho G6 D20Z) s ≤ 96 := by
  apply F3Kernel.leafS_le_row_bound G6 D20Z _ (weightRho_nonneg G6 D20Z) (by norm_num)
  intro i
  calc
    _ ≤ ∑ _j : Fin 6, (16 : ℝ) := sum_le_sum fun j _ => weights_rho_small i j
    _ = 96 := by norm_num

theorem fm_small (s : ℕ) (hs : s ≤ 2) :
    leafFm G6 D20Z anchor 6 (leafEhat G6 anchor 6) s ≤ (10001 / 10000 : ℝ) := by
  have he := coarse_error_small s 6 hs (by decide)
  have hS := special_m_small s
  have hpow : (2 : ℝ) ^ s ≤ 4 :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hs).trans_eq (by norm_num)
  have hmul : (2 : ℝ) ^ s * leafS G6 D20Z (weightM G6 D20Z) s ≤ 4 * 24 :=
    mul_le_mul hpow hS (leafS_nonneg G6 D20Z _ (weightM_nonneg G6 D20Z) s) (by norm_num)
  unfold leafFm
  rw [div_le_iff₀ (by linarith [ehat_small] : 0 < 1 - leafEhat G6 anchor 6), sqrt_anchor]
  norm_num only [show (1048576 : ℝ)⁻¹ ^ 2 = 1 / 1099511627776 by norm_num]
  nlinarith [ehat_small]

theorem frho_small (s : ℕ) (hs : s ≤ 2) :
    leafFrho G6 D20Z anchor 6 (leafEhat G6 anchor 6) s ≤ (10001 / 10000 : ℝ) := by
  have he := coarse_error_small s 12 hs (by decide)
  have hS := special_rho_small s
  have hpow : (2 : ℝ) ^ s ≤ 4 :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hs).trans_eq (by norm_num)
  have hmul : (2 : ℝ) ^ s * leafS G6 D20Z (weightRho G6 D20Z) s ≤ 4 * 96 :=
    mul_le_mul hpow hS (leafS_nonneg G6 D20Z _ (weightRho_nonneg G6 D20Z) s) (by norm_num)
  unfold leafFrho
  rw [div_le_iff₀ (by linarith [ehat_small] : 0 < 1 - leafEhat G6 anchor 6), sqrt_anchor]
  norm_num only [show (1048576 : ℝ)⁻¹ ^ 2 = 1 / 1099511627776 by norm_num]
  change 1 + coarseError s anchor 12 + _ ≤ _
  nlinarith [ehat_small]

theorem rows_ratio_small : rowsR G6 anchor 6 univ ≤ (10001 / 10000 : ℝ) := by
  unfold rowsR
  calc
    _ ≤ ∏ _i : Fin 6, (1000003 / 1000000 : ℝ) := by
      apply prod_le_prod₀
      · intro i _
        have he := coarse_error_small (rowsDeg0 G6 i) 6 (half_degree i) (by decide)
        have h0 := coarseError_nonneg (q := anchor) (by norm_num : (0 : ℝ) ≤ 6)
          (rowsDeg0 G6 i)
        norm_num only [Nat.cast_ofNat] at he ⊢
        exact div_nonneg (by linarith) (by linarith)
      · intro i _
        have he := coarse_error_small (rowsDeg0 G6 i) 6 (half_degree i) (by decide)
        norm_num only [Nat.cast_ofNat] at he ⊢
        rw [div_le_iff₀ (by linarith : 0 < 1 - coarseError (rowsDeg0 G6 i) anchor 6)]
        linarith
    _ ≤ _ := by norm_num

theorem coefficient_prefactor :
    (10001 / 10000 : ℝ) ^ 6 / (1 - leafEhat G6 anchor 6) ^ 2 ≤ 1001 / 1000 := by
  have hd : 0 < 1 - leafEhat G6 anchor 6 := by linarith [ehat_small]
  rw [div_le_iff₀ (sq_pos_of_pos hd)]
  nlinarith [ehat_small, sq_nonneg (leafEhat G6 anchor 6)]

end Sarkozy.L20Cap.RectangleCertificate
