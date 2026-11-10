module

public import Sarkozy.L20Cap.BalancedGeometry
public import Sarkozy.L20Cap.SanityX1

/-! Identify the extraction count errors with `Λ_c`, `U_c`, and `E_{c,j}`. -/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy.Extraction

theorem balanced_error_zero {Q : ℝ} (hQ : 0 < Q) :
    coarseError 0 Q 6 = 6 * Q⁻¹ := by
  norm_num [coarseError, coarseH, coverRow_r_sq hQ]

theorem balanced_error_two {Q : ℝ} (hQ : 0 < Q) :
    coarseError 2 Q 6 = (Real.sqrt Q)⁻¹ + 24 * Q⁻¹ := by
  norm_num [coarseError, coarseH, coverRow_r_sq hQ]
  ring

theorem balanced_Ec {Q : ℝ} (hQ : 0 < Q) (j : ℕ) :
    coarseError j Q 12 = Ec (Real.sqrt Q)⁻¹ Q⁻¹ j := by
  have h2 : (2 : ℝ) ^ j * (2 : ℝ)⁻¹ ^ j = 1 := by
    rw [← mul_pow]
    norm_num
  unfold coarseError coarseH Ec
  rw [coverRow_r_sq hQ]
  calc _ = (((j : ℝ) / 2 - 1) * 2 ^ j + 2 ^ j * (2 : ℝ)⁻¹ ^ j) *
        (Real.sqrt Q)⁻¹ + 12 * 2 ^ j * Q⁻¹ := by ring
    _ = _ := by rw [h2]

theorem balanced_Lint {Q : ℝ} (hQ : 0 < Q) :
    collisionLint G6 Q 6 = Lamc (Real.sqrt Q)⁻¹ Q⁻¹ := by
  unfold collisionLint
  simp_rw [balanced_degree]
  norm_num [Fin.prod_univ_six, balanced_error_zero hQ, balanced_error_two hQ, Lamc]
  ring

theorem balanced_Lamc_pos {Q : ℝ} (hQ : 64 ≤ Q) :
    0 < Lamc (Real.sqrt Q)⁻¹ Q⁻¹ := by
  rw [← balanced_Lint (by linarith : 0 < Q)]
  exact prod_pos fun i _ => sub_pos.mpr (SanityX1.coarseError_G6_lt hQ i)

theorem balanced_Ups {Q : ℝ} (hQ : 0 < Q) :
    collisionUps G6 D20Z Q 6 = Uc (Real.sqrt Q)⁻¹ Q⁻¹ := by
  unfold collisionUps
  simp_rw [balanced_total_degree]
  norm_num [balanced_Ec hQ, Uc]

theorem balanced_UpsK (π : ℕ → Fin 6 → ℕ) {Q : ℝ} (hQ : 0 < Q) {k : ℕ}
    (hk : 2 ≤ k) : collisionUpsK G6 D20Z π Q 6 k = Uc (Real.sqrt Q)⁻¹ Q⁻¹ := by
  rw [collisionUpsK_eq G6 D20Z π Q 6 (by rwa [balanced_delta]), balanced_Ups hQ]

theorem balanced_Ec_nonneg {Q : ℝ} (hQ : 0 < Q) (j : ℕ) :
    0 ≤ Ec (Real.sqrt Q)⁻¹ Q⁻¹ j := by
  rw [← balanced_Ec hQ]
  exact coarseError_nonneg (by norm_num) j

theorem balanced_Uc_nonneg {Q : ℝ} (hQ : 0 < Q) :
    0 ≤ Uc (Real.sqrt Q)⁻¹ Q⁻¹ := by
  unfold Uc
  have h := balanced_Ec_nonneg hQ 4
  positivity

end Sarkozy.L20Cap
