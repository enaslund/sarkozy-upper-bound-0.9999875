module

public import Sarkozy.PositiveRoots.CoherentProductInputs

/-! Scalar identities putting the product-map prices in the paper's q,r notation. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Sarkozy.SpectralC Sarkozy.SpectralD

theorem variable_diagonal_price_eq {p : ℕ} (hp : 3 ≤ p) (c b : ℝ) :
    ((p : ℝ) / Real.sqrt (p - 2)) * (rp p + c * (p : ℝ)⁻¹ + b * rp p) =
      (1 + c * rp p + b) / Real.sqrt (1 - 2 * (p : ℝ)⁻¹) := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have he : 1 - 2 * (p : ℝ)⁻¹ = ((p : ℝ) - 2) / p := by field_simp
  have hf : rp p + c * (p : ℝ)⁻¹ + b * rp p = rp p * (1 + c * rp p + b) := by
    rw [← rp_sq]
    ring
  rw [he, Real.sqrt_div (by linarith : 0 ≤ (p : ℝ) - 2), hf]
  calc
    _ = ((p : ℝ) * rp p) / Real.sqrt (p - 2) * (1 + c * rp p + b) := by ring
    _ = Real.sqrt (p : ℝ) / Real.sqrt (p - 2) * (1 + c * rp p + b) := by
      rw [rp, ← div_eq_mul_inv, Real.div_sqrt]
    _ = _ := by rw [div_div_eq_mul_div]; ring

theorem entangled_image_factor_eq {p : ℕ} (hp : 2 ≤ p) :
    (p : ℝ) / Real.sqrt (p - 1) = 1 / (rp p * Real.sqrt (1 - (p : ℝ)⁻¹)) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hs0 : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have hs1 : Real.sqrt ((p : ℝ) - 1) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have he : 1 - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p := by field_simp
  rw [he, Real.sqrt_div (by linarith : 0 ≤ (p : ℝ) - 1), rp]
  field_simp
  exact (Real.sq_sqrt (Nat.cast_nonneg p)).symm

end Sarkozy.PositiveRoots.CoherentFrame
