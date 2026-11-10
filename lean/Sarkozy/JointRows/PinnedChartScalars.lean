module

public import Sarkozy.SpectralD.TailErrorBounds

/-! The remaining tail margin absorbs normalization and recentering. -/

@[expose] public section

namespace Sarkozy.JointRows.PinTail

variable {p : ℕ}

theorem deviation_small (hp : 2 ^ 512 ≤ p) :
    (2 : ℝ) ^ 44 * (Real.sqrt p)⁻¹ ≤ 1 / 1000000 := by
  have h := mul_le_mul_of_nonneg_left (SpectralD.tail_rp_le hp)
    (by positivity : (0 : ℝ) ≤ 2 ^ 44)
  exact h.trans (by norm_num)

theorem chart_tail_scalar (hp : 2 ^ 512 ≤ p) {c : ℝ} (hc0 : 3 ≤ c) (hc1 : c ≤ 258) :
    ((c - 1 / 50) * (Real.sqrt p)⁻¹) / (1 - 2 ^ 44 * (Real.sqrt p)⁻¹) +
      (2 ^ 44 * (Real.sqrt p)⁻¹) ^ 2 / (1 - 2 ^ 44 * (Real.sqrt p)⁻¹) ^ 2 ≤
        (c - 1 / 100) * (Real.sqrt p)⁻¹ := by
  let r := (Real.sqrt (p : ℝ))⁻¹
  let d := (2 : ℝ) ^ 44 * r
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hd : d ≤ 1 / 1000000 := deviation_small hp
  have hden : 0 < 1 - d := by linarith
  have hs : ((c - 1 / 50) * r) / (1 - d) ≤ (c - 3 / 200) * r := by
    calc
      _ ≤ ((c - 1 / 50) * r) / (1 - 1 / 1000000) :=
        div_le_div_of_nonneg_left (mul_nonneg (by linarith) hr0)
          (by norm_num) (by linarith)
      _ ≤ _ := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1 - 1 / 1000000)]
        have hc : c - 1 / 50 ≤ (c - 3 / 200) * (1 - 1 / 1000000) := by linarith
        have hh := mul_le_mul_of_nonneg_right hc hr0
        nlinarith
  have hsq : d ^ 2 / (1 - d) ^ 2 ≤ 4 * d ^ 2 := by
    rw [div_le_iff₀ (pow_pos hden 2)]
    have hh : (1 / 4 : ℝ) ≤ (1 - d) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg d)]
  have herr : 4 * d ^ 2 ≤ (1 / 200) * r := by
    have hr := mul_le_mul_of_nonneg_right (SpectralD.tail_rp_le hp) hr0
    have hh := mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ 2 ^ 90)
    dsimp [d, r] at hh hr0 ⊢
    nlinarith only [hh, hr0]
  change ((c - 1 / 50) * r) / (1 - d) + d ^ 2 / (1 - d) ^ 2 ≤ _
  nlinarith

end Sarkozy.JointRows.PinTail
