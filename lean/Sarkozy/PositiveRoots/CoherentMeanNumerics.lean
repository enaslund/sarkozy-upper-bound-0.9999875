module

public import Sarkozy.PositiveRoots.CoherentMeanOrder

/-! Uniform numerical prices for the actual invariant branch, already for `p ≥ 4096`. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Sarkozy.SpectralC Sarkozy.SpectralD Sarkozy.L20Cap

variable {p : ℕ}

theorem q_le_4096 (hp : 4096 ≤ p) : (p : ℝ)⁻¹ ≤ 1 / 4096 := by
  have h : (4096 : ℝ) ≤ p := by exact_mod_cast hp
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4096) h

theorem chamberCubeDensity_le (hp : 4096 ≤ p) : chamberCubeDensity p ≤ 81 / 5 := by
  have hq := q_le_4096 hp
  have hq0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have h1 : (4089 / 4096 : ℝ) ≤ 1 - (p : ℝ)⁻¹ := by nlinarith
  have h3 : (4089 / 4096 : ℝ) ≤ 1 - 3 * (p : ℝ)⁻¹ := by nlinarith
  have h7 : (4089 / 4096 : ℝ) ≤ 1 - 7 * (p : ℝ)⁻¹ := by nlinarith
  have h4 : (4089 / 4096 : ℝ) ≤ 1 - 4 * (p : ℝ)⁻¹ := by nlinarith
  have h5 : (4089 / 4096 : ℝ) ≤ 1 - 5 * (p : ℝ)⁻¹ := by nlinarith
  have hd : (4089 / 4096 : ℝ) ^ 5 ≤
      (1 - (p : ℝ)⁻¹) * (1 - 3 * (p : ℝ)⁻¹) * (1 - 7 * (p : ℝ)⁻¹) *
        (1 - 4 * (p : ℝ)⁻¹) * (1 - 5 * (p : ℝ)⁻¹) := by
    calc
      _ = (4089 / 4096 : ℝ) * (4089 / 4096) * (4089 / 4096) *
          (4089 / 4096) * (4089 / 4096) := by ring
      _ ≤ _ := by gcongr
  unfold chamberCubeDensity
  have hb := (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 16)
    (by norm_num : (0 : ℝ) < (4089 / 4096) ^ 5) hd).trans
      (by norm_num : (16 : ℝ) / (4089 / 4096) ^ 5 ≤ 81 / 5)
  simpa only [div_eq_mul_inv, one_mul] using hb

theorem privateCompression_le (hp : 4096 ≤ p) : privateCompression p ≤ 101 / 100 := by
  have hq := q_le_4096 hp
  have h4 : (4091 / 4096 : ℝ) ≤ 1 - 4 * (p : ℝ)⁻¹ := by linarith
  have h5 : (4091 / 4096 : ℝ) ≤ 1 - 5 * (p : ℝ)⁻¹ := by linarith
  have hd : (4091 / 4096 : ℝ) ^ 2 ≤ (1 - 4 * (p : ℝ)⁻¹) * (1 - 5 * (p : ℝ)⁻¹) := by
    rw [pow_two]
    gcongr
  rw [privateCompression_eq (by omega)]
  have hb := (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) < (4091 / 4096) ^ 2) hd).trans
      (by norm_num : (1 : ℝ) / (4091 / 4096) ^ 2 ≤ 101 / 100)
  simpa only [div_eq_mul_inv] using hb

theorem mixedMeanPrice_le (hp : 4096 ≤ p) : mixedMeanPrice p ≤ 17 / 10 := by
  have hq := q_le_4096 hp
  have hr := rp_le hp
  have hΓ : 0 ≤ 1 + 42 * rp p + 56 * (p : ℝ)⁻¹ := by
    have := rp_nonneg (p := p)
    positivity
  calc
    _ ≤ (101 / 100 : ℝ) * (1 + 42 * (1 / 64) + 56 * (1 / 4096)) :=
      mul_le_mul (privateCompression_le hp) (by nlinarith) hΓ (by norm_num)
    _ ≤ _ := by norm_num

theorem invariantMeanPrice_le (hp : 4096 ≤ p) : invariantMeanPrice p ≤ 3 / 2 := by
  have hc := chamberCubeDensity_le hp
  have hm := mixedMeanPrice_le hp
  unfold invariantMeanPrice
  linarith

theorem invariant_branch_below (hp : 4096 ≤ p) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 12 / 5) :
    CoherentParameters.strength t * invariantMeanPrice p ≤ 18 / 5 := by
  have hs := CoherentParameters.strength_le_endpoint ht1
  have hs0 := CoherentParameters.strength_nonneg ht0
  calc
    _ ≤ CoherentParameters.strength t * (3 / 2) :=
      mul_le_mul_of_nonneg_left (invariantMeanPrice_le hp) hs0
    _ ≤ _ := by linarith

end Sarkozy.PositiveRoots.CoherentFrame
