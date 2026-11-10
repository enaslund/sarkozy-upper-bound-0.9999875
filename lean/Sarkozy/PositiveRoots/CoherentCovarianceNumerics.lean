module

public import Sarkozy.PositiveRoots.CoherentSoftBound

/-! Uniform numerical bounds for the full coherent covariance above 2^40. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Sarkozy.L20Cap Sarkozy.SpectralD Sarkozy.SpectralC

noncomputable def coherentCovariancePrice (p : ℕ) (a M : ℝ) : ℝ :=
  (p : ℝ)⁻¹ * (256 * a * ((20992 / 225 : ℝ) * (coreCubeDensity p / 16) +
    (2108 / 225 : ℝ) * ((p : ℝ) / (p - 1))) +
      (32 / 225 + 8 / 25 + 2028 / 25 : ℝ) * M)

variable {p : ℕ}

theorem q_small_40 (hp40 : 2 ^ 40 ≤ p) : (p : ℝ)⁻¹ ≤ 1 / 100000000 := by
  have hp : (100000000 : ℝ) ≤ p := by exact_mod_cast (by omega : 100000000 ≤ p)
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 100000000) hp

theorem rp_small_40 (hp40 : 2 ^ 40 ≤ p) : rp p ≤ 1 / 1000000 := by
  have hp : (1000000 : ℝ) ^ 2 ≤ p := by
    norm_num
    exact_mod_cast (by omega : 1000000000000 ≤ p)
  have hs : (1000000 : ℝ) ≤ Real.sqrt p := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1000000)]
    exact Real.sqrt_le_sqrt hp
  simpa only [rp, one_div] using
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1000000) hs

theorem core_density_small_40 (hp40 : 2 ^ 40 ≤ p) :
    coreCubeDensity p / 16 ≤ 10001 / 10000 := by
  let q : ℝ := (p : ℝ)⁻¹
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq : q ≤ 1 / 100000000 := q_small_40 hp40
  have htheta : 1 - 11 * q ≤ (1 - q) * (1 - 3 * q) * (1 - 7 * q) := by
    have h := mul_nonneg (sq_nonneg q) (show 0 ≤ 31 - 21 * q by linarith)
    nlinarith
  have htheta0 : 0 < (1 - q) * (1 - 3 * q) * (1 - 7 * q) := by linarith
  have he : coreCubeDensity p / 16 = 1 / ((1 - q) * (1 - 3 * q) * (1 - 7 * q)) := by
    unfold coreCubeDensity q
    ring
  rw [he, div_le_iff₀ htheta0]
  linarith

theorem private_density_small_40 (hp40 : 2 ^ 40 ≤ p) :
    (p : ℝ) / (p - 1) ≤ 10001 / 10000 := by
  have hp : (100000000 : ℝ) ≤ p := by exact_mod_cast (by omega : 100000000 ≤ p)
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < p - 1)]
  linarith

variable [Fact p.Prime]

theorem etaL_small_40 (hp40 : 2 ^ 40 ≤ p) : etaL (ZMod p) ≤ 1 / 50000 := by
  have hq := q_small_40 hp40
  have hr := rp_small_40 hp40
  have he : etaL (ZMod p) = 2 * (p : ℝ)⁻¹ + 11 * rp p := by
    unfold etaL rp
    rw [ZMod.card]
    ring
  rw [he]
  linarith

theorem rectangleMassUpper_small_40 (hp40 : 2 ^ 40 ≤ p) :
    rectangleMassUpper p ≤ 10001 / 10000 := by
  have hq := q_small_40 hp40
  have he := etaL_small_40 hp40
  have he0 : 0 ≤ etaL (ZMod p) := by unfold etaL; positivity
  unfold rectangleMassUpper
  rw [div_le_iff₀ (by linarith : 0 < 1 - (p : ℝ)⁻¹)]
  have hs := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + etaL (ZMod p))
    (show 1 + etaL (ZMod p) ≤ 1 + 1 / 50000 by linarith) 2
  nlinarith

theorem coherent_covariance_price_lt (hp40 : 2 ^ 40 ≤ p) :
    coherentCovariancePrice p (rectangleMassUpper p) (rectangleMassUpper p ^ 2) <
      26400 * (p : ℝ)⁻¹ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have ha0 := rectangleMassUpper_nonneg (p := p)
  have ha := rectangleMassUpper_small_40 hp40
  have hc := core_density_small_40 hp40
  have hp := private_density_small_40 hp40
  have hc0 : 0 ≤ coreCubeDensity p / 16 := div_nonneg
    (coreCubeDensity_pos (by omega : 7 < p)).le (by norm_num)
  have hp' : (7 : ℝ) < p := by exact_mod_cast (by omega : 7 < p)
  have hp1 : 0 ≤ (p : ℝ) / (p - 1) := div_nonneg hp0.le (by linarith)
  have hb : 256 * rectangleMassUpper p *
      ((20992 / 225 : ℝ) * (coreCubeDensity p / 16) + (2108 / 225 : ℝ) * ((p : ℝ) / (p - 1))) +
      (32 / 225 + 8 / 25 + 2028 / 25 : ℝ) * rectangleMassUpper p ^ 2 ≤
      256 * (10001 / 10000 : ℝ) *
      ((20992 / 225 : ℝ) * (10001 / 10000) + (2108 / 225 : ℝ) * (10001 / 10000)) +
      (32 / 225 + 8 / 25 + 2028 / 25 : ℝ) * (10001 / 10000) ^ 2 := by
    gcongr
  have hnum : 256 * (10001 / 10000 : ℝ) *
      ((20992 / 225 : ℝ) * (10001 / 10000) + (2108 / 225 : ℝ) * (10001 / 10000)) +
      (32 / 225 + 8 / 25 + 2028 / 25 : ℝ) * (10001 / 10000) ^ 2 < 26400 := by norm_num
  unfold coherentCovariancePrice
  calc
    _ < (p : ℝ)⁻¹ * 26400 := mul_lt_mul_of_pos_left (hb.trans_lt hnum) (inv_pos.mpr hp0)
    _ = _ := mul_comm _ _

end Sarkozy.PositiveRoots.CoherentFrame
