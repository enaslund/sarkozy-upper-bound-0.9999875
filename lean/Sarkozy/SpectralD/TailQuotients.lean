module

public import Sarkozy.SpectralD.TailErrorBounds

/-!
# Explicit denominator estimates at tail primes

These inequalities turn the small-pair row bounds into the numerical
eta_Q and epsilon_V allowances of the root spectral criterion.
-/

@[expose] public section

namespace Sarkozy.SpectralD

theorem tail_prime_ratio {p : ℕ} (hp : 2 ^ 512 ≤ p) : (p : ℝ) / (p - 1) ≤ 2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (show 2 ≤ p by omega)
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem tail_inv_sub_one {p : ℕ} (hp : 2 ^ 512 ≤ p) :
    1 / ((p : ℝ) - 1) ≤ (2 : ℝ)⁻¹ ^ 40 := by
  have hp' : (2 : ℝ) ^ 40 + 1 ≤ p := by
    exact_mod_cast (show 2 ^ 40 + 1 ≤ p by omega)
  have h := inv_anti₀ (by positivity : (0 : ℝ) < 2 ^ 40) (by linarith : (2 : ℝ) ^ 40 ≤ p - 1)
  simpa only [one_div, inv_pow] using h

theorem tail_rp_le40 {p : ℕ} (hp : 2 ^ 512 ≤ p) :
    (Real.sqrt p)⁻¹ ≤ (2 : ℝ)⁻¹ ^ 40 := (tail_rp_le hp).trans (by norm_num)

theorem tail_root_quotient {p : ℕ} (hp : 2 ^ 512 ≤ p) :
    1 / (((p : ℝ) - 1) * (Real.sqrt p)⁻¹) ≤ 2 * (Real.sqrt p)⁻¹ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hs : (p : ℝ) * (Real.sqrt p)⁻¹ = Real.sqrt p := by
    rw [eq_comm, eq_mul_inv_iff_mul_eq₀ hs0.ne', Real.mul_self_sqrt hp0.le]
  calc _ = ((p : ℝ) - 1)⁻¹ * Real.sqrt p := by rw [one_div, mul_inv, inv_inv]
    _ = ((p : ℝ) - 1)⁻¹ * ((p : ℝ) * (Real.sqrt p)⁻¹) :=
        congrArg (fun t => ((p : ℝ) - 1)⁻¹ * t) hs.symm
    _ = (p : ℝ) / (p - 1) * (Real.sqrt p)⁻¹ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (tail_prime_ratio hp) (by positivity)

theorem tail_etaQ {p : ℕ} (hp : 2 ^ 512 ≤ p) {d : ℝ} (hd : d ≤ 12) :
    d / ((p : ℝ) - 1) + (p : ℝ) / (p - 1) * 2⁻¹ ^ 40 +
      36 / (((p : ℝ) - 1) * (Real.sqrt p)⁻¹) ≤ 1 / 1000 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have h1 : d / ((p : ℝ) - 1) ≤ 12 * (2 : ℝ)⁻¹ ^ 40 := by
    calc _ ≤ 12 / ((p : ℝ) - 1) := div_le_div_of_nonneg_right hd (by linarith)
      _ = 12 * (1 / ((p : ℝ) - 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (tail_inv_sub_one hp) (by norm_num)
  have h2 := mul_le_mul_of_nonneg_right (tail_prime_ratio hp)
    (by positivity : (0 : ℝ) ≤ 2⁻¹ ^ 40)
  have h3 : 36 / (((p : ℝ) - 1) * (Real.sqrt p)⁻¹) ≤ 72 * (2 : ℝ)⁻¹ ^ 40 := by
    calc _ = 36 * (1 / (((p : ℝ) - 1) * (Real.sqrt p)⁻¹)) := by ring
      _ ≤ 36 * (2 * (Real.sqrt p)⁻¹) :=
          mul_le_mul_of_nonneg_left (tail_root_quotient hp) (by norm_num)
      _ = 72 * (Real.sqrt p)⁻¹ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (tail_rp_le40 hp) (by norm_num)
  exact (add_le_add (add_le_add h1 h2) h3).trans (by norm_num)

theorem tail_epsilonV {p : ℕ} (hp : 2 ^ 512 ≤ p) :
    (36 - 1) / ((p : ℝ) - 1) + (p : ℝ) / (p - 1) * (Real.sqrt p)⁻¹ * 36 ≤
      1 / 100000 := by
  have h1 : (36 - 1) / ((p : ℝ) - 1) ≤ 35 * (2 : ℝ)⁻¹ ^ 40 := by
    calc _ = 35 * (1 / ((p : ℝ) - 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (tail_inv_sub_one hp) (by norm_num)
  have h2 : (p : ℝ) / (p - 1) * (Real.sqrt p)⁻¹ * 36 ≤ 72 * (2 : ℝ)⁻¹ ^ 40 := by
    calc _ ≤ (2 : ℝ) * (2⁻¹ ^ 40) * 36 := by
          gcongr
          · exact tail_prime_ratio hp
          · exact tail_rp_le40 hp
      _ = _ := by ring
  exact (add_le_add h1 h2).trans (by norm_num)

end Sarkozy.SpectralD
