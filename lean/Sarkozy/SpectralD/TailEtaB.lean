module

public import Sarkozy.SpectralD.TailQuotients

/-!
# The coupling allowance eta_B for class-three tail primes

The common numerical allowances cover both root matrices, whose model
row sums are at most 8856 and whose degree-one norms are at most 12.
-/

@[expose] public section

namespace Sarkozy.SpectralD

open Sarkozy.SpectralC

theorem tail_prime_ratio_sharp {p : ℕ} (hp : 2 ^ 512 ≤ p) :
    (p : ℝ) / (p - 1) ≤ 1 + (2 : ℝ)⁻¹ ^ 40 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hd : (p : ℝ) - 1 ≠ 0 := by linarith
  calc _ = 1 + 1 / ((p : ℝ) - 1) := by field_simp [hd]; ring
    _ ≤ _ := by linarith [tail_inv_sub_one hp]

theorem etaB_tail {p : ℕ} (hp : 2 ^ 512 ≤ p) (hp3 : p % 4 = 3)
    {R L ρ D Λnc : ℝ} (hR : R ≤ 1 + 2⁻¹ ^ 40) (hL0 : 0 ≤ L) (hL : L ≤ 8856)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 301768740) (hD0 : 0 ≤ D) (hD : D ≤ 12) :
    Cx.etaBcx p R L (1 / 1000) 64 ρ (1 / 100000000) L 1 Λnc
      (1 / 100000) D (1 / 1000) ≤ 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hfac : R * p / ((p : ℝ) - 1) ≤ 1 + 1 / 1000000 := by
    calc _ = R * ((p : ℝ) / (p - 1)) := by ring
      _ ≤ (1 + (2 : ℝ)⁻¹ ^ 40) * (1 + (2 : ℝ)⁻¹ ^ 40) :=
          mul_le_mul hR (tail_prime_ratio_sharp hp)
            (div_nonneg (by linarith) (by linarith)) (by positivity)
      _ ≤ 1 + 1 / 1000000 := by norm_num
  have hsqrt : Real.sqrt (1 / 100000000 * (L + 1 / 1000)) ≤ 1 / 100 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    linarith
  have hrho : rp p * 64 * ρ ≤ (2 : ℝ)⁻¹ ^ 40 * 64 * 301768740 :=
    mul_le_mul (mul_le_mul_of_nonneg_right (tail_rp_le40 hp) (by norm_num))
      hρ hρ0 (by positivity)
  have hsum : 1 / 1000 + rp p * 64 * ρ +
      (2 * Real.sqrt (1 / 100000000 * (L + 1 / 1000)) + 1 / 100000000) ≤ 1 / 10 := by
    norm_num at hrho
    linarith
  have h1 : (R * p / ((p : ℝ) - 1) - 1) * L ≤ (1 / 1000000) * 8856 := by
    calc _ ≤ (1 / 1000000) * L := mul_le_mul_of_nonneg_right (by linarith) hL0
      _ ≤ _ := mul_le_mul_of_nonneg_left hL (by norm_num)
  have hrp0 : 0 ≤ rp p := by unfold rp; positivity
  have h2 := mul_le_mul hfac hsum (by positivity)
    (by norm_num : (0 : ℝ) ≤ 1 + 1 / 1000000)
  have h3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD0 hD 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 100000)
  have h4 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hD (by norm_num : (0 : ℝ) ≤ 2))
    (by norm_num : (0 : ℝ) ≤ 1 / 1000)
  unfold Cx.etaBcx
  simp only [hp3, show ¬ (3 : ℕ) = 1 by decide, ite_false, zero_mul, add_zero]
  exact (add_le_add (add_le_add (add_le_add h1 h2) h3) h4).trans (by norm_num)

end Sarkozy.SpectralD
