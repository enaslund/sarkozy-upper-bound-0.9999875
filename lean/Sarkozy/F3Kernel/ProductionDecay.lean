module

public import Sarkozy.F3Kernel.ProductionCoefficients

/-!
# Endpoint extension of the certified nonstar coefficients

The production polynomial divided by r = p^(-1/2) is a polynomial with
nonnegative coefficients. Its value at one endpoint bounds every larger p.
This supplies the nonstar input in the monotone spectral endpoint argument.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset

noncomputable def normalizedProduction (cap : ℕ → ℕ) (r : ℝ) : ℝ :=
  (cap 2 : ℝ) * r + (cap 3 : ℝ) * r ^ 2 + (cap 4 : ℝ) * r ^ 3

theorem normalizedProduction_nonneg (cap : ℕ → ℕ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ normalizedProduction cap r := by
  unfold normalizedProduction
  positivity

theorem normalizedProduction_mono (cap : ℕ → ℕ) {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) :
    normalizedProduction cap r ≤ normalizedProduction cap s := by
  unfold normalizedProduction
  exact add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hrs (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrs 2) (Nat.cast_nonneg _)))
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrs 3) (Nat.cast_nonneg _))

theorem productionPolynomial_factor (cap : ℕ → ℕ) (p : ℕ) :
    productionPolynomial cap p =
      normalizedProduction cap (Real.sqrt p)⁻¹ * (Real.sqrt p)⁻¹ := by
  unfold productionPolynomial
  rw [sum_insert (by decide), sum_insert (by decide), sum_singleton]
  unfold normalizedProduction
  ring

theorem productionPolynomial_nonneg (cap : ℕ → ℕ) (p : ℕ) :
    0 ≤ productionPolynomial cap p := by
  rw [productionPolynomial_factor]
  exact mul_nonneg (normalizedProduction_nonneg cap
    (inv_nonneg.mpr (Real.sqrt_nonneg _))) (inv_nonneg.mpr (Real.sqrt_nonneg _))

theorem productionPolynomial_endpoint (cap : ℕ → ℕ) {p q : ℕ}
    (hq : 0 < q) (hqp : q ≤ p) {c : ℝ}
    (hc : normalizedProduction cap (Real.sqrt q)⁻¹ ≤ c) :
    productionPolynomial cap p ≤ c * (Real.sqrt p)⁻¹ := by
  rw [productionPolynomial_factor]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  refine (normalizedProduction_mono cap (inv_nonneg.mpr (Real.sqrt_nonneg _)) ?_).trans hc
  exact inv_anti₀ (Real.sqrt_pos.mpr (by exact_mod_cast hq))
    (Real.sqrt_le_sqrt (by exact_mod_cast hqp))

theorem sqrt_two_pow_even (b : ℕ) :
    Real.sqrt (((2 ^ (2 * b) : ℕ) : ℝ)) = (2 : ℝ) ^ b := by
  push_cast
  rw [mul_comm 2 b, pow_mul, Real.sqrt_sq (by positivity)]

theorem LL20_production_decay {p : ℕ} (hp : productionAnchor ≤ p) :
    productionPolynomial coefficientCap20 p ≤ 77 * (Real.sqrt p)⁻¹ := by
  apply productionPolynomial_endpoint coefficientCap20
    (by exact_mod_cast productionAnchor_pos) hp
  rw [sqrt_productionAnchor]
  norm_num [normalizedProduction, coefficientCap20]

theorem LL22_production_decay {p : ℕ} (hp : productionAnchor ≤ p) :
    productionPolynomial coefficientCap22 p ≤ 62 * (Real.sqrt p)⁻¹ := by
  apply productionPolynomial_endpoint coefficientCap22
    (by exact_mod_cast productionAnchor_pos) hp
  rw [sqrt_productionAnchor]
  norm_num [normalizedProduction, coefficientCap22]

theorem LL20_production_decay64 {p : ℕ} (hp : 2 ^ 64 ≤ p) :
    productionPolynomial coefficientCap20 p ≤ 19 * (Real.sqrt p)⁻¹ := by
  apply productionPolynomial_endpoint coefficientCap20 (by norm_num : 0 < 2 ^ 64) hp
  rw [show 64 = 2 * 32 by rfl, sqrt_two_pow_even]
  norm_num [normalizedProduction, coefficientCap20]

theorem LL22_production_decay64 {p : ℕ} (hp : 2 ^ 64 ≤ p) :
    productionPolynomial coefficientCap22 p ≤ 16 * (Real.sqrt p)⁻¹ := by
  apply productionPolynomial_endpoint coefficientCap22 (by norm_num : 0 < 2 ^ 64) hp
  rw [show 64 = 2 * 32 by rfl, sqrt_two_pow_even]
  norm_num [normalizedProduction, coefficientCap22]

theorem LL20_production_decay512 {p : ℕ} (hp : 2 ^ 512 ≤ p) :
    productionPolynomial coefficientCap20 p ≤ 2⁻¹ ^ 200 * (Real.sqrt p)⁻¹ := by
  apply productionPolynomial_endpoint coefficientCap20 (by positivity : 0 < 2 ^ 512) hp
  rw [show 512 = 2 * 256 by rfl, sqrt_two_pow_even]
  norm_num [normalizedProduction, coefficientCap20]

theorem LL22_production_decay512 {p : ℕ} (hp : 2 ^ 512 ≤ p) :
    productionPolynomial coefficientCap22 p ≤ 2⁻¹ ^ 200 * (Real.sqrt p)⁻¹ := by
  apply productionPolynomial_endpoint coefficientCap22 (by positivity : 0 < 2 ^ 512) hp
  rw [show 512 = 2 * 256 by rfl, sqrt_two_pow_even]
  norm_num [normalizedProduction, coefficientCap22]

end Sarkozy.F3Kernel
