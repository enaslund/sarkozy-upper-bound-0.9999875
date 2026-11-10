module

public import Sarkozy.SpectralD.StarBounds
public import Sarkozy.F3Kernel.ProductionDecay

/-!
# Normalizing and perpendicular error budgets in the tail range

At p ≥ 2^512, the uniform star estimates and the nonstar and collision
coefficients fit the allowances epsilon_Z = 1/100 and c_perp = 1/4.
These scalar inequalities retain their dependence on p.
-/

@[expose] public section

namespace Sarkozy.SpectralD

theorem tail_rp_le {p : ℕ} (hp : 2 ^ 512 ≤ p) :
    (Real.sqrt p)⁻¹ ≤ (2 : ℝ)⁻¹ ^ 256 := by
  have hs : (2 : ℝ) ^ 256 ≤ Real.sqrt p := by
    have h := Real.sqrt_le_sqrt (show (2 : ℝ) ^ 512 ≤ p by exact_mod_cast hp)
    rwa [show 512 = 256 * 2 by rfl, pow_mul, Real.sqrt_sq (by positivity)] at h
  simpa only [inv_pow] using inv_anti₀ (by positivity : (0 : ℝ) < 2 ^ 256) hs

theorem tail_normalizer_scalar {r z n d : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 2⁻¹ ^ 256)
    (hz : z ≤ 2 ^ 88 * r ^ 2) (hn : n ≤ 2⁻¹ ^ 200 * r)
    (hd : d ≤ 2⁻¹ ^ 200 * r) : 2 * z + n + d ≤ 1 / 100 := by
  have hr1 : r ≤ 1 := hr.trans (by norm_num)
  have hz' : z ≤ 2 ^ 88 * r := hz.trans
    (mul_le_mul_of_nonneg_left (by nlinarith : r ^ 2 ≤ r) (by positivity))
  calc 2 * z + n + d ≤ 2 * (2 ^ 88 * r) + 2⁻¹ ^ 200 * r + 2⁻¹ ^ 200 * r := by
        gcongr
    _ = (2 ^ 89 + 2⁻¹ ^ 199) * r := by ring
    _ ≤ (2 ^ 89 + 2⁻¹ ^ 199) * (2⁻¹ ^ 256) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
    _ ≤ 1 / 100 := by norm_num

theorem tail_perpendicular_scalar {r m n d : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ 2⁻¹ ^ 256) (hm0 : 0 ≤ m) (hn0 : 0 ≤ n) (hd0 : 0 ≤ d)
    (hm : m ≤ 2 ^ 84 * r) (hn : n ≤ 2⁻¹ ^ 200 * r) (hd : d ≤ 2⁻¹ ^ 200 * r) :
    (n + d) / (1 - 1 / 100) + ((m + n + d) / (1 - 1 / 100)) ^ 2 ≤ 1 / 4 * r := by
  have hnd : n + d ≤ 2⁻¹ ^ 199 * r := by
    calc _ ≤ 2⁻¹ ^ 200 * r + 2⁻¹ ^ 200 * r := add_le_add hn hd
      _ = _ := by ring
  have hn' : (n + d) / (1 - 1 / 100) ≤ 2⁻¹ ^ 198 * r := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 - 1 / 100)).mpr
    calc n + d ≤ 2⁻¹ ^ 199 * r := hnd
      _ ≤ (2⁻¹ ^ 198 * (1 - 1 / 100)) * r :=
          mul_le_mul_of_nonneg_right (by norm_num) hr0
      _ = _ := by ring
  have hm' : (m + n + d) / (1 - 1 / 100) ≤ 2 ^ 86 * r := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 - 1 / 100)).mpr
    calc m + n + d = m + (n + d) := by ring
      _ ≤ 2 ^ 84 * r + 2⁻¹ ^ 199 * r := add_le_add hm hnd
      _ = (2 ^ 84 + 2⁻¹ ^ 199) * r := by ring
      _ ≤ (2 ^ 86 * (1 - 1 / 100)) * r :=
          mul_le_mul_of_nonneg_right (by norm_num) hr0
      _ = _ := by ring
  have hs := pow_le_pow_left₀ (div_nonneg (by linarith : 0 ≤ m + n + d)
    (by norm_num : (0 : ℝ) ≤ 1 - 1 / 100)) hm' 2
  calc _ ≤ 2⁻¹ ^ 198 * r + (2 ^ 86 * r) ^ 2 := add_le_add hn' hs
    _ = (2⁻¹ ^ 198 + 2 ^ 172 * r) * r := by ring
    _ ≤ (2⁻¹ ^ 198 + 2 ^ 172 * (2⁻¹ ^ 256)) * r := by gcongr
    _ ≤ 1 / 4 * r := mul_le_mul_of_nonneg_right (by norm_num) hr0

end Sarkozy.SpectralD
