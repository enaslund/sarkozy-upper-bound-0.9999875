module

public import Sarkozy.SpectralD.TailGramRows
public import Sarkozy.SpectralD.TailQuotients

/-!
# Coupling deviation and conditional-variance bounds in the tail

The complete count ratios give Gamma_E ≤ 10^(-8), and the internal
degree bound gives theta ≤ 64, for the root spectral criterion.
-/

@[expose] public section

namespace Sarkozy.SpectralD

open Finset Sarkozy.SpectralC

theorem tail_inv_prime {p : ℕ} (hp : 2 ^ 512 ≤ p) :
    (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ ^ 128 := by
  have hp' : (2 : ℝ) ^ 128 ≤ p := by exact_mod_cast (show 2 ^ 128 ≤ p by omega)
  simpa only [inv_pow] using inv_anti₀ (by positivity : (0 : ℝ) < 2 ^ 128) hp'

theorem tail_coupling_entry {p t : ℕ} (hp : 2 ^ 512 ≤ p) (ht : t ≤ 12)
    {e R : ℝ} (he0 : 0 ≤ e) (he : e ≤ 2⁻¹ ^ 50)
    (hR1 : 1 ≤ R) (hR : R ≤ 1 + 2⁻¹ ^ 40) :
    (2 : ℝ) ^ t * (1 + e) * devConst R e ^ 2 + 36 * 4 ^ t / p ≤ 2⁻¹ ^ 40 := by
  have hdev := tail_devConst he0 he hR1 hR
  have h1 : (2 : ℝ) ^ t * (1 + e) * devConst R e ^ 2 ≤
      2 ^ 12 * (1 + (2 : ℝ)⁻¹ ^ 50) * ((2 : ℝ)⁻¹ ^ 38) ^ 2 :=
    mul_le_mul (mul_le_mul (pow_le_pow_right₀ (by norm_num) ht)
      (by linarith) (by linarith) (by positivity))
      (pow_le_pow_left₀ hdev.1 hdev.2 2) (sq_nonneg _) (by positivity)
  have h2 : 36 * (4 : ℝ) ^ t / p ≤ 36 * 4 ^ 12 * (2 : ℝ)⁻¹ ^ 128 := by
    rw [div_eq_mul_inv]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) ht)
      (by norm_num)) (tail_inv_prime hp) (by positivity) (by positivity)
  exact (add_le_add h1 h2).trans (by norm_num)

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

omit [DecidableEq U] in
theorem coupling_error_tail (N : U → Finset U) (R : U → ℝ) (hp : 2 ^ 512 ≤ p)
    (hn : Fintype.card U = 36) (hr : ∀ k, (N k).card ≤ 12)
    (hR1 : ∀ k, 1 ≤ R k) (hR : ∀ k, R k ≤ 1 + 2⁻¹ ^ 40) :
    ∑ k, ((2 : ℝ) ^ (N k).card *
        (1 + TraceMixing.coarseErr p (N k).card (Fintype.card U)) *
        devConst (R k) (TraceMixing.coarseErr p (N k).card (Fintype.card U)) ^ 2 +
      (Fintype.card U : ℝ) * 4 ^ (N k).card / p) ≤ 1 / 100000000 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  calc _ ≤ ∑ _k : U, (2 : ℝ)⁻¹ ^ 40 := sum_le_sum fun k _ => by
        rw [hn]
        exact tail_coupling_entry hp (hr k) (TraceMixing.coarseErr_nonneg hp0 _ _)
          (coarseErr_tail hp ((hr k).trans (by norm_num)) (by norm_num)) (hR1 k) (hR k)
    _ = 36 * (2 : ℝ)⁻¹ ^ 40 := by
        simp only [sum_const, card_univ, hn, nsmul_eq_mul, Nat.cast_ofNat]
    _ ≤ 1 / 100000000 := by norm_num

theorem tail_theta_scalar {R e : ℝ} {d : ℕ} (hR0 : 0 ≤ R) (hR : R ≤ 1 + 2⁻¹ ^ 40)
    (he : e ≤ 2⁻¹ ^ 50) (hd : d ≤ 10) : R ^ 2 * (2 ^ d / (1 - e)) - 1 ≤ 64 ^ 2 := by
  have he1 : 0 < 1 - e := by norm_num at he ⊢; linarith
  have hdiv : (2 : ℝ) ^ d / (1 - e) ≤ 2 ^ 10 / (1 - (2 : ℝ)⁻¹ ^ 50) :=
    div_le_div₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hd)
      (by norm_num) (by linarith)
  have hmul := mul_le_mul (pow_le_pow_left₀ hR0 hR 2) hdiv
    (div_nonneg (by positivity) he1.le) (by positivity)
  exact (sub_le_sub_right hmul 1).trans (by norm_num)

end Sarkozy.SpectralD
