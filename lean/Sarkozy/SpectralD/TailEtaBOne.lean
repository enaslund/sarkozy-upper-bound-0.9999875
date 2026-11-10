module

public import Sarkozy.SpectralD.TailEtaB

/-!
# A coupling allowance including the class-one Paley term

The larger class-one model row sums fit eta_B = 3/20 once the
non-coverable contribution is bounded by 2^(-38).
-/

@[expose] public section

namespace Sarkozy.SpectralD

open Sarkozy.SpectralC

theorem etaB_tail_with_parity {p : ℕ} (hp : 2 ^ 512 ≤ p)
    {R Lp L ρ D ζ Λnc : ℝ} (hR : R ≤ 1 + 2⁻¹ ^ 40)
    (hLp0 : 0 ≤ Lp) (hLp : Lp ≤ 12384) (hL : L ≤ 8928)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 301768740) (hD0 : 0 ≤ D) (hD : D ≤ 12)
    (hζ0 : 0 ≤ ζ) (hnc0 : 0 ≤ Λnc) (hpar : ζ * Λnc ≤ 2⁻¹ ^ 38) :
    Cx.etaBcx p R Lp (1 / 1000) 64 ρ (1 / 100000000) L ζ Λnc
      (1 / 100000) D (1 / 1000) ≤ 3 / 20 := by
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
  have hpar' : (if p % 4 = 1 then (1 : ℝ) else 0) * ζ * Λnc ≤ 2⁻¹ ^ 38 := by
    split_ifs
    · simpa only [one_mul] using hpar
    · simp only [zero_mul]; positivity
  have hpz : 0 ≤ (if p % 4 = 1 then (1 : ℝ) else 0) * ζ * Λnc := by
    split_ifs <;> positivity
  have hsum : 1 / 1000 + rp p * 64 * ρ +
      (2 * Real.sqrt (1 / 100000000 * (L + 1 / 1000)) + 1 / 100000000) +
      (if p % 4 = 1 then (1 : ℝ) else 0) * ζ * Λnc ≤ 1 / 10 := by
    norm_num only at hrho hpar'
    linarith
  have h1 : (R * p / ((p : ℝ) - 1) - 1) * Lp ≤ (1 / 1000000) * 12384 := by
    calc _ ≤ (1 / 1000000) * Lp := mul_le_mul_of_nonneg_right (by linarith) hLp0
      _ ≤ _ := mul_le_mul_of_nonneg_left hLp (by norm_num)
  have hrp0 : 0 ≤ rp p := by unfold rp; positivity
  have h2 := mul_le_mul hfac hsum (by positivity)
    (by norm_num : (0 : ℝ) ≤ 1 + 1 / 1000000)
  have h3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD0 hD 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 100000)
  have h4 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hD (by norm_num : (0 : ℝ) ≤ 2))
    (by norm_num : (0 : ℝ) ≤ 1 / 1000)
  exact (add_le_add (add_le_add (add_le_add h1 h2) h3) h4).trans (by norm_num)

end Sarkozy.SpectralD
