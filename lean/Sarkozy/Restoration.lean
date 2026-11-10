module

public import Sarkozy.Parameters
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The scalar density-sensitive restoration bound

The quadratic inversion in `lem:density:restoration` (Section 31).
This proves the exact scalar step. Deriving its moment and domination
hypotheses for the actual probability laws, and absorbing the o(1) errors,
remain separate obligations.
-/

namespace Sarkozy

/-- Solve the centered chi-square inequality for a lower bound on the mean. -/
theorem restoration_quadratic_bound {m C χ ℓ : ℝ}
    (hm : 0 ≤ m) (hχ : 0 ≤ χ) (hvariance : 0 ≤ C ^ 2 - m ^ 2)
    (hcomparison : ℓ ≤ m + Real.sqrt χ * Real.sqrt (C ^ 2 - m ^ 2)) :
    (ℓ - Real.sqrt (χ * ((1 + χ) * C ^ 2 - ℓ ^ 2))) / (1 + χ) ≤ m := by
  have hden : 0 < 1 + χ := by linarith
  apply (div_le_iff₀ hden).2
  by_cases heasy : ℓ ≤ m
  · have hs := Real.sqrt_nonneg (χ * ((1 + χ) * C ^ 2 - ℓ ^ 2))
    have hmχ := mul_nonneg hm hχ
    nlinarith
  have hgap : 0 ≤ ℓ - m := by linarith
  have hsqrt : 0 ≤ Real.sqrt χ * Real.sqrt (C ^ 2 - m ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsquare : (ℓ - m) ^ 2 ≤
      (Real.sqrt χ * Real.sqrt (C ^ 2 - m ^ 2)) ^ 2 := by
    nlinarith
  rw [mul_pow, Real.sq_sqrt hχ, Real.sq_sqrt hvariance] at hsquare
  have hproduct := mul_nonneg hden.le (sub_nonneg.mpr hsquare)
  have hidentity : χ * ((1 + χ) * C ^ 2 - ℓ ^ 2) - (ℓ - (1 + χ) * m) ^ 2 =
      (1 + χ) * (χ * (C ^ 2 - m ^ 2) - (ℓ - m) ^ 2) := by ring
  have hdisc : (ℓ - (1 + χ) * m) ^ 2 ≤ χ * ((1 + χ) * C ^ 2 - ℓ ^ 2) := by
    linarith only [hidentity, hproduct]
  have hroot := Real.le_sqrt_of_sq_le hdisc
  nlinarith only [hroot]

/-- The three branches in the paper's F₂ restoration function. -/
noncomputable def restoration (C h M χ : ℝ) : ℝ :=
  let ℓ := max 0 (1 - (C - 1) * h)
  max 0 (max (ℓ / M)
    ((ℓ - Real.sqrt (χ * ((1 + χ) * C ^ 2 - ℓ ^ 2))) / (1 + χ)))

theorem restoration_nonneg (C h M χ : ℝ) : 0 ≤ restoration C h M χ :=
  le_max_left _ _

/-- Positivity, density domination, and centered comparison imply all three branches. -/
theorem restoration_le_mean {m C h M χ : ℝ}
    (hm : 0 ≤ m) (hM : 0 < M) (hχ : 0 ≤ χ)
    (hvariance : 0 ≤ C ^ 2 - m ^ 2)
    (hdomination : max 0 (1 - (C - 1) * h) ≤ m * M)
    (hcomparison : max 0 (1 - (C - 1) * h) ≤
      m + Real.sqrt χ * Real.sqrt (C ^ 2 - m ^ 2)) :
    restoration C h M χ ≤ m := by
  exact max_le hm (max_le ((div_le_iff₀ hM).2 hdomination)
    (restoration_quadratic_bound hm hχ hvariance hcomparison))

end Sarkozy
