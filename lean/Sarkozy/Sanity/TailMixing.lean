module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real



@[expose] public section

namespace Sarkozy.Sanity

/-- `2^92/p ≤ p^{-255/512}` for `p ≥ 2^512`. -/
theorem two_pow_92_div_le (p : ℝ) (hp : (2 : ℝ) ^ 512 ≤ p) :
    (2 : ℝ) ^ 92 / p ≤ p ^ (-(255 / 512 : ℝ)) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have h1 : p ^ (-(255 / 512 : ℝ)) = p ^ (257 / 512 : ℝ) / p := by
    rw [eq_div_iff hp0.ne', ← Real.rpow_add_one hp0.ne']
    norm_num
  rw [h1]
  apply div_le_div_of_nonneg_right _ hp0.le
  calc (2 : ℝ) ^ 92 ≤ (2 : ℝ) ^ 257 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    _ = ((2 : ℝ) ^ 512) ^ (257 / 512 : ℝ) := by
        rw [show ((2 : ℝ) ^ 512) = (2 : ℝ) ^ ((512 : ℕ) : ℝ) from (Real.rpow_natCast 2 512).symm,
          ← Real.rpow_mul (by norm_num),
          show ((512 : ℕ) : ℝ) * (257 / 512) = ((257 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    _ ≤ p ^ (257 / 512 : ℝ) := Real.rpow_le_rpow (by positivity) hp (by norm_num)

/-- The side conditions of `tail_R4` hold together at every `p ≥ 2^512`. -/
theorem tail_R4_side_conditions (p : ℝ) (hp : (2 : ℝ) ^ 512 ≤ p) :
    ∃ ϖ h S : ℝ, 0 ≤ ϖ ∧ ϖ ≤ 1 ∧ 1 - ϖ ≤ h ∧ (2 : ℝ) ^ 92 / p + h ≤ S ∧
      S ≤ p ^ (-(255 / 512 : ℝ)) :=
  ⟨1, 0, 2 ^ 92 / p, zero_le_one, le_rfl, by norm_num, by norm_num, two_pow_92_div_le p hp⟩

end Sarkozy.Sanity
