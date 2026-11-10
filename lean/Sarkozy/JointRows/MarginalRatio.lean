module

public import Sarkozy.JointRows.RowsA

/-! A ratio bound on raw marginals yields a pointwise lower bound after normalization. -/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows

open Finset Sarkozy.FiveType

variable {X : Type*} [Fintype X]

theorem expect_le_of_charged (μ : FiniteLaw X) (f : X → ℝ) (C : ℝ)
    (h : ∀ x, μ.weight x ≠ 0 → f x ≤ C) : μ.expect f ≤ C := by
  rw [← μ.expect_const C]
  apply sum_le_sum
  intro x _
  by_cases hx : μ.weight x = 0
  · simp [hx]
  · exact mul_le_mul_of_nonneg_left (h x hx) (μ.nonneg x)

theorem dens1_lower_of_ratio (μ : FiniteLaw X) (K : X → X → ℝ) {R : ℝ}
    (hR : 0 < R) (hZ : 0 < RowsA.mass μ K) (x : X)
    (h : ∀ x', μ.weight x' ≠ 0 → kone μ K x' ≤ R * kone μ K x) :
    R⁻¹ ≤ RowsA.dens1 μ K x := by
  have hm : RowsA.mass μ K ≤ R * kone μ K x := by
    rw [RowsA.mass, kf_one_one]
    exact expect_le_of_charged μ _ _ h
  rw [RowsA.dens1, le_div_iff₀ hZ, inv_mul_eq_div, div_le_iff₀ hR]
  simpa only [mul_comm] using hm

theorem dens2_lower_of_ratio (μ : FiniteLaw X) (K : X → X → ℝ) {R : ℝ}
    (hR : 0 < R) (hZ : 0 < RowsA.mass μ K) (y : X)
    (h : ∀ y', μ.weight y' ≠ 0 → kone' μ K y' ≤ R * kone' μ K y) :
    R⁻¹ ≤ RowsA.dens2 μ K y := by
  have hm : RowsA.mass μ K ≤ R * kone' μ K y := by
    rw [RowsA.mass, kf_one_one']
    exact expect_le_of_charged μ _ _ h
  rw [RowsA.dens2, le_div_iff₀ hZ, inv_mul_eq_div, div_le_iff₀ hR]
  simpa only [mul_comm] using hm

end Sarkozy.JointRows
