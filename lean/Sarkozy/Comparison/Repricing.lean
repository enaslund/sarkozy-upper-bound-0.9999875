module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Repricing between exponents

`lem:record:repricing` (`paper/sections/09_comparison_theorem.tex`). A price is an unpriced
part (a mass, a weight or a norm, independent of the exponent) times the selection factor
`q_𝔅^(2a)`. For atoms of logarithmic size at most `L`, raising the exponent from `a'` to
`a'' ≥ a'` multiplies every price by at most `e^(2(a''-a')L)`; sums of nonnegative
unpriced parts are repriced the same way, and two steps with a common budget compose.
The closing of Part V certifies the middle charges at an anchor `a₀` and reprices them
by `t = e^(2(a - a₀)·570)`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Comparison

/-- One atom: `q^(2a'') ≤ e^(2(a''-a')L) q^(2a')` when `1 ≤ q`, `log q ≤ L`, `a' ≤ a''`. -/
theorem selection_factor_reprice {q a₁ a₂ L : ℝ} (hq : 1 ≤ q) (hlog : Real.log q ≤ L)
    (ha : a₁ ≤ a₂) :
    q ^ (2 * a₂) ≤ Real.exp (2 * (a₂ - a₁) * L) * q ^ (2 * a₁) := by
  have hq0 : 0 < q := by linarith
  rw [Real.rpow_def_of_pos hq0, Real.rpow_def_of_pos hq0, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : Real.log q * (2 * a₂) = Real.log q * (2 * a₁) + 2 * (a₂ - a₁) * Real.log q := by
    ring
  rw [h1]
  have h2 : 2 * (a₂ - a₁) * Real.log q ≤ 2 * (a₂ - a₁) * L :=
    mul_le_mul_of_nonneg_left hlog (by linarith)
  linarith

/-- **Repricing of a total.** -/
theorem total_reprice {ι : Type*} (s : Finset ι) (c q : ι → ℝ) {a₁ a₂ L : ℝ}
    (hc : ∀ i ∈ s, 0 ≤ c i) (hq : ∀ i ∈ s, 1 ≤ q i) (hlog : ∀ i ∈ s, Real.log (q i) ≤ L)
    (ha : a₁ ≤ a₂) :
    ∑ i ∈ s, c i * q i ^ (2 * a₂) ≤
      Real.exp (2 * (a₂ - a₁) * L) * ∑ i ∈ s, c i * q i ^ (2 * a₁) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  calc c i * q i ^ (2 * a₂) ≤ c i * (Real.exp (2 * (a₂ - a₁) * L) * q i ^ (2 * a₁)) :=
        mul_le_mul_of_nonneg_left (selection_factor_reprice (hq i hi) (hlog i hi) ha) (hc i hi)
    _ = Real.exp (2 * (a₂ - a₁) * L) * (c i * q i ^ (2 * a₁)) := by ring

/-- Two repricing steps with a common budget compose to one. -/
theorem reprice_compose {a₀ a₁ a₂ L : ℝ} :
    Real.exp (2 * (a₁ - a₀) * L) * Real.exp (2 * (a₂ - a₁) * L) =
      Real.exp (2 * (a₂ - a₀) * L) := by
  rw [← Real.exp_add]
  congr 1
  ring

end Sarkozy.Comparison
