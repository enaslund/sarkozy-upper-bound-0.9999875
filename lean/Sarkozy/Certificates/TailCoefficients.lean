module

public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The tail coefficients (`def:tail-law`, certificate item (S7))

`paper/sections/27_tail_index.tex`. The tail law at a prime `p ≥ P₄ = 2^512` is normalized by
`P_μ(r) = ∑_{d=0}^7 c_d r^d` with the record weights `c_d` below, and its prices use the *tail
coefficients* `C_j = ∑_{d ≥ j} c_d P₄^{-(d-j)/2}` (`j = 1, 2, 3`), where `P₄^{-1/2} = 2^{-256}`.
`tail_coefficients_bounds` checks, in exact rational arithmetic (kernel `norm_num`, no native
evaluation), the bounds `C₁ < 1197.601`, `C₂ < 609305.05`, `C₃ < 1.4176·10⁸` of item (S7) of
`cert:record:analytic-stage`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Certificates

/-- The record weights `c_0, …, c_7` of the tail law. -/
def tailWeight : Fin 8 → ℚ :=
  ![1, 5988 / 5, 15232626 / 25, 24807984744 / 175, 50638290432 / 5, 621170191872 / 5,
    1877429977088 / 7, 970455252992 / 7]

/-- `P₄^{-1/2} = 2^{-256}`. -/
def tailStep : ℚ := 1 / 2 ^ 256

/-- `C_j = ∑_{d ≥ j} c_d P₄^{-(d-j)/2}`. -/
def tailCoefficient (j : ℕ) : ℚ :=
  ∑ d : Fin 8, if j ≤ d.val then tailWeight d * tailStep ^ (d.val - j) else 0

theorem tail_coefficients_bounds :
    tailCoefficient 1 < 1197601 / 1000 ∧ tailCoefficient 2 < 60930505 / 100 ∧
      tailCoefficient 3 < 14176 * 10 ^ 4 := by
  unfold tailCoefficient tailWeight tailStep
  simp only [Fin.sum_univ_eight, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num [Fin.isValue]

end Sarkozy.Certificates
