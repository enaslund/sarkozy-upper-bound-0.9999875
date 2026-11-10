module

public import Sarkozy.PositiveRoots.CoherentMatrixChecks
public import Sarkozy.PositiveRoots.CoherentMatrixAlgebra

/-!
# The selected coherent chamber cap `5.41674864`

The matrix includes the physical dictionary at parameter `67/40` and floor
`1/100`. The analytic comparison of this leading matrix with the finite-prime
operator remains separate.
-/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentMatrix

open Finset Sarkozy.SpectralD Sarkozy.SpectralC
open scoped ComplexConjugate

/-- The rational leading-matrix gate at the paper's selected coherent parameter. -/
theorem selected_chamber_bound (x : Fin 64 → ℂ) :
    -((541674864 : ℝ) / 100000000) * ∑ i, ‖x i‖ ^ 2 ≤ (qform leading x).re := by
  have h := checked_matrix_nonneg x
  simp_rw [model_eq_shift] at h
  rw [qform_scalar] at h
  have hs : (0 : ℝ) < (denominator : ℤ) := by norm_num [denominator]
  have hd : (denominator : ℂ) = ((denominator : ℝ) : ℂ) := by simp
  rw [hd, Complex.re_ofReal_mul] at h
  have hb := (mul_nonneg_iff_of_pos_left hs).mp h
  have he := qform_shift (fun i j => -leading i j) (cap : ℝ) x
  have hc : ((cap : ℝ) : ℂ) = (cap : ℂ) := by norm_num [cap]
  simp only [sub_neg_eq_add, qform_neg, Complex.neg_re, hc] at he
  rw [he] at hb
  norm_num [cap] at hb ⊢
  linarith

end Sarkozy.PositiveRoots.CoherentMatrix
