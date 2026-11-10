module

public import Sarkozy.PositiveRoots.CoherentMatrixModel

/-! Algebra relating the scaled integer matrix to the selected coherent chamber model. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentMatrix

open Finset Sarkozy.SpectralD Sarkozy.SpectralC
open scoped ComplexConjugate

theorem selected_strength :
    1 + (1 : ℚ) / 100 + (13 / 75) * (67 / 40) ^ 2 = 179557 / 120000 ∧
      2 * (67 / 40) / (1 + (1 : ℚ) / 100 + (13 / 75) * (67 / 40) ^ 2) = strength := by
  norm_num [strength]

theorem model_eq_shift (i j : Fin 64) :
    gaussian (modelReal i j) (modelImag i j) =
      (denominator : ℂ) * ((if i = j then (cap : ℂ) else 0) + leading i j) := by
  rw [leading, coefficient_eq]
  unfold modelReal modelImag gaussian denominator cap strength
  push_cast
  split_ifs <;> apply Complex.ext <;> simp <;> ring

theorem qform_scalar {U : Type*} [Fintype U] (A : U → U → ℂ) (s : ℂ) (x : U → ℂ) :
    qform (fun i j => s * A i j) x = s * qform A x := by
  unfold qform
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

theorem qform_neg {U : Type*} [Fintype U] (A : U → U → ℂ) (x : U → ℂ) :
    qform (fun i j => -A i j) x = -qform A x := by
  have h := qform_scalar A (-1) x
  simpa only [neg_one_mul] using h

end Sarkozy.PositiveRoots.CoherentMatrix
