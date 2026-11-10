module

public import Sarkozy.PositiveRoots.CoherentMeanData

/-! Kernel-checked Gram certificates for all three coherent invariant-mean matrices. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentMean

open Finset Sarkozy.SpectralD Sarkozy.SpectralC

def entry (k : Kind) (T : List (List ℤ)) (i j : Fin (size k)) : ℤ :=
  (T.getD i.val []).getD j.val 0

def R (k : Kind) := entry k (matrixTable k)
def B (k : Kind) := entry k (factorTable k)

def residual (k : Kind) (i j : Fin (size k)) : ℤ :=
  1000000000000 * R k i j - gramReal (B k) (fun _ _ => 0) i j

theorem model_checks (k : Kind) : ∀ i j, R k i j = modelReal k i j := by
  cases k <;> decide +kernel

theorem residual_symm (k : Kind) : ∀ i j, residual k i j = residual k j i := by
  cases k <;> decide +kernel

theorem residual_rows (k : Kind) : ∀ i,
    (∑ j, |(if i = j then 2000000000 else 0) - residual k i j|) ≤ 2000000000 := by
  cases k <;> decide +kernel

theorem checked_matrix_nonneg (k : Kind) (x : Fin (size k) → ℂ) :
    0 ≤ (qform (fun i j => gaussian (modelReal k i j) 0) x).re := by
  have h := qform_nonneg_of_gaussian_factor (R k) (fun _ _ => 0)
    (B k) (fun _ _ => 0) 1000000000000 2000000000 (by norm_num)
    (residual_symm k) (by intros; simp [gramImag])
    (by intro i; simpa [gramImag, residual] using residual_rows k i) x
  simpa only [model_checks] using h

end Sarkozy.PositiveRoots.CoherentMean
