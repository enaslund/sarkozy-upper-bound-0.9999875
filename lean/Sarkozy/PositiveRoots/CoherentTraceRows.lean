module

public import Sarkozy.PositiveRoots.CoherentTraceKeys

/-! Exact row sums and symmetry of the physical score coefficient matrix, checked on the
explicit key list of `CoherentTraceKeys`. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.SpectralC

theorem chamberCoeff_row : ∀ a : Feature, (∑ b, |chamberCoeff a b|) ≤ 1 / 3 :=
  chamberCoeff_row_keys

theorem chamberCoeff_symm : ∀ a b : Feature, chamberCoeff a b = chamberCoeff b a :=
  chamberCoeff_symm_keys

theorem chamberCoeff_norm : NormLe (fun a b => (chamberCoeff a b : ℂ)) (1 / 3) := by
  apply normLe_schur _ (fun a b => |(chamberCoeff a b : ℝ)|)
  · exact fun _ _ => abs_nonneg _
  · intro a b
    rw [chamberCoeff_symm a b]
  · intro a b
    have he : (chamberCoeff a b : ℂ) = ((chamberCoeff a b : ℝ) : ℂ) := by simp
    rw [he, Complex.norm_real, Real.norm_eq_abs]
  · intro a
    have h : ((∑ b, |chamberCoeff a b| : ℚ) : ℝ) ≤ ((1 / 3 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (chamberCoeff_row a)
    simpa only [Rat.cast_sum, Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

end Sarkozy.PositiveRoots.CoherentFrame
