module

public import Sarkozy.PositiveRoots.CoherentDiagonalMaps
public import Sarkozy.SpectralD.StarMatrixNorm

/-! Sharp raw-star norms for mean-zero auxiliary inputs under an affine-invariant injective law. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.SpectralC Sarkozy.SpectralC.TwoLabel Sarkozy.SpectralD
open Sarkozy.SpectralD.StarMatrix
open scoped ComplexConjugate

variable {p : ℕ} [Fact p.Prime]

theorem field_meanC_real (F : ZMod p → ℝ) :
    meanC (fun z => (F z : ℂ)) = ((fieldLaw p).expect F : ℂ) := by
  unfold meanC fieldLaw
  rw [FiniteLaw.expect_uniform, ZMod.card]
  push_cast
  ring

theorem field_l2sq_real (F : ZMod p → ℝ) :
    l2sq (fun z => (F z : ℂ)) = (fieldLaw p).expect (fun z => F z ^ 2) := by
  simp only [l2sq, Complex.norm_real, Real.norm_eq_abs, sq_abs, fieldLaw,
    FiniteLaw.expect_uniform, ZMod.card, div_eq_mul_inv]
  ring

theorem rawStarMap_ofReal {U : Type*} (S : Finset U) (F : ZMod p → ℝ) (x : U → ZMod p) :
    kerMap (starKer S) (fun z => (F z : ℂ)) x = (rawStarMap S F x : ℂ) := by
  unfold kerMap starKer rawStarMap fieldLaw StarMatrix.psi
  rw [FiniteLaw.expect_uniform, ZMod.card]
  push_cast
  simp only [mul_assoc, ← mul_sum]
  ring

theorem rawStarMap_mean_zero_sq {U : Type*} [Fintype U] [DecidableEq U]
    (hp3 : p % 4 = 3) (ν : FiniteLaw (U → ZMod p))
    (hinv : ∀ s c x, s ≠ 0 → IsSquare s → ν.weight (affLab s c x) = ν.weight x)
    (hinj : ∀ x k l, ν.weight x ≠ 0 → k ≠ l → x k ≠ x l)
    (S : Finset U) (hS : S.Nonempty) (F : ZMod p → ℝ) (hF : (fieldLaw p).expect F = 0) :
    ν.expect (fun x => rawStarMap S F x ^ 2) ≤
      (p : ℝ)⁻¹ * (fieldLaw p).expect (fun z => F z ^ 2) := by
  obtain ⟨hT, hα⟩ := star_diagonal (by omega) hp3 ν.weight ν.nonneg ν.total hinv hinj S
  let α : ℝ := (p : ℝ)⁻¹ * (1 - (S.card : ℝ) * (p : ℝ)⁻¹ -
    ∑ x, ν.weight x * starMean S x ^ 2) / (1 - (p : ℝ)⁻¹)
  have hm : meanC (fun z => (F z : ℂ)) = 0 := by rw [field_meanC_real, hF, Complex.ofReal_zero]
  have hG : gramOp ν.weight (starKer S) (starKer S) (fun z => (F z : ℂ)) =
      fun z => (α : ℂ) * (F z : ℂ) := funext (hT _ hm)
  have hn := norm_kerMap_sq ν.weight (starKer S) (fun z => (F z : ℂ))
  rw [hG, ip_smul_right', ← l2sq_eq_re_ip] at hn
  simp only [rawStarMap_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    field_l2sq_real] at hn
  have he : ν.expect (fun x => rawStarMap S F x ^ 2) =
      α * (fieldLaw p).expect (fun z => F z ^ 2) := by exact_mod_cast hn
  rw [he]
  exact mul_le_mul_of_nonneg_right (hα hS) ((fieldLaw p).second_moment_nonneg F)

end Sarkozy.PositiveRoots.CoherentFrame
