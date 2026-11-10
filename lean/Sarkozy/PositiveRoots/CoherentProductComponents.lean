module

public import Sarkozy.PositiveRoots.CoherentVariableDiagonal
public import Sarkozy.PositiveRoots.CoherentConstantDiagonal
public import Sarkozy.PositiveRoots.CoherentProductScalars

/-! The three component estimates in the coherent product-map argument. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.L20Cap Sarkozy.SpectralC Sarkozy.SpectralC.TwoLabel Sarkozy.SpectralD
open Sarkozy.Cuts Sarkozy.Recentering

variable {p : ℕ} [Fact p.Prime] [Nonempty (CoreT (ZMod p))]

theorem core_offDiagonal_product_norm (hDLK : Target.FourCycle)
    (hp3 : p % 4 = 3) (hp7 : 7 < p) (S T : Finset (Fin 4))
    (hS : S.Nonempty) (hT : T.Nonempty) (hST : 2 ≤ (S ∪ T).card)
    (F : ZMod p × ZMod p → ℝ) :
    nrm coreLaw (fun c : CoreT (ZMod p) => normalizedStarProduct S T (offDiagonalPart F) c.val) ≤
      (productFactor S T * Real.sqrt (coreCubeDensity p)) *
        nrm ((fieldLaw p).product (fieldLaw p)) (offDiagonalPart F) := by
  have hc : 3 ≤ Fintype.card (ZMod p) := by rw [ZMod.card]; omega
  have h := normalizedStarProduct_offdiag_sq hDLK (by omega : p ≠ 2) coreLaw
    (fun c : CoreT (ZMod p) => c.val) (fun c => c.property.1)
    (coreCubeDensity_pos hp7).le (coreLaw_cube_comparison hp3 hp7)
    S T hS hT hST (offDiagonalPart F) (offDiagonalPart_diagonal hc F)
  apply nrm_le_of_sq_le coreLaw ((fieldLaw p).product (fieldLaw p))
    (mul_nonneg (productFactor_nonneg S T) (Real.sqrt_nonneg _))
  simpa only [nrm_sq_expect, mul_pow, Real.sq_sqrt (coreCubeDensity_pos hp7).le,
    productFactor_sq] using h

theorem core_variableDiagonal_paper_norm (hp3 : p % 4 = 3) (hp : 3 ≤ p)
    (S T : Finset (Fin 4)) (F : ZMod p × ZMod p → ℝ)
    {bS bT : ℝ} (hbS : 0 ≤ bS) (hbT : 0 ≤ bT)
    (hS : ∀ c : CoreT (ZMod p), |starMean S c.val| ≤ bS)
    (hT : ∀ c : CoreT (ZMod p), |starMean T c.val| ≤ bT) :
    nrm coreLaw (fun c : CoreT (ZMod p) => normalizedStarProduct S T (variableDiagonalPart F) c.val) ≤
      ((1 + ((S ∩ T).card : ℝ) * rp p + bS + bT) /
        Real.sqrt (1 - 2 * (p : ℝ)⁻¹)) *
          nrm ((fieldLaw p).product (fieldLaw p)) (variableDiagonalPart F) := by
  have h := core_variableDiagonal_product_norm hp3 hp S T F hbS hbT hS hT
  rw [variable_diagonal_price_eq hp] at h
  convert h using 1
  ring

omit [Nonempty (CoreT (ZMod p))] in
theorem normalizedStarProduct_components (S T : Finset (Fin 4))
    (F : ZMod p × ZMod p → ℝ) (x : Fin 4 → ZMod p) :
    normalizedStarProduct S T F x =
      normalizedStarProduct S T (constantDiagonalPart F) x +
        normalizedStarProduct S T (variableDiagonalPart F) x +
        normalizedStarProduct S T (offDiagonalPart F) x := by
  have he : F = fun z => constantDiagonalPart F z + variableDiagonalPart F z + offDiagonalPart F z :=
    funext (diagonal_parts_sum F)
  calc
    _ = normalizedStarProduct S T
      (fun z => constantDiagonalPart F z + variableDiagonalPart F z + offDiagonalPart F z) x :=
        congrArg (fun G => normalizedStarProduct S T G x) he
    _ = _ := by rw [normalizedStarProduct_add, normalizedStarProduct_add]

end Sarkozy.PositiveRoots.CoherentFrame
