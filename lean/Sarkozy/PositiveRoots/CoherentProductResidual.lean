module

public import Sarkozy.PositiveRoots.CoherentProductComponents
public import Sarkozy.Cuts.ThreeComponentBound

/-! Orthogonal-input combination of the coherent raw-star product estimates. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.L20Cap Sarkozy.SpectralC Sarkozy.SpectralC.TwoLabel Sarkozy.SpectralD
open Sarkozy.Cuts Sarkozy.Recentering
open scoped symmDiff

variable {p : ℕ} [Fact p.Prime]

noncomputable def productExceptional (S T : Finset (Fin 4)) (F : ZMod p × ZMod p → ℝ) : ℝ :=
  if S = T then entangledCoefficient F * ((p : ℝ) / Real.sqrt (p - 1)) else 0

noncomputable def reducedStarProduct (S T : Finset (Fin 4)) (F : ZMod p × ZMod p → ℝ)
    (x : Fin 4 → ZMod p) : ℝ := normalizedStarProduct S T F x - productExceptional S T F

noncomputable def constantProductPrice (p : ℕ) (S T : Finset (Fin 4)) (bS bT bD : ℝ) : ℝ :=
  ((p : ℝ) / Real.sqrt (p - 1)) *
    if S = T then (S.card : ℝ) * (p : ℝ)⁻¹ + bS ^ 2
    else bD + ((S ∩ T).card : ℝ) * (p : ℝ)⁻¹ + bS * bT

noncomputable def variableProductPrice (p : ℕ) (S T : Finset (Fin 4)) (bS bT : ℝ) : ℝ :=
  (1 + ((S ∩ T).card : ℝ) * rp p + bS + bT) / Real.sqrt (1 - 2 * (p : ℝ)⁻¹)

noncomputable def residualProductPrice (p : ℕ) (S T : Finset (Fin 4)) (bS bT bD : ℝ) : ℝ :=
  Real.sqrt (constantProductPrice p S T bS bT bD ^ 2 + variableProductPrice p S T bS bT ^ 2 +
    (productFactor S T * Real.sqrt (coreCubeDensity p)) ^ 2)

omit [Fact p.Prime] in
theorem constantProductPrice_nonneg (S T : Finset (Fin 4)) {bS bT bD : ℝ}
    (hbS : 0 ≤ bS) (hbT : 0 ≤ bT) (hbD : 0 ≤ bD) :
    0 ≤ constantProductPrice p S T bS bT bD := by
  unfold constantProductPrice
  split_ifs <;> positivity

omit [Fact p.Prime] in
theorem variableProductPrice_nonneg (S T : Finset (Fin 4)) {bS bT : ℝ}
    (hbS : 0 ≤ bS) (hbT : 0 ≤ bT) : 0 ≤ variableProductPrice p S T bS bT := by
  unfold variableProductPrice
  have hr := rp_nonneg (p := p)
  positivity

variable [Nonempty (CoreT (ZMod p))]

theorem core_reducedStarProduct_norm (hDLK : Target.FourCycle)
    (hp3 : p % 4 = 3) (hp7 : 7 < p) (S T : Finset (Fin 4))
    (hSne : S.Nonempty) (hTne : T.Nonempty) (hST : 2 ≤ (S ∪ T).card)
    {bS bT bD : ℝ} (hbS : 0 ≤ bS) (hbT : 0 ≤ bT) (hbD : 0 ≤ bD)
    (hS : ∀ c : CoreT (ZMod p), |starMean S c.val| ≤ bS)
    (hT : ∀ c : CoreT (ZMod p), |starMean T c.val| ≤ bT)
    (hD : S ≠ T → ∀ c : CoreT (ZMod p), |starMean (S ∆ T) c.val| ≤ bD)
    (F : ZMod p × ZMod p → ℝ)
    (hrow : ∀ u, (fieldLaw p).expect (fun v => F (u, v)) = 0)
    (hcol : ∀ v, (fieldLaw p).expect (fun u => F (u, v)) = 0) :
    nrm coreLaw (fun c : CoreT (ZMod p) => reducedStarProduct S T F c.val) ≤
      residualProductPrice p S T bS bT bD * nrm ((fieldLaw p).product (fieldLaw p)) F := by
  have hc : 3 ≤ Fintype.card (ZMod p) := by rw [ZMod.card]; omega
  have hconst : nrm coreLaw (fun c : CoreT (ZMod p) =>
      normalizedStarProduct S T (constantDiagonalPart F) c.val - productExceptional S T F) ≤
        constantProductPrice p S T bS bT bD *
          nrm ((fieldLaw p).product (fieldLaw p)) (constantDiagonalPart F) := by
    by_cases he : S = T
    · subst T
      simpa only [productExceptional, constantProductPrice, ite_true] using
        core_constantDiagonal_equal_remainder (by omega : 2 ≤ p) S F hS
    · simpa only [productExceptional, constantProductPrice, ite_eq_right he, sub_zero] using
        core_constantDiagonal_product_norm (by omega : 2 ≤ p) S T F hbD hbS hbT (hD he) hS hT
  have hvar := core_variableDiagonal_paper_norm hp3 (by omega : 3 ≤ p) S T F hbS hbT hS hT
  have hoff := core_offDiagonal_product_norm hDLK hp3 hp7 S T hSne hTne hST F
  have h := three_component_bound coreLaw ((fieldLaw p).product (fieldLaw p))
    (fun c : CoreT (ZMod p) =>
      normalizedStarProduct S T (constantDiagonalPart F) c.val - productExceptional S T F)
    (fun c : CoreT (ZMod p) => normalizedStarProduct S T (variableDiagonalPart F) c.val)
    (fun c : CoreT (ZMod p) => normalizedStarProduct S T (offDiagonalPart F) c.val)
    F (constantDiagonalPart F) (variableDiagonalPart F) (offDiagonalPart F)
    (constantProductPrice_nonneg S T hbS hbT hbD) (variableProductPrice_nonneg S T hbS hbT)
    (mul_nonneg (productFactor_nonneg S T) (Real.sqrt_nonneg _)) hconst hvar hoff
    (diagonal_parts_energy hc F hrow hcol)
  have he : (fun c : CoreT (ZMod p) => reducedStarProduct S T F c.val) =
      fun c => (normalizedStarProduct S T (constantDiagonalPart F) c.val - productExceptional S T F) +
        normalizedStarProduct S T (variableDiagonalPart F) c.val +
        normalizedStarProduct S T (offDiagonalPart F) c.val := by
    funext c
    unfold reducedStarProduct
    rw [normalizedStarProduct_components]
    ring
  rw [he]
  exact h

end Sarkozy.PositiveRoots.CoherentFrame
