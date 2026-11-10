module

public import Sarkozy.PositiveRoots.CoherentProductLinearity
public import Sarkozy.Cuts.DiagonalNormValues

/-! Constant-diagonal images, with the equal-support exceptional constant removed. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.L20Cap Sarkozy.SpectralC Sarkozy.SpectralC.TwoLabel Sarkozy.SpectralD
open Sarkozy.Cuts Sarkozy.Recentering
open scoped symmDiff

variable {p : ℕ} [Fact p.Prime]

noncomputable def entangledCoefficient (F : ZMod p × ZMod p → ℝ) : ℝ :=
  diagonalMean F / Real.sqrt ((p : ℝ) - 1)

theorem entangledCoefficient_abs (hp : 2 ≤ p) (F : ZMod p × ZMod p → ℝ) :
    |entangledCoefficient F| =
      nrm ((fieldLaw p).product (fieldLaw p)) (constantDiagonalPart F) := by
  have hc : 2 ≤ Fintype.card (ZMod p) := by simpa only [ZMod.card] using hp
  rw [entangledCoefficient, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  simpa only [ZMod.card, fieldLaw] using (constantDiagonalPart_norm hc F).symm

theorem normalizedStarProduct_constantDiagonal {U : Type*} (hp : 2 ≤ p)
    (S T : Finset U) (F : ZMod p × ZMod p → ℝ) (x : U → ZMod p) :
    normalizedStarProduct S T (constantDiagonalPart F) x =
      entangledCoefficient F * normalizedStarProduct S T (fun z => entangled z.1 z.2) x := by
  have hc : 2 ≤ Fintype.card (ZMod p) := by simpa only [ZMod.card] using hp
  have he : constantDiagonalPart F =
      fun z => entangledCoefficient F * entangled z.1 z.2 := by
    funext z
    simpa only [ZMod.card, entangledCoefficient] using constantDiagonalPart_entangled hc F z
  rw [he, normalizedStarProduct_smul]

variable [Nonempty (CoreT (ZMod p))]

theorem core_constantDiagonal_product_norm (hp : 2 ≤ p)
    (S T : Finset (Fin 4)) (F : ZMod p × ZMod p → ℝ) {bD bS bT : ℝ}
    (hbD : 0 ≤ bD) (hbS : 0 ≤ bS) (hbT : 0 ≤ bT)
    (hD : ∀ c : CoreT (ZMod p), |starMean (S ∆ T) c.val| ≤ bD)
    (hS : ∀ c : CoreT (ZMod p), |starMean S c.val| ≤ bS)
    (hT : ∀ c : CoreT (ZMod p), |starMean T c.val| ≤ bT) :
    nrm coreLaw (fun c : CoreT (ZMod p) => normalizedStarProduct S T (constantDiagonalPart F) c.val) ≤
      ((p : ℝ) / Real.sqrt (p - 1)) *
        (bD + ((S ∩ T).card : ℝ) * (p : ℝ)⁻¹ + bS * bT) *
          nrm ((fieldLaw p).product (fieldLaw p)) (constantDiagonalPart F) := by
  have h := nrm_le_of_abs_le coreLaw (by positivity : 0 ≤
      ((p : ℝ) / Real.sqrt (p - 1)) *
        (bD + ((S ∩ T).card : ℝ) * (p : ℝ)⁻¹ + bS * bT))
    (fun c : CoreT (ZMod p) => normalizedStarProduct_entangled_bound S T c.val
      c.property.1.injOn (hD c) (hS c) (hT c))
  simp_rw [normalizedStarProduct_constantDiagonal hp]
  rw [nrm_smul, entangledCoefficient_abs hp]
  exact (mul_le_mul_of_nonneg_left h (nrm_nonneg _ _)).trans_eq (by ring)

theorem core_constantDiagonal_equal_remainder (hp : 2 ≤ p)
    (S : Finset (Fin 4)) (F : ZMod p × ZMod p → ℝ) {b : ℝ}
    (hS : ∀ c : CoreT (ZMod p), |starMean S c.val| ≤ b) :
    nrm coreLaw (fun c : CoreT (ZMod p) =>
      normalizedStarProduct S S (constantDiagonalPart F) c.val -
        entangledCoefficient F * ((p : ℝ) / Real.sqrt (p - 1))) ≤
      ((p : ℝ) / Real.sqrt (p - 1)) * ((S.card : ℝ) * (p : ℝ)⁻¹ + b ^ 2) *
        nrm ((fieldLaw p).product (fieldLaw p)) (constantDiagonalPart F) := by
  have h := nrm_le_of_abs_le coreLaw (by positivity : 0 ≤
      ((p : ℝ) / Real.sqrt (p - 1)) * ((S.card : ℝ) * (p : ℝ)⁻¹ + b ^ 2))
    (fun c : CoreT (ZMod p) => normalizedStarProduct_equal_remainder S c.val c.property.1 (hS c))
  simp_rw [normalizedStarProduct_constantDiagonal hp, ← mul_sub]
  rw [nrm_smul, entangledCoefficient_abs hp]
  exact (mul_le_mul_of_nonneg_left h (nrm_nonneg _ _)).trans_eq (by ring)

end Sarkozy.PositiveRoots.CoherentFrame
