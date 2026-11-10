module

public import Sarkozy.PositiveRoots.CoherentProductDiagonal
public import Sarkozy.PositiveRoots.CoherentProductLinearity
public import Sarkozy.Cuts.DiagonalNormValues

/-! The mean-zero diagonal component has its exact auxiliary norm price. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.L20Cap Sarkozy.SpectralC Sarkozy.SpectralC.TwoLabel Sarkozy.SpectralD
open Sarkozy.Cuts Sarkozy.Recentering

variable {p : ℕ} [Fact p.Prime] [Nonempty (CoreT (ZMod p))]

omit [Nonempty (CoreT (ZMod p))] in
theorem normalizedStarProduct_variableDiagonal (S T : Finset (Fin 4))
    (F : ZMod p × ZMod p → ℝ) (x : Fin 4 → ZMod p) :
    normalizedStarProduct S T (variableDiagonalPart F) x =
      ((p : ℝ) / (p - 2)) * centeredProductImage S T (diagonalFluctuation F) x := by
  unfold variableDiagonalPart
  rw [normalizedStarProduct_smul, normalizedStarProduct_projectedDiagonal, ZMod.card]
  ring

theorem core_variableDiagonal_product_norm (hp3 : p % 4 = 3) (hp : 3 ≤ p)
    (S T : Finset (Fin 4)) (F : ZMod p × ZMod p → ℝ)
    {bS bT : ℝ} (hbS : 0 ≤ bS) (hbT : 0 ≤ bT)
    (hS : ∀ c : CoreT (ZMod p), |starMean S c.val| ≤ bS)
    (hT : ∀ c : CoreT (ZMod p), |starMean T c.val| ≤ bT) :
    nrm coreLaw (fun c : CoreT (ZMod p) => normalizedStarProduct S T (variableDiagonalPart F) c.val) ≤
      ((p : ℝ) / Real.sqrt (p - 2)) *
        (rp p + ((S ∩ T).card : ℝ) * (p : ℝ)⁻¹ + (bS + bT) * rp p) *
          nrm ((fieldLaw p).product (fieldLaw p)) (variableDiagonalPart F) := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp2 : (0 : ℝ) < p - 2 := by linarith
  have hs : Real.sqrt ((p : ℝ) - 2) ≠ 0 := (Real.sqrt_pos.mpr hp2).ne'
  have hcard : 3 ≤ Fintype.card (ZMod p) := by simpa only [ZMod.card] using hp
  have hnorm := variableDiagonalPart_norm hcard F
  simp only [ZMod.card] at hnorm
  simp_rw [normalizedStarProduct_variableDiagonal]
  rw [nrm_smul, abs_of_nonneg (div_nonneg (Nat.cast_nonneg p) hp2.le)]
  have h := core_centeredProductImage_norm hp3 S T (diagonalFluctuation F)
    (diagonalFluctuation_mean F) hbS hbT hS hT
  refine (mul_le_mul_of_nonneg_left h (div_nonneg (Nat.cast_nonneg p) hp2.le)).trans_eq ?_
  change _ = _ * nrm ((FiniteLaw.uniform (ZMod p)).product (FiniteLaw.uniform (ZMod p)))
    (variableDiagonalPart F)
  rw [hnorm]
  change _ = (p : ℝ) / Real.sqrt (p - 2) *
    (rp p + ((S ∩ T).card : ℝ) * (p : ℝ)⁻¹ + (bS + bT) * rp p) *
      (nrm (fieldLaw p) (diagonalFluctuation F) / Real.sqrt (p - 2))
  have he := Real.sq_sqrt hp2.le
  field_simp [hp2.ne']
  rw [he]
  ring

end Sarkozy.PositiveRoots.CoherentFrame
