module

public import Sarkozy.PositiveRoots.CoherentDiagonalGeometry
public import Sarkozy.PositiveRoots.CoherentDiagonalRectangle

/-! Exact scalar prices for the collected auxiliary-diagonal traces. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.PartV.CoherentDictionary Sarkozy.L20Cap

theorem diagonalCoreFactor_real (S : Finset (Fin 4)) :
    (diagonalCoreFactor S : ℝ) = coreStarFactor S := by
  unfold diagonalCoreFactor coreStarFactor
  split_ifs <;> norm_num

noncomputable def diagonalWeightedPrice (p : ℕ) (R M : ℝ) (sc : Support × ℚ) : ℝ :=
  (p : ℝ)⁻¹ * (R * ((diagonalCoreCost sc : ℝ) * (coreCubeDensity p / 16) +
    (diagonalPrivateCost sc : ℝ) * ((p : ℝ) / (p - 1))) + (diagonalCrossCost sc : ℝ) * M)

noncomputable def coherentTwoSidedPrice (p : ℕ) (R M : ℝ) : ℝ :=
  (p : ℝ)⁻¹ * (R * ((3712 / 225 : ℝ) * (coreCubeDensity p / 16) +
    (44 / 15 : ℝ) * ((p : ℝ) / (p - 1))) + (32 / 225 : ℝ) * M)

theorem diagonal_price_sum (p : ℕ) (R M : ℝ) :
    (collectedTwoSided.map (diagonalWeightedPrice p R M)).sum = coherentTwoSidedPrice p R M := by
  have hc := congrArg (fun q : ℚ => (q : ℝ)) diagonal_core_sum
  have hp := congrArg (fun q : ℚ => (q : ℝ)) diagonal_private_sum
  have hx := congrArg (fun q : ℚ => (q : ℝ)) diagonal_cross_sum
  simp only [Rat.cast_list_sum, List.map_map, Function.comp_def, Rat.cast_div, Rat.cast_ofNat]
    at hc hp hx
  unfold diagonalWeightedPrice coherentTwoSidedPrice
  simp only [List.sum_map_mul_left, List.sum_map_add, List.sum_map_mul_right, hc, hp, hx]

theorem coherentTwoSidedPrice_nonneg {p : ℕ} (hp7 : 7 < p) {R M : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M) : 0 ≤ coherentTwoSidedPrice p R M := by
  have hp : (7 : ℝ) < p := by exact_mod_cast hp7
  have hD := (coreCubeDensity_pos hp7).le
  have hfrac : 0 ≤ (p : ℝ) / (p - 1) := div_nonneg (by positivity) (by linarith)
  unfold coherentTwoSidedPrice
  positivity

end Sarkozy.PositiveRoots.CoherentFrame
