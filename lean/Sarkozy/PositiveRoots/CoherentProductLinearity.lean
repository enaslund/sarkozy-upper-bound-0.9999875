module

public import Sarkozy.PositiveRoots.CoherentProductInputs

/-! Linearity of the normalized raw-star product in its auxiliary input. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Sarkozy.SpectralC.TwoLabel

variable {p : ℕ} [Fact p.Prime] {U : Type*}

theorem normalizedStarProduct_smul (S T : Finset U) (a : ℝ) (F : ZMod p × ZMod p → ℝ)
    (x : U → ZMod p) :
    normalizedStarProduct S T (fun z => a * F z) x = a * normalizedStarProduct S T F x := by
  unfold normalizedStarProduct starProduct
  simp_rw [mul_left_comm _ a, FiniteLaw.expect_const_mul]
  ring

theorem normalizedStarProduct_add (S T : Finset U) (F G : ZMod p × ZMod p → ℝ)
    (x : U → ZMod p) :
    normalizedStarProduct S T (fun z => F z + G z) x =
      normalizedStarProduct S T F x + normalizedStarProduct S T G x := by
  unfold normalizedStarProduct starProduct
  simp_rw [mul_add, FiniteLaw.expect_add]
  ring

theorem normalizedStarProduct_sub (S T : Finset U) (F G : ZMod p × ZMod p → ℝ)
    (x : U → ZMod p) :
    normalizedStarProduct S T (fun z => F z - G z) x =
      normalizedStarProduct S T F x - normalizedStarProduct S T G x := by
  unfold normalizedStarProduct starProduct
  simp_rw [mul_sub, FiniteLaw.expect_sub]
  ring

end Sarkozy.PositiveRoots.CoherentFrame
