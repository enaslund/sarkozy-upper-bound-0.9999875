module

public import Sarkozy.JointRows.StarHoeffding

/-! Integrating two selected coordinates of an independent finite law. -/

@[expose] public section

namespace Sarkozy.JointRows.Star

open Sarkozy.FiveType Sarkozy.FiveType.Blocks

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X]

theorem expect_update_two (ν : ι → FiniteLaw X) (i j : ι) (f : (ι → X) → ℝ) :
    (blockLaw ν).expect f = (blockLaw ν).expect (fun x =>
      (ν i).expect (fun a => (ν j).expect (fun b => f (Function.update (Function.update x i a) j b)))) := by
  change (blockLaw ν).expect f = (blockLaw ν).expect (condMean ν i (condMean ν j f))
  rw [expect_condMean, expect_condMean]

theorem expect_two_coordinate_bound (ν : ι → FiniteLaw X) (i j : ι)
    (f : (ι → X) → ℝ) {B : ℝ}
    (hB : ∀ x, (ν i).expect (fun a => (ν j).expect
      (fun b => f (Function.update (Function.update x i a) j b))) ≤ B) :
    (blockLaw ν).expect f ≤ B := by
  rw [expect_update_two ν i j f]
  exact FiniteLaw.expect_le_const _ hB

end Sarkozy.JointRows.Star
