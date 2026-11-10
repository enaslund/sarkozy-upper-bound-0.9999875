module

public import Sarkozy.SpectralD.RootTailOne
public import Sarkozy.SpectralD.RootTailThree

/-! The two root spectral bounds for every tail prime. -/

@[expose] public section

namespace Sarkozy.SpectralD.Root

open Sarkozy.Labellings Sarkozy.Extraction Sarkozy.SpectralC
open scoped InnerProductSpace

variable {p : ℕ} [Fact p.Prime]

theorem LL20_tail (hW : Target.Weil) (hMR : Target.MovingRoot) (h4 : FourCycleBound p)
    (hp : 2 ^ 512 ≤ p) (hne : (injLabellings (ZMod p) LL20.G).Nonempty)
    (v : EuclideanSpace ℝ (LL20.cut.Half → ZMod p)) :
    -(113 * rp p) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp LL20 hne v⟫_ℝ := by
  rcases PaleyB.mod_four_cases (Fact.out : p.Prime) (by omega) with hp1 | hp3
  · exact LL20_tail_one hW hMR h4 hp hp1 hne v
  · exact LL20_tail_three hW hMR h4 hp hp3 hne v

theorem LL22_tail (hW : Target.Weil) (hMR : Target.MovingRoot) (h4 : FourCycleBound p)
    (hp : 2 ^ 512 ≤ p) (hne : (injLabellings (ZMod p) LL22.G).Nonempty)
    (v : EuclideanSpace ℝ (LL22.cut.Half → ZMod p)) :
    -(45 * rp p) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp LL22 hne v⟫_ℝ := by
  rcases PaleyB.mod_four_cases (Fact.out : p.Prime) (by omega) with hp1 | hp3
  · exact LL22_tail_one hW hMR h4 hp hp1 hne v
  · exact LL22_tail_three hW hMR h4 hp hp3 hne v

end Sarkozy.SpectralD.Root
