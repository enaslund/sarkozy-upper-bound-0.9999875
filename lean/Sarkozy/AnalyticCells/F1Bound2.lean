module

public import Sarkozy.AnalyticCells.F1Consts

@[expose] public section

/-!
# The F1 cell bounds at `s = 1`

`bound2 ≤ c'_2` for the 29 F1 pieces (`decide +kernel`).
-/

namespace Sarkozy.AnalyticCells

theorem f1_bound2 : ∀ i : Fin 29, (f1Geo i.val).bound2 ≤ f1C2 i.val := by decide +kernel

end Sarkozy.AnalyticCells
