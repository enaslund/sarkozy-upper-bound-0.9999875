module

public import Sarkozy.AnalyticCells.F1Data

@[expose] public section

/-!
# The kernel conditions on the F1 cells

`GeoQ.Checks` for the 29 F1 pieces: `n_j = ⌊570/log x_{j+1}⌋` on all 799 cells, and the
ranges.
-/

namespace Sarkozy.AnalyticCells

theorem f1_checks : ∀ i : Fin 29, (f1Geo i.val).Checks = true := by decide +kernel

end Sarkozy.AnalyticCells
