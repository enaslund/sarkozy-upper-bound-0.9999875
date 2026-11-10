module

public import Sarkozy.AnalyticCells.F1Consts

@[expose] public section

/-!
# The F1 cell bounds at `s = 3/2`

`bound3c ≤ c'_3` (secant bound) for the 29 F1 pieces and the paper's pieces `29–32`
(`decide +kernel`).
-/

namespace Sarkozy.AnalyticCells

theorem f1_bound3 : ∀ i : Fin 29, (f1Geo i.val).bound3c ≤ f1C3 i.val := by decide +kernel

theorem paper_bound3c : geo29.bound3c ≤ f1C3 29 ∧ geo30.bound3c ≤ f1C3 30 ∧
    geo31.bound3c ≤ f1C3 31 ∧ geo32.bound3c ≤ f1C3 32 := by decide +kernel

end Sarkozy.AnalyticCells
