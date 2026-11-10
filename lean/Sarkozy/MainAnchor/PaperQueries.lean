module

public import Sarkozy.TheoremC.Defs

@[expose] public section



namespace Sarkozy.MainAnchor

open Sarkozy.TheoremC

/-- The sources `(0, j, 0)` lie in the plus half `V₊` of the reserved cut. -/
theorem querySource_mem_half : ∀ j : Chamber, querySource j ∈ reservedCut.half := by
  decide

/-- The reflected targets `ι(2, ρj, 1) = (2, ρj, 0)` lie in `V₊`. -/
theorem flip_queryTarget_mem_half :
    ∀ j : Chamber, reservedCut.flip (queryTarget j) ∈ reservedCut.half := by
  decide

theorem querySource_injective : Function.Injective querySource := by
  decide

theorem flip_queryTarget_injective :
    Function.Injective (fun j : Chamber => reservedCut.flip (queryTarget j)) := by
  decide

/-- **The paper's six queries `𝓔₆`** (`subsec:front6:construction`), indexed by `j ∈ ℤ/6ℤ`. -/
def paperQueries : Queries Chamber where
  u j := ⟨querySource j, querySource_mem_half j⟩
  w j := ⟨reservedCut.flip (queryTarget j), flip_queryTarget_mem_half j⟩
  hu _ _ h := querySource_injective (congrArg Subtype.val h)
  hw _ _ h := flip_queryTarget_injective (congrArg Subtype.val h)

/-- The source of the query `j` is `(0, j, 0)`. -/
theorem paperQueries_source (j : Chamber) : paperQueries.source j = (0, j, 0) := rfl

/-- The target of the query `j` is `(2, ρj, 1)`. -/
theorem paperQueries_target (j : Chamber) :
    paperQueries.target j = (2, chamberRotation j, 1) := by
  show reservedCut.flip (reservedCut.flip (queryTarget j)) = _
  rw [reservedCut.flip_flip]
  rfl

/-- Six queries. -/
theorem card_chamber : Fintype.card Chamber = 6 := ZMod.card 6

end Sarkozy.MainAnchor
