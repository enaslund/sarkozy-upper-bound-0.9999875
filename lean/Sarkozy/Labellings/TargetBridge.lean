module

public import Sarkozy.Labellings.Extension
public import Sarkozy.Target

/-!
# From the target's Weil hypothesis to `WeilBound`

`Sarkozy.Target.Weil` (the literature input H1 as stated in the review file `Sarkozy/Target.lean`)
gives `WeilBound (ZMod p)` at every odd prime, the form used by `Sarkozy.Labellings`.
-/

@[expose] public section

namespace Sarkozy.Labellings

theorem weilBound_of_target (h : Target.Weil) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    WeilBound (ZMod p) := by
  intro S hS
  have := h p hp2 S hS
  rw [ZMod.card]
  exact this

end Sarkozy.Labellings
