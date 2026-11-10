module

public import Sarkozy.F3Kernel.Components

/-! One bounded part of the kernel verification of the four-witness component table. -/

@[expose] public section

namespace Sarkozy.F3Kernel.Components.Four10

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked : ∀ j : Fin 2048,
    DiagZero 4 (2048 * 10 + j.val) → ValidEntry LL20.SCC4 4 (2048 * 10 + j.val) := by
  decide +kernel

end Sarkozy.F3Kernel.Components.Four10
