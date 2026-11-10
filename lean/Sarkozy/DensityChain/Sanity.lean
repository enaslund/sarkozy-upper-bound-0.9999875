module

public import Sarkozy.DensityChain.BlockDC

@[expose] public section

/-!
# Sanity checks for the density-chain package

* **(S1) is satisfiable at the remainder exponent.** The chain's comparison
  (`density_dc_block`) holds for every `σ ≥ 0` with `ε/20 − γ/40 ≤ −σ`. At `ε = 1/10` this allows
  `σ = cancellationDecay = 1/825`, the exponent of `Comparison.remainder`, which
  `EnvMeanBound` and `FixMeanBound` ask (`S1_at_cancellationDecay`).
* **(S4) leaves room for `lem:record:density-lp`.** Rankin's trick gives `N^{-τ/4}` and the
  moment bound `N^ε`: `τ/4 > 1/825` (`lp_room`), so `N^{ε − τ/4} ≤ L^{-1/825}` for small `ε`.
* **The prefix conductor is positive and independent of the scale** (`prefixConductor_pos`), and
  `C_dc ≥ 0` (`dcConstant_nonneg`).
-/

namespace Sarkozy.DensityChain

/-- (S1) at `ε = 1/10` and `σ = cancellationDecay`. -/
theorem S1_at_cancellationDecay :
    (1 / 10 : ℝ) / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -Sarkozy.cancellationDecay := by
  unfold Sarkozy.AnalyticStage.γ Sarkozy.cancellationDecay
  norm_num

/-- The room of `lem:record:density-lp` against the remainder exponent: `1/825 < τ/4`. -/
theorem lp_room : Sarkozy.cancellationDecay < Sarkozy.Functional.stageTau / 4 := by
  unfold Sarkozy.cancellationDecay Sarkozy.Functional.stageTau
  norm_num

end Sarkozy.DensityChain
