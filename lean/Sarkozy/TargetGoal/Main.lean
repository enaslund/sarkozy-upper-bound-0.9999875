module

public import Sarkozy.TargetConclusion
public import Sarkozy.MainFinalF1.Main

/-!
# The owner's goal exponent `N^{0.99999}`

On 7 November 2026 the owner set the formal goal to `s(N) ≤ C·N^{0.99999}`, i.e. `ε = 10⁻⁵`.
This is weaker than the round target `Target.epsTarget = 3/250000` (`N^{0.999988}`) at which the
current ledger is built. Since 7 November 2026 the endgame runs at the baseline `ϑ = 1`, so the
ledger's price exponent `a_T` gives the saving `TargetLedger.targetSaving = a_T/71 ≈ 1.19975·10⁻⁵`,
slightly below `epsTarget` but above the goal; every result at `targetSaving` gives the goal by
`Target.sarkozyBound_mono` (`epsGoal_le_targetSaving`).

`epsGoal` lives here, not in `Sarkozy/Target.lean`, so that the large tree does not rebuild. When
the Palomar challenge is assembled, it should move into the challenge file.

The extra room, `a` from about `8.52·10⁻⁴` down to `10⁻⁵·71 = 7.1·10⁻⁴`, is not used yet.
Using it means rebuilding the ledger at the smaller `a`.
-/

@[expose] public section

namespace Sarkozy.TargetGoal

/-- The owner's goal exponent: `ε = 10⁻⁵`, the bound `s(N) ≤ C·N^{0.99999}`. -/
noncomputable def epsGoal : ℝ := 1 / 100000

/-- The goal is weaker than the round target `N^{0.999988}`. -/
theorem epsGoal_le_epsTarget : epsGoal ≤ Target.epsTarget := by
  norm_num [epsGoal, Target.epsTarget]

/-- **The goal is weaker than the baseline saving at `a_T`**: `10⁻⁵ ≤ a_T/71`
(`TargetLedger.targetSaving`, the exponent of the endgame at `ϑ = 1` since 7 November 2026). -/
theorem epsGoal_le_targetSaving : epsGoal ≤ TargetLedger.targetSaving :=
  TargetLedger.goal_le_targetSaving

/-- **The current main statement at the goal exponent.** This is
`MainFinalF1.main_target_f1_final3c` (the F1 partition, the combined residual gate) followed by
monotonicity in the exponent. -/
theorem main_goal_f1 (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalF1.MainFinalObligations3c hWeil hMovingRoot hFourCycle hBMOR) :
    Target.SarkozyBound epsGoal :=
  Target.sarkozyBound_mono epsGoal_le_targetSaving
    (MainFinalF1.main_target_f1_final3c hWeil hBMOR hMovingRoot hFourCycle
      hThetaSmallRR O)

end Sarkozy.TargetGoal
