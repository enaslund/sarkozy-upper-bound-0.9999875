module

public import Sarkozy.Companion.Main

@[expose] public section





namespace Sarkozy.Rebase

open Sarkozy.Companion (CompanionObligations)
open Sarkozy.UpperCapsPaper (UpperRecordTables)

/-- **The saving of the rebased ledger is the goal**: `a_G/71 = 10⁻⁵ = epsGoal`. -/
theorem targetSaving_eq_epsGoal : TargetLedger.targetSaving = TargetGoal.epsGoal := by
  norm_num [TargetLedger.targetSaving, TargetGoal.epsGoal]

/-- **The main statement at the goal, directly** (`thm:main` at `ε = 10⁻⁵`; `thm:density:induction`
at `ϑ = 1` with the four-routes closing at `a_G = 71/10⁵`, `Θ < 0.72`): `s(N) ≤ C·N^{0.99999}` from
the literature hypotheses, the record table `UpT` and the companion obligations `O`. The endgame's
conclusion `SarkozyBound targetSaving` is the goal itself (`targetSaving_eq_epsGoal`), with no
monotonicity step. -/
theorem main_goal_rebased (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables)
    (O : CompanionObligations hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR UpT) :
    Target.SarkozyBound TargetGoal.epsGoal := by
  have h := MainCombined.main_target_f1_final3gc hWeil hBMOR hMovingRoot hFourCycle
    hThetaSmallRR O.toKT1.toT1.toGP.toG
  rwa [targetSaving_eq_epsGoal] at h

end Sarkozy.Rebase
