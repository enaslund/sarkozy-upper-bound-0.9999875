module

public import Sarkozy.Param.Anchor
public import Sarkozy.TargetConclusion

@[expose] public section





namespace Sarkozy.TargetLedger

open Sarkozy.Param (Params)

/-- **The ledger's price exponent** `a_G = 71/10⁵ = ε_G (72 − 1)` with `ε_G = 10⁻⁵`
(`TargetGoal.epsGoal`) at `ϑ = 1` (RG, 7 November 2026; it was
`a_T = 212956239/250000000000`). -/
noncomputable def targetDecay : ℝ := 71 / 100000

theorem targetDecay_nonneg : 0 ≤ targetDecay := by norm_num [targetDecay]

theorem targetDecay_pos : 0 < targetDecay := by norm_num [targetDecay]

/-- `a_G < a₀`: the ledger's exponent lies below the anchor (`a_G/a₀ ≈ 0.79806`). -/
theorem targetDecay_lt_anchorDecay : targetDecay < Params.anchorDecay := by
  norm_num [targetDecay, Params.anchorDecay]

/-- The side conditions of `thm:density:induction` hold at `a_G`. -/
theorem target_valid : (Params.ofDecay targetDecay).Valid :=
  Params.ofDecay_valid (by norm_num [targetDecay])

/-- **The saving at `a_G` and `ϑ = 1`**: `a_G/71 = 10⁻⁵`, the owner's goal. -/
noncomputable def targetSaving : ℝ := 1 / 100000

/-- `targetSaving = 10⁻⁵` is below the earlier round target `3/250000`. -/
theorem targetSaving_lt_epsTarget : targetSaving < Target.epsTarget := by
  norm_num [targetSaving, Target.epsTarget]

/-- `targetSaving` is the owner's goal `ε = 10⁻⁵` (`TargetGoal.epsGoal`); this is `≤` by
equality. -/
theorem goal_le_targetSaving : (1 : ℝ) / 100000 ≤ targetSaving := by
  norm_num [targetSaving]

theorem targetSaving_pos : 0 < targetSaving := by norm_num [targetSaving]

/-- **The saving at `a_G`**: `a_G/(72 − ϑ) = a_G/71 = targetSaving = 10⁻⁵` at `ϑ = 1`. -/
theorem target_saving : (Params.ofDecay targetDecay).saving = targetSaving := by
  rw [Params.ofDecay_saving]
  norm_num [targetDecay, targetSaving, slots, Sarkozy.densityExponent]

/-- The development's conclusion at `a_G` is the target statement at `targetSaving = 10⁻⁵`
(`N^{0.99999}`). -/
theorem target_powerSavingBound_iff :
    Param.PowerSavingBound (Params.ofDecay targetDecay) ↔ Target.SarkozyBound targetSaving := by
  rw [Param.sarkozyBound_iff, target_saving]

end Sarkozy.TargetLedger
