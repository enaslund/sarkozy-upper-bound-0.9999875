module

public import Sarkozy.Target
public import Sarkozy.Definitions

/-!
# The target's conclusion is the development's `PowerSavingBound`

`Sarkozy/Target.lean` states the agreed target as `Target.SarkozyBound ε`, using only Mathlib.
The development proves its main theorems with the conclusion `PowerSavingBound`
(`Sarkozy/Definitions.lean`). This file checks that the two agree at the paper's exponent:
`PowerSavingBound ↔ Target.SarkozyBound saving`. The definitions differ only in currying
(`Admissible N A` versus the two separate conditions).

Since 7 November 2026 the hard-coded `saving = decay/(72 − ϑ)` is at the baseline `ϑ = 1`, i.e.
`saving = 1814179/142000000000`, just below the paper's record `Target.epsPaper`
(`saving_lt_epsPaper`), which is computed at the upgraded `ϑ = 1014587/10⁶`.
-/

@[expose] public section

namespace Sarkozy

/-- At `ϑ = 1` the hard-coded saving is below the paper's record exponent. -/
theorem saving_lt_epsPaper : saving < Target.epsPaper := by
  norm_num [saving, Target.epsPaper]

theorem isSquareDifferenceFree_iff (A : Finset ℤ) :
    IsSquareDifferenceFree A ↔ Target.SquareDifferenceFree A := Iff.rfl

/-- **`PowerSavingBound` is the target's conclusion at the hard-coded exponent `saving`.** -/
theorem powerSavingBound_iff_target : PowerSavingBound ↔ Target.SarkozyBound saving := by
  unfold PowerSavingBound CardinalityBound Target.SarkozyBound Admissible
  constructor
  · rintro ⟨C, hC, h⟩
    exact ⟨C, hC, fun N hN A hA hsq => h N hN A ⟨hA, hsq⟩⟩
  · rintro ⟨C, hC, h⟩
    exact ⟨C, hC, fun N hN A hA => h N hN A hA.1 hA.2⟩

theorem target_of_powerSavingBound (h : PowerSavingBound) :
    Target.SarkozyBound saving :=
  powerSavingBound_iff_target.mp h

/-! ## Facts about the target's hypotheses and exponents -/

/-- **H2″ in Theorem 5.2.1's form implies the Theorem 2 form** (`1.174 ≤ 2.072`). -/
theorem Target.thetaSmall_of_thetaSmallRR (h : Target.ThetaSmallRR) : Target.ThetaSmall :=
  fun x hx1 hx2 => (h x hx1 hx2).trans
    (mul_le_mul_of_nonneg_right (by norm_num) (Real.sqrt_nonneg x))

/-- **`SarkozyBound` is monotone in the exponent**: a bound with a larger saving implies one with a
smaller saving, because `N^{1-ε₁} ≤ N^{1-ε₂}` for `N ≥ 1` and `ε₂ ≤ ε₁`. -/
theorem Target.sarkozyBound_mono {ε₁ ε₂ : ℝ} (h : ε₂ ≤ ε₁) (hB : Target.SarkozyBound ε₁) :
    Target.SarkozyBound ε₂ := by
  obtain ⟨C, hC, hB⟩ := hB
  refine ⟨C, hC, fun N hN A hA hsd => (hB N hN A hA hsd).trans ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) hC.le

/-- The round target `N^{0.999988}` is weaker than the anchor `N^{0.99998747}`. -/
theorem Target.epsTarget_le_epsAnchor : Target.epsTarget ≤ Target.epsAnchor := by
  norm_num [Target.epsTarget, Target.epsAnchor]

/-- **A bound at the anchor exponent gives the owner's round target `N^{0.999988}`.** -/
theorem Target.sarkozyBound_epsTarget_of_epsAnchor (h : Target.SarkozyBound Target.epsAnchor) :
    Target.SarkozyBound Target.epsTarget :=
  Target.sarkozyBound_mono Target.epsTarget_le_epsAnchor h

end Sarkozy
