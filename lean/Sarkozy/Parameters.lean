module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section




namespace Sarkozy

def slots : ℕ := 72
def blockScale : ℕ := 863660
noncomputable def decay : ℝ := 1814179 / 2000000000
noncomputable def densityExponent : ℝ := 1
/-- The paper's upgraded density exponent `ϑ = 1014587/10⁶` (reference only; not used by the
endgame since 7 November 2026). -/
noncomputable def upgradedDensityExponent : ℝ := 1014587 / 1000000
noncomputable def saving : ℝ := 1814179 / 142000000000
noncomputable def titleExponent : ℝ := 0.9999873
noncomputable def closingCap : ℝ := 0.999999771
noncomputable def closingMargin : ℝ := 0.000000229
noncomputable def momentSlack : ℝ := 1 / 10000
noncomputable def cancellationDecay : ℝ := 1 / 825
noncomputable def densityRatio : ℝ := (densityExponent - 1) / (2 - densityExponent)
noncomputable def relativeErrorDecay : ℝ :=
  cancellationDecay - decay - (decay + momentSlack) * densityRatio

theorem decay_pos : 0 < decay := by norm_num [decay]

theorem densityExponent_bounds : 1 ≤ densityExponent ∧ densityExponent < 2 := by
  norm_num [densityExponent]

theorem degree_gap_pos : 0 < (slots : ℝ) - densityExponent := by
  norm_num [slots, densityExponent]

theorem saving_eq : saving = decay / ((slots : ℝ) - densityExponent) := by
  norm_num [saving, decay, slots, densityExponent]

theorem saving_pos : 0 < saving := by norm_num [saving]

theorem saving_lt_one : saving < 1 := by norm_num [saving]

theorem exact_exponent_lt_title : 1 - saving < titleExponent := by
  norm_num [saving, titleExponent]

theorem closingCap_lt_one : closingCap < 1 := by norm_num [closingCap]

theorem closingMargin_pos : 0 < closingMargin := by norm_num [closingMargin]

theorem closingCap_add_margin : closingCap + closingMargin = 1 := by
  norm_num [closingCap, closingMargin]

/-- The uniform analytic error gate in the proof of the upgraded induction. -/
theorem uniform_error_margin :
    (1 : ℝ) / 825 -
        (91 / 100000 + (101 / 100000) * (14587 / 985413)) =
      943271 / 3284710000 := by
  norm_num

/-- The selected parameters lie strictly inside that analytic error gate. -/
theorem selected_error_gate :
    decay + (decay + 1 / 10000) *
      ((densityExponent - 1) / (2 - densityExponent)) < (1 : ℝ) / 825 := by
  norm_num [decay, densityExponent]

/-- At the baseline `ϑ = 1` the density ratio `(ϑ − 1)/(2 − ϑ)` vanishes. -/
theorem densityRatio_eq_zero : densityRatio = 0 := by
  norm_num [densityRatio, densityExponent]

theorem densityRatio_nonneg : 0 ≤ densityRatio := by
  norm_num [densityRatio, densityExponent]

theorem relativeErrorDecay_pos : 0 < relativeErrorDecay := by
  norm_num [relativeErrorDecay, cancellationDecay, decay, momentSlack,
    densityRatio, densityExponent]

end Sarkozy
