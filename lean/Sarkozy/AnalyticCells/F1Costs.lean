module

public import Sarkozy.AnalyticCells.F1Consts
public import Sarkozy.PaperNumbers.Costs

@[expose] public section





open Finset
open scoped BigOperators

namespace Sarkozy.AnalyticCells

open Sarkozy.PartV Sarkozy.BlockSpecPaper Sarkozy.RecordExpansion Sarkozy.Certificates
  Sarkozy.MiddleRecords Sarkozy.PaperNumbers
open Sarkozy.TargetLedger (targetDecay targetLedger)

/-- A decimal upper bound of the price total at the F1 numbers. -/
def costP2 : ℚ := 1392745204910237 / 1000000000000000

/-- A decimal upper bound of the sharp tag total at the F1 numbers. -/
def costD2 : ℚ := 195696186319033 / 10000000000000000000

/-- An upper bound of `𝔗⁺₃(costD2, costV)`. -/
def costT2 : ℚ := 1664333213533133 / 25000000000000000000

theorem f1_sumU_le : ∑ i : Fin 33, (U2Q i * f1C2 i.val + U3Q i * f1C3 i.val) ≤ costU := by
  decide +kernel

theorem f1_sumP_le : ∑ i : Fin 33, (P2Q i * f1C2 i.val + P3Q i * f1C3 i.val) ≤ costP2 := by
  decide +kernel

theorem f1_sumD_le : ∑ i : Fin 33, D3Q i * f1C3 i.val ≤ costD2 := by decide +kernel

theorem f1_sumV_le : ∑ i : Fin 33, V2Q i * f1C2 i.val ≤ costV := by decide +kernel

theorem f1C_nonneg : ∀ i : Fin 33, 0 ≤ f1C2 i.val ∧ 0 ≤ f1C3 i.val := by decide +kernel

theorem costD2_nonneg : (0 : ℝ) ≤ (costD2 : ℝ) := by unfold costD2; norm_num

/-- **`cor:two-cut-series` at the F1 totals**: `𝔗⁺₃(costD2, costV) ≤ costT2`. -/
theorem twoTagUpper_le2 : twoTagUpper 3 (costD2 : ℝ) (costV : ℝ) ≤ (costT2 : ℝ) := by
  have hE : Real.exp (costV : ℝ) ≤ (expUpper costVWitness : ℝ) := (ExpWitness.sound costV_valid).2
  unfold twoTagUpper twoGroup
  generalize Real.exp (costV : ℝ) = y at hE ⊢
  norm_num [Finset.sum_range_succ, Nat.factorial, costD2, costV, costT2, expUpper, costVWitness]
    at hE ⊢
  linarith

theorem tagSeries_le_costT2 {d v : Fin 2 → ℝ} (hd0 : ∀ j, 0 ≤ d j) (hv0 : ∀ j, 0 ≤ v j)
    (hd : ∀ j, d j ≤ costD2) (hv : ∀ j, v j ≤ costV) : tagSeries d v ≤ (costT2 : ℝ) := by
  have h1 := tagSeries_mono (d' := fun _ => (costD2 : ℝ)) (v' := fun _ => (costV : ℝ)) hd0 hv0
    hd hv
  rw [tagSeries_fin_two] at h1
  have hgate1 : (costD2 : ℝ) < (3 : ℕ) + 2 := by norm_num [costD2]
  have hgate2 : (costD2 : ℝ) * costV < (((3 : ℕ) : ℝ) + 2) ^ 2 := by norm_num [costD2, costV]
  exact h1.trans ((tagSeries_two_le costD2_nonneg costV_nonneg 3 hgate1 hgate2).trans
    twoTagUpper_le2)

/-- The F1 charge numbers as reals. -/
noncomputable def f1c2 (i : Fin 33) : ℝ := (f1C2 i.val : ℝ)

/-- The F1 charge numbers as reals. -/
noncomputable def f1c3 (i : Fin 33) : ℝ := (f1C3 i.val : ℝ)

/-- The sharp tag totals at the F1 numbers. -/
noncomputable def f1D : Fin 2 → ℝ := fun _ => ∑ i, (0 * f1c2 i + fsD3 i * f1c3 i)

/-- The variation tag totals at the F1 numbers. -/
noncomputable def f1V : Fin 2 → ℝ := fun _ => ∑ i, (fsV2 i * f1c2 i + 0 * f1c3 i)

theorem f1D_le (j : Fin 2) : f1D j ≤ costD2 := by
  unfold f1D
  have h : ∑ i, (0 * f1c2 i + fsD3 i * f1c3 i) ≤ ∑ i, ((D3Q i * f1C3 i.val : ℚ) : ℝ) :=
    sum_le_sum fun i _ => by
      unfold f1c3
      push_cast
      rw [zero_mul, zero_add]
      exact mul_le_mul_of_nonneg_right (fsD3_le i) (by exact_mod_cast (f1C_nonneg i).2)
  refine h.trans ?_
  rw [← Rat.cast_sum]
  exact_mod_cast f1_sumD_le

theorem f1V_le (j : Fin 2) : f1V j ≤ costV := by
  unfold f1V
  have h : ∑ i, (fsV2 i * f1c2 i + 0 * f1c3 i) = ∑ i, ((V2Q i * f1C2 i.val : ℚ) : ℝ) :=
    sum_congr rfl fun i _ => by
      unfold f1c2
      push_cast
      rw [fsV2_eq, zero_mul, add_zero]
  rw [h, ← Rat.cast_sum]
  exact_mod_cast f1_sumV_le

theorem f1D_nonneg (j : Fin 2) : 0 ≤ f1D j :=
  sum_nonneg fun i _ => by
    rw [zero_mul, zero_add]
    exact mul_nonneg (fsD3_nonneg i) (by unfold f1c3; exact_mod_cast (f1C_nonneg i).2)

theorem f1V_nonneg (j : Fin 2) : 0 ≤ f1V j :=
  sum_nonneg fun i _ => by
    rw [zero_mul, add_zero]
    exact mul_nonneg (fsV2_nonneg i) (by unfold f1c2; exact_mod_cast (f1C_nonneg i).1)

/-- **The cost inequality of `hB` at the F1 numbers.** -/
theorem f1_costB_le :
    Real.exp (∑ i : Fin 33, (chargeU2 i * f1c2 i + chargeU3 i * f1c3 i)) *
      (1 + tagSeries f1D f1V) ≤ targetLedger.B := by
  have hsum : ∑ i : Fin 33, (chargeU2 i * f1c2 i + chargeU3 i * f1c3 i) =
      ((∑ i : Fin 33, (U2Q i * f1C2 i.val + U3Q i * f1C3 i.val) : ℚ) : ℝ) := by
    rw [Rat.cast_sum]
    exact sum_congr rfl fun i _ => by
      unfold f1c2 f1c3
      push_cast
      rw [chargeU2_eq, chargeU3_eq]
  have hU : Real.exp (∑ i : Fin 33, (chargeU2 i * f1c2 i + chargeU3 i * f1c3 i)) ≤
      (expUpper costUWitness : ℝ) := by
    rw [hsum]
    refine (Real.exp_le_exp.mpr ?_).trans (ExpWitness.sound costU_valid).2
    exact_mod_cast f1_sumU_le
  have hT := tagSeries_le_costT2 f1D_nonneg f1V_nonneg f1D_le f1V_le
  have hT0 : 0 ≤ tagSeries f1D f1V := tagSeries_nonneg f1D_nonneg f1V_nonneg
  have hE0 : (0 : ℝ) ≤ (expUpper costUWitness : ℝ) := (Real.exp_pos _).le.trans hU
  calc Real.exp (∑ i : Fin 33, (chargeU2 i * f1c2 i + chargeU3 i * f1c3 i)) *
        (1 + tagSeries f1D f1V)
      ≤ (expUpper costUWitness : ℝ) * (1 + (costT2 : ℝ)) :=
        mul_le_mul hU (by linarith) (by linarith) hE0
    _ ≤ targetLedger.B := by
        norm_num [targetLedger, expUpper, costUWitness, costT2]

theorem costL2_check : expUpQ costP2 * costT2 ≤ 271970853 / 1000000000000 := by decide +kernel

/-- **The cost inequality of `hL₀` at the F1 numbers.** -/
theorem f1_costL_le :
    TheoremC.firstStageCost (∑ i, (fsP2 i * f1c2 i + fsP3 i * f1c3 i)) f1D f1V ≤
      targetLedger.L₀ := by
  have hsum : ∑ i, (fsP2 i * f1c2 i + fsP3 i * f1c3 i) =
      ((∑ i : Fin 33, (P2Q i * f1C2 i.val + P3Q i * f1C3 i.val) : ℚ) : ℝ) := by
    rw [Rat.cast_sum]
    exact sum_congr rfl fun i _ => by
      unfold f1c2 f1c3
      push_cast
      rw [fsP2_eq, fsP3_eq]
  have hP : Real.exp (∑ i, (fsP2 i * f1c2 i + fsP3 i * f1c3 i)) ≤ (expUpQ costP2 : ℝ) := by
    rw [hsum]
    refine (Real.exp_le_exp.mpr ?_).trans (exp_le_expUpQ (by unfold costP2; norm_num [abs_le]))
    exact_mod_cast f1_sumP_le
  have hT := tagSeries_le_costT2 f1D_nonneg f1V_nonneg f1D_le f1V_le
  have hT0 : 0 ≤ tagSeries f1D f1V := tagSeries_nonneg f1D_nonneg f1V_nonneg
  have hE0 : (0 : ℝ) ≤ (expUpQ costP2 : ℝ) := (Real.exp_pos _).le.trans hP
  have hL : (expUpQ costP2 : ℝ) * (costT2 : ℝ) ≤ targetLedger.L₀ := by
    have h : ((expUpQ costP2 * costT2 : ℚ) : ℝ) ≤ ((271970853 / 1000000000000 : ℚ) : ℝ) := by
      exact_mod_cast costL2_check
    push_cast at h
    have hL0 : targetLedger.L₀ = 271970853 / 1000000000000 := by norm_num [targetLedger]
    rw [hL0]
    exact h
  unfold TheoremC.firstStageCost
  calc Real.exp (∑ i, (fsP2 i * f1c2 i + fsP3 i * f1c3 i)) * tagSeries f1D f1V
      ≤ (expUpQ costP2 : ℝ) * (costT2 : ℝ) := mul_le_mul hP hT hT0 hE0
    _ ≤ targetLedger.L₀ := hL

end Sarkozy.AnalyticCells
