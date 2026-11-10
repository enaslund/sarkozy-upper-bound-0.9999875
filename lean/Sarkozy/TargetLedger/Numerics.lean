module

public import Sarkozy.Comparison.Final
public import Sarkozy.Certificates.Elementary

@[expose] public section






open scoped Topology

namespace Sarkozy.TargetLedger

open Sarkozy.Certificates Sarkozy.Comparison

/-! ## Exponential certificates at the evaluation points `S⁺ + A⁺`, `S⁺ − A⁺`, `T⁺` -/

def targetExpSplusInterval : Interval := ⟨(239151564131440228425611 / 100000000000000000000000),
    (2391515641314402284256111 / 1000000000000000000000000)⟩
def targetExpSplusWitness : ExpWitness := ⟨1, 28,
    (239151564131440228425611 / 100000000000000000000000),
    (2391515641314402284256111 / 1000000000000000000000000)⟩

theorem targetExpSplusValid : targetExpSplusWitness.Valid
    (174385464899 / 200000000000) targetExpSplusInterval := by
  norm_num [ExpWitness.Valid, targetExpSplusWitness, targetExpSplusInterval, expSeries,
    expRemainder, Finset.sum_range_succ, Nat.factorial]

theorem targetExpSplusBounds : targetExpSplusInterval.Contains (Real.exp
    ((174385464899 / 200000000000) : ℝ)) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one] using
    ExpWitness.sound targetExpSplusValid

def targetExpSminusInterval : Interval := ⟨(90152097161459471169767 / 200000000000000000000000),
    (112690121451824338962209 / 250000000000000000000000)⟩
def targetExpSminusWitness : ExpWitness := ⟨1, 28,
    (90152097161459471169767 / 200000000000000000000000),
    (112690121451824338962209 / 250000000000000000000000)⟩

theorem targetExpSminusValid : targetExpSminusWitness.Valid
    (-796819154147 / 1000000000000) targetExpSminusInterval := by
  norm_num [ExpWitness.Valid, targetExpSminusWitness, targetExpSminusInterval, expSeries,
    expRemainder, Finset.sum_range_succ, Nat.factorial]

theorem targetExpSminusBounds : targetExpSminusInterval.Contains (Real.exp
    ((-796819154147 / 1000000000000) : ℝ)) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one] using
    ExpWitness.sound targetExpSminusValid

def targetExpTInterval : Interval := ⟨(428488027357671873157979 / 250000000000000000000000),
    (1713952109430687492631917 / 1000000000000000000000000)⟩
def targetExpTWitness : ExpWitness := ⟨1, 28,
    (428488027357671873157979 / 250000000000000000000000),
    (1713952109430687492631917 / 1000000000000000000000000)⟩

theorem targetExpTValid : targetExpTWitness.Valid
    (538801878963 / 1000000000000) targetExpTInterval := by
  norm_num [ExpWitness.Valid, targetExpTWitness, targetExpTInterval, expSeries, expRemainder,
    Finset.sum_range_succ, Nat.factorial]

theorem targetExpTBounds : targetExpTInterval.Contains (Real.exp
    ((538801878963 / 1000000000000) : ℝ)) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one] using
    ExpWitness.sound targetExpTValid

/-! ## The ledger at `a_G` -/

/-- **The primitive totals of the closing ledger at `a_G`** (`tab:four-routes-ledger`,
`cert:four-routes-closing`), in the configuration of this file (F1/F2/F4 replaced, paper objects
only, H2″ = `ThetaSmallRR`, R2's F3, R4's far bands), rounded outward; with the nonnegativity of
the totals that enter multiplicatively, as in `PrimitiveLedger.Bounds`. Each entry is a Part V
certificate at `a_G` (*open*). -/
structure TargetBounds (l : PrimitiveLedger) : Prop where
  B_nonneg : 0 ≤ l.B
  B_le : l.B ≤ 2.016052216152
  L₀_le : l.L₀ ≤ 0.000271970853
  S_nonneg : 0 ≤ l.S
  S_le : l.S ≤ 0.037554085174
  A_nonneg : 0 ≤ l.A
  A_le : l.A ≤ 0.834373239321
  T_le : l.T ≤ 0.538801878963
  D_ge : 0.274706053366 ≤ l.D
  m₁_ge : 0 ≤ l.m₁
  R_I_nonneg : 0 ≤ l.R_I
  R_I_le : l.R_I ≤ 1.193909842518
  deltaAlpha_ge : 0.004914747146 ≤ l.deltaAlpha
  deltaMatching_ge : 0.007740956387 ≤ l.deltaMatching
  deltaOdd_ge : 0.003927490486 ≤ l.deltaOdd
  deltaEven_ge : 0.000405557461 ≤ l.deltaEven
  deltaUpper_ge : 0.002446945672 ≤ l.deltaUpper
  upperError_le : l.upperError ≤ 0.000000186538

/-- The cap: `Θ(a_G) < 0.72`, margin `0.0018` (RB's package R with `m₁ = 0`:
`Θ ≤ 0.718211450512`; it was `0.7` with the harness's `m₁`). -/
noncomputable def closingCapTarget : ℝ := 0.72

namespace TargetBounds

variable {l : PrimitiveLedger}

/-- `e^S cosh A ≤ (e^{S⁺+A⁺} + e^{S⁺−A⁺})/2` at the upper bounds `S⁺, A⁺`. -/
theorem exp_mul_cosh_le {S A : ℝ} (hS : S ≤ 0.037554085174) (hA0 : 0 ≤ A)
    (hA : A ≤ 0.834373239321) :
    Real.exp S * Real.cosh A ≤
      ((targetExpSplusInterval.hi : ℝ) + targetExpSminusInterval.hi) / 2 := by
  have hcosh : Real.cosh A ≤ Real.cosh 0.834373239321 :=
    Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg hA0, abs_of_nonneg (by norm_num)]; exact hA)
  have h1 : Real.exp S * Real.cosh A ≤ Real.exp 0.037554085174 * Real.cosh 0.834373239321 :=
    mul_le_mul (Real.exp_le_exp.mpr hS) hcosh (Real.cosh_pos _).le (Real.exp_pos _).le
  have h2 : Real.exp 0.037554085174 * Real.cosh 0.834373239321 =
      (Real.exp ((((174385464899 / 200000000000) : ℚ)) : ℝ) + Real.exp
          ((((-796819154147 / 1000000000000) : ℚ)) : ℝ)) / 2 := by
    rw [Real.cosh_eq, mul_div_assoc', mul_add, ← Real.exp_add, ← Real.exp_add]
    congr 3 <;> norm_num
  have hp := targetExpSplusBounds.2
  have hm := targetExpSminusBounds.2
  rw [h2] at h1
  refine h1.trans ?_
  have hp' : Real.exp ((((174385464899 / 200000000000) : ℚ)) : ℝ) ≤
      (targetExpSplusInterval.hi : ℝ) := by
    simpa using hp
  have hm' : Real.exp ((((-796819154147 / 1000000000000) : ℚ)) : ℝ) ≤
      (targetExpSminusInterval.hi : ℝ) := by
    simpa using hm
  linarith

theorem E_le (h : TargetBounds l) :
    l.E ≤ 2.016052216152 *
        (((targetExpSplusInterval.hi : ℝ) + targetExpSminusInterval.hi) / 2 - 1) -
      0.274706053366 := by
  have hx := exp_mul_cosh_le h.S_le h.A_nonneg h.A_le
  have hone : 1 ≤ Real.exp l.S * Real.cosh l.A := by
    have := Real.one_le_exp h.S_nonneg
    have := Real.one_le_cosh l.A
    nlinarith
  have hB := mul_le_mul h.B_le (sub_le_sub_right hx 1) (by linarith) (by norm_num)
  unfold PrimitiveLedger.E
  linarith [h.D_ge]

theorem J_le (h : TargetBounds l) :
    l.J ≤ 2.016052216152 * (targetExpTInterval.hi : ℝ) * (1.193909842518 / 2) ^ 6 := by
  have heT : Real.exp l.T ≤ (targetExpTInterval.hi : ℝ) := by
    have hb := targetExpTBounds.2
    refine (Real.exp_le_exp.mpr h.T_le).trans (le_of_eq_of_le ?_ hb)
    congr 1
    norm_num
  have hR : (l.R_I / 2) ^ 6 ≤ (1.193909842518 / 2) ^ 6 :=
    pow_le_pow_left₀ (by linarith [h.R_I_nonneg]) (by linarith [h.R_I_le]) 6
  unfold PrimitiveLedger.J
  have h1 := mul_le_mul h.B_le heT (Real.exp_pos _).le (by norm_num)
  exact mul_le_mul h1 hR (pow_nonneg (by linarith [h.R_I_nonneg]) 6)
    (by simp only [targetExpTInterval]; norm_num)

theorem W_le (h : TargetBounds l) :
    l.W ≤ 2.016052216152 * (targetExpSplusInterval.hi : ℝ) *
      ((1 + 1.193909842518 / 2 * (expWrapInterval.hi : ℝ)) ^ 6 - 1) := by
  have hSA : Real.exp (l.S + l.A) ≤ (targetExpSplusInterval.hi : ℝ) := by
    have hb := targetExpSplusBounds.2
    refine (Real.exp_le_exp.mpr (add_le_add h.S_le h.A_le)).trans (le_of_eq_of_le ?_ hb)
    congr 1
    norm_num
  have hw0 := PrimitiveLedger.wrapFactor_pos
  have hw := PrimitiveLedger.wrapFactor_le
  have hx0 : 0 ≤ l.R_I / 2 * PrimitiveLedger.wrapFactor :=
    mul_nonneg (by linarith [h.R_I_nonneg]) hw0.le
  have hx : l.R_I / 2 * PrimitiveLedger.wrapFactor ≤
      1.193909842518 / 2 * (expWrapInterval.hi : ℝ) :=
    mul_le_mul (by linarith [h.R_I_le]) hw hw0.le (by norm_num)
  have hpow : (1 + l.R_I / 2 * PrimitiveLedger.wrapFactor) ^ 6 - 1 ≤
      (1 + 1.193909842518 / 2 * (expWrapInterval.hi : ℝ)) ^ 6 - 1 :=
    sub_le_sub_right (pow_le_pow_left₀ (by linarith) (by linarith) 6) 1
  have hpow0 : 0 ≤ (1 + l.R_I / 2 * PrimitiveLedger.wrapFactor) ^ 6 - 1 := by
    have := one_le_pow₀ (n := 6) (show (1 : ℝ) ≤ 1 + l.R_I / 2 * PrimitiveLedger.wrapFactor by
      linarith)
    linarith
  unfold PrimitiveLedger.W
  have h1 := mul_le_mul h.B_le hSA (Real.exp_pos _).le (by norm_num)
  exact mul_le_mul h1 hpow hpow0 (by simp only [targetExpSplusInterval]; norm_num)

/-- **The closing number at `a_G` is below `0.72`**, from the primitive bounds alone. All
transcendental evaluations are certified (`targetExp*`, `PrimitiveLedger.wrapFactor_le`); the
final comparison is exact rational arithmetic checked by `norm_num`. -/
theorem theta_lt_cap (h : TargetBounds l) : l.theta < closingCapTarget := by
  have hE := E_le h
  have hJ := J_le h
  have hW := W_le h
  have hbound : (63 / 64 : ℝ) * (0.000271970853 + (2.016052216152 *
        (((targetExpSplusInterval.hi : ℝ) +
            targetExpSminusInterval.hi) / 2 - 1) - 0.274706053366)) +
      2.016052216152 * (targetExpTInterval.hi : ℝ) * (1.193909842518 / 2) ^ 6 +
      2.016052216152 * (targetExpSplusInterval.hi : ℝ) *
        ((1 + 1.193909842518 / 2 * (expWrapInterval.hi : ℝ)) ^ 6 - 1) +
      (1 - 0) / 64 -
      (0.004914747146 + 0.007740956387 + 0.003927490486 + 0.000405557461) -
      0.002446945672 + 0.000000186538 < closingCapTarget := by
    simp only [targetExpSplusInterval, targetExpSminusInterval, targetExpTInterval,
      expWrapInterval, closingCapTarget]
    norm_num
  unfold PrimitiveLedger.theta
  linarith [h.L₀_le, h.m₁_ge, h.deltaAlpha_ge, h.deltaMatching_ge, h.deltaOdd_ge,
    h.deltaEven_ge, h.deltaUpper_ge, h.upperError_le]

/-- **`Θ(a_G) < 1`** from the ledger bounds. -/
theorem theta_lt_one (h : TargetBounds l) : l.theta < 1 :=
  (theta_lt_cap h).trans (by norm_num [closingCapTarget])

/-- The closing number of `cor:joint-closing` with six queries and the ledger's joint constant
is below one at `a_G`. -/
theorem jointTheta_lt_one (h : TargetBounds l) :
    jointTheta 6 l.L₀ l.J l.W l.jointConstant < 1 := by
  rw [PrimitiveLedger.jointTheta_eq]
  exact theta_lt_one h

end TargetBounds

/-! ## The ledger itself, and its non-vacuity -/

/-- **The ledger at `a_G`**, entries at their rounded bounds (`TargetBounds`). -/
noncomputable def targetLedger : PrimitiveLedger :=
  ⟨2.016052216152, 0.000271970853, 0.037554085174, 0.834373239321, 0.538801878963, 0.274706053366,
      0, 1.193909842518, 0.004914747146, 0.007740956387, 0.003927490486,
      0.000405557461, 0.002446945672, 0.000000186538⟩

/-- The rounded entries satisfy their own bounds: `TargetBounds` is consistent. -/
theorem targetLedger_bounds : TargetBounds targetLedger := by
  constructor <;> norm_num [targetLedger]

/-- **The closing number of the target ledger is below `0.72`** (kernel-checked). -/
theorem targetLedger_theta_lt : targetLedger.theta < closingCapTarget :=
  targetLedger_bounds.theta_lt_cap

/-- **`Θ < 1` at `a_G`** for the target ledger. -/
theorem targetLedger_theta_lt_one : targetLedger.theta < 1 :=
  targetLedger_bounds.theta_lt_one

end Sarkozy.TargetLedger
