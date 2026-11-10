module

public import Sarkozy.Comparison.Final
public import Sarkozy.Certificates.Elementary

@[expose] public section






open scoped Topology

namespace Sarkozy.LedgerAnchor

open Sarkozy.Certificates Sarkozy.Comparison

/-! ## Exponential certificates at the evaluation points `S⁺ + A⁺`, `S⁺ − A⁺`, `T⁺` -/

def anchorExpSplusInterval : Interval := ⟨(53260111727997419244087 / 20000000000000000000000),
    (2663005586399870962204351 / 1000000000000000000000000)⟩
def anchorExpSplusWitness : ExpWitness := ⟨1, 28,
    (53260111727997419244087 / 20000000000000000000000),
    (2663005586399870962204351 / 1000000000000000000000000)⟩

theorem anchorExpSplusValid : anchorExpSplusWitness.Valid
    (489727702307 / 500000000000) anchorExpSplusInterval := by
  norm_num [ExpWitness.Valid, anchorExpSplusWitness, anchorExpSplusInterval, expSeries,
    expRemainder, Finset.sum_range_succ, Nat.factorial]

theorem anchorExpSplusBounds : anchorExpSplusInterval.Contains (Real.exp
    ((489727702307 / 500000000000) : ℝ)) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one] using
    ExpWitness.sound anchorExpSplusValid

def anchorExpSminusInterval : Interval := ⟨(191988100324433928269161 / 500000000000000000000000),
    (383976200648867856538323 / 1000000000000000000000000)⟩
def anchorExpSminusWitness : ExpWitness := ⟨1, 28,
    (191988100324433928269161 / 500000000000000000000000),
    (383976200648867856538323 / 1000000000000000000000000)⟩

theorem anchorExpSminusValid : anchorExpSminusWitness.Valid
    (-7477927389 / 7812500000) anchorExpSminusInterval := by
  norm_num [ExpWitness.Valid, anchorExpSminusWitness, anchorExpSminusInterval, expSeries,
    expRemainder, Finset.sum_range_succ, Nat.factorial]

theorem anchorExpSminusBounds : anchorExpSminusInterval.Contains (Real.exp
    ((-7477927389 / 7812500000) : ℝ)) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one] using
    ExpWitness.sound anchorExpSminusValid

def anchorExpTInterval : Interval := ⟨(114218813198417288253771 / 62500000000000000000000),
    (1827501011174676612060337 / 1000000000000000000000000)⟩
def anchorExpTWitness : ExpWitness := ⟨1, 28,
    (114218813198417288253771 / 62500000000000000000000),
    (1827501011174676612060337 / 1000000000000000000000000)⟩

theorem anchorExpTValid : anchorExpTWitness.Valid
    (18842170811 / 31250000000) anchorExpTInterval := by
  norm_num [ExpWitness.Valid, anchorExpTWitness, anchorExpTInterval, expSeries, expRemainder,
    Finset.sum_range_succ, Nat.factorial]

theorem anchorExpTBounds : anchorExpTInterval.Contains (Real.exp
    ((18842170811 / 31250000000) : ℝ)) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one] using
    ExpWitness.sound anchorExpTValid

/-! ## The ledger at `a₀` -/

/-- **The primitive totals of the closing ledger at `a₀`**, formalization-friendly variant
(R1, point `F1+F2+F4dropped`), rounded outward; with the nonnegativity of the totals that enter
multiplicatively, as in `PrimitiveLedger.Bounds`. -/
structure AnchorBounds (l : PrimitiveLedger) : Prop where
  B_nonneg : 0 ≤ l.B
  B_le : l.B ≤ 2.336116464034
  L₀_le : l.L₀ ≤ 0.00047996208
  S_nonneg : 0 ≤ l.S
  S_le : l.S ≤ 0.011140349411
  A_nonneg : 0 ≤ l.A
  A_le : l.A ≤ 0.968315055203
  T_le : l.T ≤ 0.602949465952
  D_ge : 0.469121104481 ≤ l.D
  m₁_ge : 1.529229285152 ≤ l.m₁
  R_I_nonneg : 0 ≤ l.R_I
  R_I_le : l.R_I ≤ 1.248422835484
  deltaAlpha_ge : 0.007609899014 ≤ l.deltaAlpha
  deltaMatching_ge : 0.012646953992 ≤ l.deltaMatching
  deltaOdd_ge : 0.006568610064 ≤ l.deltaOdd
  deltaEven_ge : 0.000741210604 ≤ l.deltaEven
  deltaUpper_ge : 0.000900869447 ≤ l.deltaUpper
  upperError_le : l.upperError ≤ 0.000000087723

/-- The cap: `Θ(a₀) < 0.95836`, margin `0.04164`. -/
noncomputable def closingCapAnchor : ℝ := 0.95836

namespace AnchorBounds

variable {l : PrimitiveLedger}

/-- `e^S cosh A ≤ (e^{S⁺+A⁺} + e^{S⁺−A⁺})/2` at the upper bounds `S⁺, A⁺`. -/
theorem exp_mul_cosh_le {S A : ℝ} (hS : S ≤ 0.011140349411) (hA0 : 0 ≤ A)
    (hA : A ≤ 0.968315055203) :
    Real.exp S * Real.cosh A ≤
      ((anchorExpSplusInterval.hi : ℝ) + anchorExpSminusInterval.hi) / 2 := by
  have hcosh : Real.cosh A ≤ Real.cosh 0.968315055203 :=
    Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg hA0, abs_of_nonneg (by norm_num)]; exact hA)
  have h1 : Real.exp S * Real.cosh A ≤ Real.exp 0.011140349411 * Real.cosh 0.968315055203 :=
    mul_le_mul (Real.exp_le_exp.mpr hS) hcosh (Real.cosh_pos _).le (Real.exp_pos _).le
  have h2 : Real.exp 0.011140349411 * Real.cosh 0.968315055203 =
      (Real.exp ((((489727702307 / 500000000000) : ℚ)) : ℝ) + Real.exp
          ((((-7477927389 / 7812500000) : ℚ)) : ℝ)) / 2 := by
    rw [Real.cosh_eq, mul_div_assoc', mul_add, ← Real.exp_add, ← Real.exp_add]
    congr 3 <;> norm_num
  have hp := anchorExpSplusBounds.2
  have hm := anchorExpSminusBounds.2
  rw [h2] at h1
  refine h1.trans ?_
  have hp' : Real.exp ((((489727702307 / 500000000000) : ℚ)) : ℝ) ≤
      (anchorExpSplusInterval.hi : ℝ) := by
    simpa using hp
  have hm' : Real.exp ((((-7477927389 / 7812500000) : ℚ)) : ℝ) ≤
      (anchorExpSminusInterval.hi : ℝ) := by
    simpa using hm
  linarith

theorem E_le (h : AnchorBounds l) :
    l.E ≤ 2.336116464034 *
        (((anchorExpSplusInterval.hi : ℝ) + anchorExpSminusInterval.hi) / 2 - 1) -
      0.469121104481 := by
  have hx := exp_mul_cosh_le h.S_le h.A_nonneg h.A_le
  have hone : 1 ≤ Real.exp l.S * Real.cosh l.A := by
    have := Real.one_le_exp h.S_nonneg
    have := Real.one_le_cosh l.A
    nlinarith
  have hB := mul_le_mul h.B_le (sub_le_sub_right hx 1) (by linarith) (by norm_num)
  unfold PrimitiveLedger.E
  linarith [h.D_ge]

theorem J_le (h : AnchorBounds l) :
    l.J ≤ 2.336116464034 * (anchorExpTInterval.hi : ℝ) * (1.248422835484 / 2) ^ 6 := by
  have heT : Real.exp l.T ≤ (anchorExpTInterval.hi : ℝ) := by
    have hb := anchorExpTBounds.2
    refine (Real.exp_le_exp.mpr h.T_le).trans (le_of_eq_of_le ?_ hb)
    congr 1
    norm_num
  have hR : (l.R_I / 2) ^ 6 ≤ (1.248422835484 / 2) ^ 6 :=
    pow_le_pow_left₀ (by linarith [h.R_I_nonneg]) (by linarith [h.R_I_le]) 6
  unfold PrimitiveLedger.J
  have h1 := mul_le_mul h.B_le heT (Real.exp_pos _).le (by norm_num)
  exact mul_le_mul h1 hR (pow_nonneg (by linarith [h.R_I_nonneg]) 6)
    (by simp only [anchorExpTInterval]; norm_num)

theorem W_le (h : AnchorBounds l) :
    l.W ≤ 2.336116464034 * (anchorExpSplusInterval.hi : ℝ) *
      ((1 + 1.248422835484 / 2 * (expWrapInterval.hi : ℝ)) ^ 6 - 1) := by
  have hSA : Real.exp (l.S + l.A) ≤ (anchorExpSplusInterval.hi : ℝ) := by
    have hb := anchorExpSplusBounds.2
    refine (Real.exp_le_exp.mpr (add_le_add h.S_le h.A_le)).trans (le_of_eq_of_le ?_ hb)
    congr 1
    norm_num
  have hw0 := PrimitiveLedger.wrapFactor_pos
  have hw := PrimitiveLedger.wrapFactor_le
  have hx0 : 0 ≤ l.R_I / 2 * PrimitiveLedger.wrapFactor :=
    mul_nonneg (by linarith [h.R_I_nonneg]) hw0.le
  have hx : l.R_I / 2 * PrimitiveLedger.wrapFactor ≤
      1.248422835484 / 2 * (expWrapInterval.hi : ℝ) :=
    mul_le_mul (by linarith [h.R_I_le]) hw hw0.le (by norm_num)
  have hpow : (1 + l.R_I / 2 * PrimitiveLedger.wrapFactor) ^ 6 - 1 ≤
      (1 + 1.248422835484 / 2 * (expWrapInterval.hi : ℝ)) ^ 6 - 1 :=
    sub_le_sub_right (pow_le_pow_left₀ (by linarith) (by linarith) 6) 1
  have hpow0 : 0 ≤ (1 + l.R_I / 2 * PrimitiveLedger.wrapFactor) ^ 6 - 1 := by
    have := one_le_pow₀ (n := 6) (show (1 : ℝ) ≤ 1 + l.R_I / 2 * PrimitiveLedger.wrapFactor by
      linarith)
    linarith
  unfold PrimitiveLedger.W
  have h1 := mul_le_mul h.B_le hSA (Real.exp_pos _).le (by norm_num)
  exact mul_le_mul h1 hpow hpow0 (by simp only [anchorExpSplusInterval]; norm_num)

/-- **The closing number at `a₀` is below `0.95836`**, from the primitive bounds alone. All
transcendental evaluations are certified (`anchorExp*`, `PrimitiveLedger.wrapFactor_le`). -/
theorem theta_lt_cap (h : AnchorBounds l) : l.theta < closingCapAnchor := by
  have hE := E_le h
  have hJ := J_le h
  have hW := W_le h
  have hbound : (63 / 64 : ℝ) * (0.00047996208 + (2.336116464034 *
        (((anchorExpSplusInterval.hi : ℝ) +
            anchorExpSminusInterval.hi) / 2 - 1) - 0.469121104481)) +
      2.336116464034 * (anchorExpTInterval.hi : ℝ) * (1.248422835484 / 2) ^ 6 +
      2.336116464034 * (anchorExpSplusInterval.hi : ℝ) *
        ((1 + 1.248422835484 / 2 * (expWrapInterval.hi : ℝ)) ^ 6 - 1) +
      (1 - 1.529229285152) / 64 -
      (0.007609899014 + 0.012646953992 + 0.006568610064 + 0.000741210604) -
      0.000900869447 + 0.000000087723 < closingCapAnchor := by
    simp only [anchorExpSplusInterval, anchorExpSminusInterval, anchorExpTInterval,
      expWrapInterval, closingCapAnchor]
    norm_num
  unfold PrimitiveLedger.theta
  linarith [h.L₀_le, h.m₁_ge, h.deltaAlpha_ge, h.deltaMatching_ge, h.deltaOdd_ge,
    h.deltaEven_ge, h.deltaUpper_ge, h.upperError_le]

theorem theta_lt_one (h : AnchorBounds l) : l.theta < 1 :=
  (theta_lt_cap h).trans (by norm_num [closingCapAnchor])

/-- The closing number of `cor:joint-closing` with six queries and the ledger's joint constant
is below one at `a₀`. -/
theorem jointTheta_lt_one (h : AnchorBounds l) :
    jointTheta 6 l.L₀ l.J l.W l.jointConstant < 1 := by
  rw [PrimitiveLedger.jointTheta_eq]
  exact theta_lt_one h

end AnchorBounds

end Sarkozy.LedgerAnchor
