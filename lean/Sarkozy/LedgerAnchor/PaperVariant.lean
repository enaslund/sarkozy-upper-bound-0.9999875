module

public import Sarkozy.Comparison.Final
public import Sarkozy.LedgerAnchor.Numerics

@[expose] public section






open scoped Topology

namespace Sarkozy.LedgerAnchor

open Sarkozy.Certificates Sarkozy.Comparison

/-! ## Exponential certificates at the evaluation points `S⁺ + A⁺`, `S⁺ − A⁺`, `T⁺` -/

def paperExpSplusInterval : Interval := ⟨(1325146353108985748149879 / 500000000000000000000000),
    (2650292706217971496299759 / 1000000000000000000000000)⟩
def paperExpSplusWitness : ExpWitness := ⟨1, 28,
    (1325146353108985748149879 / 500000000000000000000000),
    (2650292706217971496299759 / 1000000000000000000000000)⟩

theorem paperExpSplusValid : paperExpSplusWitness.Valid
    (38986803563 / 40000000000) paperExpSplusInterval := by
  norm_num [ExpWitness.Valid, paperExpSplusWitness, paperExpSplusInterval, expSeries, expRemainder,
    Finset.sum_range_succ, Nat.factorial]

theorem paperExpSplusBounds : paperExpSplusInterval.Contains (Real.exp
    ((38986803563 / 40000000000) : ℝ)) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one] using
    ExpWitness.sound paperExpSplusValid

def paperExpSminusInterval : Interval := ⟨(384020925062424717269199 / 1000000000000000000000000),
    (960052312656061793173 / 2500000000000000000000)⟩
def paperExpSminusWitness : ExpWitness := ⟨1, 28,
    (384020925062424717269199 / 1000000000000000000000000),
    (960052312656061793173 / 2500000000000000000000)⟩

theorem paperExpSminusValid : paperExpSminusWitness.Valid
    (-957058235529 / 1000000000000) paperExpSminusInterval := by
  norm_num [ExpWitness.Valid, paperExpSminusWitness, paperExpSminusInterval, expSeries,
    expRemainder, Finset.sum_range_succ, Nat.factorial]

theorem paperExpSminusBounds : paperExpSminusInterval.Contains (Real.exp
    ((-957058235529 / 1000000000000) : ℝ)) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one] using
    ExpWitness.sound paperExpSminusValid

def paperExpTInterval : Interval := ⟨(454884825120865982897527 / 250000000000000000000000),
    (1819539300483463931590109 / 1000000000000000000000000)⟩
def paperExpTWitness : ExpWitness := ⟨1, 28,
    (454884825120865982897527 / 250000000000000000000000),
    (1819539300483463931590109 / 1000000000000000000000000)⟩

theorem paperExpTValid : paperExpTWitness.Valid
    (598583337443 / 1000000000000) paperExpTInterval := by
  norm_num [ExpWitness.Valid, paperExpTWitness, paperExpTInterval, expSeries, expRemainder,
    Finset.sum_range_succ, Nat.factorial]

theorem paperExpTBounds : paperExpTInterval.Contains (Real.exp
    ((598583337443 / 1000000000000) : ℝ)) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one] using
    ExpWitness.sound paperExpTValid

/-! ## The ledger at `a₀` -/

/-- **The primitive totals of the closing ledger at `a₀`**, with the paper's certificates
(R1, `out/author_a0.json`), rounded outward; with the nonnegativity of the totals that enter
multiplicatively, as in `PrimitiveLedger.Bounds`. -/
structure AnchorBoundsPaper (l : PrimitiveLedger) : Prop where
  B_nonneg : 0 ≤ l.B
  B_le : l.B ≤ 2.333773146847
  L₀_le : l.L₀ ≤ 0.000476049892
  S_nonneg : 0 ≤ l.S
  S_le : l.S ≤ 0.008805926773
  A_nonneg : 0 ≤ l.A
  A_le : l.A ≤ 0.965864162302
  T_le : l.T ≤ 0.598583337443
  D_ge : 0.467569676434 ≤ l.D
  m₁_ge : 1.529599479214 ≤ l.m₁
  R_I_nonneg : 0 ≤ l.R_I
  R_I_le : l.R_I ≤ 1.247518781991
  deltaAlpha_ge : 0.00758997189 ≤ l.deltaAlpha
  deltaMatching_ge : 0.012609201077 ≤ l.deltaMatching
  deltaOdd_ge : 0.006547928062 ≤ l.deltaOdd
  deltaEven_ge : 0.000738471869 ≤ l.deltaEven
  deltaUpper_ge : 0.000681478634 ≤ l.deltaUpper
  upperError_le : l.upperError ≤ 0.000000065513

/-- The cap: `Θ(a₀) < 0.94198`, margin `0.05802`. -/
noncomputable def closingCapPaper : ℝ := 0.94198

namespace AnchorBoundsPaper

variable {l : PrimitiveLedger}

/-- `e^S cosh A ≤ (e^{S⁺+A⁺} + e^{S⁺−A⁺})/2` at the upper bounds `S⁺, A⁺`. -/
theorem exp_mul_cosh_le {S A : ℝ} (hS : S ≤ 0.008805926773) (hA0 : 0 ≤ A)
    (hA : A ≤ 0.965864162302) :
    Real.exp S * Real.cosh A ≤
      ((paperExpSplusInterval.hi : ℝ) + paperExpSminusInterval.hi) / 2 := by
  have hcosh : Real.cosh A ≤ Real.cosh 0.965864162302 :=
    Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg hA0, abs_of_nonneg (by norm_num)]; exact hA)
  have h1 : Real.exp S * Real.cosh A ≤ Real.exp 0.008805926773 * Real.cosh 0.965864162302 :=
    mul_le_mul (Real.exp_le_exp.mpr hS) hcosh (Real.cosh_pos _).le (Real.exp_pos _).le
  have h2 : Real.exp 0.008805926773 * Real.cosh 0.965864162302 =
      (Real.exp ((((38986803563 / 40000000000) : ℚ)) : ℝ) + Real.exp
          ((((-957058235529 / 1000000000000) : ℚ)) : ℝ)) / 2 := by
    rw [Real.cosh_eq, mul_div_assoc', mul_add, ← Real.exp_add, ← Real.exp_add]
    congr 3 <;> norm_num
  have hp := paperExpSplusBounds.2
  have hm := paperExpSminusBounds.2
  rw [h2] at h1
  refine h1.trans ?_
  have hp' : Real.exp ((((38986803563 / 40000000000) : ℚ)) : ℝ) ≤
      (paperExpSplusInterval.hi : ℝ) := by
    simpa using hp
  have hm' : Real.exp ((((-957058235529 / 1000000000000) : ℚ)) : ℝ) ≤
      (paperExpSminusInterval.hi : ℝ) := by
    simpa using hm
  linarith

theorem E_le (h : AnchorBoundsPaper l) :
    l.E ≤ 2.333773146847 * (((paperExpSplusInterval.hi : ℝ) + paperExpSminusInterval.hi) / 2 - 1) -
      0.467569676434 := by
  have hx := exp_mul_cosh_le h.S_le h.A_nonneg h.A_le
  have hone : 1 ≤ Real.exp l.S * Real.cosh l.A := by
    have := Real.one_le_exp h.S_nonneg
    have := Real.one_le_cosh l.A
    nlinarith
  have hB := mul_le_mul h.B_le (sub_le_sub_right hx 1) (by linarith) (by norm_num)
  unfold PrimitiveLedger.E
  linarith [h.D_ge]

theorem J_le (h : AnchorBoundsPaper l) :
    l.J ≤ 2.333773146847 * (paperExpTInterval.hi : ℝ) * (1.247518781991 / 2) ^ 6 := by
  have heT : Real.exp l.T ≤ (paperExpTInterval.hi : ℝ) := by
    have hb := paperExpTBounds.2
    refine (Real.exp_le_exp.mpr h.T_le).trans (le_of_eq_of_le ?_ hb)
    congr 1
    norm_num
  have hR : (l.R_I / 2) ^ 6 ≤ (1.247518781991 / 2) ^ 6 :=
    pow_le_pow_left₀ (by linarith [h.R_I_nonneg]) (by linarith [h.R_I_le]) 6
  unfold PrimitiveLedger.J
  have h1 := mul_le_mul h.B_le heT (Real.exp_pos _).le (by norm_num)
  exact mul_le_mul h1 hR (pow_nonneg (by linarith [h.R_I_nonneg]) 6)
    (by simp only [paperExpTInterval]; norm_num)

theorem W_le (h : AnchorBoundsPaper l) :
    l.W ≤ 2.333773146847 * (paperExpSplusInterval.hi : ℝ) *
      ((1 + 1.247518781991 / 2 * (expWrapInterval.hi : ℝ)) ^ 6 - 1) := by
  have hSA : Real.exp (l.S + l.A) ≤ (paperExpSplusInterval.hi : ℝ) := by
    have hb := paperExpSplusBounds.2
    refine (Real.exp_le_exp.mpr (add_le_add h.S_le h.A_le)).trans (le_of_eq_of_le ?_ hb)
    congr 1
    norm_num
  have hw0 := PrimitiveLedger.wrapFactor_pos
  have hw := PrimitiveLedger.wrapFactor_le
  have hx0 : 0 ≤ l.R_I / 2 * PrimitiveLedger.wrapFactor :=
    mul_nonneg (by linarith [h.R_I_nonneg]) hw0.le
  have hx : l.R_I / 2 * PrimitiveLedger.wrapFactor ≤
      1.247518781991 / 2 * (expWrapInterval.hi : ℝ) :=
    mul_le_mul (by linarith [h.R_I_le]) hw hw0.le (by norm_num)
  have hpow : (1 + l.R_I / 2 * PrimitiveLedger.wrapFactor) ^ 6 - 1 ≤
      (1 + 1.247518781991 / 2 * (expWrapInterval.hi : ℝ)) ^ 6 - 1 :=
    sub_le_sub_right (pow_le_pow_left₀ (by linarith) (by linarith) 6) 1
  have hpow0 : 0 ≤ (1 + l.R_I / 2 * PrimitiveLedger.wrapFactor) ^ 6 - 1 := by
    have := one_le_pow₀ (n := 6) (show (1 : ℝ) ≤ 1 + l.R_I / 2 * PrimitiveLedger.wrapFactor by
      linarith)
    linarith
  unfold PrimitiveLedger.W
  have h1 := mul_le_mul h.B_le hSA (Real.exp_pos _).le (by norm_num)
  exact mul_le_mul h1 hpow hpow0 (by simp only [paperExpSplusInterval]; norm_num)

/-- **The closing number at `a₀` is below `0.94198`**, from the primitive bounds alone. All
transcendental evaluations are certified (`paperExp*`, `PrimitiveLedger.wrapFactor_le`). -/
theorem theta_lt_cap (h : AnchorBoundsPaper l) : l.theta < closingCapPaper := by
  have hE := E_le h
  have hJ := J_le h
  have hW := W_le h
  have hbound : (63 / 64 : ℝ) * (0.000476049892 + (2.333773146847 *
        (((paperExpSplusInterval.hi : ℝ) + paperExpSminusInterval.hi) / 2 - 1) - 0.467569676434)) +
      2.333773146847 * (paperExpTInterval.hi : ℝ) * (1.247518781991 / 2) ^ 6 +
      2.333773146847 * (paperExpSplusInterval.hi : ℝ) *
        ((1 + 1.247518781991 / 2 * (expWrapInterval.hi : ℝ)) ^ 6 - 1) +
      (1 - 1.529599479214) / 64 -
      (0.00758997189 + 0.012609201077 + 0.006547928062 + 0.000738471869) -
      0.000681478634 + 0.000000065513 < closingCapPaper := by
    simp only [paperExpSplusInterval, paperExpSminusInterval, paperExpTInterval,
      expWrapInterval, closingCapPaper]
    norm_num
  unfold PrimitiveLedger.theta
  linarith [h.L₀_le, h.m₁_ge, h.deltaAlpha_ge, h.deltaMatching_ge, h.deltaOdd_ge,
    h.deltaEven_ge, h.deltaUpper_ge, h.upperError_le]

theorem theta_lt_one (h : AnchorBoundsPaper l) : l.theta < 1 :=
  (theta_lt_cap h).trans (by norm_num [closingCapPaper])

/-- The closing number of `cor:joint-closing` with six queries and the ledger's joint constant
is below one at `a₀` (paper variant). -/
theorem jointTheta_lt_one (h : AnchorBoundsPaper l) :
    jointTheta 6 l.L₀ l.J l.W l.jointConstant < 1 := by
  rw [PrimitiveLedger.jointTheta_eq]
  exact theta_lt_one h

end AnchorBoundsPaper

end Sarkozy.LedgerAnchor
