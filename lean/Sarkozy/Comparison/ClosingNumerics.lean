module

public import Sarkozy.Certificates.Elementary
public import Sarkozy.RelativeErrors
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real






@[expose] public section

open scoped Topology

namespace Sarkozy.Comparison

open Sarkozy.Certificates

/-! ## Exponential certificates at the four evaluation points -/

def expSplusInterval : Interval := ⟨(675659141810494161097979 / 250000000000000000000000), (2702636567241976644391917 / 1000000000000000000000000)⟩
def expSplusWitness : ExpWitness := ⟨1, 28, (675659141810494161097979 / 250000000000000000000000), (2702636567241976644391917 / 1000000000000000000000000)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem expSplusValid : expSplusWitness.Valid (248556950731 / 250000000000) expSplusInterval := by
  norm_num [ExpWitness.Valid, expSplusWitness, expSplusInterval, expSeries, expRemainder,
    Finset.sum_range_succ, Nat.factorial]

theorem expSplusBounds : expSplusInterval.Contains (Real.exp ((248556950731 / 250000000000) : ℝ)) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one] using
    ExpWitness.sound expSplusValid

def expSminusInterval : Interval := ⟨(376715892870576480977593 / 1000000000000000000000000), (188357946435288240488797 / 500000000000000000000000)⟩
def expSminusWitness : ExpWitness := ⟨1, 28, (376715892870576480977593 / 1000000000000000000000000), (188357946435288240488797 / 500000000000000000000000)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem expSminusValid : expSminusWitness.Valid (-488131987723 / 500000000000) expSminusInterval := by
  norm_num [ExpWitness.Valid, expSminusWitness, expSminusInterval, expSeries, expRemainder,
    Finset.sum_range_succ, Nat.factorial]

theorem expSminusBounds : expSminusInterval.Contains (Real.exp ((-488131987723 / 500000000000) : ℝ)) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one] using
    ExpWitness.sound expSminusValid

def expTInterval : Interval := ⟨(920762585897889629891221 / 500000000000000000000000), (1841525171795779259782443 / 1000000000000000000000000)⟩
def expTWitness : ExpWitness := ⟨1, 28, (920762585897889629891221 / 500000000000000000000000), (1841525171795779259782443 / 1000000000000000000000000)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem expTValid : expTWitness.Valid (61059412599 / 100000000000) expTInterval := by
  norm_num [ExpWitness.Valid, expTWitness, expTInterval, expSeries, expRemainder,
    Finset.sum_range_succ, Nat.factorial]

theorem expTBounds : expTInterval.Contains (Real.exp ((61059412599 / 100000000000) : ℝ)) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one] using
    ExpWitness.sound expTValid

/-- The wrap factor's exponential at the baseline `ϑ = 1` (7 November 2026): the exponent is
`(−35/36) · log K` at the lower end of `logBlockInterval`. (At the upgraded `ϑ = 1014587/10⁶` the
exponent was `(−34985413/36000000) · log K`.) -/
def expWrapInterval : Interval := ⟨(1692604945028000497 / 1000000000000000000000000), (846302472514000249 / 500000000000000000000000)⟩
def expWrapWitness : ExpWitness := ⟨14, 28, (3870383252685103860809 / 10000000000000000000000), (387038325268510386080901 / 1000000000000000000000000)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem expWrapValid : expWrapWitness.Valid (-95682541162732600573 / 7200000000000000000) expWrapInterval := by
  norm_num [ExpWitness.Valid, expWrapWitness, expWrapInterval, expSeries, expRemainder,
    Finset.sum_range_succ, Nat.factorial]

theorem expWrapBounds : expWrapInterval.Contains (Real.exp ((-95682541162732600573 / 7200000000000000000) : ℝ)) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one] using
    ExpWitness.sound expWrapValid

/-! ## The primitive ledger -/

/-- Primitive totals of the final joint closing (`tab:four-routes-ledger`). -/
structure PrimitiveLedger where
  /-- Energy factor of the bracket dominating the first stage, (CP3). -/
  B : ℝ
  /-- Cost of the first stage, (CP2). -/
  L₀ : ℝ
  /-- Total symmetric price of the comparison change, (CP4). -/
  S : ℝ
  /-- Total skew price of the comparison change, (CP4). -/
  A : ℝ
  /-- Matching exponent of the dominators of the comparison law, (CP6). -/
  T : ℝ
  /-- Total certified savings subtracted in `E`. -/
  D : ℝ
  /-- Mean credit `m₁` of the joint closing. -/
  m₁ : ℝ
  /-- Conductor moment of one index. -/
  R_I : ℝ
  deltaAlpha : ℝ
  deltaMatching : ℝ
  deltaOdd : ℝ
  deltaEven : ℝ
  deltaUpper : ℝ
  upperError : ℝ

namespace PrimitiveLedger

variable (l : PrimitiveLedger)

/-- Dominated price of the comparison change, `E = B(e^S cosh A - 1) - D`. -/
noncomputable def E : ℝ := l.B * (Real.exp l.S * Real.cosh l.A - 1) - l.D

/-- Coupled index term, `J = B e^T (R_I/2)^6`. -/
noncomputable def J : ℝ := l.B * Real.exp l.T * (l.R_I / 2) ^ 6

/-- Wrapping factor `K^(-1+ϑ/36)` of the density induction, with `K = blockScale`. -/
noncomputable def wrapFactor : ℝ := (blockScale : ℝ) ^ (-1 + densityExponent / 36)

/-- Wrapping term, `W = B e^(S+A) [(1 + (R_I/2) K^(-1+ϑ/36))^6 - 1]`. -/
noncomputable def W : ℝ :=
  l.B * Real.exp (l.S + l.A) * ((1 + l.R_I / 2 * wrapFactor) ^ 6 - 1)

/-- The joint closing number `eq:final-joint-closing`. -/
noncomputable def theta : ℝ :=
  (63 / 64 : ℝ) * (l.L₀ + l.E) + l.J + l.W + (1 - l.m₁) / 64 -
    (l.deltaAlpha + l.deltaMatching + l.deltaOdd + l.deltaEven) -
    l.deltaUpper + l.upperError

/-- The outward-rounded primitive bounds of `tab:four-routes-ledger`, together with
the nonnegativity of the totals that enter multiplicatively (all are sums of
prices, or a moment of a positive random variable, in the paper). -/
structure Bounds : Prop where
  B_nonneg : 0 ≤ l.B
  B_le : l.B ≤ 2.373803797078
  L₀_le : l.L₀ ≤ 0.000507024733
  S_nonneg : 0 ≤ l.S
  S_le : l.S ≤ 0.008981913739
  A_nonneg : 0 ≤ l.A
  A_le : l.A ≤ 0.985245889185
  T_le : l.T ≤ 0.610594125990
  D_ge : 0.495667577473 ≤ l.D
  m₁_ge : 1.529526120248 ≤ l.m₁
  R_I_nonneg : 0 ≤ l.R_I
  R_I_le : l.R_I ≤ 1.252937308029
  deltaAlpha_ge : 0.007949257298 ≤ l.deltaAlpha
  deltaMatching_ge : 0.013289595166 ≤ l.deltaMatching
  deltaOdd_ge : 0.006920381923 ≤ l.deltaOdd
  deltaEven_ge : 0.000788314597 ≤ l.deltaEven
  deltaUpper_ge : 0.000716967431 ≤ l.deltaUpper
  upperError_le : l.upperError ≤ 0.000000070807

/-! ## Elementary enclosures -/

theorem wrapFactor_pos : 0 < wrapFactor :=
  Real.rpow_pos_of_pos (by norm_num [blockScale]) _

theorem wrapFactor_le : wrapFactor ≤ (expWrapInterval.hi : ℝ) := by
  have hK : (0 : ℝ) < (blockScale : ℝ) := by norm_num [blockScale]
  have hy : (-1 + densityExponent / 36 : ℝ) < 0 := by norm_num [densityExponent]
  have hlog := log_blockScale_bounds.1
  unfold wrapFactor
  rw [Real.rpow_def_of_pos hK]
  have hmul : Real.log (blockScale : ℝ) * (-1 + densityExponent / 36) ≤
      ((logBlockInterval.lo : ℚ) : ℝ) * (-1 + densityExponent / 36) :=
    mul_le_mul_of_nonpos_right hlog hy.le
  refine (Real.exp_le_exp.mpr hmul).trans ?_
  have hb := expWrapBounds.2
  have heq : ((logBlockInterval.lo : ℚ) : ℝ) * (-1 + densityExponent / 36) =
      (((-35 / 36 : ℚ) * (13668934451818942939 / 1000000000000000000 : ℚ) : ℚ) : ℝ) := by
    simp only [logBlockInterval, densityExponent]
    push_cast
    ring
  rw [heq]
  refine le_of_eq_of_le ?_ hb
  congr 1
  push_cast
  ring

/-- `e^S cosh A ≤ (e^(S⁺+A⁺) + e^(S⁺-A⁺))/2` at the ledger's upper bounds `S⁺, A⁺`. -/
theorem exp_mul_cosh_le {S A : ℝ} (hS : S ≤ 0.008981913739) (hA0 : 0 ≤ A)
    (hA : A ≤ 0.985245889185) :
    Real.exp S * Real.cosh A ≤ ((expSplusInterval.hi : ℝ) + expSminusInterval.hi) / 2 := by
  have hcosh : Real.cosh A ≤ Real.cosh 0.985245889185 :=
    Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg hA0, abs_of_nonneg (by norm_num)]; exact hA)
  have h1 : Real.exp S * Real.cosh A ≤ Real.exp 0.008981913739 * Real.cosh 0.985245889185 :=
    mul_le_mul (Real.exp_le_exp.mpr hS) hcosh (Real.cosh_pos _).le (Real.exp_pos _).le
  have h2 : Real.exp 0.008981913739 * Real.cosh 0.985245889185 =
      (Real.exp (((248556950731 / 250000000000 : ℚ)) : ℝ) +
        Real.exp (((-488131987723 / 500000000000 : ℚ)) : ℝ)) / 2 := by
    rw [Real.cosh_eq, mul_div_assoc', mul_add, ← Real.exp_add, ← Real.exp_add]
    congr 3 <;> norm_num
  have hp := expSplusBounds.2
  have hm := expSminusBounds.2
  rw [h2] at h1
  refine h1.trans ?_
  have hp' : Real.exp (((248556950731 / 250000000000 : ℚ)) : ℝ) ≤ (expSplusInterval.hi : ℝ) := by
    simpa using hp
  have hm' : Real.exp (((-488131987723 / 500000000000 : ℚ)) : ℝ) ≤ (expSminusInterval.hi : ℝ) := by
    simpa using hm
  linarith

theorem E_le (h : l.Bounds) :
    l.E ≤ 2.373803797078 * (((expSplusInterval.hi : ℝ) + expSminusInterval.hi) / 2 - 1) -
      0.495667577473 := by
  have hx := exp_mul_cosh_le h.S_le h.A_nonneg h.A_le
  have hone : 1 ≤ Real.exp l.S * Real.cosh l.A := by
    have := Real.one_le_exp h.S_nonneg
    have := Real.one_le_cosh l.A
    nlinarith
  have hB := mul_le_mul h.B_le (sub_le_sub_right hx 1) (by linarith) (by norm_num)
  unfold E
  linarith [h.D_ge]

theorem J_le (h : l.Bounds) :
    l.J ≤ 2.373803797078 * (expTInterval.hi : ℝ) * (1.252937308029 / 2) ^ 6 := by
  have heT : Real.exp l.T ≤ (expTInterval.hi : ℝ) := by
    have hb := expTBounds.2
    refine (Real.exp_le_exp.mpr h.T_le).trans (le_of_eq_of_le ?_ hb)
    congr 1
    norm_num
  have hR : (l.R_I / 2) ^ 6 ≤ (1.252937308029 / 2) ^ 6 :=
    pow_le_pow_left₀ (by linarith [h.R_I_nonneg]) (by linarith [h.R_I_le]) 6
  unfold J
  have h1 := mul_le_mul h.B_le heT (Real.exp_pos _).le (by norm_num)
  exact mul_le_mul h1 hR (pow_nonneg (by linarith [h.R_I_nonneg]) 6)
    (by simp only [expTInterval]; norm_num)

theorem W_le (h : l.Bounds) :
    l.W ≤ 2.373803797078 * (expSplusInterval.hi : ℝ) *
      ((1 + 1.252937308029 / 2 * (expWrapInterval.hi : ℝ)) ^ 6 - 1) := by
  have hSA : Real.exp (l.S + l.A) ≤ (expSplusInterval.hi : ℝ) := by
    have hb := expSplusBounds.2
    refine (Real.exp_le_exp.mpr (add_le_add h.S_le h.A_le)).trans (le_of_eq_of_le ?_ hb)
    congr 1
    norm_num
  have hw0 := wrapFactor_pos
  have hw := wrapFactor_le
  have hx0 : 0 ≤ l.R_I / 2 * wrapFactor := mul_nonneg (by linarith [h.R_I_nonneg]) hw0.le
  have hx : l.R_I / 2 * wrapFactor ≤ 1.252937308029 / 2 * (expWrapInterval.hi : ℝ) :=
    mul_le_mul (by linarith [h.R_I_le]) hw hw0.le (by norm_num)
  have hpow : (1 + l.R_I / 2 * wrapFactor) ^ 6 - 1 ≤
      (1 + 1.252937308029 / 2 * (expWrapInterval.hi : ℝ)) ^ 6 - 1 :=
    sub_le_sub_right (pow_le_pow_left₀ (by linarith) (by linarith) 6) 1
  have hpow0 : 0 ≤ (1 + l.R_I / 2 * wrapFactor) ^ 6 - 1 := by
    have := one_le_pow₀ (n := 6) (show (1 : ℝ) ≤ 1 + l.R_I / 2 * wrapFactor by linarith)
    linarith
  unfold W
  have h1 := mul_le_mul h.B_le hSA (Real.exp_pos _).le (by norm_num)
  exact mul_le_mul h1 hpow hpow0 (by simp only [expSplusInterval]; norm_num)

/-- The final joint closing number is below the paper's cap, from the primitive
bounds alone. All transcendental evaluations are certified in this file. -/
theorem theta_lt_cap (h : l.Bounds) : l.theta < closingCap := by
  have hE := l.E_le h
  have hJ := l.J_le h
  have hW := l.W_le h
  have hbound : (63 / 64 : ℝ) * (0.000507024733 + (2.373803797078 *
        (((expSplusInterval.hi : ℝ) + expSminusInterval.hi) / 2 - 1) - 0.495667577473)) +
      2.373803797078 * (expTInterval.hi : ℝ) * (1.252937308029 / 2) ^ 6 +
      2.373803797078 * (expSplusInterval.hi : ℝ) *
        ((1 + 1.252937308029 / 2 * (expWrapInterval.hi : ℝ)) ^ 6 - 1) +
      (1 - 1.529526120248) / 64 -
      (0.007949257298 + 0.013289595166 + 0.006920381923 + 0.000788314597) -
      0.000716967431 + 0.000000070807 < closingCap := by
    simp only [expSplusInterval, expSminusInterval, expTInterval, expWrapInterval, closingCap]
    norm_num
  unfold theta
  linarith [h.L₀_le, h.m₁_ge, h.deltaAlpha_ge, h.deltaMatching_ge, h.deltaOdd_ge,
    h.deltaEven_ge, h.deltaUpper_ge, h.upperError_le]

theorem theta_lt_one (h : l.Bounds) : l.theta < 1 :=
  (l.theta_lt_cap h).trans closingCap_lt_one

end PrimitiveLedger

/-- The existing raw-comparison endgame with the eleven composite ledger inputs
replaced by the primitive totals of `tab:four-routes-ledger`. -/
theorem powerSavingBound_of_rawComparison_primitive
    {l : PrimitiveLedger} (hledger : l.Bounds)
    {Y : ℕ → Finset ℤ → ℝ} {M E : ℝ} {q : ℕ → ℝ}
    (hM : 0 < M) (hE : 0 ≤ E)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (blockScale * L) A → density (blockScale * L) A ^ slots ≤ Y L A)
    (hglobal : GlobalMomentBound Y M) (hrec : RawComparison Y q E)
    (hq : Filter.Tendsto q Filter.atTop (𝓝 l.theta)) : PowerSavingBound :=
  powerSavingBound_of_scaledEnergyEstimate
    (scaledEnergyEstimate_of_rawComparison hM hE (l.theta_lt_one hledger)
      hreflection hglobal hrec hq)

end Sarkozy.Comparison
