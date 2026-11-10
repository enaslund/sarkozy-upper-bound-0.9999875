module

public import Sarkozy.MeanCredit2.Evaluation

@[expose] public section





open Finset

namespace Sarkozy.MeanCredit2

open Sarkozy.ClassData Sarkozy.MeanCredit

/-- The harness's `B` (upper end, rounded up). -/
def Bh : ℚ := 2016052216151308472944308654391 / 1000000000000000000000000000000
/-- The harness's `S` (upper end, rounded up). -/
def Sh : ℚ := 37554085173804775805363093431 / 1000000000000000000000000000000
/-- The harness's `A` (upper end, rounded up). -/
def Ah : ℚ := 812373239320786268050997728761 / 1000000000000000000000000000000
/-- The harness's 16 class discounts (lower end, rounded down). -/
def Dcls : ℚ := 264439290659953064774079292601 / 1000000000000000000000000000000
/-- The harness's variance credit (lower end, rounded down). -/
def Dvar : ℚ := 10266762707010917240523092359 / 1000000000000000000000000000000
/-- An upper bound for `e^{S+A}`. -/
def epHi : ℚ := 23394768230870894801060575578192319913317 / 10 ^ 40
/-- A lower bound for `e^{A−S}`. -/
def emLo : ℚ := 21701996200913563335239689773711109372642 / 10 ^ 40

theorem exp_SA_le : Real.exp ((Sh + Ah : ℚ) : ℝ) ≤ (epHi : ℝ) :=
  exp_le_of_ps (by norm_num [Sh, Ah]) (by norm_num [Sh, Ah]) (n := 40) (by norm_num)
    (by decide +kernel)

theorem exp_AS_ge : (emLo : ℝ) ≤ Real.exp ((Ah - Sh : ℚ) : ℝ) :=
  le_exp_of_ps (by norm_num [Sh, Ah]) (by norm_num [Sh, Ah]) (n := 40) (by norm_num)
    (by decide +kernel)

/-- **The harness's `𝓔` from its formula** (kernel exponentials):
`Bh(e^{Sh} cosh Ah − 1) − (Dcls + Dvar) ≤ 𝓔_h + 10⁻²⁸`. -/
theorem harnessE_formula :
    (Bh : ℝ) * (Real.exp Sh * Real.cosh Ah - 1) - (Dcls + Dvar) ≤ harnessE + 1 / 10 ^ 28 := by
  have h1 := exp_SA_le
  have h2 := exp_AS_ge
  have hpos : (0 : ℝ) < emLo := by norm_num [emLo]
  have e : Real.exp (Sh : ℝ) * Real.cosh Ah =
      (Real.exp ((Sh + Ah : ℚ) : ℝ) + (Real.exp ((Ah - Sh : ℚ) : ℝ))⁻¹) / 2 := by
    rw [Real.cosh_eq, ← Real.exp_neg]
    push_cast
    rw [mul_div_assoc', mul_add, ← Real.exp_add, ← Real.exp_add]
    congr 3
    ring
  have h3 : (Real.exp ((Ah - Sh : ℚ) : ℝ))⁻¹ ≤ (emLo : ℝ)⁻¹ := inv_anti₀ hpos h2
  rw [e]
  have hB : (0 : ℝ) ≤ Bh := by norm_num [Bh]
  have h4 : (Bh : ℝ) * ((Real.exp ((Sh + Ah : ℚ) : ℝ) + (Real.exp ((Ah - Sh : ℚ) : ℝ))⁻¹) / 2 - 1)
      ≤ (Bh : ℝ) * (((epHi : ℝ) + (emLo : ℝ)⁻¹) / 2 - 1) := by
    apply mul_le_mul_of_nonneg_left _ hB
    linarith
  have h5 : (Bh : ℝ) * (((epHi : ℝ) + (emLo : ℝ)⁻¹) / 2 - 1) - (Dcls + Dvar) ≤
      harnessE + 1 / 10 ^ 28 := by
    have : ((Bh * ((epHi + emLo⁻¹) / 2 - 1) - (Dcls + Dvar) : ℚ) : ℝ) ≤
        ((harnessE + 1 / 10 ^ 28 : ℚ) : ℝ) := by
      exact_mod_cast (show Bh * ((epHi + emLo⁻¹) / 2 - 1) - (Dcls + Dvar) ≤
        harnessE + 1 / 10 ^ 28 by decide +kernel)
    push_cast at this
    exact this
  linarith

variable {C : Type} [Fintype C]

/-- **The evaluation with the comparison split into its class-free part and the class savings**
(`eq:final-joint-closing`): `c = c_B − s` with the class-free completion `hB` and the savings
completion `S_v ≥ Dcls + Dvar` (`hS`, `hSv`). The class costs and the variance credit enter only
through `hS`, once each. -/
theorem seriesBound_split (cB s : (MLetter ⊕ C → ℕ) → ℝ) (X : MLetter ⊕ C → ℝ)
    (hX0 : ∀ l, 0 ≤ X l) (hXm : ∀ l, X (.inl l) = mTot xq 0 0 Vq (Uq - Vq) l)
    (hres : ∀ d, 0 ≤ 63 * (cB d - s d) - mLift d)
    (hB : HasSum (fun d => cB d * ∏ l, X l ^ d l / (d l).factorial)
      ((Bh : ℝ) * (Real.exp Sh * Real.cosh Ah - 1)))
    (Sv : ℝ) (hS : HasSum (fun d => s d * ∏ l, X l ^ d l / (d l).factorial) Sv)
    (hSv : ((Dcls + Dvar : ℚ) : ℝ) ≤ Sv) :
    SeriesBound (fun d => 63 * (cB d - s d) - mLift d) X
      (63 * (harnessE : ℝ) - 64 * (ledgerMid : ℝ) + (63 * (1 / 10 ^ 28) - 4 / 10 ^ 11)) := by
  have hC : HasSum (fun d => (cB d - s d) * ∏ l, X l ^ d l / (d l).factorial)
      ((Bh : ℝ) * (Real.exp Sh * Real.cosh Ah - 1) - Sv) := by
    have h := hB.sub hS
    convert h using 1
    funext d
    ring
  refine seriesBound_paper (fun d => cB d - s d) X hX0 hXm hres _ (1 / 10 ^ 28) hC ?_
  have h := harnessE_formula
  push_cast at hSv
  linarith

end Sarkozy.MeanCredit2
