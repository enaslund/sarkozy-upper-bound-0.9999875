module

public import Sarkozy.ClassData.JointGate

@[expose] public section





open Finset

namespace Sarkozy.ClassData

open Sarkozy.ClassBoundsPaper Sarkozy.Certificates Sarkozy.TargetLedger
open Sarkozy.TheoremC Sarkozy.TheoremCBlock

/-- The harness's `𝓔 = B(e^S cosh A − 1) − D` at RB's point at `a_G` (upper end, rounded up). -/
def harnessE : ℚ := 531980879396602080563481603191 / 1000000000000000000000000000000

/-- The harness's `Δ_α + Δ_M + Δ_O + Δ_K + Δ_u − R_u` at RB's point at `a_G` (lower ends; `R_u`
upper end; rounded down). -/
def harnessDelta : ℚ := 971775530876326143244040873 / 50000000000000000000000000000

/-- **`𝓔` of the ledger from below**, with the ledger's exponential certificates. -/
theorem targetLedger_E_ge :
    2.016052216152 * (((targetExpSplusInterval.lo : ℝ) + targetExpSminusInterval.lo) / 2 - 1) -
      0.274706053366 ≤ targetLedger.E := by
  have h2 : Real.exp 0.037554085174 * Real.cosh 0.834373239321 =
      (Real.exp ((((174385464899 / 200000000000) : ℚ)) : ℝ) + Real.exp
          ((((-796819154147 / 1000000000000) : ℚ)) : ℝ)) / 2 := by
    rw [Real.cosh_eq, mul_div_assoc', mul_add, ← Real.exp_add, ← Real.exp_add]
    congr 3 <;> norm_num
  have hp' : (targetExpSplusInterval.lo : ℝ) ≤
      Real.exp ((((174385464899 / 200000000000) : ℚ)) : ℝ) := by
    simpa using targetExpSplusBounds.1
  have hm' : (targetExpSminusInterval.lo : ℝ) ≤
      Real.exp ((((-796819154147 / 1000000000000) : ℚ)) : ℝ) := by
    simpa using targetExpSminusBounds.1
  have e : targetLedger.E = 2.016052216152 *
      (Real.exp 0.037554085174 * Real.cosh 0.834373239321 - 1) - 0.274706053366 := rfl
  rw [e, h2]
  linarith

/-- **The ledger's room for the joint gate**: `63 𝓔_h − 64 Δ_h + 3.7·10⁻¹⁰ ≤ 63 𝓔 − 64 Δ` (at
RB's package R the untrusted value is about `2.668`, almost all from the deliberate slack `0.022`
on the ledger's `A`; at E3's v2 ledger it was `0.32302`). -/
theorem ledger_room :
    63 * (harnessE : ℝ) - 64 * (harnessDelta : ℝ) + 37 / 100000000000 ≤
      63 * targetLedger.E - ledgerDelta targetLedger := by
  have h := targetLedger_E_ge
  have hd : ledgerDelta targetLedger = 64 * ((0.004914747146 + 0.007740956387 + 0.003927490486 +
      0.000405557461) + 0.002446945672 - 0.000000186538) := rfl
  rw [hd]
  norm_num [targetExpSplusInterval, targetExpSminusInterval, harnessE, harnessDelta] at h ⊢
  linarith

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **`AllocJ` from the completed residual series at the harness values** (`prop:joint-middle-mean`,
`prop:joint-upper-mean`, `eq:final-joint-closing`): if at every scale
`63 (κ_L + ∑_j w_j u_j) − ∑_j b_j u_j ≤ 63 𝓔_h − 64 Δ_h`, then `AllocJ` holds, with room
`3.7·10⁻¹⁰` (`ledger_room`). -/
theorem allocJ_of_completed {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {CI : ClassInputs D.CL} (CE : ClassEnergyInputs D CI) (b : ∀ L, CE.Θ L → ℝ)
    (hc : ∀ L, 63 * (CE.κ L + ∑ j, CE.w L j * CE.u L j) - ∑ j, b L j * CE.u L j ≤
      63 * (harnessE : ℝ) - 64 * (harnessDelta : ℝ)) : AllocJ CE b := fun L => by
  have h1 := ledger_room
  have h2 := hc L
  linarith

end Sarkozy.ClassData
