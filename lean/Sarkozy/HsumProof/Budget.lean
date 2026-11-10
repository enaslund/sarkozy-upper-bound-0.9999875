module

public import Sarkozy.MainFinalF1.K3

@[expose] public section








open Finset
open scoped BigOperators

namespace Sarkozy.HsumProof

open Sarkozy.UpperComparison Sarkozy.PartV
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.MainFinal (MiddleConsts midK2 midK3 midK4 midK5 pieceScale)
open Sarkozy.NumericalFields (bandBound)
open Sarkozy.AnalyticCells (f1c2 f1c3)

/-- The budget of the upper part of `hsum`. -/
noncomputable def upperBudget : ℝ := 37 / 1000

/-- The budget of the middle part of `hsum`. -/
noncomputable def middleBudget : ℝ := 8349 / 10000

/-- The upper part of `hsum` (bands `β`, degrees `d ∈ [3, 7]`). -/
noncomputable def upperPart (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i)
    (hCa : ∀ k i, 0 ≤ Ca k i) : ℝ :=
  ∑ β, ∑ d ∈ upperDegrees,
    ((upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefS d *
        bandBound targetDecay d β +
      (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefA d *
        bandBound targetDecay d β)

/-- The middle part of `hsum` at the F1 numbers. -/
noncomputable def middlePart (κ : Fin 33 → MiddleConsts) : ℝ :=
  ∑ i : Fin 33, (midK2 κ i * f1c2 i +
    (midK3 κ i + midK4 i * pieceScale i + midK5 i * pieceScale i ^ 2) * f1c3 i)

/-- **The budget closes at the ledger**: `12/2⁵³⁴ + 0.037 + 0.8349 + 11/10⁷⁰ ≤ S + A` (RG's split at
`a_G`; it was `0.0526 + 0.9304` at the v2 ledger). -/
theorem budget_closes :
    12 / 2 ^ 534 + upperBudget + middleBudget + 11 / 10 ^ 70 ≤
      targetLedger.S + targetLedger.A := by
  have hc : (12 : ℝ) / 2 ^ 534 ≤ 12 / 2 ^ 200 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by norm_num))
  have hn : (12 : ℝ) / 2 ^ 200 + upperBudget + middleBudget + 11 / 10 ^ 70 ≤
      targetLedger.S + targetLedger.A := by
    norm_num [upperBudget, middleBudget, targetLedger]
  generalize (12 : ℝ) / 2 ^ 534 = c at hc ⊢
  linarith

/-- **`SAParts3.hsum` from the two part bounds**, for any data `Cs`, `Ca`, `κ`. The conclusion is
the field's statement verbatim. -/
theorem hsum_of_budget (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i)
    (hCa : ∀ k i, 0 ≤ Ca k i) (κ : Fin 33 → MiddleConsts)
    (hU : upperPart Cs Ca hCs hCa ≤ upperBudget) (hM : middlePart κ ≤ middleBudget) :
    12 / 2 ^ 534 + ∑ β, ∑ d ∈ upperDegrees,
        ((upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefS d *
            bandBound targetDecay d β +
          (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefA d *
            bandBound targetDecay d β) +
      ∑ i : Fin 33, (midK2 κ i * f1c2 i +
        (midK3 κ i + midK4 i * pieceScale i + midK5 i * pieceScale i ^ 2) * f1c3 i) +
        11 / 10 ^ 70 ≤ targetLedger.S + targetLedger.A := by
  have h := budget_closes
  unfold upperPart at hU
  unfold middlePart at hM
  generalize (12 : ℝ) / 2 ^ 534 = c at h ⊢
  linarith

end Sarkozy.HsumProof
