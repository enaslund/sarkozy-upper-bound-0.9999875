module

public import Sarkozy.HsumProof.UpperDefs
public import Sarkozy.HsumProof.UpperRound
public import Sarkozy.HsumProof.Budget

@[expose] public section





open Finset

namespace Sarkozy.HsumProof

open Sarkozy.PartV Sarkozy.UpperComparison Sarkozy.NumericalFields
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.MainFinal (MiddleConsts midK2 midK3 midK4 midK5 pieceScale)
open Sarkozy.AnalyticCells (f1c2 f1c3)

/-- The rounded bound of band `k`. -/
def roundQ (k : Fin 310) : ℚ := (UpperRound.roundTab.getD k.val 0 : ℚ) / 10 ^ 40

/-- **The check of band `k`.** -/
def bandCheck (k : Fin 310) : Bool :=
  bandOK aT k && decide (∀ d ∈ Finset.Icc (3 : ℕ) 7, 0 ≤ UBQ aT k d) &&
    decide (bandTot k ≤ roundQ k)

theorem bandCheck_0 : ∀ k : Fin 310, k.val < 40 → bandCheck k = true := by decide +kernel

theorem bandCheck_1 : ∀ k : Fin 310, 40 ≤ k.val → k.val < 80 → bandCheck k = true := by
  decide +kernel

theorem bandCheck_2 : ∀ k : Fin 310, 80 ≤ k.val → k.val < 120 → bandCheck k = true := by
  decide +kernel

theorem bandCheck_3 : ∀ k : Fin 310, 120 ≤ k.val → k.val < 160 → bandCheck k = true := by
  decide +kernel

theorem bandCheck_4 : ∀ k : Fin 310, 160 ≤ k.val → k.val < 200 → bandCheck k = true := by
  decide +kernel

theorem bandCheck_5 : ∀ k : Fin 310, 200 ≤ k.val → k.val < 240 → bandCheck k = true := by
  decide +kernel

theorem bandCheck_6 : ∀ k : Fin 310, 240 ≤ k.val → k.val < 280 → bandCheck k = true := by
  decide +kernel

theorem bandCheck_7 : ∀ k : Fin 310, 280 ≤ k.val → k.val < 309 → bandCheck k = true := by
  decide +kernel

/-- Band 309 (`[2⁶⁴, 2⁵¹²)`, 448 octaves). -/
theorem bandCheck_309 : bandCheck 309 = true := by decide +kernel

theorem bandCheck_all (k : Fin 310) : bandCheck k = true := by
  have hk := k.isLt
  by_cases h0 : k.val < 40
  · exact bandCheck_0 k h0
  by_cases h1 : k.val < 80
  · exact bandCheck_1 k (by omega) h1
  by_cases h2 : k.val < 120
  · exact bandCheck_2 k (by omega) h2
  by_cases h3 : k.val < 160
  · exact bandCheck_3 k (by omega) h3
  by_cases h4 : k.val < 200
  · exact bandCheck_4 k (by omega) h4
  by_cases h5 : k.val < 240
  · exact bandCheck_5 k (by omega) h5
  by_cases h6 : k.val < 280
  · exact bandCheck_6 k (by omega) h6
  by_cases h7 : k.val < 309
  · exact bandCheck_7 k (by omega) h7
  have : k = 309 := Fin.ext (by show k.val = 309; omega)
  rw [this]
  exact bandCheck_309

/-- **The final sum**: `∑_k roundTab k / 10⁴⁰ ≤ 21/1000`. -/
theorem round_sum : ∑ k : Fin 310, roundQ k ≤ 21 / 1000 := by decide +kernel

/-- The terms of one band are at most `roundQ k`. -/
theorem band_le (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i)
    (hCa : ∀ k i, 0 ≤ Ca k i) (hL : PaperLedgers Cs Ca) (β : Fin 310) :
    ∑ d ∈ upperDegrees,
        ((upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefS d *
            bandBound targetDecay d β +
          (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefA d *
            bandBound targetDecay d β) ≤ (roundQ β : ℝ) := by
  have hc := bandCheck_all β
  simp only [bandCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hok, hUB0⟩, htot⟩ := hc
  have hterm : ∀ d ∈ upperDegrees,
      (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefS d *
            bandBound targetDecay d β +
          (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefA d *
            bandBound targetDecay d β ≤
        (cSQ β d : ℝ) * (UBQ aT β d : ℝ) + (cAQ β d : ℝ) * (UBQ aT β d : ℝ) := by
    intro d hd
    have hd' : d ∈ Finset.Icc 3 7 := hd
    have hd2 : 2 ≤ d := by
      have := (Finset.mem_Icc.mp hd').1
      omega
    have hb := bandBound_le_UBQ aT β hok hd2
    rw [aT_cast] at hb
    have hU0 : (0 : ℝ) ≤ (UBQ aT β d : ℝ) := by exact_mod_cast hUB0 d hd'
    have hS := coefS_le β (Cs β) (Ca β) (hCs β) (hCa β) (fun t => (hL β t).1) hd'
    have hA := coefA_le β (Cs β) (Ca β) (hCs β) (hCa β) (fun t => (hL β t).2) d
    have hS0 := RecordLedger.coefS_nonneg
      (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)) d
    have hA0 := RecordLedger.coefA_nonneg
      (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)) d
    apply add_le_add
    · exact (mul_le_mul_of_nonneg_left hb hS0).trans (mul_le_mul_of_nonneg_right hS hU0)
    · exact (mul_le_mul_of_nonneg_left hb hA0).trans (mul_le_mul_of_nonneg_right hA hU0)
  refine (sum_le_sum hterm).trans ?_
  have e : ∑ d ∈ upperDegrees, ((cSQ β d : ℝ) * (UBQ aT β d : ℝ) +
      (cAQ β d : ℝ) * (UBQ aT β d : ℝ)) = (bandTot β : ℝ) := by
    unfold bandTot
    push_cast
    rfl
  rw [e]
  exact_mod_cast htot

/-- **The upper part of `hsum`**: `upperPart Cs Ca ≤ 21/1000` for data with the paper's state
ledgers. -/
theorem upperPart_le (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i)
    (hCa : ∀ k i, 0 ≤ Ca k i) (hL : PaperLedgers Cs Ca) :
    upperPart Cs Ca hCs hCa ≤ 21 / 1000 := by
  unfold upperPart
  calc _ ≤ ∑ β : Fin 310, (roundQ β : ℝ) := sum_le_sum fun β _ => band_le Cs Ca hCs hCa hL β
    _ = ((∑ β : Fin 310, roundQ β : ℚ) : ℝ) := by push_cast; rfl
    _ ≤ 21 / 1000 := by
      have := round_sum
      have h' : ((∑ β : Fin 310, roundQ β : ℚ) : ℝ) ≤ ((21 / 1000 : ℚ) : ℝ) := by
        exact_mod_cast this
      simpa using h'

/-- With E3's budget: `upperPart ≤ 0.0526`. -/
theorem upperPart_le_budget (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i)
    (hCa : ∀ k i, 0 ≤ Ca k i) (hL : PaperLedgers Cs Ca) :
    upperPart Cs Ca hCs hCa ≤ upperBudget :=
  (upperPart_le Cs Ca hCs hCa hL).trans (by unfold upperBudget; norm_num)

/-- **HS's budget split**: the upper part takes `0.021`, the middle part `0.8509` (RG, at `a_G`;
it was `0.962` at `a_T`); `12/2⁵³⁴ + 0.021 + 0.8509 + 11/10⁷⁰ ≤ S + A` (margin `2.7·10⁻⁵`). -/
noncomputable def middleBudgetHS : ℝ := 8509 / 10000

theorem budget_closes_HS :
    12 / 2 ^ 534 + 21 / 1000 + middleBudgetHS + 11 / 10 ^ 70 ≤
      targetLedger.S + targetLedger.A := by
  have hc : (12 : ℝ) / 2 ^ 534 ≤ 12 / 2 ^ 200 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by norm_num))
  have hn : (12 : ℝ) / 2 ^ 200 + 21 / 1000 + middleBudgetHS + 11 / 10 ^ 70 ≤
      targetLedger.S + targetLedger.A := by
    norm_num [middleBudgetHS, Sarkozy.TargetLedger.targetLedger]
  generalize (12 : ℝ) / 2 ^ 534 = c at hc ⊢
  linarith

/-- **`SAParts3.hsum` from the paper's ledgers and the middle bound** `middlePart κ ≤ 0.8509`. The
conclusion is the field's statement verbatim. -/
theorem hsum_of_ledgers (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i)
    (hCa : ∀ k i, 0 ≤ Ca k i) (hL : PaperLedgers Cs Ca) (κ : Fin 33 → MiddleConsts)
    (hM : middlePart κ ≤ middleBudgetHS) :
    12 / 2 ^ 534 + ∑ β, ∑ d ∈ upperDegrees,
        ((upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefS d *
            bandBound targetDecay d β +
          (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefA d *
            bandBound targetDecay d β) +
      ∑ i : Fin 33, (midK2 κ i * f1c2 i +
        (midK3 κ i + midK4 i * pieceScale i + midK5 i * pieceScale i ^ 2) * f1c3 i) +
        11 / 10 ^ 70 ≤ targetLedger.S + targetLedger.A := by
  have h := budget_closes_HS
  have hU := upperPart_le Cs Ca hCs hCa hL
  unfold upperPart at hU
  unfold middlePart at hM
  generalize (12 : ℝ) / 2 ^ 534 = c at h ⊢
  linarith

end Sarkozy.HsumProof
