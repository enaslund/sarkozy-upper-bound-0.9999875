module

public import Sarkozy.LetterTotals.Split
public import Sarkozy.HsumProof.PaperKappa

@[expose] public section

/-!
# The two middle totals at the paper's constants, evaluated (HX)

HX, 8 November 2026. HS's and RG's `middlePart_paperKappa` evaluates the middle term of `hsum`
(`∑_i K_d(i) c_d(i)`, value `0.8348806`) through HS's linear form `middle_term_le` (with
`r_X, b^{-1/2} ≤ 2^{-12}`) and one kernel check. The same form, split by change type:

* `midFixS`, `midFixA`: the `κ`-free parts of HS's `midFix`, per change type (`midFix_split`);
* `middleS_term_le`, `middleA_term_le`: HS's `middle_term_le` per change type;
* `middleS_check`, `middleA_check` (`decide +kernel`, two 33-term rational sums, as HS's
  `middle_paper_check`): the symmetric linear form is at most `0.0179`, the skew one at most
  `0.8171` (their values lie in `(0.0178, 0.0179]` and `(0.8170, 0.8171]`);
* **`middleS_paperKappa`**: `middleS paperKappa ≤ 0.0179`; **`middleA_paperKappa`**:
  `middleA paperKappa ≤ 0.8171`.

So of `SForm F`, everything but the upper symmetric sum `upperS` is evaluated.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.LetterTotals

open Sarkozy.PartV Sarkozy.MainFinal Sarkozy.NumericalFields
open Sarkozy.MiddleRecords (coefS2 coefS3 coefS4 coefS5 coefA2 coefA3 coefA4 gS gA rXof)
open Sarkozy.BlockSpecPaper (allpWeights allpInputs)
open Sarkozy.BlockSpecPaper.AllpData (allpRecord)
open Sarkozy.AnalyticCells (f1c2 f1c3 f1C2 f1C3)
open Sarkozy.HsumProof (midW2 midW3 midQ rB midFix f1C3_nonneg pieceScale_le rXof_le paperKappa
  kSF kAF kL kSE kAE)

/-- The symmetric part of HS's `midFix`: the deleted records, `S₄ r_B`, `S₅ r_B²`. -/
def midFixS (i : Fin 33) : ℚ :=
  (6 * (allpRecord i).vR + 2 * (allpRecord i).vD * ((allpRecord i).f₁ + (allpRecord i).h₁)) *
      f1C3 i.val +
    (2 * (allpRecord i).vC + (allpRecord i).wR * (20 / ((1 - 2 * midQ i) * (1 - 3 * midQ i)) +
        4 / (1 - 2 * midQ i) + 2 / (1 - midQ i))) * rB * f1C3 i.val +
    2 * (allpRecord i).wC / (1 - midQ i) ^ 2 * rB ^ 2 * f1C3 i.val

/-- The skew part of HS's `midFix`: `w_R g_A` (at `r_X ≤ r_B`) and `A₄ r_B`. -/
def midFixA (i : Fin 33) : ℚ :=
  (allpRecord i).wR * (4 * (1 + 8 * rB) / ((1 - 2 * midQ i) * (1 - 3 * midQ i)) +
      2 / (1 - midQ i)) * f1C3 i.val +
    2 * (allpRecord i).wC / (1 - midQ i) * rB * f1C3 i.val

/-- HS's `midFix` is the sum of the two parts. -/
theorem midFix_split (i : Fin 33) : midFixS i + midFixA i = midFix i := by
  unfold midFixS midFixA midFix
  ring

/-- **HS's `middle_term_le`, symmetric half.** -/
theorem middleS_term_le (κ : Fin 33 → MiddleConsts) (i : Fin 33) :
    midS2 κ i * f1c2 i + (midS3 κ i + midS4 i * pieceScale i + midS5 i * pieceScale i ^ 2) *
        f1c3 i ≤
      (midW2 i : ℝ) * (κ i).sE + (midW3 i : ℝ) * (κ i).sF + (midFixS i : ℝ) := by
  have hq := qX_mem i
  have hq1 : (0 : ℝ) < 1 - 1 / (pieceStart i : ℝ) := by linarith [hq.2]
  have hc3 : (0 : ℝ) ≤ f1c3 i := by unfold f1c3; exact_mod_cast f1C3_nonneg _
  have hr := pieceScale_le i
  have hr0 : 0 ≤ pieceScale i := pieceScale_nonneg i
  have hS4 : 0 ≤ midS4 i := by
    have hv := (allpWeights i).v_nonneg .C
    have hwR := (allpWeights i).w_nonneg .R
    have hg := gS_nonneg i
    unfold midS4 coefS4
    positivity
  have hS5 : 0 ≤ midS5 i := by
    have hwC := (allpWeights i).w_nonneg .C
    unfold midS5 coefS5
    positivity
  have h4 : midS4 i * pieceScale i ≤ midS4 i * (rB : ℝ) := mul_le_mul_of_nonneg_left hr hS4
  have h5 : midS5 i * pieceScale i ^ 2 ≤ midS5 i * (rB : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr 2) hS5
  have hsum : midS3 κ i + midS4 i * pieceScale i + midS5 i * pieceScale i ^ 2 ≤
      midS3 κ i + midS4 i * (rB : ℝ) + midS5 i * (rB : ℝ) ^ 2 := by linarith
  have h3 := mul_le_mul_of_nonneg_right hsum hc3
  refine (add_le_add (le_refl _) h3).trans (le_of_eq ?_)
  unfold midS2 midS3 midS4 midS5 coefS2 coefS3 coefS4 coefS5 midW2 midW3 midFixS f1c2 f1c3 gS
    midQ
  simp only [allpWeights, allpInputs, MiddleRecords.CompletionRecord.weights,
    MiddleRecords.CompletionRecord.inputs, MiddleRecords.CompletionRecord.w,
    MiddleRecords.CompletionRecord.v]
  push_cast
  ring

/-- **HS's `middle_term_le`, skew half.** -/
theorem middleA_term_le (κ : Fin 33 → MiddleConsts) (i : Fin 33) :
    midA2 κ i * f1c2 i + (midA3 κ i + midA4 i * pieceScale i) * f1c3 i ≤
      (midW2 i : ℝ) * ((κ i).aE + (κ i).ℓ) + (midW3 i : ℝ) * (κ i).aF + (midFixA i : ℝ) := by
  have hq := qX_mem i
  have hq2 : (0 : ℝ) < 1 - 2 * (1 / (pieceStart i : ℝ)) := by linarith [hq.2]
  have hq3 : (0 : ℝ) < 1 - 3 * (1 / (pieceStart i : ℝ)) := by linarith [hq.2]
  have hq1 : (0 : ℝ) < 1 - 1 / (pieceStart i : ℝ) := by linarith [hq.2]
  have hc3 : (0 : ℝ) ≤ f1c3 i := by unfold f1c3; exact_mod_cast f1C3_nonneg _
  have hr := pieceScale_le i
  have hrX := rXof_le i
  have hwR : (0 : ℝ) ≤ (allpWeights i).w .R := (allpWeights i).w_nonneg _
  have hA4 : 0 ≤ midA4 i := by
    have hwC := (allpWeights i).w_nonneg .C
    unfold midA4 coefA4
    positivity
  have hgA : gA (1 / (pieceStart i : ℝ)) (rXof (pieceStart i)) ≤
      4 * (1 + 8 * (rB : ℝ)) / ((1 - 2 * (1 / (pieceStart i : ℝ))) *
        (1 - 3 * (1 / (pieceStart i : ℝ)))) + 2 / (1 - 1 / (pieceStart i : ℝ)) := by
    unfold gA
    have := div_le_div_of_nonneg_right (by linarith : 4 * (1 + 8 * rXof (pieceStart i)) ≤
      4 * (1 + 8 * (rB : ℝ))) (mul_pos hq2 hq3).le
    linarith
  have h4 : midA4 i * pieceScale i ≤ midA4 i * (rB : ℝ) := mul_le_mul_of_nonneg_left hr hA4
  have hA3 : midA3 κ i ≤ 2 * (allpWeights i).w .D * (κ i).aF +
      (allpWeights i).w .R * (4 * (1 + 8 * (rB : ℝ)) / ((1 - 2 * (1 / (pieceStart i : ℝ))) *
        (1 - 3 * (1 / (pieceStart i : ℝ)))) + 2 / (1 - 1 / (pieceStart i : ℝ))) := by
    unfold midA3 coefA3
    have := mul_le_mul_of_nonneg_left hgA hwR
    linarith
  have hsum : midA3 κ i + midA4 i * pieceScale i ≤ 2 * (allpWeights i).w .D * (κ i).aF +
      (allpWeights i).w .R * (4 * (1 + 8 * (rB : ℝ)) / ((1 - 2 * (1 / (pieceStart i : ℝ))) *
        (1 - 3 * (1 / (pieceStart i : ℝ)))) + 2 / (1 - 1 / (pieceStart i : ℝ))) +
      midA4 i * (rB : ℝ) := by linarith
  have h3 := mul_le_mul_of_nonneg_right hsum hc3
  refine (add_le_add (le_refl _) h3).trans (le_of_eq ?_)
  unfold midA2 midA4 coefA2 coefA4 midW2 midW3 midFixA f1c2 f1c3 midQ
  simp only [allpWeights, MiddleRecords.CompletionRecord.weights,
    MiddleRecords.CompletionRecord.w, MiddleRecords.CompletionRecord.v]
  push_cast
  ring

/-- The rational check of the symmetric linear form at the table's constants (`≤ 0.0179`). -/
theorem middleS_check :
    ∑ i : Fin 33, (midW2 i * kSE i + midW3 i * kSF i + midFixS i) ≤ 179 / 10000 := by
  decide +kernel

/-- The rational check of the skew linear form at the table's constants (`≤ 0.8171`). -/
theorem middleA_check :
    ∑ i : Fin 33, (midW2 i * (kAE i + kL i) + midW3 i * kAF i + midFixA i) ≤ 8171 / 10000 := by
  decide +kernel

/-- **The symmetric middle total at the paper's constants**: `middleS paperKappa ≤ 0.0179`. -/
theorem middleS_paperKappa : middleS paperKappa ≤ 179 / 10000 := by
  refine (sum_le_sum fun i _ => middleS_term_le paperKappa i).trans ?_
  calc ∑ i : Fin 33, ((midW2 i : ℝ) * (paperKappa i).sE + (midW3 i : ℝ) * (paperKappa i).sF +
        (midFixS i : ℝ)) =
      ((∑ i : Fin 33, (midW2 i * kSE i + midW3 i * kSF i + midFixS i) : ℚ) : ℝ) := by
        push_cast
        rfl
    _ ≤ ((179 / 10000 : ℚ) : ℝ) := by exact_mod_cast middleS_check
    _ = 179 / 10000 := by push_cast; rfl

/-- **The skew middle total at the paper's constants**: `middleA paperKappa ≤ 0.8171`. -/
theorem middleA_paperKappa : middleA paperKappa ≤ 8171 / 10000 := by
  refine (sum_le_sum fun i _ => middleA_term_le paperKappa i).trans ?_
  calc ∑ i : Fin 33, ((midW2 i : ℝ) * ((paperKappa i).aE + (paperKappa i).ℓ) +
        (midW3 i : ℝ) * (paperKappa i).aF + (midFixA i : ℝ)) =
      ((∑ i : Fin 33, (midW2 i * (kAE i + kL i) + midW3 i * kAF i + midFixA i) : ℚ) : ℝ) := by
        push_cast
        rfl
    _ ≤ ((8171 / 10000 : ℚ) : ℝ) := by exact_mod_cast middleA_check
    _ = 8171 / 10000 := by push_cast; rfl

end Sarkozy.LetterTotals
