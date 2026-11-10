module

public import Sarkozy.MiddleRefinement.Hmid

@[expose] public section

/-!
# The paper's chosen sides and the finite sum of `hmid` (MRG)

`paper/sections/24_matching_mean.tex`, `prop:signed-sides`(ii),(iii);
`paper/sections/E_data.tex`, `tab:data:sides`.

* **`sideTab`**: the chosen sides `d_L(X_i) = d_R(X_i)` of the 33 pieces, in units of `10⁻⁷`: the
  column `H̄_{X_i} d_t(X_i)` of `tab:data:sides` (an upper bound rounded up at `10⁻⁷`) plus one
  unit. The paper's chosen sides lie within `10⁻³⁰` above the certified upper end of
  `H̄_X d_t(X)` (`eq:signed-increment`), so these sides are at least the paper's, and the block
  Grams hold at them by `lem:record:asymmetric-gram`(a) (enlargement) if they hold at the paper's.
  The values were transcribed from the table (MRG, 7 November 2026). An untrusted script check
  parses the table in `E_data.tex` and confirms, on all 33 rows, that each value is the column
  plus `10⁻⁷` and is at least `d^aux_s + δ⁺_s` (both columns rounded up) for `s = L, R`. They are
  data, and every statement below is checked in the kernel at them. **RG (7 November 2026):** each
  side is now MRG's value plus `0.02` (RB's `sideTab′`, package R), so the sides remain at least the
  paper's and the enlargement argument applies unchanged; the room pays for the crude collision
  constant `c_col = 73` in the gates (`SignedDecomp.gate73_check`).
* **`gates_check`**: `k_s(i) = w_{D,i} d_s(i) - v_{D,i} ≥ 0` on every piece (the side gates; the
  smallest was about `2.098` at the paper's sides).
* **`hmid_check`**: `∑_i [2 w_{D,i} c'₂(i) (s_E + a_E)(i) + fix_i + 2 k_s(i) c'₂(i)] ≤ 0.4927`
  (kernel; the value is about `0.564842`: matchings `0.407772`, other records `0.000231`, fold
  sides `0.156839`), with HS's `midW2`, `midFix` and the paper's `κ` (`paperKappa`).
* **`hnum_paper`**: the finite inequality `hnum` of `hmid_of_pieces` at the paper's data, with
  `τ = 12/2⁵³⁴ + Uup + 3/2¹⁵¹` and `Uup ≤ 0.037` (HS's `upperPart_le_budget`):
  `0.4927 + 12/2⁵³⁴ + 0.037 + 3/2¹⁵¹ ≤ T^{ledger} = 0.538801878963` (margin about `9.1·10⁻³`).

**RG (7 November 2026).** At the ledger's exponent `a_G = 71/10⁵` (the F1 numbers regenerated),
RB's loosened sides (`sideTab`: the paper's plus `0.02`) and RB's loosened `κ` (`paperKappa`):
the exact value of the `hmid_check` sum is `0.4926793` (at `a_T` with the paper's tables it was
`0.564842`); `Uup ≤ 0.037` is `upperBudget` (HS's proved `upperPart_le` gives `≤ 0.021`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.MiddleRefinement

open Sarkozy.PartV Sarkozy.MainFinal Sarkozy.NumericalFields Sarkozy.HsumProof
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.AnalyticCells (f1c2 f1c3 f1C2 f1C3)
open Sarkozy.BlockSpecPaper (allpWeights)
open Sarkozy.BlockSpecPaper.AllpData (allpRecord)

/-- **The chosen sides** `d_s(X_i)` (both `s`), in units of `10⁻⁷` (`tab:data:sides`, plus one
unit, plus RG's `0.02`). Data. -/
def sideTab : List ℕ :=
  [24103403, 24100799, 24098315, 24096397, 24095927, 24093647,
  24089367, 24085449, 24081855, 24078559, 24075542, 24072777,
  24070242, 24067916, 24065784, 24063831, 24062039, 24060397,
  24058891, 24057511, 24056246, 24055085, 24054021, 24053045,
  24052151, 24051331, 24050578, 24048145, 24046425, 24044350,
  24043312, 24042534, 24042320]

/-- The chosen side of piece `i`. -/
def sideQ (i : Fin 33) : ℚ := (sideTab.getD i.val 0 : ℚ) / 10 ^ 7

/-- The chosen side of piece `i`, as a real. -/
noncomputable def paperSide (i : Fin 33) : ℝ := (sideQ i : ℝ)

/-- The side coefficient `k_s(i) = w_{D,i} d_s(i) - v_{D,i}`, as a rational. -/
def kSideQ (i : Fin 33) : ℚ := (allpRecord i).wD * sideQ i - (allpRecord i).vD

theorem sideTab_length : sideTab.length = 33 := by decide

/-- **The side gates** `k_s(i) ≥ 0` (`prop:signed-sides`(ii), `cert:record:matching`). -/
theorem gates_check : ∀ i : Fin 33, 0 ≤ kSideQ i := by decide +kernel

/-- **The finite sum of `hmid`** at the paper's data (kernel). -/
theorem hmid_check :
    ∑ i : Fin 33, (midW2 i * (kSE i + kAE i) + midFix i + 2 * kSideQ i * f1C2 i.val) ≤
      4927 / 10000 := by
  decide +kernel

theorem kPiece_paperSide (i : Fin 33) : kPiece paperSide i = (kSideQ i : ℝ) := by
  unfold kPiece paperSide kSideQ allpWeights
  simp [MiddleRecords.CompletionRecord.weights, MiddleRecords.CompletionRecord.w,
    MiddleRecords.CompletionRecord.v]

theorem kPiece_paperSide_nonneg (i : Fin 33) : 0 ≤ kPiece paperSide i := by
  rw [kPiece_paperSide]
  exact_mod_cast gates_check i

/-- **The middle part of `hmid` at the paper's data**:
`middlePart κ⁰ + ∑_i 2 k_s(i) c'₂(i) ≤ 0.5655`
(HS's `middlePart_le_linear` at `κ⁰`, then `hmid_check`). -/
theorem hmid_middle_paper :
    middlePart (fun i => noFoldConsts (paperKappa i)) +
      ∑ i : Fin 33, (kPiece paperSide i + kPiece paperSide i) * f1c2 i ≤ 4927 / 10000 := by
  have h1 := middlePart_le_linear (fun i => noFoldConsts (paperKappa i))
  have h2 : ∑ i : Fin 33, ((midW2 i : ℝ) * ((noFoldConsts (paperKappa i)).sE +
      (noFoldConsts (paperKappa i)).aE + (noFoldConsts (paperKappa i)).ℓ) +
      (midW3 i : ℝ) * ((noFoldConsts (paperKappa i)).sF + (noFoldConsts (paperKappa i)).aF) +
      (midFix i : ℝ)) + ∑ i : Fin 33, (kPiece paperSide i + kPiece paperSide i) * f1c2 i =
      ((∑ i : Fin 33, (midW2 i * (kSE i + kAE i) + midFix i + 2 * kSideQ i * f1C2 i.val) : ℚ) :
        ℝ) := by
    rw [← sum_add_distrib]
    push_cast
    refine sum_congr rfl fun i _ => ?_
    rw [kPiece_paperSide]
    simp only [noFoldConsts, paperKappa, f1c2]
    ring
  have h3 : ((∑ i : Fin 33, (midW2 i * (kSE i + kAE i) + midFix i + 2 * kSideQ i * f1C2 i.val) :
      ℚ) : ℝ) ≤ ((4927 / 10000 : ℚ) : ℝ) := by exact_mod_cast hmid_check
  have h4 : ((4927 / 10000 : ℚ) : ℝ) = 4927 / 10000 := by push_cast; ring
  linarith

/-- **The finite inequality of `hmid` at the paper's data** (`hnum` of `hmid_of_pieces` with
`τ = 12/2⁵³⁴ + U + 3/2¹⁵¹`, `U ≤ 0.037`). -/
theorem hnum_paper {U : ℝ} (hU : U ≤ upperBudget) :
    middlePart (fun i => noFoldConsts (paperKappa i)) +
      ∑ i : Fin 33, (kPiece paperSide i + kPiece paperSide i) * f1c2 i +
        (12 / 2 ^ 534 + U + 3 / 2 ^ 151) ≤ targetLedger.T := by
  have h := hmid_middle_paper
  have hc : (12 : ℝ) / 2 ^ 534 ≤ 12 / 2 ^ 200 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by norm_num))
  have hn : (4927 / 10000 : ℝ) + 12 / 2 ^ 200 + upperBudget + 3 / 2 ^ 151 ≤ targetLedger.T := by
    norm_num [upperBudget, targetLedger]
  generalize (12 : ℝ) / 2 ^ 534 = c at hc ⊢
  linarith

end Sarkozy.MiddleRefinement
