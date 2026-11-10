module

public import Sarkozy.AnalyticCells.Logs

@[expose] public section

/-!
# The cell bounds of piece 30, `[2³⁶, 2⁴⁰)` (512 cells)

`lem:record:block-charge`(i), `eq:record:cell-charge` at `a_T`, `def:record:exact-blocks`(d).

The kernel checks `Checks` (the cardinalities `n_j = ⌊570/log x_{j+1}⌋` and the ranges) and the two
rational sums `bound2 ≤ c₂`, `bound3 ≤ c₃` (`decide +kernel`); then **`cellBound_le_30`**: M2's cell
bound of N1's `paperPiece 30` at `a_T`, with `thm:bmor`'s error, is at most `c₂` at `s = 1` and `c₃`
at `s = 3/2`. The constants `c_d` are `⌈10³⁰ bound_d⌉/10³⁰` (computed by `#eval`; untrusted, checked
here).
-/

namespace Sarkozy.AnalyticCells

open Sarkozy.Misc Sarkozy.PartV Sarkozy.PaperNumbers

theorem checks_30 : geo30.Checks = true := by decide +kernel

/-- The cell constants of piece 30 at `s = 1` and `s = 3/2`. -/
def cellK_30 : ℚ × ℚ := (5492340727973873065680828803 / 10 ^ 30, 11335319241348855991269 / 10 ^ 30)

theorem bound2_30 : geo30.bound2 ≤ cellK_30.1 := by decide +kernel

theorem bound3_30 : geo30.bound3 ≤ cellK_30.2 := by decide +kernel

theorem cellStart_30 : cellStart 30 = (2 : ℝ) ^ 36 := by
  unfold cellStart
  rw [pieceStart_30, max_eq_left (by norm_num [XCh])]
  push_cast
  ring

theorem encl_30 : Encl geo30 (cellStart 30) (pieceStop 30 : ℝ) where
  one_lt := by
    rw [cellStart_30]
    norm_num
  le := by
    rw [cellStart_30, pieceStop_30]
    norm_num
  lx_lo := by
    rw [cellStart_30]
    have h := (log_two_pow_mem 36).1
    push_cast at h
    simp only [geo30]
    push_cast
    linarith
  lx_hi := by
    rw [cellStart_30]
    have h := (log_two_pow_mem 36).2
    push_cast at h
    simp only [geo30]
    push_cast
    linarith
  lY_lo := by
    rw [show ((pieceStop 30 : ℕ) : ℝ) = (2 : ℝ) ^ 40 by rw [pieceStop_30]; push_cast; ring]
    have h := (log_two_pow_mem 40).1
    push_cast at h
    simp only [geo30]
    push_cast
    linarith
  lY_hi := by
    rw [show ((pieceStop 30 : ℕ) : ℝ) = (2 : ℝ) ^ 40 by rw [pieceStop_30]; push_cast; ring]
    have h := (log_two_pow_mem 40).2
    push_cast at h
    simp only [geo30]
    push_cast
    linarith
  checks := checks_30

/-- **The cell bounds of piece 30** (`eq:record:cell-charge`, `d = 2, 3`, at `a_T`). -/
theorem cellBound_le_30 :
    cellBound (paperPiece 30) Sarkozy.TargetLedger.targetDecay 1
        (2411 / (5000000 * Real.log ((paperPiece 30).x 0))) ≤ (cellK_30.1 : ℝ) ∧
      cellBound (paperPiece 30) Sarkozy.TargetLedger.targetDecay (3 / 2)
        (2411 / (5000000 * Real.log ((paperPiece 30).x 0))) ≤ (cellK_30.2 : ℝ) := by
  have hstop : XCh < pieceStop 30 := by decide +kernel
  obtain ⟨hn, hx, hnc⟩ := paperPiece_fields 30 (n := geo30.n) hstop cellCount_30
  rw [← aQ_eq]
  have h2 : (geo30.bound2 : ℝ) ≤ (cellK_30.1 : ℝ) := by exact_mod_cast bound2_30
  have h3 : (geo30.bound3 : ℝ) ≤ (cellK_30.2 : ℝ) := by exact_mod_cast bound3_30
  exact ⟨(encl_30.cellBound_le_bound2 _ hn hx hnc (by decide +kernel)).trans h2,
    (encl_30.cellBound_le_bound3 _ hn hx hnc (by decide +kernel)).trans h3⟩

end Sarkozy.AnalyticCells
