module

public import Sarkozy.AnalyticCells.Logs

@[expose] public section

/-!
# The cell bounds of piece 28, `[X_Ch, 2³⁴)` (236 cells)

`lem:record:block-charge`(i), `eq:record:cell-charge` at `a_T`, `def:record:exact-blocks`(d).

The kernel checks `Checks` (the cardinalities `n_j = ⌊570/log x_{j+1}⌋` and the ranges) and the two
rational sums `bound2 ≤ c₂`, `bound3 ≤ c₃` (`decide +kernel`); then **`cellBound_le_28`**: M2's cell
bound of N1's `paperPiece 28` at `a_T`, with `thm:bmor`'s error, is at most `c₂` at `s = 1` and `c₃`
at `s = 3/2`. The constants `c_d` are `⌈10³⁰ bound_d⌉/10³⁰` (computed by `#eval`; untrusted, checked
here).
-/

namespace Sarkozy.AnalyticCells

open Sarkozy.Misc Sarkozy.PartV Sarkozy.PaperNumbers

theorem checks_28 : geo28.Checks = true := by decide +kernel

/-- The cell constants of piece 28 at `s = 1` and `s = 3/2`. -/
def cellK_28 : ℚ × ℚ := (2522977016448348289745228327 / 10 ^ 30, 26928838036354790242263 / 10 ^ 30)

theorem bound2_28 : geo28.bound2 ≤ cellK_28.1 := by decide +kernel

theorem bound3_28 : geo28.bound3 ≤ cellK_28.2 := by decide +kernel

theorem cellStart_28 : cellStart 28 = (XCh : ℝ) := by
  unfold cellStart
  rw [pieceStart_28, max_eq_right (by norm_num [XCh])]

theorem encl_28 : Encl geo28 (cellStart 28) (pieceStop 28 : ℝ) where
  one_lt := by
    rw [cellStart_28]
    unfold XCh
    norm_num
  le := by
    rw [cellStart_28, pieceStop_28]
    unfold XCh
    norm_num
  lx_lo := by
    rw [cellStart_28]
    simp only [geo28]
    exact log_XCh_mem.1
  lx_hi := by
    rw [cellStart_28]
    simp only [geo28]
    exact log_XCh_mem.2
  lY_lo := by
    rw [show ((pieceStop 28 : ℕ) : ℝ) = (2 : ℝ) ^ 34 by rw [pieceStop_28]; push_cast; ring]
    have h := (log_two_pow_mem 34).1
    push_cast at h
    simp only [geo28]
    push_cast
    linarith
  lY_hi := by
    rw [show ((pieceStop 28 : ℕ) : ℝ) = (2 : ℝ) ^ 34 by rw [pieceStop_28]; push_cast; ring]
    have h := (log_two_pow_mem 34).2
    push_cast at h
    simp only [geo28]
    push_cast
    linarith
  checks := checks_28

/-- **The cell bounds of piece 28** (`eq:record:cell-charge`, `d = 2, 3`, at `a_T`). -/
theorem cellBound_le_28 :
    cellBound (paperPiece 28) Sarkozy.TargetLedger.targetDecay 1
        (2411 / (5000000 * Real.log ((paperPiece 28).x 0))) ≤ (cellK_28.1 : ℝ) ∧
      cellBound (paperPiece 28) Sarkozy.TargetLedger.targetDecay (3 / 2)
        (2411 / (5000000 * Real.log ((paperPiece 28).x 0))) ≤ (cellK_28.2 : ℝ) := by
  have hstop : XCh < pieceStop 28 := by decide +kernel
  obtain ⟨hn, hx, hnc⟩ := paperPiece_fields 28 (n := geo28.n) hstop cellCount_28
  rw [← aQ_eq]
  have h2 : (geo28.bound2 : ℝ) ≤ (cellK_28.1 : ℝ) := by exact_mod_cast bound2_28
  have h3 : (geo28.bound3 : ℝ) ≤ (cellK_28.2 : ℝ) := by exact_mod_cast bound3_28
  exact ⟨(encl_28.cellBound_le_bound2 _ hn hx hnc (by decide +kernel)).trans h2,
    (encl_28.cellBound_le_bound3 _ hn hx hnc (by decide +kernel)).trans h3⟩

end Sarkozy.AnalyticCells
