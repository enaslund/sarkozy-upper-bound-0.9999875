module

public import Sarkozy.AnalyticCells.Logs

@[expose] public section

/-!
# The cell bounds of piece 29, `[2³⁴, 2³⁶)` (256 cells)

`lem:record:block-charge`(i), `eq:record:cell-charge` at `a_T`, `def:record:exact-blocks`(d).

The kernel checks `Checks` (the cardinalities `n_j = ⌊570/log x_{j+1}⌋` and the ranges) and the two
rational sums `bound2 ≤ c₂`, `bound3 ≤ c₃` (`decide +kernel`); then **`cellBound_le_29`**: M2's cell
bound of N1's `paperPiece 29` at `a_T`, with `thm:bmor`'s error, is at most `c₂` at `s = 1` and `c₃`
at `s = 3/2`. The constants `c_d` are `⌈10³⁰ bound_d⌉/10³⁰` (computed by `#eval`; untrusted, checked
here).
-/

namespace Sarkozy.AnalyticCells

open Sarkozy.Misc Sarkozy.PartV Sarkozy.PaperNumbers

theorem checks_29 : geo29.Checks = true := by decide +kernel

/-- The cell constants of piece 29 at `s = 1` and `s = 3/2`. -/
def cellK_29 : ℚ × ℚ := (2744435029332152127527990013 / 10 ^ 30, 15105745318962353267257 / 10 ^ 30)

theorem bound2_29 : geo29.bound2 ≤ cellK_29.1 := by decide +kernel

theorem bound3_29 : geo29.bound3 ≤ cellK_29.2 := by decide +kernel

theorem cellStart_29 : cellStart 29 = (2 : ℝ) ^ 34 := by
  unfold cellStart
  rw [pieceStart_29, max_eq_left (by norm_num [XCh])]
  push_cast
  ring

theorem encl_29 : Encl geo29 (cellStart 29) (pieceStop 29 : ℝ) where
  one_lt := by
    rw [cellStart_29]
    norm_num
  le := by
    rw [cellStart_29, pieceStop_29]
    norm_num
  lx_lo := by
    rw [cellStart_29]
    have h := (log_two_pow_mem 34).1
    push_cast at h
    simp only [geo29]
    push_cast
    linarith
  lx_hi := by
    rw [cellStart_29]
    have h := (log_two_pow_mem 34).2
    push_cast at h
    simp only [geo29]
    push_cast
    linarith
  lY_lo := by
    rw [show ((pieceStop 29 : ℕ) : ℝ) = (2 : ℝ) ^ 36 by rw [pieceStop_29]; push_cast; ring]
    have h := (log_two_pow_mem 36).1
    push_cast at h
    simp only [geo29]
    push_cast
    linarith
  lY_hi := by
    rw [show ((pieceStop 29 : ℕ) : ℝ) = (2 : ℝ) ^ 36 by rw [pieceStop_29]; push_cast; ring]
    have h := (log_two_pow_mem 36).2
    push_cast at h
    simp only [geo29]
    push_cast
    linarith
  checks := checks_29

/-- **The cell bounds of piece 29** (`eq:record:cell-charge`, `d = 2, 3`, at `a_T`). -/
theorem cellBound_le_29 :
    cellBound (paperPiece 29) Sarkozy.TargetLedger.targetDecay 1
        (2411 / (5000000 * Real.log ((paperPiece 29).x 0))) ≤ (cellK_29.1 : ℝ) ∧
      cellBound (paperPiece 29) Sarkozy.TargetLedger.targetDecay (3 / 2)
        (2411 / (5000000 * Real.log ((paperPiece 29).x 0))) ≤ (cellK_29.2 : ℝ) := by
  have hstop : XCh < pieceStop 29 := by decide +kernel
  obtain ⟨hn, hx, hnc⟩ := paperPiece_fields 29 (n := geo29.n) hstop cellCount_29
  rw [← aQ_eq]
  have h2 : (geo29.bound2 : ℝ) ≤ (cellK_29.1 : ℝ) := by exact_mod_cast bound2_29
  have h3 : (geo29.bound3 : ℝ) ≤ (cellK_29.2 : ℝ) := by exact_mod_cast bound3_29
  exact ⟨(encl_29.cellBound_le_bound2 _ hn hx hnc (by decide +kernel)).trans h2,
    (encl_29.cellBound_le_bound3 _ hn hx hnc (by decide +kernel)).trans h3⟩

end Sarkozy.AnalyticCells
