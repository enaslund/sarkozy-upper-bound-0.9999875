module

public import Sarkozy.AnalyticCells.Logs

@[expose] public section

/-!
# The cell bounds of piece 31, `[2⁴⁰, 2⁴⁵)` (640 cells)

`lem:record:block-charge`(i), `eq:record:cell-charge` at `a_T`, `def:record:exact-blocks`(d).

The kernel checks `Checks` (the cardinalities `n_j = ⌊570/log x_{j+1}⌋` and the ranges) and the two
rational sums `bound2 ≤ c₂`, `bound3 ≤ c₃` (`decide +kernel`); then **`cellBound_le_31`**: M2's cell
bound of N1's `paperPiece 31` at `a_T`, with `thm:bmor`'s error, is at most `c₂` at `s = 1` and `c₃`
at `s = 3/2`. The constants `c_d` are `⌈10³⁰ bound_d⌉/10³⁰` (computed by `#eval`; untrusted, checked
here).
-/

namespace Sarkozy.AnalyticCells

open Sarkozy.Misc Sarkozy.PartV Sarkozy.PaperNumbers

theorem checks_31 : geo31.Checks = true := by decide +kernel

/-- The cell constants of piece 31 at `s = 1` and `s = 3/2`. -/
def cellK_31 : ℚ × ℚ := (6867202204257239823188005843 / 10 ^ 30, 3110670209133068660932 / 10 ^ 30)

theorem bound2_31 : geo31.bound2 ≤ cellK_31.1 := by decide +kernel

theorem bound3_31 : geo31.bound3 ≤ cellK_31.2 := by decide +kernel

theorem cellStart_31 : cellStart 31 = (2 : ℝ) ^ 40 := by
  unfold cellStart
  rw [pieceStart_31, max_eq_left (by norm_num [XCh])]
  push_cast
  ring

theorem encl_31 : Encl geo31 (cellStart 31) (pieceStop 31 : ℝ) where
  one_lt := by
    rw [cellStart_31]
    norm_num
  le := by
    rw [cellStart_31, pieceStop_31]
    norm_num
  lx_lo := by
    rw [cellStart_31]
    have h := (log_two_pow_mem 40).1
    push_cast at h
    simp only [geo31]
    push_cast
    linarith
  lx_hi := by
    rw [cellStart_31]
    have h := (log_two_pow_mem 40).2
    push_cast at h
    simp only [geo31]
    push_cast
    linarith
  lY_lo := by
    rw [show ((pieceStop 31 : ℕ) : ℝ) = (2 : ℝ) ^ 45 by rw [pieceStop_31]; push_cast; ring]
    have h := (log_two_pow_mem 45).1
    push_cast at h
    simp only [geo31]
    push_cast
    linarith
  lY_hi := by
    rw [show ((pieceStop 31 : ℕ) : ℝ) = (2 : ℝ) ^ 45 by rw [pieceStop_31]; push_cast; ring]
    have h := (log_two_pow_mem 45).2
    push_cast at h
    simp only [geo31]
    push_cast
    linarith
  checks := checks_31

/-- **The cell bounds of piece 31** (`eq:record:cell-charge`, `d = 2, 3`, at `a_T`). -/
theorem cellBound_le_31 :
    cellBound (paperPiece 31) Sarkozy.TargetLedger.targetDecay 1
        (2411 / (5000000 * Real.log ((paperPiece 31).x 0))) ≤ (cellK_31.1 : ℝ) ∧
      cellBound (paperPiece 31) Sarkozy.TargetLedger.targetDecay (3 / 2)
        (2411 / (5000000 * Real.log ((paperPiece 31).x 0))) ≤ (cellK_31.2 : ℝ) := by
  have hstop : XCh < pieceStop 31 := by decide +kernel
  obtain ⟨hn, hx, hnc⟩ := paperPiece_fields 31 (n := geo31.n) hstop cellCount_31
  rw [← aQ_eq]
  have h2 : (geo31.bound2 : ℝ) ≤ (cellK_31.1 : ℝ) := by exact_mod_cast bound2_31
  have h3 : (geo31.bound3 : ℝ) ≤ (cellK_31.2 : ℝ) := by exact_mod_cast bound3_31
  exact ⟨(encl_31.cellBound_le_bound2 _ hn hx hnc (by decide +kernel)).trans h2,
    (encl_31.cellBound_le_bound3 _ hn hx hnc (by decide +kernel)).trans h3⟩

end Sarkozy.AnalyticCells
