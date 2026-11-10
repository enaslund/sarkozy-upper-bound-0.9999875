module

public import Sarkozy.AnalyticCells.Logs

@[expose] public section

/-!
# The cell bounds of piece 32, `[2⁴⁵, 167·2⁴⁰)` (306 cells)

`lem:record:block-charge`(i), `eq:record:cell-charge` at `a_T`, `def:record:exact-blocks`(d).

The kernel checks `Checks` (the cardinalities `n_j = ⌊570/log x_{j+1}⌋` and the ranges) and the two
rational sums `bound2 ≤ c₂`, `bound3 ≤ c₃` (`decide +kernel`); then **`cellBound_le_32`**: M2's cell
bound of N1's `paperPiece 32` at `a_T`, with `thm:bmor`'s error, is at most `c₂` at `s = 1` and `c₃`
at `s = 3/2`. The constants `c_d` are `⌈10³⁰ bound_d⌉/10³⁰` (computed by `#eval`; untrusted, checked
here).
-/

namespace Sarkozy.AnalyticCells

open Sarkozy.Misc Sarkozy.PartV Sarkozy.PaperNumbers

theorem checks_32 : geo32.Checks = true := by decide +kernel

/-- The cell constants of piece 32 at `s = 1` and `s = 3/2`. -/
def cellK_32 : ℚ × ℚ := (3276731024180767137135061909 / 10 ^ 30, 375894930307428738876 / 10 ^ 30)

theorem bound2_32 : geo32.bound2 ≤ cellK_32.1 := by decide +kernel

theorem bound3_32 : geo32.bound3 ≤ cellK_32.2 := by decide +kernel

theorem cellStart_32 : cellStart 32 = (2 : ℝ) ^ 45 := by
  unfold cellStart
  rw [pieceStart_32, max_eq_left (by norm_num [XCh])]
  push_cast
  ring

theorem encl_32 : Encl geo32 (cellStart 32) (pieceStop 32 : ℝ) where
  one_lt := by
    rw [cellStart_32]
    norm_num
  le := by
    rw [cellStart_32, pieceStop_32]
    norm_num
  lx_lo := by
    rw [cellStart_32]
    have h := (log_two_pow_mem 45).1
    push_cast at h
    simp only [geo32]
    push_cast
    linarith
  lx_hi := by
    rw [cellStart_32]
    have h := (log_two_pow_mem 45).2
    push_cast at h
    simp only [geo32]
    push_cast
    linarith
  lY_lo := by
    rw [show ((pieceStop 32 : ℕ) : ℝ) = 167 * (2 : ℝ) ^ 40 by rw [pieceStop_32]; push_cast; ring]
    have h := log_167_pow_mem.1
    push_cast at h
    simp only [geo32]
    push_cast
    linarith
  lY_hi := by
    rw [show ((pieceStop 32 : ℕ) : ℝ) = 167 * (2 : ℝ) ^ 40 by rw [pieceStop_32]; push_cast; ring]
    have h := log_167_pow_mem.2
    push_cast at h
    simp only [geo32]
    push_cast
    linarith
  checks := checks_32

/-- **The cell bounds of piece 32** (`eq:record:cell-charge`, `d = 2, 3`, at `a_T`). -/
theorem cellBound_le_32 :
    cellBound (paperPiece 32) Sarkozy.TargetLedger.targetDecay 1
        (2411 / (5000000 * Real.log ((paperPiece 32).x 0))) ≤ (cellK_32.1 : ℝ) ∧
      cellBound (paperPiece 32) Sarkozy.TargetLedger.targetDecay (3 / 2)
        (2411 / (5000000 * Real.log ((paperPiece 32).x 0))) ≤ (cellK_32.2 : ℝ) := by
  have hstop : XCh < pieceStop 32 := by decide +kernel
  obtain ⟨hn, hx, hnc⟩ := paperPiece_fields 32 (n := geo32.n) hstop cellCount_32
  rw [← aQ_eq]
  have h2 : (geo32.bound2 : ℝ) ≤ (cellK_32.1 : ℝ) := by exact_mod_cast bound2_32
  have h3 : (geo32.bound3 : ℝ) ≤ (cellK_32.2 : ℝ) := by exact_mod_cast bound3_32
  exact ⟨(encl_32.cellBound_le_bound2 _ hn hx hnc (by decide +kernel)).trans h2,
    (encl_32.cellBound_le_bound3 _ hn hx hnc (by decide +kernel)).trans h3⟩

end Sarkozy.AnalyticCells
