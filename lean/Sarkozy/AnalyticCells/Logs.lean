module

public import Sarkozy.AnalyticCells.GeoCells
public import Sarkozy.PaperNumbers.Checks

@[expose] public section

/-!
# The logarithms of the piece endpoints above `X_Ch`, and the pieces in M2's form

`def:record:exact-blocks`(a), (d), `tab:record:middle-pieces`.

* `log_mem`: `lo ≤ log X ≤ hi` from the two kernel-checkable inequalities `expUpQ lo ≤ X` and
  `X · expUpQ(-hi) ≤ 1`. It gives 25-digit enclosures of `log 2`, `log X_Ch` and `log 167`, hence of
  `log` of every piece endpoint above `X_Ch` (`2³⁴, 2³⁶, 2⁴⁰, 2⁴⁵, 167·2⁴⁰`).
* `paperPiece_fields`: for `28 ≤ i ≤ 32`, N1's `paperPiece i` has `𝗇 = (geo i).n` cells, the cell
  points `cellPoint (cellStart i) (pieceStop i) 𝗇` and the cardinalities
  `cellCard 570 (cellStart i) (pieceStop i) 𝗇` (`def:record:exact-blocks`(d)), so the soundness
  theorems of `GeoCells.lean` apply to it.
-/

namespace Sarkozy.AnalyticCells

open Sarkozy.Misc Sarkozy.PartV Sarkozy.PaperNumbers

/-- **Logarithm enclosures by the exponential bound.** -/
theorem log_mem {X : ℝ} (hX : 0 < X) {lo hi : ℚ} (hlo : |lo| ≤ 64) (hhi : |-hi| ≤ 64)
    (h1 : (expUpQ lo : ℝ) ≤ X) (h2 : X * (expUpQ (-hi) : ℝ) ≤ 1) :
    (lo : ℝ) ≤ Real.log X ∧ Real.log X ≤ hi := by
  constructor
  · rw [Real.le_log_iff_exp_le hX]
    exact (exp_le_expUpQ hlo).trans h1
  · rw [Real.log_le_iff_le_exp hX]
    have h3 := exp_le_expUpQ hhi
    push_cast at h3
    have h4 : X * Real.exp (-(hi : ℝ)) ≤ 1 := (mul_le_mul_of_nonneg_left h3 hX.le).trans h2
    have h5 : Real.exp (-(hi : ℝ)) * Real.exp (hi : ℝ) = 1 := by
      rw [← Real.exp_add]
      simp
    have h6 := Real.exp_pos (hi : ℝ)
    nlinarith

theorem log_two_mem : (l2lo : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (l2hi : ℝ) := by
  have h := log_mem (X := 2) (by norm_num) (lo := l2lo) (hi := l2hi)
    (by unfold l2lo; norm_num [abs_le]) (by unfold l2hi; norm_num [abs_le])
    (by have : expUpQ l2lo ≤ 2 := by decide +kernel
        exact_mod_cast this)
    (by have : 2 * expUpQ (-l2hi) ≤ 1 := by decide +kernel
        exact_mod_cast this)
  exact h

theorem log_XCh_mem : (lXChlo : ℝ) ≤ Real.log (XCh : ℝ) ∧ Real.log (XCh : ℝ) ≤ (lXChhi : ℝ) := by
  have h := log_mem (X := (XCh : ℝ)) (by unfold XCh; norm_num) (lo := lXChlo) (hi := lXChhi)
    (by unfold lXChlo; norm_num [abs_le]) (by unfold lXChhi; norm_num [abs_le])
    (by have : expUpQ lXChlo ≤ 4800162890 := by decide +kernel
        have h' : ((expUpQ lXChlo : ℚ) : ℝ) ≤ ((4800162890 : ℚ) : ℝ) := by exact_mod_cast this
        unfold XCh
        push_cast at h' ⊢
        exact h')
    (by have : 4800162890 * expUpQ (-lXChhi) ≤ 1 := by decide +kernel
        have h' : (((4800162890 : ℚ) * expUpQ (-lXChhi) : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := by
          exact_mod_cast this
        unfold XCh
        push_cast at h' ⊢
        exact h')
  exact h

theorem log_167_mem : (l167lo : ℝ) ≤ Real.log 167 ∧ Real.log 167 ≤ (l167hi : ℝ) := by
  have h := log_mem (X := 167) (by norm_num) (lo := l167lo) (hi := l167hi)
    (by unfold l167lo; norm_num [abs_le]) (by unfold l167hi; norm_num [abs_le])
    (by have : expUpQ l167lo ≤ 167 := by decide +kernel
        exact_mod_cast this)
    (by have : 167 * expUpQ (-l167hi) ≤ 1 := by decide +kernel
        exact_mod_cast this)
  exact h

theorem log_two_pow_mem (b : ℕ) :
    ((b * l2lo : ℚ) : ℝ) ≤ Real.log ((2 : ℝ) ^ b) ∧
      Real.log ((2 : ℝ) ^ b) ≤ ((b * l2hi : ℚ) : ℝ) := by
  rw [Real.log_pow]
  push_cast
  have h := log_two_mem
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  exact ⟨mul_le_mul_of_nonneg_left h.1 hb, mul_le_mul_of_nonneg_left h.2 hb⟩

theorem log_167_pow_mem :
    ((l167lo + 40 * l2lo : ℚ) : ℝ) ≤ Real.log (167 * (2 : ℝ) ^ 40) ∧
      Real.log (167 * (2 : ℝ) ^ 40) ≤ ((l167hi + 40 * l2hi : ℚ) : ℝ) := by
  rw [Real.log_mul (by norm_num) (by positivity)]
  have h1 := log_167_mem
  have h2 := log_two_pow_mem 40
  push_cast at h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-! ## The pieces above `X_Ch` in M2's form -/

theorem pieceStart_28 : pieceStart 28 = 2 ^ 32 := by decide +kernel
theorem pieceStart_29 : pieceStart 29 = 2 ^ 34 := by decide +kernel
theorem pieceStart_30 : pieceStart 30 = 2 ^ 36 := by decide +kernel
theorem pieceStart_31 : pieceStart 31 = 2 ^ 40 := by decide +kernel
theorem pieceStart_32 : pieceStart 32 = 2 ^ 45 := by decide +kernel
theorem pieceStop_28 : pieceStop 28 = 2 ^ 34 := by decide +kernel
theorem pieceStop_29 : pieceStop 29 = 2 ^ 36 := by decide +kernel
theorem pieceStop_30 : pieceStop 30 = 2 ^ 40 := by decide +kernel
theorem pieceStop_31 : pieceStop 31 = 2 ^ 45 := by decide +kernel
theorem pieceStop_32 : pieceStop 32 = 167 * 2 ^ 40 := by decide +kernel

/-- `paperPiece i` for a piece above `X_Ch` with `𝗇` cells is the geometric piece of
`[cellStart i, pieceStop i)`. -/
theorem paperPiece_fields (i : Fin 33) {n : ℕ} (hstop : XCh < pieceStop i)
    (hn : cellCount (cellStart i) (pieceStop i) = n) :
    (paperPiece i).n = n ∧ (paperPiece i).x = cellPoint (cellStart i) (pieceStop i) n ∧
      (paperPiece i).nc = cellCard 570 (cellStart i) (pieceStop i) n := by
  have hb : ((middleBudget : ℕ) : ℝ) = 570 := by unfold middleBudget; norm_num
  refine ⟨?_, ?_, ?_⟩
  · simp only [paperPiece, cellNum, hstop, ↓reduceIte]
    exact hn
  · simp only [paperPiece]
    rw [hn]
  · simp only [paperPiece]
    rw [hn, hb]

end Sarkozy.AnalyticCells
