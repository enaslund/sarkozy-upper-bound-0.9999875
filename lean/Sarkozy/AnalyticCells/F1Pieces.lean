module

public import Sarkozy.AnalyticCells.F1Charge
public import Sarkozy.AnalyticCells.F1Checks
public import Sarkozy.AnalyticCells.F1Bound2
public import Sarkozy.AnalyticCells.F1Bound3
public import Sarkozy.AnalyticCells.F1Costs
public import Sarkozy.AnalyticCells.Piece29
public import Sarkozy.AnalyticCells.Piece30
public import Sarkozy.AnalyticCells.Piece31
public import Sarkozy.AnalyticCells.Piece32

@[expose] public section

/-!
# The 66 analytic charge bounds of the F1 partition

`lem:record:block-charge`(i), `eq:record:cell-charge`, at `a_T`, on every middle piece; `thm:bmor`
(H2) above `X_Ch`, `ThetaSmallRR` (H2″, Ramaré–Rumely Thm 5.2.1, `1.174 √x` for `x ≤ 10¹⁰`) below.

**`f1_charge_le`**: for every middle piece `i` and `d ∈ {2, 3}`, the charge `b_d(i)` of the F1
blocks is at most the rational `c'_d(i)` (`f1C2`, `f1C3`). The chain is
`b_d(i) ≤ pieceCharge (f1Piece i)` (`f1_blockCharge_le`) `≤ cellBound (f1Piece i) a_T (d/2) 𝖾_i`
(M2's `piece_charge_le`) `≤ bound ≤ c'_d(i)` (`GeoCells`, `Chord`, kernel checks), with
* `𝖾_i = 1.174/⌊√X_i⌋` on the pieces `0–27` (`|θ(t) − t/2| ≤ 1.174 √t ≤ (1.174/√X_i) t`);
* `𝖾_28 = 2411/(5·10⁶ log 4800162889)` on `[2³², 2³⁴]` (RR below `10¹⁰`, `thm:bmor` above);
* `thm:bmor`'s `2411/(5·10⁶ log x_0)` on the pieces `29–32`.
No histogram and no sieve enter.
-/

open Finset

namespace Sarkozy.AnalyticCells

open Sarkozy.PartV Sarkozy.CancellationSteps Sarkozy.PartVLaws Sarkozy.FirstStagePaper
  Sarkozy.BlockSpecPaper Sarkozy.PaperNumbers Sarkozy.MainTarget Sarkozy.Misc
open Sarkozy.TargetLedger (targetDecay)

/-! ## The logarithms of the endpoints -/

theorem f1Ends_check : ∀ k : Fin 30, |f1Lo k.val| ≤ 64 ∧ |-f1Hi k.val| ≤ 64 ∧
    expUpQ (f1Lo k.val) ≤ (f1End k.val : ℚ) ∧ (f1End k.val : ℚ) * expUpQ (-f1Hi k.val) ≤ 1 ∧
    0 < f1End k.val := by
  decide +kernel

theorem f1_log_mem {k : ℕ} (hk : k < 30) :
    (f1Lo k : ℝ) ≤ Real.log (f1End k : ℝ) ∧ Real.log (f1End k : ℝ) ≤ (f1Hi k : ℝ) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := f1Ends_check ⟨k, hk⟩
  have h5' : (0 : ℝ) < (f1End k : ℝ) := by exact_mod_cast h5
  apply log_mem h5' h1 h2
  · have : ((expUpQ (f1Lo k) : ℚ) : ℝ) ≤ (((f1End k : ℚ) : ℚ) : ℝ) := by exact_mod_cast h3
    simpa using this
  · have : (((f1End k : ℚ) * expUpQ (-f1Hi k) : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := by exact_mod_cast h4
    push_cast at this
    exact this

theorem f1End_eq : ∀ i : Fin 33, i.val < 29 →
    f1End i.val = f1XN i ∧ f1End (i.val + 1) = pieceStop i ∧ (2 : ℚ) ≤ f1Lo i.val ∧
      (f1Cells.getD i.val 1 = nF1 i) := by
  decide +kernel

theorem lBlo_check : |lBlo| ≤ 64 ∧ expUpQ lBlo ≤ 4800162889 := by decide +kernel

theorem f1Sqrt_check : ∀ i : Fin 28, 0 < f1Sqrt.getD i.val 1 ∧
    (f1Sqrt.getD i.val 1) ^ 2 ≤ f1End i.val ∧ f1End (i.val + 1) ≤ 2 ^ 32 := by
  decide +kernel

/-- RR's constant on `[2³², 2³⁴]` is below `𝖾_28`. -/
theorem rr28_check : (1174 / 1000 : ℚ) / 65536 ≤ 2411 / (5000000 * lBlo) := by decide +kernel

/-! ## The error constants -/

theorem f1_theta_low {i : Fin 33} (hi : i.val < 28) (hRR : Target.ThetaSmallRR) {t : ℝ}
    (h1 : (f1XN i : ℝ) ≤ t) (h2 : t ≤ (pieceStop i : ℝ)) :
    |Target.theta4 t 3 - t / 2| ≤ (f1Err i.val : ℝ) * t := by
  obtain ⟨hs0, hs2, hY⟩ := f1Sqrt_check ⟨i.val, hi⟩
  obtain ⟨hX, hYe, -, -⟩ := f1End_eq i (by omega)
  set s := f1Sqrt.getD i.val 1
  have hX1 : (1 : ℝ) ≤ (f1XN i : ℝ) := by
    have := (f1XN_facts i).2.2.1
    exact_mod_cast this.le
  have ht10 : t ≤ 10 ^ 10 := by
    have : (pieceStop i : ℝ) ≤ 2 ^ 32 := by
      rw [← hYe]
      exact_mod_cast hY
    linarith
  have h := (hRR t (by linarith) ht10).trans
    (sqrt_le_div_sqrt_mul (C := 1174 / 1000) (by norm_num) hX1 h1)
  have hs : (s : ℝ) ≤ Real.sqrt (f1XN i : ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    rw [← hX]
    exact_mod_cast hs2
  have hs0' : (0 : ℝ) < s := by exact_mod_cast hs0
  have herr : (f1Err i.val : ℝ) = 1174 / 1000 / (s : ℝ) := by
    unfold f1Err
    simp only [hi, ↓reduceIte]
    push_cast
    ring
  rw [herr]
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
  exact div_le_div_of_nonneg_left (by norm_num) hs0' hs

theorem f1_theta_28 (hB : Target.BMOR) (hRR : Target.ThetaSmallRR) {t : ℝ}
    (h1 : ((2 : ℝ) ^ 32) ≤ t) (_h2 : t ≤ 2 ^ 34) :
    |Target.theta4 t 3 - t / 2| ≤ (f1Err 28 : ℝ) * t := by
  have herr : (f1Err 28 : ℝ) = 2411 / (5000000 * (lBlo : ℝ)) := by
    unfold f1Err
    norm_num
  rw [herr]
  have hl0 : (0 : ℝ) < lBlo := by unfold lBlo; norm_num
  rcases le_or_gt t (10 ^ 10) with ht | ht
  · have h := (hRR t (by linarith) ht).trans
      (sqrt_le_div_sqrt_mul (C := 1174 / 1000) (by norm_num) (by norm_num : (1 : ℝ) ≤ 2 ^ 32) h1)
    have hsq : Real.sqrt ((2 : ℝ) ^ 32) = 65536 := by
      rw [show ((2 : ℝ) ^ 32) = 65536 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hsq] at h
    have hc : ((1174 / 1000 / 65536 : ℚ) : ℝ) ≤ ((2411 / (5000000 * lBlo) : ℚ) : ℝ) := by
      exact_mod_cast rr28_check
    push_cast at hc
    exact h.trans (mul_le_mul_of_nonneg_right hc (by linarith))
  · have h := bmor_eta_le hB (x := (4800162889 : ℝ)) (t := t) le_rfl (by linarith)
    have hlog : (lBlo : ℝ) ≤ Real.log 4800162889 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have h1 := exp_le_expUpQ lBlo_check.1
      have h2 : ((expUpQ lBlo : ℚ) : ℝ) ≤ ((4800162889 : ℚ) : ℝ) := by exact_mod_cast lBlo_check.2
      push_cast at h2
      exact h1.trans h2
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    linarith

/-! ## The cells of `f1Piece i` -/

theorem f1Piece_cellsOK (i : Fin 33) : CellsOK (f1Piece i) := by
  obtain ⟨hev1, hev2, h1, h2, -⟩ := f1XN_facts i
  have hN1 := one_le_f1N i
  have hx1 : (1 : ℝ) < (f1XN i : ℝ) := by exact_mod_cast h1
  have hxY : (f1XN i : ℝ) ≤ (pieceStop i : ℝ) := by exact_mod_cast h2.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [f1Piece, Misc.cellPoint_zero]
    exact hx1
  · intro j _
    exact Misc.cellPoint_mono (by linarith) hxY _ _
  · intro j hj
    exact Misc.notPrime3_cellPoint hev1 hev2 hN1 hj
  · intro j hj
    simp only [f1Piece]
    obtain ⟨hlo, hhi⟩ := cellPoint_le_top (by linarith) hxY hN1 (by exact hj)
    have hlc : 0 < Real.log (cellPoint (f1XN i : ℝ) (pieceStop i : ℝ) (f1N i) (j + 1)) :=
      Real.log_pos (by linarith)
    have hlY : Real.log (cellPoint (f1XN i : ℝ) (pieceStop i : ℝ) (f1N i) (j + 1)) ≤
        (middleBudget : ℝ) := by
      have h1 := Real.log_le_log (by linarith) hhi
      have h2 := log_siteStop_lt (.inl i)
      have h3 : (355 : ℝ) ≤ middleBudget := by norm_num [middleBudget]
      exact h1.trans ((le_of_lt h2).trans h3)
    unfold cellCard
    rw [Nat.one_le_floor_iff, one_le_div hlc]
    exact hlY

theorem f1Piece_partsOK (i : Fin 33) : PartsOK binU (f1Piece i) := by
  intro ps hps
  simp [f1Piece] at hps

theorem f1Piece_top (i : Fin 33) : (f1Piece i).x (f1Piece i).n = (pieceStop i : ℝ) :=
  Misc.cellPoint_self (one_le_f1N i)

/-! ## The pieces `0–28` -/

theorem f1_encl {i : Fin 33} (hi : i.val < 29) :
    Encl (f1Geo i.val) (f1XN i : ℝ) (pieceStop i : ℝ) := by
  obtain ⟨hX, hY, -, -⟩ := f1End_eq i hi
  obtain ⟨-, -, h1, h2, -⟩ := f1XN_facts i
  have hl0 := f1_log_mem (k := i.val) (by omega)
  have hl1 := f1_log_mem (k := i.val + 1) (by omega)
  rw [hX] at hl0
  rw [hY] at hl1
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2.le, hl0.1, hl0.2, hl1.1, hl1.2,
    f1_checks ⟨i.val, hi⟩⟩

theorem f1Piece_fields {i : Fin 33} (hi : i.val < 29) :
    (f1Piece i).n = (f1Geo i.val).n ∧
      (f1Piece i).x = cellPoint (f1XN i : ℝ) (pieceStop i : ℝ) (f1Geo i.val).n ∧
      (f1Piece i).nc = cellCard 570 (f1XN i : ℝ) (pieceStop i : ℝ) (f1Geo i.val).n := by
  obtain ⟨-, -, -, hc⟩ := f1End_eq i hi
  have hn : f1N i = (f1Geo i.val).n := by
    unfold f1N
    simp only [hi, ↓reduceIte]
    exact hc.symm
  have hb : ((middleBudget : ℕ) : ℝ) = 570 := by unfold middleBudget; norm_num
  refine ⟨hn, ?_, ?_⟩
  · simp only [f1Piece]
    rw [hn]
  · simp only [f1Piece]
    rw [hn, hb]

theorem f1_cell_low {i : Fin 33} (hi : i.val < 29) {e : ℝ} (he0 : 0 ≤ e)
    (he : e ≤ (f1Err i.val : ℝ)) :
    cellBound (f1Piece i) targetDecay 1 e ≤ f1c2 i ∧
      cellBound (f1Piece i) targetDecay (3 / 2) e ≤ f1c3 i := by
  have H := f1_encl hi
  obtain ⟨hPn, hPx, hPnc⟩ := f1Piece_fields hi
  obtain ⟨-, -, h2, -⟩ := f1End_eq i hi
  rw [← aQ_eq]
  have he' : e ≤ ((f1Geo i.val).ehi : ℝ) := he
  have b2 : ((f1Geo i.val).bound2 : ℝ) ≤ f1c2 i := by
    unfold f1c2
    exact_mod_cast f1_bound2 ⟨i.val, hi⟩
  have b3 : ((f1Geo i.val).bound3c : ℝ) ≤ f1c3 i := by
    unfold f1c3
    exact_mod_cast f1_bound3 ⟨i.val, hi⟩
  exact ⟨(H.cellBound_le_bound2_e _ hPn hPx hPnc he0 he').trans b2,
    (H.cellBound_le_bound3c_e h2 _ hPn hPx hPnc he0 he').trans b3⟩

end Sarkozy.AnalyticCells
