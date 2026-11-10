module

public import Sarkozy.AnalyticCells.Piece28
public import Sarkozy.AnalyticCells.Piece29
public import Sarkozy.AnalyticCells.Piece30
public import Sarkozy.AnalyticCells.Piece31
public import Sarkozy.AnalyticCells.Piece32

@[expose] public section

/-!
# The cell bounds discharged, and the main statement without `CellClaim`

`paper/sections/20_middle_reference.tex`, `lem:record:block-charge`(i), `eq:record:cell-charge`;
`paper/sections/D_certificates.tex`, `cert:record:middle-price`(c).

* **`cellClaimN2`** (proved): for the five pieces above `X_Ch` and `d ∈ {2, 3}`, M2's cell bound
  `cellBound (paperPiece i) a_T (d/2) 𝖾_{x_0}` is at most the rational `cellK d i`. This is N1's
  `CellClaim` with the constants `cellK` in place of the pipeline's `cellC`: `cellK` is our own
  rigorous bound, larger than `cellC` by about `10⁻⁷` (relative) at `d = 2` and `0.85–1.2·10⁻⁴` at
  `d = 3` (there the pipeline bounds `I_j(3/2)` with the secant of `1/log t`, we with `1/log x_j`).
  So N1's `CellClaim` itself, with the constants `cellC`, is **not** proved; it is not needed.
* **`exact_cellK_le_charge`** (`decide +kernel`): on the pieces `28–32`, the exact part from the
  histogram plus `cellK` is still at most N1's `c_d(i)`.
* **`pieceBound_le_charge_N2`**: the 66 bounds `pieceBound a_T d i ≤ c_d(i)` from `HistogramClaim`
  alone.
* **`main_target_paper_joint_N2`**: N1's `main_target_paper_joint_N1_hist` without `CellClaim`.
-/

namespace Sarkozy.AnalyticCells

open Finset
open Sarkozy.Misc Sarkozy.PartV Sarkozy.PaperNumbers Sarkozy.BlockSpecPaper Sarkozy.PartVLaws
open Sarkozy.TargetLedger (targetDecay targetLedger)

/-- The constant of degree `d` from a pair. -/
def cellKd (d : ℕ) (k : ℚ × ℚ) : ℚ := if d = 2 then k.1 else k.2

/-- **Our cell constants** (`0` below piece 28). -/
def cellK (d : ℕ) (i : Fin 33) : ℚ :=
  if i.val = 28 then cellKd d cellK_28 else if i.val = 29 then cellKd d cellK_29
  else if i.val = 30 then cellKd d cellK_30 else if i.val = 31 then cellKd d cellK_31
  else if i.val = 32 then cellKd d cellK_32 else 0

theorem cellBound_le_pair {i : Fin 33} {k : ℚ × ℚ} {d : ℕ} (hd : d = 2 ∨ d = 3)
    (h : cellBound (paperPiece i) targetDecay 1
        (2411 / (5000000 * Real.log ((paperPiece i).x 0))) ≤ (k.1 : ℝ) ∧
      cellBound (paperPiece i) targetDecay (3 / 2)
        (2411 / (5000000 * Real.log ((paperPiece i).x 0))) ≤ (k.2 : ℝ)) :
    cellBound (paperPiece i) targetDecay ((d : ℝ) / 2)
      (2411 / (5000000 * Real.log ((paperPiece i).x 0))) ≤ (cellKd d k : ℝ) := by
  rcases hd with rfl | rfl
  · have : ((2 : ℕ) : ℝ) / 2 = 1 := by norm_num
    rw [this]
    simpa [cellKd] using h.1
  · have : ((3 : ℕ) : ℝ) / 2 = 3 / 2 := by norm_num
    rw [this]
    simpa [cellKd] using h.2

/-- **The cell bounds, proved** (`eq:record:cell-charge` with `thm:bmor`'s error, at `a_T`): N1's
`CellClaim` with our constants `cellK`. -/
theorem cellClaimN2 : ∀ i : Fin 33, 28 ≤ i.val → ∀ d : ℕ, (d = 2 ∨ d = 3) →
    cellBound (paperPiece i) targetDecay ((d : ℝ) / 2)
      (2411 / (5000000 * Real.log ((paperPiece i).x 0))) ≤ (cellK d i : ℝ) := by
  intro i hi d hd
  obtain ⟨v, hv⟩ := i
  simp only at hi
  have hcases : v = 28 ∨ v = 29 ∨ v = 30 ∨ v = 31 ∨ v = 32 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · simpa [cellK] using cellBound_le_pair hd cellBound_le_28
  · simpa [cellK] using cellBound_le_pair hd cellBound_le_29
  · simpa [cellK] using cellBound_le_pair hd cellBound_le_30
  · simpa [cellK] using cellBound_le_pair hd cellBound_le_31
  · simpa [cellK] using cellBound_le_pair hd cellBound_le_32

/-- **The checks on pieces `28–32`** (`decide +kernel`): exact part plus `cellK` at most
`c_d(i)`. -/
theorem exact_cellK_le_charge : ∀ i : Fin 33, 28 ≤ i.val →
    (exPieceN i 2 : ℚ) / ((unitD : ℚ) * 2 ^ 95) + cellK 2 i ≤ chargeC2 i ∧
      (exPieceN i 3 : ℚ) / ((unitD : ℚ) * 2 ^ 95) + cellK 3 i ≤ chargeC3 i := by
  decide +kernel

theorem cellC_low : ∀ i : Fin 33, i.val < 28 → cellC2 i = 0 ∧ cellC3 i = 0 := by decide +kernel

/-- The exact part of piece `i` from the histogram, plus any cell bound `c`. -/
theorem pieceBound_le_of_cell (hH : HistogramClaim) (i : Fin 33) {d : ℕ} (hd : d = 2 ∨ d = 3)
    {c : ℝ} (hc : cellBound (paperPiece i) targetDecay ((d : ℝ) / 2)
      (2411 / (5000000 * Real.log ((paperPiece i).x 0))) ≤ c) :
    pieceBound targetDecay d i ≤ (exPieceN i d : ℝ) / ((unitD : ℝ) * 2 ^ 95) + c := by
  unfold pieceBound
  apply add_le_add _ hc
  have h1 : ((paperPiece i).parts.map (exactBound binU targetDecay d)).sum =
      ((partsOf i).map fun k => exactBound binU targetDecay d (partList k)).sum := by
    simp only [paperPiece, List.map_map]
    rfl
  have h2 : ((partsOf i).map fun k => exactBound binU targetDecay d (partList k)).sum ≤
      ((partsIn i).map fun k => exactBound binU targetDecay d (partList k)).sum := by
    apply List.Sublist.sum_le_sum ((List.filter_sublist).map _)
    intro x hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
    exact exactBound_nonneg _ _ _
  have h3 : ((partsIn i).map fun k => exactBound binU targetDecay d (partList k)).sum ≤
      ((partsIn i).map fun k => (partSumN k d : ℝ) / ((unitD : ℝ) * 2 ^ 95)).sum := by
    apply List.sum_le_sum
    intro k hk
    have hk35 : k < 35 := by
      unfold partsIn at hk
      exact List.mem_range.mp (List.mem_filter.mp hk).1
    exact exactBound_le_hist hH hk35 hd
  have h4 : ((partsIn i).map fun k => (partSumN k d : ℝ) / ((unitD : ℝ) * 2 ^ 95)).sum =
      (exPieceN i d : ℝ) / ((unitD : ℝ) * 2 ^ 95) := by
    unfold exPieceN
    rw [list_sum_div_const, Nat.cast_list_sum, List.map_map]
    rfl
  rw [h1]
  exact h2.trans (h3.trans h4.le)

/-- **The 66 charge bounds** `pieceBound a_T d i ≤ c_d(i)` from the histogram certificate alone. -/
theorem pieceBound_le_charge_N2 (hH : HistogramClaim) (i : Fin 33) :
    pieceBound targetDecay 2 i ≤ chargeC2 i ∧ pieceBound targetDecay 3 i ≤ chargeC3 i := by
  rcases Nat.lt_or_ge i.val 28 with hi | hi
  · obtain ⟨h2, h3⟩ := exact_cell_le_charge i
    obtain ⟨c2, c3⟩ := cellC_low i hi
    have hc2 : cellC 2 i = 0 := by simp [cellC, c2]
    have hc3 : cellC 3 i = 0 := by simp [cellC, c3]
    rw [hc2, add_zero] at h2
    rw [hc3, add_zero] at h3
    have h2' : (((exPieceN i 2 : ℚ) / ((unitD : ℚ) * 2 ^ 95) : ℚ) : ℝ) ≤
        ((chargeC2 i : ℚ) : ℝ) := by
      exact_mod_cast h2
    have h3' : (((exPieceN i 3 : ℚ) / ((unitD : ℚ) * 2 ^ 95) : ℚ) : ℝ) ≤
        ((chargeC3 i : ℚ) : ℝ) := by
      exact_mod_cast h3
    push_cast at h2' h3'
    have e2 := pieceBound_le_of_cell hH i (Or.inl rfl) (le_of_eq (cellBound_low hi _ _ _))
    have e3 := pieceBound_le_of_cell hH i (Or.inr rfl) (le_of_eq (cellBound_low hi _ _ _))
    rw [add_zero] at e2 e3
    exact ⟨e2.trans h2', e3.trans h3'⟩
  · obtain ⟨h2, h3⟩ := exact_cellK_le_charge i hi
    have h2' : ((((exPieceN i 2 : ℚ) / ((unitD : ℚ) * 2 ^ 95) + cellK 2 i : ℚ)) : ℝ) ≤
        ((chargeC2 i : ℚ) : ℝ) := by exact_mod_cast h2
    have h3' : ((((exPieceN i 3 : ℚ) / ((unitD : ℚ) * 2 ^ 95) + cellK 3 i : ℚ)) : ℝ) ≤
        ((chargeC3 i : ℚ) : ℝ) := by exact_mod_cast h3
    push_cast at h2' h3'
    exact ⟨(pieceBound_le_of_cell hH i (Or.inl rfl) (cellClaimN2 i hi 2 (Or.inl rfl))).trans h2',
      (pieceBound_le_of_cell hH i (Or.inr rfl) (cellClaimN2 i hi 3 (Or.inr rfl))).trans h3'⟩

open Sarkozy.JointClosing Sarkozy.FirstStagePaper in
/-- **The main statement at `ε = a_T/71` at the paper's partition, with `hB` and `hL₀` from the
histogram certificate alone** (`thm:main` at `ε = a_T/71`, `cor:joint-closing`,
`lem:record:block-charge`, `cert:record:middle-price`(b); the cell bounds
`eq:record:cell-charge` of `cert:record:middle-price`(c) are proved, `cellClaimN2`): N1's
`main_target_paper_joint_N1_hist` without `CellClaim`. Hypotheses: H1, H2, H4, H5, `thm:dl:K`, H2″,
the lemma families `hU`, `hM`, `hI`, the **histogram certificate** `HistogramClaim`, and the 9
fields `Dv` (`CL`, `ME`, `SM`), `hT`, `hSA`, `JB`, `SF`, `fix`, `env`. -/
theorem main_target_paper_joint_N2 (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (hU : ∀ k, UpperBandLemma k) (hM : ∀ i, allpIndividual i = none → MiddleUniformLemma i)
    (hI : ∀ i u, allpIndividual i = some u → MiddleIndividualLemma i u)
    (Dv : N1JointBlockData hWeil hMovingRoot hFourCycle hU hM hI)
    (hHist : HistogramClaim)
    (hT : Dv.toJoint.data.ME.T ≤ targetLedger.T)
    (hSA : Dv.toJoint.data.CL.S + Dv.toJoint.data.CL.A ≤ targetLedger.S + targetLedger.A)
    (JB : JointBound Dv.toJoint.data targetLedger.jointConstant)
    (SF : EnvelopeInputsBlock.SharpFirstInputs Dv.toJoint.data)
    (fix : EnvelopeInputsBlock.FixedIntervalInputs
      (BlockAnchor.index_coprime_block Dv.toJoint.data) Dv.toJoint.data)
    (env : EnvelopeInputsBlock.EnvelopeEnergyInputs
      (BlockAnchor.index_coprime_block Dv.toJoint.data) Dv.toJoint.data) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_joint_N1_final hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR
    hU hM hI Dv (fun i => (pieceBound_le_charge_N2 hHist i).1)
    (fun i => (pieceBound_le_charge_N2 hHist i).2) hT hSA JB SF fix env

end Sarkozy.AnalyticCells
