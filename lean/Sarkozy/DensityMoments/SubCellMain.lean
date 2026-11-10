module

public import Sarkozy.DensityMoments.SubCellData1
public import Sarkozy.DensityMoments.SubCellData2
public import Sarkozy.DensityMoments.SubCellData3
public import Sarkozy.DensityMoments.SubCellData4
public import Sarkozy.DensityMoments.SubCellData5
public import Sarkozy.DensityMoments.SubCellData6






@[expose] public section

namespace Sarkozy.DensityMoments

/-- The sub-cell chain from `a` to `b`. -/
def chainOK : ℕ → List SubCellRow → ℕ → Bool
  | a, [], b => a == b
  | a, r :: rs, b => (r.beta == a) && decide (r.beta < r.yUp) && chainOK r.yUp rs b

/-- A chain of sub-cells from `a` to `b` covers `[a, b)`. -/
theorem chainOK_cover : ∀ (rows : List SubCellRow) (a b : ℕ), chainOK a rows b = true →
    ∀ m, a ≤ m → m < b → ∃ r ∈ rows, r.beta ≤ m ∧ m < r.yUp
  | [], a, b, h, m, hm1, hm2 => by
    simp only [chainOK, beq_iff_eq] at h
    omega
  | r :: rs, a, b, h, m, hm1, hm2 => by
    simp only [chainOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨hra, _⟩, hrest⟩ := h
    by_cases hm : m < r.yUp
    · exact ⟨r, List.mem_cons_self .., by omega, hm⟩
    · obtain ⟨r', hr', h1, h2⟩ := chainOK_cover rs r.yUp b hrest m (by omega) hm2
      exact ⟨r', List.mem_cons_of_mem _ hr', h1, h2⟩

/-- The sub-cells of the six pieces. -/
def subRowsOf : ℕ → List SubCellRow
  | 0 => subRowsPiece0
  | 1 => subRowsPiece1
  | 2 => subRowsPiece2
  | 3 => subRowsPiece3
  | 4 => subRowsPiece4
  | 5 => subRowsPiece5
  | _ => []

theorem subRowsOf_check : ∀ i, ∀ row ∈ subRowsOf i, row.Check (packetPiece row.piece) := by
  intro i row hrow
  match i, hrow with
  | 0, h => exact subRowsPiece0_check row h
  | 1, h => exact subRowsPiece1_check row h
  | 2, h => exact subRowsPiece2_check row h
  | 3, h => exact subRowsPiece3_check row h
  | 4, h => exact subRowsPiece4_check row h
  | 5, h => exact subRowsPiece5_check row h

/-- The piece starts `X` and ends `Y` of the six pieces. -/
def pieceStart (i : ℕ) : ℕ := (packetPiece i).X
def pieceEnd : ℕ → ℕ
  | 0 => 21757358 | 1 => 23726568 | 2 => 25429506 | 3 => 25874006 | 4 => 28215802
  | 5 => 33554432 | _ => 0

/-- **The sub-cells of each piece tile it**, every sub-cell belongs to its piece, and its upper
bound for the primes is the piece end. -/
theorem subRows_chain : ∀ i < 6, chainOK (pieceStart i) (subRowsOf i) (pieceEnd i) = true ∧
    ∀ row ∈ subRowsOf i, row.piece = i ∧ row.pieceY = pieceEnd i := by
  decide +kernel

/-- The number of sub-cells: `511, 256, 256, 256, 256, 256`. -/
theorem subRows_count : (List.range 6).map (fun i => (subRowsOf i).length) =
    [511, 256, 256, 256, 256, 256] := by
  decide +kernel

/-- **The cell-based joint block-size gates, under `ThetaSmall`.** -/
theorem cell_gates (hθ : Target.ThetaSmall) {i : ℕ} (hi : i < 6) {B : Finset ℕ}
    {hB : B.Nonempty} (hc : ConsecBlock B hB) (hlo : pieceStart i ≤ B.min' hB)
    (hhi : B.min' hB < pieceEnd i) (hY : B.max' hB < pieceEnd i) :
    ∃ row ∈ subRowsOf i, row.beta ≤ B.min' hB ∧ B.min' hB < row.yUp ∧
      (B.card = row.n →
        Real.log (∏ p ∈ B, (p : ℝ)) ≤ (row.gate.L : ℝ) ∧
        ∀ b : ℝ, (row.beta : ℝ) ≤ b →
          Real.exp (-((row.gate.L : ℝ) * (1 - (kappaStar : ℝ)))) < kappaStar ∧
          (packetPiece i).sym (1 / Real.sqrt b) * (1 + mixtureBound row.gate.L) < 1 ∧
          (packetPiece i).skew (1 / Real.sqrt b) * (1 + mixtureBound row.gate.L) < 1) := by
  obtain ⟨hchain, hrows⟩ := subRows_chain i hi
  obtain ⟨row, hrow, h1, h2⟩ := chainOK_cover _ _ _ hchain (B.min' hB) hlo hhi
  refine ⟨row, hrow, h1, h2, fun hcard => ?_⟩
  obtain ⟨hpi, hpY⟩ := hrows row hrow
  have hcheck := subRowsOf_check i row hrow
  have hlt : row.piece < 33 := by omega
  have hP := packetPiece_valid row.piece hlt
  rw [hpi] at hcheck hP
  have h := row.sound hθ hP hcheck hc hcard h1 h2 (by rw [hpY]; exact hY)
  exact h

end Sarkozy.DensityMoments
