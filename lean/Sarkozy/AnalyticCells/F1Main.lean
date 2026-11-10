module

public import Sarkozy.AnalyticCells.F1Pieces
public import Sarkozy.BlockSpecPaper.Joint

@[expose] public section

/-!
# The main statement at the F1 partition, with no histogram

`thm:main` at `ε = a_T/71`, `cor:joint-closing`, `def:construction`(b), `lem:record:block-charge`,
`lem:record:middle-prices`, `def:closing-quantities`(2), (3).

At the F1 partition `f1Cell` (R1's analytic cells below `X_Ch`, the configuration of T1's ledger;
`F1Cell.lean`):
* **`f1_charge_le`**: the 66 charge bounds `b_d(i) ≤ c'_d(i)` are proved from `thm:bmor` (H2) and
  `ThetaSmallRR` (H2″) alone (`F1Pieces.lean`): no sieve, no histogram, no `HistogramClaim`;
* the first-stage sums are N1's `sum_pvar_le`, `sum_dTag_le`, `sum_vTag_le` (generic in the rule);
* the cost inequalities are `f1_costB_le`, `f1_costL_le` against T1's ledger `B`, `L₀`.

**`main_target_f1`**: `Target.SarkozyBound TargetLedger.targetSaving` from H1, H2, H4, H5,
`thm:dl:K`, H2″,
B1's lemma families `hU`, `hM`, `hI`, and the 9 Part V fields at the F1 partition: `Dv` (`CL`,
`ME`, `SM`), `hT`, `hSA`, `JB`, `SF`, `fix`, `env`. `hB` and `hL₀` are discharged.
-/

open Finset

namespace Sarkozy.AnalyticCells

open Sarkozy.PartV Sarkozy.CancellationSteps Sarkozy.PartVLaws Sarkozy.FirstStagePaper
  Sarkozy.BlockSpecPaper Sarkozy.PaperNumbers Sarkozy.MainTarget Sarkozy.Misc
  Sarkozy.JointClosing Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.GramBracketPaper
open Sarkozy.TargetLedger (targetDecay targetLedger)

/-! ## The pieces `29–32` -/

theorem f1_cell_high {i : Fin 33} (hi : 29 ≤ i.val) {G : GeoQ}
    (H : Encl G (cellStart i) (pieceStop i : ℝ)) (hn : cellCount (cellStart i) (pieceStop i) = G.n)
    (herr : G.err = 2411 / (5000000 * G.Llo 0)) (h2 : (2 : ℚ) ≤ G.lxl)
    (b2 : G.bound2 ≤ f1C2 i.val) (b3 : G.bound3c ≤ f1C3 i.val) :
    cellBound (f1Piece i) targetDecay 1
        (2411 / (5000000 * Real.log ((f1Piece i).x 0))) ≤ f1c2 i ∧
      cellBound (f1Piece i) targetDecay (3 / 2)
        (2411 / (5000000 * Real.log ((f1Piece i).x 0))) ≤ f1c3 i := by
  have hX : ((f1XN i : ℕ) : ℝ) = cellStart i := by
    rw [cellStart_eq]
    unfold f1XN
    simp only [show ¬ i.val < 29 by omega, ↓reduceIte]
  have hN : f1N i = G.n := by
    unfold f1N
    simp only [show ¬ i.val < 29 by omega, ↓reduceIte]
    exact hn
  have hb : ((middleBudget : ℕ) : ℝ) = 570 := by unfold middleBudget; norm_num
  have hPn : (f1Piece i).n = G.n := hN
  have hPx : (f1Piece i).x = cellPoint (cellStart i) (pieceStop i : ℝ) G.n := by
    simp only [f1Piece]
    rw [hX, hN]
  have hPnc : (f1Piece i).nc = cellCard 570 (cellStart i) (pieceStop i : ℝ) G.n := by
    simp only [f1Piece]
    rw [hX, hN, hb]
  have h0 : (f1Piece i).x 0 = cellStart i := by rw [hPx, cellPoint_zero]
  rw [← aQ_eq]
  have b2' : (G.bound2 : ℝ) ≤ f1c2 i := by unfold f1c2; exact_mod_cast b2
  have b3' : (G.bound3c : ℝ) ≤ f1c3 i := by unfold f1c3; exact_mod_cast b3
  refine ⟨(H.cellBound_le_bound2 _ hPn hPx hPnc herr).trans b2', ?_⟩
  rw [h0]
  exact (H.cellBound_le_bound3c_e h2 _ hPn hPx hPnc (H.e_bounds herr).1
    (H.e_bounds herr).2).trans b3'

theorem cellK_eq_f1C2 : cellK_29.1 = f1C2 29 ∧ cellK_30.1 = f1C2 30 ∧ cellK_31.1 = f1C2 31 ∧
    cellK_32.1 = f1C2 32 := by decide +kernel

/-! ## The 66 charge bounds -/

/-- The charge of the F1 blocks of piece `i` in degree `d`. -/
noncomputable abbrev f1Charge (d : ℕ) (i : Fin 33) : ℝ :=
  blockCharge (fun b => paperSelAt (paperAtomMap (paperBlockOf f1Cell)) targetDecay (.inr b)) d i

/-- The charges from any error constant valid on the piece. -/
theorem f1_charge_of (i : Fin 33) {e : ℝ}
    (hθ : ∀ t, (f1XN i : ℝ) ≤ t → t ≤ (pieceStop i : ℝ) → |Target.theta4 t 3 - t / 2| ≤ e * t) :
    f1Charge 2 i ≤ cellBound (f1Piece i) targetDecay 1 e ∧
      f1Charge 3 i ≤ cellBound (f1Piece i) targetDecay (3 / 2) e := by
  have ha := TargetLedger.targetDecay_nonneg
  have hθ' : 1 ≤ (f1Piece i).n → ∀ t, (f1Piece i).x 0 ≤ t → t ≤ (f1Piece i).x (f1Piece i).n →
      |Target.theta4 t 3 - t / 2| ≤ e * t := by
    intro _ t h1 h2
    rw [f1Piece_top] at h2
    have h0 : (f1Piece i).x 0 = (f1XN i : ℝ) := by simp only [f1Piece, Misc.cellPoint_zero]
    rw [h0] at h1
    exact hθ t h1 h2
  have h2 := (f1_blockCharge_le i ha 2).trans (piece_charge_le binU binU_le (f1Piece i)
    (f1Piece_partsOK i) (fun _ => f1Piece_cellsOK i) ha (Or.inl rfl) hθ')
  have h3 := (f1_blockCharge_le i ha 3).trans (piece_charge_le binU binU_le (f1Piece i)
    (f1Piece_partsOK i) (fun _ => f1Piece_cellsOK i) ha (Or.inr (Or.inl rfl)) hθ')
  have e2 : ((2 : ℕ) : ℝ) / 2 = 1 := by norm_num
  have e3 : ((3 : ℕ) : ℝ) / 2 = 3 / 2 := by norm_num
  rw [e2] at h2
  rw [e3] at h3
  simp only [f1Piece, List.map_nil, List.sum_nil, zero_add] at h2 h3
  exact ⟨h2, h3⟩

/-- **The 66 charge bounds at the F1 partition** (`lem:record:block-charge` with `thm:bmor` and
`ThetaSmallRR`): `b_d(i) ≤ c'_d(i)` for every middle piece and `d ∈ {2, 3}`. -/
theorem f1_charge_le (hB : Target.BMOR) (hRR : Target.ThetaSmallRR) (i : Fin 33) :
    f1Charge 2 i ≤ f1c2 i ∧ f1Charge 3 i ≤ f1c3 i := by
  rcases Nat.lt_or_ge i.val 29 with hi | hi
  · -- the F1 pieces
    have herr0 : (0 : ℝ) ≤ (f1Err i.val : ℝ) := by
      have : (0 : ℚ) ≤ f1Err i.val := by
        have h : ∀ k : Fin 29, (0 : ℚ) ≤ f1Err k.val := by decide +kernel
        exact h ⟨i.val, hi⟩
      exact_mod_cast this
    have hθ : ∀ t, (f1XN i : ℝ) ≤ t → t ≤ (pieceStop i : ℝ) →
        |Target.theta4 t 3 - t / 2| ≤ (f1Err i.val : ℝ) * t := by
      intro t h1 h2
      rcases Nat.lt_or_ge i.val 28 with h28 | h28
      · exact f1_theta_low h28 hRR h1 h2
      · have hi28 : i.val = 28 := by omega
        have hX : (f1XN i : ℝ) = 2 ^ 32 := by
          have : f1XN i = 2 ^ 32 := by
            have h : ∀ k : Fin 33, k.val = 28 → f1XN k = 2 ^ 32 ∧ pieceStop k = 2 ^ 34 := by
              decide +kernel
            exact (h i hi28).1
          rw [this]
          norm_num
        have hY : (pieceStop i : ℝ) = 2 ^ 34 := by
          have : pieceStop i = 2 ^ 34 := by
            have h : ∀ k : Fin 33, k.val = 28 → f1XN k = 2 ^ 32 ∧ pieceStop k = 2 ^ 34 := by
              decide +kernel
            exact (h i hi28).2
          rw [this]
          norm_num
        rw [hi28]
        rw [hX] at h1
        rw [hY] at h2
        exact f1_theta_28 hB hRR h1 h2
    obtain ⟨c2, c3⟩ := f1_charge_of i hθ
    obtain ⟨d2, d3⟩ := f1_cell_low hi herr0 le_rfl
    exact ⟨c2.trans d2, c3.trans d3⟩
  · -- the paper's pieces above `X_Ch`
    have hX0 : (4800162889 : ℝ) ≤ (f1XN i : ℝ) := by
      have h : ∀ k : Fin 33, 29 ≤ k.val → 4800162889 ≤ f1XN k := by decide +kernel
      exact_mod_cast h i hi
    have h0 : (f1Piece i).x 0 = (f1XN i : ℝ) := by simp only [f1Piece, Misc.cellPoint_zero]
    have hθ : ∀ t, (f1XN i : ℝ) ≤ t → t ≤ (pieceStop i : ℝ) →
        |Target.theta4 t 3 - t / 2| ≤ 2411 / (5000000 * Real.log ((f1Piece i).x 0)) * t := by
      intro t h1 _
      rw [h0]
      exact bmor_eta_le hB hX0 h1
    obtain ⟨c2, c3⟩ := f1_charge_of i hθ
    obtain ⟨v, hv⟩ := i
    simp only at hi
    have hcases : v = 29 ∨ v = 30 ∨ v = 31 ∨ v = 32 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · have h := f1_cell_high (i := 29) (by decide) encl_29 cellCount_29 (by decide +kernel)
        (by decide +kernel) (cellK_eq_f1C2.1 ▸ bound2_29) paper_bound3c.1
      exact ⟨c2.trans h.1, c3.trans h.2⟩
    · have h := f1_cell_high (i := 30) (by decide) encl_30 cellCount_30 (by decide +kernel)
        (by decide +kernel) (cellK_eq_f1C2.2.1 ▸ bound2_30) paper_bound3c.2.1
      exact ⟨c2.trans h.1, c3.trans h.2⟩
    · have h := f1_cell_high (i := 31) (by decide) encl_31 cellCount_31 (by decide +kernel)
        (by decide +kernel) (cellK_eq_f1C2.2.2.1 ▸ bound2_31) paper_bound3c.2.2.1
      exact ⟨c2.trans h.1, c3.trans h.2⟩
    · have h := f1_cell_high (i := 32) (by decide) encl_32 cellCount_32 (by decide +kernel)
        (by decide +kernel) (cellK_eq_f1C2.2.2.2 ▸ bound2_32) paper_bound3c.2.2.2
      exact ⟨c2.trans h.1, c3.trans h.2⟩

/-! ## The main statement -/

/-- The analytic block inputs at the F1 partition, from B1's lemma forms (the budget proved). -/
noncomputable abbrev f1A (hU : ∀ k, UpperBandLemma k)
    (hM : ∀ i, allpIndividual i = none → MiddleUniformLemma i)
    (hI : ∀ i u, allpIndividual i = some u → MiddleIndividualLemma i u) :
    PaperAnalyticInputs f1Cell :=
  paperAnalyticInputs_of_lemmas f1Cell_budget hU hM hI

/-- **The main statement at `ε = a_T/71` at the F1 partition, with `hB` and `hL₀` proved and no
histogram** (`thm:main` at `ε = a_T/71`, `cor:joint-closing`, `def:construction`(b),
`lem:record:block-charge` with `thm:bmor` and `ThetaSmallRR`, `lem:record:middle-prices`,
`def:closing-quantities`(2), (3)). Hypotheses: H1 (`Weil`), H2 (`BMOR`), H5
(`MovingRoot`), `thm:dl:K` (`FourCycle`), H2″ (`ThetaSmallRR`), B1's lemma families `hU`, `hM`,
`hI`, and the 9 Part V fields at the F1 partition: `Dv` (`CL`, `ME`, `SM`), `hT`, `hSA`, `JB`,
`SF`, `fix`, `env`. -/
theorem main_target_f1 (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (hU : ∀ k, UpperBandLemma k) (hM : ∀ i, allpIndividual i = none → MiddleUniformLemma i)
    (hI : ∀ i u, allpIndividual i = some u → MiddleIndividualLemma i u)
    (Dv : B1JointBlockData f1Cell hWeil hMovingRoot hFourCycle (f1A hU hM hI))
    (hT : Dv.toJoint.data.ME.T ≤ targetLedger.T)
    (hSA : Dv.toJoint.data.CL.S + Dv.toJoint.data.CL.A ≤ targetLedger.S + targetLedger.A)
    (JB : JointBound Dv.toJoint.data targetLedger.jointConstant)
    (SF : EnvelopeInputsBlock.SharpFirstInputs Dv.toJoint.data)
    (fix : EnvelopeInputsBlock.FixedIntervalInputs
      (BlockAnchor.index_coprime_block Dv.toJoint.data) Dv.toJoint.data)
    (env : EnvelopeInputsBlock.EnvelopeEnergyInputs
      (BlockAnchor.index_coprime_block Dv.toJoint.data) Dv.toJoint.data) :
    Target.SarkozyBound TargetLedger.targetSaving := by
  have hb₂ : ∀ i, f1Charge 2 i ≤ f1c2 i := fun i => (f1_charge_le hBMOR hThetaSmallRR i).1
  have hb₃ : ∀ i, f1Charge 3 i ≤ f1c3 i := fun i => (f1_charge_le hBMOR hThetaSmallRR i).2
  have hd := fun j => (sum_dTag_le hWeil hMovingRoot hFourCycle (f1A hU hM hI) j).trans
    (sum_lin_le (fun _ => le_refl 0) fsD3_nonneg hb₂ hb₃)
  have hv := fun j => (sum_vTag_le hWeil hMovingRoot hFourCycle (f1A hU hM hI) j).trans
    (sum_lin_le fsV2_nonneg (fun _ => le_refl 0) hb₂ hb₃)
  have hP := (sum_pvar_le hWeil hMovingRoot hFourCycle (f1A hU hM hI)).trans
    (sum_lin_le fsP2_nonneg fsP3_nonneg hb₂ hb₃)
  exact main_target_paper_joint_B1_charges hWeil hMovingRoot hFourCycle
    hThetaSmallRR f1Cell (f1A hU hM hI) Dv hb₂ hb₃ (d' := f1D) (v' := f1V) hd hv f1_costB_le
    (hL₀_of_prices Dv.toJoint.toA2.toA1 hP hd hv f1_costL_le) hT hSA JB SF fix env

end Sarkozy.AnalyticCells
