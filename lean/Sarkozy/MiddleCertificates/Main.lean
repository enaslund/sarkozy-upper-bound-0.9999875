module

public import Sarkozy.MiddleCertificates.L20Bridge

/-!
# The main statement with the three middle per-prime certificates reduced (C8)

B6's `main_target_paper_joint_B6` with its per-prime fields replaced:

* `h10` (L10, all 33 pieces) and `h21` (L21, the 31 uniform pieces) by `MidInputs`: the analytic
  parts of route A, `thm:spectral-criterion`(a),(d), at the bars of `cert:layer12-grid` at the
  piece start (`Caps.lean`; the finite tests are proved);
* `h20` (L20, the 31 uniform pieces) by W3-form bounds `L20W3Bounds` at every class-three prime of
  the piece (`L20Bridge.lean`; sufficient conditions `l20W3Bounds_of_target`, W3's
  `l20_prime_caps_target` with the two gates of `cert:l20-grid` at `p`).
-/

@[expose] public section

namespace Sarkozy.MiddleCertificates

open Sarkozy.BlockAdapter Sarkozy.PartV Sarkozy.BlockSpecPaper Sarkozy.BlockSpecPaper.AllpData

/-- The W3-form L20 bounds at every class-three prime of piece `i`. *Hypothesis.* -/
def L20Inputs (i : Fin 33) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → pieceStart i ≤ p → p < pieceStop i → L20W3Bounds i p

/-- **B6's main statement with all three middle per-prime certificate families reduced**:
`h10`, `h21` to the analytic route-A inputs `MidInputs` (finite tests proved), `h20` to the
W3-form bounds `L20Inputs` (bridge to B6's cut operator proved). -/
theorem main_target_paper_joint_C8W (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR) (cell : ℕ → ℕ)
    (hbud : PaperBudget cell) (hUR : ∀ k, UpperBandRowsNonEE k) (hUC : ∀ k, UpperRootCaps k)
    (hMB : ∀ i, allpIndividual i = none → MiddleUniformBlockInputs i)
    (hIB : ∀ i u, allpIndividual i = some u → MiddleIndividualBlockInputs i u)
    (h20 : ∀ i, allpIndividual i = none → L20Inputs i)
    (h10 : ∀ i, MidInputs .l10 i)
    (h21 : ∀ i, allpIndividual i = none → MidInputs .l21 i)
    (O : B1JointFinalObligations cell hWeil hMovingRoot hFourCycle
      (paperAnalyticInputs_B6 hbud
        (fun k => upperBandLemma_of_rest
          (upperBandRest_of_rows (upperBandRows_of_nonEE (hUR k)) (hUC k)) (hUC k))
        hMB hIB (fun i hi => middleRootCaps_l20_of_W3 (h20 i hi))
        (fun i => middleRootCaps_l10 (h10 i))
        (fun i hi => middleL21Caps_of_inputs (h21 i hi)) middleE21Caps_proved)) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_joint_C8 hWeil hMovingRoot hFourCycle hThetaSmallRR cell hbud hUR
    hUC hMB hIB (fun i hi => middleRootCaps_l20_of_W3 (h20 i hi)) h10 h21 O

end Sarkozy.MiddleCertificates
