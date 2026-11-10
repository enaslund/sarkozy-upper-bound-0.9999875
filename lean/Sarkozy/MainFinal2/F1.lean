module

public import Sarkozy.MainFinal2.Main
public import Sarkozy.AnalyticCells.F1Main

@[expose] public section






open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MainFinal2

open Sarkozy.MainFinal
open Sarkozy.TheoremC Sarkozy.RecordExpansion
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PaperNumbers (sum_lin_le fsD3_nonneg fsV2_nonneg fsP2_nonneg fsP3_nonneg)
open Sarkozy.AnalyticCells (f1Cell f1Cell_budget f1_charge_le f1c2 f1c3 f1D f1V f1_costB_le
  f1_costL_le)

/-- **The analytic inputs `A` at `f1Cell`** (B6's adapter with N2's `f1Cell_budget`, C8/C9's
per-prime certificates, B6's block-level inputs, E21 and the upper `E × E` caps proved). -/
theorem analyticInputsF1 (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (PC : PrimeCertificates2) (BA : BlockAnalytic) : PaperAnalyticInputs f1Cell :=
  BlockAdapter.paperAnalyticInputs_B6 f1Cell_budget
    (fun k => BlockAdapter.upperBandLemma_of_rest
      (BlockAdapter.upperBandRest_of_rows (BlockAdapter.upperBandRows_of_nonEE (BA.hUR k))
        ((PC.toPC hW hMR hFour).hUC k)) ((PC.toPC hW hMR hFour).hUC k))
    BA.hMB BA.hIB (PC.toPC hW hMR hFour).h20 (PC.toPC hW hMR hFour).h10
    (PC.toPC hW hMR hFour).h21 BlockAdapter.middleE21Caps_proved

/-- **The obligations of the F1 variant.** 7 fields: the per-prime certificates and block
inputs (as at `paperCell`), B1's block data `Dv` at `f1Cell` (`CL`, `ME`, `SM`; *open*), `hT`
(`def:cp6`; *open*), `hSA` (`def:closing-quantities`, `def:cp4`(b); *open*), and the
layout-generic class and sharp inputs. No `HistogramClaim`. -/
structure MainFinalObligationsF1 (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) where
  /-- The per-prime cut certificates (C8, C9). -/
  PC : PrimeCertificates2
  /-- The block-level analytic inputs (B6). -/
  BA : BlockAnalytic
  /-- B1's block data at `f1Cell`: (CP4) `CL`, (CP6) `ME`, (CP8)(c) `SM`. *Open.* -/
  Dv : B1JointBlockData f1Cell hW hMR hFour (analyticInputsF1 hW hMR hFour PC BA)
  /-- `T ≤ T^{ledger}` (`def:cp6`). *Open.* -/
  hT : Dv.toJoint.data.ME.T ≤ targetLedger.T
  /-- `S + A ≤ S^{ledger} + A^{ledger}` (`def:closing-quantities`, `def:cp4`(b)). *Open.* -/
  hSA : Dv.toJoint.data.CL.S + Dv.toJoint.data.CL.A ≤ targetLedger.S + targetLedger.A
  /-- The inputs of the joint bound (B4, B10, G1). -/
  Cls : ClassParts2 Dv.toJoint.data
  /-- The inputs of `SF`, `fix`, `env` (B5, B9). -/
  Sh : SharpParts2 Dv.toJoint

/-- **The main statement at `ε = a_T/71` at the F1 partition, with `hB`, `hL₀` proved and no
histogram claim** (`thm:main` at `ε = a_T/71`, `cor:joint-closing`; `def:record:exact-blocks`(d)
in place of (c) on the middle pieces — a deviation from the paper's construction).
Hypotheses: H1, H2 (`BMOR`), H4 (passed along), H5, `thm:dl:K`, H2″ (`ThetaSmallRR`, used for the
F1 cells below `10¹⁰`), and `O : MainFinalObligationsF1`. -/
theorem main_target_f1_final2 (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligationsF1 hWeil hMovingRoot hFourCycle) :
    Target.SarkozyBound TargetLedger.targetSaving := by
  have hb₂ := fun i => (f1_charge_le hBMOR hThetaSmallRR i).1
  have hb₃ := fun i => (f1_charge_le hBMOR hThetaSmallRR i).2
  have hd := fun j => (PaperNumbers.sum_dTag_le hWeil hMovingRoot hFourCycle
    (analyticInputsF1 hWeil hMovingRoot hFourCycle O.PC O.BA) j).trans
    (sum_lin_le (fun _ => le_refl 0) fsD3_nonneg hb₂ hb₃)
  have hv := fun j => (PaperNumbers.sum_vTag_le hWeil hMovingRoot hFourCycle
    (analyticInputsF1 hWeil hMovingRoot hFourCycle O.PC O.BA) j).trans
    (sum_lin_le fsV2_nonneg (fun _ => le_refl 0) hb₂ hb₃)
  have hP := (PaperNumbers.sum_pvar_le hWeil hMovingRoot hFourCycle
    (analyticInputsF1 hWeil hMovingRoot hFourCycle O.PC O.BA)).trans
    (sum_lin_le fsP2_nonneg fsP3_nonneg hb₂ hb₃)
  have hB := hB_of_blockCharges_joint O.Dv (d' := f1D) (v' := f1V) hb₂ hb₃ hd hv f1_costB_le
  exact main_target_paper_joint_B1_charges hWeil hMovingRoot hFourCycle
    hThetaSmallRR f1Cell (analyticInputsF1 hWeil hMovingRoot hFourCycle O.PC O.BA) O.Dv hb₂ hb₃
    (d' := f1D) (v' := f1V) hd hv f1_costB_le
    (hL₀_of_prices O.Dv.toJoint.toA2.toA1 hP hd hv f1_costL_le) O.hT O.hSA
    (O.Cls.jointBound hB) O.Sh.SF O.Sh.fix O.Sh.env

end Sarkozy.MainFinal2
