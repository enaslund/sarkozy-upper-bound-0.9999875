module

public import Sarkozy.MainFinalF1.Prices
public import Sarkozy.MainFinalJ.All

@[expose] public section

/-!
# K1's layer at `f1Cell`, with the combined gate and `hB`, `hL₀` proved (F1P)

C10's `MainFinalJ.MainFinalObligationsJ` / `main_target_paper_finalJ` at N2's partition `f1Cell`:

* `hB` (`def:closing-quantities`(3), `lem:record:block-charge`, `cor:two-cut-series`) and `hL₀`
  (`def:closing-quantities`(2), `def:cp2`) are **proved** from `BMOR` and `ThetaSmallRR`: N2's
  `f1_charge_le` (the 66 charges `b_d(i) ≤ f1c2 i, f1c3 i`), `f1_costB_le`, `f1_costL_le`, as in
  N2's `main_target_f1` and K2's `main_target_f1_final2`. There is **no `NumericalCertificates`
  and no `HistogramClaim`**.
* `hT`, `hSA` as in K1 (`hT` by B3's construction, `hSA` from its explicit form).
* `JB := Cls.jointBound` (E4's `ClassParts2J`, combined gate `AllocJ`, layout-generic);
  `SF`, `fix`, `env` from K2's layout-generic `SharpParts2` (B5, B9).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MainFinalF1

open Sarkozy.TheoremC Sarkozy.RecordExpansion
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (paperAtomMap)
open Sarkozy.PaperNumbers (sum_lin_le fsD3_nonneg fsV2_nonneg fsP2_nonneg fsP3_nonneg)
open Sarkozy.AnalyticCells (f1Cell f1_charge_le f1c2 f1c3 f1D f1V f1_costB_le f1_costL_le)
open Sarkozy.MainFinal2 (SharpParts2)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

namespace FinalBlockData

/-- **`hB` at `f1Cell`, proved** (`def:closing-quantities`(3), `lem:record:middle-prices`,
`lem:record:block-charge`, `cor:two-cut-series`): `B ≤ B^{ledger}` from H2 (`thm:bmor`), H2″
(`ThetaSmallRR`), N2's charge bounds `f1_charge_le` and N2's cost inequality `f1_costB_le`. -/
theorem hB_final (hBMOR : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (D : FinalBlockData hW hMR hFour) : D.data.B ≤ targetLedger.B :=
  hB_of_blockCharges_joint D.toFixed (c₂ := f1c2) (c₃ := f1c3) (d' := f1D) (v' := f1V)
    (fun i => (f1_charge_le hBMOR hRR i).1) (fun i => (f1_charge_le hBMOR hRR i).2)
    (fun j => (PaperNumbers.sum_dTag_le hW hMR hFour D.AI j).trans
      (sum_lin_le (fun _ => le_refl 0) fsD3_nonneg (fun i => (f1_charge_le hBMOR hRR i).1)
        (fun i => (f1_charge_le hBMOR hRR i).2)))
    (fun j => (PaperNumbers.sum_vTag_le hW hMR hFour D.AI j).trans
      (sum_lin_le fsV2_nonneg (fun _ => le_refl 0) (fun i => (f1_charge_le hBMOR hRR i).1)
        (fun i => (f1_charge_le hBMOR hRR i).2)))
    f1_costB_le

/-- **`hL₀` at `f1Cell`, proved** (`def:closing-quantities`(2), `def:cp2`,
`lem:record:middle-prices`): `L₀ ≤ L₀^{ledger}` from H2, H2″, `f1_charge_le` and `f1_costL_le`. -/
theorem hL₀_final (hBMOR : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (D : FinalBlockData hW hMR hFour) : D.data.L₀ ≤ targetLedger.L₀ :=
  hL₀_of_prices D.toFixed.toJoint.toA2.toA1 (d' := f1D) (v' := f1V)
    ((PaperNumbers.sum_pvar_le hW hMR hFour D.AI).trans
      (sum_lin_le fsP2_nonneg fsP3_nonneg (fun i => (f1_charge_le hBMOR hRR i).1)
        (fun i => (f1_charge_le hBMOR hRR i).2)))
    (fun j => (PaperNumbers.sum_dTag_le hW hMR hFour D.AI j).trans
      (sum_lin_le (fun _ => le_refl 0) fsD3_nonneg (fun i => (f1_charge_le hBMOR hRR i).1)
        (fun i => (f1_charge_le hBMOR hRR i).2)))
    (fun j => (PaperNumbers.sum_vTag_le hW hMR hFour D.AI j).trans
      (sum_lin_le fsV2_nonneg (fun _ => le_refl 0) (fun i => (f1_charge_le hBMOR hRR i).1)
        (fun i => (f1_charge_le hBMOR hRR i).2)))
    f1_costL_le

/-- **`hT`** (`def:cp6`, `prop:record:matching`(ii)): B3's construction has `T = T^{ledger}`. -/
theorem hT_final (D : FinalBlockData hW hMR hFour) : D.data.ME.T ≤ targetLedger.T :=
  le_refl _

/-- **`hSA` from its explicit form** (`def:cp4`(b), `def:closing-quantities`; B2's
`comparisonLawTarget_SA`). -/
theorem hSA_final (D : FinalBlockData hW hMR hFour) (h : ComparisonLawPaper.SAExplicit D.Cmp.Ci) :
    D.data.CL.S + D.data.CL.A ≤ targetLedger.S + targetLedger.A :=
  (ComparisonLawPaper.comparisonLawTarget_SA hW _ _ _ D.Cmp.Ci).trans_le h

end FinalBlockData

/-- **K1's obligations at `f1Cell` with the combined gate**: C10's `MainFinalObligationsJ` without
`NC` (the charges are proved), with `Sh : SharpParts2` (K2's layout-generic sharp inputs). 4
fields. -/
structure MainFinalObligationsJ (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) where
  /-- The block data (K1, at `f1Cell`). -/
  Dv : FinalBlockData hW hMR hFour
  /-- `hSA` in explicit per-atom form (B2). -/
  hSA : ComparisonLawPaper.SAExplicit Dv.Cmp.Ci
  /-- The class inputs with the combined allocation gate (E4). -/
  Cls : ClassData.ClassParts2J Dv.data
  /-- The inputs of `SF`, `fix`, `env` (B5, B9). -/
  Sh : SharpParts2 Dv.toJoint

/-- **To B1's joint obligations at `f1Cell`**: `hB`, `hL₀` proved (N2), `JB := Cls.jointBound`. -/
noncomputable def MainFinalObligationsJ.toB1 (hBMOR : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (O : MainFinalObligationsJ hW hMR hFour) :
    B1JointFinalObligations f1Cell hW hMR hFour O.Dv.AI where
  Dv := O.Dv.toFixed
  hB := O.Dv.hB_final hBMOR hRR
  hL₀ := O.Dv.hL₀_final hBMOR hRR
  hT := O.Dv.hT_final
  hSA := O.Dv.hSA_final O.hSA
  JB := O.Cls.jointBound
  SF := O.Sh.SF
  fix := O.Sh.fix
  env := O.Sh.env

/-- **K1's main statement at `f1Cell` with the combined gate** (`thm:main` at `ε = a_T/71`, via
`thm:comparison` with `cor:joint-closing`, `eq:final-joint-closing`;
`def:record:exact-blocks`(d) in place of (c) below `X_Ch`, a deviation from the paper's
construction). Hypotheses: H1, H2, H4 (passed along), H5, `thm:dl:K`, H2″, and
`O : MainFinalObligationsJ`. -/
theorem main_target_f1_finalJ (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligationsJ hWeil hMovingRoot hFourCycle) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_joint_B1 hWeil hMovingRoot hFourCycle hThetaSmallRR f1Cell
    O.Dv.AI (O.toB1 hBMOR hThetaSmallRR)

end Sarkozy.MainFinalF1
