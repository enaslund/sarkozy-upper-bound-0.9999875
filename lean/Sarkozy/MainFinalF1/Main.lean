module

public import Sarkozy.MainFinalF1.Env

@[expose] public section






open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MainFinalF1

open Sarkozy.TargetLedger (targetLedger)
open Sarkozy.MainFinal2 (SharpParts2)
open Sarkozy.MainFinalJ (ClassPartsE4)

/-- **The combined obligations at `f1Cell` with the combined allocation gate and E4's closures**:
C10's `MainFinalObligations3c` without `hHist`. 5 fields. -/
structure MainFinalObligations3c (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) where
  /-- The block data (`EnvPrefix`, at `f1Cell`). -/
  Dv : FinalBlockData3b hW hMR hFour
  /-- `hSA` in reduced form (`MainFinal3`; final inequality at N2's numbers). -/
  SA : SAParts3 hW hMR hFour (analyticInputs (Dv.PC.toPC hW hMR hFour) Dv.BA) Dv.Cmp
  /-- The middle part of `hothT` (`EnvPrefix`). *Open*. -/
  hmid : ∀ L, midOthers Dv.Cmp.toK2 Dv.MR L +
    max (∑ β, Dv.MR.toPrefix.KL β) (∑ β, Dv.MR.toPrefix.KR β) +
    (12 / 2 ^ 534 + Sarkozy.EnvPrefix.Uup SA.Cs SA.Ca SA.hCs SA.hCa + 11 / 10 ^ 70) ≤
      targetLedger.T
  /-- The class inputs with the combined gate, through E4's constructors (B10, B11, G1, E4). -/
  Cls : ClassPartsE4 (Dv.toMF3 hB SA hmid).toK2.toK1.data
  /-- The inputs of `SF`, `fix`, `env` (B5, B9). -/
  Sh : SharpParts2 (Dv.toMF3 hB SA hmid).toK2.toK1.toJoint

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-- `MainFinal3`'s layer at `f1Cell` (`toMF3`, `ClassPartsE4.toJ`). -/
noncomputable def MainFinalObligations3c.to3J {hB : Target.BMOR}
    (O : MainFinalObligations3c hW hMR hFour hB) : MainFinalObligations3J hW hMR hFour where
  Dv := O.Dv.toMF3 hB O.SA O.hmid
  SA := O.SA
  Cls := O.Cls.toJ
  Sh := O.Sh

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵` at the F1 partition, with `hB`, `hL₀`
proved and no histogram claim** (`thm:main` at `ε = a_T/71`, via `thm:comparison` with
`cor:joint-closing`, `eq:final-joint-closing` and `thm:density:induction` at `a_T`;
`def:construction`(b) in the ALLp configuration, with `def:record:exact-blocks`(d) in place of (c)
below `X_Ch` — a deviation from the paper's construction). Hypotheses: H1 `Weil`, H2 `BMOR`, H5
`MovingRoot`, `thm:dl:K` `FourCycle`, H2″
`ThetaSmallRR` (used for the F1 cells below `10¹⁰`), and `O : MainFinalObligations3c`.
H4 `TwoVariable` was removed on 9 November 2026 as unused. -/
theorem main_target_f1_final3c (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3c hWeil hMovingRoot hFourCycle hBMOR) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_f1_finalJ hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR
    ((O.to3J.toK2J hBMOR).toK1J hBMOR hThetaSmallRR)

end Sarkozy.MainFinalF1
