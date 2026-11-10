module

public import Sarkozy.MainFinalJ.K1
public import Sarkozy.EnvPrefix.Main

@[expose] public section





open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MainFinalJ

open Sarkozy.MainFinal Sarkozy.MainFinal2 Sarkozy.MainFinal3 Sarkozy.EnvPrefix
open Sarkozy.TargetLedger (targetLedger)
open Sarkozy.PaperNumbers (paperCell HistogramClaim)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-! ## K2's layer -/

/-- **K2's obligations with the combined gate** (`Cls : ClassParts2J`). 5 fields. -/
structure MainFinalObligations2J (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) where
  Dv : FinalBlockData2 hW hMR hFour
  hHist : HistogramClaim
  SA : SAParts hW hMR hFour (analyticInputs (Dv.PC.toPC hW hMR hFour) Dv.BA) Dv.Cmp
  Cls : ClassData.ClassParts2J Dv.toK1.data
  Sh : SharpParts2U Dv.toK1.toJoint

/-- K1's layer (K2's `toK1` maps for every field but `Cls`). -/
noncomputable def MainFinalObligations2J.toK1J (hBMOR : Target.BMOR)
    (O : MainFinalObligations2J hW hMR hFour) : MainFinalObligationsJ hW hMR hFour where
  Dv := O.Dv.toK1
  NC := numericalCertificates_of_hist O.hHist
  hSA := O.SA.toSAExplicit hBMOR (numericalCertificates_of_hist O.hHist)
  Cls := O.Cls
  Sh := O.Sh.toK1

/-! ## `MainFinal3`'s layer -/

/-- **`MainFinal3`'s obligations with the combined gate.** 5 fields. -/
structure MainFinalObligations3J (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) where
  Dv : FinalBlockData3 hW hMR hFour
  hHist : HistogramClaim
  SA : SAParts3 hW hMR hFour (analyticInputs (Dv.PC.toPC hW hMR hFour) Dv.BA) Dv.Cmp
  Cls : ClassData.ClassParts2J Dv.toK2.toK1.data
  Sh : SharpParts2U Dv.toK2.toK1.toJoint

/-- K2's layer (`MainFinal3`'s `toK2` maps). -/
noncomputable def MainFinalObligations3J.toK2J (hBMOR : Target.BMOR)
    (O : MainFinalObligations3J hW hMR hFour) : MainFinalObligations2J hW hMR hFour where
  Dv := O.Dv.toK2
  hHist := O.hHist
  SA := O.SA.toK2 hBMOR
  Cls := O.Cls
  Sh := O.Sh

/-! ## `EnvPrefix`'s layer, with E4's closures -/

/-- **The combined obligations with the combined allocation gate and E4's closures.** 6 fields:
`EnvPrefix`'s `MainFinalObligations3b` with `Cls : ClassPartsE4`. -/
structure MainFinalObligations3c (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) where
  /-- The block data (`EnvPrefix`). -/
  Dv : FinalBlockData3b hW hMR hFour
  /-- The histogram certificate (`cert:record:middle-price`(b)). *Open* (N2, K2). -/
  hHist : HistogramClaim
  /-- `hSA` in reduced form (`MainFinal3`). -/
  SA : SAParts3 hW hMR hFour (analyticInputs (Dv.PC.toPC hW hMR hFour) Dv.BA) Dv.Cmp
  /-- The middle part of `hothT` (`EnvPrefix`). *Open*. -/
  hmid : ∀ L, midOthers Dv.Cmp.toK2 Dv.MR L +
    max (∑ β, Dv.MR.toPrefix.KL β) (∑ β, Dv.MR.toPrefix.KR β) +
    (12 / 2 ^ 534 + Uup SA.Cs SA.Ca SA.hCs SA.hCa + 11 / 10 ^ 70) ≤ targetLedger.T
  /-- The class inputs with the combined gate, through E4's constructors (B10, B11, G1, E4). -/
  Cls : ClassPartsE4 (Dv.toMF3 hB SA hmid).toK2.toK1.data
  /-- The inputs of `SF`, `fix`, `env` (B5, B9). -/
  Sh : SharpParts2U (Dv.toMF3 hB SA hmid).toK2.toK1.toJoint

/-- `MainFinal3`'s layer (`EnvPrefix`'s `toMF3` map of the block data, `ClassPartsE4.toJ`). -/
noncomputable def MainFinalObligations3c.to3J {hB : Target.BMOR}
    (O : MainFinalObligations3c hW hMR hFour hB) : MainFinalObligations3J hW hMR hFour where
  Dv := O.Dv.toMF3 hB O.SA O.hmid
  hHist := O.hHist
  SA := O.SA
  Cls := O.Cls.toJ
  Sh := O.Sh

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵`, with the combined allocation gate**
(`thm:main` at `ε = a_T/71`, via `thm:comparison` with `cor:joint-closing`,
`eq:final-joint-closing` and `thm:density:induction` at `a_T`; `def:construction`(b) in the ALLp
configuration). Hypotheses: H1 `Weil`, H2 `BMOR`, H5 `MovingRoot`,
`thm:dl:K` `FourCycle`, H2″ `ThetaSmallRR`, and `O : MainFinalObligations3c`.
H4 `TwoVariable` was removed on 9 November 2026 as unused. -/
theorem main_target_paper_final3c (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3c hWeil hMovingRoot hFourCycle hBMOR) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_finalJ hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR
    ((O.to3J.toK2J hBMOR).toK1J hBMOR)

end Sarkozy.MainFinalJ
