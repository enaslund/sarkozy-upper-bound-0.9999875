module

public import Sarkozy.MainCombined2.Main
public import Sarkozy.ThetaOne.Main

@[expose] public section

/-!
# The combined main statement on the baseline induction `ϑ = 1` (`main_goal_theta1k`)

`MainCombined2.main_goal_f1k` combines three reductions of 7 November (UC's upper caps, PG's
prime Gram, NB2's merge norms) in the reduced front `FrontK`, on top of `main_goal_f1i`, whose
`Sh` group is the upgrade route `MainFinal2.SharpParts2U` (with `Sh.fibre`). TH's
`ThetaOne.main_goal_theta1` has the same front fields as `main_goal_f1i` and the baseline `Sh`
group (`ThetaOne.SharpPartsBase`, `ϑ = 1`). Here the two are combined:

* **`MainFinalObligationsKT1`** (3 fields: `F : FrontK`, `Cls`, `Sh : SharpPartsBase`): as UC's
  `MainFinalObligationsK`, with the baseline `Sh`;
* **`toT1`**: `ThetaOne.MainFinalObligationsT1` at the images `F.PC`, `F.Up`, `F.SGp`, `F.hNr`
  (definitional maps);
* **`main_goal_theta1k`**: `s(N) ≤ C·N^{0.99999}`, through `ThetaOne.main_goal_theta1`.
-/

namespace Sarkozy.MainCombined2

open Sarkozy.PartV Sarkozy.BlockSpecPaper Sarkozy.MainCombined
open Sarkozy.MainFinalF1b (ClassPartsE4B)
open Sarkozy.NormBoundsPaper (hNG)
open Sarkozy.UpperCapsPaper (UpperRecordTables)
open Sarkozy.ThetaOne (SharpPartsBase MainFinalObligationsT1)

/-- **The obligations of `main_goal_theta1k`**: UC's reduced front `F`, the class inputs `Cls`
and the **baseline** sharp inputs `Sh` (`ϑ = 1`: no `Sh.fibre`; `SF` by the folded route; the mean
bounds of `fixM`, `envM` reduced). 3 fields (`F` has 5, `Sh` has 3). -/
structure MainFinalObligationsKT1 (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables) : Type 1 where
  /-- The reduced front (UC, PG, NB2). -/
  F : FrontK hW hMR hFour UpT
  /-- The class inputs (as in `MainFinalObligationsGPN`). *Open*. -/
  Cls : ClassPartsE4B ((dvG F.PC F.BA F.Up F.SGp.toSector.toGram.toSG).to3e.toK1 hB
    ((dvG F.PC F.BA F.Up F.SGp.toSector.toGram.toSG).saOfS (hNG F.PC F.BA F.Up F.hNr))
    (hmidG hB hRR F.PC F.BA F.Up F.SGp.toSector.toGram.toSG (hNG F.PC F.BA F.Up F.hNr))).data
  /-- **The baseline inputs of `SF`, `fix`, `env`** (`ThetaOne.SharpPartsBase`). *Open*:
  `SF.hfold`, `SF.hrem`; per `fixM`, `envM`: `hdiffL/R`, `hzu`, `hr2L/R`. -/
  Sh : SharpPartsBase ((dvG F.PC F.BA F.Up F.SGp.toSector.toGram.toSG).to3e.toK1 hB
    ((dvG F.PC F.BA F.Up F.SGp.toSector.toGram.toSG).saOfS (hNG F.PC F.BA F.Up F.hNr))
    (hmidG hB hRR F.PC F.BA F.Up F.SGp.toSector.toGram.toSG
      (hNG F.PC F.BA F.Up F.hNr))).toJoint

/-- **`ThetaOne.MainFinalObligationsT1` from the combined obligations**: `PC := F.PCu.toPC2'`,
`Up := ofSplit UpT F.UpB`, `SGp := F.SD.toPrime`, `hNr := hNrGPN … F.hNr2`. -/
noncomputable def MainFinalObligationsKT1.toT1 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {hB : Target.BMOR} {hRR : Target.ThetaSmallRR}
    {UpT : UpperRecordTables} (O : MainFinalObligationsKT1 hW hMR hFour hB hRR UpT) :
    MainFinalObligationsT1 hW hMR hFour hB hRR where
  PC := O.F.PC
  BA := O.F.BA
  Up := O.F.Up
  SGp := O.F.SGp
  hNr := O.F.hNr
  Cls := O.Cls
  Sh := O.Sh

/-- **The combined main statement on the baseline induction `ϑ = 1`, at `N^{0.99999}`**
(`thm:main` at `ε = 10⁻⁵`; `thm:density:induction` at `ϑ = 1` with the four-routes closing at
`a_T`, saving `a_T/71`): UC, PG and NB2 in the front, TH's baseline `Sh`. Its hypotheses are
H1–H5, H2″, `thm:dl:K`, the finite record table `UpT` (`UpperRecordTables`) and the obligations
`O`. -/
theorem main_goal_theta1k (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables)
    (O : MainFinalObligationsKT1 hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR UpT) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  ThetaOne.main_goal_theta1 hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O.toT1

end Sarkozy.MainCombined2
