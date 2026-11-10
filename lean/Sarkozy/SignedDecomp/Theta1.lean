module

public import Sarkozy.SignedDecomp.Main2
public import Sarkozy.MainCombined2.Theta1

@[expose] public section

/-!
# `main_goal_theta1k` with PG's `SD` reduced to two analytic statements (SD2)

`MainCombined2.main_goal_theta1k` takes `O : MainFinalObligationsKT1` (3 fields: `F : FrontK`,
`Cls`, `Sh`). Here `F` is replaced by **`F : FrontKB`**, in which PG's `SD` (the collision bound,
`prop:signed-bounds`(c) for the record and the components, and the gates) is replaced by
`SDB : SignedDecompAnalytic2` (the collision bound `lem:record:conditional-collision`(d) and the
signed decomposition `prop:signed-bounds`(c) at the paper's constants): the component norms and
the gates are proved (`SignedDecompAnalytic2.toSD`).

* **`MainFinalObligationsKT1B`** (3 fields), **`toKT1`** (`F := F.toFrontK`);
* **`main_goal_theta1k_sd2`**: `s(N) ≤ C·N^{0.99999}`, through `main_goal_theta1k`.
-/

namespace Sarkozy.SignedDecomp

open Sarkozy.PartV Sarkozy.BlockSpecPaper Sarkozy.MainCombined
open Sarkozy.MainFinalF1b (ClassPartsE4B)
open Sarkozy.NormBoundsPaper (hNG)
open Sarkozy.UpperCapsPaper (UpperRecordTables)
open Sarkozy.ThetaOne (SharpPartsBase)
open Sarkozy.MainCombined2 (MainFinalObligationsKT1 main_goal_theta1k)

/-- **The obligations of `main_goal_theta1k_sd2`**: `MainFinalObligationsKT1` with the front
`F : FrontKB` (SD2's `SDB` in place of PG's `SD`). 3 fields. -/
structure MainFinalObligationsKT1B (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables) : Type 1 where
  /-- The reduced front, with `SDB`. -/
  F : FrontKB hW hMR hFour UpT
  /-- The class inputs (as in `MainFinalObligationsKT1`). *Open*. -/
  Cls : ClassPartsE4B ((dvG F.toFrontK.PC F.toFrontK.BA F.toFrontK.Up
    F.toFrontK.SGp.toSector.toGram.toSG).to3e.toK1 hB
    ((dvG F.toFrontK.PC F.toFrontK.BA F.toFrontK.Up
      F.toFrontK.SGp.toSector.toGram.toSG).saOfS
      (hNG F.toFrontK.PC F.toFrontK.BA F.toFrontK.Up F.toFrontK.hNr))
    (hmidG hB hRR F.toFrontK.PC F.toFrontK.BA F.toFrontK.Up F.toFrontK.SGp.toSector.toGram.toSG
      (hNG F.toFrontK.PC F.toFrontK.BA F.toFrontK.Up F.toFrontK.hNr))).data
  /-- The baseline inputs of `SF`, `fix`, `env` (as in `MainFinalObligationsKT1`). *Open*. -/
  Sh : SharpPartsBase ((dvG F.toFrontK.PC F.toFrontK.BA F.toFrontK.Up
    F.toFrontK.SGp.toSector.toGram.toSG).to3e.toK1 hB
    ((dvG F.toFrontK.PC F.toFrontK.BA F.toFrontK.Up
      F.toFrontK.SGp.toSector.toGram.toSG).saOfS
      (hNG F.toFrontK.PC F.toFrontK.BA F.toFrontK.Up F.toFrontK.hNr))
    (hmidG hB hRR F.toFrontK.PC F.toFrontK.BA F.toFrontK.Up F.toFrontK.SGp.toSector.toGram.toSG
      (hNG F.toFrontK.PC F.toFrontK.BA F.toFrontK.Up F.toFrontK.hNr))).toJoint

/-- `MainFinalObligationsKT1` from `MainFinalObligationsKT1B` (`F := F.toFrontK`). -/
noncomputable def MainFinalObligationsKT1B.toKT1 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {hB : Target.BMOR} {hRR : Target.ThetaSmallRR}
    {UpT : UpperRecordTables} (O : MainFinalObligationsKT1B hW hMR hFour hB hRR UpT) :
    MainFinalObligationsKT1 hW hMR hFour hB hRR UpT where
  F := O.F.toFrontK
  Cls := O.Cls
  Sh := O.Sh

/-- **The main statement at `N^{0.99999}` with PG's `SD` reduced to two analytic statements**
(the collision bound and the signed decomposition at the paper's constants; the component norms
and the gates proved): `main_goal_theta1k` at `O.toKT1`. Its hypotheses are H1–H5, H2″,
`thm:dl:K`, the finite record table `UpT` and the obligations `O`. -/
theorem main_goal_theta1k_sd2 (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables)
    (O : MainFinalObligationsKT1B hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR UpT) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_theta1k hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR UpT O.toKT1

end Sarkozy.SignedDecomp
