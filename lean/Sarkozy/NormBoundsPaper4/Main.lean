module

public import Sarkozy.NormBoundsPaper4.Constructor
public import Sarkozy.NormBoundsPaper4.EEps
public import Sarkozy.NormBoundsPaper3.Main

@[expose] public section

/-!
# `main_goal_nb3` with `hEs` proved and the fold norms reduced to one prime (`main_goal_nb4`)

NB3's `main_goal_nb3` takes `MainFinalObligationsN3` (`F : FrontN3`, `Cls`, `Sh`). Two of the six
front fields are removed here:
* `F.hEs` (`lem:record:e-orthogonal`(c) at one prime, at the paper's `s^E_p`) is **proved**
  (`eOrthPaperInput`, `EEps.lean`), so the matching families `Es`, `Ea` are both unconditional;
* `F.hNr4` (the two fold families `Fs`, `Fa` at `paperKappa`, `prop:signed-bounds`(a),(b),(e)) is
  replaced by `hFold`: at every prime of every middle block, the one-prime statement
  `prop:signed-bounds`(c) (symmetric and skew parts of the prime fold difference at the piece
  constants) and the component norms `c_+ r` (`FoldInputs`); `hNr4_of_inputs` rebuilds `hNr4`
  (the collision part of the reference record is bounded crudely, `FoldCol`).

* **`FrontN4`**: 5 fields (`PCu`, `BA`, `UpB`, `SD`, `hFold`), all *open*; `FrontN4.toN3`;
* **`MainFinalObligationsN4`**, `toN3` (definitional);
* **`main_goal_nb4`**: `main_goal_nb3` applied to `O.toN3`.
-/

namespace Sarkozy.NormBoundsPaper4

open Sarkozy.PartV Sarkozy.BlockSpecPaper Sarkozy.MainCombined Sarkozy.MainCombined2
open Sarkozy.MainFinal (BlockAnalytic)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.MainFinalF1 (analyticInputs specF)
open Sarkozy.MainFinalF1b (ClassPartsE4B)
open Sarkozy.HsumProof (paperKappa)
open Sarkozy.NormBoundsPaper (hNG)
open Sarkozy.UpperCapsPaper (PrimeCertificatesUC UpperRecordTables UpperRecordBlocks)
open Sarkozy.PrimeGram (SignedDecompInputsC)
open Sarkozy.ThetaOne (SharpPartsBase)
open Sarkozy.NormBoundsPaper3 (FrontN3 MainFinalObligationsN3 main_goal_nb3)

/-- **The reduced front with `hEs` proved and the fold norms reduced to one prime**: NB3's
`FrontN3` without `hEs` (proved, `eOrthPaperInput`) and with `hNr4` (the block fold families)
replaced by `hFold` (`FoldInputs` at every middle block). All five fields are *open*. -/
structure FrontN4 (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (UpT : UpperRecordTables) : Type 1 where
  /-- UC: the 320 upper anchor certificates and the four middle certificate fields. *Open*. -/
  PCu : PrimeCertificatesUC
  /-- The block-level analytic inputs (B6). *Open*. -/
  BA : BlockAnalytic
  /-- UC: the upper blocks against the record table. *Open*. -/
  UpB : UpperRecordBlocks hW (analyticInputs (PCu.toPC2'.toPC hW hMR hFour) BA) UpT
  /-- PG: the remaining prime inputs of the block Grams. *Open*. -/
  SD : SignedDecompInputsC
    ((UpperCapsPaper.UpperRepairDataS.ofSplit UpT UpB).toCmp hMR hFour)
  /-- FD: at every prime of every middle block, `prop:signed-bounds`(c) for the symmetric and
  skew parts of the prime fold difference at the piece constants, and the component norms
  `c_+ r` (`FoldInputs`). *Open*. -/
  hFold : ∀ b i, blockSite b = .inl i →
    SpecFoldInputs hW (paperKappa i)
      (specF hW (analyticInputs (PCu.toPC2'.toPC hW hMR hFour) BA) b)
      (((UpperCapsPaper.UpperRepairDataS.ofSplit UpT UpB).toCmp hMR hFour).blk b)

/-- **NB3's per-piece matching input at `paperKappa`, proved** (`lem:record:e-orthogonal`(c) with
the monotonicity of `lem:record:exact-marginal-e`(i)). -/
theorem esPrimeInput_paper : Sarkozy.NormBoundsPaper3.EsPrimeInput paperKappa :=
  Sarkozy.NormBoundsPaper3.esPrimeInput_of_paper eOrthPaperInput

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {UpT : UpperRecordTables}

/-- `FrontN3` from `FrontN4`: `hEs := eOrthPaperInput` (proved),
`hNr4 := hNr4_of_inputs … hFold`. -/
noncomputable def FrontN4.toN3 (F : FrontN4 hW hMR hFour UpT) : FrontN3 hW hMR hFour UpT where
  PCu := F.PCu
  BA := F.BA
  UpB := F.UpB
  SD := F.SD
  hEs := eOrthPaperInput
  hNr4 := hNr4_of_inputs hW _ _ F.hFold

/-- **The obligations of `main_goal_nb4`**: `FrontN4` and the class and baseline sharp inputs of
`MainFinalObligationsN3`, typed at `F.toN3`. 3 fields (`F` has 5). -/
structure MainFinalObligationsN4 (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables) : Type 1 where
  /-- The reduced front (UC, PG, FD). -/
  F : FrontN4 hW hMR hFour UpT
  /-- The class inputs (as in `MainFinalObligationsN3`). *Open*. -/
  Cls : ClassPartsE4B ((dvG F.toN3.toK.PC F.toN3.toK.BA F.toN3.toK.Up
    F.toN3.toK.SGp.toSector.toGram.toSG).to3e.toK1
    hB ((dvG F.toN3.toK.PC F.toN3.toK.BA F.toN3.toK.Up F.toN3.toK.SGp.toSector.toGram.toSG).saOfS
      (hNG F.toN3.toK.PC F.toN3.toK.BA F.toN3.toK.Up F.toN3.toK.hNr))
    (hmidG hB hRR F.toN3.toK.PC F.toN3.toK.BA F.toN3.toK.Up F.toN3.toK.SGp.toSector.toGram.toSG
      (hNG F.toN3.toK.PC F.toN3.toK.BA F.toN3.toK.Up F.toN3.toK.hNr))).data
  /-- The baseline inputs of `SF`, `fix`, `env` (as in `MainFinalObligationsN3`). *Open*. -/
  Sh : SharpPartsBase ((dvG F.toN3.toK.PC F.toN3.toK.BA F.toN3.toK.Up
    F.toN3.toK.SGp.toSector.toGram.toSG).to3e.toK1
    hB ((dvG F.toN3.toK.PC F.toN3.toK.BA F.toN3.toK.Up F.toN3.toK.SGp.toSector.toGram.toSG).saOfS
      (hNG F.toN3.toK.PC F.toN3.toK.BA F.toN3.toK.Up F.toN3.toK.hNr))
    (hmidG hB hRR F.toN3.toK.PC F.toN3.toK.BA F.toN3.toK.Up F.toN3.toK.SGp.toSector.toGram.toSG
      (hNG F.toN3.toK.PC F.toN3.toK.BA F.toN3.toK.Up F.toN3.toK.hNr))).toJoint

/-- `MainFinalObligationsN3` from `MainFinalObligationsN4` (definitional). -/
noncomputable def MainFinalObligationsN4.toN3 {hB : Target.BMOR} {hRR : Target.ThetaSmallRR}
    (O : MainFinalObligationsN4 hW hMR hFour hB hRR UpT) :
    MainFinalObligationsN3 hW hMR hFour hB hRR UpT where
  F := O.F.toN3
  Cls := O.Cls
  Sh := O.Sh

/-- **The combined main statement with the fold norms reduced to one prime**
(`main_goal_nb3` with `O.toN3`): `s(N) ≤ C·N^{0.99999}` from H1–H5, H2″, `thm:dl:K`, the record
table `UpT` and `MainFinalObligationsN4`. -/
theorem main_goal_nb4 (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables)
    (O : MainFinalObligationsN4 hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR UpT) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_nb3 hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR UpT O.toN3

end Sarkozy.NormBoundsPaper4
