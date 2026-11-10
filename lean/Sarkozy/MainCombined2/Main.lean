module

public import Sarkozy.UpperCapsPaper.Main
public import Sarkozy.PrimeGram.Main
public import Sarkozy.NormBoundsPaper2.Main

@[expose] public section

/-!
# The combined main statement with the three reductions of 7 November (`main_goal_f1k`)

`MainCombined.main_goal_f1i` takes `MainFinalObligationsGPN` (7 fields: `PC`, `BA`, `Up`, `SGp`,
`hNr`, `Cls`, `Sh`). Three reductions of it are combined here:
* **UC** (`UpperCapsPaper`): `PC` from `PCu : PrimeCertificatesUC` (the 320 upper anchor
  certificates and the four middle fields), with the cap tables proved (`upperCapTables_holds`);
  `Up` from the finite record table `UpT : UpperRecordTables` (a parameter) and the block
  statements `UpB : UpperRecordBlocks` (`UpperRepairDataS.ofSplit`);
* **PG** (`PrimeGram`): `SGp` from `SD : SignedDecompInputsC` (`SignedDecompInputsC.toPrime`);
* **NB2** (`NormBoundsPaper2`): `hNr` from `hNr2`, the four remaining norm families
  (`hNrGPN`).

The structure is in two layers, so that the combination can be re-applied to a statement that
changes only the `Sh` group (TH's `main_goal_theta1`):
* **`FrontK`** (5 fields: `PCu`, `BA`, `UpB`, `SD`, `hNr2`) and its images `FrontK.PC`, `.Up`,
  `.SGp`, `.hNr` in the fields of `MainFinalObligationsGPN` (definitional maps, no `Sh`);
* **`MainFinalObligationsK`** (3 fields: `F : FrontK`, `Cls`, `Sh`), with `Cls`, `Sh` of
  `MainFinalObligationsGPN` at the images; **`toGPN`**;
* **`main_goal_f1k`**: `s(N) ≤ C·N^{0.99999}`, through `main_goal_f1i`.
-/

namespace Sarkozy.MainCombined2

open Sarkozy.PartV Sarkozy.BlockSpecPaper Sarkozy.MainCombined
open Sarkozy.MainFinal (BlockAnalytic)
open Sarkozy.MainFinal2 (PrimeCertificates2 SharpParts2U)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.MainFinalF1 (analyticInputs specF)
open Sarkozy.MainFinalF1b (ClassPartsE4B)
open Sarkozy.HsumProof (paperKappa)
open Sarkozy.UpperRepair (UpperRepairDataS)
open Sarkozy.SignedGram (SignedPrimeInputs)
open Sarkozy.NormBoundsPaper (SpecNormBoundsRest hNG)
open Sarkozy.UpperCapsPaper (PrimeCertificatesUC UpperRecordTables UpperRecordBlocks)
open Sarkozy.PrimeGram (SignedDecompInputsC)
open Sarkozy.NormBoundsPaper2 (SpecNormBoundsRest2 hNrGPN)

/-! ## The front: everything except `Cls` and `Sh` -/

/-- **The reduced front fields** (UC, PG, NB2): the per-prime certificates with the upper anchor
certificates (`PCu`), the block-level analytic inputs (`BA`), the upper blocks against the record
table (`UpB`), the remaining prime inputs of the block Grams (`SD`) and the four remaining middle
norm families (`hNr2`). All five are *open*. -/
structure FrontK (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (UpT : UpperRecordTables) : Type 1 where
  /-- UC: the 320 upper anchor certificates and the four middle certificate fields. *Open*. -/
  PCu : PrimeCertificatesUC
  /-- The block-level analytic inputs (B6). *Open*. -/
  BA : BlockAnalytic
  /-- UC: the upper blocks, with constants at most `UpT` times `r_𝔅` (`lem:record:domain`(ii)).
  *Open*. -/
  UpB : UpperRecordBlocks hW (analyticInputs (PCu.toPC2'.toPC hW hMR hFour) BA) UpT
  /-- PG: the collision bound, `prop:signed-bounds`(c) and the gates at every prime of every
  middle block. *Open*. -/
  SD : SignedDecompInputsC
    ((UpperCapsPaper.UpperRepairDataS.ofSplit UpT UpB).toCmp hMR hFour)
  /-- NB2: the four remaining middle norm families at `paperKappa`. *Open*. -/
  hNr2 : ∀ b i, blockSite b = .inl i →
    SpecNormBoundsRest2 hW (paperIn f1Cell) (paperKappa i) (blockLeast b)
      (specF hW (analyticInputs (PCu.toPC2'.toPC hW hMR hFour) BA) b)
      (((UpperCapsPaper.UpperRepairDataS.ofSplit UpT UpB).toCmp hMR hFour).blk b)

namespace FrontK

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {UpT : UpperRecordTables}

/-- The field `PC` of `MainFinalObligationsGPN` (UC, tables proved). -/
theorem PC (F : FrontK hW hMR hFour UpT) : PrimeCertificates2 := F.PCu.toPC2'

/-- The field `Up` of `MainFinalObligationsGPN` (UC). -/
noncomputable def Up (F : FrontK hW hMR hFour UpT) :
    UpperRepairDataS hW (analyticInputs (F.PC.toPC hW hMR hFour) F.BA) :=
  UpperCapsPaper.UpperRepairDataS.ofSplit UpT F.UpB

/-- The field `SGp` of `MainFinalObligationsGPN` (PG). -/
theorem SGp (F : FrontK hW hMR hFour UpT) : SignedPrimeInputs (F.Up.toCmp hMR hFour) :=
  F.SD.toPrime

/-- The field `hNr` of `MainFinalObligationsGPN` (NB2). -/
theorem hNr (F : FrontK hW hMR hFour UpT) :
    ∀ b i, blockSite b = .inl i →
      SpecNormBoundsRest hW (paperIn f1Cell) (paperKappa i) (blockLeast b)
        (specF hW (analyticInputs (F.PC.toPC hW hMR hFour) F.BA) b)
        ((F.Up.toCmp hMR hFour).blk b) :=
  hNrGPN F.PC F.BA F.Up F.hNr2

end FrontK

/-! ## The obligations and the main statement -/

/-- **The obligations of `main_goal_f1k`**: the reduced front `F` and the groups `Cls`, `Sh` of
`MainFinalObligationsGPN` at its images. 3 fields (`F` has 5). -/
structure MainFinalObligationsK (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables) : Type 1 where
  /-- The reduced front (UC, PG, NB2). -/
  F : FrontK hW hMR hFour UpT
  /-- The class inputs (as in `MainFinalObligationsGPN`). *Open*. -/
  Cls : ClassPartsE4B ((dvG F.PC F.BA F.Up F.SGp.toSector.toGram.toSG).to3e.toK1 hB
    ((dvG F.PC F.BA F.Up F.SGp.toSector.toGram.toSG).saOfS (hNG F.PC F.BA F.Up F.hNr))
    (hmidG hB hRR F.PC F.BA F.Up F.SGp.toSector.toGram.toSG (hNG F.PC F.BA F.Up F.hNr))).data
  /-- The inputs of `SF`, `fix`, `env` (as in `MainFinalObligationsGPN`). *Open*. -/
  Sh : SharpParts2U ((dvG F.PC F.BA F.Up F.SGp.toSector.toGram.toSG).to3e.toK1 hB
    ((dvG F.PC F.BA F.Up F.SGp.toSector.toGram.toSG).saOfS (hNG F.PC F.BA F.Up F.hNr))
    (hmidG hB hRR F.PC F.BA F.Up F.SGp.toSector.toGram.toSG
      (hNG F.PC F.BA F.Up F.hNr))).toJoint

/-- **`MainFinalObligationsGPN` from the combined obligations**: `PC := F.PCu.toPC2'`,
`Up := ofSplit UpT F.UpB`, `SGp := F.SD.toPrime`, `hNr := hNrGPN … F.hNr2`. -/
noncomputable def MainFinalObligationsK.toGPN {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {hB : Target.BMOR} {hRR : Target.ThetaSmallRR}
    {UpT : UpperRecordTables} (O : MainFinalObligationsK hW hMR hFour hB hRR UpT) :
    MainFinalObligationsGPN hW hMR hFour hB hRR where
  PC := O.F.PC
  BA := O.F.BA
  Up := O.F.Up
  SGp := O.F.SGp
  hNr := O.F.hNr
  Cls := O.Cls
  Sh := O.Sh

/-- **The combined main statement at `N^{0.99999}` with the three reductions of 7 November**
(UC, PG, NB2): `main_goal_f1i` at `O.toGPN`. Its hypotheses are H1–H5, H2″, `thm:dl:K`, the
finite record table `UpT` (`UpperRecordTables`) and the obligations `O`. -/
theorem main_goal_f1k (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables)
    (O : MainFinalObligationsK hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR UpT) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_f1i hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O.toGPN

end Sarkozy.MainCombined2
