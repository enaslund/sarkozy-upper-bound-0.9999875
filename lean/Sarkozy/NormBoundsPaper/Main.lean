module

public import Sarkozy.NormBoundsPaper.Constructor
public import Sarkozy.MainCombined.Main

@[expose] public section

/-!
# `main_goal_f1g` with the constant norm families proved (`main_goal_hn`)

`Sarkozy.MainCombined.main_goal_f1g` takes `MainFinalObligationsG` (7 fields). Its field `hN` is
K2's `SpecNormBounds` at `paperKappa` on every middle block: B8's `NormBounds`, ten fields. The two
constant fields `Cs`, `Ca` (`lem:record:accepting-c2`) are proved here
(`Sarkozy.NormBoundsPaper.Const`). This file restates the main statement with `hN` replaced by
**`hNr`**, the seven remaining fields (`SpecNormBoundsRest`, `prop:signed-bounds`(a),(b),(e),
`lem:record:exact-marginal-e`(ii), `lem:merge-repair`), at the same `paperKappa`.

* **`MainFinalObligationsHN`** (7 fields: `PC`, `BA`, `Up`, `SG`, `hNr`, `Cls`, `Sh`);
* `MainFinalObligationsHN.toG` (MRG's `MainFinalObligationsG`, with `hN := hN_of_rest … hNr`);
* **`main_goal_hn`**: `Target.SarkozyBound TargetGoal.epsGoal`.
-/

namespace Sarkozy.NormBoundsPaper

open Sarkozy.PartV Sarkozy.BlockSpecPaper Sarkozy.MainCombined
open Sarkozy.MainFinal (BlockAnalytic)
open Sarkozy.MainFinal2 (PrimeCertificates2 SharpParts2)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.MainFinalF1 (bOf specF Blk analyticInputs SpecNormBounds)
open Sarkozy.MainFinalF1b (ClassPartsE4B)
open Sarkozy.HsumProof (paperKappa)
open Sarkozy.UpperRepair (UpperRepairDataS)
open Sarkozy.MiddleRefinement (SignedSideInputs)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-- `hN` of `MainFinalObligationsG` from the seven remaining families (`hN_of_rest`). -/
theorem hNG (PC : PrimeCertificates2) (BA : BlockAnalytic)
    (Up : UpperRepairDataS hW (analyticInputs (PC.toPC hW hMR hFour) BA))
    (hNr : ∀ b i, blockSite b = .inl i →
      SpecNormBoundsRest hW (paperIn f1Cell) (paperKappa i) (blockLeast b)
        (specF hW (analyticInputs (PC.toPC hW hMR hFour) BA) b) ((Up.toCmp hMR hFour).blk b)) :
    ∀ b i, blockSite b = .inl i →
      SpecNormBounds hW (paperIn f1Cell) (paperKappa i) (blockLeast b)
        (specF hW (analyticInputs (PC.toPC hW hMR hFour) BA) b) ((Up.toCmp hMR hFour).blk b) :=
  hN_of_rest hW _ (fun b => (Up.toCmp hMR hFour).blk b) paperKappa hNr

/-- **The obligations of the combined F1 statement with the constant norms proved**: MRG's
`MainFinalObligationsG` with `hN` (ten norm families) replaced by `hNr` (the seven families other
than `lem:record:accepting-c2` and `Ma₂`, at `paperKappa`). 7 fields. -/
structure MainFinalObligationsHN (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR) where
  /-- The per-prime cut certificates (C8, C9). -/
  PC : PrimeCertificates2
  /-- The block-level analytic inputs (B6). -/
  BA : BlockAnalytic
  /-- The upper blocks (UR). *Open* (`rep`, `hs`, `ha`). -/
  Up : UpperRepairDataS hW (analyticInputs (PC.toPC hW hMR hFour) BA)
  /-- The block Grams of `prop:signed-sides`(i),(ii) (MRG). *Open*. -/
  SG : SignedSideInputs (Up.toCmp hMR hFour).toK1
  /-- **The seven remaining norm families** at `paperKappa` (`prop:signed-bounds`(a),(b),(e),
  `lem:record:exact-marginal-e`(ii), `lem:merge-repair`). *Open*. The constants
  (`lem:record:accepting-c2`) are proved. -/
  hNr : ∀ b i, blockSite b = .inl i →
    SpecNormBoundsRest hW (paperIn f1Cell) (paperKappa i) (blockLeast b)
      (specF hW (analyticInputs (PC.toPC hW hMR hFour) BA) b) ((Up.toCmp hMR hFour).blk b)
  /-- The class inputs (as in `MainFinalObligationsG`). -/
  Cls : ClassPartsE4B ((dvG PC BA Up SG).to3e.toK1 hB ((dvG PC BA Up SG).saOfS (hNG PC BA Up hNr))
    (hmidG hB hRR PC BA Up SG (hNG PC BA Up hNr))).data
  /-- The inputs of `SF`, `fix`, `env` (as in `MainFinalObligationsG`). -/
  Sh : SharpParts2 ((dvG PC BA Up SG).to3e.toK1 hB ((dvG PC BA Up SG).saOfS (hNG PC BA Up hNr))
    (hmidG hB hRR PC BA Up SG (hNG PC BA Up hNr))).toJoint

/-- MRG's `MainFinalObligationsG`. -/
noncomputable def MainFinalObligationsHN.toG {hB : Target.BMOR} {hRR : Target.ThetaSmallRR}
    (O : MainFinalObligationsHN hW hMR hFour hB hRR) :
    MainFinalObligationsG hW hMR hFour hB hRR where
  PC := O.PC
  BA := O.BA
  Up := O.Up
  SG := O.SG
  hN := hNG O.PC O.BA O.Up O.hNr
  Cls := O.Cls
  Sh := O.Sh

/-- **The combined main statement at `N^{0.99999}` with the constant norms proved**
(`main_goal_f1g` with `O.toG`). -/
theorem main_goal_hn (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligationsHN hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_f1g hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O.toG

end Sarkozy.NormBoundsPaper
