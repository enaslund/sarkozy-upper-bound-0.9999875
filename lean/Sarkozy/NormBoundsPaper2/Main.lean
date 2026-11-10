module

public import Sarkozy.NormBoundsPaper2.Constructor
public import Sarkozy.MainCombined.PrimeNorms

@[expose] public section

/-!
# `main_goal_f1i` with the merge norms proved (`main_goal_nb2`)

`Sarkozy.MainCombined.main_goal_f1i` takes `MainFinalObligationsGPN` (7 fields). Its field `hNr`
is HN's `SpecNormBoundsRest` at `paperKappa` on every middle block (seven norm families). The
three merge families `Ms`, `Ma`, `Ms₂` (`lem:merge-repair`: `s_b`, `a_b`, `d_b + η_b`) are proved
here (`Sarkozy.NormBoundsPaper2.MirrorBlock`, `Merge2Sym`). This file restates the main statement
with `hNr` replaced by **`hNr2`**, the four remaining families (`SpecNormBoundsRest2`:
`prop:signed-bounds`(a),(b),(e), `lem:record:exact-marginal-e`(ii)), at the same `paperKappa`.

* **`MainFinalObligationsNB2`** (7 fields: `PC`, `BA`, `Up`, `SGp`, `hNr2`, `Cls`, `Sh`);
* `MainFinalObligationsNB2.toGPN` (`MainFinalObligationsGPN`, with `hNr := hNr_of_rest2 … hNr2`);
* **`main_goal_nb2`**: `Target.SarkozyBound TargetGoal.epsGoal`.
-/

namespace Sarkozy.NormBoundsPaper2

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

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-- `hNr` of `MainFinalObligationsGPN` from the four remaining families (`hNr_of_rest2`). -/
theorem hNrGPN (PC : PrimeCertificates2) (BA : BlockAnalytic)
    (Up : UpperRepairDataS hW (analyticInputs (PC.toPC hW hMR hFour) BA))
    (hNr2 : ∀ b i, blockSite b = .inl i →
      SpecNormBoundsRest2 hW (paperIn f1Cell) (paperKappa i) (blockLeast b)
        (specF hW (analyticInputs (PC.toPC hW hMR hFour) BA) b) ((Up.toCmp hMR hFour).blk b)) :
    ∀ b i, blockSite b = .inl i →
      SpecNormBoundsRest hW (paperIn f1Cell) (paperKappa i) (blockLeast b)
        (specF hW (analyticInputs (PC.toPC hW hMR hFour) BA) b) ((Up.toCmp hMR hFour).blk b) :=
  hNr_of_rest2 hW _ (fun b => (Up.toCmp hMR hFour).blk b) paperKappa hNr2

/-- **The obligations of the combined F1 statement with the merge norms proved**:
`MainFinalObligationsGPN` with `hNr` (seven norm families) replaced by `hNr2` (four families, at
`paperKappa`). 7 fields. -/
structure MainFinalObligationsNB2 (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR) where
  /-- The per-prime cut certificates (C8, C9). -/
  PC : PrimeCertificates2
  /-- The block-level analytic inputs (B6). -/
  BA : BlockAnalytic
  /-- The upper blocks (UR). *Open* (`rep`, `hs`, `ha`). -/
  Up : UpperRepairDataS hW (analyticInputs (PC.toPC hW hMR hFour) BA)
  /-- The prime-level inputs of the block Grams (SGA). *Open*. -/
  SGp : SignedPrimeInputs (Up.toCmp hMR hFour)
  /-- **The four remaining middle norm families** at `paperKappa` (`prop:signed-bounds`(a),(b),(e),
  `lem:record:exact-marginal-e`(ii)). *Open*. -/
  hNr2 : ∀ b i, blockSite b = .inl i →
    SpecNormBoundsRest2 hW (paperIn f1Cell) (paperKappa i) (blockLeast b)
      (specF hW (analyticInputs (PC.toPC hW hMR hFour) BA) b) ((Up.toCmp hMR hFour).blk b)
  /-- The class inputs (as in `MainFinalObligationsGPN`). -/
  Cls : ClassPartsE4B ((dvG PC BA Up SGp.toSector.toGram.toSG).to3e.toK1 hB
    ((dvG PC BA Up SGp.toSector.toGram.toSG).saOfS (hNG PC BA Up (hNrGPN PC BA Up hNr2)))
    (hmidG hB hRR PC BA Up SGp.toSector.toGram.toSG (hNG PC BA Up (hNrGPN PC BA Up hNr2)))).data
  /-- The inputs of `SF`, `fix`, `env` (as in `MainFinalObligationsGPN`). -/
  Sh : SharpParts2U ((dvG PC BA Up SGp.toSector.toGram.toSG).to3e.toK1 hB
    ((dvG PC BA Up SGp.toSector.toGram.toSG).saOfS (hNG PC BA Up (hNrGPN PC BA Up hNr2)))
    (hmidG hB hRR PC BA Up SGp.toSector.toGram.toSG
      (hNG PC BA Up (hNrGPN PC BA Up hNr2)))).toJoint

/-- `MainFinalObligationsGPN`, with `hNr := hNrGPN … hNr2`. -/
noncomputable def MainFinalObligationsNB2.toGPN {hB : Target.BMOR} {hRR : Target.ThetaSmallRR}
    (O : MainFinalObligationsNB2 hW hMR hFour hB hRR) :
    MainFinalObligationsGPN hW hMR hFour hB hRR where
  PC := O.PC
  BA := O.BA
  Up := O.Up
  SGp := O.SGp
  hNr := hNrGPN O.PC O.BA O.Up O.hNr2
  Cls := O.Cls
  Sh := O.Sh

/-- **The combined main statement at `N^{0.99999}` with the merge norms proved**
(`main_goal_f1i` with `O.toGPN`). -/
theorem main_goal_nb2 (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligationsNB2 hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_f1i hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O.toGPN

end Sarkozy.NormBoundsPaper2
