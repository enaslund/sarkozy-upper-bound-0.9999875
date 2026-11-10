module

public import Sarkozy.MainCombined.Prime
public import Sarkozy.NormBoundsPaper.Main

@[expose] public section





namespace Sarkozy.MainCombined

open Sarkozy.PartV Sarkozy.BlockSpecPaper
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

/-- **The obligations of the combined F1 statement**: `MainFinalObligationsGP` with the middle
norm bounds reduced to HN's seven open families `hNr`. -/
structure MainFinalObligationsGPN (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR) where
  /-- The per-prime cut certificates (C8, C9). -/
  PC : PrimeCertificates2
  /-- The block-level analytic inputs (B6). -/
  BA : BlockAnalytic
  /-- The upper blocks (UR). *Open* (`rep`, `hs`, `ha`). -/
  Up : UpperRepairDataS hW (analyticInputs (PC.toPC hW hMR hFour) BA)
  /-- The prime-level inputs of the block Grams (SGA). *Open*. -/
  SGp : SignedPrimeInputs (Up.toCmp hMR hFour)
  /-- The seven middle norm families not yet proved (HN), at the paper's constants. *Open*. -/
  hNr : ∀ b i, blockSite b = .inl i →
    SpecNormBoundsRest hW (paperIn f1Cell) (paperKappa i) (blockLeast b)
      (specF hW (analyticInputs (PC.toPC hW hMR hFour) BA) b) ((Up.toCmp hMR hFour).blk b)
  /-- The class inputs. -/
  Cls : ClassPartsE4B ((dvG PC BA Up SGp.toSector.toGram.toSG).to3e.toK1 hB
    ((dvG PC BA Up SGp.toSector.toGram.toSG).saOfS (hNG PC BA Up hNr))
    (hmidG hB hRR PC BA Up SGp.toSector.toGram.toSG (hNG PC BA Up hNr))).data
  /-- The inputs of `SF`, `fix`, `env` (upgrade route, with `Sh.fibre`). -/
  Sh : SharpParts2U ((dvG PC BA Up SGp.toSector.toGram.toSG).to3e.toK1 hB
    ((dvG PC BA Up SGp.toSector.toGram.toSG).saOfS (hNG PC BA Up hNr))
    (hmidG hB hRR PC BA Up SGp.toSector.toGram.toSG (hNG PC BA Up hNr))).toJoint

/-- `MainFinalObligationsGP`, with `hN := hNG … hNr` (HN). -/
noncomputable def MainFinalObligationsGPN.toGP {hB : Target.BMOR} {hRR : Target.ThetaSmallRR}
    (O : MainFinalObligationsGPN hW hMR hFour hB hRR) :
    MainFinalObligationsGP hW hMR hFour hB hRR where
  PC := O.PC
  BA := O.BA
  Up := O.Up
  SGp := O.SGp
  hN := hNG O.PC O.BA O.Up O.hNr
  Cls := O.Cls
  Sh := O.Sh.toSharpParts2

/-- **The combined main statement at the owner's goal exponent `N^{0.99999}`**, with the block
Grams at prime level (SGA) and three of the ten middle norm families proved (HN). -/
theorem main_goal_f1i (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligationsGPN hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_f1h hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O.toGP

end Sarkozy.MainCombined
