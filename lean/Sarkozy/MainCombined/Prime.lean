module

public import Sarkozy.MainCombined.Main
public import Sarkozy.SignedGram.Main

@[expose] public section




namespace Sarkozy.MainCombined

open Sarkozy.PartV Sarkozy.BlockSpecPaper
open Sarkozy.MainFinal (BlockAnalytic)
open Sarkozy.MainFinal2 (PrimeCertificates2 SharpParts2)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.MainFinalF1 (analyticInputs specF SpecNormBounds)
open Sarkozy.MainFinalF1b (ClassPartsE4B)
open Sarkozy.HsumProof (paperKappa)
open Sarkozy.UpperRepair (UpperRepairDataS)
open Sarkozy.SignedGram (SignedPrimeInputs)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-- **The obligations of the combined F1 statement, with the block Grams at prime level.**
`MainFinalObligationsG` with `SG` replaced by SGA's `SGp`. -/
structure MainFinalObligationsGP (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR) where
  /-- The per-prime cut certificates (C8, C9). -/
  PC : PrimeCertificates2
  /-- The block-level analytic inputs (B6). -/
  BA : BlockAnalytic
  /-- The upper blocks (UR). *Open* (`rep`, `hs`, `ha`). -/
  Up : UpperRepairDataS hW (analyticInputs (PC.toPC hW hMR hFour) BA)
  /-- **The prime-level inputs of the block Grams** (SGA): at each prime of each middle block, the
  prime Gram on centred functions and the centred-norm bound of `prop:signed-bounds`(c). *Open*. -/
  SGp : SignedPrimeInputs (Up.toCmp hMR hFour)
  /-- The middle norm bounds at the paper's constants. *Open*. -/
  hN : ∀ b i, blockSite b = .inl i →
    SpecNormBounds hW (paperIn f1Cell) (paperKappa i) (blockLeast b)
      (specF hW (analyticInputs (PC.toPC hW hMR hFour) BA) b) ((Up.toCmp hMR hFour).blk b)
  /-- The class inputs. -/
  Cls : ClassPartsE4B ((dvG PC BA Up SGp.toSector.toGram.toSG).to3e.toK1 hB
    ((dvG PC BA Up SGp.toSector.toGram.toSG).saOfS hN)
    (hmidG hB hRR PC BA Up SGp.toSector.toGram.toSG hN)).data
  /-- The inputs of `SF`, `fix`, `env`. -/
  Sh : SharpParts2 ((dvG PC BA Up SGp.toSector.toGram.toSG).to3e.toK1 hB
    ((dvG PC BA Up SGp.toSector.toGram.toSG).saOfS hN)
    (hmidG hB hRR PC BA Up SGp.toSector.toGram.toSG hN)).toJoint

/-- `MainFinalObligationsG`, with `SG := SGp.toSector.toGram.toSG` (SGA). -/
noncomputable def MainFinalObligationsGP.toG {hB : Target.BMOR} {hRR : Target.ThetaSmallRR}
    (O : MainFinalObligationsGP hW hMR hFour hB hRR) : MainFinalObligationsG hW hMR hFour hB hRR where
  PC := O.PC
  BA := O.BA
  Up := O.Up
  SG := O.SGp.toSector.toGram.toSG
  hN := O.hN
  Cls := O.Cls
  Sh := O.Sh

/-- **The combined main statement at the owner's goal exponent `N^{0.99999}`**, with the block
Grams of `prop:signed-sides` reduced to prime level (SGA). -/
theorem main_goal_f1h (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligationsGP hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_f1g hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O.toG

end Sarkozy.MainCombined
