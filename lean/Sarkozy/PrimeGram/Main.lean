module

public import Sarkozy.PrimeGram.BlockRef
public import Sarkozy.MainCombined.PrimeNorms

@[expose] public section

/-!
# The combined main statement with `SGp` reduced to the remaining prime inputs (PG)

`MainCombined.MainFinalObligationsGPN` (7 fields: `PC`, `BA`, `Up`, **`SGp`**, `hNr`, `Cls`, `Sh`)
with SGA's `SGp` replaced by **`SD : SignedDecompInputsC`**: at every prime of every middle block,
* `lem:record:conditional-collision`(d) (`CollisionBound`, the constant `c_col`);
* `prop:signed-bounds`(c): the centred signed record `O₀ + L^m_t + R^new`, `‖R^new‖ ≤ e_sg q`
  (`NewDecomp`), and the centred components `≤ c_+ r` (`CentredNorm`);
* the numerical gates (`GateAt`, with the paper's `e_o` of `eq:signed-constants`, `eoP`).

Between `SD` and `SGp` (all proved here): the features of `lem:actual-features` at `m₀` and the
frame bound (d); `lem:record:direct-gram` at the actual features; `lem:old-f-law`(b)(ii) and (f);
the prime Gram on the centred functions and the reference centred norm.

* **`MainFinalObligationsPG`** (7 fields), **`toGPN`**, **`main_goal_f1j`**: `s(N) ≤ C·N^{0.99999}`.
-/

namespace Sarkozy.PrimeGram

open Sarkozy.PartV Sarkozy.BlockSpecPaper Sarkozy.MainCombined
open Sarkozy.MainFinal (BlockAnalytic)
open Sarkozy.MainFinal2 (PrimeCertificates2 SharpParts2U)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.MainFinalF1 (analyticInputs specF)
open Sarkozy.MainFinalF1b (ClassPartsE4B)
open Sarkozy.HsumProof (paperKappa)
open Sarkozy.UpperRepair (UpperRepairDataS)
open Sarkozy.NormBoundsPaper (SpecNormBoundsRest hNG)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-- **The obligations of the combined F1 statement with `SGp` reduced** (PG):
`MainFinalObligationsGPN` with `SGp` replaced by `SD`. 7 fields. -/
structure MainFinalObligationsPG (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR) where
  /-- The per-prime cut certificates (C8, C9). -/
  PC : PrimeCertificates2
  /-- The block-level analytic inputs (B6). -/
  BA : BlockAnalytic
  /-- The upper blocks (UR). *Open*. -/
  Up : UpperRepairDataS hW (analyticInputs (PC.toPC hW hMR hFour) BA)
  /-- **The remaining prime inputs of the block Grams** (PG): the collision bound,
  `prop:signed-bounds`(c) and the gates. *Open*. -/
  SD : SignedDecompInputsC (Up.toCmp hMR hFour)
  /-- The seven middle norm families not yet proved (HN). *Open*. -/
  hNr : ∀ b i, blockSite b = .inl i →
    SpecNormBoundsRest hW (paperIn f1Cell) (paperKappa i) (blockLeast b)
      (specF hW (analyticInputs (PC.toPC hW hMR hFour) BA) b) ((Up.toCmp hMR hFour).blk b)
  /-- The class inputs. -/
  Cls : ClassPartsE4B ((dvG PC BA Up SD.toPrime.toSector.toGram.toSG).to3e.toK1 hB
    ((dvG PC BA Up SD.toPrime.toSector.toGram.toSG).saOfS (hNG PC BA Up hNr))
    (hmidG hB hRR PC BA Up SD.toPrime.toSector.toGram.toSG (hNG PC BA Up hNr))).data
  /-- The inputs of `SF`, `fix`, `env`. -/
  Sh : SharpParts2U ((dvG PC BA Up SD.toPrime.toSector.toGram.toSG).to3e.toK1 hB
    ((dvG PC BA Up SD.toPrime.toSector.toGram.toSG).saOfS (hNG PC BA Up hNr))
    (hmidG hB hRR PC BA Up SD.toPrime.toSector.toGram.toSG (hNG PC BA Up hNr))).toJoint

/-- `MainFinalObligationsGPN`, with `SGp := SD.toPrime` (PG). -/
noncomputable def MainFinalObligationsPG.toGPN {hB : Target.BMOR} {hRR : Target.ThetaSmallRR}
    (O : MainFinalObligationsPG hW hMR hFour hB hRR) :
    MainFinalObligationsGPN hW hMR hFour hB hRR where
  PC := O.PC
  BA := O.BA
  Up := O.Up
  SGp := O.SD.toPrime
  hNr := O.hNr
  Cls := O.Cls
  Sh := O.Sh

/-- **The combined main statement at `N^{0.99999}` with `SGp` reduced** to the collision bound,
`prop:signed-bounds`(c) and the gates (PG). -/
theorem main_goal_f1j (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligationsPG hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_f1i hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O.toGPN

end Sarkozy.PrimeGram
