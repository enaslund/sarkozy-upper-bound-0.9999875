module

public import Sarkozy.NormBoundsPaper3.EsPaper
public import Sarkozy.MainCombined2.Theta1

@[expose] public section

/-!
# `main_goal_theta1k` with the matching norms reduced (`main_goal_nb3`)

`Sarkozy.MainCombined2.main_goal_theta1k` takes `MainFinalObligationsKT1` (`F : FrontK`, `Cls`,
`Sh`). The front field `F.hNr2` is NB2's four remaining middle norm families at `paperKappa`
(`Fs`, `Fa`, `Es`, `Ea`). Here:

* `Ea` (`lem:record:exact-marginal-e`(ii), skew) is proved (`match_skew_paper`);
* `Es` (`lem:record:exact-marginal-e`(ii), symmetric) is proved from the one-prime lemma
  `lem:record:e-orthogonal`(c), taken verbatim at the paper's constant `s^E_p`
  (`EOrthPaperInput`; `esPrimeInput_of_paper`, `match_sym_paper`).

* **`FrontN3`** (6 fields: `PCu`, `BA`, `UpB`, `SD`, **`hEs`**, **`hNr4`**): `FrontK` with `hNr2`
  replaced by `lem:record:e-orthogonal`(c) (`hEs : EOrthPaperInput`) and the two fold families
  `hNr4`; `FrontN3.toK` (`hNr2 := hNr2_of_rest4 … (esPrimeInput_of_paper hEs) hNr4`);
* **`MainFinalObligationsN3`** (3 fields: `F : FrontN3`, `Cls`, `Sh`, typed at `F.toK`);
  `toKT1`;
* **`main_goal_nb3`**: `Target.SarkozyBound TargetGoal.epsGoal`, through `main_goal_theta1k`.
-/

namespace Sarkozy.NormBoundsPaper3

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

/-- **The reduced front with the matching norms reduced**: `MainCombined2.FrontK` with `hNr2`
(four families) replaced by the one-prime lemma `lem:record:e-orthogonal`(c) at the paper's
constant (`hEs`) and the two fold families `hNr4` (`prop:signed-bounds`(a),(b),(e)). All six
fields are *open*. -/
structure FrontN3 (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
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
  /-- NB3: `lem:record:e-orthogonal`(c), `‖Sym(K₁ − K^E_0)‖ ≤ s^E_p` at every prime
  `p ≡ 3 (mod 4)`, `p ≥ 2^20`. *Open*. -/
  hEs : EOrthPaperInput
  /-- NB3: the two fold families at `paperKappa` (`prop:signed-bounds`(a),(b),(e)). *Open*. -/
  hNr4 : ∀ b i, blockSite b = .inl i →
    SpecNormBoundsRest4 hW (paperIn f1Cell) (paperKappa i) (blockLeast b)
      (specF hW (analyticInputs (PCu.toPC2'.toPC hW hMR hFour) BA) b)
      (((UpperCapsPaper.UpperRepairDataS.ofSplit UpT UpB).toCmp hMR hFour).blk b)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {UpT : UpperRecordTables}

/-- `FrontK` from `FrontN3`: `hNr2 := hNr2_of_rest4 … (esPrimeInput_of_paper hEs) hNr4`. -/
noncomputable def FrontN3.toK (F : FrontN3 hW hMR hFour UpT) : FrontK hW hMR hFour UpT where
  PCu := F.PCu
  BA := F.BA
  UpB := F.UpB
  SD := F.SD
  hNr2 := hNr2_of_rest4 hW _ _ (esPrimeInput_of_paper F.hEs) F.hNr4

/-- **The obligations of `main_goal_nb3`**: `FrontN3` and the class and baseline sharp inputs
of `MainFinalObligationsKT1`, typed at `F.toK`. 3 fields (`F` has 6). -/
structure MainFinalObligationsN3 (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables) : Type 1 where
  /-- The reduced front (UC, PG, NB3). -/
  F : FrontN3 hW hMR hFour UpT
  /-- The class inputs (as in `MainFinalObligationsKT1`). *Open*. -/
  Cls : ClassPartsE4B ((dvG F.toK.PC F.toK.BA F.toK.Up F.toK.SGp.toSector.toGram.toSG).to3e.toK1
    hB ((dvG F.toK.PC F.toK.BA F.toK.Up F.toK.SGp.toSector.toGram.toSG).saOfS
      (hNG F.toK.PC F.toK.BA F.toK.Up F.toK.hNr))
    (hmidG hB hRR F.toK.PC F.toK.BA F.toK.Up F.toK.SGp.toSector.toGram.toSG
      (hNG F.toK.PC F.toK.BA F.toK.Up F.toK.hNr))).data
  /-- The baseline inputs of `SF`, `fix`, `env` (as in `MainFinalObligationsKT1`). *Open*. -/
  Sh : SharpPartsBase ((dvG F.toK.PC F.toK.BA F.toK.Up F.toK.SGp.toSector.toGram.toSG).to3e.toK1
    hB ((dvG F.toK.PC F.toK.BA F.toK.Up F.toK.SGp.toSector.toGram.toSG).saOfS
      (hNG F.toK.PC F.toK.BA F.toK.Up F.toK.hNr))
    (hmidG hB hRR F.toK.PC F.toK.BA F.toK.Up F.toK.SGp.toSector.toGram.toSG
      (hNG F.toK.PC F.toK.BA F.toK.Up F.toK.hNr))).toJoint

/-- `MainFinalObligationsKT1` from `MainFinalObligationsN3` (definitional). -/
noncomputable def MainFinalObligationsN3.toKT1 {hB : Target.BMOR} {hRR : Target.ThetaSmallRR}
    (O : MainFinalObligationsN3 hW hMR hFour hB hRR UpT) :
    MainFinalObligationsKT1 hW hMR hFour hB hRR UpT where
  F := O.F.toK
  Cls := O.Cls
  Sh := O.Sh

/-- **The combined main statement with the matching norms reduced** (`main_goal_theta1k` with
`O.toKT1`): `s(N) ≤ C·N^{0.99999}` from H1–H5, H2″, `thm:dl:K`, the record table `UpT` and
`MainFinalObligationsN3`. -/
theorem main_goal_nb3 (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables)
    (O : MainFinalObligationsN3 hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR UpT) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_theta1k hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR UpT O.toKT1

end Sarkozy.NormBoundsPaper3
