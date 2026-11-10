module

public import Sarkozy.SharpBase2.Fields
public import Sarkozy.SharpBase.Parts
public import Sarkozy.MainCombined2.Theta1

@[expose] public section

/-!
# A constructor of `ThetaOne.SharpPartsBase` with the per-term remainders, and the main statement

SH2 (7 November 2026). As `SharpBase.Parts`, with `fixM`, `envM` built by `SharpBase2.fixMeansPT`,
`envMeansPT` (per-term geometric means of `lem:sharp-first`):

* **`SharpBaseInputsPT D`**: `SF` (TH's `SharpFirstBaseInputs`, open `hfold`, `hrem`), `c₂ ≥ 0`
  and the four summations `RchSumPTFixL/R`, `RchSumPTEnvL/R` of the per-term remainders;
* **`SharpBaseInputsPT.toSharpPartsBase`**: the constructor (nonempty blocks `hne`);
* **`MainFinalObligationsSH3`**, **`main_goal_theta1_sh3`**: `main_goal_theta1k` with
  `Sh : SharpBaseInputsPT`.

Compared with `SharpBase.SharpBaseInputs` (`main_goal_theta1_sh2`) only the four summation
inputs change: their integrands no longer contain cross terms between the small pieces' main
terms and the large pieces' energies (`SharpBase2.PerTerm`).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.SharpBase2

open Sarkozy.PartV Sarkozy.JointClosing Sarkozy.BlockSpecPaper Sarkozy.MainCombined
  Sarkozy.MainCombined2 Sarkozy.SharpBase
open Sarkozy.EnvelopeEnergiesPaper (paper_pairwise)
open Sarkozy.CancellationSteps (PaperJ0)
open Sarkozy.MainFinalF1b (ClassPartsE4B)
open Sarkozy.NormBoundsPaper (hNG)
open Sarkozy.UpperCapsPaper (UpperRecordTables)
open Sarkozy.AnalyticCells (f1Cell)

/-- **The remaining inputs of `Sh` at `ϑ = 1`** after SH2: `SF` as in TH's `SharpPartsBase`, and
for `fixM`, `envM` only the four summations of the explicit sharp-first remainders `rch`
(`lem:sharp-first`, the error terms; `lem:record:density-dc`, `lem:record:density-lp`), with one
constant `c₂`, at the decompositions `SF.dec`. 7 fields. -/
structure SharpBaseInputsPT {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
    {hW : Target.Weil} (D : JointBlockDataTarget blockOf hW) where
  /-- `SF` on the baseline route (TH's `SharpFirstBaseInputs`). *Open*: `SF.hfold`,
  `SF.hrem`. -/
  SF : ThetaOne.SharpFirstBaseInputs D.data
  /-- The constant of the `rch` summations. -/
  c₂ : ℝ
  hc₂ : 0 ≤ c₂
  /-- The summation of `rchFixL` (`Sh.fixM.hr2L`). *Open*. -/
  fixL : RchSumPTFixL (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise SF.dec c₂
  /-- The summation of `rchFixR` (`Sh.fixM.hr2R`). *Open*. -/
  fixR : RchSumPTFixR (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise SF.dec c₂
  /-- The summation of `rchEnvL` (`Sh.envM.hr2L`). *Open*. -/
  envL : RchSumPTEnvL (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise SF.dec c₂
  /-- The summation of `rchEnvR` (`Sh.envM.hr2R`). *Open*. -/
  envR : RchSumPTEnvR (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise SF.dec c₂

/-- **A constructor of `ThetaOne.SharpPartsBase`** (`lem:sharp-first`, `lem:envelope-energy`,
`lem:bracket-energy`, `lem:scale-conditions`): `SF` is passed through; `fixM`, `envM` are
`fixMeansPT`, `envMeansPT` at the paper's standing data (parity
`parity_blockPaperStandingAt`, `blockSel ≤ selPre` by `hsel_blockPaperStandingAt`) and nonempty
blocks `hne`. -/
noncomputable def SharpBaseInputsPT.toSharpPartsBase {B : Type} [Fintype B] [DecidableEq B]
    {blockOf : PaperJ0 → B} {hW : Target.Weil} {D : JointBlockDataTarget blockOf hW}
    (hne : ∀ β, ∃ i, PartVLaws.paperAtomMap blockOf i = β) (I : SharpBaseInputsPT D) :
    ThetaOne.SharpPartsBase D where
  SF := I.SF
  fixM := fixMeansPT _ D.data paper_pairwise I.SF.dec TargetLedger.targetDecay_nonneg
    (DensityChain2.parity_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
    (DensityChain2.hsel_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _) hne
    I.c₂ I.hc₂ I.fixL I.fixR
  envM := envMeansPT _ D.data paper_pairwise I.SF.dec TargetLedger.targetDecay_nonneg
    (DensityChain2.parity_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
    (DensityChain2.hsel_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _) hne
    I.c₂ I.hc₂ I.envL I.envR

/-- **The obligations of `main_goal_theta1_sh3`**: those of `main_goal_theta1k` with
`Sh : SharpBaseInputsPT` (SH2, per-term remainders) in place of `Sh : SharpPartsBase`. 3 fields. -/
structure MainFinalObligationsSH3 (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables) : Type 1 where
  /-- The reduced front (UC, PG, NB2). -/
  F : FrontK hW hMR hFour UpT
  /-- The class inputs. *Open*. -/
  Cls : ClassPartsE4B ((dvG F.PC F.BA F.Up F.SGp.toSector.toGram.toSG).to3e.toK1 hB
    ((dvG F.PC F.BA F.Up F.SGp.toSector.toGram.toSG).saOfS (hNG F.PC F.BA F.Up F.hNr))
    (hmidG hB hRR F.PC F.BA F.Up F.SGp.toSector.toGram.toSG (hNG F.PC F.BA F.Up F.hNr))).data
  /-- **The remaining sharp inputs** (SH2). *Open*: `SF.hfold`, `SF.hrem` and the four `rch`
  summations. -/
  Sh : SharpBaseInputsPT ((dvG F.PC F.BA F.Up F.SGp.toSector.toGram.toSG).to3e.toK1 hB
    ((dvG F.PC F.BA F.Up F.SGp.toSector.toGram.toSG).saOfS (hNG F.PC F.BA F.Up F.hNr))
    (hmidG hB hRR F.PC F.BA F.Up F.SGp.toSector.toGram.toSG
      (hNG F.PC F.BA F.Up F.hNr))).toJoint

/-- `MainFinalObligationsKT1` from SH2's obligations, with
`Sh := Sh.toSharpPartsBase (paperAtomMap_paperBlockOf_surjective f1Cell)`. -/
noncomputable def MainFinalObligationsSH3.toKT1 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {hB : Target.BMOR} {hRR : Target.ThetaSmallRR}
    {UpT : UpperRecordTables} (O : MainFinalObligationsSH3 hW hMR hFour hB hRR UpT) :
    MainFinalObligationsKT1 hW hMR hFour hB hRR UpT where
  F := O.F
  Cls := O.Cls
  Sh := O.Sh.toSharpPartsBase (ThetaOne.paperAtomMap_paperBlockOf_surjective f1Cell)

/-- **`main_goal_theta1k` with SH2's per-term sharp inputs** (`thm:main` at `ε = 10⁻⁵`, baseline
induction `ϑ = 1`): the sharp-first differences `hdiff`, the scale condition and the reduction of
the `r₂` summations are proved; the `Sh` group is `SF` and the four `rch` summations. -/
theorem main_goal_theta1_sh3 (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables)
    (O : MainFinalObligationsSH3 hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR UpT) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_theta1k hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR UpT O.toKT1

end Sarkozy.SharpBase2
