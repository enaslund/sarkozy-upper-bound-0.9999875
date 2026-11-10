module

public import Sarkozy.SharpBase.Means
public import Sarkozy.MainCombined2.Theta1

@[expose] public section

/-!
# A constructor of `ThetaOne.SharpPartsBase` and the main statement with it

SH2 (7 November 2026). `ThetaOne.SharpPartsBase D` (the `Sh` group of `main_goal_theta1k`) has
three parts, `SF`, `fixM`, `envM`. With `SharpBase.Means`:

* **`SharpBaseInputs D`**: `SF` (TH's `SharpFirstBaseInputs`, unchanged: open `hfold`, `hrem`),
  one constant `c₂ ≥ 0` and the four summations of the explicit `rch`
  (`RchSumFixL/R`, `RchSumEnvL/R`; `lem:sharp-first`), at the sharp decompositions `SF.dec`.
  Everything else in `fixM`, `envM` is proved: `hdiffL/R` (the sharp-first differences), `hzu`
  (the scale condition), the reduction of `hr2L/R` to the `rch` summations, and the paper-data
  facts (parity `paperEP`, `blockSel = selPre`);
* **`SharpBaseInputs.toSharpPartsBase`**: the constructor, given that every block is nonempty
  (`ThetaOne.paperAtomMap_paperBlockOf_surjective` for the paper's layout);
* **`MainFinalObligationsSH2`**, **`main_goal_theta1_sh2`**: `main_goal_theta1k` with
  `Sh : SharpBaseInputs` in place of `Sh : SharpPartsBase`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.SharpBase

open Sarkozy.PartV Sarkozy.JointClosing Sarkozy.BlockSpecPaper Sarkozy.MainCombined
  Sarkozy.MainCombined2
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
structure SharpBaseInputs {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
    {hW : Target.Weil} (D : JointBlockDataTarget blockOf hW) where
  /-- `SF` on the baseline route (TH's `SharpFirstBaseInputs`). *Open*: `SF.hfold`,
  `SF.hrem`. -/
  SF : ThetaOne.SharpFirstBaseInputs D.data
  /-- The constant of the `rch` summations. -/
  c₂ : ℝ
  hc₂ : 0 ≤ c₂
  /-- The summation of `rchFixL` (`Sh.fixM.hr2L`). *Open*. -/
  fixL : RchSumFixL (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise SF.dec c₂
  /-- The summation of `rchFixR` (`Sh.fixM.hr2R`). *Open*. -/
  fixR : RchSumFixR (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise SF.dec c₂
  /-- The summation of `rchEnvL` (`Sh.envM.hr2L`). *Open*. -/
  envL : RchSumEnvL (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise SF.dec c₂
  /-- The summation of `rchEnvR` (`Sh.envM.hr2R`). *Open*. -/
  envR : RchSumEnvR (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise SF.dec c₂

/-- **A constructor of `ThetaOne.SharpPartsBase`** (`lem:sharp-first`, `lem:envelope-energy`,
`lem:bracket-energy`, `lem:scale-conditions`): `SF` is passed through; `fixM`, `envM` are
`fixMeansBase`, `envMeansBase` at the paper's standing data (parity
`parity_blockPaperStandingAt`, `blockSel ≤ selPre` by `hsel_blockPaperStandingAt`) and nonempty
blocks `hne`. -/
noncomputable def SharpBaseInputs.toSharpPartsBase {B : Type} [Fintype B] [DecidableEq B]
    {blockOf : PaperJ0 → B} {hW : Target.Weil} {D : JointBlockDataTarget blockOf hW}
    (hne : ∀ β, ∃ i, PartVLaws.paperAtomMap blockOf i = β) (I : SharpBaseInputs D) :
    ThetaOne.SharpPartsBase D where
  SF := I.SF
  fixM := fixMeansBase _ D.data paper_pairwise I.SF.dec TargetLedger.targetDecay_nonneg
    (DensityChain2.parity_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
    (DensityChain2.hsel_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _) hne
    I.c₂ I.hc₂ I.fixL I.fixR
  envM := envMeansBase _ D.data paper_pairwise I.SF.dec TargetLedger.targetDecay_nonneg
    (DensityChain2.parity_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
    (DensityChain2.hsel_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _) hne
    I.c₂ I.hc₂ I.envL I.envR

/-- **The obligations of `main_goal_theta1_sh2`**: those of `main_goal_theta1k` with
`Sh : SharpBaseInputs` (SH2) in place of `Sh : SharpPartsBase`. 3 fields. -/
structure MainFinalObligationsSH2 (hW : Target.Weil) (hMR : Target.MovingRoot)
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
  Sh : SharpBaseInputs ((dvG F.PC F.BA F.Up F.SGp.toSector.toGram.toSG).to3e.toK1 hB
    ((dvG F.PC F.BA F.Up F.SGp.toSector.toGram.toSG).saOfS (hNG F.PC F.BA F.Up F.hNr))
    (hmidG hB hRR F.PC F.BA F.Up F.SGp.toSector.toGram.toSG
      (hNG F.PC F.BA F.Up F.hNr))).toJoint

/-- `MainFinalObligationsKT1` from SH2's obligations, with
`Sh := Sh.toSharpPartsBase (paperAtomMap_paperBlockOf_surjective f1Cell)`. -/
noncomputable def MainFinalObligationsSH2.toKT1 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {hB : Target.BMOR} {hRR : Target.ThetaSmallRR}
    {UpT : UpperRecordTables} (O : MainFinalObligationsSH2 hW hMR hFour hB hRR UpT) :
    MainFinalObligationsKT1 hW hMR hFour hB hRR UpT where
  F := O.F
  Cls := O.Cls
  Sh := O.Sh.toSharpPartsBase (ThetaOne.paperAtomMap_paperBlockOf_surjective f1Cell)

/-- **`main_goal_theta1k` with SH2's sharp inputs** (`thm:main` at `ε = 10⁻⁵`, baseline
induction `ϑ = 1`): the sharp-first differences `hdiff`, the scale condition and the reduction of
the `r₂` summations are proved; the `Sh` group is `SF` and the four `rch` summations. -/
theorem main_goal_theta1_sh2 (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables)
    (O : MainFinalObligationsSH2 hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR UpT) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_theta1k hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR UpT O.toKT1

end Sarkozy.SharpBase
