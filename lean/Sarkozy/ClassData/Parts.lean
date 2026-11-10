module

public import Sarkozy.ClassData.JointMean
public import Sarkozy.ClassData.Steps
public import Sarkozy.MainFinal2.Obligations

@[expose] public section






open Filter Finset
open scoped Topology

namespace Sarkozy.ClassData

open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper Sarkozy.MainFinal2
open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.JointClosing
open Sarkozy.PartVLaws (paperAtomMap)
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.GramBracketPaper

/-- **K2's class inputs with the combined allocation gate** (`cor:joint-closing`): `ClassParts2`
with `MD : MeanDataJ` and without `PD`. *Open*: as in K2 (fields 20–24, 41, 42, 44, 45), with
field 46 in the combined form `AllocJ` and field 43 removed. -/
structure ClassParts2J {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
    (D : TheoremCBlock.ComparisonData targetDecay paperM0 (paperAtomMap blockOf)
    paperTail paperPr paperH Chamber) where
  cd : ClassInputsPaper.ClassData D.CL
  ES : ClassEnergySteps D cd
  E1 : E1Inputs D
  MD : MeanDataJ ES.toED

/-- **The joint bound `JB` from `ClassParts2J`** (`cor:joint-closing`, `eq:final-joint-closing`). -/
theorem ClassParts2J.jointBound {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
    {D : TheoremCBlock.ComparisonData targetDecay paperM0 (paperAtomMap blockOf) paperTail paperPr
      paperH Chamber} (C : ClassParts2J D) :
    JointBound D targetLedger.jointConstant :=
  C.MD.jointBound MainAnchor.card_chamber (C.E1.toE1 targetDecay_nonneg)

/-- **K2's `ClassParts2` gives `ClassParts2J`** (`MeanDataJ.ofMeanData`, given `B ≤ B^{ledger}`). -/
noncomputable def ClassParts2.toJ {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
    {D : TheoremCBlock.ComparisonData targetDecay paperM0 (paperAtomMap blockOf) paperTail paperPr
      paperH Chamber} (C : ClassParts2 D) (hB : D.B ≤ targetLedger.B) : ClassParts2J D where
  cd := C.cd
  ES := C.ES
  E1 := C.E1
  MD := MeanDataJ.ofMeanData C.PD hB C.MD

end Sarkozy.ClassData
