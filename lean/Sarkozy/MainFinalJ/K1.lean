module

public import Sarkozy.MainFinal.Main
public import Sarkozy.MainFinalJ.Classes

@[expose] public section

/-!
# K1's main statement with the combined allocation gate

K1's `MainFinal.main_target_paper_final` with `Cls : ClassParts` (B4's five inputs of `JB`, with
the separate lower bound `alloc` of (G2) and the polynomial data `PD`) replaced by E4's
`ClassParts2J` (the combined gate `AllocJ` of `cor:joint-closing`, no `PD`).

`JB := O.Cls.jointBound` (E4's `ClassParts2J.jointBound`, i.e. `jointBound_target_allocJ` at
`ES.toED.toCI`, `ES.toED.toCE`) in place of K1's
`O.Cls.MA.jointBound MainAnchor.card_chamber O.Cls.PD O.Cls.E1 (O.Dv.hB_final hBMOR O.NC)`; every
other field of B1's obligations is K1's, verbatim (`hB_final`, `hL₀_final`, `hT_final`,
`hSA_final`, `SF`, `fix`, `env`). The class inputs enter only through `JB`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MainFinalJ

open Sarkozy.MainFinal
open Sarkozy.TheoremC Sarkozy.RecordExpansion
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PaperNumbers (paperCell)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-- **K1's obligations with the combined gate**: K1's `MainFinalObligations` with
`Cls : ClassParts2J Dv.data` (E4). 5 fields. -/
structure MainFinalObligationsJ (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) where
  /-- The block data (K1). -/
  Dv : FinalBlockData hW hMR hFour
  /-- The 66 per-piece charge bounds (N1). -/
  NC : NumericalCertificates
  /-- `hSA` in explicit per-atom form (B2). -/
  hSA : ComparisonLawPaper.SAExplicit Dv.Cmp.Ci
  /-- The class inputs with the combined allocation gate (E4). -/
  Cls : ClassData.ClassParts2J Dv.data
  /-- The inputs of `SF`, `fix`, `env` (B5). -/
  Sh : SharpParts Dv.toJoint

/-- **To B1's joint obligations**: K1's `toB1` with `JB := O.Cls.jointBound`. -/
noncomputable def MainFinalObligationsJ.toB1 (hBMOR : Target.BMOR)
    (O : MainFinalObligationsJ hW hMR hFour) :
    B1JointFinalObligations paperCell hW hMR hFour O.Dv.AI where
  Dv := O.Dv.toFixed
  hB := O.Dv.hB_final hBMOR O.NC
  hL₀ := O.Dv.hL₀_final hBMOR O.NC
  hT := O.Dv.hT_final
  hSA := O.Dv.hSA_final O.hSA
  JB := O.Cls.jointBound
  SF := (EnvelopeEnergiesPaper.SharpFirstCoupledInputs.ofBlocks O.Dv.toJoint O.Sh.θ O.Sh.hθ
    (EnvelopeEnergiesPaper.paperStageMoments_proved hW O.Dv.toJoint.In O.Sh.hθ O.Sh.hθ'
      O.Dv.toJoint.spec)
    O.Sh.ε O.Sh.hε0 O.Sh.hεt O.Sh.c₁ O.Sh.hc₁ O.Sh.fibre).toSharpFirstInputs
  fix := O.Sh.fixC.toG1
  env := O.Sh.envC.toG1

/-- **K1's main statement with the combined allocation gate** (`thm:main` at `ε = a_T/71`, via
`thm:comparison` with `cor:joint-closing`, `eq:final-joint-closing`). Hypotheses as K1's
`main_target_paper_final`, with `O : MainFinalObligationsJ`. -/
theorem main_target_paper_finalJ (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligationsJ hWeil hMovingRoot hFourCycle) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_joint_B1 hWeil hMovingRoot hFourCycle hThetaSmallRR paperCell
    O.Dv.AI (O.toB1 hBMOR)

end Sarkozy.MainFinalJ
