module

public import Sarkozy.HsumProof.ConstructorK
public import Sarkozy.HsumProof.PaperKappa
public import Sarkozy.TargetGoal.Main

@[expose] public section

/-!
# `SA.hsum` removed, with `κ` fixed to the paper's constants (HS)

`SAParts3P` is `MainFinalF1.SAParts3` with
* `κ := paperKappa`, the paper's `(s_F, a_F, ℓ_t, s_E, a_E)` at the 33 piece starts
  (`cert:signed-local`; `PaperKappa.lean`), so the data field `κ` and its side condition `hκ` are
  gone (`paperKappa_nonneg`);
* `hsum` replaced by the side condition `hLed : PaperLedgers Cs Ca` (the per-record data have the
  paper's state ledgers, `def:upper-comparison`); `hsum` is `hsum_paperKappa`.

Fields: the data `Cs`, `Ca` with `hCs`, `hCa`, `hLed`, and the analytic `hR`, `hN` (unchanged, at
`κ = paperKappa`). `main_target_f1_final3cP` is `main_target_f1_final3c` from
`MainFinalObligations3cP`, and `main_goal_f1P` is `TargetGoal.main_goal_f1` (the owner's goal
`N^{0.99999}`) from the same obligations.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.HsumProof

open Sarkozy.MainFinalF1
open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.MainFinal (MiddleConsts)
open Sarkozy.MainFinal2 (SharpParts2)
open Sarkozy.MainFinalJ (ClassPartsE4)
open Sarkozy.NumericalFields (KappaNonneg)
open Sarkozy.AnalyticCells (f1Cell)

/-- **`SAParts3` at the paper's constants, without `hsum`.** -/
structure SAParts3P (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs f1Cell) (C : ComparisonParts3 hW hMR hFour A) where
  /-- The per-band record coefficients. Data. -/
  Cs : Fin 310 → UpIdx → ℝ
  Ca : Fin 310 → UpIdx → ℝ
  hCs : ∀ k i, 0 ≤ Cs k i
  hCa : ∀ k i, 0 ≤ Ca k i
  /-- **The data have the paper's state ledgers.** Side condition on the data. -/
  hLed : PaperLedgers Cs Ca
  /-- The upper per-record bounds (`prop:record:upper`(ii)). *Open* (analytic). -/
  hR : C.toK2.toK1.UpperRecs hW A Cs Ca hCs hCa
  /-- The twelve norm bounds of every middle block at the paper's constants. *Open* (analytic). -/
  hN : ∀ b i, blockSite b = .inl i →
    SpecNormBounds hW (paperIn f1Cell) (paperKappa i) (blockLeast b) (specF hW A b) (C.toK2.blk b)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-- **`SAParts3` from `SAParts3P`**: `κ = paperKappa`, `hsum` is `hsum_paperKappa`. -/
noncomputable def SAParts3P.toSAParts3 {A : PaperAnalyticInputs f1Cell}
    {C : ComparisonParts3 hW hMR hFour A} (S : SAParts3P hW hMR hFour A C) :
    SAParts3 hW hMR hFour A C where
  Cs := S.Cs
  Ca := S.Ca
  hCs := S.hCs
  hCa := S.hCa
  hR := S.hR
  κ := paperKappa
  hκ := paperKappa_nonneg
  hN := S.hN
  hsum := hsum_paperKappa S.Cs S.Ca S.hCs S.hCa S.hLed

/-- **`MainFinalObligations3c` with `SAParts3P`** (no `hsum`, no `κ`). -/
structure MainFinalObligations3cP (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) where
  /-- The block data (`EnvPrefix`, at `f1Cell`). -/
  Dv : FinalBlockData3b hW hMR hFour
  /-- `hSA` in reduced form, at the paper's constants, without `hsum`. -/
  SA : SAParts3P hW hMR hFour (analyticInputs (Dv.PC.toPC hW hMR hFour) Dv.BA) Dv.Cmp
  /-- The middle part of `hothT` (`EnvPrefix`). *Open*. -/
  hmid : ∀ L, midOthers Dv.Cmp.toK2 Dv.MR L +
    max (∑ β, Dv.MR.toPrefix.KL β) (∑ β, Dv.MR.toPrefix.KR β) +
    (12 / 2 ^ 534 + Sarkozy.EnvPrefix.Uup SA.Cs SA.Ca SA.hCs SA.hCa + 11 / 10 ^ 70) ≤
      targetLedger.T
  /-- The class inputs (as in `MainFinalObligations3c`). -/
  Cls : ClassPartsE4 (Dv.toMF3 hB SA.toSAParts3 hmid).toK2.toK1.data
  /-- The inputs of `SF`, `fix`, `env` (as in `MainFinalObligations3c`). -/
  Sh : SharpParts2 (Dv.toMF3 hB SA.toSAParts3 hmid).toK2.toK1.toJoint

/-- The obligations of `main_target_f1_final3c`. -/
noncomputable def MainFinalObligations3cP.to3c {hB : Target.BMOR}
    (O : MainFinalObligations3cP hW hMR hFour hB) : MainFinalObligations3c hW hMR hFour hB where
  Dv := O.Dv
  SA := O.SA.toSAParts3
  hmid := O.hmid
  Cls := O.Cls
  Sh := O.Sh

/-- **`main_target_f1_final3c` without `hsum`, at the paper's constants** (`thm:main` at
`ε = 3/250000`), from `MainFinalObligations3cP`. -/
theorem main_target_f1_final3cP (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3cP hWeil hMovingRoot hFourCycle hBMOR) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_f1_final3c hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O.to3c

/-- **`TargetGoal.main_goal_f1` without `hsum`** (`s(N) ≤ C N^{0.99999}`), from
`MainFinalObligations3cP`. -/
theorem main_goal_f1P (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3cP hWeil hMovingRoot hFourCycle hBMOR) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  TargetGoal.main_goal_f1 hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O.to3c

end Sarkozy.HsumProof
