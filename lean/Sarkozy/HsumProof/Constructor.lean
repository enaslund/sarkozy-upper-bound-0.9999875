module

public import Sarkozy.HsumProof.Upper
public import Sarkozy.MainFinalF1.Main

@[expose] public section

/-!
# `SA.hsum` replaced by the paper's ledgers and the middle bound (HS)

`MainFinalF1.SAParts3.hsum` (the final inequality of `hSA`, `cor:joint-closing`) is replaced by two
fields:

* `hLed : PaperLedgers Cs Ca` — the per-record data `Cs`, `Ca` have the paper's state ledgers
  `Λ^s_k(𝔱)`, `Λ^a_k(𝔱)` (`def:upper-comparison`; `upper_dense_refined.json`) as state sums. This is
  a statement about the data (the paper *defines* the ledgers as these sums); with it the upper
  part of `hsum` is proved (`upperPart_le`, kernel-checked);
* `hM : middlePart κ ≤ 0.962` — the middle part at the F1 numbers. *Open* (numerical; `κ` is
  the paper's `eq:signed-constants` and `lem:record:exact-marginal-e`(ii), not exported).

`SAParts3H.toSAParts3` rebuilds `SAParts3` (`hsum_of_ledgers`), and
`MainFinalObligations3cH` is `MainFinalObligations3c` with `SAParts3H` in place of `SAParts3`;
`main_target_f1_final3cH` is `main_target_f1_final3c` through it. `Uup_le` gives the same bound for
the upper term of the field `hmid` (`EnvPrefix.Uup` is the same sum).
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

/-- **`SAParts3` with `hsum` replaced** by the paper's ledgers `hLed` and the middle bound `hM`.
8 fields besides the data. -/
structure SAParts3H (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs f1Cell) (C : ComparisonParts3 hW hMR hFour A) where
  /-- The per-band record coefficients. Data. -/
  Cs : Fin 310 → UpIdx → ℝ
  Ca : Fin 310 → UpIdx → ℝ
  hCs : ∀ k i, 0 ≤ Cs k i
  hCa : ∀ k i, 0 ≤ Ca k i
  /-- **The data have the paper's state ledgers** (`def:upper-comparison`,
  `upper_dense_refined.json`). Side condition on the data. -/
  hLed : PaperLedgers Cs Ca
  /-- The upper per-record bounds (`prop:record:upper`(ii), W8's ledger). *Open* (analytic). -/
  hR : C.toK2.toK1.UpperRecs hW A Cs Ca hCs hCa
  /-- The per-piece constants `(s_F, a_F, ℓ_t, s_E, a_E)`. Data. -/
  κ : Fin 33 → MiddleConsts
  /-- The constants are nonnegative (E2). Side condition on the data `κ`. -/
  hκ : ∀ i, KappaNonneg (κ i)
  /-- The twelve norm bounds of every middle block (as in `SAParts3`). *Open* (analytic). -/
  hN : ∀ b i, blockSite b = .inl i →
    SpecNormBounds hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (C.toK2.blk b)
  /-- **The middle part of `hsum`** at the F1 numbers, with HS's budget `0.962`. *Open*
  (numerical). -/
  hM : middlePart κ ≤ middleBudgetHS

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-- **`SAParts3` from `SAParts3H`**: `hsum` is `hsum_of_ledgers`. -/
noncomputable def SAParts3H.toSAParts3 {A : PaperAnalyticInputs f1Cell}
    {C : ComparisonParts3 hW hMR hFour A} (S : SAParts3H hW hMR hFour A C) :
    SAParts3 hW hMR hFour A C where
  Cs := S.Cs
  Ca := S.Ca
  hCs := S.hCs
  hCa := S.hCa
  hR := S.hR
  κ := S.κ
  hκ := S.hκ
  hN := S.hN
  hsum := hsum_of_ledgers S.Cs S.Ca S.hCs S.hCa S.hLed S.κ S.hM

/-- **The upper term of `hmid`**: `Uup Cs Ca ≤ 21/1000` for data with the paper's ledgers. -/
theorem Uup_le (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i)
    (hCa : ∀ k i, 0 ≤ Ca k i) (hL : PaperLedgers Cs Ca) :
    Sarkozy.EnvPrefix.Uup Cs Ca hCs hCa ≤ 21 / 1000 :=
  upperPart_le Cs Ca hCs hCa hL

/-- **`MainFinalObligations3c` with `SAParts3H`** (no `hsum`; `hLed`, `hM` instead). -/
structure MainFinalObligations3cH (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) where
  /-- The block data (`EnvPrefix`, at `f1Cell`). -/
  Dv : FinalBlockData3b hW hMR hFour
  /-- `hSA` in reduced form, with `hsum` replaced. -/
  SA : SAParts3H hW hMR hFour (analyticInputs (Dv.PC.toPC hW hMR hFour) Dv.BA) Dv.Cmp
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
noncomputable def MainFinalObligations3cH.to3c {hB : Target.BMOR}
    (O : MainFinalObligations3cH hW hMR hFour hB) : MainFinalObligations3c hW hMR hFour hB where
  Dv := O.Dv
  SA := O.SA.toSAParts3
  hmid := O.hmid
  Cls := O.Cls
  Sh := O.Sh

/-- **`main_target_f1_final3c` without `hsum`** (`thm:main` at `ε = a_T/71`, as there), from
`MainFinalObligations3cH`. -/
theorem main_target_f1_final3cH (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3cH hWeil hMovingRoot hFourCycle hBMOR) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_f1_final3c hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O.to3c

end Sarkozy.HsumProof
