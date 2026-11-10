module

public import Sarkozy.HsumProof.Constructor
public import Sarkozy.HsumProof.Middle

@[expose] public section

/-!
# `SA.hsum` replaced by two conditions on the data (HS)

`SAParts3K` is `MainFinalF1.SAParts3` with the field `hsum` replaced by two side conditions on the
data, both statements about the paper's constants, not inequalities to be proved:

* `hLed : PaperLedgers Cs Ca` — the state sums of the per-record coefficients are at most the
  paper's state ledgers (`def:upper-comparison`, `upper_dense_refined.json`);
* `hκB` — on every middle piece `i`, `s_E + a_E + ℓ_t ≤ 23/10` and `s_F + a_F ≤ 3700` (RG;
  `1000` at `a_T`) for the constants `κ` (`eq:signed-constants`, `lem:record:exact-marginal-e`(ii);
  `lem:middle-comparison-prices`). RB's loosened table satisfies it (`paperKappa_bounds`).

`SAParts3K.toH` gives HS's `SAParts3H` (`middlePart_le_of_kappa`), hence `SAParts3`
(`hsum_of_ledgers`); `main_target_f1_final3cK` is `main_target_f1_final3c` from
`MainFinalObligations3cK`.
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

/-- **`SAParts3` without `hsum`**: the paper's ledgers `hLed` and the per-piece bounds `hκB` on
the paper's constants instead. -/
structure SAParts3K (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
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
  /-- The per-piece constants `(s_F, a_F, ℓ_t, s_E, a_E)`. Data. -/
  κ : Fin 33 → MiddleConsts
  /-- The constants are nonnegative (E2). Side condition on the data `κ`. -/
  hκ : ∀ i, KappaNonneg (κ i)
  /-- **Per-piece bounds on the paper's constants.** Side condition on the data `κ`. -/
  hκB : ∀ i, (κ i).sE + (κ i).aE + (κ i).ℓ ≤ 23 / 10 ∧ (κ i).sF + (κ i).aF ≤ 3700
  /-- The twelve norm bounds of every middle block (as in `SAParts3`). *Open* (analytic). -/
  hN : ∀ b i, blockSite b = .inl i →
    SpecNormBounds hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (C.toK2.blk b)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-- `SAParts3H` from `SAParts3K` (`middlePart_le_of_kappa`). -/
noncomputable def SAParts3K.toH {A : PaperAnalyticInputs f1Cell}
    {C : ComparisonParts3 hW hMR hFour A} (S : SAParts3K hW hMR hFour A C) :
    SAParts3H hW hMR hFour A C where
  Cs := S.Cs
  Ca := S.Ca
  hCs := S.hCs
  hCa := S.hCa
  hLed := S.hLed
  hR := S.hR
  κ := S.κ
  hκ := S.hκ
  hN := S.hN
  hM := middlePart_le_of_kappa S.κ S.hκB

/-- **`MainFinalObligations3c` with `SAParts3K`** (no `hsum`). -/
structure MainFinalObligations3cK (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) where
  /-- The block data (`EnvPrefix`, at `f1Cell`). -/
  Dv : FinalBlockData3b hW hMR hFour
  /-- `hSA` in reduced form, without `hsum`. -/
  SA : SAParts3K hW hMR hFour (analyticInputs (Dv.PC.toPC hW hMR hFour) Dv.BA) Dv.Cmp
  /-- The middle part of `hothT` (`EnvPrefix`). *Open*. -/
  hmid : ∀ L, midOthers Dv.Cmp.toK2 Dv.MR L +
    max (∑ β, Dv.MR.toPrefix.KL β) (∑ β, Dv.MR.toPrefix.KR β) +
    (12 / 2 ^ 534 + Sarkozy.EnvPrefix.Uup SA.Cs SA.Ca SA.hCs SA.hCa + 11 / 10 ^ 70) ≤
      targetLedger.T
  /-- The class inputs (as in `MainFinalObligations3c`). -/
  Cls : ClassPartsE4 (Dv.toMF3 hB SA.toH.toSAParts3 hmid).toK2.toK1.data
  /-- The inputs of `SF`, `fix`, `env` (as in `MainFinalObligations3c`). -/
  Sh : SharpParts2 (Dv.toMF3 hB SA.toH.toSAParts3 hmid).toK2.toK1.toJoint

/-- The obligations of `main_target_f1_final3c`. -/
noncomputable def MainFinalObligations3cK.to3c {hB : Target.BMOR}
    (O : MainFinalObligations3cK hW hMR hFour hB) : MainFinalObligations3c hW hMR hFour hB where
  Dv := O.Dv
  SA := O.SA.toH.toSAParts3
  hmid := O.hmid
  Cls := O.Cls
  Sh := O.Sh

/-- **`main_target_f1_final3c` without `hsum`** (`thm:main` at `ε = a_T/71`), from
`MainFinalObligations3cK`: `hsum` is proved from `hLed` and `hκB`. -/
theorem main_target_f1_final3cK (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3cK hWeil hMovingRoot hFourCycle hBMOR) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_f1_final3c hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O.to3c

end Sarkozy.HsumProof
