module

public import Sarkozy.EnvPrefix.Prices

@[expose] public section

/-!
# The combined main statement with the prefix parts of (CP6) and (CP8)(c) reduced

**`main_target_paper_final3b`**: `MainFinal3.main_target_paper_final3` with the obligations
`MainFinalObligations3b`, in which E2's `EnvelopePartsE2` (`Dv.Env`) is replaced by

* `Dv.MR`: the refinement on the middle blocks (as before);
* `hmid`: the middle part of `hothT` (`prop:record:matching`(ii)): the records not replaced at
  the middle blocks, plus `T_K = max(∑ KL, ∑ KR)`, plus the numbers `12/2^{534}` (square-clique
  atoms, C10), `Uup` (upper blocks: the band sum of `SA.hsum`, from `SA.hR` and `thm:bmor`) and
  `11/10⁷⁰` (tail), fit in `T`. It is stated after `SA`, whose per-record data it uses.

The square-clique and upper parts of `hothT` are proved (`hothT_of_mid`), and **`hCLpre` with its
datum `σ_pre` is gone** (`hCLpre_proved`, `σ_pre := σpreOf`). The structure takes `BMOR` as a
parameter: the types of `Cls` and `Sh` contain the constructed (CP6) data, whose `hothT` is proved
from `thm:bmor` (the upper band charges).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.EnvPrefix

open Sarkozy.MainFinal Sarkozy.MainFinal2 Sarkozy.MainFinal3
open Sarkozy.TargetLedger (targetLedger)
open Sarkozy.FirstStagePaper Sarkozy.GramBracketPaper Sarkozy.BlockSpecPaper
open Sarkozy.PaperNumbers (paperCell HistogramClaim)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-- **E2's `EnvelopePartsE2` from the middle part** (`hothT_of_mid`, `hCLpre_proved`). -/
noncomputable def envOf (hB : Target.BMOR) {A : PaperAnalyticInputs paperCell}
    (C : ComparisonParts3 hW hMR hFour A)
    (MR : MidRefinement (gramBracketTarget bOf hW (specF hW A) (hCF hW hMR hFour)
      (paperIn paperCell) (paperGi hW A)) C.toK2.toK1.CL (fun β => midAtom hW A β = true))
    (S : SAParts3 hW hMR hFour A C)
    (hmid : ∀ L, midOthers C.toK2 MR L + max (∑ β, MR.toPrefix.KL β) (∑ β, MR.toPrefix.KR β) +
      (12 / 2 ^ 534 + Uup S.Cs S.Ca S.hCs S.hCa + 11 / 10 ^ 70) ≤ targetLedger.T) :
    NumericalFields.EnvelopePartsE2 hW hMR hFour A C.toK2 where
  MR := MR
  hothT := hothT_of_mid hB C.toK2 C.cliquePrice_le MR S.Cs S.Ca S.hCs S.hCa S.hR hmid
  σpre := σpreOf C.toK2.toK1
  hCLpre := hCLpre_proved C.toK2.toK1

/-- **The block data with the prefix parts of (CP6), (CP8)(c) reduced.** 4 fields. -/
structure FinalBlockData3b (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    where
  /-- The per-prime cut certificates (C8, C9). -/
  PC : PrimeCertificates2
  /-- The block-level analytic inputs (B6). -/
  BA : BlockAnalytic
  /-- The (CP4) inputs (as in `MainFinal3`). -/
  Cmp : ComparisonParts3 hW hMR hFour (analyticInputs (PC.toPC hW hMR hFour) BA)
  /-- The prefix refinement on the middle blocks (`prop:record:matching`(i), `prop:signed-sides`;
  K2's `MR`). *Open*. -/
  MR : MidRefinement
    (gramBracketTarget bOf hW (specF hW (analyticInputs (PC.toPC hW hMR hFour) BA))
      (hCF hW hMR hFour) (paperIn paperCell)
      (paperGi hW (analyticInputs (PC.toPC hW hMR hFour) BA)))
    Cmp.toK2.toK1.CL (fun β => midAtom hW (analyticInputs (PC.toPC hW hMR hFour) BA) β = true)

/-- `MainFinal3`'s block data (E2's (CP6) inputs by `envOf`). -/
noncomputable def FinalBlockData3b.toMF3 (hB : Target.BMOR) (D : FinalBlockData3b hW hMR hFour)
    (S : SAParts3 hW hMR hFour (analyticInputs (D.PC.toPC hW hMR hFour) D.BA) D.Cmp)
    (hmid : ∀ L, midOthers D.Cmp.toK2 D.MR L +
      max (∑ β, D.MR.toPrefix.KL β) (∑ β, D.MR.toPrefix.KR β) +
      (12 / 2 ^ 534 + Uup S.Cs S.Ca S.hCs S.hCa + 11 / 10 ^ 70) ≤ targetLedger.T) :
    FinalBlockData3 hW hMR hFour where
  PC := D.PC
  BA := D.BA
  Cmp := D.Cmp
  Env := envOf hB D.Cmp D.MR S hmid

/-- **The combined obligations with the prefix parts of (CP6), (CP8)(c) reduced.** 6 fields:
`MainFinal3`'s five, with `Dv.Env` replaced by `Dv.MR` and the middle part `hmid`. -/
structure MainFinalObligations3b (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) where
  /-- The block data. -/
  Dv : FinalBlockData3b hW hMR hFour
  /-- The histogram certificate (`cert:record:middle-price`(b)). *Open* (N2, K2). -/
  hHist : HistogramClaim
  /-- `hSA` in reduced form (as in `MainFinal3`). -/
  SA : SAParts3 hW hMR hFour (analyticInputs (Dv.PC.toPC hW hMR hFour) Dv.BA) Dv.Cmp
  /-- **The middle part of `hothT`** (`prop:record:matching`(ii), "The matching exponent"): the
  records not replaced at the middle blocks, plus `T_K = max(∑ KL, ∑ KR)`, plus the clique bound
  `12/2^{534}`, the upper band sum `Uup` (of `SA.hsum`) and the tail bound `11/10⁷⁰`, are at most
  `T^{ledger}` at every scale. *Open* (a property of `CL` and `MR` at the middle blocks). -/
  hmid : ∀ L, midOthers Dv.Cmp.toK2 Dv.MR L +
    max (∑ β, Dv.MR.toPrefix.KL β) (∑ β, Dv.MR.toPrefix.KR β) +
    (12 / 2 ^ 534 + Uup SA.Cs SA.Ca SA.hCs SA.hCa + 11 / 10 ^ 70) ≤ targetLedger.T
  /-- The inputs of the joint bound (B10, B11, G1). -/
  Cls : ClassParts2 (Dv.toMF3 hB SA hmid).toK2.toK1.data
  /-- The inputs of `SF`, `fix`, `env` (B5, B9). -/
  Sh : SharpParts2U (Dv.toMF3 hB SA hmid).toK2.toK1.toJoint

/-- `MainFinal3`'s obligations. -/
noncomputable def MainFinalObligations3b.toMF3 {hB : Target.BMOR}
    (O : MainFinalObligations3b hW hMR hFour hB) : MainFinalObligations3 hW hMR hFour where
  Dv := O.Dv.toMF3 hB O.SA O.hmid
  hHist := O.hHist
  SA := O.SA
  Cls := O.Cls
  Sh := O.Sh

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵`, with the prefix parts of (CP6) and
(CP8)(c) reduced** (`thm:main` at `ε = a_T/71`; `MainFinal3.main_target_paper_final3` through
`MainFinalObligations3b.toMF3`). Hypotheses: H1 `Weil`, H2 `BMOR`, H5
`MovingRoot`, `thm:dl:K` `FourCycle`, H2″ `ThetaSmallRR`, and `O : MainFinalObligations3b`.
H4 `TwoVariable` was removed on 9 November 2026 as unused. -/
theorem main_target_paper_final3b (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3b hWeil hMovingRoot hFourCycle hBMOR) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_final3 hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O.toMF3

end Sarkozy.EnvPrefix
