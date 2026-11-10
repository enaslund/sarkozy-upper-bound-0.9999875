module

public import Sarkozy.MainFinal3.Comparison

@[expose] public section

/-!
# The combined main statement, third round

`thm:main` at `ε = a_T/71`, i.e. `s(N) ≤ C N^{1 − a_T/71}`, joint form (`cor:joint-closing`,
`eq:final-joint-closing`), on the paper's construction in the ALLp configuration.

**`main_target_paper_final3`** concludes `Target.SarkozyBound TargetLedger.targetSaving` from H1
`Weil`, H2
`BMOR`, H5 `MovingRoot`, `thm:dl:K` `FourCycle`, H2″ `ThetaSmallRR` and one
structure `MainFinalObligations3`, through K2's `main_target_paper_final2`
(`MainFinalObligations3.toK2`). Closed beyond K2:

* C10: the square-clique deletions `Dv.Cmp.clique` (`CliqueDeletion.cliqueK1`, proved with no
  hypothesis) and the clique bound `SA.H`, `SA.hq` (`H = 12/2^{534}`, proved);
* E1: the signed estimates of every middle block, K2's field 11 `MiddleEstimates`
  (`SignedEstimates.paperMiddleEstimates`, proved from H1 with `η_p = 10/p`, `e_p = e₀(p)`);
  the data `η`, `e` and their four side conditions go with it;
* E2 (`Sarkozy/NumericalFields/`): the band charges `SA.hUS`, `SA.hUA` (from `thm:bmor` at
  `𝒰 = bandBound a_T`, with the data `US`, `UA`), the signs `SA.hK` (from the new side condition
  `κ ≥ 0`), and the (CP6) gates `Env.hK`, `Env.hTK` (with the data `TK`, `Tpre`), by
  `T_K = max(∑ KL, ∑ KR)`, `T_pre = T − T_K − 11/10⁷⁰` (`EnvelopePartsE2`, `SAPartsE3`).

This statement combines the three independent reductions of K2's obligations: E1's
`Sarkozy.SignedEstimates.main_target_paper_final3` (field 11 only) and E2's
`Sarkozy.NumericalFields.main_target_paper_final_E3` (fields 35–37, 39, 40 only) are special
cases; each piece is mapped to K2's structure (`toK2`, E2's `toParts2`, `toE2`).

K2's F1 variant `main_target_f1_final2` keeps (CP4) in B1's raw form (`Dv.CL`), so neither field
occurs in it; it is unchanged.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MainFinal3

open Sarkozy.MainFinal Sarkozy.MainFinal2
open Sarkozy.PaperNumbers (paperCell HistogramClaim)

/-- **The block data, third round**: K2's `FinalBlockData2` with the (CP4) inputs of
`ComparisonParts3` (no square-clique field, no middle-block estimates). 4 fields. -/
structure FinalBlockData3 (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    where
  /-- The per-prime cut certificates (C8, C9). -/
  PC : PrimeCertificates2
  /-- The block-level analytic inputs (B6). -/
  BA : BlockAnalytic
  /-- The (CP4) inputs (B8, T2; the square-clique atoms proved by C10, the middle estimates by
  E1). -/
  Cmp : ComparisonParts3 hW hMR hFour (analyticInputs (PC.toPC hW hMR hFour) BA)
  /-- The (CP6), (CP8)(c) inputs (B3, K1, K2), without the gates `hK`, `hTK` (E2's
  `EnvelopePartsE2`). -/
  Env : NumericalFields.EnvelopePartsE2 hW hMR hFour (analyticInputs (PC.toPC hW hMR hFour) BA)
    Cmp.toK2

/-- K2's `FinalBlockData2`. -/
noncomputable def FinalBlockData3.toK2 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} (D : FinalBlockData3 hW hMR hFour) :
    FinalBlockData2 hW hMR hFour where
  PC := D.PC
  BA := D.BA
  Cmp := D.Cmp.toK2
  Env := D.Env.toParts2

structure MainFinalObligations3 (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) where
  /-- The block data. -/
  Dv : FinalBlockData3 hW hMR hFour
  /-- The histogram certificate (`cert:record:middle-price`(b)). *Open*: an unproved claim about
  prime sums (N2, K2). -/
  hHist : HistogramClaim
  /-- `hSA` in reduced form: the clique bound and the band charges entered, the signs proved. -/
  SA : SAParts3 hW hMR hFour (analyticInputs (Dv.PC.toPC hW hMR hFour) Dv.BA) Dv.Cmp
  /-- The inputs of the joint bound (B10, B11, G1). -/
  Cls : ClassParts2 Dv.toK2.toK1.data
  /-- The inputs of `SF`, `fix`, `env` (B5, B9). -/
  Sh : SharpParts2U Dv.toK2.toK1.toJoint

/-- **K2's obligations from the third-round obligations.** -/
noncomputable def MainFinalObligations3.toK2 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} (hB : Target.BMOR) (O : MainFinalObligations3 hW hMR hFour) :
    MainFinalObligations2 hW hMR hFour where
  Dv := O.Dv.toK2
  hHist := O.hHist
  SA := O.SA.toK2 hB
  Cls := O.Cls
  Sh := O.Sh

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵`, third round** (`thm:main` at
`ε = 3/250000`, via `thm:comparison` with `cor:joint-closing`, `eq:final-joint-closing` and
`thm:density:induction` at `a_T`; `def:construction`(b) in the ALLp configuration).

Hypotheses: H1 `Weil`, H2 `BMOR`, H5 `MovingRoot` and
`thm:dl:K` `FourCycle` (tail input), H2″ `ThetaSmallRR`, and `O : MainFinalObligations3`.
`AhlgrenOno` (H3) is not used; H4 `TwoVariable` was removed on 9 November 2026 as unused. -/
theorem main_target_paper_final3 (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3 hWeil hMovingRoot hFourCycle) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_final2 hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR
    (O.toK2 hBMOR)

end Sarkozy.MainFinal3
