module

public import Sarkozy.MainFinal2.Obligations
public import Sarkozy.AnalyticCells.Main

@[expose] public section

/-!
# The combined main statement, second round (K2)

`thm:main` at `ε = a_T/71`, i.e. `s(N) ≤ C N^{1 − a_T/71}`, joint form (`cor:joint-closing`,
`eq:final-joint-closing`), on the paper's construction in the ALLp configuration.

**`main_target_paper_final2`** concludes `Target.SarkozyBound TargetLedger.targetSaving` from H1
`Weil`, H2
`BMOR`, H5 `MovingRoot`, `thm:dl:K` `FourCycle`, H2″ `ThetaSmallRR` and one
structure `MainFinalObligations2`, through K1's `main_target_paper_final` (`toK1`). Beyond K1:

* N2: the 66 charge bounds from **`HistogramClaim`** alone (`numericalCertificates_of_hist`; the
  cells above `X_Ch` proved, `cellClaimN2`);
* C8: `h10`, `h21`, `h20` from `MidInputs`, `L20Inputs`;
* B8: `ReplacementData` constructed on every middle block from the signed estimates; the norm
  sizes from the twelve norm bounds;
* T2: the tail atoms from the repairs at the paper's caps; `tail_S`, `tail_A`, `St`, `At`, the
  cap ledger proved;
* K1's `SAExplicit_full` and `ofOthers` plugged in;
* B10: `CI.robust`, `MA.upper` proved, `CE.energy` from the steps;
* B9: `fixC`, `envC` in mean-bound form, the bracket of `lem:bracket-energy` removed.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MainFinal2

open Sarkozy.MainFinal
open Sarkozy.TargetLedger (targetDecay)
open Sarkozy.PaperNumbers (paperCell HistogramClaim)

/-- **N1's 66 charge bounds from the histogram certificate alone** (N2's
`pieceBound_le_charge_N2`: below `X_Ch` the recorded histogram, above it the proved cell bounds
`cellClaimN2`; `cert:record:middle-price`(b),(c), `lem:record:repricing`). -/
theorem numericalCertificates_of_hist (hH : HistogramClaim) : NumericalCertificates where
  h₂ i := (AnalyticCells.pieceBound_le_charge_N2 hH i).1
  h₃ i := (AnalyticCells.pieceBound_le_charge_N2 hH i).2

structure MainFinalObligations2 (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) where
  /-- The block data. -/
  Dv : FinalBlockData2 hW hMR hFour
  /-- **The histogram certificate** (`cert:record:middle-price`(b)): the sieve's per-bucket sums
  of `w_d(b_𝔅)` over the greedy blocks of the 35 parts are at most the recorded numbers. *Open*:
  an unproved claim about prime sums (the C++ sieve has not been re-run or checked in Lean). -/
  hHist : HistogramClaim
  /-- `hSA` in reduced form. -/
  SA : SAParts hW hMR hFour (analyticInputs (Dv.PC.toPC hW hMR hFour) Dv.BA) Dv.Cmp
  /-- The inputs of the joint bound (B10). -/
  Cls : ClassParts2 Dv.toK1.data
  /-- The inputs of `SF`, `fix`, `env` (B5, B9). -/
  Sh : SharpParts2U Dv.toK1.toJoint

/-- **K1's obligations from the second-round obligations.** -/
noncomputable def MainFinalObligations2.toK1 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} (hBMOR : Target.BMOR) (O : MainFinalObligations2 hW hMR hFour) :
    MainFinalObligations hW hMR hFour where
  Dv := O.Dv.toK1
  NC := numericalCertificates_of_hist O.hHist
  hSA := O.SA.toSAExplicit hBMOR (numericalCertificates_of_hist O.hHist)
  Cls := O.Cls.toB10.toClassParts
  Sh := O.Sh.toK1

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵`, second round** (`thm:main` at
`ε = 3/250000`, via `thm:comparison` with `cor:joint-closing`, `eq:final-joint-closing` and
`thm:density:induction` at `a_T`; `def:construction`(b) in the ALLp configuration).

Hypotheses: H1 `Weil`, H2 `BMOR` (block and cell charges), H5 `MovingRoot` and
`thm:dl:K` `FourCycle` (tail input), H2″
`ThetaSmallRR` (`cert:index-moment`), and `O : MainFinalObligations2`. `AhlgrenOno` (H3) is not
used; H4 `TwoVariable` was removed on 9 November 2026 as unused. -/
theorem main_target_paper_final2 (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations2 hWeil hMovingRoot hFourCycle) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_final hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR
    (O.toK1 hBMOR)

end Sarkozy.MainFinal2
