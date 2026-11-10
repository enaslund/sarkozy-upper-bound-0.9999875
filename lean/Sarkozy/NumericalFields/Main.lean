module

public import Sarkozy.NumericalFields.Reduced
public import Sarkozy.MainFinal2.Main

@[expose] public section

/-!
# The main statement without K2's fields 36, 37, 39, 40 (E2)

**`main_target_paper_final_E2`** is K2's `MainFinal2.main_target_paper_final2`
(`thm:main` at `ε = a_T/71`, i.e. `s(N) ≤ C N^{1 − a_T/71}`) with `MainFinalObligations2`
replaced by `MainFinalObligationsE2`, in which
* the signs `SA.hK` of the price coefficients `K_d(i)` (K2's field 37,
  `lem:middle-comparison-prices`) are **proved** (`midK_signs`), from the side condition
  `SA.hκ` (the constants `κ` of `eq:signed-constants` are nonnegative);
* the gates `Env.hK : ∑ KL ≤ T_K, ∑ KR ≤ T_K` and `Env.hTK : T_K + T_pre + 11/10⁷⁰ ≤ T` (K2's
  fields 39, 40) are **removed**, with the data `T_K`, `T_pre`, by the paper's definitions of
  `T_K` and `T` (`EnvelopePartsE2`, an equivalent form of `EnvelopeParts2`);
* the two band-charge fields `SA.hUS`, `SA.hUA` (K2's fields 35, 36) are one field `SA.hU`: they
  are the same prime-sum statement for two data, and `min(US, UA)` serves both prices
  (`SAPartsE2.ofParts2`). The prime sums themselves (`def:record:upper-bands`) stay open.

`MainFinalObligationsE2.toMF2` maps to K2's obligations; `MainFinalObligationsE2.ofMF2` maps back
(given `hκ`), so nothing is lost.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.NumericalFields

open Sarkozy.MainFinal Sarkozy.MainFinal2
open Sarkozy.PaperNumbers (paperCell HistogramClaim)

/-- **The block data with the (CP6) gates removed** (K2's `FinalBlockData2` with `Env` in the
form `EnvelopePartsE2`). 4 fields. -/
structure FinalBlockDataE2 (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    where
  /-- The per-prime cut certificates (C8). -/
  PC : PrimeCertificates2
  /-- The block-level analytic inputs (B6). -/
  BA : BlockAnalytic
  /-- The (CP4) inputs (B8, T2). -/
  Cmp : ComparisonParts2 hW hMR hFour (analyticInputs (PC.toPC hW hMR hFour) BA)
  /-- The (CP6), (CP8)(c) inputs without the gates `hK`, `hTK`. -/
  Env : EnvelopePartsE2 hW hMR hFour (analyticInputs (PC.toPC hW hMR hFour) BA) Cmp

/-- K2's `FinalBlockData2`. -/
noncomputable def FinalBlockDataE2.toMF2 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} (D : FinalBlockDataE2 hW hMR hFour) :
    FinalBlockData2 hW hMR hFour where
  PC := D.PC
  BA := D.BA
  Cmp := D.Cmp
  Env := D.Env.toParts2

/-- **The combined obligations of the main statement without K2's fields 36, 37, 39, 40.** 5 fields,
as `MainFinalObligations2`: `Dv` (with `Env : EnvelopePartsE2`), `hHist`, `SA : SAPartsE2`,
`Cls`, `Sh`. -/
structure MainFinalObligationsE2 (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) where
  /-- The block data. -/
  Dv : FinalBlockDataE2 hW hMR hFour
  /-- **The histogram certificate** (`cert:record:middle-price`(b)). *Open*; as in
  `MainFinalObligations2.hHist`. -/
  hHist : HistogramClaim
  /-- `hSA` in reduced form, without the signs. -/
  SA : SAPartsE2 hW hMR hFour (analyticInputs (Dv.PC.toPC hW hMR hFour) Dv.BA) Dv.Cmp
  /-- The inputs of the joint bound (B10). -/
  Cls : ClassParts2 Dv.toMF2.toK1.data
  /-- The inputs of `SF`, `fix`, `env` (B5, B9). -/
  Sh : SharpParts2U Dv.toMF2.toK1.toJoint

/-- **K2's obligations** from the reduced ones. -/
noncomputable def MainFinalObligationsE2.toMF2 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} (O : MainFinalObligationsE2 hW hMR hFour) :
    MainFinalObligations2 hW hMR hFour where
  Dv := O.Dv.toMF2
  hHist := O.hHist
  SA := O.SA.toParts2
  Cls := O.Cls
  Sh := O.Sh

/-- **Nothing is lost**: K2's obligations with nonnegative constants `κ` give the reduced ones
(same `PC`, `BA`, `Cmp`, refinement `MR`, `hHist`, `SA` data). The class and sharp inputs are
carried over because `toParts2 ∘ ofParts2` returns K2's `Env` up to the data `T_K`, `T_pre`, which
the class and sharp inputs do not see: K1's `EnvelopeParts.ofOthers` uses them only in the proof
of `hrepl`, a `Prop`. -/
noncomputable def MainFinalObligationsE2.ofMF2 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} (O : MainFinalObligations2 hW hMR hFour)
    (hκ : ∀ i, KappaNonneg (O.SA.κ i)) : MainFinalObligationsE2 hW hMR hFour where
  Dv := ⟨O.Dv.PC, O.Dv.BA, O.Dv.Cmp, EnvelopePartsE2.ofParts2 O.Dv.Env⟩
  hHist := O.hHist
  SA := SAPartsE2.ofParts2 O.SA hκ
  Cls := O.Cls
  Sh := O.Sh

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵`, without K2's fields 36, 37, 39, 40**
(`thm:main` at `ε = a_T/71`; K2's `main_target_paper_final2` through
`MainFinalObligationsE2.toMF2`). Hypotheses: H1 `Weil`, H2 `BMOR`, H5
`MovingRoot`, `thm:dl:K` `FourCycle`, H2″ `ThetaSmallRR`, and `O : MainFinalObligationsE2`.
H4 `TwoVariable` was removed on 9 November 2026 as unused. -/
theorem main_target_paper_final_E2 (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligationsE2 hWeil hMovingRoot hFourCycle) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_final2 hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O.toMF2

end Sarkozy.NumericalFields
