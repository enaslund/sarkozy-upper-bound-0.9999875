module

public import Sarkozy.MainFinal.Main
public import Sarkozy.ClassInputsPaper.Energy

@[expose] public section

/-!
# The class inputs of the combined main statement, with the evaluated class bounds proved

K1's `MainFinal.main_target_paper_final` takes B4's five inputs of `JB` as
`Cls : ClassParts Dv.data`: `CI` (24 sub-fields; analytic `robust`), `PD`, `CE` (8 sub-fields),
`E1`, `MA` (6 sub-fields; analytic `mean`, `upper`).

`ClassPartsB10 D` replaces them by:
* `cd : ClassData D.CL` — the 23 data fields of `CI`, without `robust`;
* `ED : ClassEnergyData D cd` — B4's `CE` fields, with nonnegative weights, and the upper prices
  of the diagonals `upper` (`lem:bracket-energy`), with error weights dominated by the class prices
  (`errw`); `ClassEnergyData.ofSteps` builds it from the steps of `thm:envelopes`(i) and
  `prop:background-variance`(a) (`StepsFamily`);
* `PD : PolynomialData ED.toCI` — unchanged;
* `E1 : D.EnvelopeBoundNonneg` — unchanged (G1's `envelopeBoundNonneg_of_coupledPieces_uniform`
  reduces it to per-term inputs);
* `MD : MeanData ED` — `MA` without `upper`, with `b ≥ 0` and the error-weight gate `V`.

**`ClassPartsB10.toClassParts`**: K1's `ClassParts`, with `CI.robust` **proved**
(`ClassEnergyData.robust`) and `MA.upper` **proved** from `ED.upper` (`MeanData.upper`).

**`main_target_paper_final_B10`**: K1's main statement with `Cls` replaced by `ClassPartsB10`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.ClassInputsPaper

open Sarkozy.MainFinal
open Sarkozy.TheoremC Sarkozy.RecordExpansion
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (paperAtomMap)
open Sarkozy.ComparisonLawPaper (SAExplicit)
open Sarkozy.ClassBoundsPaper (PolynomialData)

/-- **The inputs of the joint bound `JB`, with the evaluated class bounds derived**
(`def:cp5`, `def:robust`, `thm:envelopes`(i), `cor:envelope-costs`, `cor:var-classes`,
`lem:var-gain`, `lem:bracket-energy`, `prop:record:mean-credit`, `cert:four-routes-closing`,
`prop:joint-middle-mean`, `prop:joint-upper-mean`). 5 fields. -/
structure ClassPartsB10 (D : TheoremCBlock.ComparisonData targetDecay paperM0 (paperAtomMap bOf)
    paperTail paperPr paperH Chamber) where
  /-- The data of the classes (`def:cp5`, `prop:closing-data`(d), `lem:middle-comparison-prices`,
  `cor:variance:final`(i), (iii)). *Open* (data). -/
  cd : ClassData D.CL
  /-- The class bounds at energy level and the upper prices of their diagonals
  (`thm:envelopes`(i), `cor:envelope-costs`, `cor:var-classes`; `lem:bracket-energy`). *Open*
  (analytic: `energy`, `upper`; evaluations: `consistent`, `errw`). -/
  ED : ClassEnergyData D cd
  /-- The upper data of the class polynomial (B4's `PolynomialData`). *Open* (data with
  numerical gates). -/
  PD : PolynomialData ED.toCI
  /-- (E1) for the selections in no class (`def:robust`). *Open* (analytic). -/
  E1 : D.EnvelopeBoundNonneg
  /-- The joint mean allocation without its upper prices. *Open* (analytic: `mean`; numerical:
  `resid`, `alloc`, `hV`). -/
  MD : MeanData ED

/-- **K1's `ClassParts` from `ClassPartsB10`**: `CI := ED.toCI` (with `robust` proved),
`CE := ED.toCE`, `MA := MD.toMA` (with `upper` proved). -/
noncomputable def ClassPartsB10.toClassParts {D : TheoremCBlock.ComparisonData targetDecay paperM0
    (paperAtomMap bOf) paperTail paperPr paperH Chamber} (C : ClassPartsB10 D) : ClassParts D where
  CI := C.ED.toCI
  PD := C.PD
  CE := C.ED.toCE
  E1 := C.E1
  MA := C.MD.toMA

/-- **The combined obligations with B10's class inputs**: K1's `MainFinalObligations` with
`Cls : ClassParts` replaced by `ClassPartsB10`. 5 fields. -/
structure MainFinalObligationsB10 (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) where
  /-- The block data. -/
  Dv : FinalBlockData hW hMR hFour
  /-- The 66 per-piece charge bounds (N1). *Open* (numerical). -/
  NC : NumericalCertificates
  /-- `S + A ≤ S^{ledger} + A^{ledger}` in explicit per-atom form. *Open*. -/
  hSA : SAExplicit Dv.Cmp.Ci
  /-- The inputs of the joint bound (B10). -/
  Cls : ClassPartsB10 Dv.data
  /-- The inputs of `SF`, `fix`, `env` (B5). -/
  Sh : SharpParts Dv.toJoint

/-- K1's obligations from B10's. -/
noncomputable def MainFinalObligationsB10.toMainFinal {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} (O : MainFinalObligationsB10 hW hMR hFour) :
    MainFinalObligations hW hMR hFour where
  Dv := O.Dv
  NC := O.NC
  hSA := O.hSA
  Cls := O.Cls.toClassParts
  Sh := O.Sh

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵` with B10's class inputs** (`thm:main` at
`ε = 3/250000`; K1's `main_target_paper_final`). The robust evaluated class bounds of (CP5)
(`def:cp5`, `def:robust`) and the upper prices (J3) of the mean allocation are no longer inputs:
both come from the class bounds at energy level and the upper prices of their diagonals
(`ClassEnergyData`). -/
theorem main_target_paper_final_B10 (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligationsB10 hWeil hMovingRoot hFourCycle) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_final hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR
    O.toMainFinal

end Sarkozy.ClassInputsPaper
