module

public import Sarkozy.GramBracketPaper.Main
public import Sarkozy.ClassBoundsPaper.Polynomial

@[expose] public section

/-!
# The A2 form of the main statement with the class bounds constructed (`CB`, `hΨ`, `hCB`)

A2's `GramBracketPaper.main_target_paper_block_A2` with the three (CP5) obligations replaced:

* **`CB`** (`def:cp5`) is `ClassInputs.toClassBounds CI`: the paper's degree classes
  (`cor:envelope-costs`) and variance classes (`cor:variance:final`), the auxiliary prices
  (`lem:middle-comparison-prices`) and the class bounds of `thm:envelopes`(i) and `cor:var-classes`
  as polynomials in them, for any comparison law `CL` (in particular B2's);
* **`hCB`** (`def:robust`) is `ClassInputs.robustNonneg CI`, proved;
* **`hΨ`** (`prop:closing-data`(d), certificate family F15) is `PolynomialData.hΨ PD hB`, proved
  from the upper data `PD` and the obligation `hB`, with the sixteen class savings kernel-checked
  (`paperSavings_ge`).

`B4FinalObligationsTarget` has the fields of A2's `A2FinalObligationsTarget` with `CB`, `hΨ`, `hCB`
replaced by `CI : ClassInputs CL` and `PD : PolynomialData CI`. Of A2's 13 fields (the data `Dv`
and 12 obligations), the three class-bound obligations become two input structures; their open
content is now the named hypotheses `ClassInputs.robust` (the robust class bounds of
`cor:envelope-costs` and `cor:var-classes` for `CL`, the analytic content) and the upper data of
`PolynomialData` (upper prices with the closing's totals, `prop:closing-data`(b); the variance
credit `D_var`, `cor:variance:final`(iv)), plus the data fields of `ClassInputs`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.ClassBoundsPaper

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper
open Sarkozy.PartVLaws (PaperBlockSpec v2Reference TailInputsCorr paperAtomMap)

variable {B : Type} [Fintype B] [DecidableEq B] (blockOf : PaperJ0 → B)

/-- **A2's final obligations with the class bounds constructed.** 12 fields: the data `Dv`, the
class inputs `CI` and upper data `PD` (replacing `CB`, `hΨ`, `hCB`), and A2's nine other
obligations, verbatim. -/
structure B4FinalObligationsTarget (hW : Target.Weil) where
  /-- The data, with the first stage and the Gram bracket constructed. -/
  Dv : A2BlockDataTarget blockOf hW
  /-- The inputs of the class bounds (`def:cp5`; `cor:envelope-costs`, `cor:var-classes`).
  *Open*: `ClassInputs.robust` and the data fields. -/
  CI : ClassInputs Dv.toA1.toV2.toCertData.toData.CL
  /-- The upper data of the class polynomial (`prop:closing-data`(b), (d);
  `cor:variance:final`(iv)). *Open*. -/
  PD : PolynomialData CI
  /-- `B ≤` the ledger's `B`, for the constructed bracket (`hB_of_prices`). *Open*. -/
  hB : Dv.toA1.toV2.toCertData.toData.B ≤ targetLedger.B
  /-- `L₀ ≤` the ledger's `L₀`. *Open*. -/
  hL₀ : Dv.toA1.toV2.toCertData.toData.L₀ ≤ targetLedger.L₀
  /-- `T ≤` the ledger's `T`. *Open*. -/
  hT : Dv.toA1.toV2.toCertData.toData.ME.T ≤ targetLedger.T
  /-- `S + A ≤` the ledger's `S + A`. *Open*. -/
  hSA : Dv.toA1.toV2.toCertData.toData.CL.S + Dv.toA1.toV2.toCertData.toData.CL.A ≤
    targetLedger.S + targetLedger.A
  /-- The mean credit pays the joint-closing allocations. *Open*. -/
  hm : targetLedger.m₁ + 64 * ((targetLedger.deltaAlpha + targetLedger.deltaMatching +
    targetLedger.deltaOdd + targetLedger.deltaEven) + targetLedger.deltaUpper -
    targetLedger.upperError) ≤ Dv.toA1.toV2.toCertData.toData.MC.m
  /-- (E1), per term. *Open*. -/
  E1 : EnvelopeInputsBlock.EnvelopeBoundInputs Dv.toA1.toV2.toCertData.toData
  /-- The sharp first-stage terms, per term. *Open*. -/
  SF : EnvelopeInputsBlock.SharpFirstInputs Dv.toA1.toV2.toCertData.toData
  /-- The fixed-interval envelope energies, per term. *Open*. -/
  fix : EnvelopeInputsBlock.FixedIntervalInputs
    (BlockAnchor.index_coprime_block Dv.toA1.toV2.toCertData.toData) Dv.toA1.toV2.toCertData.toData
  /-- The envelope energies, per term. *Open*. -/
  env : EnvelopeInputsBlock.EnvelopeEnergyInputs
    (BlockAnchor.index_coprime_block Dv.toA1.toV2.toCertData.toData) Dv.toA1.toV2.toCertData.toData

variable {blockOf}

/-- **To A2's obligations**: `CB := CI.toClassBounds`, `hΨ := PD.hΨ hB`, `hCB := CI.robustNonneg`;
the other fields copied. -/
noncomputable def B4FinalObligationsTarget.toA2 {hW : Target.Weil}
    (O : B4FinalObligationsTarget blockOf hW) : A2FinalObligationsTarget blockOf hW where
  Dv := O.Dv
  CB := O.CI.toClassBounds
  hΨ := O.PD.hΨ O.hB
  hCB := O.CI.robustNonneg
  hB := O.hB
  hL₀ := O.hL₀
  hT := O.hT
  hSA := O.hSA
  hm := O.hm
  E1 := O.E1
  SF := O.SF
  fix := O.fix
  env := O.env

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵`, with the class bounds of the paper's
construction** (`thm:main` at `ε = a_T/71`, via `thm:comparison` with (CP5) and
`prop:closing-data`(d)): from the literature inputs and `B4FinalObligationsTarget blockOf`, in
which (CP5) is `ClassInputs.toClassBounds` (`def:cp5`, `cor:envelope-costs`, `cor:var-classes`),
its robustness is proved (`def:robust`), and the complete polynomial is bounded by the ledger's
`𝓔` with the sixteen class savings kernel-checked (F15). -/
theorem main_target_paper_block_B4_A2 (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmallRR : Target.ThetaSmallRR) (O : B4FinalObligationsTarget blockOf hWeil) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_block_A2 hWeil hMovingRoot hFourCycle hThetaSmallRR O.toA2

end Sarkozy.ClassBoundsPaper
