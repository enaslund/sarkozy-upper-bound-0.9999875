module

public import Sarkozy.EnvelopeInputsParam.Inputs
public import Sarkozy.EnvelopeInputsParam.PaperMoment

@[expose] public section

/-!
# The assembly at `a₀` with the envelope hypotheses replaced by their per-term inputs

`MainAnchor.main_anchor_paper` (D1) concludes `Target.SarkozyBound Param.anchorSaving` from the
literature inputs and `MainAnchor.PaperObligations`, 14 fields. Four of them are the envelope
hypotheses of Theorem C at `a₀`, as conclusions of Section 10 lemmas:
* `hE1 : EnvelopeBoundNonneg` (`lem:bracket-energy` at `ϑ`, `def:robust`);
* `hSF : SharpFirstTerms` (`lem:sharp-first`, `lem:record:folded-energy`);
* `hfix : FixedIntervalEnvelopeEnergies` and `henv : EnvelopeEnergies` (`lem:envelope-energy`).

`PaperInputObligations` is `PaperObligations` with those four fields replaced by the per-term
inputs of I1's reductions at `a₀` (`Inputs.lean`). `PaperInputObligations.toObligations`
rebuilds `PaperObligations` with the reductions; `main_anchor_paper_inputs` is then
`main_anchor_paper`. The two other inputs of the reductions are proved:
* `0 ≤ a₀` (`TheoremCParam.ComparisonData.anchorDecay_nonneg`);
* I1's `IndexMomentBound`, which both envelope energies use: for the paper's index law the
  conductor moment of every query is `R_I = M_pad(K)` exactly (`paper_indexMomentBound`,
  `PaperMoment.lean`).

The ten other fields are copied from `PaperObligations` with their labels and statuses. No file
of D1 or P1 is changed.
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.EnvelopeInputsParam

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.Param (Params)
open Sarkozy.LedgerAnchor (anchorLedger)
open Sarkozy.MainAnchor (PaperData PaperObligations index_coprime)
open Sarkozy.CancellationSteps

/-- **Everything that remains between the tree and the target at `a₀`, for the paper's data,
with the envelope hypotheses at the level of their per-term inputs.** D1's `PaperObligations`
with `hE1`, `hSF`, `hfix` and `henv` replaced by the four bundles `E1`, `SF`, `fix`, `env` of
per-term inputs. The first ten fields are those of `PaperObligations`, with its labels and
statuses. -/
structure PaperInputObligations (hW : Target.Weil) where
  /-- **The open parts of the comparison data** (`def:cp0`–`def:cp8`). *Open* (Part V). -/
  Dp : PaperData hW
  /-- **The (CP5) class bounds** (`def:cp5`) of the comparison law at `a₀`. *Open* (Part V). -/
  CB : TheoremCParam.ClassBounds Params.anchorDecay paperM0 paperTail Dp.toData.CL
  /-- **The complete polynomial with class bounds is at most the ledger's `E`** at every scale
  (`def:cp5`, `thm:comparison`). *Open* (Part V, certificate family F15). -/
  hΨ : ∀ L, ∑ ω ∈ univ.filter (fun ω : Choice (Dp.toData.CL.T L) => IsSelection ω),
    (if CB.cls L ω = none then Dp.toData.B * monomial (Dp.toData.CL.π L) ω else CB.phi L ω) ≤
      anchorLedger.E
  /-- The class bounds are robust with nonnegative remainders (`def:robust`, (CP5)). *Open*. -/
  hCB : CB.RobustNonneg
  /-- `B ≤` the ledger's `B` ((CP3), `def:closing-quantities`). *Open* (Part V). -/
  hB : Dp.toData.B ≤ anchorLedger.B
  /-- `L₀ ≤` the ledger's `L₀` ((CP2)). *Open* (Part V). -/
  hL₀ : Dp.toData.L₀ ≤ anchorLedger.L₀
  /-- `T ≤` the ledger's `T` ((CP6)). *Open* (Part V). -/
  hT : Dp.toData.ME.T ≤ anchorLedger.T
  /-- **`M_pad(K) ≤` the ledger's `R_I`** (`cert:index-moment`, family F2). *Open* (a numeric
  certificate). -/
  hR : Sarkozy.PaperData.paperRI ≤ anchorLedger.R_I
  /-- `S + A ≤` the ledger's `S + A` ((CP4)). *Open* (Part V). -/
  hSA : Dp.toData.CL.S + Dp.toData.CL.A ≤ anchorLedger.S + anchorLedger.A
  /-- **The mean credit pays the joint-closing allocations** (`cor:joint-closing`,
  `prop:joint-middle-mean`, `prop:joint-upper-mean`). *Open* (Part V). -/
  hm : anchorLedger.m₁ + 64 * ((anchorLedger.deltaAlpha + anchorLedger.deltaMatching +
    anchorLedger.deltaOdd + anchorLedger.deltaEven) + anchorLedger.deltaUpper -
    anchorLedger.upperError) ≤ Dp.toData.MC.m
  /-- **(E1), per term** (`lem:bracket-energy`, `lem:density:coupled`): the subset terms and the
  coupled sharp-first terms under the selected envelopes, at `a₀`. *Open* (replaces `hE1`). -/
  E1 : EnvelopeBoundInputs Dp.toData
  /-- **The sharp first-stage terms, per term** (`lem:sharp-first`, `lem:density:coupled`), at
  `a₀`. *Open* (replaces `hSF`). -/
  SF : SharpFirstInputs Dp.toData
  /-- **The fixed-interval envelope energies, per term** (`lem:envelope-energy`,
  `lem:hyb:moment`), at `a₀`. *Open* (replaces `hfix`). -/
  fix : FixedIntervalInputs (index_coprime Dp.toData) Dp.toData
  /-- **The envelope energies, per term** (`lem:envelope-energy`, `lem:hyb:moment`), at `a₀`.
  *Open* (replaces `henv`). -/
  env : EnvelopeEnergyInputs (index_coprime Dp.toData) Dp.toData

/-- **D1's obligations from the per-term inputs**: the four envelope hypotheses at `a₀` are
I1's reductions (`EnvelopeBoundInputs.envelopeBoundNonneg`, `SharpFirstInputs.sharpFirstTerms`,
`FixedIntervalInputs.fixedIntervalEnvelopeEnergies`, `EnvelopeEnergyInputs.envelopeEnergies`),
with `0 ≤ a₀` and the paper's `IndexMomentBound` (`paper_indexMomentBound`); the other ten
fields are copied. -/
noncomputable def PaperInputObligations.toObligations {hW : Target.Weil}
    (O : PaperInputObligations hW) : PaperObligations hW where
  Dp := O.Dp
  CB := O.CB
  hΨ := O.hΨ
  hCB := O.hCB
  hB := O.hB
  hL₀ := O.hL₀
  hT := O.hT
  hR := O.hR
  hSA := O.hSA
  hm := O.hm
  hE1 := O.E1.envelopeBoundNonneg TheoremCParam.ComparisonData.anchorDecay_nonneg
  hSF := O.SF.sharpFirstTerms TheoremCParam.ComparisonData.anchorDecay_nonneg
  hfix := O.fix.fixedIntervalEnvelopeEnergies (index_coprime O.Dp.toData)
    TheoremCParam.ComparisonData.anchorDecay_nonneg (paper_indexMomentBound O.Dp)
  henv := O.env.envelopeEnergies (index_coprime O.Dp.toData)
    TheoremCParam.ComparisonData.anchorDecay_nonneg (paper_indexMomentBound O.Dp)

/-- **The target at `a₀` for the paper's data, with the envelope hypotheses per term**
(`thm:main` at the formal exponent, through `thm:density:induction` and `thm:comparison`):
`main_anchor_paper` with `PaperInputObligations.toObligations`. The literature inputs are those
of `main_anchor_paper`. -/
theorem main_anchor_paper_inputs (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (O : PaperInputObligations hWeil) : Target.SarkozyBound Param.anchorSaving :=
  MainAnchor.main_anchor_paper hWeil hMovingRoot hFourCycle O.toObligations

end Sarkozy.EnvelopeInputsParam
