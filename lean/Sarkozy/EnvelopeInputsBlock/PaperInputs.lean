module

public import Sarkozy.EnvelopeInputsBlock.Inputs
public import Sarkozy.EnvelopeInputsBlock.PaperMoment

@[expose] public section






open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.EnvelopeInputsBlock

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.Param (Params)
open Sarkozy.LedgerAnchor (anchorLedger)
open Sarkozy.BlockAnchor (BlockPaperData BlockPaperObligations index_coprime_block)
open Sarkozy.CancellationSteps

variable {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : PaperJ0 → Bk)

/-- **Everything that remains between the tree and the target at `a₀`, for the paper's data on its
prefix atoms, with the envelope hypotheses at the level of their per-term inputs.** K0's
`BlockPaperObligations blk` with `hE1`, `hSF`, `hfix` and `henv` replaced by the four bundles `E1`,
`SF`, `fix`, `env` of per-term inputs. The first ten fields are K0's (D1's labels and statuses). -/
structure BlockPaperInputObligations (hW : Target.Weil) where
  /-- **The open parts of the comparison data** (`def:cp0`–`def:cp8`). *Open* (Part V). -/
  Dp : BlockPaperData blk hW
  /-- **The (CP5) class bounds** (`def:cp5`) of the comparison law at `a₀`. *Open* (Part V). -/
  CB : TheoremCBlock.ClassBounds Params.anchorDecay paperM0 blk paperTail Dp.toData.CL
  /-- **The complete polynomial with class bounds is at most the ledger's `E`** at every scale
  (`def:cp5`, `thm:comparison`). *Open* (Part V, certificate family F15). -/
  hΨ : ∀ L, ∑ ω ∈ univ.filter (fun ω : Choice (Dp.toData.CL.T L) => IsSelection ω),
    (if CB.cls L ω = none then Dp.toData.B * monomial (Dp.toData.CL.π L) ω else CB.phi L ω) ≤
      anchorLedger.E
  /-- The class bounds are robust with nonnegative remainders (`def:robust`, (CP5)). *Open*. -/
  hCB : CB.RobustNonneg
  /-- `B ≤` the ledger's `B` ((CP3), `def:closing-quantities`). *Open* (Part V). -/
  hB : Dp.toData.B ≤ anchorLedger.B
  /-- `L₀ ≤` the ledger's `L₀` ((CP2)), with the first-stage prices at the paper's block factors.
  *Open* (Part V). -/
  hL₀ : Dp.toData.L₀ ≤ anchorLedger.L₀
  /-- `T ≤` the ledger's `T` ((CP6)). *Open* (Part V). -/
  hT : Dp.toData.ME.T ≤ anchorLedger.T
  /-- **`M_pad(K) ≤` the ledger's `R_I`** (`cert:index-moment`, family F2). *Open* (numeric). -/
  hR : Sarkozy.PaperData.paperRI ≤ anchorLedger.R_I
  /-- `S + A ≤` the ledger's `S + A` ((CP4)). *Open* (Part V). -/
  hSA : Dp.toData.CL.S + Dp.toData.CL.A ≤ anchorLedger.S + anchorLedger.A
  /-- **The mean credit pays the joint-closing allocations** (`cor:joint-closing`,
  `prop:joint-middle-mean`, `prop:joint-upper-mean`). *Open* (Part V). -/
  hm : anchorLedger.m₁ + 64 * ((anchorLedger.deltaAlpha + anchorLedger.deltaMatching +
    anchorLedger.deltaOdd + anchorLedger.deltaEven) + anchorLedger.deltaUpper -
    anchorLedger.upperError) ≤ Dp.toData.MC.m
  /-- **(E1), per term** (`lem:bracket-energy`, `lem:density:coupled`): the subset terms and the
  coupled sharp-first terms under the selected envelopes, at `a₀`, on the block atoms. *Open*
  (replaces `hE1`). -/
  E1 : EnvelopeBoundInputs Dp.toData
  /-- **The sharp first-stage terms, per term** (`lem:sharp-first`, `lem:density:coupled`), at
  `a₀`, on the block atoms. *Open* (replaces `hSF`). -/
  SF : SharpFirstInputs Dp.toData
  /-- **The fixed-interval envelope energies, per term** (`lem:envelope-energy`,
  `lem:hyb:moment`), at `a₀`, on the block atoms. *Open* (replaces `hfix`). -/
  fix : FixedIntervalInputs (index_coprime_block Dp.toData) Dp.toData
  /-- **The envelope energies, per term** (`lem:envelope-energy`, `lem:hyb:moment`), at `a₀`, on
  the block atoms. *Open* (replaces `henv`). -/
  env : EnvelopeEnergyInputs (index_coprime_block Dp.toData) Dp.toData

variable {blk}

/-- **K0's obligations from the per-term inputs**: the four envelope hypotheses at `a₀` on the
block atoms are I1's reductions (`EnvelopeBoundInputs.envelopeBoundNonneg`,
`SharpFirstInputs.sharpFirstTerms`, `FixedIntervalInputs.fixedIntervalEnvelopeEnergies`,
`EnvelopeEnergyInputs.envelopeEnergies`), with `0 ≤ a₀` and the paper's `IndexMomentBound`
(`paper_indexMomentBound_block`); the other ten fields are copied. -/
noncomputable def BlockPaperInputObligations.toObligations {hW : Target.Weil}
    (O : BlockPaperInputObligations blk hW) : BlockPaperObligations blk hW where
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
  hfix := O.fix.fixedIntervalEnvelopeEnergies (index_coprime_block O.Dp.toData)
    TheoremCParam.ComparisonData.anchorDecay_nonneg (paper_indexMomentBound_block O.Dp)
  henv := O.env.envelopeEnergies (index_coprime_block O.Dp.toData)
    TheoremCParam.ComparisonData.anchorDecay_nonneg (paper_indexMomentBound_block O.Dp)

/-- **The target at `a₀` for the paper's data on its prefix atoms, with the envelope hypotheses per
term** (`thm:main` at the formal exponent, through `thm:density:induction` and
`thm:comparison`): K0's `main_anchor_paper_block` with `BlockPaperInputObligations.toObligations`,
for every block assignment `blk`. The literature inputs are those of `main_anchor_paper_block`. -/
theorem main_anchor_paper_block_inputs (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (O : BlockPaperInputObligations blk hWeil) : Target.SarkozyBound Param.anchorSaving :=
  BlockAnchor.main_anchor_paper_block hWeil hMovingRoot hFourCycle O.toObligations

end Sarkozy.EnvelopeInputsBlock
