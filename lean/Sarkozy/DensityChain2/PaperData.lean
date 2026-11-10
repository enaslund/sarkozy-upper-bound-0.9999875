module

public import Sarkozy.DensityChain2.Folded
public import Sarkozy.MainTarget.Block
public import Sarkozy.BlockAnchor.Paper

@[expose] public section

/-!
# The parity condition and the selection factors for the paper's standing data

The constructors of `Fields` take the parity condition `e_p ∈ {1} ∪ 2ℕ` and `blockSel ≤ selPre`
as hypotheses on the data. For the paper's standing data on the block atoms (K0's
`BlockAnchor.blockPaperStanding` at `a₀`, and `MainTarget.blockPaperStandingAt` at any `a ≥ 0`,
in particular `a_T`) the exponents are `paperEP` and the selection factors are the `def:price`
values, so both hold (the second with equality).
-/

namespace Sarkozy.DensityChain2

open Sarkozy.CancellationSteps Sarkozy.BlockAnchor

variable {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : PaperJ0 → Bk)

omit [Fintype Bk] in
/-- The parity condition for `MainTarget.blockPaperStandingAt` (`e_p = paperEP`). -/
theorem parity_blockPaperStandingAt (a : ℝ) (ha : 0 ≤ a)
    (index : Sarkozy.TheoremC.IndexLaw paperPr paperH Chamber) :
    ParityCondition (MainTarget.blockPaperStandingAt blk a ha index).ep :=
  paperEP_parity

omit [Fintype Bk] in
/-- `blockSel ≤ selPre` (with equality) for `MainTarget.blockPaperStandingAt`. -/
theorem hsel_blockPaperStandingAt (a : ℝ) (ha : 0 ≤ a)
    (index : Sarkozy.TheoremC.IndexLaw paperPr paperH Chamber) (β : Bk) :
    blockSel a (MainTarget.blockPaperStandingAt blk a ha index).pp
        (MainTarget.blockPaperStandingAt blk a ha index).ep blk β ≤
      (MainTarget.blockPaperStandingAt blk a ha index).selPre β :=
  le_of_eq (MainTarget.paperSelAt_eq blk a β).symm

omit [Fintype Bk] in
/-- The parity condition for K0's `BlockAnchor.blockPaperStanding`. -/
theorem parity_blockPaperStanding (index : Sarkozy.TheoremC.IndexLaw paperPr paperH Chamber) :
    ParityCondition (blockPaperStanding blk index).ep :=
  paperEP_parity

omit [Fintype Bk] in
/-- `blockSel ≤ selPre` (with equality) for K0's `BlockAnchor.blockPaperStanding` at `a₀`. -/
theorem hsel_blockPaperStanding (index : Sarkozy.TheoremC.IndexLaw paperPr paperH Chamber)
    (β : Bk) :
    blockSel Param.Params.anchorDecay (blockPaperStanding blk index).pp
        (blockPaperStanding blk index).ep blk β ≤ (blockPaperStanding blk index).selPre β :=
  le_of_eq (paperSel_eq blk β).symm

end Sarkozy.DensityChain2
