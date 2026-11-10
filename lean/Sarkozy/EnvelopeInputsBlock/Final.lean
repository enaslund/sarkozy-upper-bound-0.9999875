module

public import Sarkozy.EnvelopeInputsBlock.PaperInputs
public import Sarkozy.IndexCert.BlockCert

@[expose] public section

/-!
# The block-atom assembly at `a₀` with both reductions: index law certified, envelopes per term

`main_anchor_paper_block_final` concludes `Target.SarkozyBound Param.anchorSaving` from the
literature inputs (`Target.Weil`, `Target.MovingRoot`, `Target.FourCycle`,
and H2″, `Target.ThetaSmall`) and one structure, `BlockFinalObligations blk`, for any block
assignment `blk` of the fixed primes. It combines two reductions of K0's `BlockPaperObligations`:
* CERT1's (`IndexCert.BlockCert`): `hIdx` (`lem:imp:padic-envelope`) is proved
  (`IndexCert.paperIndexBound`), and `hR` (`cert:index-moment`) follows from H2″
  (`IndexCert.paperRI_le_anchorLedger`);
* G1's (`EnvelopeInputsBlock.PaperInputs`): the four envelope hypotheses `hE1`, `hSF`, `hfix`,
  `henv` are replaced by the per-term inputs of I1's reductions (the bundles of `Inputs.lean`), with
  I1's `IndexMomentBound` proved (`paper_indexMomentBound_block`) and `0 ≤ a₀`.

`BlockFinalObligations` is CERT1's `BlockCertObligations` with `hE1`, `hSF`, `hfix`, `henv`
replaced by the bundles `E1`, `SF`, `fix`, `env`, over CERT1's `BlockCertData`.
`toCertObligations` maps it to CERT1's structure, and the theorem is CERT1's
`main_anchor_paper_block_cert`. As a sanity check, `ofInputObligations` maps G1's
`BlockPaperInputObligations` to it by forgetting `hIdx` and `hR`, field for field.

**Field count.**
* K0's `BlockPaperObligations`: 14 fields (`Dp` and 13 others), with `BlockPaperData` of 12;
  25 open leaves.
* `BlockFinalObligations`: 13 fields (`Dp` and 12 others), with `BlockCertData` of 11; 23 open
  leaves, plus the literature input `Target.ThetaSmall`. Four of the 12 are the bundles of
  per-term inputs: `E1` has 7 fields, `SF` 6, `fix` and `env` 11 each.
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.EnvelopeInputsBlock

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.Param (Params)
open Sarkozy.LedgerAnchor (anchorLedger)
open Sarkozy.BlockAnchor (index_coprime_block)
open Sarkozy.IndexCert (BlockCertData BlockCertObligations)
open Sarkozy.CancellationSteps

variable {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : PaperJ0 → Bk)

/-- **Everything that remains between the tree and the target at `a₀`, for the paper's data on its
prefix atoms, with the index law certified and the envelope hypotheses per term.** CERT1's
`BlockCertObligations blk` (K0's `BlockPaperObligations` without `hR`, over `BlockCertData`, which
has no `hIdx`) with `hE1`, `hSF`, `hfix` and `henv` replaced by the four bundles `E1`, `SF`, `fix`,
`env` of per-term inputs. 13 fields: the open data `Dp` and 12 others. Labels and statuses are
K0's (D1's, P1's) and G1's. -/
structure BlockFinalObligations (hW : Target.Weil) where
  /-- **The open parts of the comparison data** (`def:cp0`–`def:cp8`), without `hIdx`
  (`lem:imp:padic-envelope`, proved by CERT1). *Open* (Part V). -/
  Dp : BlockCertData blk hW
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
  /-- `S + A ≤` the ledger's `S + A` ((CP4)). *Open* (Part V). -/
  hSA : Dp.toData.CL.S + Dp.toData.CL.A ≤ anchorLedger.S + anchorLedger.A
  /-- **The mean credit pays the joint-closing allocations** (`cor:joint-closing`,
  `prop:joint-middle-mean`, `prop:joint-upper-mean`). *Open* (Part V). -/
  hm : anchorLedger.m₁ + 64 * ((anchorLedger.deltaAlpha + anchorLedger.deltaMatching +
    anchorLedger.deltaOdd + anchorLedger.deltaEven) + anchorLedger.deltaUpper -
    anchorLedger.upperError) ≤ Dp.toData.MC.m
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

/-- **CERT1's obligations from the per-term inputs**: the four envelope hypotheses at `a₀` on the
block atoms are I1's reductions, with `0 ≤ a₀` and the paper's `IndexMomentBound`
(`paper_indexMomentBound_block`); the other nine fields are copied. -/
noncomputable def BlockFinalObligations.toCertObligations {hW : Target.Weil}
    (O : BlockFinalObligations blk hW) : BlockCertObligations blk hW where
  Dp := O.Dp
  CB := O.CB
  hΨ := O.hΨ
  hCB := O.hCB
  hB := O.hB
  hL₀ := O.hL₀
  hT := O.hT
  hSA := O.hSA
  hm := O.hm
  hE1 := O.E1.envelopeBoundNonneg TheoremCParam.ComparisonData.anchorDecay_nonneg
  hSF := O.SF.sharpFirstTerms TheoremCParam.ComparisonData.anchorDecay_nonneg
  hfix := O.fix.fixedIntervalEnvelopeEnergies (index_coprime_block O.Dp.toData)
    TheoremCParam.ComparisonData.anchorDecay_nonneg
    (paper_indexMomentBound_block O.Dp.toBlockPaperData)
  henv := O.env.envelopeEnergies (index_coprime_block O.Dp.toData)
    TheoremCParam.ComparisonData.anchorDecay_nonneg
    (paper_indexMomentBound_block O.Dp.toBlockPaperData)

/-- **Sanity: the final obligations are no stronger than G1's `BlockPaperInputObligations`.**
Forgetting `hIdx` (in the data) and `hR` turns `BlockPaperInputObligations blk` into
`BlockFinalObligations blk`; every other field, the four bundles included, is passed unchanged
(the index law of the data does not depend on the proof of `hIdx`). -/
noncomputable def BlockFinalObligations.ofInputObligations {hW : Target.Weil}
    (O : BlockPaperInputObligations blk hW) : BlockFinalObligations blk hW where
  Dp :=
    { μ₀ := O.Dp.μ₀
      rp₀ := O.Dp.rp₀
      inv₀ := O.Dp.inv₀
      unif₀ := O.Dp.unif₀
      hV := O.Dp.hV
      FS := O.Dp.FS
      GB := O.Dp.GB
      CL := O.Dp.CL
      ME := O.Dp.ME
      MC := O.Dp.MC
      SM := O.Dp.SM }
  CB := O.CB
  hΨ := O.hΨ
  hCB := O.hCB
  hB := O.hB
  hL₀ := O.hL₀
  hT := O.hT
  hSA := O.hSA
  hm := O.hm
  E1 := O.E1
  SF := O.SF
  fix := O.fix
  env := O.env

/-- **The target at `a₀` for the paper's data on its prefix atoms, with the index law certified
and the envelope hypotheses per term** (`thm:main` at the formal exponent, via `thm:comparison`
and `thm:density:induction`). From the literature inputs, H2″ (`Target.ThetaSmall`, for
`cert:index-moment`) and `BlockFinalObligations blk`, for any block assignment `blk` of the fixed
primes: CERT1's `main_anchor_paper_block_cert` with `BlockFinalObligations.toCertObligations`. -/
theorem main_anchor_paper_block_final (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmall : Target.ThetaSmall) (O : BlockFinalObligations blk hWeil) :
    Target.SarkozyBound Param.anchorSaving :=
  IndexCert.main_anchor_paper_block_cert hWeil hMovingRoot hFourCycle hThetaSmall
    O.toCertObligations

end Sarkozy.EnvelopeInputsBlock
