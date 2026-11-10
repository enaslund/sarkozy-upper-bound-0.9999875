module

public import Sarkozy.BlockAnchor.Paper
public import Sarkozy.IndexCert.Moment
public import Sarkozy.IndexCert.EnvelopePaper

@[expose] public section

/-!
# The block-atom assembly at `a₀` with the index law certified

`main_anchor_paper_block_cert` is K0's `BlockAnchor.main_anchor_paper_block` with the two
index-law obligations discharged:
* `lem:imp:padic-envelope` (the field `hIdx` of `BlockPaperData`), proved with no hypothesis
  (`IndexCert.paperIndexBound`);
* `cert:index-moment` (the field `hR` of `BlockPaperObligations`), proved from H2″
  (`Target.ThetaSmall`) by `IndexCert.paperRI_le_anchorLedger`.

`BlockCertData` is `BlockPaperData` without `hIdx`, and `BlockCertObligations` is
`BlockPaperObligations` without `hR`, over `BlockCertData`. Every other field, with its label and
status, is K0's (D1's, P1's). `BlockCertObligations.toObligations` rebuilds K0's structure.

**Field count.** Before: `BlockPaperObligations` has 14 fields (the data `Dp` and 13 others), and
`BlockPaperData` has 12; 25 open leaves. After: `BlockCertObligations` has 13 fields (`Dp` and 12
others), and `BlockCertData` has 11; 23 open leaves, plus the literature input `Target.ThetaSmall`.
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.IndexCert

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.Param (Params)
open Sarkozy.LedgerAnchor (anchorLedger)
open Sarkozy.CancellationSteps Sarkozy.PaperFrame Sarkozy.FourierArithmetic Sarkozy.Functional
  Sarkozy.IndexSupport Sarkozy.BlockFrame Sarkozy.MainAnchor Sarkozy.BlockAnchor

variable {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : PaperJ0 → Bk)

/-- **The open parts of the comparison data on the prefix atoms, with the index law certified**
(`def:cp0`–`def:cp8`, `def:construction`). K0's `BlockPaperData` without `hIdx`, which is
`lem:imp:padic-envelope`, proved (`IndexCert.paperIndexBound`). All *open* (Part V):
* `μ₀`, `rp₀`, `inv₀`, `unif₀`: the block laws of the prefix (the square-clique laws of the atoms
  `{p}`, the middle and upper block laws, `def:construction`(b)) with (R2) at the cuts of `𝔉`,
  (R3) and uniform marginals. V1 and V2 prove these for each block law given the spectral inputs
  (`PartV.middleBlockReference_*`, `PartVLaws.upperBlock_R1R3`, `Construction/`);
* `hV`: `lem:tail-law`(i), the validity of the tail inputs (spectral);
* `FS`, `GB`, `CL`, `ME`, `MC`, `SM`: (CP2)–(CP4), (CP6)–(CP8) at `a₀` on the block atoms, priced by
  `paperSel blk`. -/
structure BlockCertData (hW : Target.Weil) where
  μ₀ : ∀ β, FiniteLaw (Slot → BlockRes paperM0 blk β)
  rp₀ : ∀ β, FamilyReflectionPositive (signedIntegral (μ₀ β).weight)
  inv₀ : ∀ β (a : ∀ i, (ZMod (blockModuli paperM0 blk β i))ˣ) (b : BlockRes paperM0 blk β),
    (∀ i, IsSquare ((a i : ZMod (blockModuli paperM0 blk β i)))) →
      ∀ F : (Slot → BlockRes paperM0 blk β) → ℝ,
        (μ₀ β).expect (fun z => F (fun v => piAffineEquiv (blockModuli paperM0 blk β) a b (z v))) =
          (μ₀ β).expect F
  unif₀ : ∀ β, HasUniformMarginals (μ₀ β)
  hV : PartVLaws.TailInputsValid PartV.P4
  FS : TheoremCBlock.FirstStage Params.anchorDecay paperM0 blk paperTail (paperSel blk)
    (blockPaperReference blk hW μ₀ rp₀ inv₀ unif₀ hV)
  GB : TheoremCBlock.GramBracket Params.anchorDecay paperM0 blk paperTail (paperSel blk) FS
  CL : TheoremCBlock.ComparisonLaw Params.anchorDecay paperM0 blk paperTail (paperSel blk) paperPP
    paperEP paperQueries FS
  ME : TheoremCBlock.MatchingEnvelopes Params.anchorDecay paperM0 blk paperTail GB CL
  MC : TheoremCBlock.MeanCredit Params.anchorDecay paperM0 blk paperTail ME
  SM : TheoremCBlock.Summability Params.anchorDecay paperM0 blk paperTail ME

variable {blk}

/-- K0's `BlockPaperData`, with `hIdx := IndexCert.paperIndexBound` (`lem:imp:padic-envelope`). -/
noncomputable def BlockCertData.toBlockPaperData {hW : Target.Weil} (Dp : BlockCertData blk hW) :
    BlockPaperData blk hW where
  hIdx := paperIndexBound
  μ₀ := Dp.μ₀
  rp₀ := Dp.rp₀
  inv₀ := Dp.inv₀
  unif₀ := Dp.unif₀
  hV := Dp.hV
  FS := Dp.FS
  GB := Dp.GB
  CL := Dp.CL
  ME := Dp.ME
  MC := Dp.MC
  SM := Dp.SM

/-- The comparison data at `a₀` on the block atoms (K0's `BlockPaperData.toData`). -/
noncomputable abbrev BlockCertData.toData {hW : Target.Weil} (Dp : BlockCertData blk hW) :
    TheoremCBlock.ComparisonData Params.anchorDecay paperM0 blk paperTail paperPr paperH
      Chamber :=
  Dp.toBlockPaperData.toData

variable (blk) in
/-- **Everything that remains between the tree and the target at `a₀`, for the paper's data on its
prefix atoms, with the index law certified.** K0's `BlockPaperObligations` without `hR`, which is
`cert:index-moment`, proved from H2″ (`IndexCert.paperRI_le_anchorLedger`), over
`BlockCertData`: the open data `Dp` and 12 others. Labels and statuses are K0's (D1's, P1's); the
ledger is `anchorLedger`. -/
structure BlockCertObligations (hW : Target.Weil) where
  /-- **The open parts of the comparison data** (`def:cp0`–`def:cp8`). *Open* (Part V). -/
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
  /-- **(E1), the envelope bound with nonnegative remainders** (`lem:bracket-energy` at `ϑ`, via
  `prop:density:production`). *Open at `a₀`*. The selection factor of a selection is now the
  product of the factors of the selected blocks and tail primes only. -/
  hE1 : Dp.toData.EnvelopeBoundNonneg
  /-- **The sharp first-stage terms** (`lem:sharp-first`, `lem:record:folded-energy`). *Open at
  `a₀`*. -/
  hSF : Dp.toData.SharpFirstTerms
  /-- **The fixed-interval envelope energies** (`lem:envelope-energy`). *Open at `a₀`*. -/
  hfix : Dp.toData.FixedIntervalEnvelopeEnergies (index_coprime_block Dp.toData)
  /-- **The envelope energies** (`lem:envelope-energy`). *Open at `a₀`*. -/
  henv : Dp.toData.EnvelopeEnergies (index_coprime_block Dp.toData)

/-- K0's `BlockPaperObligations` from the certified obligations: `hIdx` and `hR` are filled by
`IndexCert.paperIndexBound` (`lem:imp:padic-envelope`) and `IndexCert.paperRI_le_anchorLedger`
(`cert:index-moment`, from H2″). -/
noncomputable def BlockCertObligations.toObligations {hW : Target.Weil}
    (hThetaSmall : Target.ThetaSmall) (O : BlockCertObligations blk hW) :
    BlockPaperObligations blk hW where
  Dp := O.Dp.toBlockPaperData
  CB := O.CB
  hΨ := O.hΨ
  hCB := O.hCB
  hB := O.hB
  hL₀ := O.hL₀
  hT := O.hT
  hR := paperRI_le_anchorLedger hThetaSmall
  hSA := O.hSA
  hm := O.hm
  hE1 := O.hE1
  hSF := O.hSF
  hfix := O.hfix
  henv := O.henv

/-- **Sanity: the certified obligations are no stronger than K0's.** Forgetting `hIdx` and `hR`
turns K0's `BlockPaperObligations` into `BlockCertObligations` (the index law of the data does
not depend on the proof of `hIdx`), so every field is K0's field, unchanged. -/
noncomputable def BlockCertObligations.ofObligations {hW : Target.Weil}
    (O : BlockPaperObligations blk hW) : BlockCertObligations blk hW where
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
  hE1 := O.hE1
  hSF := O.hSF
  hfix := O.hfix
  henv := O.henv

/-- **The target at `a₀` for the paper's data on its prefix atoms, with the index law certified**
(`thm:main` at the formal exponent, via `thm:comparison` and `thm:density:induction`), from the
literature inputs, H2″ (`Target.ThetaSmall`, for `cert:index-moment`) and the remaining
obligations, for any block assignment `blk` of the fixed primes. K0's `main_anchor_paper_block`
with `BlockCertObligations.toObligations`. -/
theorem main_anchor_paper_block_cert (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmall : Target.ThetaSmall) (O : BlockCertObligations blk hWeil) :
    Target.SarkozyBound Param.anchorSaving :=
  main_anchor_paper_block hWeil hMovingRoot hFourCycle (O.toObligations hThetaSmall)

end Sarkozy.IndexCert
