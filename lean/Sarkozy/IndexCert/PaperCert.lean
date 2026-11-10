module

public import Sarkozy.MainAnchor.Paper
public import Sarkozy.IndexCert.Moment
public import Sarkozy.IndexCert.EnvelopePaper

@[expose] public section

/-!
# The merged-atom assembly at `a₀` with the index law certified

`main_anchor_paper_cert` is D1's `MainAnchor.main_anchor_paper` (the merged prefix atom) with the
two index-law obligations discharged, exactly as `main_anchor_paper_block_cert` does for K0's block
atoms (`BlockCert.lean`, the version that matters):
* `lem:imp:padic-envelope` (the field `hIdx` of `PaperData`), proved with no hypothesis
  (`IndexCert.paperIndexBound`);
* `cert:index-moment` (the field `hR` of `PaperObligations`), proved from H2″ (`Target.ThetaSmall`)
  by `IndexCert.paperRI_le_anchorLedger`.

**Field count.** Before: `PaperObligations` has 14 fields (`Dp` and 13 others), and `PaperData`
has 14; 27 open leaves. After: `PaperCertObligations` has 13 fields, and `PaperCertData` has 13;
25 open leaves, plus the literature input `Target.ThetaSmall`.
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.IndexCert

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.Param (Params)
open Sarkozy.LedgerAnchor (anchorLedger)
open Sarkozy.CancellationSteps Sarkozy.PaperFrame Sarkozy.FourierArithmetic Sarkozy.Functional
  Sarkozy.IndexSupport Sarkozy.MainAnchor

/-- **The open parts of the comparison data `D` for the paper's construction, with the index law
certified** (`def:cp0`–`def:cp8`, `def:construction`). D1's `PaperData` without `hIdx`, which is
`lem:imp:padic-envelope`, proved (`IndexCert.paperIndexBound`). All *open* (Part V), with P1's
statuses:
* `selPre`, `one_le_selPre`: the selection factor of the merged prefix atom (`def:price`,
  `def:cp0`). It is kept: the paper's `def:price` value for the merged atom, the product of the
  factors of all its atoms, would make the first-stage price total at the merged atom
  astronomically large (WP-FI's note on the merged prefix atom; I1's "Gap 2");
* `μ₀`, `rp₀`, `inv₀`, `unif₀`: the prefix reference law (the clique and block laws carried to
  `ResidueSpace M`) with (R2), (R3) and uniform marginals. V2's `PartVLaws.prefixAssembly`
  builds these from atom laws with (R1)–(R3), once the block partitions are entered;
* `hV`: `lem:tail-law`(i), the validity of the tail inputs at every tail prime (spectral). It
  gives `rpp`;
* `FS`, `GB`, `CL`, `ME`, `MC`, `SM`: (CP2)–(CP4), (CP6)–(CP8) at `a₀`. -/
structure PaperCertData (hW : Target.Weil) where
  selPre : ℝ
  one_le_selPre : 1 ≤ selPre
  μ₀ : FiniteLaw (Slot → ResidueSpace paperM0)
  rp₀ : FamilyReflectionPositive (signedIntegral μ₀.weight)
  inv₀ : ∀ (a : ∀ i, (ZMod (paperM0 i))ˣ) (b : ResidueSpace paperM0),
    (∀ i, IsSquare ((a i : ZMod (paperM0 i)))) → ∀ F : (Slot → ResidueSpace paperM0) → ℝ,
      μ₀.expect (fun z => F (fun v => piAffineEquiv paperM0 a b (z v))) = μ₀.expect F
  unif₀ : HasUniformMarginals μ₀
  hV : PartVLaws.TailInputsValid PartV.P4
  FS : TheoremCParam.FirstStage Params.anchorDecay paperM0 paperTail selPre
    (paperReference hW μ₀ rp₀ inv₀ unif₀ hV)
  GB : TheoremCParam.GramBracket Params.anchorDecay paperM0 paperTail selPre FS
  CL : TheoremCParam.ComparisonLaw Params.anchorDecay paperM0 paperTail selPre paperPP paperEP
    paperQueries FS
  ME : TheoremCParam.MatchingEnvelopes Params.anchorDecay paperM0 paperTail GB CL
  MC : TheoremCParam.MeanCredit Params.anchorDecay paperM0 paperTail ME
  SM : TheoremCParam.Summability Params.anchorDecay paperM0 paperTail ME

/-- D1's `PaperData`, with `hIdx := IndexCert.paperIndexBound` (`lem:imp:padic-envelope`). -/
noncomputable def PaperCertData.toPaperData {hW : Target.Weil} (Dp : PaperCertData hW) :
    PaperData hW where
  selPre := Dp.selPre
  one_le_selPre := Dp.one_le_selPre
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

/-- The comparison data at `a₀` (D1's `PaperData.toData`). -/
noncomputable abbrev PaperCertData.toData {hW : Target.Weil} (Dp : PaperCertData hW) :
    TheoremCParam.ComparisonData Params.anchorDecay paperM0 paperTail paperPr paperH Chamber :=
  Dp.toPaperData.toData

/-- **Everything that remains between the tree and the target at `a₀`, for the paper's data, with
the index law certified.** D1's `PaperObligations` without `hR`, which is `cert:index-moment`,
proved from H2″ (`IndexCert.paperRI_le_anchorLedger`), over `PaperCertData`: the open data `Dp`
and 12 others. Labels and statuses are D1's (P1's); the ledger is `anchorLedger`. -/
structure PaperCertObligations (hW : Target.Weil) where
  /-- **The open parts of the comparison data** (`def:cp0`–`def:cp8`). *Open* (Part V). -/
  Dp : PaperCertData hW
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
  /-- `S + A ≤` the ledger's `S + A` ((CP4)). *Open* (Part V). -/
  hSA : Dp.toData.CL.S + Dp.toData.CL.A ≤ anchorLedger.S + anchorLedger.A
  /-- **The mean credit pays the joint-closing allocations** (`cor:joint-closing`,
  `prop:joint-middle-mean`, `prop:joint-upper-mean`). *Open* (Part V). -/
  hm : anchorLedger.m₁ + 64 * ((anchorLedger.deltaAlpha + anchorLedger.deltaMatching +
    anchorLedger.deltaOdd + anchorLedger.deltaEven) + anchorLedger.deltaUpper -
    anchorLedger.upperError) ≤ Dp.toData.MC.m
  /-- **(E1), the envelope bound with nonnegative remainders** (`lem:bracket-energy` at `ϑ`, via
  `prop:density:production`). *Open at `a₀`* (P1's docstring of `PartVObligations.hE1`). -/
  hE1 : Dp.toData.EnvelopeBoundNonneg
  /-- **The sharp first-stage terms** (`lem:sharp-first`, `lem:record:folded-energy`). *Open at
  `a₀`*. -/
  hSF : Dp.toData.SharpFirstTerms
  /-- **The fixed-interval envelope energies** (`lem:envelope-energy`). *Open at `a₀`*. -/
  hfix : Dp.toData.FixedIntervalEnvelopeEnergies (index_coprime Dp.toData)
  /-- **The envelope energies** (`lem:envelope-energy`). *Open at `a₀`*. -/
  henv : Dp.toData.EnvelopeEnergies (index_coprime Dp.toData)

/-- D1's `PaperObligations` from the certified obligations: `hIdx` and `hR` are filled by
`IndexCert.paperIndexBound` (`lem:imp:padic-envelope`) and `IndexCert.paperRI_le_anchorLedger`
(`cert:index-moment`, from H2″). -/
noncomputable def PaperCertObligations.toObligations {hW : Target.Weil}
    (hThetaSmall : Target.ThetaSmall) (O : PaperCertObligations hW) : PaperObligations hW where
  Dp := O.Dp.toPaperData
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

/-- **Sanity: the certified obligations are no stronger than D1's.** Forgetting `hIdx` and `hR`
turns D1's `PaperObligations` into `PaperCertObligations`; every field is D1's, unchanged. -/
noncomputable def PaperCertObligations.ofObligations {hW : Target.Weil}
    (O : PaperObligations hW) : PaperCertObligations hW where
  Dp :=
    { selPre := O.Dp.selPre
      one_le_selPre := O.Dp.one_le_selPre
      μ₀ := O.Dp.μ₀
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

/-- **The target at `a₀` for the paper's data (merged prefix atom), with the index law
certified**, from the literature inputs, H2″ (`Target.ThetaSmall`, for `cert:index-moment`) and the
remaining obligations. D1's `main_anchor_paper` with `PaperCertObligations.toObligations`. The
block-atom version `main_anchor_paper_block_cert` is the one meant to be satisfiable at the paper's
prices (K0, D1 package 6). -/
theorem main_anchor_paper_cert (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmall : Target.ThetaSmall) (O : PaperCertObligations hWeil) :
    Target.SarkozyBound Param.anchorSaving :=
  main_anchor_paper hWeil hMovingRoot hFourCycle (O.toObligations hThetaSmall)

end Sarkozy.IndexCert
