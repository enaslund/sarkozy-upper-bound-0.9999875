module

public import Sarkozy.NumericalFields.Bands
public import Sarkozy.NumericalFields.Main

@[expose] public section




open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.NumericalFields

open Sarkozy.MainFinal Sarkozy.MainFinal2
open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (paperAtomMap)
open Sarkozy.ComparisonLawPaper (upperBand blockSel specUpper)
open Sarkozy.PaperNumbers (paperCell HistogramClaim)

/-- **K2's field 35 (`SA.hUS`, = `SA.hUA`) from `thm:bmor`** (`Target.BMOR`, H2;
`lem:record:block-charge`(i), `eq:record:cell-charge`, `def:record:upper-bands`(b),
`prop:record:upper`(ii)): for every band `β` and every `d`, the charge of the upper blocks of the
band at `a_T` is at most `bandBound a_T d β`. -/
theorem upperBand_le_bandBound (hB : Target.BMOR) (hW : Target.Weil)
    (A : PaperAnalyticInputs paperCell) (β : Fin 310) (d : ℕ) :
    ∑ b ∈ upperBand (specF hW A) bandIdx β, blockSel bOf b * BlockSpecPaper.blockScale b ^ d ≤
      bandBound targetDecay d β := by
  have hsub : upperBand (specF hW A) bandIdx β ⊆
      univ.filter (fun b : PaperBlock paperCell => blockSite b = .inr β) := by
    intro b hb
    unfold ComparisonLawPaper.upperBand at hb
    rw [mem_filter, mem_filter] at hb
    obtain ⟨⟨-, hup⟩, hβ⟩ := hb
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rw [blockSite_of_upper b hup, hβ]
  calc ∑ b ∈ upperBand (specF hW A) bandIdx β, blockSel bOf b * BlockSpecPaper.blockScale b ^ d
      = ∑ b ∈ upperBand (specF hW A) bandIdx β, BlockSpecPaper.blockScale b ^ d *
          paperSelAt (paperAtomMap (paperBlockOf paperCell)) targetDecay (.inr b) :=
        sum_congr rfl fun b _ => mul_comm _ _
    _ ≤ ∑ b ∈ univ.filter (fun b : PaperBlock paperCell => blockSite b = .inr β),
          BlockSpecPaper.blockScale b ^ d *
            paperSelAt (paperAtomMap (paperBlockOf paperCell)) targetDecay (.inr b) := by
        apply sum_le_sum_of_subset_of_nonneg hsub
        intro b _ _
        refine mul_nonneg (pow_nonneg ?_ d)
          (zero_le_one.trans (one_le_paperSelAt _ targetDecay_nonneg _))
        unfold BlockSpecPaper.blockScale
        exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    _ ≤ bandBound targetDecay d β := bandCharge_le_bandBound hB β targetDecay_nonneg d

/-- **`hSA` in reduced form without the signs and without the band-charge field** (`SAPartsE2` at
`U = bandBound a_T`, `hU` proved by `upperBand_le_bandBound`). 13 fields. -/
structure SAPartsE3 (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs paperCell) (C : ComparisonParts2 hW hMR hFour A) where
  /-- The clique bound. Data. -/
  H : ℝ
  /-- `∑_p λ^ex_p(1) q_p^{2a} ≤ H` (`lem:frontier:iidenergy`(iii)). *Open* (analytic). -/
  hq : ∑ q, C.toK1.Ci.cliquePrice q ≤ H
  /-- The per-band record coefficients. Data. -/
  Cs : Fin 310 → UpIdx → ℝ
  Ca : Fin 310 → UpIdx → ℝ
  hCs : ∀ k i, 0 ≤ Cs k i
  hCa : ∀ k i, 0 ≤ Ca k i
  /-- The upper per-record bounds (`prop:record:upper`(ii), W8's ledger). *Open* (analytic). -/
  hR : C.toK1.UpperRecs hW A Cs Ca hCs hCa
  /-- The per-piece constants `(s_F, a_F, ℓ_t, s_E, a_E)`. Data. -/
  κ : Fin 33 → MiddleConsts
  /-- The constants are nonnegative. Side condition on the data `κ`. -/
  hκ : ∀ i, KappaNonneg (κ i)
  /-- **The twelve norm bounds of every middle block** (B8's `NormBounds`). *Open* (analytic). -/
  hN : ∀ b i, blockSite b = .inl i →
    SpecNormBounds hW (paperIn paperCell) (κ i) (blockLeast b) (specF hW A b) (C.blk b)
  /-- **The final numerical inequality** of `hSA`, at the band charges `bandBound a_T`
  (`def:closing-quantities`). *Open* (numerical: `bandBound` is explicit, but not evaluated). -/
  hsum : H + ∑ β, ∑ d ∈ upperDegrees,
      ((upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefS d *
          bandBound targetDecay d β +
        (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefA d *
          bandBound targetDecay d β) +
    ∑ i : Fin 33, (midK2 κ i * (PaperNumbers.chargeC2 i : ℝ) +
      (midK3 κ i + midK4 i * pieceScale i + midK5 i * pieceScale i ^ 2) *
        (PaperNumbers.chargeC3 i : ℝ)) + 11 / 10 ^ 70 ≤ targetLedger.S + targetLedger.A

/-- `SAPartsE2` from `SAPartsE3`, with `hU` from `thm:bmor` (`upperBand_le_bandBound`). -/
noncomputable def SAPartsE3.toE2 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle}
    {A : PaperAnalyticInputs paperCell} {C : ComparisonParts2 hW hMR hFour A}
    (hB : Target.BMOR) (S : SAPartsE3 hW hMR hFour A C) : SAPartsE2 hW hMR hFour A C where
  H := S.H
  hq := S.hq
  Cs := S.Cs
  Ca := S.Ca
  hCs := S.hCs
  hCa := S.hCa
  hR := S.hR
  U β d := bandBound targetDecay d β
  hU β d _ := upperBand_le_bandBound hB hW A β d
  κ := S.κ
  hκ := S.hκ
  hN := S.hN
  hsum := S.hsum

/-- **The combined obligations of the main statement without K2's fields 35, 36, 37, 39, 40.** As
`MainFinalObligationsE2`, with `SA : SAPartsE3`. 5 fields. -/
structure MainFinalObligationsE3 (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) where
  /-- The block data (with the (CP6) gates removed). -/
  Dv : FinalBlockDataE2 hW hMR hFour
  /-- **The histogram certificate** (`cert:record:middle-price`(b)). *Open*. -/
  hHist : HistogramClaim
  /-- `hSA` in reduced form, without the signs and the band-charge field. -/
  SA : SAPartsE3 hW hMR hFour (analyticInputs (Dv.PC.toPC hW hMR hFour) Dv.BA) Dv.Cmp
  /-- The inputs of the joint bound (B10). -/
  Cls : ClassParts2 Dv.toMF2.toK1.data
  /-- The inputs of `SF`, `fix`, `env` (B5, B9). -/
  Sh : SharpParts2U Dv.toMF2.toK1.toJoint

/-- `MainFinalObligationsE2` from `MainFinalObligationsE3` (`thm:bmor` for the band charges). -/
noncomputable def MainFinalObligationsE3.toE2 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} (hB : Target.BMOR) (O : MainFinalObligationsE3 hW hMR hFour) :
    MainFinalObligationsE2 hW hMR hFour where
  Dv := O.Dv
  hHist := O.hHist
  SA := O.SA.toE2 hB
  Cls := O.Cls
  Sh := O.Sh

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵`, without K2's fields 35, 36, 37, 39, 40**
(`thm:main` at `ε = a_T/71`; `main_target_paper_final_E2` through
`MainFinalObligationsE3.toE2`). Hypotheses: H1 `Weil`, H2 `BMOR`, H5
`MovingRoot`, `thm:dl:K` `FourCycle`, H2″ `ThetaSmallRR`, and `O : MainFinalObligationsE3`.
H4 `TwoVariable` was removed on 9 November 2026 as unused. -/
theorem main_target_paper_final_E3 (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligationsE3 hWeil hMovingRoot hFourCycle) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_final_E2 hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR
    (O.toE2 hBMOR)

end Sarkozy.NumericalFields
