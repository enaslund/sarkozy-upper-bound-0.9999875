module

public import Sarkozy.MainFinal2.Main
public import Sarkozy.CliqueDeletion.MainFinal
public import Sarkozy.SignedEstimates.Final
public import Sarkozy.NumericalFields.BandField

@[expose] public section

/-!
# Third round: (CP4) and `hSA` with the fields closed since K2

K2's `MainFinal2` with the fields closed by C10, E1 and E2 in (CP4) and `hSA`:

* `ComparisonParts3` — K2's `ComparisonParts2` **without `clique`** and **without the middle
  blocks**:
  - the square-clique deletions are C10's `cliqueK1` (`lem:frontier:iidenergy`(ii),
    `lem:frontier:iidlocal`(iv),(v); proved with no hypothesis);
  - the middle-block estimates are E1's `paperMiddleEstimates` (`lem:signed-components`(b),
    `lem:old-f-law`(a); proved from H1, with `η_p = 10/p`, `e_p = e₀(p)`), through E1's
    `UpperSpec.toSigned`; `blkU` asks only for the upper blocks.

  `ComparisonParts3.toK2`.
* `SAParts3` — E2's `SAPartsE3` (K2's `SAParts` with the band charges `hUS`, `hUA` proved from
  `thm:bmor` and the signs `hK` proved from `κ ≥ 0`) **without `H`, `hq`**: the clique bound is
  `H = 12/2^{534}` (`lem:frontier:iidenergy`(iii),(iv); C10's
  `ComparisonInputs.cliquePrice_sum_le`), entered as a number in `hsum`. `SAParts3.toE3`,
  `SAParts3.toK2` (through E2's `toE2`, `toParts2`).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MainFinal3

open Sarkozy.MainFinal Sarkozy.MainFinal2
open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.ComparisonLawPaper (upperBand blockSel)
open Sarkozy.PaperNumbers (paperCell)

/-! ## (CP4): the square-clique atoms proved -/

/-- **The open inputs of (CP4), third round**: K2's `ComparisonParts2` with the square-clique
deletions proved (C10's `cliqueK1`) and the middle-block estimates proved (E1's
`paperMiddleEstimates`). 3 fields: per upper block B2's upper inputs, per tail prime the repairs
and their cap bounds. -/
structure ComparisonParts3 (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs paperCell) where
  /-- Upper blocks only (E1's `UpperSpec`): B2's `UpperAtomInputs` (`prop:record:upper`(i);
  *open*); nothing on a middle block (`MiddleEstimates` proved by E1). -/
  blkU : ∀ b : Blk, SignedEstimates.UpperSpec hW (specF hW A b)
  /-- Tail primes `q ≥ P₄`: a repair of each changed record (`lem:tr:repair`, (F7)). *Open*. -/
  Rp : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q),
    TailPrices.TailRepairs q (ComparisonLawPaper.tailNe hW h4)
  /-- The repair constants against the paper's caps (`cert:tail-caps`,
  `lem:record:domain`(iii)). *Open*. -/
  hcap : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q) t φ (h : upperFate (true, ⟨t, φ⟩) = .changed)
    (e : ChangeType), (Rp q h4 t φ h).C e ≤ TailPrices.tailCap (true, ⟨t, φ⟩) * tailR q

/-- **K2's `ComparisonParts2`**, with `clique := CliqueDeletion.cliqueK1` (C10) and the middle
blocks from `paperMiddleEstimates` (E1's `UpperSpec.toSigned`). -/
noncomputable def ComparisonParts3.toK2 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs paperCell}
    (C : ComparisonParts3 hW hMR hFour A) : ComparisonParts2 hW hMR hFour A where
  clique := CliqueDeletion.cliqueK1 hW hMR hFour A
  blk b := SignedEstimates.UpperSpec.toSigned hW (specF hW A b) (C.blkU b)
  Rp := C.Rp
  hcap := C.hcap

/-- **The clique bound, proved** (`lem:frontier:iidenergy`(iii),(iv) at `a_T`):
`∑_p λ^ex_p(1) q_p^{2a_T} ≤ 12/2^{534}` (C10). -/
theorem ComparisonParts3.cliquePrice_le {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs paperCell}
    (C : ComparisonParts3 hW hMR hFour A) :
    ∑ q, C.toK2.toK1.Ci.cliquePrice q ≤ 12 / 2 ^ 534 := by
  apply CliqueDeletion.ComparisonInputs.cliquePrice_sum_le
  intro q
  show (CliqueDeletion.cliqueK1 hW hMR hFour A q).ω ≤ _
  exact CliqueDeletion.cliqueK1_ω_le hW hMR hFour A q

/-! ## `hSA`: the clique bound entered, E2's reductions -/

/-- **`S + A ≤ S^{ledger} + A^{ledger}` in reduced form, third round**: E2's `SAPartsE3` (K2's
`SAParts` with the band charges `hUS`, `hUA` proved from `thm:bmor` at `𝒰 = bandBound a_T`, and the
signs `hK` proved from the side condition `hκ`) without the clique bound `H`, `hq` (proved:
`H = 12/2^{534}`, `ComparisonParts3.cliquePrice_le`). 9 fields. -/
structure SAParts3 (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs paperCell) (C : ComparisonParts3 hW hMR hFour A) where
  /-- The per-band record coefficients. Data. -/
  Cs : Fin 310 → UpIdx → ℝ
  Ca : Fin 310 → UpIdx → ℝ
  hCs : ∀ k i, 0 ≤ Cs k i
  hCa : ∀ k i, 0 ≤ Ca k i
  /-- The upper per-record bounds (`prop:record:upper`(ii), W8's ledger). *Open* (analytic). -/
  hR : C.toK2.toK1.UpperRecs hW A Cs Ca hCs hCa
  /-- The per-piece constants `(s_F, a_F, ℓ_t, s_E, a_E)`. Data. -/
  κ : Fin 33 → MiddleConsts
  /-- The constants are nonnegative (E2). Side condition on the data `κ`. -/
  hκ : ∀ i, NumericalFields.KappaNonneg (κ i)
  /-- The twelve norm bounds of every middle block (B8's `NormBounds`), for the paper's records
  (`paperComponents` of `paperMiddleEstimates`, `M_c(10/p, e₀(p))`). *Open* (analytic). -/
  hN : ∀ b i, blockSite b = .inl i →
    SpecNormBounds hW (paperIn paperCell) (κ i) (blockLeast b) (specF hW A b) (C.toK2.blk b)
  /-- **The final numerical inequality** of `hSA`, with the clique bound `12/2^{534}`, the band
  charges `bandBound a_T` (E2) and the tail bound `11/10⁷⁰` entered. *Open* (numerical). -/
  hsum : 12 / 2 ^ 534 + ∑ β, ∑ d ∈ upperDegrees,
      ((upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefS d *
          NumericalFields.bandBound targetDecay d β +
        (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefA d *
          NumericalFields.bandBound targetDecay d β) +
    ∑ i : Fin 33, (midK2 κ i * (PaperNumbers.chargeC2 i : ℝ) +
      (midK3 κ i + midK4 i * pieceScale i + midK5 i * pieceScale i ^ 2) *
        (PaperNumbers.chargeC3 i : ℝ)) + 11 / 10 ^ 70 ≤ targetLedger.S + targetLedger.A

/-- **E2's `SAPartsE3`**, with `H := 12/2^{534}` and `hq := ComparisonParts3.cliquePrice_le`. -/
noncomputable def SAParts3.toE3 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs paperCell}
    {C : ComparisonParts3 hW hMR hFour A} (S : SAParts3 hW hMR hFour A C) :
    NumericalFields.SAPartsE3 hW hMR hFour A C.toK2 where
  H := 12 / 2 ^ 534
  hq := C.cliquePrice_le
  Cs := S.Cs
  Ca := S.Ca
  hCs := S.hCs
  hCa := S.hCa
  hR := S.hR
  κ := S.κ
  hκ := S.hκ
  hN := S.hN
  hsum := S.hsum

/-- **K2's `SAParts`** (E2's `SAPartsE3.toE2` with `thm:bmor`, then `SAPartsE2.toParts2`). -/
noncomputable def SAParts3.toK2 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs paperCell}
    {C : ComparisonParts3 hW hMR hFour A} (hB : Target.BMOR) (S : SAParts3 hW hMR hFour A C) :
    SAParts hW hMR hFour A C.toK2 :=
  (S.toE3.toE2 hB).toParts2

end Sarkozy.MainFinal3
