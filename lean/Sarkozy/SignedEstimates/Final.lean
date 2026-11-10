module

public import Sarkozy.SignedEstimates.Paper
public import Sarkozy.MainFinal2.Main

@[expose] public section






open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.SignedEstimates

open Sarkozy.MainFinal Sarkozy.MainFinal2
open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (PaperBlockSpec v2Reference paperAtomMap PrefixCoord blockPrimes)
open Sarkozy.ComparisonLawPaper (DeletionInputs paperPrefixAccepted tailNe UpperAtomInputs upperNe)
open Sarkozy.PaperNumbers (paperCell HistogramClaim)

/-- **The upper-block part of K2's `SignedSpec`**: B2's `UpperAtomInputs` on an upper block
(`prop:record:upper`(i), open), nothing on a middle block. -/
def UpperSpec (hW : Target.Weil) {b : Blk} : PaperBlockSpec bOf b → Type 1
  | .upper U => ULift (UpperAtomInputs (blockPrimes bOf b) (upperNe hW U) U.W U.r)
  | .middleUniform _ => PUnit
  | .middleIndividual _ => PUnit
  | .middleCoherent _ => PUnit

/-- **K2's `SignedSpec` with the middle blocks proved** (`paperMiddleEstimates`:
`lem:signed-components`(b), `lem:old-f-law`(a) from H1, `η_p = 10/p`, `e_p = e₀(p)`). -/
noncomputable def UpperSpec.toSigned (hW : Target.Weil) {b : Blk} :
    (S : PaperBlockSpec bOf b) → UpperSpec hW S → SignedSpec hW S
  | .upper _, U => U
  | .middleUniform M, _ => ULift.up (paperMiddleEstimates hW b M.hne)
  | .middleIndividual M, _ => ULift.up (paperMiddleEstimates hW b M.hne)
  | .middleCoherent M, _ => ULift.up (paperMiddleEstimates hW b M.hne)

/-- **The open inputs of (CP4) after E1**: K2's `ComparisonParts2` with the middle-block field
removed (`blkU` asks only for the upper blocks). 4 fields. -/
structure ComparisonParts3 (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs paperCell) where
  /-- Square-clique atoms (as in `ComparisonParts2.clique`). *Open*. -/
  clique : ∀ q : PrefixCoord, DeletionInputs
    ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μ₀ (.inl q))
    (paperPrefixAccepted bOf (.inl q)) MainAnchor.paperQueries
  /-- Upper blocks only: B2's `UpperAtomInputs` (`prop:record:upper`(i)). *Open*. -/
  blkU : ∀ b : Blk, UpperSpec hW (specF hW A b)
  /-- Tail repairs (as in `ComparisonParts2.Rp`). *Open*. -/
  Rp : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailPrices.TailRepairs q (tailNe hW h4)
  /-- The repair constants against the caps (as in `ComparisonParts2.hcap`). *Open*. -/
  hcap : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q) t φ (h : upperFate (true, ⟨t, φ⟩) = .changed)
    (e : ChangeType), (Rp q h4 t φ h).C e ≤ TailPrices.tailCap (true, ⟨t, φ⟩) * tailR q

/-- K2's `ComparisonParts2`, the middle blocks from `paperMiddleEstimates`. -/
noncomputable def ComparisonParts3.toCP2 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs paperCell}
    (C : ComparisonParts3 hW hMR hFour A) : ComparisonParts2 hW hMR hFour A where
  clique := C.clique
  blk b := UpperSpec.toSigned hW (specF hW A b) (C.blkU b)
  Rp := C.Rp
  hcap := C.hcap

/-- **The block data after E1** (K2's `FinalBlockData2` with `ComparisonParts3`). -/
structure FinalBlockData3 (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    where
  /-- The per-prime cut certificates (C8). -/
  PC : PrimeCertificates2
  /-- The block-level analytic inputs (B6). -/
  BA : BlockAnalytic
  /-- The (CP4) inputs, the middle blocks removed. -/
  Cmp : ComparisonParts3 hW hMR hFour (analyticInputs (PC.toPC hW hMR hFour) BA)
  /-- The (CP6), (CP8)(c) inputs (B3, K1). -/
  Env : EnvelopeParts2 hW hMR hFour (analyticInputs (PC.toPC hW hMR hFour) BA) Cmp.toCP2

/-- K2's `FinalBlockData2`. -/
noncomputable def FinalBlockData3.toFBD2 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} (D : FinalBlockData3 hW hMR hFour) : FinalBlockData2 hW hMR hFour
    where
  PC := D.PC
  BA := D.BA
  Cmp := D.Cmp.toCP2
  Env := D.Env

/-- **The combined obligations after E1**: K2's `MainFinalObligations2` without field 11
(`MiddleEstimates`). 5 fields, as in K2, with `Dv : FinalBlockData3`. -/
structure MainFinalObligations3 (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) where
  /-- The block data, the middle estimates removed. -/
  Dv : FinalBlockData3 hW hMR hFour
  /-- The histogram certificate (`cert:record:middle-price`(b)). *Open*. -/
  hHist : HistogramClaim
  /-- `hSA` in reduced form, for the paper's records (`M_c(10/p, e₀(p))`). -/
  SA : SAParts hW hMR hFour (analyticInputs (Dv.PC.toPC hW hMR hFour) Dv.BA) Dv.toFBD2.Cmp
  /-- The inputs of the joint bound (B10). -/
  Cls : ClassParts2 Dv.toFBD2.toK1.data
  /-- The inputs of `SF`, `fix`, `env` (B5, B9). -/
  Sh : SharpParts2U Dv.toFBD2.toK1.toJoint

/-- **K2's obligations from E1's** (field 11 filled by `paperMiddleEstimates`). -/
noncomputable def MainFinalObligations3.toMFO2 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} (O : MainFinalObligations3 hW hMR hFour) :
    MainFinalObligations2 hW hMR hFour where
  Dv := O.Dv.toFBD2
  hHist := O.hHist
  SA := O.SA
  Cls := O.Cls
  Sh := O.Sh

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵`, with field 11 proved** (`thm:main` at
`ε = 3/250000`; `lem:signed-components`(b) and `lem:old-f-law`(a) proved from H1). The hypotheses
are those of `main_target_paper_final2`, with `MainFinalObligations3` in place of
`MainFinalObligations2`. -/
theorem main_target_paper_final3 (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3 hWeil hMovingRoot hFourCycle) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_final2 hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O.toMFO2

end Sarkozy.SignedEstimates
