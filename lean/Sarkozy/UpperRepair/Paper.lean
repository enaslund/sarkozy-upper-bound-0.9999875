module

public import Sarkozy.UpperRepair.Replacement
public import Sarkozy.MainFinalF1d.All

@[expose] public section

/-!
# `Cmp.blkU` and `SA.hR` from the replacing laws of the upper blocks (`main_target_f1_final3g`)

`paper/sections/26_upper_comparison.tex`, `prop:record:upper`(i) and (ii), `lem:record:domain`.
TC's `MainFinalObligations3f` (`Sarkozy/MainFinalF1d/Main.lean`) still has K2's field 9, `Cmp.blkU`
(B2's `UpperAtomInputs` at every upper block), and, in `SA`, the per-record data `Cs`, `Ca`, the
side condition `hLed : PaperLedgers Cs Ca` and the per-record bounds `hR`. Here all of these come
from one input structure:

* **`UpperRepairData hW A`**: per-band record coefficients `Cs k ρ`, `Ca k ρ` with the paper's state
  ledgers (`hLed`, HS's `PaperLedgers`), and at every upper block `𝔅` of band `k` a replacing law
  for each of its `92` changed records (`BlockRepl`, `ReplRecord`) whose bounds satisfy
  `C^s_ρ ≤ Cs k ρ · r_𝔅` and `C^a_ρ ≤ Ca k ρ · r_𝔅` (`r_𝔅 = U.r`, the block scale `b^{-1/2}`).
  This is
  the paper's (F7)/(F9) at the block with the band coefficients of `lem:record:domain`.
* `specU`, **`UpperRepairData.toCmp`**: TC's `ComparisonPartsTC` (its one field `blkU`), from
  `BlockRepl.toInputs`. Acceptance, uniform one-slot marginals and the brackets are proved
  (`Replacement.lean`).
* **`UpperRepairData.upperRecs`**: `SA.hR` (`UpperRecs`) for `toCmp`, proved, through
  `BlockRepl.price_le`.
* `FinalBlockData3g` (`PC`, `BA`, `Up`, `MR`), `to3e`, `saOf` (TC's `SAPartsTCP`, all seven fields
  from `Up` and `hN`); **`MainFinalObligations3g`** (5 fields: `Dv`, `hN`, `hmid`, `Cls`, `Sh`),
  `to3f`; **`main_target_f1_final3g`**, **`main_goal_f1e`**.

Against `final3f`, `final3g` removes `Cmp.blkU` and, in `SA`, the data `Cs`, `Ca`, `hCs`, `hCa`,
`hLed` and the open field `hR`; it adds `Dv.Up : UpperRepairData`, whose analytic content is the
per-record replacing laws with their constants.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.UpperRepair

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (PaperBlockSpec blockPrimes UpperBlockInputs)
open Sarkozy.ComparisonLawPaper (upperNe)
open Sarkozy.MainFinal (PrimeCertificates BlockAnalytic hCF SpecUpperRec)
open Sarkozy.MainFinal2 (PrimeCertificates2 MidRefinement SharpParts2)
open Sarkozy.EnvPrefix (Uup)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.MainFinalF1 (analyticInputs specF SpecNormBounds Blk bOf UpperSpec SignedSpec
  midAtom bandIdx)
open Sarkozy.MainFinalF1b (ClassPartsE4B)
open Sarkozy.MainFinalF1c (ComparisonPartsTC FinalBlockData3e midOthersK1 tailStTC tailAtTC)
open Sarkozy.MainFinalF1d (SAPartsTCP MainFinalObligations3f main_target_f1_final3f)
open Sarkozy.HsumProof (PaperLedgers paperKappa)

/-! ## The inputs -/

/-- **The replacing laws of the paper's upper blocks with their band coefficients**
(`prop:record:upper`(i), (F7), (F9), `lem:record:domain`; `def:upper-comparison` for the state
ledgers).
* `Cs`, `Ca`: the per-band record coefficients (data), nonnegative, with the paper's state ledgers
  (`hLed`, the band record `upper_dense_refined.json`);
* `rep`: at every upper block, a replacing law of each changed record (`BlockRepl`); *open*
  (analytic: the one-way repairs of (F7) through `OneWayInput.toRepl`, the dense EL laws of
  `prop:dense-comparison`, the LE mixtures of `prop:le-mixture`);
* `hs`, `ha`: the bounds of the replacing laws are at most the band coefficients times the block
  scale; *open* (numerical: the paper's (F7)/(F9) values at the band start, extended to the block by
  `lem:record:domain`). -/
structure UpperRepairData (hW : Target.Weil) (A : PaperAnalyticInputs f1Cell) where
  /-- The per-band symmetric record coefficients. Data. -/
  Cs : Fin 310 → UpIdx → ℝ
  /-- The per-band skew record coefficients. Data. -/
  Ca : Fin 310 → UpIdx → ℝ
  hCs : ∀ k i, 0 ≤ Cs k i
  hCa : ∀ k i, 0 ≤ Ca k i
  /-- The coefficients have the paper's state ledgers (HS's `PaperLedgers`). Finite. -/
  hLed : PaperLedgers Cs Ca
  /-- The replacing laws of the changed records at every upper block. *Open* (analytic). -/
  rep : ∀ (b : Blk) (U : UpperBlockInputs bOf b), specF hW A b = .upper U →
    BlockRepl (blockPrimes bOf b) (upperNe hW U)
  /-- `C^s_ρ ≤ Cs_{k,ρ} r_𝔅` at a block of band `k`. *Open* (numerical). -/
  hs : ∀ b U (h : specF hW A b = .upper U) ρ, upperFate ρ = .changed →
    (rep b U h).coef ρ .sym ≤ Cs (bandIdx b) ρ * U.r
  /-- `C^a_ρ ≤ Ca_{k,ρ} r_𝔅` at a block of band `k`. *Open* (numerical). -/
  ha : ∀ b U (h : specF hW A b = .upper U) ρ, upperFate ρ = .changed →
    (rep b U h).coef ρ .skew ≤ Ca (bandIdx b) ρ * U.r

variable {hW : Target.Weil}

/-- E1's `UpperSpec` of a block from replacing laws at its upper specification. -/
noncomputable def specU {b : Blk} : (S : PaperBlockSpec bOf b) →
    (∀ U, S = .upper U → BlockRepl (blockPrimes bOf b) (upperNe hW U)) → UpperSpec hW S
  | .upper U, f => ULift.up ((f U rfl).toInputs U.W U.hr.le)
  | .middleUniform _, _ => PUnit.unit
  | .middleIndividual _, _ => PUnit.unit
  | .middleCoherent _, _ => PUnit.unit

/-- **The per-record bounds of a block from those of its replacing laws** (`SpecUpperRec`,
`prop:record:upper`(i)). -/
theorem specU_rec (Cs Ca : UpIdx → ℝ) (hCs : ∀ i, 0 ≤ Cs i) (hCa : ∀ i, 0 ≤ Ca i) {b : Blk} :
    ∀ (S : PaperBlockSpec bOf b)
      (f : ∀ U, S = .upper U → BlockRepl (blockPrimes bOf b) (upperNe hW U)),
      (∀ U (h : S = .upper U),
        (∀ ρ, upperFate ρ = .changed → (f U h).coef ρ .sym ≤ Cs ρ * U.r) ∧
        (∀ ρ, upperFate ρ = .changed → (f U h).coef ρ .skew ≤ Ca ρ * U.r)) →
      SpecUpperRec hW (paperIn f1Cell) Cs Ca hCs hCa S
        (SignedSpec.toSpecData hW (paperIn f1Cell) S (UpperSpec.toSigned hW S (specU S f)))
  | .upper U, f, hf =>
    (f U rfl).price_le U.W U.hr.le Cs Ca hCs hCa (hf U rfl).1 (hf U rfl).2
  | .middleUniform _, _, _ => trivial
  | .middleIndividual _, _, _ => trivial
  | .middleCoherent _, _, _ => trivial

namespace UpperRepairData

variable {A : PaperAnalyticInputs f1Cell}

/-- **K2's field 9, `Cmp.blkU`, from the replacing laws**: TC's `ComparisonPartsTC`. -/
noncomputable def toCmp (D : UpperRepairData hW A) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) : ComparisonPartsTC hW hMR hFour A where
  blkU b := specU (specF hW A b) (D.rep b)

theorem bandIdx_eq {b : Blk} {k : Fin 310} (hs : blockSite b = .inr k) : bandIdx b = k := by
  unfold bandIdx
  rw [hs]

/-- **`SA.hR` for `toCmp`, proved** (`prop:record:upper`(i)): the prices of the changed records of
every upper block are at most W8's ledger coefficients with the band coefficients `Cs`, `Ca`. -/
theorem upperRecs (D : UpperRepairData hW A) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) : (D.toCmp hMR hFour).toK1.UpperRecs hW A D.Cs D.Ca D.hCs D.hCa := by
  intro b k hs
  have hk := bandIdx_eq hs
  refine MainFinalF1c.specUpperRec_at hW (paperIn f1Cell) _ _ _ _ (specF hW A b) _
    (specU_rec (D.Cs k) (D.Ca k) (D.hCs k) (D.hCa k) (specF hW A b) (D.rep b) ?_)
  intro U h
  refine ⟨fun ρ hρ => ?_, fun ρ hρ => ?_⟩
  · have := D.hs b U h ρ hρ
    rwa [hk] at this
  · have := D.ha b U h ρ hρ
    rwa [hk] at this

end UpperRepairData

/-! ## The obligations -/

variable {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-- **The block data with the upper blocks from their replacing laws**: TC's `FinalBlockData3e`
with `Cmp` replaced by `Up : UpperRepairData`. 4 fields. -/
structure FinalBlockData3g (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    where
  /-- The per-prime cut certificates (C8, C9). -/
  PC : PrimeCertificates2
  /-- The block-level analytic inputs (B6). -/
  BA : BlockAnalytic
  /-- The replacing laws of the upper blocks with their band coefficients. *Open*. -/
  Up : UpperRepairData hW (analyticInputs (PC.toPC hW hMR hFour) BA)
  /-- The prefix refinement on the middle blocks (K2's `MR`). *Open*. -/
  MR : MidRefinement
    (gramBracketTarget bOf hW (specF hW (analyticInputs (PC.toPC hW hMR hFour) BA))
      (hCF hW hMR hFour) (paperIn f1Cell)
      (paperGi hW (analyticInputs (PC.toPC hW hMR hFour) BA)))
    (Up.toCmp hMR hFour).toK1.CL
    (fun β => midAtom hW (analyticInputs (PC.toPC hW hMR hFour) BA) β = true)

namespace FinalBlockData3g

/-- TC's `FinalBlockData3e` (`Cmp := Up.toCmp`). -/
noncomputable def to3e (D : FinalBlockData3g hW hMR hFour) : FinalBlockData3e hW hMR hFour where
  PC := D.PC
  BA := D.BA
  Cmp := D.Up.toCmp hMR hFour
  MR := D.MR

/-- **TC's `SAPartsTCP`, all seven fields from `Up` and the middle norm bounds `hN`**: `Cs`, `Ca`,
`hCs`, `hCa`, `hLed` from `Up`; `hR` proved (`UpperRepairData.upperRecs`). -/
noncomputable def saOf (D : FinalBlockData3g hW hMR hFour)
    (hN : ∀ b i, blockSite b = .inl i →
      SpecNormBounds hW (paperIn f1Cell) (paperKappa i) (blockLeast b)
        (specF hW (analyticInputs (D.PC.toPC hW hMR hFour) D.BA) b) (D.to3e.Cmp.blk b)) :
    SAPartsTCP hW hMR hFour (analyticInputs (D.to3e.PC.toPC hW hMR hFour) D.to3e.BA)
      D.to3e.Cmp where
  Cs := D.Up.Cs
  Ca := D.Up.Ca
  hCs := D.Up.hCs
  hCa := D.Up.hCa
  hLed := D.Up.hLed
  hR := D.Up.upperRecs hMR hFour
  hN := hN

end FinalBlockData3g

/-- **The obligations with the upper blocks from their replacing laws**: TC's
`MainFinalObligations3f` with `Dv.Cmp` replaced by `Dv.Up`, and `SA` reduced to the middle norm
bounds `hN`. 5 fields. -/
structure MainFinalObligations3g (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) where
  /-- The block data (the tail proved, the upper blocks from `Up`). -/
  Dv : FinalBlockData3g hW hMR hFour
  /-- The twelve norm bounds of every middle block at the paper's constants. *Open* (analytic). -/
  hN : ∀ b i, blockSite b = .inl i →
    SpecNormBounds hW (paperIn f1Cell) (paperKappa i) (blockLeast b)
      (specF hW (analyticInputs (Dv.PC.toPC hW hMR hFour) Dv.BA) b) (Dv.to3e.Cmp.blk b)
  /-- The middle part of `hothT`, with TC's tail bound. *Open*. -/
  hmid : ∀ L, midOthersK1 Dv.to3e.Cmp.toK1 Dv.MR L +
    max (∑ β, Dv.MR.toPrefix.KL β) (∑ β, Dv.MR.toPrefix.KR β) +
    (12 / 2 ^ 534 + Uup Dv.Up.Cs Dv.Up.Ca Dv.Up.hCs Dv.Up.hCa + (tailStTC + tailAtTC)) ≤
      targetLedger.T
  /-- The class inputs (`ClassPartsE4B`). -/
  Cls : ClassPartsE4B (Dv.to3e.toK1 hB (Dv.saOf hN).toTC hmid).data
  /-- The inputs of `SF`, `fix`, `env` (B5, B9). -/
  Sh : SharpParts2 (Dv.to3e.toK1 hB (Dv.saOf hN).toTC hmid).toJoint

/-- TC's obligations `MainFinalObligations3f`. -/
noncomputable def MainFinalObligations3g.to3f {hB : Target.BMOR}
    (O : MainFinalObligations3g hW hMR hFour hB) : MainFinalObligations3f hW hMR hFour hB where
  Dv := O.Dv.to3e
  SA := O.Dv.saOf O.hN
  hmid := O.hmid
  Cls := O.Cls
  Sh := O.Sh

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵`, with the tail repairs, `SA.hsum` and the
upper-block reduction proved** (`thm:main` at `ε = a_T/71`; TC's `main_target_f1_final3f`
with `Cmp.blkU` and `SA.hR` from `UpperRepairData`). Hypotheses as `main_target_f1_final3f`, with
`O : MainFinalObligations3g`. -/
theorem main_target_f1_final3g (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3g hWeil hMovingRoot hFourCycle hBMOR) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_f1_final3f hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O.to3f

/-- **`main_target_f1_final3g` at the owner's goal exponent** `N^{0.99999}`. -/
theorem main_goal_f1e (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3g hWeil hMovingRoot hFourCycle hBMOR) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  Target.sarkozyBound_mono TargetGoal.epsGoal_le_targetSaving
    (main_target_f1_final3g hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O)

end Sarkozy.UpperRepair
