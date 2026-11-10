module

public import Sarkozy.MainFinalF1c.All
public import Sarkozy.HsumProof.Upper
public import Sarkozy.HsumProof.PaperKappa

@[expose] public section







open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MainFinalF1d

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.MainFinal (midK2 midK3 midK4 midK5 pieceScale)
open Sarkozy.MainFinal2 (SharpParts2)
open Sarkozy.NumericalFields (bandBound)
open Sarkozy.AnalyticCells (f1Cell f1c2 f1c3)
open Sarkozy.EnvPrefix (Uup)
open Sarkozy.MainFinalF1 (analyticInputs specF SpecNormBounds)
open Sarkozy.MainFinalF1b (ClassPartsE4B)
open Sarkozy.MainFinalF1c (ComparisonPartsTC SAPartsTC FinalBlockData3e MainFinalObligations3e
  midOthersK1 tailStTC tailAtTC tailTC_eq main_target_f1_final3e)
open Sarkozy.HsumProof (PaperLedgers paperKappa paperKappa_nonneg upperBudget
  upperPart middlePart upperPart_le_budget middlePart_paperKappa)

/-- **E3's budget closes at TC's tail bound**: `12/2⁵³⁴ + 0.037 + 0.8349 + 3/2¹⁵¹ ≤ S + A`
(E3's `budget_closes` with `3/2¹⁵¹` for `11/10⁷⁰`; exact rational arithmetic). -/
theorem budget_closes_TC :
    12 / 2 ^ 534 + upperBudget + HsumProof.middleBudget + (tailStTC + tailAtTC) ≤
      targetLedger.S + targetLedger.A := by
  rw [tailTC_eq]
  have hc : (12 : ℝ) / 2 ^ 534 ≤ 12 / 2 ^ 200 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by norm_num))
  have hn : (12 : ℝ) / 2 ^ 200 + upperBudget + HsumProof.middleBudget + 3 / 2 ^ 151 ≤
      targetLedger.S + targetLedger.A := by
    norm_num [upperBudget, HsumProof.middleBudget, targetLedger]
  generalize (12 : ℝ) / 2 ^ 534 = c at hc ⊢
  linarith

/-- **`SAPartsTC.hsum` at the paper's data** (HS's `hsum_paperKappa` at TC's tail bound): for
per-record data with the paper's ledgers and `κ = paperKappa`, the field holds. -/
theorem hsum_paperKappa_TC (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i)
    (hCa : ∀ k i, 0 ≤ Ca k i) (hL : PaperLedgers Cs Ca) :
    12 / 2 ^ 534 + ∑ β, ∑ d ∈ upperDegrees,
        ((upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefS d *
            bandBound targetDecay d β +
          (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefA d *
            bandBound targetDecay d β) +
      ∑ i : Fin 33, (midK2 paperKappa i * f1c2 i +
        (midK3 paperKappa i + midK4 i * pieceScale i + midK5 i * pieceScale i ^ 2) * f1c3 i) +
        (tailStTC + tailAtTC) ≤ targetLedger.S + targetLedger.A := by
  have h := budget_closes_TC
  have hU := upperPart_le_budget Cs Ca hCs hCa hL
  have hM := middlePart_paperKappa
  unfold upperPart at hU
  unfold middlePart at hM
  generalize (12 : ℝ) / 2 ^ 534 = c at h ⊢
  generalize tailStTC + tailAtTC = τ at h ⊢
  linarith

/-- **`SAPartsTC` at the paper's constants, without `hsum`** (HS's `SAParts3P` at
`ComparisonPartsTC`): `κ = paperKappa`, and `hsum` replaced by `hLed`. 7 fields. -/
structure SAPartsTCP (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs f1Cell) (C : ComparisonPartsTC hW hMR hFour A) where
  /-- The per-band record coefficients. Data. -/
  Cs : Fin 310 → UpIdx → ℝ
  Ca : Fin 310 → UpIdx → ℝ
  hCs : ∀ k i, 0 ≤ Cs k i
  hCa : ∀ k i, 0 ≤ Ca k i
  /-- **The data have the paper's state ledgers** (HS). Side condition on the data (finite). -/
  hLed : PaperLedgers Cs Ca
  /-- The upper per-record bounds (`prop:record:upper`(ii)). *Open* (analytic). -/
  hR : C.toK1.UpperRecs hW A Cs Ca hCs hCa
  /-- The twelve norm bounds of every middle block at the paper's constants. *Open* (analytic). -/
  hN : ∀ b i, blockSite b = .inl i →
    SpecNormBounds hW (paperIn f1Cell) (paperKappa i) (blockLeast b) (specF hW A b) (C.blk b)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-- **`SAPartsTC` from `SAPartsTCP`**: `κ = paperKappa`, `hsum` is `hsum_paperKappa_TC`. -/
noncomputable def SAPartsTCP.toTC {A : PaperAnalyticInputs f1Cell}
    {C : ComparisonPartsTC hW hMR hFour A} (S : SAPartsTCP hW hMR hFour A C) :
    SAPartsTC hW hMR hFour A C where
  Cs := S.Cs
  Ca := S.Ca
  hCs := S.hCs
  hCa := S.hCa
  hR := S.hR
  κ := paperKappa
  hκ := paperKappa_nonneg
  hκP i := MainFinalF1c.KappaLe.refl (paperKappa i)
  hN := S.hN
  hsum := hsum_paperKappa_TC S.Cs S.Ca S.hCs S.hCa S.hLed

/-- **The combined obligations with the tail and `hsum` proved**: TC's `MainFinalObligations3e`
with `SA : SAPartsTCP` (no `κ`, `hκ`, `hsum`; `hLed` added). 5 fields. -/
structure MainFinalObligations3f (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) where
  /-- The block data (at `f1Cell`, the tail proved). -/
  Dv : FinalBlockData3e hW hMR hFour
  /-- `hSA` in reduced form, at the paper's constants, without `hsum`. -/
  SA : SAPartsTCP hW hMR hFour (analyticInputs (Dv.PC.toPC hW hMR hFour) Dv.BA) Dv.Cmp
  /-- The middle part of `hothT`, with TC's tail bound. *Open*. -/
  hmid : ∀ L, midOthersK1 Dv.Cmp.toK1 Dv.MR L +
    max (∑ β, Dv.MR.toPrefix.KL β) (∑ β, Dv.MR.toPrefix.KR β) +
    (12 / 2 ^ 534 + Uup SA.Cs SA.Ca SA.hCs SA.hCa + (tailStTC + tailAtTC)) ≤ targetLedger.T
  /-- The class inputs (`ClassPartsE4B`, as in `final3d`, `final3e`). -/
  Cls : ClassPartsE4B (Dv.toK1 hB SA.toTC hmid).data
  /-- The inputs of `SF`, `fix`, `env` (B5, B9). -/
  Sh : SharpParts2 (Dv.toK1 hB SA.toTC hmid).toJoint

/-- The obligations of `main_target_f1_final3e`. -/
noncomputable def MainFinalObligations3f.to3e {hB : Target.BMOR}
    (O : MainFinalObligations3f hW hMR hFour hB) : MainFinalObligations3e hW hMR hFour hB where
  Dv := O.Dv
  SA := O.SA.toTC
  hmid := O.hmid
  Cls := O.Cls
  Sh := O.Sh

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵` at the F1 partition, with the tail repairs
and `SA.hsum` proved** (`thm:main` at `ε = a_T/71`; TC's `main_target_f1_final3e` with HS's
`hsum`). Hypotheses as `MainFinalF1b.main_target_f1_final3d`, with `O : MainFinalObligations3f`. -/
theorem main_target_f1_final3f (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3f hWeil hMovingRoot hFourCycle hBMOR) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_f1_final3e hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O.to3e

/-- **`main_target_f1_final3f` at the owner's goal exponent** `N^{0.99999}`
(`TargetGoal.epsGoal = 10⁻⁵ ≤ epsTarget`, `Target.sarkozyBound_mono`). -/
theorem main_goal_f1d (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3f hWeil hMovingRoot hFourCycle hBMOR) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  Target.sarkozyBound_mono TargetGoal.epsGoal_le_targetSaving
    (main_target_f1_final3f hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O)

end Sarkozy.MainFinalF1d
