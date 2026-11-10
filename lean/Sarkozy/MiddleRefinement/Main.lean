module

public import Sarkozy.MiddleRefinement.Numbers

@[expose] public section

/-!
# The F1 main statement with `Env.MR` built and `hmid` proved (MRG)

`MainFinalF1d.MainFinalObligations3f` (5 fields: `Dv` = `PC`, `BA`, `Cmp`, **`MR`**; `SA`;
**`hmid`**; `Cls`; `Sh`) with the pair (`MR`, `hmid`) replaced by the block Grams of
`prop:signed-sides`(i),(ii) at the paper's chosen sides:

* **`SignedSideInputs C`**: one field `gram`, the block Grams `SpecSides` of every middle block of
  piece `i` at the sides `paperSide i` (both sides);
* `SignedSideInputs.toPieceSides` (the gates `k_s(i) ≥ 0` are `gates_check`);
* **`dvOf`**: the block data `FinalBlockData3e` with `MR := midRefinementOf` (`Paper.lean`);
* **`hmidOf`**: the field `hmid` of `MainFinalObligations3f`, proved from `SA.hN`, `SA.hLed`,
  `thm:bmor`, `ThetaSmallRR` and the kernel check `hmid_check` (`hmid_of_pieces`,
  `hnum_paper`);
* **`MainFinalObligations3g`** (`PC`, `BA`, `Cmp`, `SG`, `SA`, `Cls`, `Sh`), **`to3f`**,
  **`main_target_f1_final3g`**, **`main_goal_f1e`**.

The structure takes `ThetaSmallRR` as a parameter (N2's charges `f1c2`, `f1c3` enter `hmid`
through it), as `MainFinalObligations3f` takes `BMOR`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.MiddleRefinement

open Sarkozy.PartV Sarkozy.BlockSpecPaper
open Sarkozy.TargetLedger (targetLedger)
open Sarkozy.MainFinal (BlockAnalytic)
open Sarkozy.MainFinal2 (PrimeCertificates2 SharpParts2)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.MainFinalF1 (ComparisonParts bOf specF Blk analyticInputs)
open Sarkozy.MainFinalF1b (ClassPartsE4B)
open Sarkozy.MainFinalF1c (ComparisonPartsTC FinalBlockData3e midOthersK1 tailStTC tailAtTC
  tailTC_eq)
open Sarkozy.MainFinalF1d (SAPartsTCP MainFinalObligations3f main_target_f1_final3f)
open Sarkozy.EnvPrefix (Uup)
open Sarkozy.HsumProof (paperKappa paperKappa_nonneg upperPart_le_budget)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell}

/-- **The block Grams of `prop:signed-sides`(i),(ii) at the paper's chosen sides**: at every
middle block of piece `i`, the signed records of `F₁`, `F₂` (B8's `ofFold` at `t = 127/500`, the
paper's fold components) satisfy the block Grams of `lem:record:asymmetric-gram`(b),(c) with the
sides `d_L = d_R = paperSide i`. 1 field. *Open* (analytic, `prop:signed-sides`). -/
structure SignedSideInputs (C : ComparisonParts hW hMR hFour A) : Prop where
  gram : ∀ b i, blockSite b = .inl i →
    SpecSides hW (paperIn f1Cell) (paperSide i) (paperSide i) (specF hW A b) (C.blk b)

/-- The per-piece sides, with the gates proved (`gates_check`). -/
theorem SignedSideInputs.toPieceSides {C : ComparisonParts hW hMR hFour A}
    (G : SignedSideInputs C) : PieceSides C paperSide paperSide where
  gram := G.gram
  gateL := kPiece_paperSide_nonneg
  gateR := kPiece_paperSide_nonneg

/-- **The block data with `MR` built** (`midRefinementOf` at the paper's sides). -/
noncomputable def dvOf (PC : PrimeCertificates2) (BA : BlockAnalytic)
    (Cmp : ComparisonPartsTC hW hMR hFour (analyticInputs (PC.toPC hW hMR hFour) BA))
    (G : SignedSideInputs Cmp.toK1) : FinalBlockData3e hW hMR hFour where
  PC := PC
  BA := BA
  Cmp := Cmp
  MR := midRefinementOf Cmp.toK1 G.toPieceSides.toSideInputs

/-- **`hmid` of `MainFinalObligations3f`, proved** at `MR = midRefinementOf` (the paper's
signed sides): from `SA.hN` (the norm bounds of the matchings, merges and constants), `SA.hLed`
(`Uup ≤ 0.037`), `thm:bmor`, `ThetaSmallRR`, and the kernel check `hmid_check`. -/
theorem hmidOf (hB : Target.BMOR) (hRR : Target.ThetaSmallRR) (PC : PrimeCertificates2)
    (BA : BlockAnalytic)
    (Cmp : ComparisonPartsTC hW hMR hFour (analyticInputs (PC.toPC hW hMR hFour) BA))
    (G : SignedSideInputs Cmp.toK1)
    (SA : SAPartsTCP hW hMR hFour (analyticInputs (PC.toPC hW hMR hFour) BA) Cmp) :
    ∀ L, midOthersK1 (dvOf PC BA Cmp G).Cmp.toK1 (dvOf PC BA Cmp G).MR L +
      max (∑ β, (dvOf PC BA Cmp G).MR.toPrefix.KL β) (∑ β, (dvOf PC BA Cmp G).MR.toPrefix.KR β) +
      (12 / 2 ^ 534 + Uup SA.Cs SA.Ca SA.hCs SA.hCa + (tailStTC + tailAtTC)) ≤
        targetLedger.T := by
  intro L
  have hU : Uup SA.Cs SA.Ca SA.hCs SA.hCa ≤ HsumProof.upperBudget :=
    upperPart_le_budget SA.Cs SA.Ca SA.hCs SA.hCa SA.hLed
  have hnum := hnum_paper hU
  rw [← tailTC_eq] at hnum
  exact hmid_of_pieces hB hRR Cmp G.toPieceSides paperKappa paperKappa_nonneg SA.hN
    (fun i => MainFinalF1c.KappaLe.refl (paperKappa i)) hnum L

/-- **The obligations of the F1 statement with `MR` built and `hmid` proved**:
`MainFinalObligations3f` with `Dv.MR` and `hmid` replaced by `SG` (the block Grams of
`prop:signed-sides` at the paper's sides). 7 fields: `PC`, `BA`, `Cmp` (the three remaining fields
of `Dv`), `SG`, `SA`, `Cls`, `Sh`. -/
structure MainFinalObligations3g (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR) where
  /-- The per-prime cut certificates (C8, C9). -/
  PC : PrimeCertificates2
  /-- The block-level analytic inputs (B6). -/
  BA : BlockAnalytic
  /-- The (CP4) inputs (upper blocks; the tail proved). -/
  Cmp : ComparisonPartsTC hW hMR hFour (analyticInputs (PC.toPC hW hMR hFour) BA)
  /-- **The block Grams of `prop:signed-sides`(i),(ii)** at the paper's sides. *Open*. -/
  SG : SignedSideInputs Cmp.toK1
  /-- `hSA` in reduced form, at the paper's constants (as in `MainFinalObligations3f`). -/
  SA : SAPartsTCP hW hMR hFour (analyticInputs (PC.toPC hW hMR hFour) BA) Cmp
  /-- The class inputs (as in `MainFinalObligations3f`). -/
  Cls : ClassPartsE4B ((dvOf PC BA Cmp SG).toK1 hB SA.toTC (hmidOf hB hRR PC BA Cmp SG SA)).data
  /-- The inputs of `SF`, `fix`, `env` (as in `MainFinalObligations3f`). -/
  Sh : SharpParts2 ((dvOf PC BA Cmp SG).toK1 hB SA.toTC (hmidOf hB hRR PC BA Cmp SG SA)).toJoint

/-- The obligations of `main_target_f1_final3f`. -/
noncomputable def MainFinalObligations3g.to3f {hB : Target.BMOR} {hRR : Target.ThetaSmallRR}
    (O : MainFinalObligations3g hW hMR hFour hB hRR) : MainFinalObligations3f hW hMR hFour hB where
  Dv := dvOf O.PC O.BA O.Cmp O.SG
  SA := O.SA
  hmid := hmidOf hB hRR O.PC O.BA O.Cmp O.SG O.SA
  Cls := O.Cls
  Sh := O.Sh

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵`, F1 partition, with `Env.MR` built from the
paper's construction and `hmid` proved** (`thm:main` at `ε = a_T/71`; `main_target_f1_final3f`
with `O.to3f`). -/
theorem main_target_f1_final3g (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3g hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_f1_final3f hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O.to3f

/-- **`main_target_f1_final3g` at the owner's goal exponent** `N^{0.99999}`. -/
theorem main_goal_f1e (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3g hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  Target.sarkozyBound_mono TargetGoal.epsGoal_le_targetSaving
    (main_target_f1_final3g hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O)

end Sarkozy.MiddleRefinement
