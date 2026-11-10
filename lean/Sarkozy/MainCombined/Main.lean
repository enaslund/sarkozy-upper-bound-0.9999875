module

public import Sarkozy.MiddleRefinement.Main
public import Sarkozy.UpperRepair.Scaled

@[expose] public section

/-!
# The F1 main statement with both reductions: MRG's middle refinement and UR's upper blocks

`main_goal_f1g` combines two reductions of TC/HS's `main_goal_f1d` chain:
* **UR** (`Sarkozy.UpperRepair`, scaled variant `MainFinalObligations3s`): `Cmp.blkU` and `SA.hR`
  replaced by `Up : UpperRepairDataS` (the replacing laws `rep` of the changed upper records and
  the numerical comparisons `hs`, `ha` against coefficients `Cs`, `Ca` whose state ledgers are at
  most `c ≤ 5/2` times the paper's); `SA` is built (`saOfS`, `hsum_scaled`), only `hN` is taken;
* **MRG** (`Sarkozy.MiddleRefinement`): `Dv.MR` built (`midRefinementOf`, the paper's signed
  sides) and `hmid` proved, from the block Grams `SG` of `prop:signed-sides`(i),(ii).

**`hmid` tolerates UR's scaling.** MRG's proof of `hmid` uses the upper coefficients only through
`Uup ≤ 0.0526` (`hnum_paper`). Under `ScaledLedgers c` with `c ≤ 5/2`, UR's
`upperPart_le_scaled` gives `Uup ≤ c · 21/1000 ≤ 0.0525` (**`Uup_le_budget_scaled`**), so the
scaled variant is used. The proof bounds `Uup` by `0.0526` in both variants, so the proved margin
of `hmid` against `T^{ledger}` is the same `6.3·10⁻⁴`.

* **`dvG`**: UR's `FinalBlockData3s` with `MR := midRefinementOf` at the paper's sides;
* **`hmidG`**: the field `hmid` of `MainFinalObligations3s` at `dvG`, proved;
* **`MainFinalObligationsG`** (7 fields: `PC`, `BA`, `Up`, `SG`, `hN`, `Cls`, `Sh`; parameters
  `hW`, `hMR`, `hFour`, `hB` and `ThetaSmallRR`), **`toS`**, **`main_target_f1_final3gc`**,
  **`main_goal_f1g`**.

`SG` stays a separate field of type `SignedSideInputs (Up.toCmp hMR hFour).toK1`, so a proof of
`prop:signed-sides`(i),(ii) (SGA, `lean/Sarkozy/SignedGram/`) plugs in by filling it.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.MainCombined

open Sarkozy.PartV Sarkozy.BlockSpecPaper
open Sarkozy.TargetLedger (targetLedger)
open Sarkozy.MainFinal (BlockAnalytic)
open Sarkozy.MainFinal2 (PrimeCertificates2 SharpParts2)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.MainFinalF1 (bOf specF Blk analyticInputs SpecNormBounds)
open Sarkozy.MainFinalF1b (ClassPartsE4B)
open Sarkozy.MainFinalF1c (midOthersK1 tailStTC tailAtTC tailTC_eq)
open Sarkozy.EnvPrefix (Uup)
open Sarkozy.HsumProof (paperKappa paperKappa_nonneg upperBudget)
open Sarkozy.UpperRepair (UpperRepairDataS FinalBlockData3s MainFinalObligations3s
  upperPart_le_scaled main_target_f1_final3s)
open Sarkozy.MiddleRefinement (SignedSideInputs midRefinementOf hmid_of_pieces hnum_paper)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-- **`Uup ≤ upperBudget = 0.037` under UR's scaled ledgers** (`c ≤ 5/4`, RG at `a_G`; it was
`0.0526` and `5/2` at `a_T`): UR's `upperPart_le_scaled` gives `Uup ≤ c · 21/1000 ≤ 0.02625`. This
is the only way `hmid` sees the upper coefficients. -/
theorem Uup_le_budget_scaled {A : PaperAnalyticInputs f1Cell} (U : UpperRepairDataS hW A) :
    Uup U.Cs U.Ca U.hCs U.hCa ≤ upperBudget := by
  have h := upperPart_le_scaled U.Cs U.Ca U.hCs U.hCa U.hc U.hLed
  have hc' := U.hc'
  refine h.trans ?_
  unfold upperBudget
  nlinarith

/-- **The block data of the combined statement**: UR's `FinalBlockData3s` with
`MR := midRefinementOf` (the paper's signed sides; MRG). -/
noncomputable def dvG (PC : PrimeCertificates2) (BA : BlockAnalytic)
    (Up : UpperRepairDataS hW (analyticInputs (PC.toPC hW hMR hFour) BA))
    (SG : SignedSideInputs (Up.toCmp hMR hFour).toK1) : FinalBlockData3s hW hMR hFour where
  PC := PC
  BA := BA
  Up := Up
  MR := midRefinementOf (Up.toCmp hMR hFour).toK1 SG.toPieceSides.toSideInputs

/-- **`hmid` of `MainFinalObligations3s` at `dvG`, proved** (`prop:record:matching`(ii)): MRG's
`hmid_of_pieces` with the norm bounds `hN`, `thm:bmor`, `ThetaSmallRR`, the kernel check
`hmid_check` and `Uup ≤ 0.0526` (`Uup_le_budget_scaled`). -/
theorem hmidG (hB : Target.BMOR) (hRR : Target.ThetaSmallRR) (PC : PrimeCertificates2)
    (BA : BlockAnalytic) (Up : UpperRepairDataS hW (analyticInputs (PC.toPC hW hMR hFour) BA))
    (SG : SignedSideInputs (Up.toCmp hMR hFour).toK1)
    (hN : ∀ b i, blockSite b = .inl i →
      SpecNormBounds hW (paperIn f1Cell) (paperKappa i) (blockLeast b)
        (specF hW (analyticInputs (PC.toPC hW hMR hFour) BA) b) ((Up.toCmp hMR hFour).blk b)) :
    ∀ L, midOthersK1 (dvG PC BA Up SG).to3e.Cmp.toK1 (dvG PC BA Up SG).MR L +
      max (∑ β, (dvG PC BA Up SG).MR.toPrefix.KL β) (∑ β, (dvG PC BA Up SG).MR.toPrefix.KR β) +
      (12 / 2 ^ 534 + Uup (dvG PC BA Up SG).Up.Cs (dvG PC BA Up SG).Up.Ca
        (dvG PC BA Up SG).Up.hCs (dvG PC BA Up SG).Up.hCa + (tailStTC + tailAtTC)) ≤
        targetLedger.T := by
  intro L
  have hnum := hnum_paper (Uup_le_budget_scaled Up)
  rw [← tailTC_eq] at hnum
  exact hmid_of_pieces hB hRR (Up.toCmp hMR hFour) SG.toPieceSides paperKappa paperKappa_nonneg
    hN (fun i => MainFinalF1c.KappaLe.refl (paperKappa i)) hnum L

/-- **The obligations of the combined F1 statement**: UR's `MainFinalObligations3s` with
`Dv.MR` built and `hmid` proved, the block Grams `SG` of `prop:signed-sides` in their place.
7 fields: `PC`, `BA`, `Up` (UR), `SG` (MRG), `hN`, `Cls`, `Sh`. -/
structure MainFinalObligationsG (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR) where
  /-- The per-prime cut certificates (C8, C9). -/
  PC : PrimeCertificates2
  /-- The block-level analytic inputs (B6). -/
  BA : BlockAnalytic
  /-- The upper blocks (UR's `UpperRepairDataS`: replacing laws `rep`, comparisons `hs`, `ha`,
  coefficients with state ledgers `≤ 5/2` times the paper's). *Open* (`rep`, `hs`, `ha`). -/
  Up : UpperRepairDataS hW (analyticInputs (PC.toPC hW hMR hFour) BA)
  /-- **The block Grams of `prop:signed-sides`(i),(ii)** at the paper's sides (MRG). *Open*. -/
  SG : SignedSideInputs (Up.toCmp hMR hFour).toK1
  /-- The middle norm bounds at the paper's constants (`prop:signed-bounds`(a),(b),(e),
  `lem:record:exact-marginal-e`(ii), `lem:merge-repair`, `lem:record:accepting-c2`). *Open*. -/
  hN : ∀ b i, blockSite b = .inl i →
    SpecNormBounds hW (paperIn f1Cell) (paperKappa i) (blockLeast b)
      (specF hW (analyticInputs (PC.toPC hW hMR hFour) BA) b) ((Up.toCmp hMR hFour).blk b)
  /-- The class inputs (as in `MainFinalObligations3s`). -/
  Cls : ClassPartsE4B ((dvG PC BA Up SG).to3e.toK1 hB ((dvG PC BA Up SG).saOfS hN)
    (hmidG hB hRR PC BA Up SG hN)).data
  /-- The inputs of `SF`, `fix`, `env` (as in `MainFinalObligations3s`). -/
  Sh : SharpParts2 ((dvG PC BA Up SG).to3e.toK1 hB ((dvG PC BA Up SG).saOfS hN)
    (hmidG hB hRR PC BA Up SG hN)).toJoint

/-- UR's `MainFinalObligations3s`. -/
noncomputable def MainFinalObligationsG.toS {hB : Target.BMOR} {hRR : Target.ThetaSmallRR}
    (O : MainFinalObligationsG hW hMR hFour hB hRR) : MainFinalObligations3s hW hMR hFour hB where
  Dv := dvG O.PC O.BA O.Up O.SG
  hN := O.hN
  hmid := hmidG hB hRR O.PC O.BA O.Up O.SG O.hN
  Cls := O.Cls
  Sh := O.Sh

/-- **The combined main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵`** (`thm:main` at `ε = a_T/71`;
UR's `main_target_f1_final3s` with `O.toS`). -/
theorem main_target_f1_final3gc (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligationsG hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_f1_final3s hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O.toS

/-- **The combined main statement at the owner's goal exponent** `N^{0.99999}`: MRG's middle
refinement (`SG` in place of `MR`, `hmid`) and UR's upper blocks (`Up` in place of `blkU`, `hR`,
ledgers scaled by `c ≤ 5/2`). -/
theorem main_goal_f1g (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligationsG hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  Target.sarkozyBound_mono TargetGoal.epsGoal_le_targetSaving
    (main_target_f1_final3gc hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O)

end Sarkozy.MainCombined
