module

public import Sarkozy.ThetaOne.Inputs
public import Sarkozy.MainCombined.PrimeNorms

@[expose] public section

/-!
# The main statement on the baseline induction `ϑ = 1`

TH (7 November 2026). The owner switched the endgame from the upgraded induction
`ϑ = 1014587/10⁶` to the baseline `ϑ = 1` (`Sarkozy.densityExponent = 1`).
* The ledger was at `a_T = 212956239/250000000000` (`Θ ≤ 0.984125434`, cap `0.9842`). Since RG's
  rebase (7 November 2026) it is at `a_G = 71/10⁵`, saving `10⁻⁵`, `Θ ≤ 0.718211451` with the
  one-block mean credit `m₁ = 0` (`TargetLedger.theta_lt_cap`, cap `0.72`).
* The endgame's saving is `a_T/71 = TargetLedger.targetSaving ≈ 1.19975·10⁻⁵`. This is just below
  `Target.epsTarget = 1.2·10⁻⁵` and above the owner's goal `TargetGoal.epsGoal = 10⁻⁵`, so the
  conclusion is stated at the goal (`Target.sarkozyBound_mono`).

**`MainFinalObligationsT1`** is `MainCombined.MainFinalObligationsGPN` (the obligations of
`main_goal_f1i`) with the sharp inputs `Sh` on the baseline route (`ThetaOne.SharpPartsBase`):
* removed: `Sh.θ`, `Sh.hθ`, `Sh.hθ'` and **`Sh.fibre`** (`CoupledFibreMoment`,
  `prop:density:production`, upgrade only);
* added: `Sh.SF` (`SharpFirstBaseInputs`: `lem:sharp-first` by `lem:record:folded-energy` with
  whole differences and their full folded laws; open `hfold`, `hrem`);
* reduced: `Sh.fixM`, `Sh.envM` (baseline, DC2 §1) are `FixMeansTheta1`, `EnvMeansTheta1`: B9's
  mean-bound forms with their mean bounds `hmL`, `hmR` (fields 28–31) replaced by what DC3's
  constructors leave at `ϑ = 1` (the scale condition `hzu` and the `r₂` summations `hr2L`,
  `hr2R`); the per-atom moments (`lem:density:packets`), the parity condition, nonempty blocks
  (`paperAtomMap_paperBlockOf_surjective`) and `blockSel ≤ selPre` are proved.

The other six fields (`PC`, `BA`, `Up`, `SGp`, `hNr`, `Cls`) are those of `main_goal_f1i`.

* **`main_goal_theta1`**: `s(N) ≤ C·N^{0.99999}` from Weil, BMOR, MovingRoot, FourCycle,
  ThetaSmallRR and `MainFinalObligationsT1`. H4 `TwoVariable` was removed on 9 November 2026 as
  unused.
-/

namespace Sarkozy.ThetaOne

open Sarkozy.PartV Sarkozy.BlockSpecPaper
open Sarkozy.MainCombined
open Sarkozy.MainFinal (BlockAnalytic)
open Sarkozy.MainFinal2 (PrimeCertificates2)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.MainFinalF1 (analyticInputs specF)
open Sarkozy.MainFinalF1b (ClassPartsE4B)
open Sarkozy.HsumProof (paperKappa)
open Sarkozy.UpperRepair (UpperRepairDataS)
open Sarkozy.SignedGram (SignedPrimeInputs)
open Sarkozy.NormBoundsPaper (SpecNormBoundsRest hNG)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-- **The obligations of the main statement at `ϑ = 1`**: `MainFinalObligationsGPN` with the
sharp inputs on the baseline route. 7 fields. -/
structure MainFinalObligationsT1 (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR) where
  /-- The per-prime cut certificates (C8, C9). -/
  PC : PrimeCertificates2
  /-- The block-level analytic inputs (B6). -/
  BA : BlockAnalytic
  /-- The upper blocks (UR). *Open* (`rep`, `hs`, `ha`). -/
  Up : UpperRepairDataS hW (analyticInputs (PC.toPC hW hMR hFour) BA)
  /-- The prime-level inputs of the block Grams (SGA). *Open*. -/
  SGp : SignedPrimeInputs (Up.toCmp hMR hFour)
  /-- The seven middle norm families not yet proved (HN), at the paper's constants. *Open*. -/
  hNr : ∀ b i, blockSite b = .inl i →
    SpecNormBoundsRest hW (paperIn f1Cell) (paperKappa i) (blockLeast b)
      (specF hW (analyticInputs (PC.toPC hW hMR hFour) BA) b) ((Up.toCmp hMR hFour).blk b)
  /-- The class inputs. -/
  Cls : ClassPartsE4B ((dvG PC BA Up SGp.toSector.toGram.toSG).to3e.toK1 hB
    ((dvG PC BA Up SGp.toSector.toGram.toSG).saOfS (hNG PC BA Up hNr))
    (hmidG hB hRR PC BA Up SGp.toSector.toGram.toSG (hNG PC BA Up hNr))).data
  /-- **The inputs of `SF`, `fix`, `env` on the baseline route** (`ϑ = 1`; no `fibre`). -/
  Sh : SharpPartsBase ((dvG PC BA Up SGp.toSector.toGram.toSG).to3e.toK1 hB
    ((dvG PC BA Up SGp.toSector.toGram.toSG).saOfS (hNG PC BA Up hNr))
    (hmidG hB hRR PC BA Up SGp.toSector.toGram.toSG (hNG PC BA Up hNr))).toJoint

/-- **Every block of the paper's layout is nonempty** (`def:construction`(b)): a prefix atom `{q}`
is the image of `q`, and a block of class-three coordinates is the label of one of them. -/
theorem paperAtomMap_paperBlockOf_surjective (cell : ℕ → ℕ) :
    ∀ β, ∃ i, PartVLaws.paperAtomMap (paperBlockOf cell) i = β := by
  intro β
  rcases β with q | b
  · refine ⟨q.1, ?_⟩
    unfold PartVLaws.paperAtomMap
    simp only [q.2, ↓reduceDIte]
  · obtain ⟨j, hj, hjb⟩ := Finset.mem_image.mp b.mem
    have hj4 : j.1 % 4 ≠ 1 := (Finset.mem_filter.mp hj).2
    refine ⟨j, ?_⟩
    rw [paperAtomMap_class3 hj4]
    congr 1
    exact PaperBlock.ext ((paperBlockOf_val hj4).trans hjb)

/-- `MainFinalObligationsGP`, with `hN := hNG … hNr` (HN) and
`Sh := Sh.toSharpParts2 (paperAtomMap_paperBlockOf_surjective f1Cell)`. -/
noncomputable def MainFinalObligationsT1.toGP {hB : Target.BMOR} {hRR : Target.ThetaSmallRR}
    (O : MainFinalObligationsT1 hW hMR hFour hB hRR) :
    MainFinalObligationsGP hW hMR hFour hB hRR where
  PC := O.PC
  BA := O.BA
  Up := O.Up
  SGp := O.SGp
  hN := hNG O.PC O.BA O.Up O.hNr
  Cls := O.Cls
  Sh := O.Sh.toSharpParts2 (paperAtomMap_paperBlockOf_surjective f1Cell)

/-- **The main statement on the baseline induction `ϑ = 1`, at the owner's goal exponent
`N^{0.99999}`** (`thm:main` at `ε = 10⁻⁵`; `thm:baseline`, i.e. `thm:density:induction` at
`ϑ = 1`, with the four-routes closing at `a_T`). The endgame gives the saving
`a_T/71 ≈ 1.19975·10⁻⁵ ≥ 10⁻⁵`. -/
theorem main_goal_theta1 (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligationsT1 hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_f1h hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O.toGP

end Sarkozy.ThetaOne
