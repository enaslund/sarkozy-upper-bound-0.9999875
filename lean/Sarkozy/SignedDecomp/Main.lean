module

public import Sarkozy.SignedDecomp.Block
public import Sarkozy.MainCombined2.Main
public import Sarkozy.AnalyticCells.F1Cell

@[expose] public section

/-!
# PG's `SD` with the gates proved: `SignedDecompAnalytic.toSD` (SD2)

`paper/sections/24_matching_mean.tex`, `prop:signed-sides`(i);
`paper/sections/21_middle_records.tex`,
`lem:record:conditional-collision`(d), `prop:signed-bounds`(c),(d), `eq:signed-constants`,
`cert:signed-local`.

PG's field `SD : SignedDecompInputsC C` of `MainCombined2.FrontK` asks, at every prime of every
middle block, for the collision bound, the signed decomposition and the component norms **with some
constants**, and for the numerical gates between those constants and the shift
`σ = r_𝔅 d_i/H_𝔅` at MRG's chosen side `d_i` (`paperSide i`).

* **`SpecAnalytic`**, **`SignedDecompAnalytic`** (hypotheses): the three analytic statements at
  **the paper's constants** `c_col`, `e_sg` of `eq:signed-constants`, per prime, and the component
  norms at the crude constant `80` (the paper has `c_+ < 1.74`; `AnalyticAt80`, implied by the
  paper's form `AnalyticAt` through `AnalyticAt.to80`). No numerical condition remains in them.
* **`SignedDecompAnalytic.toSD : SignedDecompInputsC C`**: the gates are proved, uniformly in the
  prime, from the kernel check `gate_check` at the 33 piece starts, the monotonicity of the
  constants (`lem:majorant`), `H_𝔅 ≤ (1 + e₀(X))^{n_i}` with the block budget `∑ log p ≤ 570`
  (`f1Cell_budget`), and the scale `r_𝔅 = b^{-1/2}` (`paperSpec_scale`).
* **`FrontKA`**, **`FrontKA.toFrontK`**: `MainCombined2.FrontK` with `SD` replaced by
  `SDA : SignedDecompAnalytic`.
-/

namespace Sarkozy.SignedDecomp

open Sarkozy.PrimeGram Sarkozy.SignedGram Sarkozy.SignedComponents
open Sarkozy.PartVLaws (PaperBlockSpec blockPrimes)
open Sarkozy.MainFinalF1 (bOf Blk SignedSpec specF analyticInputs)
open Sarkozy.MainFinalF1c (ComparisonPartsTC)
open Sarkozy.BlockSpecPaper
open Sarkozy.AnalyticCells (f1Cell f1Cell_budget)
open Sarkozy.FirstStagePaper (FirstStageInputs)
open Sarkozy.GramBracketPaper (specScale)
open Sarkozy.MiddleRefinement (paperSide)

/-- **`DecompGateAtC` at a middle block of piece `k`** of the F1 data, for any scale `r ≥ 0` with
`r² b_𝔅 = 1`, from the analytic inputs at the paper's constants. -/
theorem blockDecomp {b : Blk} {k : Fin 33} (hb : blockSite b = .inl k)
    (hne : PartV.MiddleNonempty (blockPrimes bOf b)) (C : FoldComponents (blockPrimes bOf b) hne)
    {r : ℝ} (hr : 0 ≤ r) (hs : r ^ 2 * (paperIn f1Cell).bmin b = 1)
    (H : AnalyticAt80 (blockPrimes bOf b) hne C) :
    DecompGateAtC (blockPrimes bOf b) hne C r (paperSide k) := by
  have hXp : ∀ j, XQ k ≤ blockPrimes bOf b j := fun j => (blockPrimes_mem_piece hb j).1
  have hbud : ∑ j, Real.log (blockPrimes bOf b j) ≤ 570 := by
    have h := (f1Cell_budget b).1 k hb
    have e : ((PartV.middleBudget : ℕ) : ℝ) = 570 := by norm_num [PartV.middleBudget]
    rw [e] at h
    exact h
  obtain ⟨hX24, -, -, hE⟩ := table_check k
  have hcard := card_le_of_budget (le_trans (by norm_num) hX24) hXp hbud hE
  have hbm : (paperIn f1Cell).bmin b = (blockLeast b : ℝ) := rfl
  have hXb : (XQ k : ℝ) ≤ (paperIn f1Cell).bmin b := by
    have h := siteStart_le_blockLeast b
    rw [hb] at h
    have h' : XQ k ≤ blockLeast b := h
    rw [hbm]
    exact Nat.cast_le.mpr h'
  have hbp : ∀ j, (paperIn f1Cell).bmin b ≤ (blockPrimes bOf b j : ℝ) := fun j => by
    rw [hbm]
    exact Nat.cast_le.mpr (blockLeast_le b j)
  obtain ⟨hrp, hrX⟩ := scale_bounds k hr hs hbp hXb
  exact decompGateAtC_of_analytic80 _ hne C k hXp hcard hr hrp hrX H

variable (hW : Target.Weil)

/-- **The analytic inputs at a class-three block of the F1 data**, by specification, at the
paper's constants `c_col`, `e_sg` and the crude component constant `80` (`AnalyticAt80`). `True`
on an upper block. -/
def SpecAnalytic {b : Blk} : (S : PaperBlockSpec bOf b) → SignedSpec hW S → Prop
  | .upper _, _ => True
  | .middleUniform M, E => AnalyticAt80 (blockPrimes bOf b) M.hne (paperComponents E.down.toDC)
  | .middleIndividual M, E =>
      AnalyticAt80 (blockPrimes bOf b) M.hne (paperComponents E.down.toDC)
  | .middleCoherent M, E => AnalyticAt80 (blockPrimes bOf b) M.hne (paperComponents E.down.toDC)

/-- **PG's `SpecDecompC` from `SpecAnalytic`** at a middle block of piece `k`, the gates proved. -/
theorem specDecompC_of_analytic {b : Blk} {k : Fin 33} (hb : blockSite b = .inl k) :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) → specScale (paperIn f1Cell) S →
      SpecAnalytic hW S E → SpecDecompC hW (paperIn f1Cell) (paperSide k) S E
  | .upper _, _, _, _ => trivial
  | .middleUniform M, E, hs, H => blockDecomp hb M.hne (paperComponents E.down.toDC) M.hr hs H
  | .middleIndividual M, E, hs, H => blockDecomp hb M.hne (paperComponents E.down.toDC) M.hr hs H
  | .middleCoherent M, E, hs, H => blockDecomp hb M.hne (paperComponents E.down.toDC) M.hr hs H

variable {hW} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell}

/-- **The analytic content of PG's `SD`, at the paper's constants** (*hypothesis*, 1 field): at
every prime of every middle block of the F1 data,
* `lem:record:conditional-collision`(d) with `c_col` of `eq:signed-constants` (`ccolP`);
* `prop:signed-bounds`(c), the centred signed record, with `e_sg` of `eq:signed-constants`
  (`esgP`, `t = 127/500`, `k_col = 9/4`);
* `prop:signed-bounds`(c), the three centred components, with the crude constant `80` in place of
  `c_+ < 1.74` of `eq:signed-constants` (implied by the paper's bound: `AnalyticAt.to80`).
The numerical gates are not part of it (`SignedDecompAnalytic.toSD`). -/
structure SignedDecompAnalytic (C : ComparisonPartsTC hW hMR hFour A) : Prop where
  an : ∀ b i, blockSite b = .inl i → SpecAnalytic hW (specF hW A b) (C.blk b)

/-- **A constructor of PG's `SignedDecompInputsC`** (the field `SD` of `MainCombined2.FrontK`):
the gates of `prop:signed-sides`(i) and `cert:signed-local` are proved at every prime of every
middle block (`gate_check`, kernel), uniformly in the prime. -/
theorem SignedDecompAnalytic.toSD {C : ComparisonPartsTC hW hMR hFour A}
    (H : SignedDecompAnalytic C) : SignedDecompInputsC C :=
  ⟨fun b i hb => specDecompC_of_analytic hW hb (specF hW A b) (C.blk b) (paperSpec_scale hW A b)
    (H.an b i hb)⟩

/-! ## The front of `main_goal_theta1k` with `SD` reduced -/

open Sarkozy.MainCombined2 (FrontK)
open Sarkozy.MainFinal (BlockAnalytic)
open Sarkozy.UpperCapsPaper (PrimeCertificatesUC UpperRecordTables UpperRecordBlocks)
open Sarkozy.NormBoundsPaper2 (SpecNormBoundsRest2)
open Sarkozy.HsumProof (paperKappa)

/-- **`MainCombined2.FrontK` with `SD` replaced by `SDA`**, the analytic statements at the paper's
constants (the gates proved). 5 fields. -/
structure FrontKA (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (UpT : UpperRecordTables) : Type 1 where
  /-- As in `FrontK`. *Open*. -/
  PCu : PrimeCertificatesUC
  /-- As in `FrontK`. *Open*. -/
  BA : BlockAnalytic
  /-- As in `FrontK`. *Open*. -/
  UpB : UpperRecordBlocks hW (analyticInputs (PCu.toPC2'.toPC hW hMR hFour) BA) UpT
  /-- **SD2**: `lem:record:conditional-collision`(d), `prop:signed-bounds`(c) (record and
  components) at the paper's constants, at every prime of every middle block. *Open*
  (analytic). -/
  SDA : SignedDecompAnalytic
    ((UpperCapsPaper.UpperRepairDataS.ofSplit UpT UpB).toCmp hMR hFour)
  /-- As in `FrontK`. *Open*. -/
  hNr2 : ∀ b i, blockSite b = .inl i →
    SpecNormBoundsRest2 hW (paperIn f1Cell) (paperKappa i) (blockLeast b)
      (specF hW (analyticInputs (PCu.toPC2'.toPC hW hMR hFour) BA) b)
      (((UpperCapsPaper.UpperRepairDataS.ofSplit UpT UpB).toCmp hMR hFour).blk b)

/-- `FrontKA` gives `FrontK` (`SD := SDA.toSD`). -/
def FrontKA.toFrontK {UpT : UpperRecordTables} (F : FrontKA hW hMR hFour UpT) :
    FrontK hW hMR hFour UpT where
  PCu := F.PCu
  BA := F.BA
  UpB := F.UpB
  SD := F.SDA.toSD
  hNr2 := F.hNr2

end Sarkozy.SignedDecomp
