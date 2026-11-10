module

public import Sarkozy.SignedDecomp.Main
public import Sarkozy.SignedDecomp.Comp

@[expose] public section

/-!
# PG's `SD` from two analytic statements: the component norms proved (SD2)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(c), Step 1;
`paper/sections/24_matching_mean.tex`, `prop:signed-sides`(i).

* **`comp80_blockComponents`**, **`comp80_paper`**: at every prime of every middle block, every
  centred fold component (B8's `P_{uv}`, any repair constants with the defect bound) has norm at
  most `80 r` (`comp_centred`). This is `prop:signed-bounds`(c), Step 1, with `80` in place of
  `c_+ < 1.74`; the gates hold with `80` (`crude_check`).
* **`AnalyticAt2`** (hypotheses, per prime): `lem:record:conditional-collision`(d) at the paper's
  `c_col` and `prop:signed-bounds`(c) for the signed record at the paper's `e_sg`.
* **`SignedDecompAnalytic2`** (1 field), **`SignedDecompAnalytic2.toSD :
  SignedDecompInputsC C`**; **`FrontKB`**, **`FrontKB.toFrontK`**: `MainCombined2.FrontK` with `SD`
  replaced by these two analytic statements.
-/

open Finset

namespace Sarkozy.SignedDecomp

open Sarkozy.PrimeGram Sarkozy.SignedGram Sarkozy.SignedComponents Sarkozy.Labellings
open Sarkozy.MiddleComparison (signedCoef)
open Sarkozy.PartV (MiddleNonempty)
open Sarkozy.MainFinal2 (tPaper tPaper_nonneg tPaper_le_one)

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]

omit [Fintype ι] [DecidableEq ι] in
/-- **The centred components of a middle block have norm at most `80 r`** (`comp_centred`), at
primes `≥ 2²⁴`, for B8's components with any repair constants satisfying the defect bound. -/
theorem comp80_blockComponents (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i)
    (hne : MiddleNonempty pr) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (M : ι → Fin 3 → ℝ)
    (hM0 : ∀ i c, 0 ≤ M i c)
    (hM : ∀ i c, (repairAt (h3 i) (h19 i) (hne.F2 i) ht0 ht1 c).DefectBound (M i c))
    (h24 : ∀ i, 2 ^ 24 ≤ pr i) (c : Fin 3) (i : ι) :
    CentredNorm (mP hne i) (compP hne (blockComponents h3 h19 hne ht0 ht1 M hM0 hM) c i)
      (80 * rP pr i) := by
  have hmat : compP hne (blockComponents h3 h19 hne ht0 ht1 M hM0 hM) c i =
      fun a b => (repairAt (h3 i) (h19 i) (hne.F2 i) ht0 ht1 c).repair (M i c) (a, b) := by
    funext a b
    change ((compLaw (h3 i) (h19 i) (hne.F2 i) ht0 ht1 (M i) (hM0 i) (hM i) c).map
      (placeEquiv 0)).weight (toY (a, b)) = _
    rw [map_equiv_weight, placeEquiv_zero_symm, lay_toY_zero, lay_toY_one]
    rfl
  rw [hmat]
  have hp : (2 : ℝ) ^ 24 ≤ (Fintype.card (ZMod (pr i)) : ℝ) := by
    rw [ZMod.card]; exact_mod_cast h24 i
  have h := comp_centred (ringChar_zmod_ne_two (h3 i)) (card_zmod_mod (h3 i))
    (card_zmod_ge (h19 i)) (hne.F2 i) ht0 ht1 hp c (hM0 i c) (hM i c)
  rw [ZMod.card] at h
  exact h

end Block

section Paper

open Sarkozy.MainFinalF1 (bOf Blk SignedSpec specF analyticInputs)
open Sarkozy.MainFinalF1c (ComparisonPartsTC)
open Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (PaperBlockSpec blockPrimes)
open Sarkozy.AnalyticCells (f1Cell)

/-- **The centred components of the paper's fold records have norm at most `80 r`**, at every
middle block of the F1 data (primes `≥ Q₃ > 2²⁴`), for any defect constants. -/
theorem comp80_paper {b : Blk} (hne : MiddleNonempty (blockPrimes bOf b))
    (Dc : DefectConstants b hne tPaper_nonneg tPaper_le_one) (c : Fin 3) (i) :
    CentredNorm (mP hne i) (compP hne (paperComponents Dc) c i) (80 * rP (blockPrimes bOf b) i) :=
  comp80_blockComponents (fun j => (Sarkozy.FirstStagePaper.blockPrimes_mod_ge b j).1)
    (blockPrimes_ge19 b) hne tPaper_nonneg tPaper_le_one Dc.M Dc.nonneg Dc.bound
    (fun j => le_trans (by norm_num [PartV.Q3])
      (Sarkozy.FirstStagePaper.blockPrimes_mod_ge b j).2) c i

variable (pr) in
/-- **The two remaining analytic inputs of a middle block** (hypotheses, per prime):
* `col`: `lem:record:conditional-collision`(d), with `c_col = ccolP` of `eq:signed-constants`;
* `new`: `prop:signed-bounds`(c), the centred signed record, with `e_sg = esgP` of
  `eq:signed-constants`. -/
structure AnalyticAt2 {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
    (hne : MiddleNonempty pr) (C : FoldComponents pr hne) : Prop where
  col : ∀ i, CollisionBound (hne.F2 i) (ccolP pr i)
  new : ∀ i, NewDecomp (mP hne i) (∑ c, signedCoef tPaper c • compP hne C c i) tPaper (esgP pr i)

variable (hW : Target.Weil)

/-- **The two analytic inputs at a class-three block of the F1 data**, by specification. `True` on
an upper block. -/
def SpecAnalytic2 {b : Blk} : (S : PaperBlockSpec bOf b) → SignedSpec hW S → Prop
  | .upper _, _ => True
  | .middleUniform M, E => AnalyticAt2 (blockPrimes bOf b) M.hne (paperComponents E.down.toDC)
  | .middleIndividual M, E =>
      AnalyticAt2 (blockPrimes bOf b) M.hne (paperComponents E.down.toDC)
  | .middleCoherent M, E => AnalyticAt2 (blockPrimes bOf b) M.hne (paperComponents E.down.toDC)

/-- `SpecAnalytic2` gives `SpecAnalytic` (the component norms proved, `comp80_paper`). -/
theorem specAnalytic_of_2 {b : Blk} :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) → SpecAnalytic2 hW S E →
      SpecAnalytic hW S E
  | .upper _, _, _ => trivial
  | .middleUniform M, E, H => ⟨H.col, H.new, fun c i => comp80_paper M.hne E.down.toDC c i⟩
  | .middleIndividual M, E, H => ⟨H.col, H.new, fun c i => comp80_paper M.hne E.down.toDC c i⟩
  | .middleCoherent M, E, H => ⟨H.col, H.new, fun c i => comp80_paper M.hne E.down.toDC c i⟩

variable {hW} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell}

/-- **The analytic content of PG's `SD`, reduced to two statements at the paper's constants**
(*hypothesis*, 1 field): at every prime of every middle block of the F1 data,
`lem:record:conditional-collision`(d) with `c_col` (`ccolP`) and `prop:signed-bounds`(c) for the
centred signed record with `e_sg` (`esgP`). The component norms and the gates are proved. -/
structure SignedDecompAnalytic2 (C : ComparisonPartsTC hW hMR hFour A) : Prop where
  an : ∀ b i, blockSite b = .inl i → SpecAnalytic2 hW (specF hW A b) (C.blk b)

theorem SignedDecompAnalytic2.toAnalytic {C : ComparisonPartsTC hW hMR hFour A}
    (H : SignedDecompAnalytic2 C) : SignedDecompAnalytic C :=
  ⟨fun b i hb => specAnalytic_of_2 hW (specF hW A b) (C.blk b) (H.an b i hb)⟩

/-- **A constructor of PG's `SignedDecompInputsC`** from the two analytic statements: the
component norms (`comp80_paper`) and all the gates are proved. -/
theorem SignedDecompAnalytic2.toSD {C : ComparisonPartsTC hW hMR hFour A}
    (H : SignedDecompAnalytic2 C) : SignedDecompInputsC C :=
  H.toAnalytic.toSD

/-! ## The front of `main_goal_theta1k` -/

open Sarkozy.MainCombined2 (FrontK)
open Sarkozy.MainFinal (BlockAnalytic)
open Sarkozy.UpperCapsPaper (PrimeCertificatesUC UpperRecordTables UpperRecordBlocks)
open Sarkozy.NormBoundsPaper2 (SpecNormBoundsRest2)
open Sarkozy.HsumProof (paperKappa)

/-- **`MainCombined2.FrontK` with `SD` replaced by `SDB`**: the collision bound and the signed
decomposition at the paper's constants (component norms and gates proved). 5 fields. -/
structure FrontKB (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (UpT : UpperRecordTables) : Type 1 where
  /-- As in `FrontK`. *Open*. -/
  PCu : PrimeCertificatesUC
  /-- As in `FrontK`. *Open*. -/
  BA : BlockAnalytic
  /-- As in `FrontK`. *Open*. -/
  UpB : UpperRecordBlocks hW (analyticInputs (PCu.toPC2'.toPC hW hMR hFour) BA) UpT
  /-- **SD2**: `lem:record:conditional-collision`(d) and `prop:signed-bounds`(c) (signed record)
  at the paper's constants, at every prime of every middle block. *Open* (analytic). -/
  SDB : SignedDecompAnalytic2
    ((UpperCapsPaper.UpperRepairDataS.ofSplit UpT UpB).toCmp hMR hFour)
  /-- As in `FrontK`. *Open*. -/
  hNr2 : ∀ b i, blockSite b = .inl i →
    SpecNormBoundsRest2 hW (paperIn f1Cell) (paperKappa i) (blockLeast b)
      (specF hW (analyticInputs (PCu.toPC2'.toPC hW hMR hFour) BA) b)
      (((UpperCapsPaper.UpperRepairDataS.ofSplit UpT UpB).toCmp hMR hFour).blk b)

/-- `FrontKB` gives `FrontK` (`SD := SDB.toSD`). -/
def FrontKB.toFrontK {UpT : UpperRecordTables} (F : FrontKB hW hMR hFour UpT) :
    FrontK hW hMR hFour UpT where
  PCu := F.PCu
  BA := F.BA
  UpB := F.UpB
  SD := F.SDB.toSD
  hNr2 := F.hNr2

end Paper

end Sarkozy.SignedDecomp
