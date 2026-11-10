module

public import Sarkozy.SignedDecomp.Main2
public import Sarkozy.CompSharp.Paper
public import Sarkozy.NormBoundsPaper4.FoldCol

@[expose] public section

/-!
# PG's `SD` at crude constants: `c_col = 73`, `c_+ = 38`, any `e_sg′` (ND)

`paper/sections/21_middle_records.tex`, `lem:record:conditional-collision`(d),
`prop:signed-bounds`(c); `paper/sections/24_matching_mean.tex`, `prop:signed-sides`(i).

SD2's `SignedDecompAnalytic2` asks for the collision bound and the signed decomposition at the
paper's constants `c_col`, `e_sg`, because SD2's gates are tight at the paper's sides
(`gate_tight`). With the sides of the rebased ledger the gates have room (RB), so the
constants may be crude. This file gives the constructor at crude constants:

* `col` is **proved**: FD's `collisionBound_73` (`c_col = 73`, `p ≥ 2²⁴`);
* `comp` is **proved**: C38's `comp38_paper` (`c_+ = 38`);
* `new` (`prop:signed-bounds`(c), the centred signed record) is the **one analytic input**, at a
  constant `e_sg′(p)` given as a function `esgF` of the prime;
* the **gate** is the numerical input `PieceGate esgF 38 k` at each of the 33 pieces: PG's
  `GateAt` with `e_o = eoP` at `c_col = 73`, `e_sg = esgF(p)`, `c_+ = 38`, at the shift
  `r d_k/H_𝔅`, for every set of primes of piece `k` within the block budget (`gateAt_gen` is
  its form at SD2's constants). It is proved at the rebased sides for `e_sg′ ≤ 21` in
  `SignedDecompCrude.Gate` (`gate21_check`, `pieceGate_esgCrude`).

* **`blockDecompCrude`**: PG's `DecompGateAtC` at a middle block from `new` and the gate;
* **`CrudeSD`** (2 fields: `new`, `gate`), **`CrudeSD.toSD :
  SignedDecompInputsC C`**;
* **`FrontKC`**, **`FrontKC.toFrontK`**: `MainCombined2.FrontK` with `SD` replaced by `SDC`.

The side `paperSide k` is MRG's (`MiddleRefinement.paperSide`); the rebase changes its table,
not this file.
-/

open Finset

namespace Sarkozy.SignedDecompCrude

open Sarkozy.PrimeGram Sarkozy.SignedGram Sarkozy.SignedComponents Sarkozy.Labellings
open Sarkozy.SignedDecomp
open Sarkozy.MiddleComparison (signedCoef)
open Sarkozy.PartV (MiddleNonempty)
open Sarkozy.MainFinal2 (tPaper tPaper_nonneg tPaper_le_one)
open Sarkozy.PartVLaws (PaperBlockSpec blockPrimes)
open Sarkozy.MainFinalF1 (bOf Blk SignedSpec specF analyticInputs)
open Sarkozy.MainFinalF1c (ComparisonPartsTC)
open Sarkozy.BlockSpecPaper
open Sarkozy.AnalyticCells (f1Cell f1Cell_budget)
open Sarkozy.GramBracketPaper (specScale)
open Sarkozy.MiddleRefinement (paperSide)

def PieceGate (esgF : ℕ → ℝ) (cB : ℝ) (k : Fin 33) : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime],
    (∀ i, XQ k ≤ pr i) → Fintype.card ι ≤ nX k → ∀ r : ℝ, 0 ≤ r → (∀ i, rP pr i ≤ r) →
      r ≤ (rX k : ℝ) →
      GateAt pr (eoP pr (fun _ => 73)) (fun i => esgF (pr i)) (fun _ => cB)
        (r * paperSide k / Hblock pr)

/-- The crude collision bound at every prime of a middle block of the F1 data
(`collisionBound_73`, FD). -/
theorem col73_paper {b : Blk} (hne : MiddleNonempty (blockPrimes bOf b)) (i) :
    CollisionBound (hne.F2 i) ((fun _ => (73 : ℝ)) i) := by
  have h3 : ∀ j, blockPrimes bOf b j % 4 = 3 :=
    fun j => (Sarkozy.FirstStagePaper.blockPrimes_mod_ge b j).1
  obtain ⟨hR, h3', -⟩ := primeHyps h3 (blockPrimes_ge19 b) i
  have h24 : 2 ^ 24 ≤ Fintype.card (ZMod (blockPrimes bOf b i)) := by
    rw [ZMod.card]; exact Sarkozy.CompSharp.blockPrimes_ge24 b i
  exact Sarkozy.NormBoundsPaper4.collisionBound_73 (hne.F2 i) hR h3' h24

/-- **PG's `DecompGateAtC` at a middle block of piece `k` at crude constants**: `c_col = 73`
(proved), `c_+ = 38` (proved), `e_sg = esgF(p)` (`new`, hypothesis), with the gate
`PieceGate esgF 38 k` (hypothesis), for any scale `r ≥ 0` with `r² b_𝔅 = 1`. -/
theorem blockDecompCrude {b : Blk} {k : Fin 33} (hb : blockSite b = .inl k)
    (hne : MiddleNonempty (blockPrimes bOf b))
    (Dc : DefectConstants b hne tPaper_nonneg tPaper_le_one)
    {r : ℝ} (hr : 0 ≤ r) (hs : r ^ 2 * (paperIn f1Cell).bmin b = 1)
    {esgF : ℕ → ℝ} (hes : ∀ i, 0 ≤ esgF (blockPrimes bOf b i))
    (hnew : ∀ i, NewDecomp (mP hne i)
      (∑ c, signedCoef tPaper c • compP hne (paperComponents Dc) c i) tPaper
      (esgF (blockPrimes bOf b i)))
    (G : PieceGate esgF 38 k) :
    DecompGateAtC (blockPrimes bOf b) hne (paperComponents Dc) r (paperSide k) := by
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
  refine ⟨fun _ => 73, fun i => esgF (blockPrimes bOf b i), fun _ => 38,
    ⟨col73_paper hne, hnew, fun c i => Sarkozy.CompSharp.comp38_paper hne Dc c i,
      fun _ => by norm_num, hes, fun _ => by norm_num⟩,
    G (blockPrimes bOf b) hXp hcard r hr hrp hrX⟩

variable (hW : Target.Weil)

/-- **The crude analytic input at a class-three block of the F1 data**, by specification:
`prop:signed-bounds`(c) for the centred signed record at `e_sg′ = esgF(p)`, at every prime, with
`esgF ≥ 0` there. `True` on an upper block. -/
def SpecNew (esgF : ℕ → ℝ) {b : Blk} : (S : PaperBlockSpec bOf b) → SignedSpec hW S → Prop
  | .upper _, _ => True
  | .middleUniform M, E => (∀ i, 0 ≤ esgF (blockPrimes bOf b i)) ∧ ∀ i, NewDecomp (mP M.hne i)
      (∑ c, signedCoef tPaper c • compP M.hne (paperComponents E.down.toDC) c i) tPaper
      (esgF (blockPrimes bOf b i))
  | .middleIndividual M, E => (∀ i, 0 ≤ esgF (blockPrimes bOf b i)) ∧ ∀ i, NewDecomp (mP M.hne i)
      (∑ c, signedCoef tPaper c • compP M.hne (paperComponents E.down.toDC) c i) tPaper
      (esgF (blockPrimes bOf b i))
  | .middleCoherent M, E => (∀ i, 0 ≤ esgF (blockPrimes bOf b i)) ∧ ∀ i, NewDecomp (mP M.hne i)
      (∑ c, signedCoef tPaper c • compP M.hne (paperComponents E.down.toDC) c i) tPaper
      (esgF (blockPrimes bOf b i))

/-- **PG's `SpecDecompC` at crude constants** at a middle block of piece `k`. -/
theorem specDecompC_crude {esgF : ℕ → ℝ} {b : Blk} {k : Fin 33} (hb : blockSite b = .inl k)
    (G : PieceGate esgF 38 k) :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) → specScale (paperIn f1Cell) S →
      SpecNew hW esgF S E → SpecDecompC hW (paperIn f1Cell) (paperSide k) S E
  | .upper _, _, _, _ => trivial
  | .middleUniform M, E, hs, H =>
      blockDecompCrude hb M.hne E.down.toDC M.hr hs H.1 H.2 G
  | .middleIndividual M, E, hs, H =>
      blockDecompCrude hb M.hne E.down.toDC M.hr hs H.1 H.2 G
  | .middleCoherent M, E, hs, H =>
      blockDecompCrude hb M.hne E.down.toDC M.hr hs H.1 H.2 G

variable {hW} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell}

/-- **PG's `SD` at crude constants** (*hypotheses*, 2 fields), for a function `esgF` of the prime:
* `new`: `prop:signed-bounds`(c), the last claim (the centred signed record is
  `O₀ + L^m_t + R^new`), with `‖R^new‖ ≤ esgF(p) q` in place of the paper's `e_sg q`, at every
  prime of every middle block of the F1 data;
* `gate`: the numerical gate `PieceGate esgF 38 k` at each of the 33 pieces.

`lem:record:conditional-collision`(d) (at `c_col = 73`) and the component norms (at `c_+ = 38`) are
proved (`collisionBound_73`, `comp38_paper`). -/
structure CrudeSD (esgF : ℕ → ℝ) (C : ComparisonPartsTC hW hMR hFour A) : Prop where
  new : ∀ b i, blockSite b = .inl i → SpecNew hW esgF (specF hW A b) (C.blk b)
  gate : ∀ k, PieceGate esgF 38 k

/-- **A constructor of PG's `SignedDecompInputsC` at crude constants** (`c_col = 73`,
`c_+ = 38`, `e_sg′ = esgF`). -/
theorem CrudeSD.toSD {esgF : ℕ → ℝ} {C : ComparisonPartsTC hW hMR hFour A}
    (H : CrudeSD esgF C) : SignedDecompInputsC C :=
  ⟨fun b i hb => specDecompC_crude hW hb (H.gate i) (specF hW A b) (C.blk b)
    (paperSpec_scale hW A b) (H.new b i hb)⟩

/-! ## The front of `main_goal_theta1k` -/

open Sarkozy.MainCombined2 (FrontK)
open Sarkozy.MainFinal (BlockAnalytic)
open Sarkozy.UpperCapsPaper (PrimeCertificatesUC UpperRecordTables UpperRecordBlocks)
open Sarkozy.NormBoundsPaper2 (SpecNormBoundsRest2)
open Sarkozy.HsumProof (paperKappa)

/-- **`MainCombined2.FrontK` with `SD` replaced by `SDC`** (crude constants: `c_col = 73` and
`c_+ = 38` proved, `e_sg′ = esgF` and the gates as inputs). 5 fields and the parameter `esgF`. -/
structure FrontKC (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (UpT : UpperRecordTables) (esgF : ℕ → ℝ) : Type 1 where
  /-- As in `FrontK`. *Open*. -/
  PCu : PrimeCertificatesUC
  /-- As in `FrontK`. *Open*. -/
  BA : BlockAnalytic
  /-- As in `FrontK`. *Open*. -/
  UpB : UpperRecordBlocks hW (analyticInputs (PCu.toPC2'.toPC hW hMR hFour) BA) UpT
  /-- **ND**: `prop:signed-bounds`(c) (signed record) at `e_sg′ = esgF` and the gates at the
  crude constants. *Open*. -/
  SDC : CrudeSD esgF
    ((UpperCapsPaper.UpperRepairDataS.ofSplit UpT UpB).toCmp hMR hFour)
  /-- As in `FrontK`. *Open*. -/
  hNr2 : ∀ b i, blockSite b = .inl i →
    SpecNormBoundsRest2 hW (paperIn f1Cell) (paperKappa i) (blockLeast b)
      (specF hW (analyticInputs (PCu.toPC2'.toPC hW hMR hFour) BA) b)
      (((UpperCapsPaper.UpperRepairDataS.ofSplit UpT UpB).toCmp hMR hFour).blk b)

/-- `FrontKC` gives `FrontK` (`SD := SDC.toSD`). -/
def FrontKC.toFrontK {UpT : UpperRecordTables} {esgF : ℕ → ℝ} (F : FrontKC hW hMR hFour UpT esgF) :
    FrontK hW hMR hFour UpT where
  PCu := F.PCu
  BA := F.BA
  UpB := F.UpB
  SD := F.SDC.toSD
  hNr2 := F.hNr2

end Sarkozy.SignedDecompCrude
