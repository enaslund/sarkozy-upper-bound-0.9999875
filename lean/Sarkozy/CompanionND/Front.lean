module

public import Sarkozy.Companion.Front
public import Sarkozy.SignedDecompCrude.Fold

@[expose] public section

/-!
# The companion front without `SDB` (FC, after ND)

RG's `Companion.CompanionFront` (6 fields) has `SDB : Rebase.SignedDecompNew`, the signed
decomposition `prop:signed-bounds`(c) at the paper's `e_sg`. ND proved the signed decomposition
with no hypothesis at a crude `e_sg′ ≤ 21` (`SignedDecompCrude`), with the gates at the rebased
sides kernel-checked (`gate21_check`): `signedDecompInputs_proved C : SignedDecompInputsC C` and
`hNr4_proved C` (the four fold bounds at `paperKappa`). Since `e_sg′` is above the paper's `e_sg`,
it does not give `Rebase.SignedDecompNew`; it enters **below** the companion front, through ND's
`FrontN3ND.toN3` (`SD := signedDecompInputs_proved _`, `hEs := eOrthPaperInput`,
`hNr4 := hNr4_proved _`).

* **`CompanionFrontND`** (5 fields: `PCu`, `BA`, `rep`, `hs`, `ha`; RG's front without `SDB`),
  `UpB`, **`toN3ND : FrontN3ND`**, **`toN3 := toN3ND.toN3`** (ND's map), **`toK := toN3.toK`**
  (NB3's map);
* **`CompanionFrontND.X`**: the joint block data at which the class and sharp groups of
  `main_goal_theta1k` are typed, at the image `F.toK`; `X_CL`, **`prices_eq_bounds`** (RP): its
  middle records are priced at their norm bounds at `κ′ = paperKappa` and the least prime.

Kinds (`TRUST_MAP.md` §3): **(C)** novel core, **(F + R)** finite comparison with a routine step,
**(C + F)** a per-prime analytic statement with a finite anchor part.
-/

namespace Sarkozy.CompanionND

open Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.UpperComparison Sarkozy.UpperRepair
  Sarkozy.F7Repair
open Sarkozy.BlockSpecPaper Sarkozy.MainCombined Sarkozy.MainCombined2
open Sarkozy.MainFinal (BlockAnalytic)
open Sarkozy.MainFinalF1 (analyticInputs specF Blk bOf bandIdx)
open Sarkozy.PartVLaws (blockPrimes UpperBlockInputs)
open Sarkozy.ComparisonLawPaper (upperNe)
open Sarkozy.NormBoundsPaper (hNG)
open Sarkozy.UpperCapsPaper (PrimeCertificatesUC UpperRecordTables UpperRecordBlocks)
open Sarkozy.NormBoundsPaper3 (FrontN3)
open Sarkozy.SignedDecompCrude (FrontN3ND)

/-- **The companion front after ND**: RG's `Companion.CompanionFront` without `SDB` (the signed
decomposition is proved by ND, below the front). 5 fields, all *open*. The order is forced by the
types (`rep` is typed at `PCu`, `BA`; `hs`, `ha` at `rep`). -/
structure CompanionFrontND (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (UpT : UpperRecordTables) : Type 1 where
  /-- **(C + F)** The per-prime certificates (UC's `PrimeCertificatesUC`, 7 fields):
  `rootB` (301 anchors; `lem:record:monotone-endpoint`, `thm:record:direct-star`(b),(c),(e),
  `cert:upper-root-caps`), `rootA` (9 anchors; `lem:upper-completed-root`), `nonroot` (10 anchors;
  `lem:record:domain`(i), (F6)), `h20lo`, `h20hi` (`prop:l20-collisions`(b),
  `prop:l20-rectangular`, `lem:l20-star-mean`, `cert:l20-grid`), `h10`, `h21`
  (`lem:layer12-caps`(b), `thm:spectral-criterion`(a),(d), `cor:spec2:coupling`,
  `cert:layer12-grid`). *Open*. -/
  PCu : PrimeCertificatesUC
  /-- **(C)** The block-level analytic inputs (B6's `BlockAnalytic`, 3 fields): `hUR`
  (`lem:upper-reference-rp`(ii), (V2), (V3)), `hMB` (`lem:front12:reference`(i),
  `lem:old-f-law`(e)), `hIB` (base prices of `def:positive-root`, `prop:root-chamber`,
  `prop:root-layer`). *Open*. -/
  BA : BlockAnalytic
  /-- **(C)** `UpB.rep`: at every upper block, the replacing two-layer laws of the 92 changed
  records with both half marginals `μ^old` (`prop:record:upper`(i); (F7), `prop:le-mixture`,
  `prop:dense-comparison`). *Open* (data with content). -/
  rep : ∀ (b : Blk) (U : UpperBlockInputs bOf b),
    specF hW (analyticInputs (PCu.toPC2'.toPC hW hMR hFour) BA) b = .upper U →
    BlockRepl (blockPrimes bOf b) (upperNe hW U)
  /-- **(F + R)** `UpB.hs`: the symmetric constants of the replacing laws are at most the
  table's `C^s_{k,ρ} r_𝔅` ((F7)/(F9) at the band start, extended by `lem:record:domain`(ii)).
  *Open*. -/
  hs : ∀ b U (h : specF hW (analyticInputs (PCu.toPC2'.toPC hW hMR hFour) BA) b = .upper U) ρ,
    upperFate ρ = .changed → (rep b U h).coef ρ .sym ≤ UpT.Cs (bandIdx b) ρ * U.r
  /-- **(F + R)** `UpB.ha`: the same for the skew constants, `C^a_{k,ρ} r_𝔅`. *Open*. -/
  ha : ∀ b U (h : specF hW (analyticInputs (PCu.toPC2'.toPC hW hMR hFour) BA) b = .upper U) ρ,
    upperFate ρ = .changed → (rep b U h).coef ρ .skew ≤ UpT.Ca (bandIdx b) ρ * U.r

namespace CompanionFrontND

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {UpT : UpperRecordTables}

/-- UC's `UpB` from the three split fields. -/
def UpB (F : CompanionFrontND hW hMR hFour UpT) :
    UpperRecordBlocks hW (analyticInputs (F.PCu.toPC2'.toPC hW hMR hFour) F.BA) UpT :=
  ⟨F.rep, F.hs, F.ha⟩

/-- **ND's `FrontN3ND`** (3 fields `PCu`, `BA`, `UpB`) from the front. -/
def toN3ND (F : CompanionFrontND hW hMR hFour UpT) : FrontN3ND hW hMR hFour UpT where
  PCu := F.PCu
  BA := F.BA
  UpB := F.UpB

/-- **NB3's `FrontN3` from the front, through ND's map `FrontN3ND.toN3`**:
`SD := signedDecompInputs_proved _` (ND: `prop:signed-bounds`(c) at `e_sg′ ≤ 21`, the collision
bound at `c_col = 73`, the component norms and the gates at the rebased sides, all proved),
`hEs := eOrthPaperInput` (FD, proved), `hNr4 := hNr4_proved _` (ND: the four fold bounds at
`paperKappa`, proved). -/
noncomputable def toN3 (F : CompanionFrontND hW hMR hFour UpT) : FrontN3 hW hMR hFour UpT :=
  F.toN3ND.toN3

/-- **`MainCombined2.FrontK` from the front**, through NB3's map `FrontN3.toK`
(`hNr2 := hNr2_of_rest4 … (esPrimeInput_of_paper hEs) hNr4`). -/
noncomputable def toK (F : CompanionFrontND hW hMR hFour UpT) : FrontK hW hMR hFour UpT :=
  F.toN3.toK

/-- **The joint block data of the front** (`MainCombined2.MainFinalObligationsKT1`'s `Cls` is
typed at `(F.X hB hRR).data`, its `Sh` at `(F.X hB hRR).toJoint`), at the image `F.toK`. -/
noncomputable abbrev X (F : CompanionFrontND hW hMR hFour UpT) (hB : Target.BMOR)
    (hRR : Target.ThetaSmallRR) :=
  (dvG F.toK.PC F.toK.BA F.toK.Up F.toK.SGp.toSector.toGram.toSG).to3e.toK1 hB
    ((dvG F.toK.PC F.toK.BA F.toK.Up F.toK.SGp.toSector.toGram.toSG).saOfS
      (hNG F.toK.PC F.toK.BA F.toK.Up F.toK.hNr))
    (hmidG hB hRR F.toK.PC F.toK.BA F.toK.Up F.toK.SGp.toSector.toGram.toSG
      (hNG F.toK.PC F.toK.BA F.toK.Up F.toK.hNr))

/-- The comparison law of the front's block data is that of TC's comparison inputs
`(F.toK.Up.toCmp hMR hFour).toK1`. -/
theorem X_CL (F : CompanionFrontND hW hMR hFour UpT) (hB : Target.BMOR)
    (hRR : Target.ThetaSmallRR) : (F.X hB hRR).data.CL = (F.toK.Up.toCmp hMR hFour).toK1.CL :=
  rfl

theorem prices_eq_bounds (F : CompanionFrontND hW hMR hFour UpT) (b : Blk) (i : Fin 33)
    (hs : BlockSpecPaper.blockSite b = .inl i) :
    MainFinalF1c.SpecPrices hW (BlockSpecPaper.paperIn AnalyticCells.f1Cell)
      (HsumProof.paperKappa i) (BlockSpecPaper.blockLeast b)
      (specF hW (analyticInputs (F.toK.PC.toPC hW hMR hFour) F.toK.BA) b)
      ((F.toK.Up.toCmp hMR hFour).toK1.blk b) :=
  (F.toK.Up.toCmp hMR hFour).toK1_prices (hNG F.toK.PC F.toK.BA F.toK.Up F.toK.hNr) b i hs

end CompanionFrontND

end Sarkozy.CompanionND
