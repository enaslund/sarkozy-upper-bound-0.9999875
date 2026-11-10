module

public import Sarkozy.SignedDecomp.Main2
public import Sarkozy.NormBoundsPaper3.Main
public import Sarkozy.NormBoundsPaper4.Main
public import Sarkozy.Rebase.FoldsSDB

@[expose] public section

/-!
# The front of the companion statement (FC)

`MainCombined2.FrontK` (5 fields: `PCu`, `BA`, `UpB`, `SD`, `hNr2`) with the three front
reductions of 7 November applied at once:

* **SD2** (`SignedDecomp`): PG's `SD` replaced by `SDB : SignedDecompAnalytic2`
  (`lem:record:conditional-collision`(d) and `prop:signed-bounds`(c) at the paper's constants;
  the component norms and the gates are proved, `SignedDecompAnalytic2.toSD`);
* **NB3** (`NormBoundsPaper3`): NB2's `hNr2` (four middle norm families) replaced by
  `hEs : EOrthPaperInput` (`lem:record:e-orthogonal`(c) at one prime; `Ea` proved, `Es` from it)
  and `hNr4` (the two fold families `Fs`, `Fa`);
* **FD** (`NormBoundsPaper4`): `hEs` proved (`eOrthPaperInput`), and `hNr4` reduced to
  `hFold : SpecFoldInputs` at every middle block (`prop:signed-bounds`(c) at one prime, symmetric
  and skew, and the component norms `c_+ r`; `hNr4_of_inputs`).

UC's `UpB : UpperRecordBlocks` is split into its three fields so that its analytic part (`rep`)
and its finite comparisons (`hs`, `ha`) carry their own kind.

**RG's rebase (7 November 2026): `SDB` loses a half and `hFold` is dropped.** At RB's loosened sides
and `κ` (package R at `a_G = 71/10⁵`):
* `SDB` is now `Rebase.SignedDecompNew` (only `prop:signed-bounds`(c) for the signed record at the
  paper's `e_sg`): the collision bound `lem:record:conditional-collision`(d) is proved at the crude
  `c_col = 73` (FD's `collisionBound_73`), and the gates hold there (`Rebase.gate73_80_check`);
  SD2's former hypothesis implies the new one (`SignedDecompAnalytic2.toNew`);
* FD's `hFold` is **dropped**: the component norms are C38's `comp38_paper`, the one-prime
  statements `sym`, `skew` are FS's (`FoldSymSkew`, from the signed decomposition `SDB`), and both
  side conditions hold on the rebased table (`Rebase.foldSides38_paperKappa`,
  `Rebase.paperKappa_symSkewSides`), so `hNr4 := Rebase.hNr4_paperKappa SDB`: all 24 middle norm
  bounds rest on `SDB`.

* **`CompanionFront`** (6 fields), **`CompanionFront.UpB`**, **`toN3 : FrontN3`** (`SD :=
  SDB.toSD`, RG's map; `hEs := eOrthPaperInput`; `hNr4 := Rebase.hNr4_paperKappa SDB`),
  **`toK := toN3.toK : FrontK`** (NB3's map:
  `hNr2 := hNr2_of_rest4 … (esPrimeInput_of_paper hEs) hNr4`);
* **`CompanionFront.X`**: the joint block data at which the class and sharp groups of
  `main_goal_theta1k` are typed, at the image `F.toK`.

Kinds (`TRUST_MAP.md` §3): **(C)** novel core, **(R)** routine analytic lemma, **(F)** finite
numerical claim; "C + F" is a per-prime analytic statement with a finite anchor part.
-/

namespace Sarkozy.Companion

open Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.UpperComparison Sarkozy.UpperRepair
  Sarkozy.F7Repair
open Sarkozy.BlockSpecPaper Sarkozy.MainCombined Sarkozy.MainCombined2
open Sarkozy.MainFinal (BlockAnalytic)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.MainFinalF1 (analyticInputs specF Blk bOf bandIdx)
open Sarkozy.PartVLaws (blockPrimes UpperBlockInputs)
open Sarkozy.ComparisonLawPaper (upperNe)
open Sarkozy.HsumProof (paperKappa)
open Sarkozy.NormBoundsPaper (hNG)
open Sarkozy.UpperCapsPaper (PrimeCertificatesUC UpperRecordTables UpperRecordBlocks)
open Sarkozy.NormBoundsPaper3 (FrontN3)

/-- **The front of the companion statement**: `FrontK` with SD2's `SDB` (RG: its `new` half) in
place of `SD` and of `hNr2` (NB3's `hEs` proved by FD, `hNr4` from `SDB` by C38, FS and RG), and
`UpB` split into `rep`, `hs`, `ha`. 6 fields, all *open*. The order is forced by the types (`rep` is
typed at `PCu`, `BA`; `SDB` at `rep`, `hs`, `ha`). -/
structure CompanionFront (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
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
  /-- **(C)** SD2/RG: at every prime of every middle block, `prop:signed-bounds`(c) for the centred
  signed record with the paper's `e_sg` (`eq:signed-constants`). The collision bound
  `lem:record:conditional-collision`(d) is no longer an input (RG: `c_col = 73` at the loosened
  sides, `Rebase.SignedDecompNew.toSD`). *Open*. -/
  SDB : Rebase.SignedDecompNew
    ((UpperCapsPaper.UpperRepairDataS.ofSplit UpT ⟨rep, hs, ha⟩).toCmp hMR hFour)

namespace CompanionFront

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {UpT : UpperRecordTables}

/-- UC's `UpB` from the three split fields. -/
def UpB (F : CompanionFront hW hMR hFour UpT) :
    UpperRecordBlocks hW (analyticInputs (F.PCu.toPC2'.toPC hW hMR hFour) F.BA) UpT :=
  ⟨F.rep, F.hs, F.ha⟩

/-- **NB3's `FrontN3` from the companion front** (RG): `UpB := ⟨rep, hs, ha⟩`,
`SD := SDB.toSD` (collision bound at `c_col = 73`, component norms at `80` and the gates proved),
`hEs := eOrthPaperInput` (FD, proved), `hNr4 := Rebase.hNr4_paperKappa SDB` (all four fold bounds
from the signed decomposition: C38's component norms at `38 r`, FS's `sym`, `skew`, the side
conditions on the rebased table proved). -/
noncomputable def toN3 (F : CompanionFront hW hMR hFour UpT) : FrontN3 hW hMR hFour UpT where
  PCu := F.PCu
  BA := F.BA
  UpB := F.UpB
  SD := F.SDB.toSD
  hEs := Sarkozy.NormBoundsPaper4.eOrthPaperInput
  hNr4 := Rebase.hNr4_paperKappa F.SDB

/-- **`MainCombined2.FrontK` from the companion front**, through NB3's map `FrontN3.toK`
(`hNr2 := hNr2_of_rest4 … (esPrimeInput_of_paper hEs) hNr4`). -/
noncomputable def toK (F : CompanionFront hW hMR hFour UpT) : FrontK hW hMR hFour UpT :=
  F.toN3.toK

/-- **The joint block data of the front** (`MainCombined2.MainFinalObligationsKT1`'s `Cls` is
typed at `(F.X hB hRR).data`, its `Sh` at `(F.X hB hRR).toJoint`), at the image `F.toK`. -/
noncomputable abbrev X (F : CompanionFront hW hMR hFour UpT) (hB : Target.BMOR)
    (hRR : Target.ThetaSmallRR) :=
  (dvG F.toK.PC F.toK.BA F.toK.Up F.toK.SGp.toSector.toGram.toSG).to3e.toK1 hB
    ((dvG F.toK.PC F.toK.BA F.toK.Up F.toK.SGp.toSector.toGram.toSG).saOfS
      (hNG F.toK.PC F.toK.BA F.toK.Up F.toK.hNr))
    (hmidG hB hRR F.toK.PC F.toK.BA F.toK.Up F.toK.SGp.toSector.toGram.toSG
      (hNG F.toK.PC F.toK.BA F.toK.Up F.toK.hNr))

end CompanionFront

end Sarkozy.Companion
