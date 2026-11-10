module

public import Sarkozy.UpperCapsPaper.RouteB
public import Sarkozy.UpperCapsPaper.Records
public import Sarkozy.UpperCapsPaper.TablesProof
public import Sarkozy.MainCombined.PrimeNorms





@[expose] public section

namespace Sarkozy.UpperCapsPaper

open Sarkozy.PartV Sarkozy.BlockSpecPaper Sarkozy.MainCombined
open Sarkozy.MainFinal (BlockAnalytic)
open Sarkozy.MainFinal2 (PrimeCertificates2 SharpParts2U L20RectData MidRplusData)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.MainFinalF1 (analyticInputs specF)
open Sarkozy.MainFinalF1b (ClassPartsE4B)
open Sarkozy.HsumProof (paperKappa)
open Sarkozy.UpperRepair (UpperRepairDataS)
open Sarkozy.SignedGram (SignedPrimeInputs)
open Sarkozy.NormBoundsPaper (SpecNormBoundsRest hNG)

/-- **The per-prime certificates with `hUC` split** (`PrimeCertificates2` with the upper root caps
replaced by the anchor certificates of the paper's tables; the four middle fields unchanged).
*Hypotheses* (analytic). -/
structure PrimeCertificatesUC : Prop where
  /-- LL20 below `2⁵²`: 301 anchor certificates (`lem:record:monotone-endpoint`). *Open*. -/
  rootB : RootAnchorsB
  /-- LL20 from `2⁵²`: 9 anchor certificates, the completed root (`lem:upper-completed-root`).
  *Open*. -/
  rootA : RootAnchorsA
  /-- The five nonroot cuts: 10 anchor certificates (`lem:record:domain`(i), (F6)). *Open*. -/
  nonroot : NonrootAnchors
  /-- As `PrimeCertificates2.h20lo`. *Open*. -/
  h20lo : ∀ i, allpIndividual i = none → pieceStart i < 2 ^ 40 → MiddleCertificates.L20Inputs i
  /-- As `PrimeCertificates2.h20hi`. *Open*. -/
  h20hi : ∀ i, allpIndividual i = none → 2 ^ 40 ≤ pieceStart i → ∀ (p : ℕ) [Fact p.Prime],
    p % 4 = 3 → pieceStart i ≤ p → p < pieceStop i → Nonempty (L20RectData i p)
  /-- As `PrimeCertificates2.h10`. *Open*. -/
  h10 : ∀ i (p : ℕ) [Fact p.Prime], p % 4 = 3 → pieceStart i ≤ p → p < pieceStop i →
    Nonempty (MidRplusData .l10 i p)
  /-- As `PrimeCertificates2.h21`. *Open*. -/
  h21 : ∀ i, allpIndividual i = none → ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 →
    pieceStart i ≤ p → p < pieceStop i → Nonempty (MidRplusData .l21 i p)

/-- **`PrimeCertificatesUC` from one package per anchor**: 301 Route B packages (LL20 below
`2⁵²`), 9 Route A packages (the completed root from `2⁵²`) and 10 Route A packages (the nonroot
cuts at `2⁴⁷`, `2⁴⁸`), with the four middle fields. -/
theorem PrimeCertificatesUC.ofPackages
    (PB : ∀ k : Fin 310, k.val < 301 → RouteBPackage (capRow k .LL20).anchor (capRow k .LL20).g
      (capRow k .LL20).B)
    (PA : ∀ k : Fin 310, 301 ≤ k.val → RouteAPackage .L (ZMod 2) (capRow k .LL20).anchor
      (capRow k .LL20).g (capRow k .LL20).B)
    (P47 : ∀ c : Cap, c ≠ .LL20 → RouteAPackage c.field c.Lam (nonroot47 c).anchor
      (nonroot47 c).g (nonroot47 c).B)
    (P48 : ∀ c : Cap, c ≠ .LL20 → RouteAPackage c.field c.Lam (nonroot48 c).anchor
      (nonroot48 c).g (nonroot48 c).B)
    (h20lo : ∀ i, allpIndividual i = none → pieceStart i < 2 ^ 40 → MiddleCertificates.L20Inputs i)
    (h20hi : ∀ i, allpIndividual i = none → 2 ^ 40 ≤ pieceStart i → ∀ (p : ℕ) [Fact p.Prime],
      p % 4 = 3 → pieceStart i ≤ p → p < pieceStop i → Nonempty (L20RectData i p))
    (h10 : ∀ i (p : ℕ) [Fact p.Prime], p % 4 = 3 → pieceStart i ≤ p → p < pieceStop i →
      Nonempty (MidRplusData .l10 i p))
    (h21 : ∀ i, allpIndividual i = none → ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 →
      pieceStart i ≤ p → p < pieceStop i → Nonempty (MidRplusData .l21 i p)) :
    PrimeCertificatesUC :=
  ⟨rootAnchorsB_of_packages PB, rootAnchorsA_of_packages PA, nonrootAnchors_of_packages P47 P48,
    h20lo, h20hi, h10, h21⟩

/-- **`PrimeCertificates2` from the split**: `hUC := upperRootCaps_of_tables`. -/
theorem PrimeCertificatesUC.toPC2 (hT : UpperCapTables) (P : PrimeCertificatesUC) :
    PrimeCertificates2 :=
  ⟨upperRootCaps_of_tables hT P.rootB P.rootA P.nonroot, P.h20lo, P.h20hi, P.h10, P.h21⟩

/-- **The obligations of `main_goal_f1i` with `PC.hUC` split** (`MainFinalObligationsGPN` with
`PC := PCu.toPC2 hT`). -/
structure MainFinalObligationsUC (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (hT : UpperCapTables) (UpT : UpperRecordTables) where
  /-- The per-prime certificates, with the upper anchor certificates. -/
  PCu : PrimeCertificatesUC
  /-- The block-level analytic inputs (B6). -/
  BA : BlockAnalytic
  /-- The upper blocks (UR), analytic part: the replacing laws with constants at most the table
  `UpT` times `r_𝔅` (`lem:record:domain`(ii)). *Open*. -/
  UpB : UpperRecordBlocks hW (analyticInputs ((PCu.toPC2 hT).toPC hW hMR hFour) BA) UpT
  /-- The prime-level inputs of the block Grams (SGA). *Open*. -/
  SGp : SignedPrimeInputs ((UpperRepairDataS.ofSplit UpT UpB).toCmp hMR hFour)
  /-- The seven middle norm families not yet proved (HN). *Open*. -/
  hNr : ∀ b i, blockSite b = .inl i →
    SpecNormBoundsRest hW (paperIn f1Cell) (paperKappa i) (blockLeast b)
      (specF hW (analyticInputs ((PCu.toPC2 hT).toPC hW hMR hFour) BA) b)
      (((UpperRepairDataS.ofSplit UpT UpB).toCmp hMR hFour).blk b)
  /-- The class inputs. -/
  Cls : ClassPartsE4B ((dvG (PCu.toPC2 hT) BA (UpperRepairDataS.ofSplit UpT UpB)
      SGp.toSector.toGram.toSG).to3e.toK1 hB
    ((dvG (PCu.toPC2 hT) BA (UpperRepairDataS.ofSplit UpT UpB) SGp.toSector.toGram.toSG).saOfS
      (hNG (PCu.toPC2 hT) BA (UpperRepairDataS.ofSplit UpT UpB) hNr))
    (hmidG hB hRR (PCu.toPC2 hT) BA (UpperRepairDataS.ofSplit UpT UpB) SGp.toSector.toGram.toSG
      (hNG (PCu.toPC2 hT) BA (UpperRepairDataS.ofSplit UpT UpB) hNr))).data
  /-- The inputs of `SF`, `fix`, `env`. -/
  Sh : SharpParts2U ((dvG (PCu.toPC2 hT) BA (UpperRepairDataS.ofSplit UpT UpB)
      SGp.toSector.toGram.toSG).to3e.toK1 hB
    ((dvG (PCu.toPC2 hT) BA (UpperRepairDataS.ofSplit UpT UpB) SGp.toSector.toGram.toSG).saOfS
      (hNG (PCu.toPC2 hT) BA (UpperRepairDataS.ofSplit UpT UpB) hNr))
    (hmidG hB hRR (PCu.toPC2 hT) BA (UpperRepairDataS.ofSplit UpT UpB) SGp.toSector.toGram.toSG
      (hNG (PCu.toPC2 hT) BA (UpperRepairDataS.ofSplit UpT UpB) hNr))).toJoint

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-- `MainFinalObligationsGPN` with `PC := PCu.toPC2 hT` and `Up := ofSplit UpT UpB`. -/
noncomputable def MainFinalObligationsUC.toGPN {hB : Target.BMOR} {hRR : Target.ThetaSmallRR}
    {hT : UpperCapTables} {UpT : UpperRecordTables}
    (O : MainFinalObligationsUC hW hMR hFour hB hRR hT UpT) :
    MainFinalObligationsGPN hW hMR hFour hB hRR where
  PC := O.PCu.toPC2 hT
  BA := O.BA
  Up := UpperRepairDataS.ofSplit UpT O.UpB
  SGp := O.SGp
  hNr := O.hNr
  Cls := O.Cls
  Sh := O.Sh

/-- **The combined main statement with the upper root caps from the paper's tables**
(`thm:main` at the goal exponent `N^{0.99999}`): `main_goal_f1i` with `PC.hUC` replaced by the
finite hypothesis `UpperCapTables` (`cert:upper-root-caps`, `cert:upper-completed-root`,
`cert:upper-band-inputs`(a)) and the anchor certificates of `PrimeCertificatesUC`, and with `Up`
split into the finite record table `UpT` (`UpperRecordTables`) and the block statements `UpB`. -/
theorem main_goal_f1i_uc (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (hTables : UpperCapTables) (UpT : UpperRecordTables)
    (O : MainFinalObligationsUC hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR hTables UpT) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_f1i hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O.toGPN

/-- **The main statement with the cap tables proved**: `main_goal_f1i_uc` at
`hTables := upperCapTables_holds` (`TablesProof.lean`). The upper root caps then rest only on the
anchor certificates of `PrimeCertificatesUC` (`RootAnchorsB`, `RootAnchorsA`, `NonrootAnchors`),
and `Up` on the record table `UpT` and the block statements `O.UpB`. -/
theorem main_goal_f1i_ucp (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables)
    (O : MainFinalObligationsUC hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR
      upperCapTables_holds UpT) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_f1i_uc hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR
    upperCapTables_holds UpT O

/-- **`PC` from the anchor certificates alone** (the cap tables proved). -/
theorem PrimeCertificatesUC.toPC2' (P : PrimeCertificatesUC) : PrimeCertificates2 :=
  P.toPC2 upperCapTables_holds

end Sarkozy.UpperCapsPaper
