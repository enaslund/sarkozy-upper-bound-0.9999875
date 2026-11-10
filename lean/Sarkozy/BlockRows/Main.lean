module

public import Sarkozy.BlockRows.MiddleCert
public import Sarkozy.BlockRows.Upper
public import Sarkozy.BlockInputs.MainEC

@[expose] public section

/-!
# The rebased companion statement with the reference rows from per-prime certificates
(`main_goal_rebased_rw`)

RW, 8 November 2026. BA-EC's `CompanionObligationsBAEC` (`BlockInputs/MainEC.lean`) with the two
block-level row fields of `BI : BlockInputsBA` (kind C) replaced by per-prime certificates
(kind C + F), from which the rows are proved:

* the upper rows `rowsU` (`lem:upper-reference-rp`(ii), (V2)) by `rowU : ∀ k, UpperRowCert k`
  (`Upper.lean`, `upperBandRowsV2_of_cert`: (F3), (F5)(a), `cor:joint-completion-blocks`);
* the middle rows `rowsM` (`lem:front12:reference`(i)) by `rowM : ∀ i, MiddleRowCert i`
  (`MiddleCert.lean`, `middleBlockRows_of_cert`: "One prime", `lem:record:class-three`(iii),
  `cor:influence-schur`; the equality of the middle laws, (ii), is proved in `MiddleLaw.lean`).

* `BlockInputsRW` (6 fields, all C + F: `rowU`, `layerU`, `obsU`, `rowM`, `foldM`, `rootI`),
  **`BlockInputsRW.toBA`**; `BlockCertsRW` (the two row families), `BlockInputsRW.ofBA`
  (non-vacuity: BA's block inputs without the rows, and the row certificates);
* `CompanionFrontRW` (BA's front with `BI : BlockInputsRW`), `toBA`, `ofBA`, `toBA_ofBA` (`rfl`);
* **`CompanionObligationsRW`**: `CompanionObligationsBAEC` with the front `FB : CompanionFrontRW`;
  every other field is a verbatim copy, typed at `FB.toBA.toND`; **`toBAEC`** (the bridge),
  **`ofBAEC`** (non-vacuity: BA-EC's obligations and the row certificates give RW's) and
  `toBAEC_ofBAEC` (`rfl`);
* **`main_goal_rebased_rw`**: `Target.SarkozyBound TargetGoal.epsGoal`, by
  `main_goal_rebased_baec` at `O.toBAEC`.
-/

namespace Sarkozy.BlockRows

open Filter Finset Function
open scoped Topology BigOperators

open Sarkozy.PartV Sarkozy.BlockSpecPaper Sarkozy.BlockAdapter Sarkozy.BlockInputs

/-! ## The block inputs -/

/-- **The block-level analytic inputs after RW**: BA's `BlockInputsBA` with the reference rows
`rowsU`, `rowsM` (block level, C) replaced by per-prime row certificates `rowU`, `rowM` (C + F).
6 fields, all per-prime certificates. -/
structure BlockInputsRW : Prop where
  /-- **(C + F)** Upper bands (310): the per-prime joint rows of the coordinate `0` at every field
  type, two-layer (ordinary input) and one-layer (reserved input), with per-band constants
  `(ℓ_mid, c_mar, c_F, c_E, k_J, t_Y)` and the gates of (F5)(a) at the band start
  (`UpperRowCert`; (F3), (F5)(a), `cor:joint-completion-blocks`, `lem:joint-rows`,
  `cert:upper-band-inputs`(c)). *Open* (per prime). -/
  rowU : ∀ k, UpperRowCert k
  /-- **(C + F)** As `BlockInputsBA.layerU`. *Open* (per prime). -/
  layerU : ∀ k, UpperLayerCertsP k
  /-- **(C + F)** As `BlockInputsBA.obsU`. *Open* (per prime). -/
  obsU : ∀ k, UpperObservedCertsP k
  /-- **(C + F)** Middle pieces (33): the per-prime rows of `lem:front12:reference`(i)
  ("One prime": `lem:record:class-three`(iii), `cor:influence-schur`), with per-piece
  constants `ρ_{F,j}, ρ_{E,j}` and the gates of the row constants `f_j`, `h_j` at the piece start
  (`MiddleRowCert`). *Open* (per prime). -/
  rowM : ∀ i, MiddleRowCert i
  /-- **(C + F)** As `BlockInputsBA.foldM`. *Open* (per prime). -/
  foldM : ∀ i, MiddleFoldCut i
  /-- **(C + F)** As `BlockInputsBA.rootI`. *Open* (per prime). -/
  rootI : ∀ i u, allpIndividual i = some u → MiddleIndividualRootCert i u

/-- The two row-certificate families of `BlockInputsRW` (kind C + F). -/
structure BlockCertsRW : Prop where
  /-- As `BlockInputsRW.rowU`. -/
  rowU : ∀ k, UpperRowCert k
  /-- As `BlockInputsRW.rowM`. -/
  rowM : ∀ i, MiddleRowCert i

namespace BlockInputsRW

/-- **BA's block inputs from RW's**: the upper and middle rows are proved from the row
certificates. -/
theorem toBA (BI : BlockInputsRW) : BlockInputsBA where
  rowsU k := upperBandRowsV2_of_cert (BI.rowU k)
  layerU := BI.layerU
  obsU := BI.obsU
  rowsM i := middleBlockRows_of_cert (BI.rowM i)
  foldM := BI.foldM
  rootI := BI.rootI

/-- **Non-vacuity**: BA's block inputs (of which the rows `rowsU`, `rowsM` are not used) and the
row certificates give RW's. -/
theorem ofBA (BI : BlockInputsBA) (C : BlockCertsRW) : BlockInputsRW where
  rowU := C.rowU
  layerU := BI.layerU
  obsU := BI.obsU
  rowM := C.rowM
  foldM := BI.foldM
  rootI := BI.rootI

end BlockInputsRW

/-! ## The front -/

section Front

open Sarkozy.PartVRecords Sarkozy.UpperComparison Sarkozy.UpperRepair Sarkozy.F7Repair
  Sarkozy.MainCombined Sarkozy.MainCombined2
open Sarkozy.MainFinalF1 (analyticInputs specF Blk bOf bandIdx)
open Sarkozy.PartVLaws (blockPrimes UpperBlockInputs)
open Sarkozy.ComparisonLawPaper (upperNe)
open Sarkozy.UpperCapsPaper (PrimeCertificatesUC UpperRecordTables)

/-- **The companion front after RW**: BA's `CompanionFrontBA` with `BI : BlockInputsRW`. 5 fields;
`rep`, `hs`, `ha` are typed at `BI.toBA.toBA` (a `Prop`, so at any proof). -/
structure CompanionFrontRW (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (UpT : UpperRecordTables) : Type 1 where
  /-- **(C + F)** As `CompanionFrontBA.PCu`. *Open*. -/
  PCu : PrimeCertificatesUC
  /-- **(C + F)** The block inputs (6 fields: `rowU`, `layerU`, `obsU`, `rowM`, `foldM`, `rootI`).
  *Open*. -/
  BI : BlockInputsRW
  /-- **(C)** As `CompanionFrontBA.rep`. *Open*. -/
  rep : ∀ (b : Blk) (U : UpperBlockInputs bOf b),
    specF hW (analyticInputs (PCu.toPC2'.toPC hW hMR hFour) BI.toBA.toBA) b = .upper U →
    BlockRepl (blockPrimes bOf b) (upperNe hW U)
  /-- **(F + R)** As `CompanionFrontBA.hs`. *Open*. -/
  hs : ∀ b U (h : specF hW (analyticInputs (PCu.toPC2'.toPC hW hMR hFour) BI.toBA.toBA) b =
      .upper U) ρ,
    upperFate ρ = .changed → (rep b U h).coef ρ .sym ≤ UpT.Cs (bandIdx b) ρ * U.r
  /-- **(F + R)** As `CompanionFrontBA.ha`. *Open*. -/
  ha : ∀ b U (h : specF hW (analyticInputs (PCu.toPC2'.toPC hW hMR hFour) BI.toBA.toBA) b =
      .upper U) ρ,
    upperFate ρ = .changed → (rep b U h).coef ρ .skew ≤ UpT.Ca (bandIdx b) ρ * U.r

namespace CompanionFrontRW

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {UpT : UpperRecordTables}

/-- BA's front, with `BI := BI.toBA`. -/
def toBA (F : CompanionFrontRW hW hMR hFour UpT) : CompanionFrontBA hW hMR hFour UpT where
  PCu := F.PCu
  BI := F.BI.toBA
  rep := F.rep
  hs := F.hs
  ha := F.ha

/-- **Non-vacuity of the front**: BA's front and the row certificates give an RW front. -/
def ofBA (F : CompanionFrontBA hW hMR hFour UpT) (C : BlockCertsRW) :
    CompanionFrontRW hW hMR hFour UpT where
  PCu := F.PCu
  BI := BlockInputsRW.ofBA F.BI C
  rep := F.rep
  hs := F.hs
  ha := F.ha

theorem toBA_ofBA (F : CompanionFrontBA hW hMR hFour UpT) (C : BlockCertsRW) :
    (ofBA F C).toBA = F := rfl

end CompanionFrontRW

end Front

/-! ## The obligations -/

section Main

open Sarkozy.ClassSlack
open Sarkozy.MainCombined Sarkozy.MainCombined2
open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper Sarkozy.ClassData Sarkozy.MainFinal2
open Sarkozy.MainFinalF1b Sarkozy.MeanCredit Sarkozy.MeanCredit2
open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.JointClosing
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.ThetaOne Sarkozy.SharpBase2
open Sarkozy.UpperCapsPaper (UpperRecordTables)
open Sarkozy.Companion (ResidualId CompId TotalsLe)

/-- **The obligations of `main_goal_rebased_rw`**: BA-EC's `CompanionObligationsBAEC` with the
front `FB : CompanionFrontRW` (BA's reference rows `rowsU`, `rowsM` replaced by the per-prime row
certificates `rowU`, `rowM`). Every other field is a verbatim copy of BA-EC's, typed at
`FB.toBA.toND`. 35 fields. -/
structure CompanionObligationsRW (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables) : Type 1 where
  /-- **The front** (5 fields): `PCu` (C + F), `BI` (6 fields, all C + F: `rowU`, `layerU`,
  `obsU`, `rowM`, `foldM`, `rootI`), `rep` (C), `hs`, `ha` (F + R). -/
  FB : CompanionFrontRW hW hMR hFour UpT
  /-- (D) As BA-EC. -/
  cd : ClassData (FB.toBA.toND.X hB hRR).data.CL
  /-- (D) As BA-EC. -/
  K : Type
  [instFK : Fintype K]
  [instDK : DecidableEq K]
  /-- (D) As BA-EC. -/
  Lt : Type
  [instFLt : Fintype Lt]
  [instDLt : DecidableEq Lt]
  /-- (D) As BA-EC. -/
  labS : ∀ L, Choice ((FB.toBA.toND.X hB hRR).data.CL.T L) → Option K
  /-- (D) As BA-EC. -/
  labK : K → PaperDiag
  /-- (D) As BA-EC. -/
  Zs : ∀ L, Finset ℤ → Choice ((FB.toBA.toND.X hB hRR).data.CL.T L) → ℝ
  /-- (D) As BA-EC. -/
  wc : ∀ L, cd.ι L → K → ℝ
  /-- (D) As BA-EC. -/
  ρ : ∀ L, Choice ((FB.toBA.toND.X hB hRR).data.CL.T L) → ℝ
  /-- (D) As BA-EC. -/
  r : ∀ L, Choice ((FB.toBA.toND.X hB hRR).data.CL.T L) → ℝ
  /-- (D) As BA-EC. -/
  Vv : ℝ
  /-- (D) As BA-EC. -/
  ℓ : ∀ L, Entry ((FB.toBA.toND.X hB hRR).data.CL.T L) → MLetter ⊕ Lt
  /-- (D) As BA-EC. -/
  c : (MLetter ⊕ Lt → ℕ) → ℝ
  /-- (D) As BA-EC. -/
  X : MLetter ⊕ Lt → ℝ
  /-- (D) As BA-EC. -/
  Cv : ℝ
  τ : ℝ
  /-- (S) As BA-EC. -/
  wc_nonneg : ∀ L i j, 0 ≤ wc L i j
  /-- (S) As BA-EC. -/
  hwHalf : WeightsHalf (FB.toBA.toND.X hB hRR).data cd labK wc
  /-- (S) As BA-EC. -/
  hVv : 0 ≤ Vv
  hvV : PriceBoundHalf (FB.toBA.toND.X hB hRR).data cd labS Vv
  /-- (S) As BA-EC. -/
  hZs : ∀ L A ω, 0 ≤ Zs L A ω
  /-- (S) As BA-EC. -/
  hX0 : ∀ l, 0 ≤ X l
  /-- (S) As BA-EC. -/
  hc0 : ∀ d, 0 ≤ c d
  /-- (S) As BA-EC. -/
  hτ : τ ≤ 13 / 625
  /-- **(F)** As BA-EC. -/
  hC : HasSum (fun d => c d * ∏ l, X l ^ d l / (d l).factorial) Cv
  /-- **(F)** As BA-EC. *Open*. -/
  hCv : Cv ≤ harnessE + τ
  /-- **(R)** As BA-EC. *Open*. -/
  hup : SelUpper (FB.toBA.toND.X hB hRR).data cd labS (wtHalf K) Zs wc
  /-- **(C)** As BA-EC. *Open*. -/
  ops : ClassStepsOps cd (fun _ => K)
    (fun L A => agg (cd.sel L) (labS L) (wtHalf K) (Zs L A)) wc ρ
  /-- **(C)** As BA-EC. *Open*. -/
  hρ : ResidualId (FB.toBA.toND.X hB hRR).data cd ρ r
  /-- **(C)** As BA-EC. *Open*. -/
  hcomp : CompId (FB.toBA.toND.X hB hRR).data cd labS labK ℓ c r
  /-- **(C)** As BA-EC. *Open*. -/
  hX : TotalsLe (FB.toBA.toND.X hB hRR).data ℓ X

attribute [instance] CompanionObligationsRW.instFK CompanionObligationsRW.instDK
  CompanionObligationsRW.instFLt CompanionObligationsRW.instDLt

namespace CompanionObligationsRW

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {hB : Target.BMOR} {hRR : Target.ThetaSmallRR} {UpT : UpperRecordTables}

/-- **BA-EC's obligations** (`FB := FB.toBA`; every other field verbatim). -/
def toBAEC (O : CompanionObligationsRW hW hMR hFour hB hRR UpT) :
    CompanionObligationsBAEC hW hMR hFour hB hRR UpT where
  FB := O.FB.toBA
  cd := O.cd
  K := O.K
  Lt := O.Lt
  labS := O.labS
  labK := O.labK
  Zs := O.Zs
  wc := O.wc
  ρ := O.ρ
  r := O.r
  Vv := O.Vv
  ℓ := O.ℓ
  c := O.c
  X := O.X
  Cv := O.Cv
  τ := O.τ
  wc_nonneg := O.wc_nonneg
  hwHalf := O.hwHalf
  hVv := O.hVv
  hvV := O.hvV
  hZs := O.hZs
  hX0 := O.hX0
  hc0 := O.hc0
  hτ := O.hτ
  hC := O.hC
  hCv := O.hCv
  hup := O.hup
  ops := O.ops
  hρ := O.hρ
  hcomp := O.hcomp
  hX := O.hX

/-- **Non-vacuity**: BA-EC's obligations and the row certificates (`BlockCertsRW`) give RW's
obligations. So RW asks, beyond BA-EC, only these per-prime certificates, which replace the
block-level rows `FB.BI.rowsU`, `FB.BI.rowsM`. -/
def ofBAEC (O : CompanionObligationsBAEC hW hMR hFour hB hRR UpT) (C : BlockCertsRW) :
    CompanionObligationsRW hW hMR hFour hB hRR UpT where
  FB := CompanionFrontRW.ofBA O.FB C
  cd := O.cd
  K := O.K
  Lt := O.Lt
  labS := O.labS
  labK := O.labK
  Zs := O.Zs
  wc := O.wc
  ρ := O.ρ
  r := O.r
  Vv := O.Vv
  ℓ := O.ℓ
  c := O.c
  X := O.X
  Cv := O.Cv
  τ := O.τ
  wc_nonneg := O.wc_nonneg
  hwHalf := O.hwHalf
  hVv := O.hVv
  hvV := O.hvV
  hZs := O.hZs
  hX0 := O.hX0
  hc0 := O.hc0
  hτ := O.hτ
  hC := O.hC
  hCv := O.hCv
  hup := O.hup
  ops := O.ops
  hρ := O.hρ
  hcomp := O.hcomp
  hX := O.hX

/-- The round trip `toBAEC ∘ ofBAEC` is the identity (definitionally; `BI` is a `Prop`). -/
theorem toBAEC_ofBAEC (O : CompanionObligationsBAEC hW hMR hFour hB hRR UpT)
    (C : BlockCertsRW) : (ofBAEC O C).toBAEC = O :=
  rfl

end CompanionObligationsRW

/-- **The rebased companion statement with the reference rows from per-prime certificates**
(`thm:main` at `ε = 10⁻⁵`): `s(N) ≤ C·N^{0.99999}` from the literature (L), the record table `UpT`
(F) and `O : CompanionObligationsRW`, in which the upper and middle reference rows
(`lem:upper-reference-rp`(ii), `lem:front12:reference`(i)) are no longer assumed at the block
level but derived from per-prime certificates: `main_goal_rebased_baec` at `O.toBAEC`. -/
theorem main_goal_rebased_rw (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables)
    (O : CompanionObligationsRW hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR UpT) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  BlockInputs.main_goal_rebased_baec hWeil hBMOR hMovingRoot hFourCycle
    hThetaSmallRR UpT O.toBAEC

end Main

end Sarkozy.BlockRows
