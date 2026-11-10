module

public import Sarkozy.BlockInputs.UpperLayer
public import Sarkozy.BlockInputs.PositiveRoot
public import Sarkozy.BlockInputs.Exchange
public import Sarkozy.BlockInputs.FoldDensity
public import Sarkozy.SharpFirst.Main

@[expose] public section

/-!
# The rebased companion statement with B6's block inputs split (`main_goal_rebased_ba`)

BA, 8 November 2026. SR's front field `F.BA : MainFinal.BlockAnalytic` (3 fields `hUR`, `hMB`,
`hIB`, all of kind C) is replaced by **`BlockInputsBA`** (6 fields). Every layer cap and root
envelope inside B6's three fields is now *proved* from per-prime certificates with per-band
(per-piece) constants (kind C + F); only the rows stay at the block level (kind C):

* `hUR` (310 bands): the (V3) caps of the 12 regular non-`E × E` states are proved from `layerU`
  (`UpperLayer.lean`), those of the 4 observed states `LR`, `RL`, `LC`, `CL` from `obsU`
  (`Observed.lean`); both in the paper's orientations, the others by the coordinate exchange
  (`Exchange.lean`); kept: `rowsU` (the V2 rows);
* `hMB` (31 pieces): the F21 caps at `k_D` are proved from `foldM` (`FoldCaps.lean`; the density
  input of `lem:old-f-law`(a) is proved, `FoldDensity.lean`); kept: `rowsM`;
* `hIB` (2 pieces): the F21 caps (`foldM`), the L20 envelope and L21 cap of the positive root
  (`rootI`, `PositiveRoot.lean`) and the rows of the individual datum, which are the uniform rows
  (`Middle.lean`), are proved; kept: `rowsM`.

* `BlockInputsBA`, **`BlockInputsBA.toBA`**; `BlockCertsBA` (the four certificate families),
  `BlockInputsBA.ofBA` (non-vacuity: the two row fields follow from B6's `BlockAnalytic`);
* `CompanionFrontBA` (SR's front with `BA` replaced by `BI`), `toND`, `ofND`;
* **`CompanionObligationsBA`**: `CompanionObligationsSR` with the front `FB : CompanionFrontBA`;
  every other field is a verbatim copy, typed at `FB.toND`; `toSR`, **`ofSR`** (non-vacuity:
  SR's obligations and `BlockCertsBA` give BA's) and `toSR_ofSR` (`rfl`);
* **`main_goal_rebased_ba`**: `Target.SarkozyBound TargetGoal.epsGoal`, by `main_goal_rebased_sr`
  at `O.toSR`.
-/

namespace Sarkozy.BlockInputs

open Filter Finset Function
open scoped Topology BigOperators

open Sarkozy.PartV Sarkozy.BlockSpecPaper Sarkozy.BlockAdapter
open Sarkozy.MainFinal (BlockAnalytic)

/-! ## The block inputs -/

/-- **The block-level analytic inputs after BA**: B6's `BlockAnalytic` with every layer cap and
root envelope replaced by per-prime certificates (4 fields, C + F); the rows stay at the block
level (2 fields, C). 6 fields. -/
structure BlockInputsBA : Prop where
  /-- **(C)** Upper bands (310): the coordinate-`0` rows `rows20`, `rows10` (V2;
  `lem:upper-reference-rp`(ii), (F5)). *Open* (block level). -/
  rowsU : ∀ k, UpperBandRowsV2 k
  /-- **(C + F)** Upper bands (310): for the layer cuts LL22, FL22, FF22, EL22, FE22 (the paper's
  orientations; the others follow by the coordinate exchange, `Exchange.lean`), constants
  `(g, B, X)` with `g e^{B L_k/(X log X)}` at most the recorded cap and the per-prime bounds
  `-g p^{-1/2} ⪯ A_p ⪯ 1 + B/p` at every class-three prime of the band ((F6),
  `cert:upper-band-inputs`(a); LL22: `cert:upper-root-caps`, `lem:upper-completed-root`). *Open*
  (per prime). -/
  layerU : ∀ k, UpperLayerCertsP k
  /-- **(C + F)** Upper bands (310): for the observed states (`RL`, `LR` and `CL`, `LC`), constants
  `(g, B, X)` with block cap at most the recorded caps and per prime
  `-g p^{-1/2} ⪯ A_p^O ⪯ 1 + B/p` for the layer cut operator of `G_{EL,2}` compressed to the merge
  or the constant labels (`prop:observed-caps`, `cert:upper-band-inputs`(b)). *Open* (per prime). -/
  obsU : ∀ k, UpperObservedCertsP k
  /-- **(C)** Middle pieces (33): the rows `j = 2, 1` (`lem:front12:reference`(i)). *Open* (block
  level). -/
  rowsM : ∀ i, MiddleBlockRows i
  /-- **(C + F)** Middle pieces (33): the F21 certificate (`lem:old-f-law`(e),(f),
  `cert:record:old-f-cap`): constants `(g, n)` with `n e₀(X) < 1`, `g/(1 - n e₀(X)) ≤ k_D`, and
  per prime `T_old ⪰ -g p^{-1/2}` on `L²(m₀)`. The density bound `g₀ ≤ 1 + e₀` of (a) is proved
  (`foldDensity_e0`). *Open* (per prime). -/
  foldM : ∀ i, MiddleFoldCut i
  /-- **(C + F)** Middle pieces `2³⁶`, `2⁴⁰`: the positive-root certificate
  (`prop:root-chamber`, `prop:root-layer`, `cert:positive-root-caps`): constants `(g, B)` per cut
  with block caps at most `capVal i 0` (L20) and `capK i L` (L21), and per prime
  `-g p^{-1/2} ⪯ T_u ⪯ 1 + B/p` for the reweighted cut operators in the fixed charts. *Open* (per
  prime). -/
  rootI : ∀ i u, allpIndividual i = some u → MiddleIndividualRootCert i u

/-- The four certificate families of `BlockInputsBA` (all of kind C + F). -/
structure BlockCertsBA : Prop where
  /-- As `BlockInputsBA.layerU`. -/
  layerU : ∀ k, UpperLayerCertsP k
  /-- As `BlockInputsBA.obsU`. -/
  obsU : ∀ k, UpperObservedCertsP k
  /-- As `BlockInputsBA.foldM`. -/
  foldM : ∀ i, MiddleFoldCut i
  /-- As `BlockInputsBA.rootI`. -/
  rootI : ∀ i u, allpIndividual i = some u → MiddleIndividualRootCert i u

namespace BlockInputsBA

/-- **B6's `BlockAnalytic` from the block inputs.** -/
theorem toBA (BI : BlockInputsBA) : BlockAnalytic where
  hUR k := upperBandRowsNonEE_of_certs (BI.rowsU k) (upperLayerCerts_of_paper (BI.layerU k))
    (upperObservedCaps_of_certs (upperObservedCerts_of_paper (BI.obsU k)))
  hMB i _ := middleUniformBlockInputs_of (BI.rowsM i) (middleFoldCert_of_cut (BI.foldM i))
  hIB i u hi := middleIndividualBlockInputs_of (BI.rowsM i) (middleFoldCert_of_cut (BI.foldM i))
    (middleIndividualRoot_of_cert (BI.rootI i u hi))

/-- **Non-vacuity**: B6's `BlockAnalytic` with the four certificate families gives
`BlockInputsBA` (the two block-level fields, the rows, are parts of B6's fields). -/
theorem ofBA (BA : BlockAnalytic) (C : BlockCertsBA) : BlockInputsBA where
  rowsU k := upperBandRowsV2_of_nonEE (BA.hUR k)
  layerU := C.layerU
  obsU := C.obsU
  rowsM i := by
    cases hi : allpIndividual i with
    | none => exact middleBlockRows_of_uniform (BA.hMB i hi)
    | some u => exact middleBlockRows_of_individual (BA.hIB i u hi)
  foldM := C.foldM
  rootI := C.rootI

end BlockInputsBA

/-! ## The front -/

section Front

open Sarkozy.PartVRecords Sarkozy.UpperComparison Sarkozy.UpperRepair Sarkozy.F7Repair
  Sarkozy.MainCombined Sarkozy.MainCombined2
open Sarkozy.MainFinalF1 (analyticInputs specF Blk bOf bandIdx)
open Sarkozy.PartVLaws (blockPrimes UpperBlockInputs)
open Sarkozy.ComparisonLawPaper (upperNe)
open Sarkozy.UpperCapsPaper (PrimeCertificatesUC UpperRecordTables)
open Sarkozy.CompanionND (CompanionFrontND)

/-- **The companion front after BA**: ND's `CompanionFrontND` with `BA` replaced by the block
inputs `BI`. 5 fields; `rep`, `hs`, `ha` are typed at `BI.toBA` (a `Prop`, so at any proof). -/
structure CompanionFrontBA (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (UpT : UpperRecordTables) : Type 1 where
  /-- **(C + F)** As `CompanionFrontND.PCu`. *Open*. -/
  PCu : PrimeCertificatesUC
  /-- **(C, C + F)** The block inputs (6 fields: the rows `rowsU`, `rowsM` (C); the certificates
  `layerU`, `obsU`, `foldM`, `rootI` (C + F)). *Open*. -/
  BI : BlockInputsBA
  /-- **(C)** As `CompanionFrontND.rep`. *Open*. -/
  rep : ∀ (b : Blk) (U : UpperBlockInputs bOf b),
    specF hW (analyticInputs (PCu.toPC2'.toPC hW hMR hFour) BI.toBA) b = .upper U →
    BlockRepl (blockPrimes bOf b) (upperNe hW U)
  /-- **(F + R)** As `CompanionFrontND.hs`. *Open*. -/
  hs : ∀ b U (h : specF hW (analyticInputs (PCu.toPC2'.toPC hW hMR hFour) BI.toBA) b = .upper U) ρ,
    upperFate ρ = .changed → (rep b U h).coef ρ .sym ≤ UpT.Cs (bandIdx b) ρ * U.r
  /-- **(F + R)** As `CompanionFrontND.ha`. *Open*. -/
  ha : ∀ b U (h : specF hW (analyticInputs (PCu.toPC2'.toPC hW hMR hFour) BI.toBA) b = .upper U) ρ,
    upperFate ρ = .changed → (rep b U h).coef ρ .skew ≤ UpT.Ca (bandIdx b) ρ * U.r

namespace CompanionFrontBA

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {UpT : UpperRecordTables}

/-- ND's front, with `BA := BI.toBA`. -/
def toND (F : CompanionFrontBA hW hMR hFour UpT) : CompanionFrontND hW hMR hFour UpT where
  PCu := F.PCu
  BA := F.BI.toBA
  rep := F.rep
  hs := F.hs
  ha := F.ha

/-- **Non-vacuity of the front**: ND's front and the two certificate families give a BA front. -/
def ofND (F : CompanionFrontND hW hMR hFour UpT) (C : BlockCertsBA) :
    CompanionFrontBA hW hMR hFour UpT where
  PCu := F.PCu
  BI := BlockInputsBA.ofBA F.BA C
  rep := F.rep
  hs := F.hs
  ha := F.ha

theorem toND_ofND (F : CompanionFrontND hW hMR hFour UpT) (C : BlockCertsBA) :
    (ofND F C).toND = F := rfl

end CompanionFrontBA

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
open Sarkozy.Companion (E1R0 E1R E1Sub E1Coup E1Rem ResidualId CompId TotalsLe)
open Sarkozy.SharpFirst (CompanionObligationsSR)

/-- **The obligations of `main_goal_rebased_ba`**: `CompanionObligationsSR` with the front
`FB : CompanionFrontBA` (B6's `BA` replaced by `BlockInputsBA`). Every other field is a verbatim
copy of SR's, typed at `FB.toND`. 47 fields, as SR; the front's block field now has 6 fields, 4 of
them per-prime (C + F). -/
structure CompanionObligationsBA (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables) : Type 1 where
  /-- **The front** (5 fields): `PCu` (C + F), `BI` (6 fields: 4 C, 2 C + F), `rep` (C), `hs`,
  `ha` (F + R). -/
  FB : CompanionFrontBA hW hMR hFour UpT
  /-- (D) As SR. -/
  cd : ClassData (FB.toND.X hB hRR).data.CL
  /-- (D) As SR. -/
  K : Type
  [instFK : Fintype K]
  [instDK : DecidableEq K]
  /-- (D) As SR. -/
  Lt : Type
  [instFLt : Fintype Lt]
  [instDLt : DecidableEq Lt]
  /-- (D) As SR. -/
  labS : ∀ L, Choice ((FB.toND.X hB hRR).data.CL.T L) → Option K
  /-- (D) As SR. -/
  labK : K → PaperDiag
  /-- (D) As SR. -/
  Zs : ∀ L, Finset ℤ → Choice ((FB.toND.X hB hRR).data.CL.T L) → ℝ
  /-- (D) As SR. -/
  wc : ∀ L, cd.ι L → K → ℝ
  /-- (D) As SR. -/
  ρ : ∀ L, Choice ((FB.toND.X hB hRR).data.CL.T L) → ℝ
  /-- (D) As SR. -/
  r : ∀ L, Choice ((FB.toND.X hB hRR).data.CL.T L) → ℝ
  /-- (D) As SR. -/
  Vv : ℝ
  /-- (D) As SR. -/
  ℓ : ∀ L, Entry ((FB.toND.X hB hRR).data.CL.T L) → MLetter ⊕ Lt
  /-- (D) As SR. -/
  c : (MLetter ⊕ Lt → ℕ) → ℝ
  /-- (D) As SR. -/
  X : MLetter ⊕ Lt → ℝ
  /-- (D) As SR. -/
  Cv : ℝ
  τ : ℝ
  /-- (D) As SR. -/
  εE : ℕ → ℝ
  cE : ℝ
  r0 : E1R0 (FB.toND.X hB hRR).data
  rE : E1R (FB.toND.X hB hRR).data
  /-- (S) As SR. -/
  wc_nonneg : ∀ L i j, 0 ≤ wc L i j
  /-- (S) As SR. -/
  hwHalf : WeightsHalf (FB.toND.X hB hRR).data cd labK wc
  /-- (S) As SR. -/
  hVv : 0 ≤ Vv
  hvV : PriceBoundHalf (FB.toND.X hB hRR).data cd labS Vv
  /-- (S) As SR. -/
  hZs : ∀ L A ω, 0 ≤ Zs L A ω
  /-- (S) As SR. -/
  hX0 : ∀ l, 0 ≤ X l
  /-- (S) As SR. -/
  hc0 : ∀ d, 0 ≤ c d
  /-- (S) As SR. -/
  hτ : τ ≤ 13 / 625
  /-- (S) As SR. -/
  hεE0 : ∀ L, 0 ≤ εE L
  hεEt : Tendsto εE atTop (𝓝 0)
  hcE : 0 ≤ cE
  hrE0 : ∀ L A ω σ j f, 0 ≤ rE L A ω σ j f
  hr00 : ∀ L A ω f, 0 ≤ r0 L A ω f
  /-- **(F)** As SR. -/
  hC : HasSum (fun d => c d * ∏ l, X l ^ d l / (d l).factorial) Cv
  /-- **(F)** As SR. *Open*. -/
  hCv : Cv ≤ harnessE + τ
  /-- **(R)** As SR. *Open*. -/
  hup : SelUpper (FB.toND.X hB hRR).data cd labS (wtHalf K) Zs wc
  /-- **(R)** As SR. *Open*. -/
  hsub : E1Sub (FB.toND.X hB hRR).data εE r0
  /-- **(C)** As SR. *Open*. -/
  ops : ClassStepsOps cd (fun _ => K)
    (fun L A => agg (cd.sel L) (labS L) (wtHalf K) (Zs L A)) wc ρ
  /-- **(C)** As SR. *Open*. -/
  hρ : ResidualId (FB.toND.X hB hRR).data cd ρ r
  /-- **(C)** As SR. *Open*. -/
  hcomp : CompId (FB.toND.X hB hRR).data cd labS labK ℓ c r
  /-- **(C)** As SR. *Open*. -/
  hX : TotalsLe (FB.toND.X hB hRR).data ℓ X
  /-- **(C)** As SR. *Open*. -/
  hcoup : E1Coup (FB.toND.X hB hRR).data εE rE
  /-- **(C)** As SR. *Open*. -/
  hremE : E1Rem (FB.toND.X hB hRR).data cE r0 rE

attribute [instance] CompanionObligationsBA.instFK CompanionObligationsBA.instDK
  CompanionObligationsBA.instFLt CompanionObligationsBA.instDLt

namespace CompanionObligationsBA

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {hB : Target.BMOR} {hRR : Target.ThetaSmallRR} {UpT : UpperRecordTables}

/-- **SR's obligations** (`F := FB.toND`; every other field verbatim). -/
noncomputable def toSR (O : CompanionObligationsBA hW hMR hFour hB hRR UpT) :
    CompanionObligationsSR hW hMR hFour hB hRR UpT where
  F := O.FB.toND
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
  εE := O.εE
  cE := O.cE
  r0 := O.r0
  rE := O.rE
  wc_nonneg := O.wc_nonneg
  hwHalf := O.hwHalf
  hVv := O.hVv
  hvV := O.hvV
  hZs := O.hZs
  hX0 := O.hX0
  hc0 := O.hc0
  hτ := O.hτ
  hεE0 := O.hεE0
  hεEt := O.hεEt
  hcE := O.hcE
  hrE0 := O.hrE0
  hr00 := O.hr00
  hC := O.hC
  hCv := O.hCv
  hup := O.hup
  hsub := O.hsub
  ops := O.ops
  hρ := O.hρ
  hcomp := O.hcomp
  hX := O.hX
  hcoup := O.hcoup
  hremE := O.hremE

/-- **Non-vacuity**: SR's obligations and the four new certificate families (`BlockCertsBA`)
give BA's obligations. So BA asks, beyond SR, only
these per-prime certificates, and of SR's block field only its parts that are not derived from
them. -/
noncomputable def ofSR (O : CompanionObligationsSR hW hMR hFour hB hRR UpT) (C : BlockCertsBA) :
    CompanionObligationsBA hW hMR hFour hB hRR UpT where
  FB := CompanionFrontBA.ofND O.F C
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
  εE := O.εE
  cE := O.cE
  r0 := O.r0
  rE := O.rE
  wc_nonneg := O.wc_nonneg
  hwHalf := O.hwHalf
  hVv := O.hVv
  hvV := O.hvV
  hZs := O.hZs
  hX0 := O.hX0
  hc0 := O.hc0
  hτ := O.hτ
  hεE0 := O.hεE0
  hεEt := O.hεEt
  hcE := O.hcE
  hrE0 := O.hrE0
  hr00 := O.hr00
  hC := O.hC
  hCv := O.hCv
  hup := O.hup
  hsub := O.hsub
  ops := O.ops
  hρ := O.hρ
  hcomp := O.hcomp
  hX := O.hX
  hcoup := O.hcoup
  hremE := O.hremE

/-- The round trip `toSR ∘ ofSR` is the identity (definitionally; `BA` is a `Prop`). -/
theorem toSR_ofSR (O : CompanionObligationsSR hW hMR hFour hB hRR UpT) (C : BlockCertsBA) :
    (ofSR O C).toSR = O :=
  rfl

end CompanionObligationsBA

/-- **The rebased companion statement with B6's block inputs split** (`thm:main` at
`ε = 10⁻⁵`): `s(N) ≤ C·N^{0.99999}` from the literature (L), the record table `UpT` (F) and the
obligations `O : CompanionObligationsBA`, in which B6's block-level layer caps and positive-root
envelopes are no longer assumed but derived from per-prime certificates (only the rows remain at
the block level): `main_goal_rebased_sr` at `O.toSR`. -/
theorem main_goal_rebased_ba (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables)
    (O : CompanionObligationsBA hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR UpT) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  SharpFirst.main_goal_rebased_sr hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR
    UpT O.toSR

end Main

end Sarkozy.BlockInputs
