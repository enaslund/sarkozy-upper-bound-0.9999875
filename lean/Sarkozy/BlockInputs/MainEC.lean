module

public import Sarkozy.BlockInputs.Main
public import Sarkozy.E1Closure.All

@[expose] public section

/-!
# BA combined with EC (`main_goal_rebased_baec`)

BA, 8 November 2026. EC's `E1Closure.CompanionObligationsEC` (SR's obligations with (E1) off the
classes constructed and proved; 35 fields) with the front's `BA : MainFinal.BlockAnalytic`
replaced by BA's `BlockInputsBA` (the rows `rowsU`, `rowsM` and the certificates `layerU`, `obsU`,
`foldM`, `rootI`; `Main.lean`):

* **`CompanionObligationsBAEC`**: `CompanionObligationsEC` with the front `FB : CompanionFrontBA`;
  every other field is a verbatim copy of EC's, typed at `FB.toND`;
* `toEC` (the bridge: `F := FB.toND`); **`ofEC`** (non-vacuity: EC's obligations and the four
  certificate families `BlockCertsBA` give BA-EC's) and `toEC_ofEC` (`rfl`);
* **`main_goal_rebased_baec`**: `Target.SarkozyBound TargetGoal.epsGoal`, by EC's
  `main_goal_rebased_ec` at `O.toEC`.
-/

namespace Sarkozy.BlockInputs

open Filter Finset Function
open scoped Topology BigOperators

open Sarkozy.ClassSlack
open Sarkozy.PartV Sarkozy.BlockSpecPaper Sarkozy.MainCombined Sarkozy.MainCombined2
open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper Sarkozy.ClassData Sarkozy.MainFinal2
open Sarkozy.MainFinalF1b Sarkozy.MeanCredit Sarkozy.MeanCredit2
open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.JointClosing
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.ThetaOne Sarkozy.SharpBase2
open Sarkozy.UpperCapsPaper (UpperRecordTables)
open Sarkozy.Companion (ResidualId CompId TotalsLe)
open Sarkozy.E1Closure (CompanionObligationsEC)

/-- **The obligations of `main_goal_rebased_baec`**: EC's `CompanionObligationsEC` with the front
`FB : CompanionFrontBA` (B6's `BA` replaced by `BlockInputsBA`). Every other field is a verbatim
copy of EC's, typed at `FB.toND`. 35 fields, as EC's. -/
structure CompanionObligationsBAEC (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables) : Type 1 where
  /-- **The front** (5 fields): `PCu` (C + F), `BI` (6 fields: `rowsU`, `rowsM` (C); `layerU`,
  `obsU`, `foldM`, `rootI` (C + F)), `rep` (C), `hs`, `ha` (F + R). -/
  FB : CompanionFrontBA hW hMR hFour UpT
  /-- (D) As EC. -/
  cd : ClassData (FB.toND.X hB hRR).data.CL
  /-- (D) As EC. -/
  K : Type
  [instFK : Fintype K]
  [instDK : DecidableEq K]
  /-- (D) As EC. -/
  Lt : Type
  [instFLt : Fintype Lt]
  [instDLt : DecidableEq Lt]
  /-- (D) As EC. -/
  labS : ∀ L, Choice ((FB.toND.X hB hRR).data.CL.T L) → Option K
  /-- (D) As EC. -/
  labK : K → PaperDiag
  /-- (D) As EC. -/
  Zs : ∀ L, Finset ℤ → Choice ((FB.toND.X hB hRR).data.CL.T L) → ℝ
  /-- (D) As EC. -/
  wc : ∀ L, cd.ι L → K → ℝ
  /-- (D) As EC. -/
  ρ : ∀ L, Choice ((FB.toND.X hB hRR).data.CL.T L) → ℝ
  /-- (D) As EC. -/
  r : ∀ L, Choice ((FB.toND.X hB hRR).data.CL.T L) → ℝ
  /-- (D) As EC. -/
  Vv : ℝ
  /-- (D) As EC. -/
  ℓ : ∀ L, Entry ((FB.toND.X hB hRR).data.CL.T L) → MLetter ⊕ Lt
  /-- (D) As EC. -/
  c : (MLetter ⊕ Lt → ℕ) → ℝ
  /-- (D) As EC. -/
  X : MLetter ⊕ Lt → ℝ
  /-- (D) As EC. -/
  Cv : ℝ
  τ : ℝ
  /-- (S) As EC. -/
  wc_nonneg : ∀ L i j, 0 ≤ wc L i j
  /-- (S) As EC. -/
  hwHalf : WeightsHalf (FB.toND.X hB hRR).data cd labK wc
  /-- (S) As EC. -/
  hVv : 0 ≤ Vv
  hvV : PriceBoundHalf (FB.toND.X hB hRR).data cd labS Vv
  /-- (S) As EC. -/
  hZs : ∀ L A ω, 0 ≤ Zs L A ω
  /-- (S) As EC. -/
  hX0 : ∀ l, 0 ≤ X l
  /-- (S) As EC. -/
  hc0 : ∀ d, 0 ≤ c d
  /-- (S) As EC. -/
  hτ : τ ≤ 13 / 625
  /-- **(F)** As EC. -/
  hC : HasSum (fun d => c d * ∏ l, X l ^ d l / (d l).factorial) Cv
  /-- **(F)** As EC. *Open*. -/
  hCv : Cv ≤ harnessE + τ
  /-- **(R)** As EC. *Open*. -/
  hup : SelUpper (FB.toND.X hB hRR).data cd labS (wtHalf K) Zs wc
  /-- **(C)** As EC. *Open*. -/
  ops : ClassStepsOps cd (fun _ => K)
    (fun L A => agg (cd.sel L) (labS L) (wtHalf K) (Zs L A)) wc ρ
  /-- **(C)** As EC. *Open*. -/
  hρ : ResidualId (FB.toND.X hB hRR).data cd ρ r
  /-- **(C)** As EC. *Open*. -/
  hcomp : CompId (FB.toND.X hB hRR).data cd labS labK ℓ c r
  /-- **(C)** As EC. *Open*. -/
  hX : TotalsLe (FB.toND.X hB hRR).data ℓ X

attribute [instance] CompanionObligationsBAEC.instFK CompanionObligationsBAEC.instDK
  CompanionObligationsBAEC.instFLt CompanionObligationsBAEC.instDLt

namespace CompanionObligationsBAEC

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {hB : Target.BMOR} {hRR : Target.ThetaSmallRR} {UpT : UpperRecordTables}

/-- **EC's obligations** (`F := FB.toND`; every other field verbatim). -/
def toEC (O : CompanionObligationsBAEC hW hMR hFour hB hRR UpT) :
    CompanionObligationsEC hW hMR hFour hB hRR UpT where
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

/-- **Non-vacuity**: EC's obligations and the four certificate families (`BlockCertsBA`) give
BA-EC's obligations. So BA-EC asks, beyond EC, only these per-prime certificates, which replace
the block-level caps of EC's `F.BA`. -/
noncomputable def ofEC (O : CompanionObligationsEC hW hMR hFour hB hRR UpT) (C : BlockCertsBA) :
    CompanionObligationsBAEC hW hMR hFour hB hRR UpT where
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

/-- The round trip `toEC ∘ ofEC` is the identity (definitionally; `BA` is a `Prop`). -/
theorem toEC_ofEC (O : CompanionObligationsEC hW hMR hFour hB hRR UpT) (C : BlockCertsBA) :
    (ofEC O C).toEC = O :=
  rfl

end CompanionObligationsBAEC

/-- **The rebased companion statement with (E1) off the classes proved (EC) and B6's block inputs
split (BA)** (`thm:main` at `ε = 10⁻⁵`): `s(N) ≤ C·N^{0.99999}` from the literature (L), the
record table `UpT` (F) and `O : CompanionObligationsBAEC`: `main_goal_rebased_ec` at `O.toEC`. -/
theorem main_goal_rebased_baec (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables)
    (O : CompanionObligationsBAEC hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR UpT) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  E1Closure.main_goal_rebased_ec hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR
    UpT O.toEC

end Sarkozy.BlockInputs
