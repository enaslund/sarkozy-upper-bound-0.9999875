module

public import Sarkozy.OpsCore.Assembly
public import Sarkozy.E1Closure.Main

@[expose] public section




open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.OpsCore

open Sarkozy.ClassSlack Sarkozy.ClassInputsPaper Sarkozy.ClassData Sarkozy.MainFinal2
open Sarkozy.MeanCredit Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.UpperCapsPaper (UpperRecordTables)
open Sarkozy.CompanionND (CompanionFrontND)
open Sarkozy.Companion (CompId TotalsLe)
open Sarkozy.E1Closure (CompanionObligationsEC main_goal_rebased_ec)
open Sarkozy.MeanCredit2

/-- **The obligations of `main_goal_rebased_ops`**: EC's `CompanionObligationsEC` without the
data `Zs`, `ρ` and the fields `hZs`, `hup`, `hρ` (theorems at the canonical data) and `ops`
(replaced by `opsIn`). Every other field is a verbatim copy of EC's. 30 fields. -/
structure CompanionObligationsOps (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables) : Type 1 where
  /-- **The front** (as EC's). -/
  F : CompanionFrontND hW hMR hFour UpT
  /-- (D) The classes (as EC's). -/
  cd : ClassData (F.X hB hRR).data.CL
  /-- (D) The labels of the aggregated diagonals (as EC's). -/
  K : Type
  [instFK : Fintype K]
  [instDK : DecidableEq K]
  /-- (D) The letters other than the mean letters (as EC's). -/
  Lt : Type
  [instFLt : Fintype Lt]
  [instDLt : DecidableEq Lt]
  /-- (D) The label of each selection (as EC's). -/
  labS : ∀ L, Choice ((F.X hB hRR).data.CL.T L) → Option K
  /-- (D) The paper type of each label (as EC's). -/
  labK : K → PaperDiag
  /-- (D) The class weights on the labels (as EC's; `toEC` uses its canonical split). -/
  wc : ∀ L, cd.ι L → K → ℝ
  /-- (D) The per-selection residual coefficients (as EC's). -/
  r : ∀ L, Choice ((F.X hB hRR).data.CL.T L) → ℝ
  /-- (D) The uniform bound of the label prices (as EC's). -/
  Vv : ℝ
  /-- (D) The lettering (as EC's). -/
  ℓ : ∀ L, Entry ((F.X hB hRR).data.CL.T L) → MLetter ⊕ Lt
  /-- (D) The comparison coefficient of a letter degree (as EC's). -/
  c : (MLetter ⊕ Lt → ℕ) → ℝ
  /-- (D) The letter totals (as EC's). -/
  X : MLetter ⊕ Lt → ℝ
  /-- (D) The completed comparison series and its slack (as EC's). -/
  Cv : ℝ
  τ : ℝ
  /-- (S) As EC's. -/
  wc_nonneg : ∀ L i j, 0 ≤ wc L i j
  /-- (S) `hwHalf`, as EC's. -/
  hwHalf : WeightsHalf (F.X hB hRR).data cd labK wc
  /-- (S) As EC's. -/
  hVv : 0 ≤ Vv
  hvV : PriceBoundHalf (F.X hB hRR).data cd labS Vv
  /-- (S) As EC's. -/
  hX0 : ∀ l, 0 ≤ X l
  hc0 : ∀ d, 0 ≤ c d
  hτ : τ ≤ 13 / 625
  /-- **(F)** As EC's. -/
  hC : HasSum (fun d => c d * ∏ l, X l ^ d l / (d l).factorial) Cv
  /-- **(F)** As EC's. *Open*. -/
  hCv : Cv ≤ harnessE + τ
  /-- **(C)** **The remaining inputs of `ops`** (`OpsInputs`): per degree class, the objects and
  operators, (N4), `hΥ` (OPS-L), the domination (OPS-F), (E1) for `Diag_ω`, Steps 3 and 4
  (OPS-S), the evaluations; per variance class `VarStepsAt` (OPS-V); the remainders. *Open*. -/
  opsIn : OpsInputs (F.X hB hRR).data cd labS labK r
  /-- **(C)** `hcomp`, as EC's. *Open*. -/
  hcomp : CompId (F.X hB hRR).data cd labS labK ℓ c r
  /-- **(C)** `hX`, as EC's. *Open*. -/
  hX : TotalsLe (F.X hB hRR).data ℓ X

attribute [instance] CompanionObligationsOps.instFK CompanionObligationsOps.instDK
  CompanionObligationsOps.instFLt CompanionObligationsOps.instDLt

namespace CompanionObligationsOps

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {hB : Target.BMOR} {hRR : Target.ThetaSmallRR} {UpT : UpperRecordTables}

/-- **The EC obligations** at the canonical data: `Zs := zsUp`, `ρ := r π`, `wc := wcCanon wc`;
`wc_nonneg`, `hwHalf`, `hZs`, `hup`, `hρ` proved; `ops := opsIn.toOps`. -/
noncomputable def toEC (O : CompanionObligationsOps hW hMR hFour hB hRR UpT) :
    CompanionObligationsEC hW hMR hFour hB hRR UpT where
  F := O.F
  cd := O.cd
  K := O.K
  Lt := O.Lt
  labS := O.labS
  labK := O.labK
  Zs := zsUp (O.F.X hB hRR).data
  wc := wcCanon O.cd O.labS O.labK O.wc
  ρ := rhoOf O.r
  r := O.r
  Vv := O.Vv
  ℓ := O.ℓ
  c := O.c
  X := O.X
  Cv := O.Cv
  τ := O.τ
  wc_nonneg := wcCanon_nonneg O.labS O.labK O.wc_nonneg
  hwHalf := weightsHalf_wcCanon O.labS O.labK O.hwHalf
  hVv := O.hVv
  hvV := O.hvV
  hZs := zsUp_nonneg O.cd
  hX0 := O.hX0
  hc0 := O.hc0
  hτ := O.hτ
  hC := O.hC
  hCv := O.hCv
  hup := selUpper_zsUp O.labS (wtHalf O.K) (wcCanon O.cd O.labS O.labK O.wc)
  ops := O.opsIn.toOps O.wc O.wc_nonneg
  hρ := residualId_rhoOf O.r
  hcomp := O.hcomp
  hX := O.hX

/-- **The other fields are implied by EC's**: an EC instance together with `OpsInputs` at its
labels and residual coefficients gives the new obligations (forget `Zs`, `ρ`, `hZs`, `hup`, `hρ`,
`ops`). -/
def ofEC (O : CompanionObligationsEC hW hMR hFour hB hRR UpT)
    (opsIn : OpsInputs (O.F.X hB hRR).data O.cd O.labS O.labK O.r) :
    CompanionObligationsOps hW hMR hFour hB hRR UpT where
  F := O.F
  cd := O.cd
  K := O.K
  Lt := O.Lt
  labS := O.labS
  labK := O.labK
  wc := O.wc
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
  hX0 := O.hX0
  hc0 := O.hc0
  hτ := O.hτ
  hC := O.hC
  hCv := O.hCv
  opsIn := opsIn
  hcomp := O.hcomp
  hX := O.hX

end CompanionObligationsOps

/-- **The rebased companion statement with `ops` replaced by its remaining inputs**
(`thm:main` at `ε = 10⁻⁵`): `s(N) ≤ C·N^{0.99999}` from the five literature hypotheses (L), the
record table `UpT` (F) and `O : CompanionObligationsOps`, through `main_goal_rebased_ec` at
`O.toEC`. -/
theorem main_goal_rebased_ops (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmallRR : Target.ThetaSmallRR) (UpT : UpperRecordTables)
    (O : CompanionObligationsOps hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR UpT) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_rebased_ec hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR UpT O.toEC

end Sarkozy.OpsCore
