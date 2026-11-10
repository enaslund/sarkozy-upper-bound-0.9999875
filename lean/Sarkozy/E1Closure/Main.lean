module

public import Sarkozy.E1Closure.CoupSmall
public import Sarkozy.SharpFirst.Main

@[expose] public section

/-!
# The rebased companion statement with (E1) off the classes proved (`main_goal_rebased_ec`)

EC, 8 November 2026. SR's `CompanionObligationsSR` (LP's with `SF` proved) has three (E1) fields
with free data `ε_E`, `c_E`, `r0`, `rE`: `hsub : E1Sub` (R), `hcoup : E1Coup` (C),
`hremE : E1Rem` (C). Here all of them are **constructed and proved**:

* `ε_E = u_L` (SR's `sfEps`), the remainders are the canonical excesses `r0X`, `rX`
  (`Excess.lean`), for which `E1Sub` and `E1Coup` hold outright (`e1Sub_r0X`, `e1Coup_rX`);
* `E1Rem` at these remainders is split by the full union (`Split.lean`,
  `10_comparison_lemmas.tex` ll. 126–140): the terms with `q_E > N^τ` by `lem:record:density-lp`
  (`e1Large_proved`), the subset terms with `q_E ≤ N^τ` by `prop:record:density-structured`
  (`e1SubSmall_proved`), the coupled pieces with `q_E ≤ N^τ` by the proof of `lem:sharp-first`
  (`lem:record:folded-energy` and `prop:record:density-structured` on each folded energy,
  `e1CoupSmall_proved`); `c_E = c_S + c_C + c_L`;
* **`CompanionObligationsEC`**: SR's obligations without `εE`, `cE`, `r0`, `rE`, `hεE0`, `hεEt`,
  `hcE`, `hrE0`, `hr00`, `hsub`, `hcoup`, `hremE` (35 fields; novel core 10 → 8, routine 2 → 1);
* `toSR` (the bridge), **`ofSR`** (non-vacuity: forget the twelve fields, so the new obligations
  are implied by SR's), `ofLP`, `ofCG0`, `ofSR_toSR` (`rfl`);
* **`main_goal_rebased_ec`**: `Target.SarkozyBound TargetGoal.epsGoal`, through SR's
  `main_goal_rebased_sr`.

The constructor uses `0 ≤ a` at `a = targetDecay`, the parity condition and `blockSel ≤ selPre` of
the paper's exponents, and nonempty blocks of the paper's layout (as SR's).
-/

namespace Sarkozy.E1Closure

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps Sarkozy.BlockAnchor Sarkozy.DensityChain2
  Sarkozy.DensityFibre Sarkozy.SharpSums
open Sarkozy.Param (Params)
open Sarkozy.ClassSlack
open Sarkozy.PartV Sarkozy.BlockSpecPaper Sarkozy.MainCombined Sarkozy.MainCombined2
open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper Sarkozy.ClassData Sarkozy.MainFinal2
open Sarkozy.MainFinalF1b Sarkozy.MeanCredit Sarkozy.MeanCredit2
open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.JointClosing
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.ThetaOne Sarkozy.SharpBase2
open Sarkozy.EnvelopeEnergiesPaper (paper_pairwise)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.UpperCapsPaper (UpperRecordTables)
open Sarkozy.CompanionND (CompanionFrontND)
open Sarkozy.Companion (E1R0 E1R E1Sub E1Coup E1Rem SFData SFFold SFRem ResidualId CompId
  TotalsLe)
open Sarkozy.CancellationSteps (PaperJ0)
open Sarkozy.TargetLedger (targetLedger)
open Sarkozy.LargeSums (CompanionObligationsLP)
open Sarkozy.SharpFirst (CompanionObligationsSR main_goal_rebased_sr sfEps sfEps_nonneg
  tendsto_sfEps)

/-- **The obligations of `main_goal_rebased_ec`**: SR's `CompanionObligationsSR` without the
data and the fields of (E1) off the classes, which are constructed and proved: `ε_E = u_L`, the
canonical remainders `r0X`, `rX` (for which `E1Sub`, `E1Coup` hold), and `E1Rem` from the split by
the full union (`e1Large_proved`, `e1SubSmall_proved`, `e1CoupSmall_proved`). Every other field
is a verbatim copy of SR's. 35 fields. -/
structure CompanionObligationsEC (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables) : Type 1 where
  /-- **The front** (5 fields, kinds marked in `CompanionFrontND`): `PCu` (C + F), `BA` (C),
  `rep` (C), `hs`, `ha` (F + R). The signed decomposition is proved below the front (ND). -/
  F : CompanionFrontND hW hMR hFour UpT
  -- (D) The free data of the class group (CM's route)
  /-- (D) The classes `ι`, `cls` of `def:cp5` (B10's `ClassData`). -/
  cd : ClassData (F.X hB hRR).data.CL
  /-- (D) The labels of the aggregated diagonals (e.g. `PaperDiag × Fin 4`, one per family). -/
  K : Type
  [instFK : Fintype K]
  [instDK : DecidableEq K]
  /-- (D) The letters of the record expansion other than CM's mean letters `F`, `E`, `I`, `G`. -/
  Lt : Type
  [instFLt : Fintype Lt]
  [instDLt : DecidableEq Lt]
  /-- (D) The label of each selection (`none`: unlabelled). -/
  labS : ∀ L, Choice ((F.X hB hRR).data.CL.T L) → Option K
  /-- (D) The paper type of each label. -/
  labK : K → PaperDiag
  /-- (D) The per-selection diagonal energies. -/
  Zs : ∀ L, Finset ℤ → Choice ((F.X hB hRR).data.CL.T L) → ℝ
  /-- (D) The class weights on the labels. -/
  wc : ∀ L, cd.ι L → K → ℝ
  /-- (D) The evaluated residuals of the selections (`cor:envelope-costs`). -/
  ρ : ∀ L, Choice ((F.X hB hRR).data.CL.T L) → ℝ
  /-- (D) The per-selection residual coefficients (the residual table). -/
  r : ∀ L, Choice ((F.X hB hRR).data.CL.T L) → ℝ
  /-- (D) The uniform bound of the label prices. -/
  Vv : ℝ
  /-- (D) The lettering of the record expansion (one letter per entry). -/
  ℓ : ∀ L, Entry ((F.X hB hRR).data.CL.T L) → MLetter ⊕ Lt
  /-- (D) The comparison coefficient of a letter degree. -/
  c : (MLetter ⊕ Lt → ℕ) → ℝ
  /-- (D) The letter totals. -/
  X : MLetter ⊕ Lt → ℝ
  /-- (D) The completed comparison series and its slack. -/
  Cv : ℝ
  τ : ℝ
  -- (S) Side conditions on the data
  /-- (S) The class weights are nonnegative. -/
  wc_nonneg : ∀ L i j, 0 ≤ wc L i j
  /-- (S) **`hwHalf`**: the aggregated class weight of a label is twice the paper's
  `κ_b − var = diagW` of its type (the residual table of `prop:joint-middle-mean`, aggregated at
  the weight `1/2`, so that the effective weight per selection is `diagW`). It pins `wc`; the
  content is then in `ops`. -/
  hwHalf : WeightsHalf (F.X hB hRR).data cd labK wc
  /-- (S) The aggregated label prices are uniformly bounded. -/
  hVv : 0 ≤ Vv
  hvV : PriceBoundHalf (F.X hB hRR).data cd labS Vv
  /-- (S) The per-selection energies are nonnegative. -/
  hZs : ∀ L A ω, 0 ≤ Zs L A ω
  /-- (S) The letter totals are nonnegative. The mean letters are not pinned (no `hXm`): no mean
  is retained, so they are ordinary letters. -/
  hX0 : ∀ l, 0 ≤ X l
  /-- (S) The comparison coefficient is nonnegative (it replaces the residual gates `hres`). -/
  hc0 : ∀ d, 0 ≤ c d
  /-- (S) The slack of the comparison series is at most `13/625 = 0.0208`
  (CG: `63 τ + 64 Δ_mid ≤ 12/5`,
  `noMean_room`; CM's route with the mean credit allows `3/100`). -/
  hτ : τ ≤ 13 / 625
  -- (F) Finite numerical claims
  /-- **(F)** The comparison side of `eq:final-joint-closing`: the completed comparison series
  `C_v = ∑_d c(d) ∏_l X_l^{d_l}/d_l!` … -/
  hC : HasSum (fun d => c d * ∏ l, X l ^ d l / (d l).factorial) Cv
  /-- **(F)** … is at most the harness's `𝓔` plus `τ` (`harnessE`, E3's v2 value). The class
  costs enter the gate here. *Open*. -/
  hCv : Cv ≤ harnessE + τ
  -- (R) Routine analytic lemmas
  /-- **(R)** `ES.upper` per selection (`lem:bracket-energy`, first display;
  `prop:record:density-structured`, `def:robust`): the labelled selection energies satisfy
  `Z_ω ≤ (1 + ε₃)π_ω Y + r_ω`, with the remainders summed against the class weights
  (`SelUpper`). *Open*. -/
  hup : SelUpper (F.X hB hRR).data cd labS (wtHalf K) Zs wc
  -- (C) Novel core still open
  /-- **(C)** `ES.ops` (`thm:envelopes`(i) Steps 1–4, `lem:oct24:mask-schur`(a),
  `lem:oct24:feature-block`(a), `prop:background-variance`(a), `lem:var-gain`(b),
  `lem:record:restoration`): B11's operator steps for the aggregated diagonals. *Open*. -/
  ops : ClassStepsOps cd (fun _ => K)
    (fun L A => agg (cd.sel L) (labS L) (wtHalf K) (Zs L A)) wc ρ
  /-- **(C)** The residual of a class selection is `r_ω` times its monomial
  (`cor:envelope-costs`). *Open*. -/
  hρ : ResidualId (F.X hB hRR).data cd ρ r
  /-- **(C)** `hcomp`: the comparison coefficient of a selection's letter degree dominates its
  class bound (`thm:envelopes`(i), `cor:envelope-costs`): `B` off the classes, `r_ω` on them,
  plus `diagW` on its label. *Open*. -/
  hcomp : CompId (F.X hB hRR).data cd labS labK ℓ c r
  /-- **(C)** `hX`: the formal letter totals are at most `X` (the price bounds of
  `lem:four-routes-normalized`). Without `hXm`, its content is joint with `hC`, `hcomp` only.
  *Open*. -/
  hX : TotalsLe (F.X hB hRR).data ℓ X

attribute [instance] CompanionObligationsEC.instFK CompanionObligationsEC.instDK
  CompanionObligationsEC.instFLt CompanionObligationsEC.instDLt

namespace CompanionObligationsEC

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {hB : Target.BMOR} {hRR : Target.ThetaSmallRR} {UpT : UpperRecordTables}

/-- **The large-union sum at the obligations' data** (`e1Large_proved`). -/
theorem large (O : CompanionObligationsEC hW hMR hFour hB hRR UpT) :
    ∃ c : ℝ, 0 ≤ c ∧ E1Large (O.F.X hB hRR).data c :=
  e1Large_proved _ TargetLedger.targetDecay_nonneg

/-- **The small-union sum of the subset terms at the obligations' data**, at `ε_E = u_L`
(`e1SubSmall_proved`). -/
theorem subS (O : CompanionObligationsEC hW hMR hFour hB hRR UpT) :
    ∃ c : ℝ, 0 ≤ c ∧ E1SubSmall (O.F.X hB hRR).data (sfEps (O.F.X hB hRR).data) c :=
  e1SubSmall_proved _ paper_pairwise TargetLedger.targetDecay_nonneg
    (DensityChain2.parity_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
    (DensityChain2.hsel_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
    (ThetaOne.paperAtomMap_paperBlockOf_surjective f1Cell)

/-- **The small-union sum of the coupled pieces at the obligations' data**, at `ε_E = u_L`
(`e1CoupSmall_proved`). -/
theorem coupS (O : CompanionObligationsEC hW hMR hFour hB hRR UpT) :
    ∃ c : ℝ, 0 ≤ c ∧ E1CoupSmall (O.F.X hB hRR).data (sfEps (O.F.X hB hRR).data) c :=
  e1CoupSmall_proved _ paper_pairwise TargetLedger.targetDecay_nonneg
    (DensityChain2.parity_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
    (DensityChain2.hsel_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
    (ThetaOne.paperAtomMap_paperBlockOf_surjective f1Cell)

/-- **The SR obligations**: `ε_E = u_L`, the canonical remainders `r0X`, `rX`, `E1Sub` and `E1Coup`
for them (`e1Sub_r0X`, `e1Coup_rX`), and `E1Rem` with `c_S + c_C + c_L` from the split
(`e1RemX_of_split`; `subS`, `coupS`, `large`). -/
noncomputable def toSR (O : CompanionObligationsEC hW hMR hFour hB hRR UpT) :
    CompanionObligationsSR hW hMR hFour hB hRR UpT where
  F := O.F
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
  εE := sfEps (O.F.X hB hRR).data
  cE := Classical.choose O.subS + Classical.choose O.coupS + Classical.choose O.large
  r0 := r0X (O.F.X hB hRR).data (sfEps (O.F.X hB hRR).data)
  rE := rX (O.F.X hB hRR).data (sfEps (O.F.X hB hRR).data)
  wc_nonneg := O.wc_nonneg
  hwHalf := O.hwHalf
  hVv := O.hVv
  hvV := O.hvV
  hZs := O.hZs
  hX0 := O.hX0
  hc0 := O.hc0
  hτ := O.hτ
  hεE0 := sfEps_nonneg (O.F.X hB hRR).data
  hεEt := tendsto_sfEps (O.F.X hB hRR).data
  hcE := add_nonneg (add_nonneg (Classical.choose_spec O.subS).1 (Classical.choose_spec O.coupS).1)
    (Classical.choose_spec O.large).1
  hrE0 := rX_nonneg (O.F.X hB hRR).data (sfEps (O.F.X hB hRR).data)
  hr00 := r0X_nonneg (O.F.X hB hRR).data (sfEps (O.F.X hB hRR).data)
  hC := O.hC
  hCv := O.hCv
  hup := O.hup
  hsub := e1Sub_r0X (O.F.X hB hRR).data (sfEps (O.F.X hB hRR).data)
  ops := O.ops
  hρ := O.hρ
  hcomp := O.hcomp
  hX := O.hX
  hcoup := e1Coup_rX (O.F.X hB hRR).data (sfEps (O.F.X hB hRR).data)
  hremE := e1RemX_of_split (O.F.X hB hRR).data (sfEps_nonneg (O.F.X hB hRR).data)
    (Classical.choose_spec O.subS).2
    (Classical.choose_spec O.coupS).2 (Classical.choose_spec O.large).2

/-- **Non-vacuity**: every `CompanionObligationsSR` gives a `CompanionObligationsEC` (forget the
twelve (E1) fields). So the new obligations are implied by SR's. -/
def ofSR (O : CompanionObligationsSR hW hMR hFour hB hRR UpT) :
    CompanionObligationsEC hW hMR hFour hB hRR UpT where
  F := O.F
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

/-- Every `CompanionObligationsLP` gives a `CompanionObligationsEC` (through SR's `ofLP`). -/
noncomputable def ofLP (O : CompanionObligationsLP hW hMR hFour hB hRR UpT) :
    CompanionObligationsEC hW hMR hFour hB hRR UpT :=
  ofSR (CompanionObligationsSR.ofLP O)

/-- Every `CompanionObligationsCG0` gives a `CompanionObligationsEC` (through SR's `ofCG0`). -/
noncomputable def ofCG0 (O : CompanionObligationsCG0 hW hMR hFour hB hRR UpT) :
    CompanionObligationsEC hW hMR hFour hB hRR UpT :=
  ofSR (CompanionObligationsSR.ofCG0 O)

/-- The round trip `ofSR ∘ toSR` is the identity (definitionally). -/
theorem ofSR_toSR (O : CompanionObligationsEC hW hMR hFour hB hRR UpT) : ofSR O.toSR = O := rfl

end CompanionObligationsEC

/-- **The rebased companion statement with (E1) off the classes proved** (`thm:main` at
`ε = 10⁻⁵`): `s(N) ≤ C·N^{0.99999}` from the literature (L), the record table `UpT` (F) and the
obligations `O : CompanionObligationsEC`, in which `SF` (SR) and (E1) off the classes (EC) are no
longer assumed: `main_goal_rebased_sr` at `O.toSR`. -/
theorem main_goal_rebased_ec (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables)
    (O : CompanionObligationsEC hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR UpT) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_rebased_sr hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR UpT O.toSR

end Sarkozy.E1Closure
