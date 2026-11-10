module

public import Sarkozy.SharpFirst.Rem
public import Sarkozy.LargeSums.Main

@[expose] public section

/-!
# The rebased companion statement with `SF.hfold` and `SF.hrem` proved (`main_goal_rebased_sr`)

SR, 8 November 2026. TH's two open fields of the baseline route of `lem:sharp-first`,
`SF.hfold` (`Companion.SFFold`, kind R) and `SF.hrem` (`Companion.SFRem`, kind C), are proved at
**constructed** data (`SharpFirst.Rem`): `ε = u_L`, the remainders `r_± = max(0, 𝔈_± − main)`,
and a constant `c` from `sfRem_proved`. The sharp decompositions `dec` exist
(`nonempty_decFamily`) and every statement downstream holds for every `dec`, so `dec` is chosen.
So the whole data `O.sf` of `CompanionObligationsLP` is constructed. Here:

* **`sfRem_target`**: `SFRem` at the paper's data, for every `dec`;
* `sfDec`, **`sfData`**: the constructed `SFData`;
* **`CompanionObligationsSR`**: `CompanionObligationsLP` without `sf`, `hεS0`, `hεSt`, `hcS`,
  `hrpm0`, `hfold`, `hremS` (47 fields; novel core (C) 10 instead of 11, routine (R) 2 instead
  of 3);
* `toLP` (the seven fields constructed), **`ofLP`** (non-vacuity: forget them), `ofCG0`;
* **`main_goal_rebased_sr`**: `Target.SarkozyBound TargetGoal.epsGoal`.

The constructor uses `0 ≤ a` at the data's `a = targetDecay`, the parity condition and
`blockSel ≤ selPre` of the paper's exponents (`parity_/hsel_blockPaperStandingAt`), and nonempty
blocks of the paper's layout (`paperAtomMap_paperBlockOf_surjective f1Cell`); it does not read the
ledger.
-/

namespace Sarkozy.SharpFirst

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps Sarkozy.BlockAnchor Sarkozy.DensityChain2
  Sarkozy.DensityFibre Sarkozy.SharpSums Sarkozy.LargeSums
open Sarkozy.Param (Params)

section Target

open Sarkozy.PartV Sarkozy.JointClosing Sarkozy.BlockSpecPaper Sarkozy.MainCombined
  Sarkozy.MainCombined2
open Sarkozy.EnvelopeEnergiesPaper (paper_pairwise)
open Sarkozy.CancellationSteps (PaperJ0)
open Sarkozy.Companion (SFData SFFold SFRem)

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B} {hW : Target.Weil}

/-- **`SF.hrem` at the paper's data** (`sfRem_proved` with the paper-data facts), for every
`dec`. -/
theorem sfRem_target (D : JointBlockDataTarget blockOf hW)
    (hne : ∀ β, ∃ i, PartVLaws.paperAtomMap blockOf i = β)
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D.data L) :
    ∃ c : ℝ, 0 ≤ c ∧ SFRem D.data c (sfRp D.data dec) (sfRm D.data dec) :=
  sfRem_proved D.data paper_pairwise dec TargetLedger.targetDecay_nonneg
    (DensityChain2.parity_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
    (DensityChain2.hsel_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _) hne

/-- The sharp decompositions of the differences, chosen (`nonempty_decFamily`). -/
noncomputable def sfDec (D : JointBlockDataTarget blockOf hW) :
    ∀ L, EnvelopeInputsBlock.DecFamily D.data L :=
  fun L => Classical.choice (EnvelopeInputsBlock.nonempty_decFamily D.data L)

/-- **The constructed data of `SF`**: `dec` chosen, `ε = u_L`, `r_± = max(0, 𝔈_± − main)`, and
the constant of `sfRem_target`. -/
noncomputable def sfData (D : JointBlockDataTarget blockOf hW)
    (hne : ∀ β, ∃ i, PartVLaws.paperAtomMap blockOf i = β) : SFData D.data where
  dec := sfDec D
  ε := sfEps D.data
  c := Classical.choose (sfRem_target D hne (sfDec D))
  rp := sfRp D.data (sfDec D)
  rm := sfRm D.data (sfDec D)

theorem sfData_c_nonneg (D : JointBlockDataTarget blockOf hW)
    (hne : ∀ β, ∃ i, PartVLaws.paperAtomMap blockOf i = β) : 0 ≤ (sfData D hne).c :=
  (Classical.choose_spec (sfRem_target D hne (sfDec D))).1

theorem sfData_rem (D : JointBlockDataTarget blockOf hW)
    (hne : ∀ β, ∃ i, PartVLaws.paperAtomMap blockOf i = β) :
    SFRem D.data (sfData D hne).c (sfData D hne).rp (sfData D hne).rm :=
  (Classical.choose_spec (sfRem_target D hne (sfDec D))).2

theorem sfData_fold (D : JointBlockDataTarget blockOf hW)
    (hne : ∀ β, ∃ i, PartVLaws.paperAtomMap blockOf i = β) :
    SFFold D.data (sfData D hne).dec (sfData D hne).ε (sfData D hne).rp (sfData D hne).rm :=
  sfFold_proved D.data (sfDec D)

end Target

section Main

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

/-- **The obligations of `main_goal_rebased_sr`**: `CompanionObligationsLP` without the data
`sf` of `SF`, its side conditions `hεS0`, `hεSt`, `hcS`, `hrpm0`, and its two open fields
`hfold` (R) and `hremS` (C), which are constructed and proved (`sfData`, `sfFold_proved`,
`sfRem_target`). Every other field is a verbatim copy. 47 fields. -/
structure CompanionObligationsSR (hW : Target.Weil) (hMR : Target.MovingRoot)
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
  -- (D) The free data of (E1)
  /-- (D) (E1): the relative error, the constant and the remainders. -/
  εE : ℕ → ℝ
  cE : ℝ
  r0 : E1R0 (F.X hB hRR).data
  rE : E1R (F.X hB hRR).data
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
  /-- (S) (E1): `0 ≤ ε_E → 0`, `c_E ≥ 0`, nonnegative remainders. -/
  hεE0 : ∀ L, 0 ≤ εE L
  hεEt : Tendsto εE atTop (𝓝 0)
  hcE : 0 ≤ cE
  hrE0 : ∀ L A ω σ j f, 0 ≤ rE L A ω σ j f
  hr00 : ∀ L A ω f, 0 ≤ r0 L A ω f
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
  /-- **(R)** `E1.hsub` (`lem:bracket-energy`, `prop:record:density-structured`): `E1Sub`.
  *Open*. -/
  hsub : E1Sub (F.X hB hRR).data εE r0
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
  /-- **(C)** `E1.hcoup` (`lem:sharp-first`, `lem:density:coupled`): `E1Coup`. *Open*. -/
  hcoup : E1Coup (F.X hB hRR).data εE rE
  /-- **(C)** `E1.hrem` (`lem:record:density-lp`, `def:robust`): `E1Rem`. *Open*. -/
  hremE : E1Rem (F.X hB hRR).data cE r0 rE

attribute [instance] CompanionObligationsSR.instFK CompanionObligationsSR.instDK
  CompanionObligationsSR.instFLt CompanionObligationsSR.instDLt

namespace CompanionObligationsSR

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {hB : Target.BMOR} {hRR : Target.ThetaSmallRR} {UpT : UpperRecordTables}

/-- **The LP obligations**: `sf` constructed (`sfData`), its side conditions and `SF.hfold`,
`SF.hrem` proved. -/
noncomputable def toLP (O : CompanionObligationsSR hW hMR hFour hB hRR UpT) :
    CompanionObligationsLP hW hMR hFour hB hRR UpT where
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
  sf := sfData (O.F.X hB hRR).toJoint (ThetaOne.paperAtomMap_paperBlockOf_surjective f1Cell)
  hεS0 := sfEps_nonneg _
  hεSt := tendsto_sfEps _
  hcS := sfData_c_nonneg _ _
  hrpm0 := sfRpm_nonneg _ _
  hfold := sfData_fold _ _
  hremS := sfData_rem _ _

/-- **Non-vacuity**: every `CompanionObligationsLP` gives a `CompanionObligationsSR` (forget `sf`,
its side conditions, `hfold` and `hremS`). So the new obligations are implied by LP's. -/
noncomputable def ofLP (O : CompanionObligationsLP hW hMR hFour hB hRR UpT) :
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

/-- Every `CompanionObligationsCG0` gives a `CompanionObligationsSR` (through LP's `ofCG0`). -/
noncomputable def ofCG0 (O : CompanionObligationsCG0 hW hMR hFour hB hRR UpT) :
    CompanionObligationsSR hW hMR hFour hB hRR UpT :=
  ofLP (CompanionObligationsLP.ofCG0 O)

/-- The round trip `ofLP ∘ toLP` is the identity (definitionally). -/
theorem ofLP_toLP (O : CompanionObligationsSR hW hMR hFour hB hRR UpT) : ofLP O.toLP = O := rfl

end CompanionObligationsSR

/-- **The rebased companion statement with `SF.hfold` and `SF.hrem` proved** (`thm:main` at
`ε = 10⁻⁵`): `s(N) ≤ C·N^{0.99999}` from the literature (L), the record table `UpT` (F) and the
obligations `O : CompanionObligationsSR`, in which the data `sf` of `SF` and its two open fields
are no longer assumed: `main_goal_rebased_lp` at `O.toLP`. -/
theorem main_goal_rebased_sr (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables)
    (O : CompanionObligationsSR hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR UpT) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  LargeSums.main_goal_rebased_lp hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR
    UpT O.toLP

end Main

end Sarkozy.SharpFirst
