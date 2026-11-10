module

public import Sarkozy.ClassSlack.Main
public import Sarkozy.ClassSlack.MeanZero

@[expose] public section




open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.ClassSlack

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

/-- **The ledger's one-block mean credit is `0`** (RG, 8 November 2026). -/
theorem targetLedger_m₁_eq_zero : targetLedger.m₁ = 0 := rfl

/-- **`hm₁` is a theorem at the ledger's `m₁ = 0`** (`prop:record:mean-credit` with credit `0`,
`def:cp7`): `selMeanAt_zero`, read at `targetLedger.m₁` by `selMeanAt_ledger`. -/
theorem hm₁_proved {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
    (D : CD blockOf) (cd : ClassData D.CL) (Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ) :
    SelMean D cd (fun _ _ => 0) Zs := by
  have e : SelMeanAt targetLedger.m₁ D cd (fun _ _ => 0) Zs =
      SelMeanAt 0 D cd (fun _ _ => 0) Zs := by
    rw [targetLedger_m₁_eq_zero]
  exact (selMeanAt_ledger D cd _ Zs).mp (e.mpr (selMeanAt_zero D cd Zs))

/-- **The obligations of `main_goal_rebased_cg0`**: `CompanionObligationsCG` without `hm₁`
(proved at `m₁ = 0`, `hm₁_proved`). Every other field is a verbatim copy. -/
structure CompanionObligationsCG0 (hW : Target.Weil) (hMR : Target.MovingRoot)
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
  -- (D) The free data of (E1) and of `SF`
  /-- (D) (E1): the relative error, the constant and the remainders. -/
  εE : ℕ → ℝ
  cE : ℝ
  r0 : E1R0 (F.X hB hRR).data
  rE : E1R (F.X hB hRR).data
  /-- (D) `SF`: the sharp decompositions `dec` of the differences (`lem:sharp-first`), the
  relative error `ε`, the constant `c` and the remainders `rp`, `rm` of the folded energies. -/
  sf : SFData (F.X hB hRR).toJoint.data
  /-- (D) The constant of the four `rch` summations. -/
  c₂ : ℝ
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
  /-- (S) `SF`: `0 ≤ ε → 0`, `c ≥ 0`, nonnegative remainders; `c₂ ≥ 0`. -/
  hεS0 : ∀ L, 0 ≤ sf.ε L
  hεSt : Tendsto sf.ε atTop (𝓝 0)
  hcS : 0 ≤ sf.c
  hrpm0 : ∀ L A σ j f, 0 ≤ sf.rp L A σ j f ∧ 0 ≤ sf.rm L A σ j f
  hc₂ : 0 ≤ c₂
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
  /-- **(R)** `SF.hfold` (`prop:record:density-structured` on the folded energies of
  `lem:record:folded-energy`): `SFFold`. *Open*. -/
  hfold : SFFold (F.X hB hRR).toJoint.data sf.dec sf.ε sf.rp sf.rm
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
  /-- **(C)** `SF.hrem` (`lem:sharp-first`, the error terms): `SFRem`. *Open*. -/
  hremS : SFRem (F.X hB hRR).toJoint.data sf.c sf.rp sf.rm
  /-- **(C)** SH2: the summation of the per-term remainders `rchFixL` (`Sh.fixM.hr2L`;
  `lem:sharp-first`, `lem:record:density-dc`, `lem:record:density-lp`). *Open*. -/
  fixL : RchSumPTFixL (BlockAnchor.index_coprime_block (F.X hB hRR).toJoint.data)
    (F.X hB hRR).toJoint.data paper_pairwise sf.dec c₂
  /-- **(C)** SH2: the same for `rchFixR` (`Sh.fixM.hr2R`). *Open*. -/
  fixR : RchSumPTFixR (BlockAnchor.index_coprime_block (F.X hB hRR).toJoint.data)
    (F.X hB hRR).toJoint.data paper_pairwise sf.dec c₂
  /-- **(C)** SH2: the same for `rchEnvL` (`Sh.envM.hr2L`). *Open*. -/
  envL : RchSumPTEnvL (BlockAnchor.index_coprime_block (F.X hB hRR).toJoint.data)
    (F.X hB hRR).toJoint.data paper_pairwise sf.dec c₂
  /-- **(C)** SH2: the same for `rchEnvR` (`Sh.envM.hr2R`). *Open*. -/
  envR : RchSumPTEnvR (BlockAnchor.index_coprime_block (F.X hB hRR).toJoint.data)
    (F.X hB hRR).toJoint.data paper_pairwise sf.dec c₂

attribute [instance] CompanionObligationsCG0.instFK CompanionObligationsCG0.instDK
  CompanionObligationsCG0.instFLt CompanionObligationsCG0.instDLt

namespace CompanionObligationsCG0

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {hB : Target.BMOR} {hRR : Target.ThetaSmallRR} {UpT : UpperRecordTables}

/-- **The CG obligations**, with `hm₁ := hm₁_proved …`. -/
noncomputable def toCG (O : CompanionObligationsCG0 hW hMR hFour hB hRR UpT) :
    CompanionObligationsCG hW hMR hFour hB hRR UpT where
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
  sf := O.sf
  c₂ := O.c₂
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
  hεS0 := O.hεS0
  hεSt := O.hεSt
  hcS := O.hcS
  hrpm0 := O.hrpm0
  hc₂ := O.hc₂
  hC := O.hC
  hCv := O.hCv
  hup := O.hup
  hsub := O.hsub
  hfold := O.hfold
  ops := O.ops
  hρ := O.hρ
  hcomp := O.hcomp
  hX := O.hX
  hcoup := O.hcoup
  hremE := O.hremE
  hremS := O.hremS
  fixL := O.fixL
  fixR := O.fixR
  envL := O.envL
  envR := O.envR
  hm₁ := hm₁_proved _ O.cd O.Zs

/-- **Non-vacuity**: every `CompanionObligationsCG` gives a `CompanionObligationsCG0` by forgetting
`hm₁` (so `CG0` is satisfiable whenever `CG` is, and with `CompanionObligationsCG.ofND`, whenever
ND's obligations are at `τ ≤ 13/625`). -/
noncomputable def ofCG (O : CompanionObligationsCG hW hMR hFour hB hRR UpT) :
    CompanionObligationsCG0 hW hMR hFour hB hRR UpT where
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
  sf := O.sf
  c₂ := O.c₂
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
  hεS0 := O.hεS0
  hεSt := O.hεSt
  hcS := O.hcS
  hrpm0 := O.hrpm0
  hc₂ := O.hc₂
  hC := O.hC
  hCv := O.hCv
  hup := O.hup
  hsub := O.hsub
  hfold := O.hfold
  ops := O.ops
  hρ := O.hρ
  hcomp := O.hcomp
  hX := O.hX
  hcoup := O.hcoup
  hremE := O.hremE
  hremS := O.hremS
  fixL := O.fixL
  fixR := O.fixR
  envL := O.envL
  envR := O.envR

end CompanionObligationsCG0

/-- **The rebased companion statement with no mean input** (`thm:main` at `ε = 10⁻⁵`):
`s(N) ≤ C·N^{0.99999}` from the literature (L), the record table `UpT` (F) and the obligations
`O : CompanionObligationsCG0` (no `hmean`, `hres`, `hXm`, `μK`, `hm`/`hm₁`; `τ ≤ 13/625`), at the
ledger with `m₁ = 0`: `main_goal_rebased_cg` at `O.toCG`. -/
theorem main_goal_rebased_cg0 (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables)
    (O : CompanionObligationsCG0 hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR UpT) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_rebased_cg hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR UpT O.toCG

end Sarkozy.ClassSlack
