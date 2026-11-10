module

public import Sarkozy.LargeSums.Env
public import Sarkozy.SharpSums.MainSum

@[expose] public section

/-!
# The rebased companion statement with the large-piece sums proved (`main_goal_rebased_lp`)

LP, 8 November 2026. SUM's four large-piece sums `LargeSumPT*` (`lem:record:density-lp` at the
folded pieces, the last open part of SH2's `r₂` summations) are proved for every comparison datum
on the paper's tails (`LargeSums.Fix`, `LargeSums.Env`). Here:

* **`largeSums_all`**: one constant `c_L ≥ 0` for all four sums (the largest of the four);
* **`sumInputsOfSF`**, **`sharpBaseOfSF`**: SUM's `SharpSumInputsL D` and SH2's
  `SharpBaseInputsPT D` from `SF` alone. So the `r₂` summations of `lem:sharp-first` need nothing
  beyond `SF` (`SF.hfold`, `SF.hrem`);
* **`CompanionObligationsLP`**: `CompanionObligationsSUM` without `cL, hcL, largeFixL, largeFixR,
  largeEnvL, largeEnvR` (54 fields, of which 11 are novel core (C) instead of 15);
* `toSUM` (the four sums from `largeSums_all`), **`ofSUM`** (non-vacuity: forget the six fields),
  `ofCG0`;
* **`main_goal_rebased_lp`**: `Target.SarkozyBound TargetGoal.epsGoal`.

The constructor uses only `0 ≤ a` at the data's `a = targetDecay` and the parity condition of the
paper's exponents (`parity_blockPaperStandingAt`); it does not read the ledger.
-/

namespace Sarkozy.LargeSums

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps Sarkozy.BlockAnchor Sarkozy.DensityChain2
  Sarkozy.DensityFibre Sarkozy.SharpSums
open Sarkozy.Param (Params)

section General

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **The four large-piece sums with one constant** (`lem:record:density-lp` at the folded pieces
of `fixC` and `envC`): for every comparison datum on the paper's tails with `a ≥ 0` and the
parity condition. -/
theorem largeSums_all (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) :
    ∃ c : ℝ, 0 ≤ c ∧ LargeSumPTFixL hcop D hpair dec c ∧ LargeSumPTFixR hcop D hpair dec c ∧
      LargeSumPTEnvL hcop D hpair dec c ∧ LargeSumPTEnvR hcop D hpair dec c := by
  obtain ⟨c1, h1, f1⟩ := largeSumPTFixL_proved hcop D hpair dec ha hpar
  obtain ⟨c2, h2, f2⟩ := largeSumPTFixR_proved hcop D hpair dec ha hpar
  obtain ⟨c3, h3, f3⟩ := largeSumPTEnvL_proved hcop D hpair dec ha hpar
  obtain ⟨c4, h4, f4⟩ := largeSumPTEnvR_proved hcop D hpair dec ha hpar
  refine ⟨max (max c1 c2) (max c3 c4), le_max_of_le_left (le_max_of_le_left h1), ?_, ?_, ?_, ?_⟩
  · unfold LargeSumPTFixL at f1 ⊢
    exact atCex_le_mono_S (le_max_of_le_left (le_max_left _ _)) f1
  · unfold LargeSumPTFixR at f2 ⊢
    exact atCex_le_mono_S (le_max_of_le_left (le_max_right _ _)) f2
  · unfold LargeSumPTEnvL at f3 ⊢
    exact atCex_le_mono (le_max_of_le_right (le_max_left _ _)) f3
  · unfold LargeSumPTEnvR at f4 ⊢
    exact atCex_le_mono (le_max_of_le_right (le_max_right _ _)) f4

end General

section Target

open Sarkozy.PartV Sarkozy.JointClosing Sarkozy.BlockSpecPaper Sarkozy.MainCombined
  Sarkozy.MainCombined2 Sarkozy.SharpBase Sarkozy.SharpBase2
open Sarkozy.EnvelopeEnergiesPaper (paper_pairwise)
open Sarkozy.CancellationSteps (PaperJ0)

/-- The four large-piece sums at the paper's data, with one constant. -/
theorem largeSums_target {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
    {hW : Target.Weil} (D : JointBlockDataTarget blockOf hW)
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D.data L) :
    ∃ c : ℝ, 0 ≤ c ∧
      LargeSumPTFixL (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise dec c ∧
      LargeSumPTFixR (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise dec c ∧
      LargeSumPTEnvL (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise dec c ∧
      LargeSumPTEnvR (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise dec c :=
  largeSums_all _ D.data paper_pairwise dec TargetLedger.targetDecay_nonneg
    (DensityChain2.parity_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)

/-- **SUM's `SharpSumInputsL` from `SF` alone**: the four large-piece sums are proved
(`largeSums_target`). -/
noncomputable def sumInputsOfSF {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
    {hW : Target.Weil} {D : JointBlockDataTarget blockOf hW}
    (SF : ThetaOne.SharpFirstBaseInputs D.data) : SharpSumInputsL D where
  SF := SF
  cL := Classical.choose (largeSums_target D SF.dec)
  hcL := (Classical.choose_spec (largeSums_target D SF.dec)).1
  largeFixL := (Classical.choose_spec (largeSums_target D SF.dec)).2.1
  largeFixR := (Classical.choose_spec (largeSums_target D SF.dec)).2.2.1
  largeEnvL := (Classical.choose_spec (largeSums_target D SF.dec)).2.2.2.1
  largeEnvR := (Classical.choose_spec (largeSums_target D SF.dec)).2.2.2.2

/-- **SH2's `SharpBaseInputsPT` from `SF` alone** (`lem:sharp-first`, the error-term
summation): the chain² and cross parts by SUM, the large pieces by `largeSums_target`. -/
noncomputable def sharpBaseOfSF {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
    {hW : Target.Weil} {D : JointBlockDataTarget blockOf hW}
    (SF : ThetaOne.SharpFirstBaseInputs D.data) : SharpBaseInputsPT D :=
  (sumInputsOfSF SF).toSharpBaseInputsPT

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

/-- **The obligations of `main_goal_rebased_lp`**: `CompanionObligationsSUM` without the
constant `c_L` and SUM's four large-piece sums, which are proved (`largeSums_target`). Every other
field is a verbatim copy. 54 fields. -/
structure CompanionObligationsLP (hW : Target.Weil) (hMR : Target.MovingRoot)
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
  /-- (S) `SF`: `0 ≤ ε → 0`, `c ≥ 0`, nonnegative remainders. -/
  hεS0 : ∀ L, 0 ≤ sf.ε L
  hεSt : Tendsto sf.ε atTop (𝓝 0)
  hcS : 0 ≤ sf.c
  hrpm0 : ∀ L A σ j f, 0 ≤ sf.rp L A σ j f ∧ 0 ≤ sf.rm L A σ j f
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

attribute [instance] CompanionObligationsLP.instFK CompanionObligationsLP.instDK
  CompanionObligationsLP.instFLt CompanionObligationsLP.instDLt

namespace CompanionObligationsLP

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {hB : Target.BMOR} {hRR : Target.ThetaSmallRR} {UpT : UpperRecordTables}

/-- The four large-piece sums at the obligations' data, with one constant. -/
theorem large (O : CompanionObligationsLP hW hMR hFour hB hRR UpT) :
    ∃ c : ℝ, 0 ≤ c ∧
      LargeSumPTFixL (BlockAnchor.index_coprime_block (O.F.X hB hRR).toJoint.data)
        (O.F.X hB hRR).toJoint.data paper_pairwise O.sf.dec c ∧
      LargeSumPTFixR (BlockAnchor.index_coprime_block (O.F.X hB hRR).toJoint.data)
        (O.F.X hB hRR).toJoint.data paper_pairwise O.sf.dec c ∧
      LargeSumPTEnvL (BlockAnchor.index_coprime_block (O.F.X hB hRR).toJoint.data)
        (O.F.X hB hRR).toJoint.data paper_pairwise O.sf.dec c ∧
      LargeSumPTEnvR (BlockAnchor.index_coprime_block (O.F.X hB hRR).toJoint.data)
        (O.F.X hB hRR).toJoint.data paper_pairwise O.sf.dec c :=
  largeSums_target (O.F.X hB hRR).toJoint O.sf.dec

/-- **The SUM obligations**: `c_L` and the four large-piece sums from `largeSums_target`. -/
noncomputable def toSUM (O : CompanionObligationsLP hW hMR hFour hB hRR UpT) :
    CompanionObligationsSUM hW hMR hFour hB hRR UpT where
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
  cL := Classical.choose O.large
  hcL := (Classical.choose_spec O.large).1
  largeFixL := (Classical.choose_spec O.large).2.1
  largeFixR := (Classical.choose_spec O.large).2.2.1
  largeEnvL := (Classical.choose_spec O.large).2.2.2.1
  largeEnvR := (Classical.choose_spec O.large).2.2.2.2

/-- **Non-vacuity**: every `CompanionObligationsSUM` gives a `CompanionObligationsLP` (forget
`c_L` and the four large-piece sums). So the new obligations are implied by SUM's. -/
noncomputable def ofSUM (O : CompanionObligationsSUM hW hMR hFour hB hRR UpT) :
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
  sf := O.sf
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

/-- Every `CompanionObligationsCG0` gives a `CompanionObligationsLP` (through SUM's `ofCG0`). -/
noncomputable def ofCG0 (O : CompanionObligationsCG0 hW hMR hFour hB hRR UpT) :
    CompanionObligationsLP hW hMR hFour hB hRR UpT :=
  ofSUM (CompanionObligationsSUM.ofCG0 O)

end CompanionObligationsLP

/-- **The rebased companion statement with the large-piece sums proved** (`thm:main` at
`ε = 10⁻⁵`): `s(N) ≤ C·N^{0.99999}` from the literature (L), the record table `UpT` (F) and the
obligations `O : CompanionObligationsLP`, in which SUM's four large-piece sums are no longer
assumed: `main_goal_rebased_sum` at `O.toSUM`. -/
theorem main_goal_rebased_lp (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables)
    (O : CompanionObligationsLP hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR UpT) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_rebased_sum hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR UpT O.toSUM

end Main

end Sarkozy.LargeSums
