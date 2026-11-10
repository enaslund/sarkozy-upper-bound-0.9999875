module

public import Sarkozy.MainFinalJ.All

@[expose] public section








open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MainFinalF1b

open Sarkozy.EnvelopeInputsBlock Sarkozy.EnvelopeInputs
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice Sarkozy.Structured ReflectionCut

section E1

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **The inputs of (E1) off the classes, in the paper's aggregate form** (`def:robust`; G1's
`envelopeBoundNonneg_of_coupledPieces`): the subset terms `hsub` (`lem:bracket-energy`, "`μ` off a
selected set") and the coupled envelope pieces `hcoup` (`lem:sharp-first`,
`lem:density:coupled`), each with a free nonnegative remainder (`r0`, `r`), and the **summed
remainder** `hrem` (`lem:record:density-lp` for the large unions, the summed errors of
`prop:record:density-structured` for the small ones; `10_comparison_lemmas.tex` ll. 126–140).
*Hypotheses* (analytic): `hsub`, `hcoup`, `hrem`. 12 fields. -/
structure E1InputsAgg (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) where
  /-- The relative error. Data, with `0 ≤ εE → 0`. -/
  εE : ℕ → ℝ
  hε0 : ∀ L, 0 ≤ εE L
  hεt : Tendsto εE atTop (𝓝 0)
  /-- The constant of the summed remainder. Data, `≥ 0`. -/
  cE : ℝ
  hcE : 0 ≤ cE
  /-- The per-term remainders of the subset terms and of the coupled pieces. Data. -/
  r0 : ∀ L, Finset ℤ → Choice (D.CL.T L) → (BlockAtom Bk J L → Bool) → ℝ
  r : ∀ L, Finset ℤ → (ω : Choice (D.CL.T L)) → (∀ b, Option (D.FS.Ib L b)) → D.FS.Tag →
    (∀ b, CEPiece D L b) → ℝ
  /-- The subset terms (`lem:bracket-energy`). *Open* (analytic). -/
  hsub : Param.AtCounterexamples (Params.ofDecay a) D.Y
    (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
    ∀ f : BlockAtom Bk J L → Bool,
    |diagonalIntegral (tensorLaw fun b => if f b then
    (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i)
    else entryFactor (D.R.law p L b) (D.CL.D L b) (ω b)) (blockLift m₀ blk p L A)| ≤
    ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
    D.Y L A) * ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) +
    r0 L A ω f)
  /-- The coupled envelope pieces (`lem:sharp-first`, `lem:density:coupled`). *Open*
  (analytic). -/
  hcoup : Param.AtCounterexamples (Params.ofDecay a) D.Y
    (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
    ∀ σ : (∀ b, Option (D.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
    1 ≤ countVec (D.FS.tag L) σ j → ∀ f : (∀ b, CEPiece D L b),
    (∀ b, ecpieceCoef D L ω σ j b (f b) ≠ 0) →
    |diagonalIntegral (tensorLaw fun b => ecpieceK D L ω b (f b)) (blockLift m₀ blk p L A)| ≤
    (∏ b, ecpieceG D L ω b (f b)) * ((1 + εE L) * D.Y L A) + r L A ω σ j f)
  /-- **The summed remainder** (`lem:record:density-lp`, `def:robust`). *Open* (analytic). -/
  hrem : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
      monomial (D.CL.πt L) ω *
        (∑ f, r0 L A ω f +
          ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
            ∑ j, ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * r L A ω σ j f) ≤
        remainder cE L A)
  /-- The remainders are nonnegative (they bound absolute values). Side conditions. -/
  hr0 : ∀ L A ω σ j f, 0 ≤ r L A ω σ j f
  hs0 : ∀ L A ω f, 0 ≤ r0 L A ω f

omit [DecidableEq P] in
/-- **(E1) off the classes from the aggregate inputs** (G1's
`envelopeBoundNonneg_of_coupledPieces`). -/
theorem E1InputsAgg.toE1 {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    (I : E1InputsAgg D) : D.EnvelopeBoundNonneg :=
  envelopeBoundNonneg_of_coupledPieces D I.εE I.hε0 I.hεt I.hcE I.r0 I.r I.hsub I.hcoup I.hrem
    I.hr0 I.hs0

end E1

/-! ## The class inputs with the aggregate (E1) -/

open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper Sarkozy.MainFinal2 Sarkozy.ClassData
open Sarkozy.TheoremCBlock Sarkozy.JointClosing
open Sarkozy.PartVLaws (paperAtomMap)
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.GramBracketPaper
open Sarkozy.MainFinalJ (ESInputsE4 MDInputsE4)

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

/-- **E4's `ClassParts2J` with the aggregate (E1)** (`cor:joint-closing`). 4 fields. -/
structure ClassParts2JA (D : TheoremCBlock.ComparisonData targetDecay paperM0
    (paperAtomMap blockOf) paperTail paperPr paperH Chamber) where
  cd : ClassInputsPaper.ClassData D.CL
  ES : ClassEnergySteps D cd
  /-- (E1) for the selections in no class, aggregate form. -/
  E1 : E1InputsAgg D
  MD : MeanDataJ ES.toED

/-- **The joint bound `JB`** (`cor:joint-closing`, `eq:final-joint-closing`; E4's
`MeanDataJ.jointBound` with (E1) from `E1InputsAgg.toE1`). -/
theorem ClassParts2JA.jointBound {D : TheoremCBlock.ComparisonData targetDecay paperM0
    (paperAtomMap blockOf) paperTail paperPr paperH Chamber} (C : ClassParts2JA D) :
    JointBound D targetLedger.jointConstant :=
  C.MD.jointBound MainAnchor.card_chamber C.E1.toE1

/-- **C10's `ClassPartsE4` with the aggregate (E1).** 4 fields. -/
structure ClassPartsE4A (D : TheoremCBlock.ComparisonData targetDecay paperM0
    (paperAtomMap blockOf) paperTail paperPr paperH Chamber) where
  /-- The data of the classes (B10's `ClassData`). *Open* (data). -/
  cd : ClassInputsPaper.ClassData D.CL
  /-- The class energies, through E4's constructor. -/
  ES : ESInputsE4 D cd
  /-- (E1) for the selections in no class, aggregate form (FA2 P1). -/
  E1 : E1InputsAgg D
  /-- The mean data, through E4's constructor, with the combined gate. -/
  MD : MDInputsE4 ES.toES.toED

/-- `ClassParts2JA` from E4's constructors. -/
noncomputable def ClassPartsE4A.toJA {D : TheoremCBlock.ComparisonData targetDecay paperM0
    (paperAtomMap blockOf) paperTail paperPr paperH Chamber} (C : ClassPartsE4A D) :
    ClassParts2JA D where
  cd := C.cd
  ES := C.ES.toES
  E1 := C.E1
  MD := C.MD.toMD

end Sarkozy.MainFinalF1b
