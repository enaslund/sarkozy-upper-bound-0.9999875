module

public import Sarkozy.ClassData.Parts

@[expose] public section

/-!
# The class inputs with the combined gate and E4's closures

`paper/sections/11_comparison_proof.tex`, `cor:joint-closing`; `paper/sections/23_envelopes.tex`,
`thm:envelopes`(i); `paper/sections/24a_joint_mean.tex`, `prop:joint-middle-mean`.

**`ClassPartsE4 D`**: E4's `ClassParts2J D` (K2's `ClassParts2` with the combined allocation gate
`AllocJ` in place of `alloc`, and without `PD`), with its two sub-bundles given by the arguments of
E4's constructors:

* `ESInputsE4` → `ClassEnergySteps` by `ClassEnergySteps.ofE4`: K2's field 41 (`consistent`) from
  `ConsistentInputs` (the numerical gate `classCost ≤ C_n` kernel-checked by E4), field 42 (`errw`)
  from the price comparison `hyπ`, with `v = u` and `errK = 3 · eUhi · K_π`;
* `MDInputsE4` → `MeanDataJ` by `MeanDataJ.ofE4`: field 44 (`hV`) from uniform bounds, field 45
  (`resid`) proved along the paper's labelling (192 gates kernel-checked by E4), field 46 in the
  combined form `AllocJ`.

`ClassPartsE4.toJ : ClassParts2J D`.
-/

open Filter Finset
open scoped Topology

namespace Sarkozy.MainFinalJ

open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper Sarkozy.MainFinal2 Sarkozy.ClassData
open Sarkozy.TheoremC Sarkozy.TheoremCBlock
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.Comparison (remainder energyMean)
open Sarkozy.BlockFrame
open Sarkozy.Param (Params)
open Sarkozy.PartVLaws (paperAtomMap)
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.CancellationSteps

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

/-- **The inputs of E4's `ClassEnergySteps.ofE4`** (`thm:envelopes`(i), `cor:envelope-costs`,
`lem:bracket-energy`): the diagonals and their prices (data), B11's operator steps `ops`, the
consistency inputs `H` (field 41), the price comparison `hyπ` (field 42) and the upper prices
`upper` (relative form, `v = u`). -/
structure ESInputsE4 (D : TheoremCBlock.ComparisonData targetDecay paperM0 (paperAtomMap blockOf)
    paperTail paperPr paperH Chamber) (cd : ClassInputsPaper.ClassData D.CL) where
  /-- The labelled positive diagonals. Data. -/
  Θ : ℕ → Type
  [ΘFintype : ∀ L, Fintype (Θ L)]
  /-- Their energies and upper prices. Data. -/
  Z : ∀ L, Finset ℤ → Θ L → ℝ
  u : ∀ L, Θ L → ℝ
  /-- The class weights on the diagonals. Data. -/
  wc : ∀ L, cd.ι L → Θ L → ℝ
  wc_nonneg : ∀ L i j, 0 ≤ wc L i j
  /-- The remainders. Data. -/
  ρ : ∀ L, Choice (D.CL.T L) → ℝ
  /-- B11's operator steps (`thm:envelopes`(i)). *Open* (analytic). -/
  ops : ClassStepsOps cd Θ Z wc ρ
  /-- The consistency inputs (K2's field 41 without its numerical gate). *Open* (analytic). -/
  H : ConsistentInputs cd Θ wc u ρ
  /-- The price constant `K_π`. Data. -/
  Kπ : ℝ
  hK : 0 ≤ Kπ
  /-- `mono(y^arm)_ω ≤ K_π π_ω` on the degree classes (K2's field 42 reduced). *Open*. -/
  hyπ : ∀ L (n : {n // n ∈ cd.N}), ∀ ω ∈ cd.clsSel L (.inl n),
    mono (cd.yarm L) (selMono ω) ≤ Kπ * monomial (D.CL.π L) ω
  /-- The upper prices of the diagonals, relative form (`lem:bracket-energy`). *Open*. -/
  upper : ∃ ε₃ : ℕ → ℝ, (∀ L, 0 ≤ ε₃ L) ∧ Tendsto ε₃ atTop (𝓝 0) ∧ ∃ c₃ : ℝ, 0 ≤ c₃ ∧
    ∃ r : ∀ L, Finset ℤ → Θ L → ℝ, (∀ L A j, 0 ≤ r L A j) ∧
    Param.AtCounterexamples (Params.ofDecay targetDecay) D.Y (fun L A =>
      ∀ j, Z L A j ≤ (u L j + ε₃ L * u L j) * D.Y L A + r L A j) ∧
    Param.AtCounterexamples (Params.ofDecay targetDecay) D.Y (fun L A =>
      ∑ j, (∑ i, wc L i j) * r L A j ≤ remainder c₃ L A)

attribute [instance] ESInputsE4.ΘFintype

/-- K2's `ClassEnergySteps` (E4's `ofE4`; fields 41, 42 from `H`, `hyπ`). -/
noncomputable def ESInputsE4.toES {D : TheoremCBlock.ComparisonData targetDecay paperM0
    (paperAtomMap blockOf) paperTail paperPr paperH Chamber} {cd : ClassInputsPaper.ClassData D.CL}
    (S : ESInputsE4 D cd) : ClassEnergySteps D cd :=
  ClassEnergySteps.ofE4 cd S.Θ S.Z S.u S.wc S.wc_nonneg S.ρ S.ops S.H S.Kπ S.hK S.hyπ S.upper

/-- **The inputs of E4's `MeanDataJ.ofE4`** (`prop:joint-middle-mean`, `cor:joint-closing`): a
labelling of the diagonals by `PaperDiag`, uniform bounds, the mean credit (J2) and the combined
gate `AllocJ`. -/
structure MDInputsE4 {D : TheoremCBlock.ComparisonData targetDecay paperM0 (paperAtomMap blockOf)
    paperTail paperPr paperH Chamber} {cd : ClassInputsPaper.ClassData D.CL}
    (ED : ClassEnergyData D cd) where
  /-- The labelling of the diagonals by the paper's diagonal types. Data. -/
  lab : ∀ L, ED.Θ L → PaperDiag
  /-- The weights are at least the paper's. Side condition. -/
  hw : ∀ L j, (diagW (lab L j) : ℝ) ≤ ED.w L j
  /-- Uniform bounds. Data with side conditions. -/
  N : ℕ
  W : ℝ
  Vv : ℝ
  hW0 : 0 ≤ W
  hVv : 0 ≤ Vv
  hcard : ∀ L, Fintype.card (ED.Θ L) ≤ N
  hwW : ∀ L j, ED.w L j ≤ W
  hv0 : ∀ L j, 0 ≤ ED.v L j
  hvV : ∀ L j, ED.v L j ≤ Vv
  /-- The mean credit (J2, `prop:record:mean-credit`). *Open* (analytic). -/
  mean : ∃ ε₂ : ℕ → ℝ, Tendsto ε₂ atTop (𝓝 0) ∧ ∃ c₂ : ℝ, 0 ≤ c₂ ∧
    Param.AtCounterexamples (Params.ofDecay targetDecay) D.Y fun L A =>
      (targetLedger.m₁ - ε₂ L) * D.Y L A + ∑ j, (diagB (lab L j) : ℝ) * ED.Z L A j -
          remainder c₂ L A ≤
        (energyMean (blockLift paperM0 (paperAtomMap blockOf) paperTail) D.ME.ML L A +
          energyMean (blockLift paperM0 (paperAtomMap blockOf) paperTail) D.ME.MR L A) / 2
  /-- **The combined gate** `Δ ≤ ∑ b u + 63(𝓔 − κ_L − ∑ w u)` (`cor:joint-closing`; E4's
  `AllocJ`, in place of K2's field 46). *Open*. -/
  alloc : AllocJ ED.toCE fun L j => (diagB (lab L j) : ℝ)

/-- E4's `MeanDataJ` (`MeanDataJ.ofE4`; fields 44, 45 proved). -/
noncomputable def MDInputsE4.toMD {D : TheoremCBlock.ComparisonData targetDecay paperM0
    (paperAtomMap blockOf) paperTail paperPr paperH Chamber} {cd : ClassInputsPaper.ClassData D.CL}
    {ED : ClassEnergyData D cd} (M : MDInputsE4 ED) : MeanDataJ ED :=
  MeanDataJ.ofE4 ED M.lab M.hw M.N M.W M.Vv M.hW0 M.hVv M.hcard M.hwW M.hv0 M.hvV M.mean M.alloc

/-- **The class inputs with the combined gate and E4's closures.** 4 fields. -/
structure ClassPartsE4 (D : TheoremCBlock.ComparisonData targetDecay paperM0
    (paperAtomMap blockOf) paperTail paperPr paperH Chamber) where
  /-- The data of the classes (B10's `ClassData`). *Open* (data). -/
  cd : ClassInputsPaper.ClassData D.CL
  /-- The class energies, through E4's constructor. -/
  ES : ESInputsE4 D cd
  /-- (E1) for the selections in no class (G1). *Open* (analytic). -/
  E1 : E1Inputs D
  /-- The mean data, through E4's constructor, with the combined gate. -/
  MD : MDInputsE4 ES.toES.toED

/-- E4's `ClassParts2J`. -/
noncomputable def ClassPartsE4.toJ {D : TheoremCBlock.ComparisonData targetDecay paperM0
    (paperAtomMap blockOf) paperTail paperPr paperH Chamber} (C : ClassPartsE4 D) :
    ClassParts2J D where
  cd := C.cd
  ES := C.ES.toES
  E1 := C.E1
  MD := C.MD.toMD

end Sarkozy.MainFinalJ
