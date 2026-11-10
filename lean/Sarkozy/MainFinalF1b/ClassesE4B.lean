module

public import Sarkozy.MainFinalF1b.ClassesB

@[expose] public section

/-!
# C10's class constructors without `ES.H`, `ES.hyπ` (F1P, after FA2's P2)

`paper/sections/11_comparison_proof.tex`, `cor:joint-closing`; `paper/sections/23_envelopes.tex`,
`thm:envelopes`(i); `paper/sections/24a_joint_mean.tex`, `prop:joint-middle-mean`.

* `ESInputsE4B D cd`: C10's `ESInputsE4` without `H` (`ConsistentInputs`), `Kπ`, `hK`, `hyπ`;
  `.toED : ClassEnergyDataB D cd` (`energy` from B11's operator steps, `energy_of_steps`;
  `v := u`).
* `MDInputsE4B ED`: C10's `MDInputsE4` at `ClassEnergyDataB` (the combined gate `AllocJB`);
  `.toMD := MeanDataJB.ofE4` (fields 44, 45 proved as by E4).
* **`ClassPartsE4B D`**: `cd`, `ES : ESInputsE4B`, `E1 : E1InputsAgg` (FA2 P1), `MD : MDInputsE4B`;
  **`ClassPartsE4B.jointBound : JointBound D targetLedger.jointConstant`**.
* `ClassPartsE4A.toB`: forgetting `H`, `Kπ`, `hK`, `hyπ` (the gate `AllocJ` is `AllocJB` with the
  same numbers, by `rfl`). So the new inputs are weaker than C10's.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MainFinalF1b

open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper Sarkozy.ClassData Sarkozy.MainFinal2
open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.JointClosing
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.Comparison (remainder energyMean)
open Sarkozy.BlockFrame
open Sarkozy.Param (Params)
open Sarkozy.PartVLaws (paperAtomMap)
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.GramBracketPaper

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

/-- **The inputs of the class energies without the unused evaluations** (`thm:envelopes`(i),
`cor:envelope-costs`, `lem:bracket-energy`): C10's `ESInputsE4` without `H`, `Kπ`, `hK`, `hyπ`
(FA2 P2). *Open*: `ops` (analytic), `upper` (analytic). -/
structure ESInputsE4B (D : TheoremCBlock.ComparisonData targetDecay paperM0 (paperAtomMap blockOf)
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
  /-- The upper prices of the diagonals, relative form (`lem:bracket-energy`). *Open*. -/
  upper : ∃ ε₃ : ℕ → ℝ, (∀ L, 0 ≤ ε₃ L) ∧ Tendsto ε₃ atTop (𝓝 0) ∧ ∃ c₃ : ℝ, 0 ≤ c₃ ∧
    ∃ r : ∀ L, Finset ℤ → Θ L → ℝ, (∀ L A j, 0 ≤ r L A j) ∧
    Param.AtCounterexamples (Params.ofDecay targetDecay) D.Y (fun L A =>
      ∀ j, Z L A j ≤ (u L j + ε₃ L * u L j) * D.Y L A + r L A j) ∧
    Param.AtCounterexamples (Params.ofDecay targetDecay) D.Y (fun L A =>
      ∑ j, (∑ i, wc L i j) * r L A j ≤ remainder c₃ L A)

attribute [instance] ESInputsE4B.ΘFintype

/-- The class energies of the inputs (`energy_of_steps` on B11's steps, `v := u`). -/
noncomputable def ESInputsE4B.toED {D : TheoremCBlock.ComparisonData targetDecay paperM0
    (paperAtomMap blockOf) paperTail paperPr paperH Chamber} {cd : ClassInputsPaper.ClassData D.CL}
    (S : ESInputsE4B D cd) : ClassEnergyDataB D cd where
  Θ := S.Θ
  Z := S.Z
  u := S.u
  wc := S.wc
  wc_nonneg := S.wc_nonneg
  ρ := S.ρ
  energy := energy_of_steps cd S.Θ S.Z S.wc S.ρ S.ops.toSteps
  v := S.u
  upper := S.upper

/-- **The inputs of E4's `MeanDataJ.ofE4` at `ClassEnergyDataB`** (`prop:joint-middle-mean`,
`cor:joint-closing`): C10's `MDInputsE4`, with the combined gate `AllocJB`. -/
structure MDInputsE4B {D : TheoremCBlock.ComparisonData targetDecay paperM0 (paperAtomMap blockOf)
    paperTail paperPr paperH Chamber} {cd : ClassInputsPaper.ClassData D.CL}
    (ED : ClassEnergyDataB D cd) where
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
  /-- **The combined gate** `Δ ≤ ∑ b u + 63(𝓔 − κ_L − ∑ w u)` (`cor:joint-closing`). *Open*. -/
  alloc : AllocJB ED fun L j => (diagB (lab L j) : ℝ)

/-- `MeanDataJB` (`MeanDataJB.ofE4`; fields 44, 45 proved). -/
noncomputable def MDInputsE4B.toMD {D : TheoremCBlock.ComparisonData targetDecay paperM0
    (paperAtomMap blockOf) paperTail paperPr paperH Chamber} {cd : ClassInputsPaper.ClassData D.CL}
    {ED : ClassEnergyDataB D cd} (M : MDInputsE4B ED) : MeanDataJB ED :=
  MeanDataJB.ofE4 ED M.lab M.hw M.N M.W M.Vv M.hW0 M.hVv M.hcard M.hwW M.hv0 M.hvV M.mean M.alloc

/-- **The class inputs without the unused evaluations, with the aggregate (E1).** 4 fields. -/
structure ClassPartsE4B (D : TheoremCBlock.ComparisonData targetDecay paperM0
    (paperAtomMap blockOf) paperTail paperPr paperH Chamber) where
  /-- The data of the classes (B10's `ClassData`: the classes `ι`, `cls` of `def:cp5`). *Open*
  (data). -/
  cd : ClassInputsPaper.ClassData D.CL
  /-- The class energies (B11's steps, the upper prices). -/
  ES : ESInputsE4B D cd
  /-- (E1) for the selections in no class, aggregate form (FA2 P1). -/
  E1 : E1InputsAgg D
  /-- The mean data, with the combined gate. -/
  MD : MDInputsE4B ES.toED

/-- **The joint bound `JB`** (`cor:joint-closing`, `eq:final-joint-closing`): `jointBound_allocJB`
through `MeanDataJB.jointBound`, with (E1) from `E1InputsAgg.toE1`. -/
theorem ClassPartsE4B.jointBound {D : TheoremCBlock.ComparisonData targetDecay paperM0
    (paperAtomMap blockOf) paperTail paperPr paperH Chamber} (C : ClassPartsE4B D) :
    JointBound D targetLedger.jointConstant :=
  C.MD.toMD.jointBound MainAnchor.card_chamber C.E1.toE1

/-- **C10's inputs give the new ones** (forgetting `H`, `Kπ`, `hK`, `hyπ`). -/
noncomputable def ClassPartsE4A.toB {D : TheoremCBlock.ComparisonData targetDecay paperM0
    (paperAtomMap blockOf) paperTail paperPr paperH Chamber} (C : ClassPartsE4A D) :
    ClassPartsE4B D where
  cd := C.cd
  ES :=
    { Θ := C.ES.Θ
      Z := C.ES.Z
      u := C.ES.u
      wc := C.ES.wc
      wc_nonneg := C.ES.wc_nonneg
      ρ := C.ES.ρ
      ops := C.ES.ops
      upper := C.ES.upper }
  E1 := C.E1
  MD :=
    { lab := C.MD.lab
      hw := C.MD.hw
      N := C.MD.N
      W := C.MD.W
      Vv := C.MD.Vv
      hW0 := C.MD.hW0
      hVv := C.MD.hVv
      hcard := C.MD.hcard
      hwW := C.MD.hwW
      hv0 := C.MD.hv0
      hvV := C.MD.hvV
      mean := C.MD.mean
      alloc := C.MD.alloc }

end Sarkozy.MainFinalF1b
