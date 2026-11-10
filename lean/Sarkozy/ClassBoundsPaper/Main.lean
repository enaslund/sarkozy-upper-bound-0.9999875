module

public import Sarkozy.JointClosing.Main
public import Sarkozy.ClassBoundsPaper.JointClasses

@[expose] public section

/-!
# The main statement at `a_T` in the joint form, with `JB` reduced to the class bounds

B3's `JointClosing.main_target_paper_block_joint` with its obligation `JB`
(`JointBound Dv.data targetLedger.jointConstant`, the hypothesis of `cor:joint-closing`) replaced by
`jointBound_target_of_classEnergy` from five labelled inputs:

* `CI : ClassInputs Dv.data.CL` — the classes of (CP5) (`def:cp5`; the sixteen envelope classes of
  `cor:envelope-costs` as 49 degree vectors, and the variance classes of `cor:variance:final`), with
  their robust evaluated class bounds (`ClassInputs.robust`; `ClassInputs.ofFamilies` builds it from
  the envelope and variance families). It is also the `CB` of the separate route
  (`ClassInputs.toClassBounds`, `ClassInputs.robustNonneg`);
* `PD : PolynomialData CI` — the upper data of the class polynomial (`prop:closing-data`(b), (d);
  the variance credit `D_var`, `cor:variance:final`(iv)); with `hB` it gives
  `Ψ(π̂, ŷ) ≤ targetLedger.E`, the sixteen class savings being kernel-checked (`paperSavings_ge`);
* `CE : ClassEnergyInputs Dv.data CI` — the class bounds at energy level on labelled positive
  diagonals (`thm:envelopes`(i), `cor:envelope-costs`), consistent with `CI`'s evaluated bounds;
* `E1 : Dv.data.EnvelopeBoundNonneg` — (E1) for the selections in no class (`def:robust`);
* `MA : MeanAllocation Dv.data CE` — the mean expansion with the one-block credit `m₁` and the
  retained energies on the shared diagonals (`prop:record:mean-credit`), the upper prices of the
  diagonals (`lem:bracket-energy`), the residual gates `b ≤ 63 w` (`cert:four-routes-closing`) and
  the joint mean allocations `∑ b u ≥ 64(Δ_mid + Δ_u − R_u)` (`prop:joint-middle-mean`,
  `prop:joint-upper-mean`).

**Count.** B3's joint statement has 13 obligations (block data `spec`, `Gi`, `CL`, `ME`, `SM`;
finals `hB`, `hL₀`, `hT`, `hSA`, `JB`, `SF`, `fix`, `env`). Here `JB` is replaced by the five
inputs `CI`, `PD`, `CE`, `E1`, `MA`: `B4JointObligationsTarget` has 13 fields (the data `Dv` and
12 final obligations), and with the five open block-data fields of `Dv` there are 17 obligations,
each a labelled input; `hB` is used both by B3's endgame and through `PD` (`B ≤ B'`).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.ClassBoundsPaper

open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.JointClosing
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper
open Sarkozy.PartVLaws (PaperBlockSpec TailInputsCorr paperAtomMap)

section Mean

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **The joint mean allocation on the diagonals of the class envelopes** (`cor:joint-closing`).
*Hypotheses*, each labelled. -/
structure MeanAllocation (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    {CI : ClassInputs D.CL} (CE : ClassEnergyInputs D CI) where
  /-- The retained mean coefficients on the shared diagonals. -/
  b : ∀ L, CE.Θ L → ℝ
  /-- The error weights of the upper prices. -/
  v : ∀ L, CE.Θ L → ℝ
  /-- (J2) **The mean expansion** (`prop:record:mean-credit`, Steps 1–2): the one-block credit
  `m₁` and the retained energies `b_j Z_j`, robustly. -/
  mean : ∃ ε₂ : ℕ → ℝ, Tendsto ε₂ atTop (𝓝 0) ∧ ∃ c₂ : ℝ, 0 ≤ c₂ ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
      (targetLedger.m₁ - ε₂ L) * D.Y L A + ∑ j, b L j * CE.Z L A j - remainder c₂ L A ≤
        (energyMean (blockLift m₀ blk p) D.ME.ML L A +
          energyMean (blockLift m₀ blk p) D.ME.MR L A) / 2
  /-- (J3) **The upper prices of the shared diagonals** (`lem:bracket-energy`, (E1)), robustly,
  with residual-weighted remainders. -/
  upper : ∃ ε₃ : ℕ → ℝ, (∀ L, 0 ≤ ε₃ L) ∧ Tendsto ε₃ atTop (𝓝 0) ∧ ∃ V c₃ : ℝ, 0 ≤ c₃ ∧
    (∀ L, ∑ j, (63 * CE.w L j - b L j) * v L j ≤ V) ∧ ∃ r : ∀ L, Finset ℤ → CE.Θ L → ℝ,
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ j, CE.Z L A j ≤ (CE.u L j + ε₃ L * v L j) * D.Y L A + r L A j) ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∑ j, (63 * CE.w L j - b L j) * r L A j ≤ remainder c₃ L A)
  /-- **The residual gates** `63 w_j − b_j ≥ 0` (`cert:four-routes-closing`, the 192 residuals). -/
  resid : ∀ L j, b L j ≤ 63 * CE.w L j
  /-- **The joint mean allocations** (`prop:joint-middle-mean`, `prop:joint-upper-mean`):
  `∑_j b_j u_j ≥ 64(Δ_α + Δ_M + Δ_O + Δ_K + Δ_u − R_u)` at every scale. -/
  alloc : ∀ L, ledgerDelta targetLedger ≤ ∑ j, b L j * CE.u L j

omit [DecidableEq P] in
/-- **`JB` from the five inputs** (`cor:joint-closing`, `eq:final-joint-closing`). -/
theorem MeanAllocation.jointBound {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    (hcard : Fintype.card E = 6) {CI : ClassInputs D.CL} (PD : PolynomialData CI)
    {CE : ClassEnergyInputs D CI} (hE1 : D.EnvelopeBoundNonneg) (hB : D.B ≤ targetLedger.B)
    (MA : MeanAllocation D CE) : JointBound D targetLedger.jointConstant :=
  jointBound_target_of_classEnergy D hcard PD CE hE1 hB MA.b MA.v MA.mean MA.upper MA.resid
    MA.alloc

end Mean

variable {B : Type} [Fintype B] [DecidableEq B] (blockOf : PaperJ0 → B)

/-- **B3's joint obligations with `JB` reduced to the class bounds.** 13 fields: the data `Dv`;
B3's `hB`, `hL₀`, `hT`, `hSA`; the five inputs `CI`, `PD`, `CE`, `E1`, `MA` in place of `JB`;
B3's `SF`, `fix`, `env`. -/
structure B4JointObligationsTarget (hW : Target.Weil) where
  /-- The data (B3's `JointBlockDataTarget`). -/
  Dv : JointBlockDataTarget blockOf hW
  /-- `B ≤` the ledger's `B`. *Open* (A2's `hB_of_prices`). -/
  hB : Dv.data.B ≤ targetLedger.B
  /-- `L₀ ≤` the ledger's `L₀`. *Open*. -/
  hL₀ : Dv.data.L₀ ≤ targetLedger.L₀
  /-- `T ≤` the ledger's `T`. *Open*. -/
  hT : Dv.data.ME.T ≤ targetLedger.T
  /-- `S + A ≤` the ledger's `S + A`. *Open*. -/
  hSA : Dv.data.CL.S + Dv.data.CL.A ≤ targetLedger.S + targetLedger.A
  /-- The classes and their robust evaluated class bounds (`def:cp5`, `cor:envelope-costs`,
  `cor:var-classes`). *Open*. -/
  CI : ClassInputs Dv.data.CL
  /-- The upper data of the class polynomial (`prop:closing-data`(b), (d);
  `cor:variance:final`(iv)). *Open*. -/
  PD : PolynomialData CI
  /-- The class bounds at energy level (`thm:envelopes`(i), `cor:envelope-costs`). *Open*. -/
  CE : ClassEnergyInputs Dv.data CI
  /-- (E1) for the selections in no class. *Open*. -/
  E1 : Dv.data.EnvelopeBoundNonneg
  /-- The joint mean allocation (`prop:record:mean-credit`, `lem:bracket-energy`,
  `cert:four-routes-closing`, `prop:joint-middle-mean`, `prop:joint-upper-mean`). *Open*. -/
  MA : MeanAllocation Dv.data CE
  /-- The sharp first-stage terms, per term. *Open* (G1's `SF`). -/
  SF : EnvelopeInputsBlock.SharpFirstInputs Dv.data
  /-- The fixed-interval envelope energies, per term. *Open* (G1's `fix`). -/
  fix : EnvelopeInputsBlock.FixedIntervalInputs (BlockAnchor.index_coprime_block Dv.data) Dv.data
  /-- The envelope energies, per term. *Open* (G1's `env`). -/
  env : EnvelopeInputsBlock.EnvelopeEnergyInputs (BlockAnchor.index_coprime_block Dv.data) Dv.data

variable {blockOf}

/-- **To B3's joint obligations**: `JB := MA.jointBound card_chamber PD E1 hB`. -/
noncomputable def B4JointObligationsTarget.toJoint {hW : Target.Weil}
    (O : B4JointObligationsTarget blockOf hW) : JointFinalObligationsTarget blockOf hW where
  Dv := O.Dv
  hB := O.hB
  hL₀ := O.hL₀
  hT := O.hT
  hSA := O.hSA
  JB := O.MA.jointBound MainAnchor.card_chamber O.PD O.E1 O.hB
  SF := O.SF
  fix := O.fix
  env := O.env

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵` in the joint form, with the joint bound from
the class bounds** (`thm:main` at `ε = a_T/71`, via `thm:comparison` with `cor:joint-closing` and
`eq:final-joint-closing`): B3's `main_target_paper_block_joint` with `JB` obtained from the class
inputs, the class polynomial (F15, kernel-checked savings), the class bounds at energy level, (E1)
and the joint mean allocation. -/
theorem main_target_paper_block_B4 (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmallRR : Target.ThetaSmallRR) (O : B4JointObligationsTarget blockOf hWeil) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_block_joint hWeil hMovingRoot hFourCycle hThetaSmallRR O.toJoint

end Sarkozy.ClassBoundsPaper
