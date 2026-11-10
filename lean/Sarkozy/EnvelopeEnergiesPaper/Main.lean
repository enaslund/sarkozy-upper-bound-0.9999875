module

public import Sarkozy.EnvelopeEnergiesPaper.MiddleFolds
public import Sarkozy.EnvelopeEnergiesPaper.CRTBundles
public import Sarkozy.EnvelopeEnergiesPaper.DataChain
public import Sarkozy.JointClosing.Main

@[expose] public section

/-!
# The joint main statement with `SF` through `lem:density:coupled` (B5)

B3's `JointClosing.main_target_paper_block_joint` has 13 obligations; three of them are G1's
envelope bundles `SF`, `fix`, `env` over the paper's comparison data at `a_T` on the block atoms.

**`SF`** is replaced, through `lem:density:coupled` on the block atoms (`SharpFirstCoupled`), by:
* the per-block moment inputs of the first stage, **proved** for the paper's blocks
  (`paperStageMoments_proved`, `MiddleMoments`, `MiddleFolds`): the six records of `ρ − μ`, the
  folded matching records `κ_s`, their replacements `κ'_s` (M1's catalog rows "folded `F₁`, `E₁`,
  `G₁`" at `L^{66}`), and the sharp folds of `κ'_s − κ_s` (A1's decomposition, folded laws at
  `L^{60}`), at every `θ ≤ 12/11`;
* `fibre`: per term, the fibre-moment input of `lem:density:coupled` (`prop:density:production`
  with `lem:record:density-dc`, `lem:record:fibre-scale`). *Open*.

The positivity and the signed Hölder property of the outside reference, the matching of the
term's weight with the coupled lemma's, the vanishing terms and the price bookkeeping are proved.

`fix` and `env` are replaced by `fixC`, `envC`: G1's bundles with every per-term energy on the
cyclic coordinates `∏_𝔟 ℤ/crtModuli_𝔟` (`CRTBundles`; the joined moduli are pairwise coprime for the
paper's data, `paper_pairwise`). They are equivalent to G1's term by term; the obstacle G1 found
for them on the block atoms (joint block laws, no product prefix) is gone, but their per-term
inputs have the bracket `Ñ` as outside law and revealed inputs, for which the formal chain has no
theorem yet (see the report).

**Count** (`main_target_paper_block_B5`): 13 obligations, as B3's: `spec`, `Gi`, `CL`, `ME`, `SM`;
`hB`, `hL₀`, `hT`, `hSA`, `JB`, **`fibre`**, `fixC`, `envC`. `fibre` replaces G1's per-term `hcoup`;
the record moments are no longer obligations.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.EnvelopeEnergiesPaper

open Sarkozy.JointClosing Sarkozy.CancellationSteps
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger targetLedger_bounds)

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

variable (blockOf) in
/-- **The obligations of the joint endgame with `SF` through `lem:density:coupled`.** 9 fields: B3's
`JointFinalObligationsTarget` with `SF`, `fix`, `env` replaced by `SFc`, `fixC`, `envC`. -/
structure B5FinalObligations (hW : Target.Weil) where
  /-- The data (B3's `JointBlockDataTarget`: `spec`, `hC`, `In`, `Gi`, `CL`, `ME`, `SM`). -/
  Dv : JointBlockDataTarget blockOf hW
  /-- `B ≤` the ledger's `B`. *Open*. -/
  hB : Dv.data.B ≤ targetLedger.B
  /-- `L₀ ≤` the ledger's `L₀`. *Open*. -/
  hL₀ : Dv.data.L₀ ≤ targetLedger.L₀
  /-- `T ≤` the ledger's `T` ((CP6)). *Open*. -/
  hT : Dv.data.ME.T ≤ targetLedger.T
  /-- `S + A ≤` the ledger's `S + A` ((CP4)). *Open*. -/
  hSA : Dv.data.CL.S + Dv.data.CL.A ≤ targetLedger.S + targetLedger.A
  /-- The joint bound (`cor:joint-closing`, `eq:final-joint-closing`). *Open*. -/
  JB : JointBound Dv.data targetLedger.jointConstant
  /-- **The sharp first-stage terms through `lem:density:coupled`** (`lem:sharp-first`,
  `lem:record:folded-energy`): per-record folded and record moments and the per-term
  fibre-and-price input (`SharpFirstCoupledInputs`). *Open* in those parts. -/
  SFc : SharpFirstCoupledInputs Dv.data
  /-- The fixed-interval envelope energies, per term, on the cyclic coordinates (G1's `fix`,
  `lem:envelope-energy`). *Open*. -/
  fixC : FixedIntervalInputsCRT (BlockAnchor.index_coprime_block Dv.data) Dv.data paper_pairwise
  /-- The envelope energies, per term, on the cyclic coordinates (G1's `env`,
  `lem:envelope-energy`). *Open*. -/
  envC : EnvelopeEnergyInputsCRT (BlockAnchor.index_coprime_block Dv.data) Dv.data paper_pairwise

variable {hW : Target.Weil}

/-- **To B3's joint obligations**: `SF := SFc.toSharpFirstInputs`, `fix := fixC.toG1`,
`env := envC.toG1`, everything else unchanged. -/
noncomputable def B5FinalObligations.toJoint (O : B5FinalObligations blockOf hW) :
    JointFinalObligationsTarget blockOf hW where
  Dv := O.Dv
  hB := O.hB
  hL₀ := O.hL₀
  hT := O.hT
  hSA := O.hSA
  JB := O.JB
  SF := O.SFc.toSharpFirstInputs
  fix := O.fixC.toG1
  env := O.envC.toG1

/-- **The main statement with `SF` through `lem:density:coupled` (record inputs per scale and
atom)**: B3's `main_target_paper_block_joint` with `B5FinalObligations.toJoint`. -/
theorem main_target_paper_block_B5_coupled (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmallRR : Target.ThetaSmallRR) (O : B5FinalObligations blockOf hWeil) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_block_joint hWeil hMovingRoot hFourCycle hThetaSmallRR O.toJoint

variable (blockOf) in
/-- **The obligations of B5's main statement**: `B5FinalObligations` with `SFc` built from the
**proved** per-block moments of the paper's first stage (`paperStageMoments_proved`: M1's catalog
rows for the six records of `ρ − μ`, `κ_s`, `κ'_s`, and the sharp folds of `κ'_s − κ_s`) and the
per-term fibre input. Open: `Dv` (`spec`, `Gi`, `CL`, `ME`, `SM`), `hB`, `hL₀`, `hT`, `hSA`, `JB`,
**`fibre`**, `fixC`, `envC`; the scalars `θ ≤ 12/11`, `ε`, `c₁` are free with the signs and limits
of G1's `SharpFirstInputs`. -/
structure B5BlockObligations (hW : Target.Weil) where
  /-- The data (B3's `JointBlockDataTarget`). -/
  Dv : JointBlockDataTarget blockOf hW
  /-- `B ≤` the ledger's `B`. *Open*. -/
  hB : Dv.data.B ≤ targetLedger.B
  /-- `L₀ ≤` the ledger's `L₀`. *Open*. -/
  hL₀ : Dv.data.L₀ ≤ targetLedger.L₀
  /-- `T ≤` the ledger's `T` ((CP6)). *Open*. -/
  hT : Dv.data.ME.T ≤ targetLedger.T
  /-- `S + A ≤` the ledger's `S + A` ((CP4)). *Open*. -/
  hSA : Dv.data.CL.S + Dv.data.CL.A ≤ targetLedger.S + targetLedger.A
  /-- The joint bound (`cor:joint-closing`, `eq:final-joint-closing`). *Open*. -/
  JB : JointBound Dv.data targetLedger.jointConstant
  /-- The density endpoint `θ` (the paper's `ϑ = 1.014587`), below the catalog's endpoint
  `12/11`. -/
  θ : ℝ
  hθ : 0 < θ
  hθ' : θ ≤ 12 / 11
  /-- The relative error and the remainder constant of the sharp terms. -/
  ε : ℕ → ℝ
  hε0 : ∀ L, 0 ≤ ε L
  hεt : Tendsto ε atTop (𝓝 0)
  c₁ : ℝ
  hc₁ : 0 ≤ c₁
  /-- **Per term of the coupled expansion of `lem:sharp-first`: the fibre-moment input**
  (`CoupledFibreMoment`; `prop:density:production` with `lem:record:density-dc`,
  `lem:record:fibre-scale`). *Open*. -/
  fibre : Param.AtCounterexamples (Param.Params.ofDecay targetDecay) Dv.data.Y
    (fun L A => ∀ σ : (∀ b, Option (Dv.data.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
      1 ≤ RecordExpansion.countVec (Dv.data.FS.tag L) σ j →
      ∀ f : (∀ b, EnvelopeInputsBlock.CPiece Dv.data L b),
      (∀ b, EnvelopeInputsBlock.cpieceCoef Dv.data L σ j b (f b) ≠ 0) →
        CoupledFibreMoment Dv.data L A f θ (ε L) c₁)
  /-- The fixed-interval envelope energies on the cyclic coordinates (G1's `fix`). *Open*. -/
  fixC : FixedIntervalInputsCRT (BlockAnchor.index_coprime_block Dv.data) Dv.data paper_pairwise
  /-- The envelope energies on the cyclic coordinates (G1's `env`). *Open*. -/
  envC : EnvelopeEnergyInputsCRT (BlockAnchor.index_coprime_block Dv.data) Dv.data paper_pairwise

/-- To `B5FinalObligations`: `SFc := SharpFirstCoupledInputs.ofBlocks …`. -/
noncomputable def B5BlockObligations.toFinal (O : B5BlockObligations blockOf hW) :
    B5FinalObligations blockOf hW where
  Dv := O.Dv
  hB := O.hB
  hL₀ := O.hL₀
  hT := O.hT
  hSA := O.hSA
  JB := O.JB
  SFc := SharpFirstCoupledInputs.ofBlocks O.Dv O.θ O.hθ
    (paperStageMoments_proved hW O.Dv.In O.hθ O.hθ' O.Dv.spec)
    O.ε O.hε0 O.hεt O.c₁ O.hc₁ O.fibre
  fixC := O.fixC
  envC := O.envC

/-- **B5's main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵`** (`thm:main` at `ε = a_T/71`, joint form):
B3's `main_target_paper_block_joint` with `SF` through `lem:density:coupled` from per-block moment
inputs and a per-term fibre-moment input, and `fix`, `env` on the cyclic coordinates. -/
theorem main_target_paper_block_B5 (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmallRR : Target.ThetaSmallRR) (O : B5BlockObligations blockOf hWeil) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_block_B5_coupled hWeil hMovingRoot hFourCycle hThetaSmallRR
    O.toFinal

end Sarkozy.EnvelopeEnergiesPaper
