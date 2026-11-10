module

public import Sarkozy.EnvelopeEnergiesPaper.SharpFirstCoupled
public import Sarkozy.FirstStagePaper.Main
public import Sarkozy.JointClosing.Main

@[expose] public section

/-!
# The per-record moment inputs of `SF` are per-block inputs

The record inputs `fold`, `momA`, `mom`, `mom'` of `SharpFirstCoupledInputs` are indexed by the
scale, the atom and the record. For a first stage built from per-atom data
(A1's `FirstStagePaper.firstStageOfAtoms`, which is how the paper's first stage is built), the
records do not depend on the scale and the tail atoms carry none. So these inputs are **per-block
inputs** (`AtomStageMoments`), and for the paper's first stage (`firstStageTarget`) only the
class-three blocks need them (the square-clique atoms carry `AtomStage.trivial`); among them the
upper blocks are trivial too (`specStage_upper_moments`), so only the **middle blocks** remain.

* `AtomStageMoments S θ`: for one block's first-stage data `S`, a sharp-fold datum for every
  difference and the record moments of its positive records;
* `FirstStageMoments.ofAtoms`: per-block data give the four families for `firstStageOfAtoms`;
* `FirstStageMoments.paper`: for the paper's first stage, from the class-three blocks;
* `SharpFirstCoupledInputs.ofBlocks`: B5's `SFc` for the paper's data from per-block moments, the
  scalars and the fibre input.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.EnvelopeEnergiesPaper

open Sarkozy.TheoremC Sarkozy.FirstStagePaper Sarkozy.BlockFrame Sarkozy.EnvelopeInputsBlock
  Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.Param (Params)

/-- **The moment inputs of one block's first stage** (`lem:density:middle-catalog`,
`lem:density:packets`, `lem:density:coupled`): a sharp-fold datum (`SharpFoldData`) for every
difference `κ'_i − κ_i` at the cut of its tag, and the record moments of `κa`, `κ`, `κ'`. -/
structure AtomStageMoments {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] {μ : SlotMeasure X}
    {Tag : Type} {cut : Tag → ReflectionCut Slot} {ϑ₀ : ReflectionCut Slot}
    (S : AtomStage μ Tag cut ϑ₀) (θ : ℝ) where
  fold : ∀ i, SharpFoldData (cut (S.tag i)) (S.κ i) (S.κ' i - S.κ i) (S.dconst i) θ
  momA : ∀ i, RecordMoment (S.κa i) θ
  mom : ∀ i, RecordMoment (S.κ i) θ
  mom' : ∀ i, RecordMoment (S.κ' i) θ

/-- The trivial first stage (no records) has the moment inputs vacuously. -/
def AtomStageMoments.trivial {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (μ : SlotMeasure X) (Tag : Type) (cut : Tag → ReflectionCut Slot) (ϑ₀ : ReflectionCut Slot)
    (θ : ℝ) : AtomStageMoments (AtomStage.trivial μ Tag cut ϑ₀) θ where
  fold i := i.elim
  momA i := i.elim
  mom i := i.elim
  mom' i := i.elim

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]

/-- **The four record families of a first stage.** -/
structure FirstStageMoments {selPre : Bk → ℝ} {R : TheoremCBlock.Reference m₀ blk}
    (FS : TheoremCBlock.FirstStage a m₀ blk p selPre R) (θ : ℝ) where
  fold : ∀ L b i, SharpFoldData (FS.cut (FS.tag L b i)) (FS.κ L b i) (FS.κ' L b i - FS.κ L b i)
    (FS.dconst L b i) θ
  momA : ∀ L b hh, RecordMoment (FS.κa L b hh) θ
  mom : ∀ L b i, RecordMoment (FS.κ L b i) θ
  mom' : ∀ L b i, RecordMoment (FS.κ' L b i) θ

/-- **Per-block moments give the record families of `firstStageOfAtoms`** (the records do not
depend on the scale; the tail atoms have none). -/
noncomputable def FirstStageMoments.ofAtoms {selPre : Bk → ℝ} {R : TheoremCBlock.Reference m₀ blk}
    {Tag : Type} [Fintype Tag] [DecidableEq Tag] {cut : Tag → ReflectionCut Slot}
    {hcut : ∀ j, IsFamilyCut (cut j)} {ϑ₀ : ReflectionCut Slot} {hϑ₀ : IsFamilyCut ϑ₀}
    {A : ∀ β, AtomStage (signedIntegral (R.μ₀ β).weight) Tag cut ϑ₀} {θ : ℝ}
    (M : ∀ β, AtomStageMoments (A β) θ) :
    FirstStageMoments (firstStageOfAtoms a m₀ blk p selPre R Tag cut hcut ϑ₀ hϑ₀ A) θ where
  fold _ b i := match b, i with
    | .inl β, i => (M β).fold i
    | .inr _, i => i.elim
  momA _ b i := match b, i with
    | .inl β, i => (M β).momA i
    | .inr _, i => i.elim
  mom _ b i := match b, i with
    | .inl β, i => (M β).mom i
    | .inr _, i => i.elim
  mom' _ b i := match b, i with
    | .inl β, i => (M β).mom' i
    | .inr _, i => i.elim

/-! ## The paper's first stage -/

section Paper

open Sarkozy.CancellationSteps Sarkozy.PartVLaws Sarkozy.JointClosing

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

omit [Fintype B] in
/-- An upper block carries the trivial first stage (A1's `specStage`), so its moment inputs hold
vacuously. -/
noncomputable def specStage_upper_moments (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (U : PaperBlockSpec blockOf b) (hU : ∃ x, U = .upper x) (θ : ℝ) :
    AtomStageMoments (specStage hW In U) θ := by
  obtain ⟨x, rfl⟩ := Classical.indefiniteDescription _ hU
  exact AtomStageMoments.trivial _ _ _ _ θ

/-- **The paper's per-atom moments from the class-three blocks**: the square-clique atoms carry the
trivial first stage. -/
noncomputable def paperStageMoments (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (In : FirstStageInputs blockOf) {θ : ℝ}
    (MB : ∀ b, AtomStageMoments (specStage hW In (spec b)) θ) :
    ∀ β, AtomStageMoments (paperStage blockOf hW spec hC In β) θ
  | .inl _ => AtomStageMoments.trivial _ _ _ _ θ
  | .inr b => MB b

/-- **The record families of the paper's first stage** (`firstStageTarget`, at `a_T`) from
per-block moments of the class-three blocks. -/
noncomputable def FirstStageMoments.paper (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (In : FirstStageInputs blockOf) {θ : ℝ}
    (MB : ∀ b, AtomStageMoments (specStage hW In (spec b)) θ) :
    FirstStageMoments (firstStageTarget blockOf hW spec hC In) θ :=
  (firstStageTarget_eq hW spec hC In).symm ▸
    FirstStageMoments.ofAtoms (paperStageMoments hW spec hC In MB)

variable {hW : Target.Weil}

/-- **B5's `SFc` for the paper's data from per-block inputs**: the record families from the
per-block moments `MB` of the class-three blocks (only the middle blocks carry records), with the
scalars and the per-term fibre input. -/
noncomputable def SharpFirstCoupledInputs.ofBlocks (Dv : JointBlockDataTarget blockOf hW) (θ : ℝ)
    (hθ : 0 < θ) (MB : ∀ b, AtomStageMoments (specStage hW Dv.In (Dv.spec b)) θ)
    (ε : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ ε L) (hεt : Tendsto ε atTop (𝓝 0)) (c₁ : ℝ) (hc₁ : 0 ≤ c₁)
    (fibre : Param.AtCounterexamples (Params.ofDecay TargetLedger.targetDecay) Dv.data.Y
      (fun L A => ∀ σ : (∀ b, Option (Dv.data.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
        1 ≤ countVec (Dv.data.FS.tag L) σ j → ∀ f : (∀ b, CPiece Dv.data L b),
        (∀ b, cpieceCoef Dv.data L σ j b (f b) ≠ 0) →
          CoupledFibreMoment Dv.data L A f θ (ε L) c₁)) :
    SharpFirstCoupledInputs Dv.data where
  θ := θ
  hθ := hθ
  fold := (FirstStageMoments.paper hW Dv.spec Dv.hC Dv.In MB).fold
  momA := (FirstStageMoments.paper hW Dv.spec Dv.hC Dv.In MB).momA
  mom := (FirstStageMoments.paper hW Dv.spec Dv.hC Dv.In MB).mom
  mom' := (FirstStageMoments.paper hW Dv.spec Dv.hC Dv.In MB).mom'
  ε := ε
  hε0 := hε0
  hεt := hεt
  c₁ := c₁
  hc₁ := hc₁
  fibre := fibre

end Paper

end Sarkozy.EnvelopeEnergiesPaper
