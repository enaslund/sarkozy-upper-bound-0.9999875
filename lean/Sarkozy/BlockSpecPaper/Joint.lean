module

public import Sarkozy.BlockSpecPaper.Charges
public import Sarkozy.JointClosing.Main

@[expose] public section

/-!
# The joint endgame with the block specification of the paper's construction

B3's `JointClosing.main_target_paper_block_joint` (`cor:joint-closing`, `eq:final-joint-closing`)
with the block data `blockOf`, `spec`, `In`, `Gi` (and the tail input `hC`) supplied as in
`Main.lean`: `paperBlockOf cell`, `paperSpec hW A`, `paperIn cell`, `paperGi hW A`, and
`TailCorrCore.tailInputsCorr` (B3's `JointBlockDataTarget.ofProvedTail`).

* `FixedJointBlockData`: B3's `JointBlockDataTarget` with `spec`, `hC`, `In`, `Gi` fixed: `CL`
  (CP4), `ME` (CP6), `SM` (CP8)(c). 3 fields. Stated for a general block type and instantiated
  by the `abbrev` `B1JointBlockData` (see `Main.lean` for why).
* `FixedJointFinalObligations`: B3's `JointFinalObligationsTarget` over it: `Dv`, `hB`, `hL₀`, `hT`,
  `hSA`, **`JB`**, `SF`, `fix`, `env`. `toJoint` maps it to B3's structure.
* **`main_target_paper_joint_B1`**: the bound `N^{1 − a_T/71}` from `Weil`, H2″, the data `cell`,
  the analytic inputs `A` and `B1JointFinalObligations`.
* **`hB_of_blockCharges_joint`**, **`main_target_paper_joint_B1_charges`**: `hB` replaced by the
  per-piece block charges (`Charges.lean`).

**Count.** `main_target_paper_joint_B1`: **11 open obligations** (`CL`, `ME`, `SM`; `hB`, `hL₀`,
`hT`, `hSA`, `JB`, `SF`, `fix`, `env`), plus the analytic inputs `A` (one `Prop`, three families)
and the data `cell`; against B3's 13 (`spec`, `Gi`, `CL`, `ME`, `SM`, and the eight finals) plus the
data `In`. `MovingRoot` and `FourCycle` enter only through the proved tail.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.BlockSpecPaper

open Sarkozy.TheoremC Sarkozy.RecordExpansion
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing
open Sarkozy.PartVLaws (PaperBlockSpec v2Reference TailInputsCorr paperAtomMap)

/-! ## B3's joint obligations at fixed block data (generic in the block type) -/

section Fixed

variable {B : Type} [Fintype B] [DecidableEq B] (blockOf : PaperJ0 → B) (hW : Target.Weil)
  (spec : ∀ b, PaperBlockSpec blockOf b) (hC : TailInputsCorr PartV.P4)
  (In : FirstStageInputs blockOf) (Gi : GramInputs blockOf spec)

/-- **B3's joint block data with `spec`, `hC`, `In`, `Gi` fixed**: `CL` (CP4), `ME` (CP6), `SM`
(CP8)(c) at `a_T`. *Open* (Part V). 3 fields. -/
structure FixedJointBlockData where
  /-- (CP4) at `a_T`. *Open*. -/
  CL : TheoremCBlock.ComparisonLaw targetDecay paperM0 (paperAtomMap blockOf) paperTail
    (paperSelAt (paperAtomMap blockOf) targetDecay) paperPP paperEP paperQueries
    (firstStageTarget blockOf hW spec hC In)
  /-- (CP6) at `a_T`, over the constructed bracket. *Open* (B3's `EnvelopeRefinement.toME`). -/
  ME : TheoremCBlock.MatchingEnvelopes targetDecay paperM0 (paperAtomMap blockOf) paperTail
    (gramBracketTarget blockOf hW spec hC In Gi) CL
  /-- (CP8)(c) at `a_T`. *Open*; read by no proof (B3). -/
  SM : TheoremCBlock.Summability targetDecay paperM0 (paperAtomMap blockOf) paperTail ME

variable {blockOf hW spec hC In Gi}

/-- **To B3's joint data**: the fixed `spec`, `hC`, `In`, `Gi`, and the three Part V fields. -/
noncomputable def FixedJointBlockData.toJoint (D : FixedJointBlockData blockOf hW spec hC In Gi) :
    JointBlockDataTarget blockOf hW where
  spec := spec
  hC := hC
  In := In
  Gi := Gi
  CL := D.CL
  ME := D.ME
  SM := D.SM

variable (blockOf hW spec hC In Gi)

/-- **B3's joint final obligations with `spec`, `hC`, `In`, `Gi` fixed.** 9 fields: `Dv` (3 open
fields) and B3's eight (`hB`, `hL₀`, `hT`, `hSA`, `JB`, `SF`, `fix`, `env`), verbatim over
`Dv.toJoint`. -/
structure FixedJointFinalObligations where
  /-- The Part V data over the fixed block specification. -/
  Dv : FixedJointBlockData blockOf hW spec hC In Gi
  /-- `B ≤` the ledger's `B` (`hB_of_blockCharges_joint`). *Open*. -/
  hB : Dv.toJoint.data.B ≤ targetLedger.B
  /-- `L₀ ≤` the ledger's `L₀`. *Open*. -/
  hL₀ : Dv.toJoint.data.L₀ ≤ targetLedger.L₀
  /-- `T ≤` the ledger's `T` ((CP6)). *Open*. -/
  hT : Dv.toJoint.data.ME.T ≤ targetLedger.T
  /-- `S + A ≤` the ledger's `S + A` ((CP4)). *Open*. -/
  hSA : Dv.toJoint.data.CL.S + Dv.toJoint.data.CL.A ≤ targetLedger.S + targetLedger.A
  /-- **The joint bound** (`cor:joint-closing`, hypothesis, at the ledger's joint constant,
  `eq:final-joint-closing`). *Open*. -/
  JB : JointBound Dv.toJoint.data targetLedger.jointConstant
  /-- The sharp first-stage terms, per term. *Open* (G1's `SF`). -/
  SF : EnvelopeInputsBlock.SharpFirstInputs Dv.toJoint.data
  /-- The fixed-interval envelope energies, per term. *Open* (G1's `fix`). -/
  fix : EnvelopeInputsBlock.FixedIntervalInputs
    (BlockAnchor.index_coprime_block Dv.toJoint.data) Dv.toJoint.data
  /-- The envelope energies, per term. *Open* (G1's `env`). -/
  env : EnvelopeInputsBlock.EnvelopeEnergyInputs
    (BlockAnchor.index_coprime_block Dv.toJoint.data) Dv.toJoint.data

variable {blockOf hW spec hC In Gi}

/-- **To B3's joint obligations**: `Dv := Dv.toJoint`, the other eight fields copied. -/
noncomputable def FixedJointFinalObligations.toJoint
    (O : FixedJointFinalObligations blockOf hW spec hC In Gi) :
    JointFinalObligationsTarget blockOf hW where
  Dv := O.Dv.toJoint
  hB := O.hB
  hL₀ := O.hL₀
  hT := O.hT
  hSA := O.hSA
  JB := O.JB
  SF := O.SF
  fix := O.fix
  env := O.env

end Fixed

/-! ## The paper's construction -/

/-- **B1's joint block data**: `CL`, `ME`, `SM` over the paper's construction. 3 fields. -/
abbrev B1JointBlockData (cell : ℕ → ℕ) (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (A : PaperAnalyticInputs cell) : Type 1 :=
  FixedJointBlockData (paperBlockOf cell) hW (paperSpec hW A)
    (TailCorrCore.tailInputsCorr hW hMR hFour) (paperIn cell) (paperGi hW A)

/-- **B1's joint obligations**: `CL`, `ME`, `SM` and B3's eight finals over the paper's
construction. 11 obligations. -/
abbrev B1JointFinalObligations (cell : ℕ → ℕ) (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (A : PaperAnalyticInputs cell) : Type 1 :=
  FixedJointFinalObligations (paperBlockOf cell) hW (paperSpec hW A)
    (TailCorrCore.tailInputsCorr hW hMR hFour) (paperIn cell) (paperGi hW A)

/-- **The main statement at `ε = a_T/71` in the joint form, with the block specification of the
paper's construction** (`thm:main` at `ε = a_T/71`, `cor:joint-closing`,
`eq:final-joint-closing`, `def:construction`(b) in the ALLp configuration): B3's
`main_target_paper_block_joint` with `blockOf := paperBlockOf cell`, `spec := paperSpec hW A`,
`In := paperIn cell`, `Gi := paperGi hW A` and the proved tail. Remaining: the data `cell`, the
analytic inputs `A` (`lem:upper-reference-rp`(ii), `lem:front12:reference`(i),(ii)) and the 11
fields of `B1JointFinalObligations`. -/
theorem main_target_paper_joint_B1 (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmallRR : Target.ThetaSmallRR) (cell : ℕ → ℕ) (A : PaperAnalyticInputs cell)
    (O : B1JointFinalObligations cell hWeil hMovingRoot hFourCycle A) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_block_joint hWeil hMovingRoot hFourCycle hThetaSmallRR O.toJoint

/-! ## `hB` from the block charges in the joint form -/

variable {cell : ℕ → ℕ}

/-- The sum of the block price bounds from the per-piece charge bounds. -/
theorem sum_paperSpec_ubound_le {hW : Target.Weil} {A : PaperAnalyticInputs cell}
    (f : PaperBlock cell → ℝ) {c₂ c₃ : Fin 33 → ℝ} (h₂ : ∀ i, blockCharge f 2 i ≤ c₂ i)
    (h₃ : ∀ i, blockCharge f 3 i ≤ c₃ i) :
    ∑ b, specUbound (paperIn cell) (paperSpec hW A b) (f b) ≤
      ∑ i : Fin 33, (chargeU2 i * c₂ i + chargeU3 i * c₃ i) := by
  rw [sum_paperSpec_ubound hW A f]
  exact Finset.sum_le_sum fun i _ => add_le_add
    (mul_le_mul_of_nonneg_left (h₂ i) (chargeU2_nonneg i))
    (mul_le_mul_of_nonneg_left (h₃ i) (chargeU3_nonneg i))

/-- **`hB` of the joint obligations from the per-piece block charges** (`lem:record:middle-prices`,
`lem:record:block-charge`, `def:closing-quantities`): A2's `hB_of_charges` at `Dv.toJoint.toA2`,
whose `B` is the joint data's `B` (the mean credit does not enter `B`). -/
theorem hB_of_blockCharges_joint {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs cell}
    (D : B1JointBlockData cell hW hMR hFour A) {c₂ c₃ : Fin 33 → ℝ} {d' v' : Fin 2 → ℝ}
    (h₂ : ∀ i, blockCharge
      (fun b => paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay (.inr b)) 2 i ≤ c₂ i)
    (h₃ : ∀ i, blockCharge
      (fun b => paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay (.inr b)) 3 i ≤ c₃ i)
    (hd : ∀ j, ∑ β, (paperStage (paperBlockOf cell) hW (paperSpec hW A)
      (TailCorrCore.tailInputsCorr hW hMR hFour) (paperIn cell) β).dTag
      (paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay β) j ≤ d' j)
    (hv : ∀ j, ∑ β, (paperStage (paperBlockOf cell) hW (paperSpec hW A)
      (TailCorrCore.tailInputsCorr hW hMR hFour) (paperIn cell) β).vTag
      (paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay β) j ≤ v' j)
    (hcost : Real.exp (∑ i : Fin 33, (chargeU2 i * c₂ i + chargeU3 i * c₃ i)) *
      (1 + tagSeries d' v') ≤ targetLedger.B) :
    D.toJoint.data.B ≤ targetLedger.B :=
  hB_of_charges D.toJoint.toA2 (fun b => paperSpec_scale hW A b)
    (sum_paperSpec_ubound_le _ h₂ h₃) hd hv hcost

/-- **The joint main statement with `hB` from the block charges**: `main_target_paper_joint_B1`
with the obligation `hB` replaced by the charge bounds `b₂(i) ≤ c₂(i)`, `b₃(i) ≤ c₃(i)`
(`lem:record:block-charge`), the first-stage tag sums `≤ d'`, `v'`, and the cost inequality
`e^{∑ (U₂ c₂ + U₃ c₃)} (1 + 𝔗(d', v')) ≤ B^{ledger}`. -/
theorem main_target_paper_joint_B1_charges (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR) (cell : ℕ → ℕ)
    (A : PaperAnalyticInputs cell) (Dv : B1JointBlockData cell hWeil hMovingRoot hFourCycle A)
    {c₂ c₃ : Fin 33 → ℝ} {d' v' : Fin 2 → ℝ}
    (h₂ : ∀ i, blockCharge
      (fun b => paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay (.inr b)) 2 i ≤ c₂ i)
    (h₃ : ∀ i, blockCharge
      (fun b => paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay (.inr b)) 3 i ≤ c₃ i)
    (hd : ∀ j, ∑ β, (paperStage (paperBlockOf cell) hWeil (paperSpec hWeil A)
      (TailCorrCore.tailInputsCorr hWeil hMovingRoot hFourCycle) (paperIn cell) β).dTag
      (paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay β) j ≤ d' j)
    (hv : ∀ j, ∑ β, (paperStage (paperBlockOf cell) hWeil (paperSpec hWeil A)
      (TailCorrCore.tailInputsCorr hWeil hMovingRoot hFourCycle) (paperIn cell) β).vTag
      (paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay β) j ≤ v' j)
    (hcost : Real.exp (∑ i : Fin 33, (chargeU2 i * c₂ i + chargeU3 i * c₃ i)) *
      (1 + tagSeries d' v') ≤ targetLedger.B)
    (hL₀ : Dv.toJoint.data.L₀ ≤ targetLedger.L₀)
    (hT : Dv.toJoint.data.ME.T ≤ targetLedger.T)
    (hSA : Dv.toJoint.data.CL.S + Dv.toJoint.data.CL.A ≤ targetLedger.S + targetLedger.A)
    (JB : JointBound Dv.toJoint.data targetLedger.jointConstant)
    (SF : EnvelopeInputsBlock.SharpFirstInputs Dv.toJoint.data)
    (fix : EnvelopeInputsBlock.FixedIntervalInputs
      (BlockAnchor.index_coprime_block Dv.toJoint.data) Dv.toJoint.data)
    (env : EnvelopeInputsBlock.EnvelopeEnergyInputs
      (BlockAnchor.index_coprime_block Dv.toJoint.data) Dv.toJoint.data) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_joint_B1 hWeil hMovingRoot hFourCycle hThetaSmallRR cell A
    { Dv := Dv
      hB := hB_of_blockCharges_joint Dv h₂ h₃ hd hv hcost
      hL₀ := hL₀
      hT := hT
      hSA := hSA
      JB := JB
      SF := SF
      fix := fix
      env := env }

end Sarkozy.BlockSpecPaper
