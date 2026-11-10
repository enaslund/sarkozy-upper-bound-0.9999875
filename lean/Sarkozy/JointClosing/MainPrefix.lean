module

public import Sarkozy.JointClosing.Main
public import Sarkozy.EnvelopesPaper.Prefix

@[expose] public section

/-!
# The joint main statement with a prefix refinement: `F`, `SI`, `hTs` reduced

`main_target_paper_block_joint_B3` with B3's inputs `F`, `hTs`, `SI` replaced by finer ones
(`EnvelopesPaper.PrefixRefinement`):

* `PR : PrefixRefinement GB CL`: the refinement with nothing replaced or added at a tail atom; its
  bracket at the tail atoms is proved, and only the prefix (middle-block) bracket of
  `prop:record:matching`(i) remains, with per-block price bounds `KL β`, `KR β`;
* `hK`: the explicit per-block sums `∑_β KL β ≤ T_K`, `∑_β KR β ≤ T_K` (`prop:signed-sides`(iii),
  `prop:record:matching`(ii));
* `hrepl`: a named property of the comparison law: at every scale its replaced (fold and matching)
  records carry at least `∑_𝔟(s_𝔟 + a_𝔟) − (T^{ledger} − T_K)` of its (CP4) price at that scale;
* `hCL`: the weighted (CP4) summability of the comparison law (`def:cp8`(c)).

`σ_K` of `SummabilityInputs` and the side sums `hTs` are proved from these
(`PrefixRefinement.summabilityInputs`, `PrefixRefinement.hTs`).

**Obligation count** of `main_target_paper_block_joint_prefix`: 14 — `spec`, `Gi`, `CL`, `PR`,
`hK`, `hrepl`, `hCL`; `hB`, `hL₀`, `hSA`, `JB`, `SF`, `fix`, `env` (`TK`, `σCL` are numbers). Against
`main_target_paper_block_joint_B3`'s 13: `hTs` becomes `hK` (finite sums over the blocks) and
`hrepl` (about `CL`), `SI` becomes `hCL` (about `CL`), and `F` becomes `PR` (prefix brackets only).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.JointClosing

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.BlockFrame
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
open Sarkozy.GramBracketPaper Sarkozy.EnvelopesPaper
open Sarkozy.PartVLaws (PaperBlockSpec TailInputsCorr paperAtomMap PaperAtom)

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

omit [Fintype B] in
theorem paper_selPre_nonneg (β : PaperAtom B) :
    0 ≤ paperSelAt (paperAtomMap blockOf) targetDecay β :=
  le_trans zero_le_one (one_le_paperSelAt (paperAtomMap blockOf) TargetLedger.targetDecay_nonneg β)

variable (blockOf) in
/-- **The joint data with a prefix refinement.** `spec`, `hC`, `In`, `Gi`, `CL`; the prefix
refinement `PR`; the number `TK` with the per-block sums `hK`; the property `hrepl` of `CL`; the
number `σCL` with the weighted (CP4) summability `hCL`. -/
structure JointPrefixBlockData (hW : Target.Weil) where
  spec : ∀ b, PaperBlockSpec blockOf b
  hC : TailInputsCorr PartV.P4
  In : FirstStageInputs blockOf
  Gi : GramInputs blockOf spec
  CL : TheoremCBlock.ComparisonLaw targetDecay paperM0 (paperAtomMap blockOf) paperTail
    (paperSelAt (paperAtomMap blockOf) targetDecay) paperPP paperEP paperQueries
    (firstStageTarget blockOf hW spec hC In)
  /-- The prefix refinement (`prop:record:matching`(i) on the middle blocks). *Open*: the prefix
  bracket `PR.bracket_pre` and the per-block bounds. -/
  PR : PrefixRefinement (gramBracketTarget blockOf hW spec hC In Gi) CL
  /-- The price `T_K` of the added diagonals (`prop:signed-sides`(iii)). -/
  TK : ℝ
  /-- **The per-block sums** `∑_β KL β ≤ T_K`, `∑_β KR β ≤ T_K`. *Open* (finite). -/
  hK : ∑ β, PR.KL β ≤ TK ∧ ∑ β, PR.KR β ≤ TK
  /-- **The replaced records of `CL` carry at least `∑_𝔟(s_𝔟 + a_𝔟) − (T^{ledger} − T_K)`** of its
  (CP4) price at the scale, at every scale (`prop:record:matching`(ii): `T = T_K + T_QE + S_oth + A_oth + S_u + A_u +
  10⁻¹²`). *Open* (a property of `CL`). -/
  hrepl : ∀ L, ∑ b, (symTotal (CL.π L) b + skewTotal (CL.π L) b) - (targetLedger.T - TK) ≤
    ∑ b, ∑ t ∈ PR.repl L b, (CL.π L b t .sym + CL.π L b t .skew)
  /-- The weighted (CP4) bound of `CL`. -/
  σCL : ℝ
  /-- **The weighted (CP4) summability of `CL`** (`def:cp8`(c)). *Open* (a property of `CL`). -/
  hCL : ∀ L, ∑ b, TheoremCBlock.oneWeight (paperAtomMap blockOf) paperTail paperPP paperEP L b ^
    ((1 : ℝ) / 4) * (symTotal (CL.π L) b + skewTotal (CL.π L) b) ≤ σCL

variable {hW : Target.Weil}

/-- **To B3's joint data**: `F := PR.toRefinement`, `hTs` and `SI` proved from `hK`, `hrepl`,
`hCL`. -/
noncomputable def JointPrefixBlockData.toB3 (D : JointPrefixBlockData blockOf hW) :
    JointB3BlockData blockOf hW where
  spec := D.spec
  hC := D.hC
  In := D.In
  Gi := D.Gi
  CL := D.CL
  F := D.PR.toRefinement
  hTs := D.PR.hTs D.hK.1 D.hK.2 D.hrepl
  SI := D.PR.summabilityInputs paperPP paperEP paper_selPre_nonneg D.σCL D.hCL

variable (blockOf) in
/-- **The obligations of the joint endgame with a prefix refinement.** 8 fields: `Dv`, `hB`, `hL₀`,
`hSA`, `JB`, `SF`, `fix`, `env` (as in `JointB3FinalObligations`). -/
structure JointPrefixFinalObligations (hW : Target.Weil) where
  Dv : JointPrefixBlockData blockOf hW
  hB : Dv.toB3.toJoint.data.B ≤ targetLedger.B
  hL₀ : Dv.toB3.toJoint.data.L₀ ≤ targetLedger.L₀
  hSA : Dv.toB3.toJoint.data.CL.S + Dv.toB3.toJoint.data.CL.A ≤ targetLedger.S + targetLedger.A
  /-- The joint bound (`cor:joint-closing`, `eq:final-joint-closing`). *Open*. -/
  JB : JointBound Dv.toB3.toJoint.data targetLedger.jointConstant
  SF : EnvelopeInputsBlock.SharpFirstInputs Dv.toB3.toJoint.data
  fix : EnvelopeInputsBlock.FixedIntervalInputs
    (BlockAnchor.index_coprime_block Dv.toB3.toJoint.data) Dv.toB3.toJoint.data
  env : EnvelopeInputsBlock.EnvelopeEnergyInputs
    (BlockAnchor.index_coprime_block Dv.toB3.toJoint.data) Dv.toB3.toJoint.data

/-- To `JointB3FinalObligations`. -/
noncomputable def JointPrefixFinalObligations.toB3 (O : JointPrefixFinalObligations blockOf hW) :
    JointB3FinalObligations blockOf hW where
  Dv := O.Dv.toB3
  hB := O.hB
  hL₀ := O.hL₀
  hSA := O.hSA
  JB := O.JB
  SF := O.SF
  fix := O.fix
  env := O.env

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵`, joint form, with a prefix refinement**
(`thm:main` via `cor:joint-closing`): `main_target_paper_block_joint_B3` with
`JointPrefixFinalObligations.toB3`. -/
theorem main_target_paper_block_joint_prefix (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : JointPrefixFinalObligations blockOf hWeil) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_block_joint_B3 hWeil hMovingRoot hFourCycle hThetaSmallRR O.toB3

end Sarkozy.JointClosing
