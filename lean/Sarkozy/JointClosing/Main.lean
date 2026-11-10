module

public import Sarkozy.JointClosing.Endgame
public import Sarkozy.EnvelopesPaper.Main
public import Sarkozy.EnvelopesPaper.Sanity
public import Sarkozy.MainTarget.Main

@[expose] public section







open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.JointClosing

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.BlockFrame Sarkozy.Comparison
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger targetLedger_bounds)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
open Sarkozy.GramBracketPaper Sarkozy.EnvelopesPaper
open Sarkozy.PartVLaws (PaperBlockSpec v2Reference TailInputsCorr paperAtomMap PaperAtom)

/-! ## (CP7) with `m = 0`, for any matching envelopes -/

section ZeroMean

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {S₀ : Bk → ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E} {R : TheoremCBlock.Reference m₀ blk}
  {FS : TheoremCBlock.FirstStage a m₀ blk p S₀ R} {GB : TheoremCBlock.GramBracket a m₀ blk p S₀ FS}
  {CL : TheoremCBlock.ComparisonLaw a m₀ blk p S₀ pp ep Q FS}

omit [∀ L, DecidableEq (J L)] in
/-- The left envelope of (CP6) is positive at `ι`: `Ñ ⪰_ι 0` plus positive reserved-diagonal
records. -/
theorem ML_positive (ME : TheoremCBlock.MatchingEnvelopes a m₀ blk p GB CL) (L : ℕ)
    (b : BlockAtom Bk J L) : reservedCut.Positive (ME.ML L b) :=
  (GB.bracket L b).left_positive.add
    (positive_sum_records _ _ (ME.cL_nonneg L b) (ME.κL_pos L b) (ME.κL_diag L b))

omit [∀ L, DecidableEq (J L)] in
/-- The right envelope of (CP6) is positive at `ι`. -/
theorem MR_positive (ME : TheoremCBlock.MatchingEnvelopes a m₀ blk p GB CL) (L : ℕ)
    (b : BlockAtom Bk J L) : reservedCut.Positive (ME.MR L b) :=
  (GB.bracket L b).left_positive.add
    (positive_sum_records _ _ (ME.cR_nonneg L b) (ME.κR_pos L b) (ME.κR_diag L b))

variable (a) in
/-- **(CP7) with mean credit `0`, for any matching envelopes** (`def:cp7`): the mean energies of
envelopes positive at `ι` are nonnegative. The joint endgame does not read `MC`; this fills the
field. -/
noncomputable def zeroMeanCredit (ME : TheoremCBlock.MatchingEnvelopes a m₀ blk p GB CL) :
    TheoremCBlock.MeanCredit a m₀ blk p ME where
  m := 0
  bound := by
    refine ⟨fun _ => 0, tendsto_const_nhds, 0, le_refl 0, ?_⟩
    unfold Param.AtCounterexamples
    filter_upwards with L
    intro _ _ _ A _ _
    have h1 := energyMean_nonneg (blockLift m₀ blk p) ME.ML (ML_positive ME) L A
    have h2 := energyMean_nonneg (blockLift m₀ blk p) ME.MR (MR_positive ME) L A
    have h0 : Sarkozy.Comparison.remainder 0 L A = 0 := by
      unfold Sarkozy.Comparison.remainder
      ring
    rw [h0]
    linarith

end ZeroMean

/-! ## The data and the obligations -/

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

variable (blockOf) in
/-- **A2's `A2BlockDataTarget` without the mean credit `MC`**: `spec`, `hC`, `In`, `Gi`, `CL`, `ME`,
`SM`, as A2's. 7 fields. -/
structure JointBlockDataTarget (hW : Target.Weil) where
  /-- The paper's block laws with their inputs (`def:construction`(b)). *Open* (V2's `spec`). -/
  spec : ∀ b, PaperBlockSpec blockOf b
  /-- The tail inputs in correlation form (supplied by `ofProvedTail`). -/
  hC : TailInputsCorr PartV.P4
  /-- The per-block constants of the first stage (A1's `FirstStageInputs`). Data. -/
  In : FirstStageInputs blockOf
  /-- The gates of the Gram bracket (A2's `GramInputs`). *Open*. -/
  Gi : GramInputs blockOf spec
  /-- (CP4) at `a_T`. *Open*. -/
  CL : TheoremCBlock.ComparisonLaw targetDecay paperM0 (paperAtomMap blockOf) paperTail
    (paperSelAt (paperAtomMap blockOf) targetDecay) paperPP paperEP paperQueries
    (firstStageTarget blockOf hW spec hC In)
  /-- (CP6) at `a_T`, over A2's bracket. *Open* (B3's `EnvelopeRefinement.toME` builds it). -/
  ME : TheoremCBlock.MatchingEnvelopes targetDecay paperM0 (paperAtomMap blockOf) paperTail
    (gramBracketTarget blockOf hW spec hC In Gi) CL
  /-- (CP8)(c) at `a_T`. *Open*; read by no proof (see the module docstring). -/
  SM : TheoremCBlock.Summability targetDecay paperM0 (paperAtomMap blockOf) paperTail ME

variable {hW : Target.Weil}

/-- **To A2's data**, with `MC := zeroMeanCredit ME`. -/
noncomputable def JointBlockDataTarget.toA2 (D : JointBlockDataTarget blockOf hW) :
    A2BlockDataTarget blockOf hW where
  spec := D.spec
  hC := D.hC
  In := D.In
  Gi := D.Gi
  CL := D.CL
  ME := D.ME
  MC := zeroMeanCredit targetDecay D.ME
  SM := D.SM

/-- The block certificate data of `D` (K0's four prefix fields, the tail inputs, the laws). -/
noncomputable abbrev JointBlockDataTarget.cert (D : JointBlockDataTarget blockOf hW) :
    BlockCertDataTarget (paperAtomMap blockOf) hW :=
  D.toA2.toA1.toV2.toCertData

/-- The comparison data of `D` (`TheoremCBlock.ComparisonData` at `a_T`). -/
noncomputable abbrev JointBlockDataTarget.data (D : JointBlockDataTarget blockOf hW) :
    TheoremCBlock.ComparisonData targetDecay paperM0 (paperAtomMap blockOf) paperTail paperPr paperH
      Chamber :=
  D.cert.toData

variable (blockOf) in
/-- **The obligations of the joint endgame at `a_T`.** 9 fields: the data `Dv`; A2's `hB`, `hL₀`,
`hT`, `hSA`; the joint bound `JB`; A2's `SF`, `fix`, `env`. -/
structure JointFinalObligationsTarget (hW : Target.Weil) where
  /-- The data. -/
  Dv : JointBlockDataTarget blockOf hW
  /-- `B ≤` the ledger's `B` (A2's `hB_of_prices`). *Open*. -/
  hB : Dv.data.B ≤ targetLedger.B
  /-- `L₀ ≤` the ledger's `L₀` (A1's `hL₀_of_prices`). *Open*. -/
  hL₀ : Dv.data.L₀ ≤ targetLedger.L₀
  /-- `T ≤` the ledger's `T` ((CP6)). *Open*. -/
  hT : Dv.data.ME.T ≤ targetLedger.T
  /-- `S + A ≤` the ledger's `S + A` ((CP4)). *Open*. -/
  hSA : Dv.data.CL.S + Dv.data.CL.A ≤ targetLedger.S + targetLedger.A
  /-- **The joint comparison-and-mean bound with the ledger's joint constant** (`cor:joint-closing`,
  hypothesis; `eq:final-joint-closing`): robustly
  `63(Y_λ − Y_ν) − ½(e_L + e_R) ≤ (64 H − 1 + o(1)) Y` with
  `H = (63/64)𝓔 + (1 − m₁)/64 − Δ_mid − Δ_u + R_u`. In the paper: the comparison expansion with
  class costs and savings (`lem:record:record-expansion`, `cor:envelope-costs`, (E1)), the one-block
  mean credits (`prop:record:mean-credit`), the joint allocations `prop:joint-middle-mean` and
  `prop:joint-upper-mean`, and the residual gates of `cert:four-routes-closing`. *Open*. -/
  JB : JointBound Dv.data targetLedger.jointConstant
  /-- The sharp first-stage terms, per term. *Open* (G1's `SF`). -/
  SF : EnvelopeInputsBlock.SharpFirstInputs Dv.data
  /-- The fixed-interval envelope energies, per term. *Open* (G1's `fix`). -/
  fix : EnvelopeInputsBlock.FixedIntervalInputs (BlockAnchor.index_coprime_block Dv.data) Dv.data
  /-- The envelope energies, per term. *Open* (G1's `env`). -/
  env : EnvelopeInputsBlock.EnvelopeEnergyInputs (BlockAnchor.index_coprime_block Dv.data) Dv.data

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵` in the joint form** (`thm:main` at
`ε = 3/250000`, via `thm:comparison` with `cor:joint-closing` and `thm:density:induction` at
`a_T`): from `Weil` (the reference), H2″ (`cert:index-moment`, `paperRIAt_le_targetLedger`) and
`JointFinalObligationsTarget`. No mean credit (`hm`, `MC`), no class bounds (`CB`, `hΨ`, `hCB`) and
no (E1) obligation: the joint bound `JB` is the only comparison-and-mean input.
`MovingRoot` and `FourCycle` are not used here (they enter A2 only through `ofProvedTail`). -/
theorem main_target_paper_block_joint (hWeil : Target.Weil)
    (_hMovingRoot : Target.MovingRoot) (_hFourCycle : Target.FourCycle)
    (hThetaSmallRR : Target.ThetaSmallRR) (O : JointFinalObligationsTarget blockOf hWeil) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  theoremC_joint_reduced_target_of_ledger O.Dv.data (BlockAnchor.index_coprime_block O.Dv.data)
    targetLedger_bounds card_chamber O.Dv.data.B_nonneg O.hB O.hL₀ O.hT
    O.Dv.data.S.index.hR_I (paperRIAt_le_targetLedger hThetaSmallRR) O.hSA O.JB
    (O.SF.sharpFirstTerms targetDecay_nonneg) O.Dv.cert.densityCancellation
    (O.fix.fixedIntervalEnvelopeEnergies (BlockAnchor.index_coprime_block O.Dv.data)
      targetDecay_nonneg O.Dv.cert.indexMomentBound)
    (O.env.envelopeEnergies (BlockAnchor.index_coprime_block O.Dv.data) targetDecay_nonneg
      O.Dv.cert.indexMomentBound)
    O.Dv.cert.hunit

/-- The joint data with the proved tail input (`TailCorrCore.tailInputsCorr`), as A2's
`A2BlockDataTarget.ofProvedTail`. -/
noncomputable def JointBlockDataTarget.ofProvedTail (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (spec : ∀ b, PaperBlockSpec blockOf b)
    (In : FirstStageInputs blockOf) (Gi : GramInputs blockOf spec)
    (CL : TheoremCBlock.ComparisonLaw targetDecay paperM0 (paperAtomMap blockOf) paperTail
      (paperSelAt (paperAtomMap blockOf) targetDecay) paperPP paperEP paperQueries
      (firstStageTarget blockOf hW spec (TailCorrCore.tailInputsCorr hW hMR hFour) In))
    (ME : TheoremCBlock.MatchingEnvelopes targetDecay paperM0 (paperAtomMap blockOf) paperTail
      (gramBracketTarget blockOf hW spec (TailCorrCore.tailInputsCorr hW hMR hFour) In Gi) CL)
    (SM : TheoremCBlock.Summability targetDecay paperM0 (paperAtomMap blockOf) paperTail ME) :
    JointBlockDataTarget blockOf hW where
  spec := spec
  hC := TailCorrCore.tailInputsCorr hW hMR hFour
  In := In
  Gi := Gi
  CL := CL
  ME := ME
  SM := SM

/-- **Forgetting the mean credit of A2's data.** -/
def JointBlockDataTarget.ofA2 (D : A2BlockDataTarget blockOf hW) : JointBlockDataTarget blockOf hW where
  spec := D.spec
  hC := D.hC
  In := D.In
  Gi := D.Gi
  CL := D.CL
  ME := D.ME
  SM := D.SM

/-! ## With B3's (CP6) and (CP8)(c) -/

variable (blockOf) in
/-- **B3's `B3BlockDataTarget` without the mean input `MI`**: `spec`, `hC`, `In`, `Gi`, `CL`, the
refinement `F`, the side sums `hTs` and the summability input `SI`. 8 fields. -/
structure JointB3BlockData (hW : Target.Weil) where
  spec : ∀ b, PaperBlockSpec blockOf b
  hC : TailInputsCorr PartV.P4
  In : FirstStageInputs blockOf
  Gi : GramInputs blockOf spec
  CL : TheoremCBlock.ComparisonLaw targetDecay paperM0 (paperAtomMap blockOf) paperTail
    (paperSelAt (paperAtomMap blockOf) targetDecay) paperPP paperEP paperQueries
    (firstStageTarget blockOf hW spec hC In)
  /-- The refined part of the matching envelopes (`prop:record:matching`(i)). *Open*. -/
  F : EnvelopeRefinement (gramBracketTarget blockOf hW spec hC In Gi) CL
  /-- The side sums of (CP6) against the ledger's `T`. *Open*. -/
  hTs : ∀ L, ∑ b, F.priceL L b ≤ targetLedger.T ∧ ∑ b, F.priceR L b ≤ targetLedger.T
  /-- The weighted summability of the (CP4) prices and of the added diagonals. *Open*. -/
  SI : SummabilityInputs paperPP paperEP F

/-- **To the joint data**: `ME := F.toME a_T T^{ledger} …`, `SM := summabilityOf …`. -/
noncomputable def JointB3BlockData.toJoint (D : JointB3BlockData blockOf hW) :
    JointBlockDataTarget blockOf hW where
  spec := D.spec
  hC := D.hC
  In := D.In
  Gi := D.Gi
  CL := D.CL
  ME := D.F.toME targetDecay targetLedger.T (fun L => (D.hTs L).1) (fun L => (D.hTs L).2)
  SM := summabilityOf D.F targetLedger.T (fun L => (D.hTs L).1) (fun L => (D.hTs L).2)
    paper_sel_nonneg (paper_stagePrice_tail hW D.spec D.hC D.In D.Gi) D.SI

variable (blockOf) in
/-- **The obligations of the joint endgame with B3's constructions.** 8 fields: `Dv`, `hB`, `hL₀`,
`hSA`, `JB`, `SF`, `fix`, `env`; `hT` is proved (`ME.T = T^{ledger}`). -/
structure JointB3FinalObligations (hW : Target.Weil) where
  Dv : JointB3BlockData blockOf hW
  hB : Dv.toJoint.data.B ≤ targetLedger.B
  hL₀ : Dv.toJoint.data.L₀ ≤ targetLedger.L₀
  hSA : Dv.toJoint.data.CL.S + Dv.toJoint.data.CL.A ≤ targetLedger.S + targetLedger.A
  /-- The joint bound (`cor:joint-closing`, `eq:final-joint-closing`). *Open*. -/
  JB : JointBound Dv.toJoint.data targetLedger.jointConstant
  SF : EnvelopeInputsBlock.SharpFirstInputs Dv.toJoint.data
  fix : EnvelopeInputsBlock.FixedIntervalInputs (BlockAnchor.index_coprime_block Dv.toJoint.data)
    Dv.toJoint.data
  env : EnvelopeInputsBlock.EnvelopeEnergyInputs (BlockAnchor.index_coprime_block Dv.toJoint.data)
    Dv.toJoint.data

/-- To the joint obligations, with `hT := le_refl`. -/
noncomputable def JointB3FinalObligations.toJoint (O : JointB3FinalObligations blockOf hW) :
    JointFinalObligationsTarget blockOf hW where
  Dv := O.Dv.toJoint
  hB := O.hB
  hL₀ := O.hL₀
  hT := le_refl _
  hSA := O.hSA
  JB := O.JB
  SF := O.SF
  fix := O.fix
  env := O.env

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵` in the joint form, with B3's (CP6) and
(CP8)(c)** (`thm:main` via `cor:joint-closing`): `main_target_paper_block_joint` with
`JointB3FinalObligations.toJoint`. -/
theorem main_target_paper_block_joint_B3 (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmallRR : Target.ThetaSmallRR) (O : JointB3FinalObligations blockOf hWeil) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_block_joint hWeil hMovingRoot hFourCycle hThetaSmallRR O.toJoint

end Sarkozy.JointClosing
