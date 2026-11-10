module

public import Sarkozy.EnvelopesPaper.Mean
public import Sarkozy.EnvelopesPaper.Summability
public import Sarkozy.GramBracketPaper.Main
public import Sarkozy.GramBracketPaper.ProvedTail

@[expose] public section






open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopesPaper

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
open Sarkozy.GramBracketPaper
open Sarkozy.PartVLaws (PaperBlockSpec v2Reference TailInputsCorr paperAtomMap PaperAtom)

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

/-! ## The paper's data: positivity of the prices, no first-stage record at a tail atom -/

omit [Fintype B] in
/-- The paper's selection factors at `a_T` are nonnegative (`paperSelAt ≥ 1`, `p^{2a} ≥ 0`). -/
theorem paper_sel_nonneg (L : ℕ) (b : BlockFrame.BlockAtom (PaperAtom B) PaperJt L) :
    0 ≤ TheoremCBlock.selectionFactor targetDecay paperTail
      (paperSelAt (paperAtomMap blockOf) targetDecay) L b := by
  cases b with
  | inl β =>
    exact le_trans zero_le_one
      (one_le_paperSelAt (paperAtomMap blockOf) TargetLedger.targetDecay_nonneg β)
  | inr j => exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- **A1's first stage and A2's bracket carry no record at a tail atom** (`firstStageOfAtoms`,
`gramBracketOfAtoms`): `p_𝔟 + v_𝔟 + d_𝔟 + u_𝔟 = 0` there. -/
theorem paper_stagePrice_tail (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (In : FirstStageInputs blockOf) (Gi : GramInputs blockOf spec)
    (L : ℕ) (j : PaperJt L) :
    stagePrice (firstStageTarget blockOf hW spec hC In) (gramBracketTarget blockOf hW spec hC In Gi)
      L (.inr j) = 0 := by
  unfold stagePrice TheoremCBlock.FirstStage.pvar TheoremCBlock.FirstStage.vprice
    TheoremCBlock.FirstStage.dprice TheoremCBlock.GramBracket.uprice
  have h1 : ∑ i, |(firstStageTarget blockOf hW spec hC In).ca L (.inr j) i| *
      TheoremC.mass ((firstStageTarget blockOf hW spec hC In).κa L (.inr j) i) *
      TheoremCBlock.selectionFactor targetDecay paperTail
        (paperSelAt (paperAtomMap blockOf) targetDecay) L (.inr j) = 0 := by
    with_unfolding_all exact Finset.sum_eq_zero fun i _ => Empty.elim i
  have h2 : ∑ i, (TheoremC.mass ((firstStageTarget blockOf hW spec hC In).κ L (.inr j) i) +
      TheoremC.mass ((firstStageTarget blockOf hW spec hC In).κ' L (.inr j) i)) *
      TheoremCBlock.selectionFactor targetDecay paperTail
        (paperSelAt (paperAtomMap blockOf) targetDecay) L (.inr j) = 0 := by
    with_unfolding_all exact Finset.sum_eq_zero fun i _ => Empty.elim i
  have h3 : ∑ i, sharpPrice (TheoremCBlock.selectionFactor targetDecay paperTail
        (paperSelAt (paperAtomMap blockOf) targetDecay) L (.inr j))
      ((firstStageTarget blockOf hW spec hC In).κ L (.inr j) i)
      ((firstStageTarget blockOf hW spec hC In).dconst L (.inr j) i) = 0 := by
    with_unfolding_all exact Finset.sum_eq_zero fun i _ => Empty.elim i
  have h4 : ∑ i, TheoremC.mass ((gramBracketTarget blockOf hW spec hC In Gi).κu L (.inr j) i) *
      TheoremCBlock.selectionFactor targetDecay paperTail
        (paperSelAt (paperAtomMap blockOf) targetDecay) L (.inr j) = 0 := by
    with_unfolding_all exact Finset.sum_eq_zero fun i _ => Empty.elim i
  rw [h1, h2, h3, h4]
  norm_num

/-! ## The block data -/

variable (blockOf) in
/-- **A2's `A2BlockDataTarget` with (CP6)–(CP8) assembled.** `spec`, `hC`, `In`, `Gi`, `CL` as in
A2; `ME`, `MC`, `SM` replaced by the refinement `F`, the side sums `hTs`, the mean input `MI` and
the summability input `SI`. 9 fields. -/
structure B3BlockDataTarget (hW : Target.Weil) where
  /-- The paper's block laws with their inputs (`def:construction`(b)). *Open* (V2's `spec`). -/
  spec : ∀ b, PaperBlockSpec blockOf b
  /-- The tail inputs in correlation form, proved in `TailCorrCore.ProvedTail`. -/
  hC : TailInputsCorr PartV.P4
  /-- The per-block constants of the first stage (A1's `FirstStageInputs`). Data. -/
  In : FirstStageInputs blockOf
  /-- The gates of the Gram bracket (A2's `GramInputs`). *Open*. -/
  Gi : GramInputs blockOf spec
  /-- (CP4) at `a_T`. *Open* (Part V; built separately). -/
  CL : TheoremCBlock.ComparisonLaw targetDecay paperM0 (paperAtomMap blockOf) paperTail
    (paperSelAt (paperAtomMap blockOf) targetDecay) paperPP paperEP paperQueries
    (firstStageTarget blockOf hW spec hC In)
  /-- **The refined part of the matching envelopes** (`prop:record:matching`(i), middle-block
  step; `prop:signed-sides`). *Open*; `trivialRefinement` shows it is satisfiable. -/
  F : EnvelopeRefinement (gramBracketTarget blockOf hW spec hC In Gi) CL
  /-- **The side sums of (CP6) against the ledger's `T`** (`prop:record:matching`(ii)): at every
  scale, `∑_𝔟 price(M_s - Ñ) ≤ T^{ledger}` for both sides. *Open*. -/
  hTs : ∀ L, ∑ b, F.priceL L b ≤ targetLedger.T ∧ ∑ b, F.priceR L b ≤ targetLedger.T
  /-- **The mean bound on the cores** (`prop:record:mean-credit`, after Step 1). *Open*. -/
  MI : MeanInputs targetDecay F
  /-- **The weighted summability of the (CP4) prices and of the added diagonals**
  (`def:cp8`(c)). *Open*. -/
  SI : SummabilityInputs paperPP paperEP F

variable {hW : Target.Weil}

/-- The matching envelopes of the block data. -/
noncomputable def B3BlockDataTarget.ME (D : B3BlockDataTarget blockOf hW) :
    TheoremCBlock.MatchingEnvelopes targetDecay paperM0 (paperAtomMap blockOf) paperTail
      (gramBracketTarget blockOf hW D.spec D.hC D.In D.Gi) D.CL :=
  D.F.toME targetDecay targetLedger.T (fun L => (D.hTs L).1) (fun L => (D.hTs L).2)

/-- **To A2's data**: `ME := F.toME …`, `MC := meanCreditOf …`, `SM := summabilityOf …`. -/
noncomputable def B3BlockDataTarget.toA2 (D : B3BlockDataTarget blockOf hW) :
    A2BlockDataTarget blockOf hW where
  spec := D.spec
  hC := D.hC
  In := D.In
  Gi := D.Gi
  CL := D.CL
  ME := D.ME
  MC := meanCreditOf D.F targetLedger.T (fun L => (D.hTs L).1) (fun L => (D.hTs L).2) D.MI
  SM := summabilityOf D.F targetLedger.T (fun L => (D.hTs L).1) (fun L => (D.hTs L).2)
    paper_sel_nonneg (paper_stagePrice_tail hW D.spec D.hC D.In D.Gi) D.SI

/-- **`hT` holds**: the matching exponent of `toA2` is the ledger's `T`. -/
theorem B3BlockDataTarget.hT (D : B3BlockDataTarget blockOf hW) :
    D.toA2.toA1.toV2.toCertData.toData.ME.T ≤ targetLedger.T := le_refl _

/-- The mean credit of `toA2` is the input's `m`. -/
theorem B3BlockDataTarget.MC_m (D : B3BlockDataTarget blockOf hW) :
    D.toA2.toA1.toV2.toCertData.toData.MC.m = D.MI.m := rfl

/-- **The side sums from the paper's split** `T = T_K + T_oth` (`subsec:matching-envelopes`): the
added diagonals cost at most `T_K` on either side, the non-replaced norm envelopes at most `T_oth`,
and `T_K + T_oth ≤ T^{ledger}`. -/
theorem hTs_of_bounds {spec : ∀ b, PaperBlockSpec blockOf b}
    {hC : TailInputsCorr PartV.P4} {In : FirstStageInputs blockOf} {Gi : GramInputs blockOf spec}
    {CL : TheoremCBlock.ComparisonLaw targetDecay paperM0 (paperAtomMap blockOf)
      paperTail (paperSelAt (paperAtomMap blockOf) targetDecay) paperPP paperEP paperQueries
      (firstStageTarget blockOf hW spec hC In)}
    (F : EnvelopeRefinement (gramBracketTarget blockOf hW spec hC In Gi) CL) {TK Toth : ℝ}
    (hK : ∀ L, ∑ b, F.KpriceL L b ≤ TK ∧ ∑ b, F.KpriceR L b ≤ TK)
    (hoth : ∀ L, ∑ b, F.otherPrice L b ≤ Toth) (hsum : TK + Toth ≤ targetLedger.T) (L : ℕ) :
    ∑ b, F.priceL L b ≤ targetLedger.T ∧ ∑ b, F.priceR L b ≤ targetLedger.T := by
  have e1 : ∑ b, F.priceL L b = ∑ b, F.KpriceL L b + ∑ b, F.otherPrice L b := by
    rw [← sum_add_distrib]
    rfl
  have e2 : ∑ b, F.priceR L b = ∑ b, F.KpriceR L b + ∑ b, F.otherPrice L b := by
    rw [← sum_add_distrib]
    rfl
  rw [e1, e2]
  have := hK L
  have := hoth L
  constructor <;> linarith

variable (blockOf) in
/-- **A2's `A2FinalObligationsTarget` with (CP6)–(CP8) assembled.** 12 fields: the data `Dv` and
T1's eleven obligations other than `hT` (proved, `B3BlockDataTarget.hT`), verbatim over
`Dv.toA2.toA1`; `hm` is over `Dv.MI.m`. -/
structure B3FinalObligationsTarget (hW : Target.Weil) where
  /-- The data. -/
  Dv : B3BlockDataTarget blockOf hW
  /-- The (CP5) class bounds at `a_T`. *Open* (Part V). -/
  CB : TheoremCBlock.ClassBounds targetDecay paperM0 (paperAtomMap blockOf) paperTail
    Dv.toA2.toA1.toV2.toCertData.toData.CL
  /-- The complete polynomial with class bounds is at most the ledger's `E`. *Open*. -/
  hΨ : ∀ L, ∑ ω ∈ univ.filter
      (fun ω : Choice (Dv.toA2.toA1.toV2.toCertData.toData.CL.T L) => IsSelection ω),
    (if CB.cls L ω = none then
      Dv.toA2.toA1.toV2.toCertData.toData.B *
        monomial (Dv.toA2.toA1.toV2.toCertData.toData.CL.π L) ω
      else CB.phi L ω) ≤ targetLedger.E
  /-- The class bounds are robust with nonnegative remainders. *Open*. -/
  hCB : CB.RobustNonneg
  /-- `B ≤` the ledger's `B` (A2's `hB_of_prices`). *Open*. -/
  hB : Dv.toA2.toA1.toV2.toCertData.toData.B ≤ targetLedger.B
  /-- `L₀ ≤` the ledger's `L₀`. *Open*. -/
  hL₀ : Dv.toA2.toA1.toV2.toCertData.toData.L₀ ≤ targetLedger.L₀
  /-- `S + A ≤` the ledger's `S + A`. *Open*. -/
  hSA : Dv.toA2.toA1.toV2.toCertData.toData.CL.S + Dv.toA2.toA1.toV2.toCertData.toData.CL.A ≤
    targetLedger.S + targetLedger.A
  /-- The mean credit pays the joint-closing allocations. *Open*; see the caution in the module
  docstring. -/
  hm : targetLedger.m₁ + 64 * ((targetLedger.deltaAlpha + targetLedger.deltaMatching +
    targetLedger.deltaOdd + targetLedger.deltaEven) + targetLedger.deltaUpper -
    targetLedger.upperError) ≤ Dv.MI.m
  /-- (E1), per term. *Open* (G1's `E1`). -/
  E1 : EnvelopeInputsBlock.EnvelopeBoundInputs Dv.toA2.toA1.toV2.toCertData.toData
  /-- The sharp first-stage terms, per term. *Open* (G1's `SF`). -/
  SF : EnvelopeInputsBlock.SharpFirstInputs Dv.toA2.toA1.toV2.toCertData.toData
  /-- The fixed-interval envelope energies, per term. *Open* (G1's `fix`). -/
  fix : EnvelopeInputsBlock.FixedIntervalInputs
    (BlockAnchor.index_coprime_block Dv.toA2.toA1.toV2.toCertData.toData)
    Dv.toA2.toA1.toV2.toCertData.toData
  /-- The envelope energies, per term. *Open* (G1's `env`). -/
  env : EnvelopeInputsBlock.EnvelopeEnergyInputs
    (BlockAnchor.index_coprime_block Dv.toA2.toA1.toV2.toCertData.toData)
    Dv.toA2.toA1.toV2.toCertData.toData

/-- **To A2's obligations**: `Dv := Dv.toA2`, `hT := Dv.hT`, the other eleven fields copied. -/
noncomputable def B3FinalObligationsTarget.toA2 (O : B3FinalObligationsTarget blockOf hW) :
    A2FinalObligationsTarget blockOf hW where
  Dv := O.Dv.toA2
  CB := O.CB
  hΨ := O.hΨ
  hCB := O.hCB
  hB := O.hB
  hL₀ := O.hL₀
  hT := O.Dv.hT
  hSA := O.hSA
  hm := O.hm
  E1 := O.E1
  SF := O.SF
  fix := O.fix
  env := O.env

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵`, with (CP6)–(CP8) assembled**
(`thm:main` at `ε = a_T/71`, via `thm:comparison` and `thm:density:induction` at `a_T`): from the
literature inputs (`Weil`, `MovingRoot`, `FourCycle`, H2″) and
`B3FinalObligationsTarget blockOf`, in which (CP6) is `EnvelopeRefinement.toME` (`def:cp6`,
`prop:record:matching`), (CP7) is `meanCreditOf` (`def:cp7`, `prop:record:mean-credit` Step 1) and
(CP8)(c) is `summabilityOf` (`def:cp8`), over A2's (CP3) and any (CP4). -/
theorem main_target_paper_block_B3 (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmallRR : Target.ThetaSmallRR) (O : B3FinalObligationsTarget blockOf hWeil) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_block_A2 hWeil hMovingRoot hFourCycle hThetaSmallRR O.toA2

/-- B3's block data with the proved tail input (`TailCorrCore.tailInputsCorr`), as A2's
`A2BlockDataTarget.ofProvedTail`. -/
noncomputable def B3BlockDataTarget.ofProvedTail (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (spec : ∀ b, PaperBlockSpec blockOf b)
    (In : FirstStageInputs blockOf) (Gi : GramInputs blockOf spec)
    (CL : TheoremCBlock.ComparisonLaw targetDecay paperM0 (paperAtomMap blockOf) paperTail
      (paperSelAt (paperAtomMap blockOf) targetDecay) paperPP paperEP paperQueries
      (firstStageTarget blockOf hW spec (TailCorrCore.tailInputsCorr hW hMR hFour) In))
    (F : EnvelopeRefinement
      (gramBracketTarget blockOf hW spec (TailCorrCore.tailInputsCorr hW hMR hFour) In Gi) CL)
    (hTs : ∀ L, ∑ b, F.priceL L b ≤ targetLedger.T ∧ ∑ b, F.priceR L b ≤ targetLedger.T)
    (MI : MeanInputs targetDecay F) (SI : SummabilityInputs paperPP paperEP F) :
    B3BlockDataTarget blockOf hW where
  spec := spec
  hC := TailCorrCore.tailInputsCorr hW hMR hFour
  In := In
  Gi := Gi
  CL := CL
  F := F
  hTs := hTs
  MI := MI
  SI := SI

end Sarkozy.EnvelopesPaper
