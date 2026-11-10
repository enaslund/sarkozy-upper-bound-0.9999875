module

public import Sarkozy.GramBracketPaper.Paper
public import Sarkozy.FirstStagePaper.Main

@[expose] public section

/-!
# The main statement at `a_T` with the first stage and the Gram bracket constructed

A1's `FirstStagePaper.main_target_paper_block_A1` with the obligation `GB` (`def:cp3` at `a_T`)
replaced by the paper's construction `gramBracketTarget blockOf hW spec hC In Gi`
(`Sarkozy.GramBracketPaper.Paper`): V3's bracket of `lem:record:gram` on the middle blocks, `Ñ = μ`
elsewhere, over A1's first stage `firstStageTarget`.

* `A2BlockDataTarget`: A1's `A1BlockDataTarget` (8 fields: `spec`, `hC`, `In`, `GB`, `CL`, `ME`,
  `MC`, `SM`) with `GB` replaced by `Gi : GramInputs blockOf spec` (one gate per middle block:
  the protection `v_D ≥ 2 k_D w_D`, `eq:protection`); `ME`, `MC`, `SM` are over
  the constructed bracket. `toA1` maps it to A1's structure, with `GB := gramBracketTarget …`.
* `A2FinalObligationsTarget`: A1's `A1FinalObligationsTarget` (13 fields) over `A2BlockDataTarget`;
  the other twelve fields are A1's (T1's), verbatim with `Dv.toA1`. `toA1` maps it to A1's.
* **`main_target_paper_block_A2`**: the bound `N^{1 − a_T/71}` from the literature inputs and
  `A2FinalObligationsTarget blockOf hWeil`.
* `hB_of_prices`: the obligation `hB` (`B ≤ B^{ledger}`) from upper bounds of the explicit sums
  `U₀ = ∑_𝔅 u_𝔅` (`gramBracketTarget_U₀_eq`, `specUprice`, `lem:record:middle-prices`) and of the
  first-stage tag totals `d_j`, `v_j` (A1's `paperStage` prices), with
  `e^{U'} (1 + 𝔗(d', v')) ≤ B^{ledger}` (`def:closing-quantities`: `B = e^{U₀} + R_err`,
  `R_err = e^{U₀} 𝔗(d, v)`).

**Field count.** The structure has 19 proof obligations, with `GB` replaced by the per-block
protection gate `Gi`. The tail obligation `hC` is now supplied by
`A2BlockDataTarget.ofProvedTail`; 18 obligations remain. They are `spec`, `Gi`, `CL`, `ME`,
`MC`, `SM` and T1's twelve (`CB`, `hΨ`, `hCB`, `hB`,
`hL₀`, `hT`, `hSA`, `hm`, `E1`, `SF`, `fix`, `env`). `In` is data, as in A1. `hB` now compares the
constructed bracket with the ledger.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.GramBracketPaper

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
open Sarkozy.PartVLaws (PaperBlockSpec v2Reference TailInputsCorr paperAtomMap)

variable {B : Type} [Fintype B] [DecidableEq B] (blockOf : PaperJ0 → B)

/-- **A1's `A1BlockDataTarget` with the Gram bracket constructed** (`def:cp3` by
`gramBracketTarget`): `spec`, `hC`, the first-stage constants `In`, the Gram gates `Gi`, and the
Part V data `CL`, `ME`, `MC`, `SM` at `a_T`, with `ME` over the constructed bracket. 8 fields. -/
structure A2BlockDataTarget (hW : Target.Weil) where
  /-- The paper's block laws with their inputs (`def:construction`(b)). *Open* (V2's `spec`). -/
  spec : ∀ b, PaperBlockSpec blockOf b
  /-- The tail inputs in correlation form, proved in `TailCorrCore.ProvedTail`. -/
  hC : TailInputsCorr PartV.P4
  /-- The per-block constants of the first stage (A1's `FirstStageInputs`). Data. -/
  In : FirstStageInputs blockOf
  /-- **The gates of the Gram bracket** (`GramInputs`): the protection `v_D ≥ 2 k_D w_D`
  (`eq:protection`) on every middle block. The 33 recorded gates are proved in
  `MiddleRecords.PieceCompletion`; the paper's full specification remains to be supplied.
  Replaces A1's `GB`. -/
  Gi : GramInputs blockOf spec
  /-- (CP4) at `a_T`. *Open* (Part V). -/
  CL : TheoremCBlock.ComparisonLaw targetDecay paperM0 (paperAtomMap blockOf) paperTail
    (paperSelAt (paperAtomMap blockOf) targetDecay) paperPP paperEP paperQueries
    (firstStageTarget blockOf hW spec hC In)
  /-- (CP6) at `a_T`, over the constructed bracket. *Open* (Part V). -/
  ME : TheoremCBlock.MatchingEnvelopes targetDecay paperM0 (paperAtomMap blockOf) paperTail
    (gramBracketTarget blockOf hW spec hC In Gi) CL
  /-- (CP7) at `a_T`. *Open* (Part V). -/
  MC : TheoremCBlock.MeanCredit targetDecay paperM0 (paperAtomMap blockOf) paperTail ME
  /-- (CP8) at `a_T`. *Open* (Part V). -/
  SM : TheoremCBlock.Summability targetDecay paperM0 (paperAtomMap blockOf) paperTail ME

variable {blockOf}

/-- **To A1's data**: `GB := gramBracketTarget blockOf hW spec hC In Gi`, the other seven fields
copied. -/
noncomputable def A2BlockDataTarget.toA1 {hW : Target.Weil} (D : A2BlockDataTarget blockOf hW) :
    A1BlockDataTarget blockOf hW where
  spec := D.spec
  hC := D.hC
  In := D.In
  GB := gramBracketTarget blockOf hW D.spec D.hC D.In D.Gi
  CL := D.CL
  ME := D.ME
  MC := D.MC
  SM := D.SM

variable (blockOf)

/-- **A1's `A1FinalObligationsTarget` with the Gram bracket constructed.** 13 fields: the data `Dv`
and A1's (T1's) other twelve, verbatim over `Dv.toA1`. -/
structure A2FinalObligationsTarget (hW : Target.Weil) where
  /-- The data, with the first stage and the Gram bracket constructed. -/
  Dv : A2BlockDataTarget blockOf hW
  /-- The (CP5) class bounds at `a_T`. *Open* (Part V). -/
  CB : TheoremCBlock.ClassBounds targetDecay paperM0 (paperAtomMap blockOf) paperTail
    Dv.toA1.toV2.toCertData.toData.CL
  /-- The complete polynomial with class bounds is at most the ledger's `E`. *Open*. -/
  hΨ : ∀ L, ∑ ω ∈ univ.filter
      (fun ω : Choice (Dv.toA1.toV2.toCertData.toData.CL.T L) => IsSelection ω),
    (if CB.cls L ω = none then
      Dv.toA1.toV2.toCertData.toData.B * monomial (Dv.toA1.toV2.toCertData.toData.CL.π L) ω
      else CB.phi L ω) ≤ targetLedger.E
  /-- The class bounds are robust with nonnegative remainders. *Open*. -/
  hCB : CB.RobustNonneg
  /-- `B ≤` the ledger's `B`, for the constructed bracket (`hB_of_prices`). *Open*. -/
  hB : Dv.toA1.toV2.toCertData.toData.B ≤ targetLedger.B
  /-- `L₀ ≤` the ledger's `L₀`, for the constructed first stage (A1's `hL₀_of_prices`). *Open*. -/
  hL₀ : Dv.toA1.toV2.toCertData.toData.L₀ ≤ targetLedger.L₀
  /-- `T ≤` the ledger's `T`. *Open*. -/
  hT : Dv.toA1.toV2.toCertData.toData.ME.T ≤ targetLedger.T
  /-- `S + A ≤` the ledger's `S + A`. *Open*. -/
  hSA : Dv.toA1.toV2.toCertData.toData.CL.S + Dv.toA1.toV2.toCertData.toData.CL.A ≤
    targetLedger.S + targetLedger.A
  /-- The mean credit pays the joint-closing allocations. *Open*. -/
  hm : targetLedger.m₁ + 64 * ((targetLedger.deltaAlpha + targetLedger.deltaMatching +
    targetLedger.deltaOdd + targetLedger.deltaEven) + targetLedger.deltaUpper -
    targetLedger.upperError) ≤ Dv.toA1.toV2.toCertData.toData.MC.m
  /-- (E1), per term. *Open* (G1's `E1`). -/
  E1 : EnvelopeInputsBlock.EnvelopeBoundInputs Dv.toA1.toV2.toCertData.toData
  /-- The sharp first-stage terms, per term. *Open* (G1's `SF`). -/
  SF : EnvelopeInputsBlock.SharpFirstInputs Dv.toA1.toV2.toCertData.toData
  /-- The fixed-interval envelope energies, per term. *Open* (G1's `fix`). -/
  fix : EnvelopeInputsBlock.FixedIntervalInputs
    (BlockAnchor.index_coprime_block Dv.toA1.toV2.toCertData.toData) Dv.toA1.toV2.toCertData.toData
  /-- The envelope energies, per term. *Open* (G1's `env`). -/
  env : EnvelopeInputsBlock.EnvelopeEnergyInputs
    (BlockAnchor.index_coprime_block Dv.toA1.toV2.toCertData.toData) Dv.toA1.toV2.toCertData.toData

variable {blockOf}

/-- **To A1's obligations**: `Dv := Dv.toA1`, the other twelve fields copied. -/
noncomputable def A2FinalObligationsTarget.toA1 {hW : Target.Weil}
    (O : A2FinalObligationsTarget blockOf hW) : A1FinalObligationsTarget blockOf hW where
  Dv := O.Dv.toA1
  CB := O.CB
  hΨ := O.hΨ
  hCB := O.hCB
  hB := O.hB
  hL₀ := O.hL₀
  hT := O.hT
  hSA := O.hSA
  hm := O.hm
  E1 := O.E1
  SF := O.SF
  fix := O.fix
  env := O.env

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵`, with the first stage and the Gram bracket
of the paper's construction** (`thm:main` at `ε = a_T/71`, via `thm:comparison` and
`thm:density:induction` at `a_T`): from the literature inputs (`Weil`,
`MovingRoot`, `FourCycle`, H2″) and `A2FinalObligationsTarget blockOf`, in which (CP2) is A1's
`firstStageTarget` and (CP3) is `gramBracketTarget` (`def:cp3`, `lem:record:gram`), from the named
inputs `FirstStageInputs` (data) and `GramInputs` (the protection `eq:protection`
on the middle blocks). -/
theorem main_target_paper_block_A2 (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmallRR : Target.ThetaSmallRR) (O : A2FinalObligationsTarget blockOf hWeil) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_block_A1 hWeil hMovingRoot hFourCycle hThetaSmallRR O.toA1

/-- **`hB` from bounds of the explicit per-block sums** (`def:closing-quantities`: `B = e^{U₀} +
R_err`, `R_err = e^{U₀} 𝔗(d, v)`; `def:cp3`; `lem:record:middle-prices`): the bracket total is
`U₀ = ∑_𝔅 specUprice(𝔅)` over the class-three blocks (`gramBracketTarget_U₀_eq`: on a middle
block `P(r)⁻¹ (2 v_D r² + 2 v_D (f₁ + h₁) r³ + 12 w_S r/(bmin - 3)) q_𝔅^{2a}`, zero on an upper
block), and the tag totals are A1's sums of the per-block first-stage prices. If these sums are at
most `U'`, `d'_j`, `v'_j` and `e^{U'} (1 + 𝔗(d', v')) ≤ B^{ledger}`, then `hB` holds. -/
theorem hB_of_prices {hW : Target.Weil} (D : A2BlockDataTarget blockOf hW) {U' : ℝ}
    {d' v' : Fin 2 → ℝ}
    (hU : ∑ b, specUprice D.In (D.spec b)
      (paperSelAt (paperAtomMap blockOf) targetDecay (.inr b)) ≤ U')
    (hd : ∀ j, ∑ β, (paperStage blockOf hW D.spec D.hC D.In β).dTag
      (paperSelAt (paperAtomMap blockOf) targetDecay β) j ≤ d' j)
    (hv : ∀ j, ∑ β, (paperStage blockOf hW D.spec D.hC D.In β).vTag
      (paperSelAt (paperAtomMap blockOf) targetDecay β) j ≤ v' j)
    (hcost : Real.exp U' * (1 + tagSeries d' v') ≤ targetLedger.B) :
    D.toA1.toV2.toCertData.toData.B ≤ targetLedger.B := by
  refine le_trans ?_ hcost
  have hsel : ∀ β, 0 ≤ paperSelAt (paperAtomMap blockOf) targetDecay β := fun β =>
    le_trans zero_le_one
      (one_le_paperSelAt (paperAtomMap blockOf) TargetLedger.targetDecay_nonneg β)
  have hd0 : ∀ j, 0 ≤ ∑ β, (paperStage blockOf hW D.spec D.hC D.In β).dTag
      (paperSelAt (paperAtomMap blockOf) targetDecay β) j :=
    fun j => sum_nonneg fun β _ => AtomStage.dTag_nonneg _ (hsel β) j
  have hv0 : ∀ j, 0 ≤ ∑ β, (paperStage blockOf hW D.spec D.hC D.In β).vTag
      (paperSelAt (paperAtomMap blockOf) targetDecay β) j :=
    fun j => sum_nonneg fun β _ => AtomStage.vTag_nonneg _ (hsel β) j
  change Real.exp (gramBracketTarget blockOf hW D.spec D.hC D.In D.Gi).U₀ +
      Real.exp (gramBracketTarget blockOf hW D.spec D.hC D.In D.Gi).U₀ *
        tagSeries (firstStageTarget blockOf hW D.spec D.hC D.In).dT
          (firstStageTarget blockOf hW D.spec D.hC D.In).vT ≤ _
  rw [gramBracketTarget_U₀_eq, firstStageTarget_eq]
  have hT : tagSeries
      (firstStagePaper blockOf targetDecay (paperSelAt (paperAtomMap blockOf) targetDecay) hW
        D.spec D.hC D.In).dT
      (firstStagePaper blockOf targetDecay (paperSelAt (paperAtomMap blockOf) targetDecay) hW
        D.spec D.hC D.In).vT ≤ tagSeries d' v' :=
    tagSeries_mono hd0 hv0 hd hv
  have hT0 : 0 ≤ tagSeries
      (firstStagePaper blockOf targetDecay (paperSelAt (paperAtomMap blockOf) targetDecay) hW
        D.spec D.hC D.In).dT
      (firstStagePaper blockOf targetDecay (paperSelAt (paperAtomMap blockOf) targetDecay) hW
        D.spec D.hC D.In).vT :=
    tagSeries_nonneg hd0 hv0
  have hE := Real.exp_le_exp.mpr hU
  have hpos := Real.exp_pos (∑ b, specUprice D.In (D.spec b)
    (paperSelAt (paperAtomMap blockOf) targetDecay (.inr b)))
  nlinarith

/-- **`hB` from the block bounds of `lem:record:middle-prices`** (`subsec:middle-frame-prices`): if
every middle block has the scale `r = bmin^{-1/2}` (`specScale`), the sum of the block bounds
`(2 v_D r² + (2 v_D (f₁ + h₁) + 12 w_S/(1 - 3/X)) r³) q_𝔅^{2a}` (`specUbound`) is at most `U'`, the
first-stage tag sums are at most `d'`, `v'`, and `e^{U'} (1 + 𝔗(d', v')) ≤ B^{ledger}`, then `hB`
holds. This is the form in which the paper evaluates `U₀` (summed with the block charges `b₂`,
`b₃` of the pieces). -/
theorem hB_of_charges {hW : Target.Weil} (D : A2BlockDataTarget blockOf hW)
    (hsc : ∀ b, specScale D.In (D.spec b)) {U' : ℝ} {d' v' : Fin 2 → ℝ}
    (hU : ∑ b, specUbound D.In (D.spec b)
      (paperSelAt (paperAtomMap blockOf) targetDecay (.inr b)) ≤ U')
    (hd : ∀ j, ∑ β, (paperStage blockOf hW D.spec D.hC D.In β).dTag
      (paperSelAt (paperAtomMap blockOf) targetDecay β) j ≤ d' j)
    (hv : ∀ j, ∑ β, (paperStage blockOf hW D.spec D.hC D.In β).vTag
      (paperSelAt (paperAtomMap blockOf) targetDecay β) j ≤ v' j)
    (hcost : Real.exp U' * (1 + tagSeries d' v') ≤ targetLedger.B) :
    D.toA1.toV2.toCertData.toData.B ≤ targetLedger.B := by
  have h := gramBracketTarget_U₀_le hW D.spec D.hC D.In D.Gi hsc
  rw [gramBracketTarget_U₀_eq] at h
  exact hB_of_prices D (h.trans hU) hd hv hcost

end Sarkozy.GramBracketPaper
