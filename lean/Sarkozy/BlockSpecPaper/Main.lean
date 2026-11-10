module

public import Sarkozy.BlockSpecPaper.Caps
public import Sarkozy.GramBracketPaper.ProvedTail

@[expose] public section







open Finset
open scoped BigOperators

namespace Sarkozy.BlockSpecPaper

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper
open Sarkozy.PartVLaws (PaperBlockSpec v2Reference TailInputsCorr paperAtomMap)

/-! ## A2's obligations at fixed block data (generic in the block type) -/

section Fixed

variable {B : Type} [Fintype B] [DecidableEq B] (blockOf : PaperJ0 → B) (hW : Target.Weil)
  (spec : ∀ b, PaperBlockSpec blockOf b) (hC : TailInputsCorr PartV.P4)
  (In : FirstStageInputs blockOf) (Gi : GramInputs blockOf spec)

/-- **A2's block data with `spec`, `hC`, `In`, `Gi` fixed**: the Part V data `CL` (CP4), `ME`
(CP6), `MC` (CP7), `SM` (CP8) at `a_T`, over the first stage and Gram bracket of the given data.
*Open* (Part V). 4 fields. (Stated for a general block type; B1 instantiates it with the paper's
construction, `B1BlockDataTarget`.) -/
structure FixedBlockData where
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

variable {blockOf hW spec hC In Gi}

/-- **To A2's data**: the fixed `spec`, `hC`, `In`, `Gi`, and the four Part V fields. -/
noncomputable def FixedBlockData.toA2 (D : FixedBlockData blockOf hW spec hC In Gi) :
    A2BlockDataTarget blockOf hW where
  spec := spec
  hC := hC
  In := In
  Gi := Gi
  CL := D.CL
  ME := D.ME
  MC := D.MC
  SM := D.SM

variable (blockOf hW spec hC In Gi)

/-- **A2's final obligations with `spec`, `hC`, `In`, `Gi` fixed.** 13 fields: the data `Dv` (4
open fields) and A2's (T1's) other twelve, verbatim over `Dv.toA2`. -/
structure FixedFinalObligations where
  /-- The Part V data over the fixed block specification. -/
  Dv : FixedBlockData blockOf hW spec hC In Gi
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
  /-- `B ≤` the ledger's `B`, for the constructed bracket (`hB_of_charges_B1`). *Open*. -/
  hB : Dv.toA2.toA1.toV2.toCertData.toData.B ≤ targetLedger.B
  /-- `L₀ ≤` the ledger's `L₀`, for the constructed first stage. *Open*. -/
  hL₀ : Dv.toA2.toA1.toV2.toCertData.toData.L₀ ≤ targetLedger.L₀
  /-- `T ≤` the ledger's `T`. *Open*. -/
  hT : Dv.toA2.toA1.toV2.toCertData.toData.ME.T ≤ targetLedger.T
  /-- `S + A ≤` the ledger's `S + A`. *Open*. -/
  hSA : Dv.toA2.toA1.toV2.toCertData.toData.CL.S + Dv.toA2.toA1.toV2.toCertData.toData.CL.A ≤
    targetLedger.S + targetLedger.A
  /-- The mean credit pays the joint-closing allocations. *Open*. -/
  hm : targetLedger.m₁ + 64 * ((targetLedger.deltaAlpha + targetLedger.deltaMatching +
    targetLedger.deltaOdd + targetLedger.deltaEven) + targetLedger.deltaUpper -
    targetLedger.upperError) ≤ Dv.toA2.toA1.toV2.toCertData.toData.MC.m
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

variable {blockOf hW spec hC In Gi}

/-- **To A2's obligations**: `Dv := Dv.toA2`, the other twelve fields copied. -/
noncomputable def FixedFinalObligations.toA2 (O : FixedFinalObligations blockOf hW spec hC In Gi) :
    A2FinalObligationsTarget blockOf hW where
  Dv := O.Dv.toA2
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

end Fixed

/-! ## The paper's construction -/

/-- **B1's block data**: A2's `CL`, `ME`, `MC`, `SM` over the paper's construction
(`paperBlockOf cell`, `paperSpec hW A`, the proved tail, `paperIn cell`, `paperGi hW A`). *Open*
(Part V). 4 fields. -/
abbrev B1BlockDataTarget (cell : ℕ → ℕ) (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (A : PaperAnalyticInputs cell) : Type 1 :=
  FixedBlockData (paperBlockOf cell) hW (paperSpec hW A) (TailCorrCore.tailInputsCorr hW hMR hFour)
    (paperIn cell) (paperGi hW A)

/-- **B1's obligations**: the four Part V block fields and A2's twelve final fields over the paper's
construction. *Open*. 16 obligations. -/
abbrev B1FinalObligationsTarget (cell : ℕ → ℕ) (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (A : PaperAnalyticInputs cell) : Type 1 :=
  FixedFinalObligations (paperBlockOf cell) hW (paperSpec hW A)
    (TailCorrCore.tailInputsCorr hW hMR hFour) (paperIn cell) (paperGi hW A)

variable {cell : ℕ → ℕ}

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵` with the block specification of the paper's
construction** (`thm:main` at `ε = a_T/71`, via `thm:comparison` and `thm:density:induction` at
`a_T`; `def:construction`(b) in the ALLp configuration): from the literature inputs (`Weil`,
`MovingRoot`, `FourCycle`, H2″), the analytic inputs of the block laws
`A : PaperAnalyticInputs cell` (`lem:upper-reference-rp`(ii), `lem:front12:reference`(i),(ii),
*hypotheses*) and the sixteen remaining Part V obligations `B1FinalObligationsTarget`. The block
assignment `paperBlockOf cell`, the specification `paperSpec`, the first-stage constants `paperIn`,
the Gram gates `paperGi` and the tail input are constructed. -/
theorem main_target_paper_block_B1 (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmallRR : Target.ThetaSmallRR) (cell : ℕ → ℕ) (A : PaperAnalyticInputs cell)
    (O : B1FinalObligationsTarget cell hWeil hMovingRoot hFourCycle A) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_block_A2 hWeil hMovingRoot hFourCycle hThetaSmallRR O.toA2

/-- **The main statement with the analytic inputs in the paper's lemma form**
(`main_target_paper_block_B1` with `A := paperAnalyticInputs_of_lemmas …`): from the literature
inputs, `lem:front12:reference`(i),(ii) on the 33 pieces at the ALLp caps (`MiddleUniformLemma`,
`MiddleIndividualLemma`), `lem:upper-reference-rp`(ii) on the 310 bands (`UpperBandLemma`), the
budget of the partition (`PaperBudget cell`) and the sixteen remaining Part V obligations. -/
theorem main_target_paper_block_B1_lemmas (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmallRR : Target.ThetaSmallRR) (cell : ℕ → ℕ) (hbud : PaperBudget cell)
    (hU : ∀ k, UpperBandLemma k)
    (hM : ∀ i, allpIndividual i = none → MiddleUniformLemma i)
    (hI : ∀ i u, allpIndividual i = some u → MiddleIndividualLemma i u)
    (O : B1FinalObligationsTarget cell hWeil hMovingRoot hFourCycle
      (paperAnalyticInputs_of_lemmas hbud hU hM hI)) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_block_B1 hWeil hMovingRoot hFourCycle hThetaSmallRR cell _ O

/-- **The main statement with the middle analytic inputs at the block-cap values**
(`main_target_paper_block_B1_lemmas` with `MiddleUniformLemma`, `MiddleIndividualLemma` from
`MiddleUniformCapLemma`, `MiddleIndividualCapLemma`: the root envelopes and the layer caps `k_L`,
`k_E` at `g exp(B·570/(X_i log X_i))`, the output form of the tensor step `cut_block_cap`). -/
theorem main_target_paper_block_B1_caps (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmallRR : Target.ThetaSmallRR) (cell : ℕ → ℕ) (hbud : PaperBudget cell)
    (hU : ∀ k, UpperBandLemma k)
    (hM : ∀ i, allpIndividual i = none → MiddleUniformCapLemma i)
    (hI : ∀ i u, allpIndividual i = some u → MiddleIndividualCapLemma i u)
    (O : B1FinalObligationsTarget cell hWeil hMovingRoot hFourCycle
      (paperAnalyticInputs_of_lemmas hbud hU (fun i hi => middleUniformLemma_of_cap (hM i hi))
        (fun i u hi => middleIndividualLemma_of_cap (hI i u hi)))) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_block_B1 hWeil hMovingRoot hFourCycle hThetaSmallRR cell _ O

/-- **`hB` from the block bounds of `lem:record:middle-prices`** for the paper's construction: A2's
`hB_of_charges` with its scale hypothesis `r² b_𝔅 = 1` discharged (`paperSpec_scale`). If the sum
of the block bounds `(2 v_D r² + (2 v_D (f₁ + h₁) + 12 w_S/(1 - 3/X)) r³) q_𝔅^{2a}` is at most `U'`,
the first-stage tag sums are at most `d'`, `v'`, and `e^{U'} (1 + 𝔗(d', v')) ≤ B^{ledger}`, then
`hB` holds. -/
theorem hB_of_charges_B1 {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
    {A : PaperAnalyticInputs cell} (D : B1BlockDataTarget cell hW hMR hFour A) {U' : ℝ}
    {d' v' : Fin 2 → ℝ}
    (hU : ∑ b, specUbound (paperIn cell) (paperSpec hW A b)
      (paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay (.inr b)) ≤ U')
    (hd : ∀ j, ∑ β, (paperStage (paperBlockOf cell) hW (paperSpec hW A)
      (TailCorrCore.tailInputsCorr hW hMR hFour) (paperIn cell) β).dTag
      (paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay β) j ≤ d' j)
    (hv : ∀ j, ∑ β, (paperStage (paperBlockOf cell) hW (paperSpec hW A)
      (TailCorrCore.tailInputsCorr hW hMR hFour) (paperIn cell) β).vTag
      (paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay β) j ≤ v' j)
    (hcost : Real.exp U' * (1 + tagSeries d' v') ≤ targetLedger.B) :
    D.toA2.toA1.toV2.toCertData.toData.B ≤ targetLedger.B :=
  hB_of_charges D.toA2 (fun b => paperSpec_scale hW A b) hU hd hv hcost

end Sarkozy.BlockSpecPaper
