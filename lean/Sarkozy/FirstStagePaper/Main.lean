module

public import Sarkozy.FirstStagePaper.Paper
public import Sarkozy.MainTarget.Main

@[expose] public section

/-!
# The main statement at `a_T` with the first stage constructed (`def:cp2`)

T1's `MainTarget.main_target_paper_block` with the obligation `FS` (`def:cp2` at `a_T`) replaced
by the paper's construction `firstStageTarget blockOf hW spec hC In` (`FirstStagePaper.Paper`): the
middle blocks are the first-stage atoms, with V3's frame (`lem:middle-polarization`,
`def:record:frame`) and the two tagged differences of the one-stage repair, whose sharp bounds
`k_new(X) b^{-1/2}` are proved (`lem:record:one-stage-folded-e`(d), (e): `block_delta_form_le`,
`blockSharp_of_block`).

* `A1BlockDataTarget`: T1's `V2BlockDataTarget` (8 fields: `spec`, `hC`, `FS`, `GB`, `CL`, `ME`,
  `MC`, `SM`) with `FS` replaced by `In : FirstStageInputs blockOf`, the per-block constants (the
  piece start and the least prime: data, with `FirstStageInputs.default` valid for every partition);
  `GB`, `CL`, `ME`, `MC`, `SM` are over the constructed first stage. `toV2` maps it to T1's
  structure, with `FS := firstStageTarget …`.
* `A1FinalObligationsTarget`: T1's `V2FinalObligationsTarget` (13 fields) over `A1BlockDataTarget`;
  the other twelve fields are T1's, verbatim (with `Dv.toV2` for `Dv`). `toV2` maps it to T1's.
* **`main_target_paper_block_A1`**: the bound `N^{1 − a_T/71}` from the literature inputs and
  `A1FinalObligationsTarget blockOf hWeil`.
* `hL₀_of_totals`, `hL₀_of_prices`: the obligation `hL₀` from upper bounds of the constructed totals
  (`firstStagePaper_P`, `_dT`, `_vT`: sums over the middle blocks of the per-block prices
  `middleStage_pvar`, `middleStage_dTag`, `middleStage_vTag`, `lem:record:middle-prices`) by
  monotonicity of the cost `L₀ = e^P 𝔗(d, v)` (`tagSeries_mono`).

**Field count.** T1's structure has 20 open leaves. Here `FS` is gone: its replacement `In` is data
(three inequalities, inhabited by `FirstStageInputs.default`), not an open statement. So
`A1FinalObligationsTarget` has **19 open leaves**: `spec`, `hC`, `GB`, `CL`, `ME`, `MC`, `SM` and
T1's twelve (`CB`, `hΨ`, `hCB`, `hB`, `hL₀`, `hT`, `hSA`, `hm`, `E1`, `SF`, `fix`, `env`). `hL₀` now
compares the constructed totals with the ledger.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.FirstStagePaper

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget
open Sarkozy.PartVLaws (PaperBlockSpec v2Reference TailInputsCorr paperAtomMap)

variable {B : Type} [Fintype B] [DecidableEq B] (blockOf : PaperJ0 → B)

/-- **T1's `V2BlockDataTarget` with the first stage constructed** (`def:cp2` by
`firstStageTarget`): `spec`, `hC` (V2's, no exponent), the named first-stage inputs `In`, and the
Part V data `GB`, `CL`, `ME`, `MC`, `SM` at `a_T` over the constructed first stage. 8 fields. -/
structure A1BlockDataTarget (hW : Target.Weil) where
  /-- The paper's block laws with their inputs (`def:construction`(b)). *Open* (V2's `spec`). -/
  spec : ∀ b, PaperBlockSpec blockOf b
  /-- The tail inputs in correlation form (`lem:tail-law`(i)). *Open* (V2's `hC`). -/
  hC : TailInputsCorr PartV.P4
  /-- **The per-block constants of the first stage** (`FirstStageInputs`): the piece start and the
  least prime of each block. Data (`FirstStageInputs.default` is valid). Replaces T1's `FS`. -/
  In : FirstStageInputs blockOf
  /-- (CP3) at `a_T` over the constructed first stage. *Open* (Part V). -/
  GB : TheoremCBlock.GramBracket targetDecay paperM0 (paperAtomMap blockOf) paperTail
    (paperSelAt (paperAtomMap blockOf) targetDecay) (firstStageTarget blockOf hW spec hC In)
  /-- (CP4) at `a_T`. *Open* (Part V). -/
  CL : TheoremCBlock.ComparisonLaw targetDecay paperM0 (paperAtomMap blockOf) paperTail
    (paperSelAt (paperAtomMap blockOf) targetDecay) paperPP paperEP paperQueries
    (firstStageTarget blockOf hW spec hC In)
  /-- (CP6) at `a_T`. *Open* (Part V). -/
  ME : TheoremCBlock.MatchingEnvelopes targetDecay paperM0 (paperAtomMap blockOf) paperTail GB CL
  /-- (CP7) at `a_T`. *Open* (Part V). -/
  MC : TheoremCBlock.MeanCredit targetDecay paperM0 (paperAtomMap blockOf) paperTail ME
  /-- (CP8) at `a_T`. *Open* (Part V). -/
  SM : TheoremCBlock.Summability targetDecay paperM0 (paperAtomMap blockOf) paperTail ME

variable {blockOf}

/-- **To T1's data**: `FS := firstStageTarget blockOf hW spec hC In`, the other seven fields
copied. -/
noncomputable def A1BlockDataTarget.toV2 {hW : Target.Weil} (D : A1BlockDataTarget blockOf hW) :
    V2BlockDataTarget blockOf hW where
  spec := D.spec
  hC := D.hC
  FS := firstStageTarget blockOf hW D.spec D.hC D.In
  GB := D.GB
  CL := D.CL
  ME := D.ME
  MC := D.MC
  SM := D.SM

variable (blockOf)

/-- **T1's `V2FinalObligationsTarget` with the first stage constructed.** 13 fields: the data
`Dv` and T1's other twelve, verbatim over `Dv.toV2`. -/
structure A1FinalObligationsTarget (hW : Target.Weil) where
  /-- The data, with the first stage constructed. -/
  Dv : A1BlockDataTarget blockOf hW
  /-- The (CP5) class bounds at `a_T`. *Open* (Part V). -/
  CB : TheoremCBlock.ClassBounds targetDecay paperM0 (paperAtomMap blockOf) paperTail
    Dv.toV2.toCertData.toData.CL
  /-- The complete polynomial with class bounds is at most the ledger's `E`. *Open*. -/
  hΨ : ∀ L, ∑ ω ∈ univ.filter (fun ω : Choice (Dv.toV2.toCertData.toData.CL.T L) => IsSelection ω),
    (if CB.cls L ω = none then
      Dv.toV2.toCertData.toData.B * monomial (Dv.toV2.toCertData.toData.CL.π L) ω
      else CB.phi L ω) ≤ targetLedger.E
  /-- The class bounds are robust with nonnegative remainders. *Open*. -/
  hCB : CB.RobustNonneg
  /-- `B ≤` the ledger's `B`. *Open*. -/
  hB : Dv.toV2.toCertData.toData.B ≤ targetLedger.B
  /-- `L₀ ≤` the ledger's `L₀`, for the constructed first stage (`hL₀_of_totals`). *Open*. -/
  hL₀ : Dv.toV2.toCertData.toData.L₀ ≤ targetLedger.L₀
  /-- `T ≤` the ledger's `T`. *Open*. -/
  hT : Dv.toV2.toCertData.toData.ME.T ≤ targetLedger.T
  /-- `S + A ≤` the ledger's `S + A`. *Open*. -/
  hSA : Dv.toV2.toCertData.toData.CL.S + Dv.toV2.toCertData.toData.CL.A ≤
    targetLedger.S + targetLedger.A
  /-- The mean credit pays the joint-closing allocations. *Open*. -/
  hm : targetLedger.m₁ + 64 * ((targetLedger.deltaAlpha + targetLedger.deltaMatching +
    targetLedger.deltaOdd + targetLedger.deltaEven) + targetLedger.deltaUpper -
    targetLedger.upperError) ≤ Dv.toV2.toCertData.toData.MC.m
  /-- (E1), per term. *Open* (G1's `E1`). -/
  E1 : EnvelopeInputsBlock.EnvelopeBoundInputs Dv.toV2.toCertData.toData
  /-- The sharp first-stage terms, per term. *Open* (G1's `SF`). -/
  SF : EnvelopeInputsBlock.SharpFirstInputs Dv.toV2.toCertData.toData
  /-- The fixed-interval envelope energies, per term. *Open* (G1's `fix`). -/
  fix : EnvelopeInputsBlock.FixedIntervalInputs
    (BlockAnchor.index_coprime_block Dv.toV2.toCertData.toData) Dv.toV2.toCertData.toData
  /-- The envelope energies, per term. *Open* (G1's `env`). -/
  env : EnvelopeInputsBlock.EnvelopeEnergyInputs
    (BlockAnchor.index_coprime_block Dv.toV2.toCertData.toData) Dv.toV2.toCertData.toData

variable {blockOf}

/-- **To T1's obligations**: `Dv := Dv.toV2`, the other twelve fields copied. -/
noncomputable def A1FinalObligationsTarget.toV2 {hW : Target.Weil}
    (O : A1FinalObligationsTarget blockOf hW) : V2FinalObligationsTarget blockOf hW where
  Dv := O.Dv.toV2
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

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵`, with the first stage of the paper's
construction** (`thm:main` at `ε = a_T/71`, via `thm:comparison` and `thm:density:induction` at
`a_T`): from the literature inputs (`Weil`, `MovingRoot`, `FourCycle`, H2″) and
`A1FinalObligationsTarget blockOf`, in which (CP2) is `firstStageTarget` (`def:cp2`,
`def:record:frame`, `lem:middle-polarization`, `lem:record:one-stage-folded-e`) from the named
inputs `FirstStageInputs`. -/
theorem main_target_paper_block_A1 (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmallRR : Target.ThetaSmallRR) (O : A1FinalObligationsTarget blockOf hWeil) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_block hWeil hMovingRoot hFourCycle hThetaSmallRR O.toV2

/-- **`hL₀` from bounds of the totals** (`def:cp2`, the cost `L₀ = e^P 𝔗(d, v)`; `rem:cp:tags`: the
series is nondecreasing): if the constructed totals are at most `P'`, `d'`, `v'` and
`e^{P'} 𝔗(d', v') ≤ L₀^{ledger}`, then `L₀ ≤ L₀^{ledger}`. -/
theorem hL₀_of_totals {hW : Target.Weil} (D : A1BlockDataTarget blockOf hW) {P' : ℝ}
    {d' v' : (firstStageTarget blockOf hW D.spec D.hC D.In).Tag → ℝ}
    (hd0 : ∀ j, 0 ≤ (firstStageTarget blockOf hW D.spec D.hC D.In).dT j)
    (hv0 : ∀ j, 0 ≤ (firstStageTarget blockOf hW D.spec D.hC D.In).vT j)
    (hP : (firstStageTarget blockOf hW D.spec D.hC D.In).P ≤ P')
    (hd : ∀ j, (firstStageTarget blockOf hW D.spec D.hC D.In).dT j ≤ d' j)
    (hv : ∀ j, (firstStageTarget blockOf hW D.spec D.hC D.In).vT j ≤ v' j)
    (hcost : TheoremC.firstStageCost P' d' v' ≤ targetLedger.L₀) :
    D.toV2.toCertData.toData.L₀ ≤ targetLedger.L₀ := by
  refine le_trans ?_ hcost
  change Real.exp (firstStageTarget blockOf hW D.spec D.hC D.In).P *
      tagSeries (firstStageTarget blockOf hW D.spec D.hC D.In).dT
        (firstStageTarget blockOf hW D.spec D.hC D.In).vT ≤ Real.exp P' * tagSeries d' v'
  exact mul_le_mul (Real.exp_le_exp.mpr hP) (tagSeries_mono hd0 hv0 hd hv)
    (tagSeries_nonneg hd0 hv0) (Real.exp_pos _).le

/-- **`hL₀` from bounds of the per-block prices** (`def:cp2`, `lem:record:middle-prices`): the
constructed totals are the sums over the prefix atoms of the per-atom prices (`middleStage_pvar`,
`middleStage_dTag`, `middleStage_vTag` on the middle blocks, zero elsewhere); if these sums are at
most `P'`, `d'_j`, `v'_j` and `e^{P'} 𝔗(d', v') ≤ L₀^{ledger}`, then `hL₀` holds. -/
theorem hL₀_of_prices {hW : Target.Weil} (D : A1BlockDataTarget blockOf hW) {P' : ℝ}
    {d' v' : Fin 2 → ℝ}
    (hP : ∑ β, (paperStage blockOf hW D.spec D.hC D.In β).pvar
      (paperSelAt (paperAtomMap blockOf) targetDecay β) ≤ P')
    (hd : ∀ j, ∑ β, (paperStage blockOf hW D.spec D.hC D.In β).dTag
      (paperSelAt (paperAtomMap blockOf) targetDecay β) j ≤ d' j)
    (hv : ∀ j, ∑ β, (paperStage blockOf hW D.spec D.hC D.In β).vTag
      (paperSelAt (paperAtomMap blockOf) targetDecay β) j ≤ v' j)
    (hcost : TheoremC.firstStageCost P' d' v' ≤ targetLedger.L₀) :
    D.toV2.toCertData.toData.L₀ ≤ targetLedger.L₀ := by
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
  change TheoremC.firstStageCost (firstStageTarget blockOf hW D.spec D.hC D.In).P
      (firstStageTarget blockOf hW D.spec D.hC D.In).dT
      (firstStageTarget blockOf hW D.spec D.hC D.In).vT ≤ _
  rw [firstStageTarget_eq]
  exact mul_le_mul (Real.exp_le_exp.mpr hP) (tagSeries_mono hd0 hv0 hd hv)
    (tagSeries_nonneg hd0 hv0) (Real.exp_pos _).le

end Sarkozy.FirstStagePaper
