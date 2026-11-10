module

public import Sarkozy.PaperNumbers.Charge
public import Sarkozy.BlockSpecPaper.Joint

@[expose] public section

/-!
# The main statement at the paper's partition (`def:construction`(b), `cor:joint-closing`)

B1's joint main statement `BlockSpecPaper.main_target_paper_joint_B1` takes the within-site rule
`cell` as data and the analytic block inputs `A : PaperAnalyticInputs cell`. Here:
* `cell := paperCell` (`Cell.lean`): the paper's rule, from the recorded bins and threshold points
  (`def:record:exact-blocks`(b)–(d)) and the default band cells (`def:record:upper-bands`(b));
* `A := paperAnalyticInputs_of_lemmas paperCell_budget hU hM hI` (B1's `Lemmas.lean`): the analytic
  inputs from B1's lemma forms, which do not depend on `cell`; the combinatorial hypothesis
  `PaperBudget cell` of that bridge is now **proved** (`paperCell_budget`).

**`main_target_paper_joint_N1`**: the bound `N^{1 − a_T/71}` from `Weil`,
`MovingRoot`, `FourCycle`, H2″, the three lemma families `hU` (`lem:upper-reference-rp`(ii), 310
bands), `hM` (`lem:front12:reference`(i),(ii), 31 pieces), `hI` (the same with the
individual-square root, 2 pieces), and the 11 fields of `N1JointFinalObligations` (B1's joint
obligations at the paper's partition: `CL`, `ME`, `SM`; `hB`, `hL₀`, `hT`, `hSA`, `JB`, `SF`,
`fix`, `env`). No data parameter and no combinatorial hypothesis remains.

**`main_target_paper_joint_N1_charges`**: the same with `hB` replaced by its inputs (B1's
`hB_of_blockCharges_joint`): the per-piece charge bounds `b₂(i) ≤ c₂(i)`, `b₃(i) ≤ c₃(i)`
(`lem:record:block-charge`) for the paper's blocks, the first-stage tag sums, and the cost
inequality.

**`main_target_paper_joint_N1_bmor`**: the same with the charge bounds derived from M2's
`piece_charge_le_bmor` at the paper's partition (`Charge.lean`, `thm:bmor`): `hB`'s remaining
inputs are numerical bounds on M2's explicit `pieceBound`, the tag sums and the cost inequality.

**`main_target_paper_joint_N1_with`**: the variant for any recorded band cells `Uc` with
`BandRulesValid Uc` (`rem:upper-band-choices`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.PaperNumbers

open Sarkozy.TheoremC Sarkozy.RecordExpansion
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (paperAtomMap)

/-- **The analytic block inputs at the paper's partition**, from B1's lemma forms (the budget
`PaperBudget paperCell` proved). -/
noncomputable abbrev paperA (hU : ∀ k, UpperBandLemma k)
    (hM : ∀ i, allpIndividual i = none → MiddleUniformLemma i)
    (hI : ∀ i u, allpIndividual i = some u → MiddleIndividualLemma i u) :
    PaperAnalyticInputs paperCell :=
  paperAnalyticInputs_of_lemmas paperCell_budget hU hM hI

/-- **The joint block data at the paper's partition**: `CL` (CP4), `ME` (CP6), `SM` (CP8)(c). -/
abbrev N1JointBlockData (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (hU : ∀ k, UpperBandLemma k) (hM : ∀ i, allpIndividual i = none → MiddleUniformLemma i)
    (hI : ∀ i u, allpIndividual i = some u → MiddleIndividualLemma i u) : Type 1 :=
  B1JointBlockData paperCell hW hMR hFour (paperA hU hM hI)

/-- **The joint obligations at the paper's partition** (11 fields). -/
abbrev N1JointFinalObligations (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hU : ∀ k, UpperBandLemma k)
    (hM : ∀ i, allpIndividual i = none → MiddleUniformLemma i)
    (hI : ∀ i u, allpIndividual i = some u → MiddleIndividualLemma i u) : Type 1 :=
  B1JointFinalObligations paperCell hW hMR hFour (paperA hU hM hI)

/-- **The main statement at `ε = a_T/71` at the paper's partition** (`thm:main` at
`ε = 3/250000`, `cor:joint-closing`, `def:construction`(b), `def:record:exact-blocks`,
`def:record:upper-bands`(b)): B1's `main_target_paper_joint_B1` at `cell := paperCell`, with the
analytic inputs from the lemma forms `hU`, `hM`, `hI` (`lem:upper-reference-rp`(ii),
`lem:front12:reference`(i),(ii); *hypotheses*, spectral) and `PaperBudget paperCell` proved
(`lem:record:local-domain`(ii)). Remaining: the 11 fields of `N1JointFinalObligations`. -/
theorem main_target_paper_joint_N1 (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmallRR : Target.ThetaSmallRR) (hU : ∀ k, UpperBandLemma k)
    (hM : ∀ i, allpIndividual i = none → MiddleUniformLemma i)
    (hI : ∀ i u, allpIndividual i = some u → MiddleIndividualLemma i u)
    (O : N1JointFinalObligations hWeil hMovingRoot hFourCycle hU hM hI) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_joint_B1 hWeil hMovingRoot hFourCycle hThetaSmallRR paperCell
    (paperA hU hM hI) O

/-- **The main statement at the paper's partition with any recorded band cells** `Uc` satisfying
`def:record:upper-bands`(b) (`BandRulesValid Uc`, `rem:upper-band-choices`). -/
theorem main_target_paper_joint_N1_with (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    {Uc : Fin 310 → CellRule} (hUc : BandRulesValid Uc) (hU : ∀ k, UpperBandLemma k)
    (hM : ∀ i, allpIndividual i = none → MiddleUniformLemma i)
    (hI : ∀ i u, allpIndividual i = some u → MiddleIndividualLemma i u)
    (O : B1JointFinalObligations (paperCellWith Uc) hWeil hMovingRoot hFourCycle
      (paperAnalyticInputs_of_lemmas (paperCellWith_budget hUc) hU hM hI)) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_joint_B1 hWeil hMovingRoot hFourCycle hThetaSmallRR
    (paperCellWith Uc) _ O

/-- **The main statement at the paper's partition with `hB` from the block charges**
(`main_target_paper_joint_N1` with B1's `hB_of_blockCharges_joint`): the per-piece charge bounds
`b₂(i) ≤ c₂(i)`, `b₃(i) ≤ c₃(i)` of the paper's blocks (`lem:record:block-charge`;
*hypotheses*), the first-stage tag sums `≤ d'`, `v'` (*hypotheses*) and the cost inequality
`e^{∑ (U₂ c₂ + U₃ c₃)} (1 + 𝔗(d', v')) ≤ B^{ledger}` (*hypothesis*), with the other ten fields. -/
theorem main_target_paper_joint_N1_charges (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (hU : ∀ k, UpperBandLemma k) (hM : ∀ i, allpIndividual i = none → MiddleUniformLemma i)
    (hI : ∀ i u, allpIndividual i = some u → MiddleIndividualLemma i u)
    (Dv : N1JointBlockData hWeil hMovingRoot hFourCycle hU hM hI)
    {c₂ c₃ : Fin 33 → ℝ} {d' v' : Fin 2 → ℝ}
    (h₂ : ∀ i, blockCharge
      (fun b => paperSelAt (paperAtomMap (paperBlockOf paperCell)) targetDecay (.inr b)) 2 i ≤ c₂ i)
    (h₃ : ∀ i, blockCharge
      (fun b => paperSelAt (paperAtomMap (paperBlockOf paperCell)) targetDecay (.inr b)) 3 i ≤ c₃ i)
    (hd : ∀ j, ∑ β, (paperStage (paperBlockOf paperCell) hWeil (paperSpec hWeil (paperA hU hM hI))
      (TailCorrCore.tailInputsCorr hWeil hMovingRoot hFourCycle) (paperIn paperCell) β).dTag
      (paperSelAt (paperAtomMap (paperBlockOf paperCell)) targetDecay β) j ≤ d' j)
    (hv : ∀ j, ∑ β, (paperStage (paperBlockOf paperCell) hWeil (paperSpec hWeil (paperA hU hM hI))
      (TailCorrCore.tailInputsCorr hWeil hMovingRoot hFourCycle) (paperIn paperCell) β).vTag
      (paperSelAt (paperAtomMap (paperBlockOf paperCell)) targetDecay β) j ≤ v' j)
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
  main_target_paper_joint_B1_charges hWeil hMovingRoot hFourCycle hThetaSmallRR
    paperCell (paperA hU hM hI) Dv h₂ h₃ hd hv hcost hL₀ hT hSA JB SF fix env

/-- **The main statement at the paper's partition with `hB` from M2's piece bounds**
(`main_target_paper_joint_N1_charges` with the charge bounds `b_d(i) ≤ c_d(i)` derived from
`blockCharge_le_pieceBound`, `lem:record:block-charge` at the paper's partition with `thm:bmor`):
the remaining inputs of `hB` are the numerical bounds `pieceBound a_T d i ≤ c_d(i)`, `d = 2, 3`, on
M2's explicit bound (the price buckets of the greedy blocks below `X_Ch`,
`cert:record:middle-price`,
and the cell integrals above `X_Ch`; *hypotheses*, numerical), the first-stage tag sums
(*hypotheses*) and the cost inequality (*hypothesis*). -/
theorem main_target_paper_joint_N1_bmor (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (hU : ∀ k, UpperBandLemma k) (hM : ∀ i, allpIndividual i = none → MiddleUniformLemma i)
    (hI : ∀ i u, allpIndividual i = some u → MiddleIndividualLemma i u)
    (Dv : N1JointBlockData hWeil hMovingRoot hFourCycle hU hM hI)
    {c₂ c₃ : Fin 33 → ℝ} {d' v' : Fin 2 → ℝ}
    (h₂ : ∀ i, pieceBound targetDecay 2 i ≤ c₂ i) (h₃ : ∀ i, pieceBound targetDecay 3 i ≤ c₃ i)
    (hd : ∀ j, ∑ β, (paperStage (paperBlockOf paperCell) hWeil (paperSpec hWeil (paperA hU hM hI))
      (TailCorrCore.tailInputsCorr hWeil hMovingRoot hFourCycle) (paperIn paperCell) β).dTag
      (paperSelAt (paperAtomMap (paperBlockOf paperCell)) targetDecay β) j ≤ d' j)
    (hv : ∀ j, ∑ β, (paperStage (paperBlockOf paperCell) hWeil (paperSpec hWeil (paperA hU hM hI))
      (TailCorrCore.tailInputsCorr hWeil hMovingRoot hFourCycle) (paperIn paperCell) β).vTag
      (paperSelAt (paperAtomMap (paperBlockOf paperCell)) targetDecay β) j ≤ v' j)
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
  main_target_paper_joint_N1_charges hWeil hMovingRoot hFourCycle hThetaSmallRR
    hU hM hI Dv
    (fun i => (blockCharge_le_pieceBound hBMOR i TargetLedger.targetDecay_nonneg
      (Or.inl rfl)).trans (h₂ i))
    (fun i => (blockCharge_le_pieceBound hBMOR i TargetLedger.targetDecay_nonneg
      (Or.inr (Or.inl rfl))).trans (h₃ i))
    hd hv hcost hL₀ hT hSA JB SF fix env

/-- **`hL₀` of the joint obligations from the first-stage prices** (A1's `hL₀_of_prices` at
`Dv.toJoint.toA2.toA1`, `def:closing-quantities`(2), `def:cp2`): `L₀ = e^{P} 𝔗(d, v)` with the
price sum `∑_β P_β ≤ P'`, the tag sums `≤ d'`, `v'`, and `e^{P'} 𝔗(d', v') ≤ L₀^{ledger}`. -/
theorem hL₀_of_prices_N1 {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
    {hU : ∀ k, UpperBandLemma k} {hM : ∀ i, allpIndividual i = none → MiddleUniformLemma i}
    {hI : ∀ i u, allpIndividual i = some u → MiddleIndividualLemma i u}
    (Dv : N1JointBlockData hW hMR hFour hU hM hI) {P' : ℝ} {d' v' : Fin 2 → ℝ}
    (hP : ∑ β, (paperStage (paperBlockOf paperCell) hW (paperSpec hW (paperA hU hM hI))
      (TailCorrCore.tailInputsCorr hW hMR hFour) (paperIn paperCell) β).pvar
      (paperSelAt (paperAtomMap (paperBlockOf paperCell)) targetDecay β) ≤ P')
    (hd : ∀ j, ∑ β, (paperStage (paperBlockOf paperCell) hW (paperSpec hW (paperA hU hM hI))
      (TailCorrCore.tailInputsCorr hW hMR hFour) (paperIn paperCell) β).dTag
      (paperSelAt (paperAtomMap (paperBlockOf paperCell)) targetDecay β) j ≤ d' j)
    (hv : ∀ j, ∑ β, (paperStage (paperBlockOf paperCell) hW (paperSpec hW (paperA hU hM hI))
      (TailCorrCore.tailInputsCorr hW hMR hFour) (paperIn paperCell) β).vTag
      (paperSelAt (paperAtomMap (paperBlockOf paperCell)) targetDecay β) j ≤ v' j)
    (hcost : TheoremC.firstStageCost P' d' v' ≤ targetLedger.L₀) :
    Dv.toJoint.data.L₀ ≤ targetLedger.L₀ :=
  hL₀_of_prices Dv.toJoint.toA2.toA1 hP hd hv hcost

/-- **The main statement at the paper's partition with `hB` and `hL₀` from their inputs**
(`main_target_paper_joint_N1_bmor` with `hL₀` from `hL₀_of_prices_N1`): besides the hypotheses
H1, H2 (`thm:bmor`), H4, H5, `thm:dl:K`, H2″ and the lemma families `hU`, `hM`, `hI`, it takes
* the numerical charge bounds `pieceBound a_T d i ≤ c_d(i)`, `d = 2, 3` (`h₂`, `h₃`);
* the first-stage sums: prices `≤ P'` (`hP`), tags `≤ d'`, `v'` (`hd`, `hv`);
* the two cost inequalities `e^{∑ (U₂ c₂ + U₃ c₃)} (1 + 𝔗(d', v')) ≤ B^{ledger}` (`hcostB`) and
  `e^{P'} 𝔗(d', v') ≤ L₀^{ledger}` (`hcostL`);
* the 9 remaining fields: `Dv` (`CL`, `ME`, `SM`), `hT`, `hSA`, `JB`, `SF`, `fix`, `env`. -/
theorem main_target_paper_joint_N1_prices (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (hU : ∀ k, UpperBandLemma k) (hM : ∀ i, allpIndividual i = none → MiddleUniformLemma i)
    (hI : ∀ i u, allpIndividual i = some u → MiddleIndividualLemma i u)
    (Dv : N1JointBlockData hWeil hMovingRoot hFourCycle hU hM hI)
    {c₂ c₃ : Fin 33 → ℝ} {P' : ℝ} {d' v' : Fin 2 → ℝ}
    (h₂ : ∀ i, pieceBound targetDecay 2 i ≤ c₂ i) (h₃ : ∀ i, pieceBound targetDecay 3 i ≤ c₃ i)
    (hP : ∑ β, (paperStage (paperBlockOf paperCell) hWeil (paperSpec hWeil (paperA hU hM hI))
      (TailCorrCore.tailInputsCorr hWeil hMovingRoot hFourCycle) (paperIn paperCell) β).pvar
      (paperSelAt (paperAtomMap (paperBlockOf paperCell)) targetDecay β) ≤ P')
    (hd : ∀ j, ∑ β, (paperStage (paperBlockOf paperCell) hWeil (paperSpec hWeil (paperA hU hM hI))
      (TailCorrCore.tailInputsCorr hWeil hMovingRoot hFourCycle) (paperIn paperCell) β).dTag
      (paperSelAt (paperAtomMap (paperBlockOf paperCell)) targetDecay β) j ≤ d' j)
    (hv : ∀ j, ∑ β, (paperStage (paperBlockOf paperCell) hWeil (paperSpec hWeil (paperA hU hM hI))
      (TailCorrCore.tailInputsCorr hWeil hMovingRoot hFourCycle) (paperIn paperCell) β).vTag
      (paperSelAt (paperAtomMap (paperBlockOf paperCell)) targetDecay β) j ≤ v' j)
    (hcostB : Real.exp (∑ i : Fin 33, (chargeU2 i * c₂ i + chargeU3 i * c₃ i)) *
      (1 + tagSeries d' v') ≤ targetLedger.B)
    (hcostL : TheoremC.firstStageCost P' d' v' ≤ targetLedger.L₀)
    (hT : Dv.toJoint.data.ME.T ≤ targetLedger.T)
    (hSA : Dv.toJoint.data.CL.S + Dv.toJoint.data.CL.A ≤ targetLedger.S + targetLedger.A)
    (JB : JointBound Dv.toJoint.data targetLedger.jointConstant)
    (SF : EnvelopeInputsBlock.SharpFirstInputs Dv.toJoint.data)
    (fix : EnvelopeInputsBlock.FixedIntervalInputs
      (BlockAnchor.index_coprime_block Dv.toJoint.data) Dv.toJoint.data)
    (env : EnvelopeInputsBlock.EnvelopeEnergyInputs
      (BlockAnchor.index_coprime_block Dv.toJoint.data) Dv.toJoint.data) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_joint_N1_bmor hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR
    hU hM hI Dv h₂ h₃ hd hv hcostB (hL₀_of_prices_N1 Dv hP hd hv hcostL) hT hSA JB SF fix env

end Sarkozy.PaperNumbers
