module

public import Sarkozy.MainFinal.Structure

@[expose] public section

/-!
# The combined main statement (K1)

`thm:main` at `ε = a_T/71`, i.e. `s(N) ≤ C N^{1 − a_T/71}`, joint form (`cor:joint-closing`,
`eq:final-joint-closing`), on the paper's construction in the ALLp configuration.

**`main_target_paper_final`** concludes `Target.SarkozyBound TargetLedger.targetSaving` from the
literature
hypotheses H1 (`Weil`), H2 (`BMOR`), H5 (`MovingRoot`), `thm:dl:K`
(`FourCycle`), H2″ (`ThetaSmallRR`), and one structure `MainFinalObligations`
(`Structure.lean`). `AhlgrenOno` (H3) is not used on this route.

What is proved here, from the reductions of B1–B7 and N1:
* `hB` (`hB_final`): B1's `hB_of_blockCharges_joint` with N1's charge bounds (`thm:bmor`, H2) and
  first-stage sums, and N1's cost inequality `costB_le`;
* `hL₀` (`hL₀_final`): A1's `hL₀_of_prices` with N1's sums and `costL_le`;
* `hT` (`hT_final`): `ME.T = T^{ledger}` for B3's prefix construction (the content is in `hK`,
  `hrepl`);
* `hSA` (`hSA_final`): from `SAExplicit` (B2's `comparisonLawTarget_SA`);
* `JB`: B4's `MeanAllocation.jointBound` with `hB_final`;
* `SF`: B5's `SharpFirstCoupledInputs.ofBlocks` with the proved per-block moments
  (`paperStageMoments_proved`); `fix`, `env`: `fixC.toG1`, `envC.toG1`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MainFinal

open Sarkozy.TheoremC Sarkozy.RecordExpansion
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (paperAtomMap)
open Sarkozy.PaperNumbers (paperCell pieceBound chargeC2 chargeC3 chargeD chargeV fsP2 fsP3 fsD3
  fsV2 sum_lin_le)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-- **The degree-2 block charges at the recorded numbers** (`lem:record:block-charge` at the
paper's partition with `thm:bmor`, N1's `blockCharge_le_pieceBound`, and N1's `h₂`). -/
theorem NumericalCertificates.hb₂ (hBMOR : Target.BMOR) (NC : NumericalCertificates) (i : Fin 33) :
    blockCharge (fun b => paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) 2 i ≤
      (chargeC2 i : ℝ) :=
  (PaperNumbers.blockCharge_le_pieceBound hBMOR i targetDecay_nonneg (Or.inl rfl)).trans (NC.h₂ i)

/-- **The degree-3 block charges at the recorded numbers.** -/
theorem NumericalCertificates.hb₃ (hBMOR : Target.BMOR) (NC : NumericalCertificates) (i : Fin 33) :
    blockCharge (fun b => paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) 3 i ≤
      (chargeC3 i : ℝ) :=
  (PaperNumbers.blockCharge_le_pieceBound hBMOR i targetDecay_nonneg
    (Or.inr (Or.inl rfl))).trans (NC.h₃ i)

namespace FinalBlockData

/-- **`hB` of the combined data** (`def:closing-quantities`(3), `lem:record:middle-prices`,
`lem:record:block-charge`, `cor:two-cut-series`): `B ≤ B^{ledger}` from the 66 numerical
certificates, H2 and N1's proved cost inequality `costB_le`. -/
theorem hB_final (hBMOR : Target.BMOR) (D : FinalBlockData hW hMR hFour)
    (NC : NumericalCertificates) : D.data.B ≤ targetLedger.B :=
  hB_of_blockCharges_joint D.toFixed (c₂ := fun i => (chargeC2 i : ℝ))
    (c₃ := fun i => (chargeC3 i : ℝ)) (d' := chargeD) (v' := chargeV)
    (NC.hb₂ hBMOR) (NC.hb₃ hBMOR)
    (fun j => (PaperNumbers.sum_dTag_le hW hMR hFour D.AI j).trans
      (sum_lin_le (fun _ => le_refl 0) PaperNumbers.fsD3_nonneg (NC.hb₂ hBMOR) (NC.hb₃ hBMOR)))
    (fun j => (PaperNumbers.sum_vTag_le hW hMR hFour D.AI j).trans
      (sum_lin_le PaperNumbers.fsV2_nonneg (fun _ => le_refl 0) (NC.hb₂ hBMOR) (NC.hb₃ hBMOR)))
    PaperNumbers.costB_le

/-- **`hL₀` of the combined data** (`def:closing-quantities`(2), `def:cp2`,
`lem:record:middle-prices`): `L₀ ≤ L₀^{ledger}` from the 66 numerical certificates, H2 and N1's
proved cost inequality `costL_le`. -/
theorem hL₀_final (hBMOR : Target.BMOR) (D : FinalBlockData hW hMR hFour)
    (NC : NumericalCertificates) : D.data.L₀ ≤ targetLedger.L₀ :=
  hL₀_of_prices D.toFixed.toJoint.toA2.toA1 (d' := chargeD) (v' := chargeV)
    ((PaperNumbers.sum_pvar_le hW hMR hFour D.AI).trans
      (sum_lin_le PaperNumbers.fsP2_nonneg PaperNumbers.fsP3_nonneg (NC.hb₂ hBMOR)
        (NC.hb₃ hBMOR)))
    (fun j => (PaperNumbers.sum_dTag_le hW hMR hFour D.AI j).trans
      (sum_lin_le (fun _ => le_refl 0) PaperNumbers.fsD3_nonneg (NC.hb₂ hBMOR) (NC.hb₃ hBMOR)))
    (fun j => (PaperNumbers.sum_vTag_le hW hMR hFour D.AI j).trans
      (sum_lin_le PaperNumbers.fsV2_nonneg (fun _ => le_refl 0) (NC.hb₂ hBMOR) (NC.hb₃ hBMOR)))
    PaperNumbers.costL_le

/-- **`hT` of the combined data** (`def:cp6`, `prop:record:matching`(ii)): B3's construction has
`T = T^{ledger}`; the content is in `Env.hK` and `Env.hrepl`. -/
theorem hT_final (D : FinalBlockData hW hMR hFour) : D.data.ME.T ≤ targetLedger.T :=
  le_refl _

/-- **`hSA` of the combined data from its explicit form** (`def:cp4`(b), `def:closing-quantities`;
B2's `comparisonLawTarget_SA`). -/
theorem hSA_final (D : FinalBlockData hW hMR hFour) (h : ComparisonLawPaper.SAExplicit D.Cmp.Ci) :
    D.data.CL.S + D.data.CL.A ≤ targetLedger.S + targetLedger.A :=
  (ComparisonLawPaper.comparisonLawTarget_SA hW _ _ _ D.Cmp.Ci).trans_le h

end FinalBlockData

/-- **To B1's joint obligations at the paper's partition**: `Dv := Dv.toFixed`; `hB`, `hL₀`,
`hT`, `hSA` as above; `JB := Cls.MA.jointBound …` (B4); `SF` from `lem:density:coupled` with the
proved per-block moments, `fix := fixC.toG1`, `env := envC.toG1` (B5). -/
noncomputable def MainFinalObligations.toB1 (hBMOR : Target.BMOR)
    (O : MainFinalObligations hW hMR hFour) :
    B1JointFinalObligations paperCell hW hMR hFour O.Dv.AI where
  Dv := O.Dv.toFixed
  hB := O.Dv.hB_final hBMOR O.NC
  hL₀ := O.Dv.hL₀_final hBMOR O.NC
  hT := O.Dv.hT_final
  hSA := O.Dv.hSA_final O.hSA
  JB := O.Cls.MA.jointBound MainAnchor.card_chamber O.Cls.PD O.Cls.E1 (O.Dv.hB_final hBMOR O.NC)
  SF := (EnvelopeEnergiesPaper.SharpFirstCoupledInputs.ofBlocks O.Dv.toJoint O.Sh.θ O.Sh.hθ
    (EnvelopeEnergiesPaper.paperStageMoments_proved hW O.Dv.toJoint.In O.Sh.hθ O.Sh.hθ'
      O.Dv.toJoint.spec)
    O.Sh.ε O.Sh.hε0 O.Sh.hεt O.Sh.c₁ O.Sh.hc₁ O.Sh.fibre).toSharpFirstInputs
  fix := O.Sh.fixC.toG1
  env := O.Sh.envC.toG1

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵`, with every reduction plugged in**
(`thm:main` at `ε = a_T/71`, via `thm:comparison` with `cor:joint-closing`,
`eq:final-joint-closing` and `thm:density:induction` at `a_T`; `def:construction`(b) in the ALLp
configuration).

Hypotheses: H1 `Weil`, H2 `BMOR` (`thm:bmor`, for the block charges), H5
`MovingRoot` and `thm:dl:K` `FourCycle` (for the tail input), H2″ `ThetaSmallRR`
(`cert:index-moment`), and `O : MainFinalObligations` — B6's per-prime certificates and
block-level analytic inputs, N1's 66 numerical charge bounds, B2/B7's (CP4) inputs, B3's prefix
refinement, B2's explicit `hSA`, B4's five inputs of `JB`, and B5's fibre input and
cyclic-coordinate bundles. H4 `TwoVariable` was removed on 9 November 2026 as unused. -/
theorem main_target_paper_final (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations hWeil hMovingRoot hFourCycle) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_joint_B1 hWeil hMovingRoot hFourCycle hThetaSmallRR paperCell
    O.Dv.AI (O.toB1 hBMOR)

end Sarkozy.MainFinal
