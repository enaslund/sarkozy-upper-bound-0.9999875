module

public import Sarkozy.MainFinalF1b.ClassesE4B
public import Sarkozy.MainFinalF1b.Uniform
public import Sarkozy.TargetGoal.Main

@[expose] public section






open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MainFinalF1b

open Sarkozy.TheoremC Sarkozy.RecordExpansion
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.MainFinal2 (SharpParts2)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.MainFinalF1 (FinalBlockData FinalBlockData3b SAParts3 midOthers analyticInputs)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-! ## K1's layer -/

/-- **K1's obligations at `f1Cell` with the combined gate and the aggregate (E1)**: F1P's
`MainFinalObligationsJ` with `Cls : ClassParts2JA`. 4 fields. -/
structure MainFinalObligationsJA (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) where
  /-- The block data (K1, at `f1Cell`). -/
  Dv : FinalBlockData hW hMR hFour
  /-- `hSA` in explicit per-atom form (B2). -/
  hSA : ComparisonLawPaper.SAExplicit Dv.Cmp.Ci
  /-- The class inputs with the combined gate and the aggregate (E1). -/
  Cls : ClassParts2JA Dv.data
  /-- The inputs of `SF`, `fix`, `env` (B5, B9). -/
  Sh : SharpParts2 Dv.toJoint

/-- **To B1's joint obligations at `f1Cell`**: as F1P's `toB1`, with `JB := Cls.jointBound`. -/
noncomputable def MainFinalObligationsJA.toB1 (hBMOR : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (O : MainFinalObligationsJA hW hMR hFour) :
    B1JointFinalObligations f1Cell hW hMR hFour O.Dv.AI where
  Dv := O.Dv.toFixed
  hB := O.Dv.hB_final hBMOR hRR
  hL₀ := O.Dv.hL₀_final hBMOR hRR
  hT := O.Dv.hT_final
  hSA := O.Dv.hSA_final O.hSA
  JB := O.Cls.jointBound
  SF := O.Sh.SF
  fix := O.Sh.fix
  env := O.Sh.env

/-- **K1's main statement at `f1Cell` with the aggregate (E1)** (`thm:main` at `ε = a_T/71`). -/
theorem main_target_f1_finalJA (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligationsJA hWeil hMovingRoot hFourCycle) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_joint_B1 hWeil hMovingRoot hFourCycle hThetaSmallRR f1Cell
    O.Dv.AI (O.toB1 hBMOR hThetaSmallRR)

/-! ## The combined layer, P1 only -/

/-- **The combined obligations at `f1Cell` with the aggregate (E1)** (P1 only): F1P's
`MainFinalObligations3c` with `Cls : ClassPartsE4A`. 5 fields. -/
structure MainFinalObligations3dA (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) where
  /-- The block data (`EnvPrefix`, at `f1Cell`). -/
  Dv : FinalBlockData3b hW hMR hFour
  /-- `hSA` in reduced form (`MainFinal3`; final inequality at N2's numbers). -/
  SA : SAParts3 hW hMR hFour (analyticInputs (Dv.PC.toPC hW hMR hFour) Dv.BA) Dv.Cmp
  /-- The middle part of `hothT` (`EnvPrefix`). *Open*. -/
  hmid : ∀ L, midOthers Dv.Cmp.toK2 Dv.MR L +
    max (∑ β, Dv.MR.toPrefix.KL β) (∑ β, Dv.MR.toPrefix.KR β) +
    (12 / 2 ^ 534 + Sarkozy.EnvPrefix.Uup SA.Cs SA.Ca SA.hCs SA.hCa + 11 / 10 ^ 70) ≤
      targetLedger.T
  /-- The class inputs: E4's constructors, the combined gate, the aggregate (E1). -/
  Cls : ClassPartsE4A (Dv.toMF3 hB SA hmid).toK2.toK1.data
  /-- The inputs of `SF`, `fix`, `env` (B5, B9). -/
  Sh : SharpParts2 (Dv.toMF3 hB SA hmid).toK2.toK1.toJoint

/-- K1's layer (F1P's maps for the block data and `hSA`; `ClassPartsE4A.toJA`). -/
noncomputable def MainFinalObligations3dA.toJA {hB : Target.BMOR} (hRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3dA hW hMR hFour hB) : MainFinalObligationsJA hW hMR hFour where
  Dv := (O.Dv.toMF3 hB O.SA O.hmid).toK2.toK1
  hSA := (O.SA.toK2 hB).toSAExplicit hB hRR
  Cls := O.Cls.toJA
  Sh := O.Sh

/-- The main statement with P1 only (`thm:main` at `ε = a_T/71`). -/
theorem main_target_f1_final3dA (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3dA hWeil hMovingRoot hFourCycle hBMOR) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_f1_finalJA hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR
    (O.toJA hThetaSmallRR)

/-! ## K1's layer, P1 and P2 -/

/-- **K1's obligations at `f1Cell` with both corrections**: `Cls : ClassPartsE4B`. 4 fields. -/
structure MainFinalObligationsJB (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) where
  /-- The block data (K1, at `f1Cell`). -/
  Dv : FinalBlockData hW hMR hFour
  /-- `hSA` in explicit per-atom form (B2). -/
  hSA : ComparisonLawPaper.SAExplicit Dv.Cmp.Ci
  /-- The class inputs without `H`, `hyπ`, with the aggregate (E1). -/
  Cls : ClassPartsE4B Dv.data
  /-- The inputs of `SF`, `fix`, `env` (B5, B9). -/
  Sh : SharpParts2 Dv.toJoint

/-- **To B1's joint obligations at `f1Cell`**: `JB := Cls.jointBound` (`ClassPartsE4B`). -/
noncomputable def MainFinalObligationsJB.toB1 (hBMOR : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (O : MainFinalObligationsJB hW hMR hFour) :
    B1JointFinalObligations f1Cell hW hMR hFour O.Dv.AI where
  Dv := O.Dv.toFixed
  hB := O.Dv.hB_final hBMOR hRR
  hL₀ := O.Dv.hL₀_final hBMOR hRR
  hT := O.Dv.hT_final
  hSA := O.Dv.hSA_final O.hSA
  JB := O.Cls.jointBound
  SF := O.Sh.SF
  fix := O.Sh.fix
  env := O.Sh.env

/-- **K1's main statement at `f1Cell` with both corrections** (`thm:main` at `ε = a_T/71`). -/
theorem main_target_f1_finalJB (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligationsJB hWeil hMovingRoot hFourCycle) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_joint_B1 hWeil hMovingRoot hFourCycle hThetaSmallRR f1Cell
    O.Dv.AI (O.toB1 hBMOR hThetaSmallRR)

/-! ## The combined layer, P1 and P2 -/

/-- **The combined obligations at `f1Cell` with FA2's two corrections**: F1P's
`MainFinalObligations3c` with `Cls : ClassPartsE4B` (the aggregate (E1); no `ES.H`, `ES.Kπ`,
`ES.hK`, `ES.hyπ`). 5 fields. -/
structure MainFinalObligations3d (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) where
  /-- The block data (`EnvPrefix`, at `f1Cell`). -/
  Dv : FinalBlockData3b hW hMR hFour
  /-- `hSA` in reduced form (`MainFinal3`; final inequality at N2's numbers). -/
  SA : SAParts3 hW hMR hFour (analyticInputs (Dv.PC.toPC hW hMR hFour) Dv.BA) Dv.Cmp
  /-- The middle part of `hothT` (`EnvPrefix`). *Open*. -/
  hmid : ∀ L, midOthers Dv.Cmp.toK2 Dv.MR L +
    max (∑ β, Dv.MR.toPrefix.KL β) (∑ β, Dv.MR.toPrefix.KR β) +
    (12 / 2 ^ 534 + Sarkozy.EnvPrefix.Uup SA.Cs SA.Ca SA.hCs SA.hCa + 11 / 10 ^ 70) ≤
      targetLedger.T
  /-- The class inputs: B11's steps, the upper prices, the aggregate (E1), the mean data with
  the combined gate (`ClassPartsE4B`). -/
  Cls : ClassPartsE4B (Dv.toMF3 hB SA hmid).toK2.toK1.data
  /-- The inputs of `SF`, `fix`, `env` (B5, B9). -/
  Sh : SharpParts2 (Dv.toMF3 hB SA hmid).toK2.toK1.toJoint

/-- K1's layer (F1P's maps for the block data and `hSA`). -/
noncomputable def MainFinalObligations3d.toJB {hB : Target.BMOR} (hRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3d hW hMR hFour hB) : MainFinalObligationsJB hW hMR hFour where
  Dv := (O.Dv.toMF3 hB O.SA O.hmid).toK2.toK1
  hSA := (O.SA.toK2 hB).toSAExplicit hB hRR
  Cls := O.Cls
  Sh := O.Sh

/-- **The P1-only obligations give the final ones** (`ClassPartsE4A.toB`): `final3d` is the
stronger theorem. -/
noncomputable def MainFinalObligations3dA.toD {hB : Target.BMOR}
    (O : MainFinalObligations3dA hW hMR hFour hB) : MainFinalObligations3d hW hMR hFour hB where
  Dv := O.Dv
  SA := O.SA
  hmid := O.hmid
  Cls := O.Cls.toB
  Sh := O.Sh

/-- **C10's class inputs give the new ones** (`E1InputsAgg.ofUniform` for (E1); `H`, `Kπ`, `hK`,
`hyπ` forgotten; the gate `AllocJ` is `AllocJB` with the same numbers). -/
noncomputable def ClassPartsE4.toB {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
    {D : TheoremCBlock.ComparisonData targetDecay paperM0 (PartVLaws.paperAtomMap blockOf)
      paperTail paperPr paperH Chamber} (C : MainFinalJ.ClassPartsE4 D) : ClassPartsE4B D where
  cd := C.cd
  ES :=
    { Θ := C.ES.Θ
      Z := C.ES.Z
      u := C.ES.u
      wc := C.ES.wc
      wc_nonneg := C.ES.wc_nonneg
      ρ := C.ES.ρ
      ops := C.ES.ops
      upper := C.ES.upper }
  E1 := E1InputsAgg.ofUniform targetDecay_nonneg C.E1
  MD :=
    { lab := C.MD.lab
      hw := C.MD.hw
      N := C.MD.N
      W := C.MD.W
      Vv := C.MD.Vv
      hW0 := C.MD.hW0
      hVv := C.MD.hVv
      hcard := C.MD.hcard
      hwW := C.MD.hwW
      hv0 := C.MD.hv0
      hvV := C.MD.hvV
      mean := C.MD.mean
      alloc := C.MD.alloc }

/-- **F1P's `final3c` obligations give the `final3d` ones**: `final3d` is the stronger theorem. -/
noncomputable def MainFinalObligations3c.toD {hB : Target.BMOR}
    (O : MainFinalF1.MainFinalObligations3c hW hMR hFour hB) :
    MainFinalObligations3d hW hMR hFour hB where
  Dv := O.Dv
  SA := O.SA
  hmid := O.hmid
  Cls := ClassPartsE4.toB O.Cls
  Sh := O.Sh

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵` at the F1 partition, with `hB`, `hL₀`
proved, no histogram claim, (E1) in the paper's aggregate form, and no unused class evaluations**
(`thm:main` at `ε = a_T/71`, via `thm:comparison` with `cor:joint-closing`,
`eq:final-joint-closing` and `thm:density:induction` at `a_T`; `def:robust` with
`lem:record:density-lp`; `def:record:exact-blocks`(d) in place of (c) below `X_Ch`). Hypotheses as
`MainFinalF1.main_target_f1_final3c`, with `O : MainFinalObligations3d`. -/
theorem main_target_f1_final3d (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3d hWeil hMovingRoot hFourCycle hBMOR) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_f1_finalJB hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR
    (O.toJB hThetaSmallRR)

/-- **`main_target_f1_final3d` at the owner's goal exponent** `N^{0.99999}`
(`TargetGoal.epsGoal = 10⁻⁵ ≤ epsTarget`, `Target.sarkozyBound_mono`). -/
theorem main_goal_f1b (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3d hWeil hMovingRoot hFourCycle hBMOR) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  Target.sarkozyBound_mono TargetGoal.epsGoal_le_targetSaving
    (main_target_f1_final3d hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O)

end Sarkozy.MainFinalF1b
