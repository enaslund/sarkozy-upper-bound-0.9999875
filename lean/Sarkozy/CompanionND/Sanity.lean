module

public import Sarkozy.CompanionND.Main

@[expose] public section

/-!
# Sanity checks for `main_goal_rebased_nd` (FC, after ND)

* **The ND statement subsumes RG's**: every `Companion.CompanionObligations` gives a
  `CompanionObligationsND` by forgetting `SDB` (`ofCompanion`; all other fields are
  passed unchanged, the class and sharp data being typed at the same joint block data up to proof
  irrelevance). So `main_goal_rebased` follows from `main_goal_rebased_nd`
  (`main_goal_rebased_of_nd`), and `CompanionObligationsND` adds no hypothesis.
* **The front is ND's**: `O.toKT1.F` is NB3's `FrontN3.toK` of ND's `FrontN3ND.toN3` (`rfl`), and
  the class group is CM's at the fields of `O` (`rfl`).
-/

namespace Sarkozy.CompanionND

open Sarkozy.Companion (CompanionObligations)
open Sarkozy.UpperCapsPaper (UpperRecordTables)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {hB : Target.BMOR} {hRR : Target.ThetaSmallRR} {UpT : UpperRecordTables}

/-- RG's front without `SDB`. -/
def frontOfCompanion (F : Companion.CompanionFront hW hMR hFour UpT) :
    CompanionFrontND hW hMR hFour UpT :=
  ⟨F.PCu, F.BA, F.rep, F.hs, F.ha⟩

/-- **Forgetting `SDB`**: `Companion.CompanionObligations` gives `CompanionObligationsND`, every
other field unchanged. -/
noncomputable def ofCompanion (O : CompanionObligations hW hMR hFour hB hRR UpT) :
    CompanionObligationsND hW hMR hFour hB hRR UpT where
  F := frontOfCompanion O.F
  cd := O.cd
  K := O.K
  instFK := O.instFK
  instDK := O.instDK
  Lt := O.Lt
  instFLt := O.instFLt
  instDLt := O.instDLt
  labS := O.labS
  labK := O.labK
  μK := O.μK
  Zs := O.Zs
  wc := O.wc
  ρ := O.ρ
  r := O.r
  Vv := O.Vv
  ℓ := O.ℓ
  c := O.c
  X := O.X
  Cv := O.Cv
  τ := O.τ
  εE := O.εE
  cE := O.cE
  r0 := O.r0
  rE := O.rE
  sf := O.sf
  c₂ := O.c₂
  hμ0 := O.hμ0
  hμle := O.hμle
  hz := O.hz
  hnz := O.hnz
  wc_nonneg := O.wc_nonneg
  hwPaper := O.hwPaper
  hVv := O.hVv
  hvV := O.hvV
  hZs := O.hZs
  hX0 := O.hX0
  hXm := O.hXm
  hτ := O.hτ
  hεE0 := O.hεE0
  hεEt := O.hεEt
  hcE := O.hcE
  hrE0 := O.hrE0
  hr00 := O.hr00
  hεS0 := O.hεS0
  hεSt := O.hεSt
  hcS := O.hcS
  hrpm0 := O.hrpm0
  hc₂ := O.hc₂
  hres := O.hres
  hC := O.hC
  hCv := O.hCv
  hup := O.hup
  hsub := O.hsub
  hfold := O.hfold
  ops := O.ops
  hm := O.hm
  hρ := O.hρ
  hcomp := O.hcomp
  hmean := O.hmean
  hX := O.hX
  hcoup := O.hcoup
  hremE := O.hremE
  hremS := O.hremS
  fixL := O.fixL
  fixR := O.fixR
  envL := O.envL
  envR := O.envR

/-- **`main_goal_rebased` from `main_goal_rebased_nd`** (through `ofCompanion`): the ND
statement is at least as strong as RG's. -/
theorem main_goal_rebased_of_nd (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables)
    (O : CompanionObligations hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR UpT) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_rebased_nd hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR UpT
    (ofCompanion O)

/-- The front of `O.toKT1` is NB3's `FrontN3.toK` of ND's `FrontN3ND.toN3`; the class group is
CM's at the fields of `O`. -/
theorem toKT1_F_nd (O : CompanionObligationsND hW hMR hFour hB hRR UpT) :
    O.toKT1.F = O.F.toN3ND.toN3.toK ∧ O.toKT1.Cls.cd = O.cd ∧ O.toKT1.Cls.ES.wc = O.wc ∧
      O.toKT1.Sh.SF.dec = O.sf.dec :=
  ⟨rfl, rfl, rfl, rfl⟩

end Sarkozy.CompanionND
