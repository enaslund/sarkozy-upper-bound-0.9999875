module

public import Sarkozy.Companion.Main
public import Sarkozy.MeanCredit2.Comparison
public import Sarkozy.MeanCredit2.Sanity

@[expose] public section




namespace Sarkozy.Companion

open Sarkozy.MainFinalF1b Sarkozy.ThetaOne Sarkozy.MainCombined2

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- Every `E1InputsAgg` is `E1InputsAgg.ofFields` of its fields: the split of (E1) into
`E1Sub` (R), `E1Coup`, `E1Rem` (C) adds no hypothesis. -/
theorem e1_ofFields_eq (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (I : E1InputsAgg D) :
    E1InputsAgg.ofFields D I.εE I.hε0 I.hεt I.cE I.hcE I.r0 I.r I.hsub I.hcoup I.hrem I.hr0
      I.hs0 = I := rfl

omit [DecidableEq P] in
/-- Every `SharpFirstBaseInputs` is `SharpFirstBaseInputs.ofFields` of its fields: the split of
`SF` into `SFFold` (R), `SFRem` (C) adds no hypothesis. -/
theorem sf_ofFields_eq (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (I : SharpFirstBaseInputs D) :
    SharpFirstBaseInputs.ofFields D I.dec I.ε I.hε0 I.hεt I.c I.hc I.rp I.rm I.hr0 I.hfold
      I.hrem = I := rfl

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {hB : Target.BMOR} {hRR : Target.ThetaSmallRR} {UpT : UpperCapsPaper.UpperRecordTables}

/-- The class group of `O.toKT1` is CM's at the fields of `O`: its classes are `O.cd`, its
labelled diagonals are `O.K`, its (E1) is the flattened one. -/
theorem toKT1_Cls (O : CompanionObligations hW hMR hFour hB hRR UpT) :
    O.toKT1.Cls.cd = O.cd ∧ O.toKT1.Cls.ES.Θ = (fun _ => O.K) ∧ O.toKT1.Cls.ES.wc = O.wc ∧
      O.toKT1.Cls.ES.ρ = O.ρ ∧ O.toKT1.Cls.E1 = O.E1 ∧ O.toKT1.Cls.MD.lab = fun _ => O.labK :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The front of `O.toKT1` is NB3's `FrontN3.toK` of RG's `CompanionFront.toN3` at
`SD := SDB.toSD`. -/
theorem toKT1_F (O : CompanionObligations hW hMR hFour hB hRR UpT) :
    O.toKT1.F = O.F.toN3.toK ∧ O.F.toN3.UpB = O.F.UpB := ⟨rfl, rfl⟩

/-- The sharp group of `O.toKT1` is SH2's constructor at the flattened `SF`. -/
theorem toKT1_Sh (O : CompanionObligations hW hMR hFour hB hRR UpT) :
    O.toKT1.Sh.SF.dec = O.sf.dec ∧ O.ShPT.c₂ = O.c₂ := ⟨rfl, rfl⟩

open Sarkozy.ClassData Sarkozy.MeanCredit2 in
/-- **CM's split comparison hypotheses give the single one** (`hC`, `hCv` with `c = c_B − s`,
`C_v = B_h(e^{S_h} cosh A_h − 1) − S_v`, `τ = 10⁻²⁸`; `harnessE_formula`). -/
theorem single_of_split {C : Type} [Fintype C] (cB s : (MLetter ⊕ C → ℕ) → ℝ)
    (X : MLetter ⊕ C → ℝ)
    (hB : HasSum (fun d => cB d * ∏ l, X l ^ d l / (d l).factorial)
      ((Bh : ℝ) * (Real.exp MeanCredit2.Sh * Real.cosh Ah - 1)))
    (Sv : ℝ) (hS : HasSum (fun d => s d * ∏ l, X l ^ d l / (d l).factorial) Sv)
    (hSv : ((Dcls + Dvar : ℚ) : ℝ) ≤ Sv) :
    HasSum (fun d => (cB d - s d) * ∏ l, X l ^ d l / (d l).factorial)
        ((Bh : ℝ) * (Real.exp MeanCredit2.Sh * Real.cosh Ah - 1) - Sv) ∧
      (Bh : ℝ) * (Real.exp MeanCredit2.Sh * Real.cosh Ah - 1) - Sv ≤ harnessE + 1 / 10 ^ 28 := by
  refine ⟨by convert hB.sub hS using 1; funext d; ring, ?_⟩
  have h := harnessE_formula
  push_cast at hSv
  linarith

open Sarkozy.ClassData Sarkozy.MeanCredit2 in
/-- **The (F) group with the side conditions `hX0`, `hXm`, `hτ` is satisfiable** (on CM's toy
lettering `MLetter ⊕ Unit`, from `split_hypotheses_satisfiable` and `single_of_split`). -/
theorem numerics_satisfiable :
    ∃ (c : (MLetter ⊕ Unit → ℕ) → ℝ) (X : MLetter ⊕ Unit → ℝ) (Cv τ : ℝ),
      (∀ l, 0 ≤ X l) ∧ (∀ l, X (.inl l) = mTot xq 0 0 Vq (Uq - Vq) l) ∧ τ ≤ 3 / 100 ∧
      (∀ d, 0 ≤ 63 * c d - mLift d) ∧
      HasSum (fun d => c d * ∏ l, X l ^ d l / (d l).factorial) Cv ∧ Cv ≤ harnessE + τ := by
  obtain ⟨cB, s, Sv, h0, hm, hres, hB, hS, hSv⟩ := split_hypotheses_satisfiable
  obtain ⟨hC, hCv⟩ := single_of_split cB s Xtoy hB Sv hS hSv
  exact ⟨fun d => cB d - s d, Xtoy, _, 1 / 10 ^ 28, h0, hm, by norm_num, hres, hC, hCv⟩

end Sarkozy.Companion
