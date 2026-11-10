module

public import Sarkozy.MeanCredit2.Classes
public import Sarkozy.MeanCredit2.Comparison

@[expose] public section

/-!
# The constructors with the comparison split into its class-free part and the class savings

`paper/sections/32_four_routes_closing.tex`, `eq:final-joint-closing`;
`paper/sections/23_envelopes.tex`, `cor:envelope-costs`.

`mdInputsPaperSplit`, `classPartsPaperSplit`, `jointBound_paperSplit`: `mdInputsPaper` etc. with
the comparison coefficient `c = c_B − s`. The single comparison hypothesis (`hC`, `hCv`) is replaced
by the class-free completion `hB` and the savings completion `hS` with `hSv`
(`S_v ≥ D_cls + D_var`); the relation to the harness's `𝓔` is kernel-checked
(`harnessE_formula`).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MeanCredit2

open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper Sarkozy.ClassData Sarkozy.MainFinal2
open Sarkozy.MainFinalF1b Sarkozy.MeanCredit
open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.JointClosing
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.Comparison (remainder energyMean)
open Sarkozy.BlockFrame
open Sarkozy.Param (Params)
open Sarkozy.PartVLaws (paperAtomMap)
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.GramBracketPaper

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
  {D : CD blockOf} {cd : ClassData D.CL} {K : Type} [Fintype K] [DecidableEq K]
  {C : Type} [Fintype C] [DecidableEq C]

/-- **The mean data at the paper's coefficients, the comparison split** (`mdInputsPaper` with
`c = c_B − s`, `hC`, `hCv` from `hB`, `hS`, `hSv` and `harnessE_formula`). -/
noncomputable def mdInputsPaperSplit
    (labS : ∀ L, Choice (D.CL.T L) → Option K) (labK : K → PaperDiag)
    (μK : K → ℝ) (hμ0 : ∀ k, 0 ≤ μK k) (hμle : ∀ k, μK k ≤ diagB (labK k))
    (hz : ∀ k, (diagB (labK k) : ℝ) = 0 → μK k = 0)
    (hnz : ∀ k, (diagB (labK k) : ℝ) ≠ 0 → μK k ≠ 0)
    (Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ)
    (wc : ∀ L, cd.ι L → K → ℝ) (wc_nonneg : ∀ L i j, 0 ≤ wc L i j)
    (ρ : ∀ L, Choice (D.CL.T L) → ℝ)
    (ops : ClassStepsOps cd (fun _ => K)
      (fun L A => agg (cd.sel L) (labS L) (wtOf labK μK) (Zs L A)) wc ρ)
    (hup : SelUpper D cd labS (wtOf labK μK) Zs wc)
    (hwPaper : ∀ L k, (aggED labS (wtOf labK μK) (wtOf_nonneg labK hμ0) Zs wc wc_nonneg ρ ops
      hup).w L k = diagW (labK k) / wtOf labK μK k)
    (W Vv : ℝ) (hW0 : 0 ≤ W) (hVv : 0 ≤ Vv)
    (hwW : ∀ L k, (aggED labS (wtOf labK μK) (wtOf_nonneg labK hμ0) Zs wc wc_nonneg ρ ops
      hup).w L k ≤ W)
    (hvV : ∀ L k, (aggED labS (wtOf labK μK) (wtOf_nonneg labK hμ0) Zs wc wc_nonneg ρ ops
      hup).v L k ≤ Vv)
    (hZs : ∀ L A ω, 0 ≤ Zs L A ω)
    (hm : SelMean D cd (fun L ω => (labS L ω).elim 0 μK) Zs)
    (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C) (cB s : (MLetter ⊕ C → ℕ) → ℝ)
    (X : MLetter ⊕ C → ℝ) (hX0 : ∀ l, 0 ≤ X l)
    (hXm : ∀ l, X (.inl l) = mTot xq 0 0 Vq (Uq - Vq) l)
    (hX : ∀ L l, letterTotal (ℓ L) (D.CL.π L) l ≤ X l)
    (hres : ∀ d, 0 ≤ 63 * (cB d - s d) - mLift d)
    (hB : HasSum (fun d => cB d * ∏ l, X l ^ d l / (d l).factorial)
      ((Bh : ℝ) * (Real.exp Sh * Real.cosh Ah - 1)))
    (Sv : ℝ) (hS : HasSum (fun d => s d * ∏ l, X l ^ d l / (d l).factorial) Sv)
    (hSv : ((Dcls + Dvar : ℚ) : ℝ) ≤ Sv)
    (r : ∀ L, Choice (D.CL.T L) → ℝ)
    (hρ : ∀ L, ∀ ω ∈ cd.sel L, cd.cls L ω ≠ none → ρ L ω ≤ r L ω * monomial (D.CL.π L) ω)
    (hcomp : ∀ L, ∀ ω ∈ cd.sel L, (if cd.cls L ω = none then D.B else r L ω) +
      (labS L ω).elim 0 (fun k => (diagW (labK k) : ℝ)) ≤ cB (deg (ℓ L) ω) - s (deg (ℓ L) ω))
    (hmean : ∀ L, ∀ ω ∈ cd.sel L, mLift (deg (ℓ L) ω) ≤ (labS L ω).elim 0 μK)
    : MDInputsE4B (aggED labS (wtOf labK μK) (wtOf_nonneg labK hμ0) Zs wc wc_nonneg ρ ops hup) :=
  mdInputsPaper labS labK μK hμ0 hμle hz hnz Zs wc wc_nonneg ρ ops hup hwPaper W Vv hW0 hVv
    hwW hvV hZs hm ℓ (fun d => cB d - s d) X hX0 hXm hX hres
    ((Bh : ℝ) * (Real.exp Sh * Real.cosh Ah - 1) - Sv) (1 / 10 ^ 28) (by norm_num)
    (by convert hB.sub hS using 1; funext d; ring)
    (by have h := harnessE_formula; push_cast at hSv; linarith) r hρ hcomp hmean

/-- **The class group at the paper's coefficients, the comparison split.** -/
noncomputable def classPartsPaperSplit
    (labS : ∀ L, Choice (D.CL.T L) → Option K) (labK : K → PaperDiag)
    (μK : K → ℝ) (hμ0 : ∀ k, 0 ≤ μK k) (hμle : ∀ k, μK k ≤ diagB (labK k))
    (hz : ∀ k, (diagB (labK k) : ℝ) = 0 → μK k = 0)
    (hnz : ∀ k, (diagB (labK k) : ℝ) ≠ 0 → μK k ≠ 0)
    (Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ)
    (wc : ∀ L, cd.ι L → K → ℝ) (wc_nonneg : ∀ L i j, 0 ≤ wc L i j)
    (ρ : ∀ L, Choice (D.CL.T L) → ℝ)
    (ops : ClassStepsOps cd (fun _ => K)
      (fun L A => agg (cd.sel L) (labS L) (wtOf labK μK) (Zs L A)) wc ρ)
    (hup : SelUpper D cd labS (wtOf labK μK) Zs wc)
    (hwPaper : ∀ L k, (aggED labS (wtOf labK μK) (wtOf_nonneg labK hμ0) Zs wc wc_nonneg ρ ops
      hup).w L k = diagW (labK k) / wtOf labK μK k)
    (W Vv : ℝ) (hW0 : 0 ≤ W) (hVv : 0 ≤ Vv)
    (hwW : ∀ L k, (aggED labS (wtOf labK μK) (wtOf_nonneg labK hμ0) Zs wc wc_nonneg ρ ops
      hup).w L k ≤ W)
    (hvV : ∀ L k, (aggED labS (wtOf labK μK) (wtOf_nonneg labK hμ0) Zs wc wc_nonneg ρ ops
      hup).v L k ≤ Vv)
    (hZs : ∀ L A ω, 0 ≤ Zs L A ω)
    (hm : SelMean D cd (fun L ω => (labS L ω).elim 0 μK) Zs)
    (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C) (cB s : (MLetter ⊕ C → ℕ) → ℝ)
    (X : MLetter ⊕ C → ℝ) (hX0 : ∀ l, 0 ≤ X l)
    (hXm : ∀ l, X (.inl l) = mTot xq 0 0 Vq (Uq - Vq) l)
    (hX : ∀ L l, letterTotal (ℓ L) (D.CL.π L) l ≤ X l)
    (hres : ∀ d, 0 ≤ 63 * (cB d - s d) - mLift d)
    (hB : HasSum (fun d => cB d * ∏ l, X l ^ d l / (d l).factorial)
      ((Bh : ℝ) * (Real.exp Sh * Real.cosh Ah - 1)))
    (Sv : ℝ) (hS : HasSum (fun d => s d * ∏ l, X l ^ d l / (d l).factorial) Sv)
    (hSv : ((Dcls + Dvar : ℚ) : ℝ) ≤ Sv)
    (r : ∀ L, Choice (D.CL.T L) → ℝ)
    (hρ : ∀ L, ∀ ω ∈ cd.sel L, cd.cls L ω ≠ none → ρ L ω ≤ r L ω * monomial (D.CL.π L) ω)
    (hcomp : ∀ L, ∀ ω ∈ cd.sel L, (if cd.cls L ω = none then D.B else r L ω) +
      (labS L ω).elim 0 (fun k => (diagW (labK k) : ℝ)) ≤ cB (deg (ℓ L) ω) - s (deg (ℓ L) ω))
    (hmean : ∀ L, ∀ ω ∈ cd.sel L, mLift (deg (ℓ L) ω) ≤ (labS L ω).elim 0 μK)
    (E1 : E1InputsAgg D) : ClassPartsE4B D :=
  classPartsOfCM D cd K labS (wtOf labK μK) (wtOf_nonneg labK hμ0) Zs wc wc_nonneg ρ ops hup E1
    (mdInputsPaperSplit labS labK μK hμ0 hμle hz hnz Zs wc wc_nonneg ρ ops hup hwPaper W Vv hW0 hVv
      hwW hvV hZs hm ℓ cB s X hX0 hXm hX hres hB Sv hS hSv r hρ hcomp hmean)

/-- **`JB` at the paper's coefficients, the comparison split** (`cor:joint-closing`). -/
theorem jointBound_paperSplit (labS : ∀ L, Choice (D.CL.T L) → Option K) (labK : K → PaperDiag)
    (μK : K → ℝ) (hμ0 : ∀ k, 0 ≤ μK k) (hμle : ∀ k, μK k ≤ diagB (labK k))
    (hz : ∀ k, (diagB (labK k) : ℝ) = 0 → μK k = 0)
    (hnz : ∀ k, (diagB (labK k) : ℝ) ≠ 0 → μK k ≠ 0)
    (Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ)
    (wc : ∀ L, cd.ι L → K → ℝ) (wc_nonneg : ∀ L i j, 0 ≤ wc L i j)
    (ρ : ∀ L, Choice (D.CL.T L) → ℝ)
    (ops : ClassStepsOps cd (fun _ => K)
      (fun L A => agg (cd.sel L) (labS L) (wtOf labK μK) (Zs L A)) wc ρ)
    (hup : SelUpper D cd labS (wtOf labK μK) Zs wc)
    (hwPaper : ∀ L k, (aggED labS (wtOf labK μK) (wtOf_nonneg labK hμ0) Zs wc wc_nonneg ρ ops
      hup).w L k = diagW (labK k) / wtOf labK μK k)
    (W Vv : ℝ) (hW0 : 0 ≤ W) (hVv : 0 ≤ Vv)
    (hwW : ∀ L k, (aggED labS (wtOf labK μK) (wtOf_nonneg labK hμ0) Zs wc wc_nonneg ρ ops
      hup).w L k ≤ W)
    (hvV : ∀ L k, (aggED labS (wtOf labK μK) (wtOf_nonneg labK hμ0) Zs wc wc_nonneg ρ ops
      hup).v L k ≤ Vv)
    (hZs : ∀ L A ω, 0 ≤ Zs L A ω)
    (hm : SelMean D cd (fun L ω => (labS L ω).elim 0 μK) Zs)
    (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C) (cB s : (MLetter ⊕ C → ℕ) → ℝ)
    (X : MLetter ⊕ C → ℝ) (hX0 : ∀ l, 0 ≤ X l)
    (hXm : ∀ l, X (.inl l) = mTot xq 0 0 Vq (Uq - Vq) l)
    (hX : ∀ L l, letterTotal (ℓ L) (D.CL.π L) l ≤ X l)
    (hres : ∀ d, 0 ≤ 63 * (cB d - s d) - mLift d)
    (hB : HasSum (fun d => cB d * ∏ l, X l ^ d l / (d l).factorial)
      ((Bh : ℝ) * (Real.exp Sh * Real.cosh Ah - 1)))
    (Sv : ℝ) (hS : HasSum (fun d => s d * ∏ l, X l ^ d l / (d l).factorial) Sv)
    (hSv : ((Dcls + Dvar : ℚ) : ℝ) ≤ Sv)
    (r : ∀ L, Choice (D.CL.T L) → ℝ)
    (hρ : ∀ L, ∀ ω ∈ cd.sel L, cd.cls L ω ≠ none → ρ L ω ≤ r L ω * monomial (D.CL.π L) ω)
    (hcomp : ∀ L, ∀ ω ∈ cd.sel L, (if cd.cls L ω = none then D.B else r L ω) +
      (labS L ω).elim 0 (fun k => (diagW (labK k) : ℝ)) ≤ cB (deg (ℓ L) ω) - s (deg (ℓ L) ω))
    (hmean : ∀ L, ∀ ω ∈ cd.sel L, mLift (deg (ℓ L) ω) ≤ (labS L ω).elim 0 μK)
    (E1 : E1InputsAgg D) : JointBound D targetLedger.jointConstant :=
  (classPartsPaperSplit labS labK μK hμ0 hμle hz hnz Zs wc wc_nonneg ρ ops hup hwPaper W Vv hW0 hVv
      hwW hvV hZs hm ℓ cB s X hX0 hXm hX hres hB Sv hS hSv r hρ hcomp hmean E1).jointBound

end Sarkozy.MeanCredit2
