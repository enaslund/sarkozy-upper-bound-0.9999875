module

public import Sarkozy.MeanCredit2.Booking

@[expose] public section

/-!
# The class group of `main_goal_theta1k` at the paper's coefficients (CM, second round)

`paper/sections/24a_joint_mean.tex`, `prop:joint-middle-mean`;
`paper/sections/11_comparison_proof.tex`, `cor:joint-closing`;
`paper/sections/32_four_routes_closing.tex`, `eq:final-joint-closing`.

**`mdInputsPaper`** is `MeanCredit.mdInputsOfSel` with:
* the exact weights `wt = wtOf labK μK` and separate labels;
* `hw` proved (`wtOf_le_one`, `diagW_pos`);
* `hμ` proved (`coefOf_wtOf`), with the selection-level mean coefficient `μ_ω = μK(label ω)`;
* the booking condition `hRc` proved from the two identifications `hcomp`, `hmean` (`hRc_paper`),
  with `R = 63c − mLift`;
* `R ≥ 0` taken as the residual gates `hres`;
* the evaluation `hser` from `seriesBound_paper`. Its mean side (`64 Δ_mid` at E3's v2 totals) is
  kernel-checked; its comparison side is the numerical hypothesis `hC`, `hCv`.

**`classPartsPaper`**, **`jointBound_paper`**: the class group and `JB`.

What this removes, compared with `MeanCredit.classPartsOfCM`:
* the weights and `hw`, `hμ`, `hRc` (now proved from the paper's coefficients);
* the free bound `SeriesBound` (now the mean closed form, the kernel-checked mean value and one
  comparison hypothesis).
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

omit [Fintype K] [DecidableEq K] in
theorem wtOf_pos (labK : K → PaperDiag) (μK : K → ℝ) (hμ0 : ∀ k, 0 ≤ μK k)
    (hnz : ∀ k, (diagB (labK k) : ℝ) ≠ 0 → μK k ≠ 0) (k : K) : 0 < wtOf labK μK k := by
  unfold wtOf
  split_ifs with h
  · exact one_pos
  · have hd : (0 : ℝ) < diagB (labK k) :=
      lt_of_le_of_ne (by exact_mod_cast diagB_nonneg (labK k)) (Ne.symm h)
    exact div_pos (lt_of_le_of_ne (hμ0 k) (Ne.symm (hnz k h))) hd

omit [Fintype K] [DecidableEq K] in
/-- **The booking condition at the paper's coefficients** (`hRc` of `alloc_of_sel`), with
`R = 63 c − mLift`: from the comparison identification `hcomp` (the comparison coefficient of a
selection's letter degree is at least `B` off the classes, `r_ω` on them, plus `κ_b − var` once when
labelled) and the mean identification `hmean` (`mLift(deg ω) ≤ μK(label ω)`, `0` unlabelled). -/
theorem hRc_paper (labS : ∀ L, Choice (D.CL.T L) → Option K) (labK : K → PaperDiag)
    (μK : K → ℝ) (hz : ∀ k, (diagB (labK k) : ℝ) = 0 → μK k = 0)
    (hnz : ∀ k, (diagB (labK k) : ℝ) ≠ 0 → μK k ≠ 0) (w : ℕ → K → ℝ)
    (hwPaper : ∀ L k, w L k = diagW (labK k) / wtOf labK μK k)
    (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C) (c : (MLetter ⊕ C → ℕ) → ℝ)
    (r : ∀ L, Choice (D.CL.T L) → ℝ)
    (hcomp : ∀ L, ∀ ω ∈ cd.sel L, (if cd.cls L ω = none then D.B else r L ω) +
      (labS L ω).elim 0 (fun k => (diagW (labK k) : ℝ)) ≤ c (deg (ℓ L) ω))
    (hmean : ∀ L, ∀ ω ∈ cd.sel L, mLift (deg (ℓ L) ω) ≤ (labS L ω).elim 0 μK) :
    ∀ L, ∀ ω ∈ cd.sel L, (if cd.cls L ω = none then 63 * D.B else 63 * r L ω) +
      coefOf (fun j => 63 * w L j - (diagB (labK j) : ℝ)) (wtOf labK μK) (labS L ω) ≤
        63 * c (deg (ℓ L) ω) - mLift (deg (ℓ L) ω) := by
  intro L ω hω
  have e : (fun j => 63 * w L j - (diagB (labK j) : ℝ)) =
      fun j => 63 * ((diagW (labK j) : ℝ) / wtOf labK μK j) - diagB (labK j) :=
    funext fun j => by rw [hwPaper]
  rw [e, bookedCoef_paper' labK μK hz hnz]
  have h1 := hcomp L ω hω
  have h2 := hmean L ω hω
  have hif : (if cd.cls L ω = none then 63 * D.B else 63 * r L ω) =
      63 * (if cd.cls L ω = none then D.B else r L ω) := by split_ifs <;> rfl
  rw [hif]
  rcases hl : labS L ω with _ | k
  · rw [hl] at h1 h2
    simp only [Option.elim_none] at h1 h2 ⊢
    linarith
  · rw [hl] at h1 h2
    simp only [Option.elim_some] at h1 h2 ⊢
    linarith

omit [Fintype K] [DecidableEq K] in
/-- **The residual gates on the degrees of labelled selections follow from the identifications**
(`prop:joint-middle-mean`, the 192 gates): `hcomp`, `hmean` and `μK ≤ diagB`, with `r ≥ 0` on the
class selections, give `63 c − mLift > 23.66` at the letter degree of every labelled selection in a
class. So `hres` is a hypothesis only on degrees no labelled selection realizes. -/
theorem hres_of_ids (labS : ∀ L, Choice (D.CL.T L) → Option K) (labK : K → PaperDiag)
    (μK : K → ℝ) (hμle : ∀ k, μK k ≤ diagB (labK k))
    (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C) (c : (MLetter ⊕ C → ℕ) → ℝ)
    (r : ∀ L, Choice (D.CL.T L) → ℝ)
    (hcomp : ∀ L, ∀ ω ∈ cd.sel L, (if cd.cls L ω = none then D.B else r L ω) +
      (labS L ω).elim 0 (fun k => (diagW (labK k) : ℝ)) ≤ c (deg (ℓ L) ω))
    (hmean : ∀ L, ∀ ω ∈ cd.sel L, mLift (deg (ℓ L) ω) ≤ (labS L ω).elim 0 μK)
    (L : ℕ) (ω : Choice (D.CL.T L)) (hω : ω ∈ cd.sel L) (hcl : cd.cls L ω ≠ none)
    (hr : 0 ≤ r L ω) (k : K) (hk : labS L ω = some k) :
    2366 / 100 < 63 * c (deg (ℓ L) ω) - mLift (deg (ℓ L) ω) := by
  have h1 := hcomp L ω hω
  have h2 := hmean L ω hω
  rw [hk] at h1 h2
  simp only [hcl, ↓reduceIte, Option.elim_some] at h1 h2
  have h3 := resid_paper_nonneg (labK k) (μK k) (hμle k)
  nlinarith

/-- **The mean data at the paper's coefficients** (`MDInputsE4B` of `main_goal_theta1k`'s class
group). *Inputs*: the labels with `μK` (`0 ≤ μK ≤ diagB`, `hz`, `hnz`); the aggregated weights
`hwPaper`; the bounds `W`, `Vv`; `SelMean` at `μ_ω = μK(label ω)` with `hZs`; the letters `ℓ`,
the comparison coefficient `c` with `hres`, the totals `X` (`hX0`, `hXm`, `hX`), the comparison
series `hC`, `hCv` with `τ ≤ 3·10⁻²` (RG; `2·10⁻³` before the rebase); the residuals `r`, `hρ`;
the identifications `hcomp`, `hmean`. -/
noncomputable def mdInputsPaper (labS : ∀ L, Choice (D.CL.T L) → Option K) (labK : K → PaperDiag)
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
    (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C) (c : (MLetter ⊕ C → ℕ) → ℝ)
    (X : MLetter ⊕ C → ℝ) (hX0 : ∀ l, 0 ≤ X l)
    (hXm : ∀ l, X (.inl l) = mTot xq 0 0 Vq (Uq - Vq) l)
    (hX : ∀ L l, letterTotal (ℓ L) (D.CL.π L) l ≤ X l)
    (hres : ∀ d, 0 ≤ 63 * c d - mLift d) (Cv τ : ℝ) (hτ : τ ≤ 3 / 100)
    (hC : HasSum (fun d => c d * ∏ l, X l ^ d l / (d l).factorial) Cv)
    (hCv : Cv ≤ harnessE + τ)
    (r : ∀ L, Choice (D.CL.T L) → ℝ)
    (hρ : ∀ L, ∀ ω ∈ cd.sel L, cd.cls L ω ≠ none → ρ L ω ≤ r L ω * monomial (D.CL.π L) ω)
    (hcomp : ∀ L, ∀ ω ∈ cd.sel L, (if cd.cls L ω = none then D.B else r L ω) +
      (labS L ω).elim 0 (fun k => (diagW (labK k) : ℝ)) ≤ c (deg (ℓ L) ω))
    (hmean : ∀ L, ∀ ω ∈ cd.sel L, mLift (deg (ℓ L) ω) ≤ (labS L ω).elim 0 μK) :
    MDInputsE4B (aggED labS (wtOf labK μK) (wtOf_nonneg labK hμ0) Zs wc wc_nonneg ρ ops hup) :=
  mdInputsOfSel labS (wtOf labK μK) (wtOf_nonneg labK hμ0) Zs wc wc_nonneg ρ ops hup labK
    (fun L k => by
      rw [hwPaper L k]
      have hp := wtOf_pos labK μK hμ0 hnz k
      have h1 := wtOf_le_one labK μK hμle k
      have h2 := diagW_pos (labK k)
      rw [le_div_iff₀ hp]
      nlinarith)
    W Vv hW0 hVv hwW hvV (fun L ω => (labS L ω).elim 0 μK)
    (fun L ω _ => by
      rcases labS L ω with _ | k
      · exact le_rfl
      · rw [coefOf_wtOf]
        simp only [Option.elim_some]
        split_ifs
        · exact hμ0 k
        · exact le_rfl)
    hZs hm (MLetter ⊕ C) ℓ (fun d => 63 * c d - mLift d) hres X hX r hρ
    (hRc_paper labS labK μK hz hnz _ hwPaper ℓ c r hcomp hmean)
    (63 * τ - 4 / 10 ^ 11) (by linarith)
    (seriesBound_paper c X hX0 hXm hres Cv τ hC hCv)

/-- **The class group of `main_goal_theta1k` at the paper's coefficients**: `classPartsOfCM` with
`MD := mdInputsPaper …` and `E1` given. -/
noncomputable def classPartsPaper (labS : ∀ L, Choice (D.CL.T L) → Option K) (labK : K → PaperDiag)
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
    (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C) (c : (MLetter ⊕ C → ℕ) → ℝ)
    (X : MLetter ⊕ C → ℝ) (hX0 : ∀ l, 0 ≤ X l)
    (hXm : ∀ l, X (.inl l) = mTot xq 0 0 Vq (Uq - Vq) l)
    (hX : ∀ L l, letterTotal (ℓ L) (D.CL.π L) l ≤ X l)
    (hres : ∀ d, 0 ≤ 63 * c d - mLift d) (Cv τ : ℝ) (hτ : τ ≤ 3 / 100)
    (hC : HasSum (fun d => c d * ∏ l, X l ^ d l / (d l).factorial) Cv)
    (hCv : Cv ≤ harnessE + τ)
    (r : ∀ L, Choice (D.CL.T L) → ℝ)
    (hρ : ∀ L, ∀ ω ∈ cd.sel L, cd.cls L ω ≠ none → ρ L ω ≤ r L ω * monomial (D.CL.π L) ω)
    (hcomp : ∀ L, ∀ ω ∈ cd.sel L, (if cd.cls L ω = none then D.B else r L ω) +
      (labS L ω).elim 0 (fun k => (diagW (labK k) : ℝ)) ≤ c (deg (ℓ L) ω))
    (hmean : ∀ L, ∀ ω ∈ cd.sel L, mLift (deg (ℓ L) ω) ≤ (labS L ω).elim 0 μK)
    (E1 : E1InputsAgg D) : ClassPartsE4B D :=
  classPartsOfCM D cd K labS (wtOf labK μK) (wtOf_nonneg labK hμ0) Zs wc wc_nonneg ρ ops hup E1
    (mdInputsPaper labS labK μK hμ0 hμle hz hnz Zs wc wc_nonneg ρ ops hup hwPaper W Vv hW0 hVv
      hwW hvV hZs hm ℓ c X hX0 hXm hX hres Cv τ hτ hC hCv r hρ hcomp hmean)

/-- **`JB` at the paper's coefficients** (`cor:joint-closing`, `eq:final-joint-closing`). -/
theorem jointBound_paper (labS : ∀ L, Choice (D.CL.T L) → Option K) (labK : K → PaperDiag)
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
    (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C) (c : (MLetter ⊕ C → ℕ) → ℝ)
    (X : MLetter ⊕ C → ℝ) (hX0 : ∀ l, 0 ≤ X l)
    (hXm : ∀ l, X (.inl l) = mTot xq 0 0 Vq (Uq - Vq) l)
    (hX : ∀ L l, letterTotal (ℓ L) (D.CL.π L) l ≤ X l)
    (hres : ∀ d, 0 ≤ 63 * c d - mLift d) (Cv τ : ℝ) (hτ : τ ≤ 3 / 100)
    (hC : HasSum (fun d => c d * ∏ l, X l ^ d l / (d l).factorial) Cv)
    (hCv : Cv ≤ harnessE + τ)
    (r : ∀ L, Choice (D.CL.T L) → ℝ)
    (hρ : ∀ L, ∀ ω ∈ cd.sel L, cd.cls L ω ≠ none → ρ L ω ≤ r L ω * monomial (D.CL.π L) ω)
    (hcomp : ∀ L, ∀ ω ∈ cd.sel L, (if cd.cls L ω = none then D.B else r L ω) +
      (labS L ω).elim 0 (fun k => (diagW (labK k) : ℝ)) ≤ c (deg (ℓ L) ω))
    (hmean : ∀ L, ∀ ω ∈ cd.sel L, mLift (deg (ℓ L) ω) ≤ (labS L ω).elim 0 μK)
    (E1 : E1InputsAgg D) : JointBound D targetLedger.jointConstant :=
  (classPartsPaper labS labK μK hμ0 hμle hz hnz Zs wc wc_nonneg ρ ops hup hwPaper W Vv hW0 hVv
      hwW hvV hZs hm ℓ c X hX0 hXm hX hres Cv τ hτ hC hCv r hρ hcomp hmean E1).jointBound

end Sarkozy.MeanCredit2
