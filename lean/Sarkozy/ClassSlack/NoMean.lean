module

public import Sarkozy.Companion.ClassFields
public import Sarkozy.MeanCredit.Evaluation

@[expose] public section

/-!
# The class group without the middle mean credit (CG, 7 November 2026)

`paper/sections/24a_joint_mean.tex`, `prop:joint-middle-mean`; `prop:record:mean-credit`;
`paper/sections/11_comparison_proof.tex`, `cor:joint-closing`;
`paper/sections/32_four_routes_closing.tex`, `eq:final-joint-closing`.

**The slack pays for the middle mean credit.** At RB's package R the AllocJ spare is about `2.51`
(63-scaled), and RG states `12/5` of it (`MeanCredit.upperFree_room`, kernel). The middle mean
credit of `prop:joint-middle-mean` (families (i)–(iv)) is worth `64 Δ_mid^{ledger} = 1.0873` in the
same scale (`MeanCredit.ledgerMid`). So the class group closes with **no** retained diagonal mean:
`63 τ + 64 Δ_mid ≤ 12/5` for `τ ≤ 13/625 = 0.0208` (`noMean_room`). In the mean data, every
aggregated diagonal is booked with a paper type of zero mean coefficient (`zeroDiag`, class 14), so

* the mean field is `SelMean` at `μ = 0`: only the one-block credit `m₁` of
  `prop:record:mean-credit` (Steps 1–3) remains; the families (i)–(iv) at energy level are not used;
* the per-selection family statement `hmean` (`MeanId`) is not needed, nor the mean letters'
  totals `hXm`, nor the residual gates `hres` (`63 c − mLift ≥ 0`): the booked coefficient is
  `R = 63 c`, and `R ≥ 0` is the side condition `c ≥ 0`;
* the labels need no family coefficient `μK` (nor `hμ0`, `hμle`, `hz`, `hnz`).

The weights of the aggregation are `1/2` (`wtHalf`): the paper's weight per selection is
`diagW(labK k)`, i.e. `∑_i w_{ik} = 2 diagW(labK k)` (`WeightsHalf`), and the formal mean label
`zeroDiag` satisfies `diagW zeroDiag ≤ 2 diagW t` for every paper type `t` (`diagW_zeroDiag_le`,
kernel), which is MD's side condition `hw`. (With weight `1` no zero-mean type has a weight below
class 13's `0.4553`.) The effective weight `w · wt = diagW` is the paper's, so `ops` and
`SelUpper` have the same content as in CM's `classPartsPaper`.

**What it costs.** The comparison slack: `hCv : C_v ≤ 𝓔_h + τ` with `τ ≤ 13/625 = 0.0208`
(CM's route at the rebased ledger allows `3/100`); the exact limit of this route at the room
`12/5` is `τ ≤ 0.020837`.

**Constructors.** `mdInputsNoMean` (`MDInputsE4B`, through CM's `mdInputsOfSel`) and
`classPartsNoMean` (`ClassPartsE4B`, through CM's `classPartsOfCM`).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.ClassSlack

open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper Sarkozy.ClassData Sarkozy.MainFinal2
open Sarkozy.MainFinalF1b Sarkozy.MeanCredit Sarkozy.MeanCredit2
open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.JointClosing
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.CancellationSteps (PaperJ0)
open Sarkozy.Companion (ResidualId CompId TotalsLe)

/-! ## The numbers -/

/-- The paper type booked on every aggregated diagonal: class 14 (the aligned `E⁴` class), whose
mean coefficient is `0` at every outside degree. -/
def zeroDiag : PaperDiag := (14, 0)

theorem diagB_zeroDiag : diagB zeroDiag = 0 := by
  decide +kernel

theorem diagB_zeroDiag_real : (diagB zeroDiag : ℝ) = 0 := by
  rw [diagB_zeroDiag, Rat.cast_zero]

/-- The weight of `zeroDiag` against twice the sixteen class weights (kernel). -/
theorem zeroDiag_weight_check :
    allBelow 16 (fun i => decide (wQ 14 ≤ 2 * wQ i)) = true := by
  decide +kernel

/-- **MD's side condition `hw` at weight `1/2`**: `diagW zeroDiag ≤ 2 diagW t` for every paper
type `t` (`0.4609 ≤ 2 · 0.4553`, class 13 being the smallest). -/
theorem diagW_zeroDiag_le (t : PaperDiag) : (diagW zeroDiag : ℝ) ≤ 2 * diagW t := by
  have h := of_decide_eq_true (allBelow_spec zeroDiag_weight_check t.1 t.1.2)
  have h' : ((wQ 14 : ℚ) : ℝ) ≤ ((2 * wQ t.1 : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  exact h'

/-- **The room of the mean-free evaluation**: `63 τ + 64 Δ_mid^{ledger} ≤ 12/5` for
`τ ≤ 13/625 = 0.0208` (`1.3104 + 1.0873 = 2.3977`). -/
theorem noMean_room (τ : ℝ) (hτ : τ ≤ 13 / 625) : 63 * τ + 64 * (ledgerMid : ℝ) ≤ 12 / 5 := by
  have h : (64 * ledgerMid : ℚ) ≤ 12 / 5 - 819 / 625 := by
    unfold ledgerMid
    norm_num
  have h' : ((64 * ledgerMid : ℚ) : ℝ) ≤ ((12 / 5 - 819 / 625 : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith

/-- **The mean-free evaluation** (`eq:final-joint-closing` with no retained mean): with `c ≥ 0`,
`X ≥ 0` and the completed comparison series `C_v ≤ 𝓔_h + τ`, every partial sum of the completed
series of `63 c` is at most `63 𝓔_h − 64 Δ_mid + (63 τ + 64 Δ_mid)`. -/
theorem seriesBound_noMean {Λ : Type} [Fintype Λ] (c : (Λ → ℕ) → ℝ) (X : Λ → ℝ)
    (hX0 : ∀ l, 0 ≤ X l) (hc0 : ∀ d, 0 ≤ c d) (Cv τ : ℝ)
    (hC : HasSum (fun d => c d * ∏ l, X l ^ d l / (d l).factorial) Cv)
    (hCv : Cv ≤ harnessE + τ) :
    SeriesBound (fun d => 63 * c d) X
      (63 * (harnessE : ℝ) - 64 * (ledgerMid : ℝ) + (63 * τ + 64 * (ledgerMid : ℝ))) := by
  have h0 : HasSum (fun d : Λ → ℕ => (fun _ => (0 : ℝ)) d * ∏ l, X l ^ d l / (d l).factorial)
      0 := by
    simp only [zero_mul]
    exact hasSum_zero
  have h := seriesBound_of_hasSum c (fun _ => 0) X hX0 (fun d => by linarith [hc0 d]) Cv 0 hC h0
  intro Ds
  have h1 := h Ds
  simp only [sub_zero] at h1
  linarith

/-! ## The constructors -/

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
  {D : CD blockOf} {cd : ClassData D.CL} {K : Type} [Fintype K] [DecidableEq K]
  {C : Type} [Fintype C] [DecidableEq C]

/-- The aggregation weights of the mean-free route: `1/2` on every label. -/
noncomputable def wtHalf (K : Type) : K → ℝ := fun _ => 1 / 2

theorem wtHalf_nonneg (K : Type) (k : K) : 0 ≤ wtHalf K k := by
  unfold wtHalf
  norm_num

/-- **(S) The weights of the mean-free route**: the aggregated class weight of a label is twice
the paper's class weight `κ_b − var = diagW` of its type (`prop:joint-middle-mean`, the residual
table, aggregated at weight `1/2`; the effective weight per selection is `diagW`). It pins `wc`. -/
def WeightsHalf (D : CD blockOf) (cd : ClassData D.CL) (labK : K → PaperDiag)
    (wc : ∀ L, cd.ι L → K → ℝ) : Prop :=
  ∀ L k, ∑ i, wc L i k = 2 * diagW (labK k)

/-- **(S) The aggregated label prices at weight `1/2` are uniformly bounded by `Vv`.** -/
def PriceBoundHalf (D : CD blockOf) (cd : ClassData D.CL)
    (labS : ∀ L, Choice (D.CL.T L) → Option K) (Vv : ℝ) : Prop :=
  ∀ L k, agg (cd.sel L) (labS L) (wtHalf K) (monomial (D.CL.π L)) k ≤ Vv

/-- `PriceBoundHalf` is the bound `hvV` of `mdInputsNoMean` (`aggED … .v` is `agg π`). Stated in
this generic context, the identification is checked without evaluating the selections (as CM's
`Companion.PriceBound.toAggED`). -/
theorem PriceBoundHalf.toAggED {labS : ∀ L, Choice (D.CL.T L) → Option K} {Vv : ℝ}
    (Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ)
    (wc : ∀ L, cd.ι L → K → ℝ) (wc_nonneg : ∀ L i j, 0 ≤ wc L i j)
    (ρ : ∀ L, Choice (D.CL.T L) → ℝ)
    (ops : ClassStepsOps cd (fun _ => K)
      (fun L A => agg (cd.sel L) (labS L) (wtHalf K) (Zs L A)) wc ρ)
    (hup : SelUpper D cd labS (wtHalf K) Zs wc) (h : PriceBoundHalf D cd labS Vv) :
    ∀ L k, (aggED labS (wtHalf K) (wtHalf_nonneg K) Zs wc wc_nonneg ρ ops hup).v L k ≤ Vv := h

/-- `WeightsHalf` is the identification `hwH` of `mdInputsNoMean` (`aggED … .w` is `∑_i wc`),
checked in the generic context. -/
theorem WeightsHalf.toAggED {labS : ∀ L, Choice (D.CL.T L) → Option K} {labK : K → PaperDiag}
    (Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ)
    (wc : ∀ L, cd.ι L → K → ℝ) (wc_nonneg : ∀ L i j, 0 ≤ wc L i j)
    (ρ : ∀ L, Choice (D.CL.T L) → ℝ)
    (ops : ClassStepsOps cd (fun _ => K)
      (fun L A => agg (cd.sel L) (labS L) (wtHalf K) (Zs L A)) wc ρ)
    (hup : SelUpper D cd labS (wtHalf K) Zs wc) (h : WeightsHalf D cd labK wc) :
    ∀ L k, (aggED labS (wtHalf K) (wtHalf_nonneg K) Zs wc wc_nonneg ρ ops hup).w L k =
      2 * diagW (labK k) := h

/-- The bound `hwW` of `mdInputsNoMean` from the bound on `∑_i wc` (generic context). -/
theorem weightsBound_toAggED {labS : ∀ L, Choice (D.CL.T L) → Option K} {W : ℝ}
    (Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ)
    (wc : ∀ L, cd.ι L → K → ℝ) (wc_nonneg : ∀ L i j, 0 ≤ wc L i j)
    (ρ : ∀ L, Choice (D.CL.T L) → ℝ)
    (ops : ClassStepsOps cd (fun _ => K)
      (fun L A => agg (cd.sel L) (labS L) (wtHalf K) (Zs L A)) wc ρ)
    (hup : SelUpper D cd labS (wtHalf K) Zs wc) (h : ∀ L k, ∑ i, wc L i k ≤ W) :
    ∀ L k, (aggED labS (wtHalf K) (wtHalf_nonneg K) Zs wc wc_nonneg ρ ops hup).w L k ≤ W := h

/-- **The mean data without the middle mean credit** (`MDInputsE4B`; `prop:record:mean-credit`
with the one-block credit only, `cor:joint-closing`, `eq:final-joint-closing`): CM's
`mdInputsOfSel` with the aggregation weights `1/2`, every diagonal booked as `zeroDiag` (mean
coefficient `0`), `μ = 0`, the booked coefficient `R = 63 c`, and the evaluation
`seriesBound_noMean` at `δ = 63 τ + 64 Δ_mid ≤ 12/5` (`noMean_room`). *Inputs*: the labels'
paper types `labK` with `WeightsHalf`; the bounds `W`, `Vv`; `SelMean` at `μ = 0` (the one-block
credit) with `hZs`; the letters `ℓ`, the comparison coefficient `c ≥ 0`, the totals `X ≥ 0` with
`hX`; the comparison series `hC`, `hCv` with `τ ≤ 13/625 = 0.0208`; the residuals `r` with `hρ`;
`hcomp`. -/
noncomputable def mdInputsNoMean (labS : ∀ L, Choice (D.CL.T L) → Option K)
    (labK : K → PaperDiag) (Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ)
    (wc : ∀ L, cd.ι L → K → ℝ) (wc_nonneg : ∀ L i j, 0 ≤ wc L i j)
    (ρ : ∀ L, Choice (D.CL.T L) → ℝ)
    (ops : ClassStepsOps cd (fun _ => K)
      (fun L A => agg (cd.sel L) (labS L) (wtHalf K) (Zs L A)) wc ρ)
    (hup : SelUpper D cd labS (wtHalf K) Zs wc)
    (hwH : ∀ L k, (aggED labS (wtHalf K) (wtHalf_nonneg K) Zs wc wc_nonneg ρ ops hup).w L k =
      2 * diagW (labK k))
    (W Vv : ℝ) (hW0 : 0 ≤ W) (hVv : 0 ≤ Vv)
    (hwW : ∀ L k, (aggED labS (wtHalf K) (wtHalf_nonneg K) Zs wc wc_nonneg ρ ops hup).w L k ≤ W)
    (hvV : ∀ L k, (aggED labS (wtHalf K) (wtHalf_nonneg K) Zs wc wc_nonneg ρ ops hup).v L k ≤ Vv)
    (hZs : ∀ L A ω, 0 ≤ Zs L A ω)
    (hm : SelMean D cd (fun _ _ => 0) Zs)
    (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C) (c : (MLetter ⊕ C → ℕ) → ℝ) (hc0 : ∀ d, 0 ≤ c d)
    (X : MLetter ⊕ C → ℝ) (hX0 : ∀ l, 0 ≤ X l)
    (hX : TotalsLe D ℓ X)
    (Cv τ : ℝ) (hτ : τ ≤ 13 / 625)
    (hC : HasSum (fun d => c d * ∏ l, X l ^ d l / (d l).factorial) Cv)
    (hCv : Cv ≤ harnessE + τ)
    (r : ∀ L, Choice (D.CL.T L) → ℝ) (hρ : ResidualId D cd ρ r)
    (hcomp : CompId D cd labS labK ℓ c r) :
    MDInputsE4B (aggED labS (wtHalf K) (wtHalf_nonneg K) Zs wc wc_nonneg ρ ops hup) :=
  mdInputsOfSel labS (wtHalf K) (wtHalf_nonneg K) Zs wc wc_nonneg ρ ops hup (fun _ => zeroDiag)
    (fun L k => by
      rw [hwH L k]
      exact diagW_zeroDiag_le (labK k))
    W Vv hW0 hVv hwW hvV (fun _ _ => 0)
    (fun L ω _ => by
      rcases labS L ω with _ | k
      · exact le_rfl
      · simp only [coefOf, Option.elim_some, diagB_zeroDiag_real, zero_mul, le_refl])
    hZs hm (MLetter ⊕ C) ℓ (fun d => 63 * c d) (fun d => by linarith [hc0 d]) X hX r hρ
    (fun L ω hω => by
      have h1 := hcomp L ω hω
      rcases hl : labS L ω with _ | k
      · rw [hl] at h1
        simp only [coefOf, Option.elim, add_zero] at h1 ⊢
        split_ifs at h1 ⊢ <;> linarith
      · rw [hl] at h1
        simp only [coefOf, Option.elim, diagB_zeroDiag_real, sub_zero] at h1 ⊢
        rw [hwH L k]
        unfold wtHalf
        split_ifs at h1 ⊢ <;> linarith)
    (63 * τ + 64 * (ledgerMid : ℝ)) (noMean_room τ hτ)
    (seriesBound_noMean c X hX0 hc0 Cv τ hC hCv)

/-- **The class group without the middle mean credit** (`ClassPartsE4B`; `cor:joint-closing`):
CM's `classPartsOfCM` at the weights `1/2`, with `MD := mdInputsNoMean …` and `E1` given. -/
noncomputable def classPartsNoMean (labS : ∀ L, Choice (D.CL.T L) → Option K)
    (labK : K → PaperDiag) (Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ)
    (wc : ∀ L, cd.ι L → K → ℝ) (wc_nonneg : ∀ L i j, 0 ≤ wc L i j)
    (ρ : ∀ L, Choice (D.CL.T L) → ℝ)
    (ops : ClassStepsOps cd (fun _ => K)
      (fun L A => agg (cd.sel L) (labS L) (wtHalf K) (Zs L A)) wc ρ)
    (hup : SelUpper D cd labS (wtHalf K) Zs wc)
    (hwH : ∀ L k, (aggED labS (wtHalf K) (wtHalf_nonneg K) Zs wc wc_nonneg ρ ops hup).w L k =
      2 * diagW (labK k))
    (W Vv : ℝ) (hW0 : 0 ≤ W) (hVv : 0 ≤ Vv)
    (hwW : ∀ L k, (aggED labS (wtHalf K) (wtHalf_nonneg K) Zs wc wc_nonneg ρ ops hup).w L k ≤ W)
    (hvV : ∀ L k, (aggED labS (wtHalf K) (wtHalf_nonneg K) Zs wc wc_nonneg ρ ops hup).v L k ≤ Vv)
    (hZs : ∀ L A ω, 0 ≤ Zs L A ω)
    (hm : SelMean D cd (fun _ _ => 0) Zs)
    (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C) (c : (MLetter ⊕ C → ℕ) → ℝ) (hc0 : ∀ d, 0 ≤ c d)
    (X : MLetter ⊕ C → ℝ) (hX0 : ∀ l, 0 ≤ X l)
    (hX : TotalsLe D ℓ X)
    (Cv τ : ℝ) (hτ : τ ≤ 13 / 625)
    (hC : HasSum (fun d => c d * ∏ l, X l ^ d l / (d l).factorial) Cv)
    (hCv : Cv ≤ harnessE + τ)
    (r : ∀ L, Choice (D.CL.T L) → ℝ) (hρ : ResidualId D cd ρ r)
    (hcomp : CompId D cd labS labK ℓ c r)
    (E1 : E1InputsAgg D) : ClassPartsE4B D :=
  classPartsOfCM D cd K labS (wtHalf K) (wtHalf_nonneg K) Zs wc wc_nonneg ρ ops hup E1
    (mdInputsNoMean labS labK Zs wc wc_nonneg ρ ops hup hwH W Vv hW0 hVv hwW hvV hZs hm ℓ c hc0
      X hX0 hX Cv τ hτ hC hCv r hρ hcomp)

end Sarkozy.ClassSlack
