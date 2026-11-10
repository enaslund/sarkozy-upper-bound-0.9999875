module

public import Sarkozy.MeanCredit.Alloc
public import Sarkozy.MainFinalF1b.ClassesE4B

@[expose] public section

/-!
# Constructors of the class group of `main_goal_theta1k` from selection-level inputs

`paper/sections/24a_joint_mean.tex`, `prop:joint-middle-mean` (families (i)–(iv), the residual
table, the completion), `prop:joint-upper-mean`; `paper/sections/24_matching_mean.tex`,
`prop:record:mean-credit`; `paper/sections/11_comparison_proof.tex`, `cor:joint-closing`;
`paper/sections/32_four_routes_closing.tex`, `eq:final-joint-closing`.

The class group `MainFinalF1b.ClassPartsE4B` (field `Cls` of `MainCombined2.main_goal_theta1k`)
indexes the joint allocation by labelled diagonals `Θ_L` with free energies `Z`, prices `u`, the
mean field `MD.mean` (#22) and the combined gate `MD.alloc : AllocJB` (#33). Here the labelled
diagonals are **aggregated from per-selection diagonals** (`MeanCredit.agg`): a label set `K`
(finite, e.g. `PaperDiag`, or `PaperDiag × families`), a label `labS ω` of each selection, weights
`wt` (exact: `wtOf`; for the family-(i) part of the `F²` labels: `wtP`), the per-selection diagonal
energies `Zs`. Then:

* **`ESInputsE4B.ofAgg`**: the class energies with `Θ_L := K`, `Z := agg Zs`, `u := agg π_ω`
  (the aggregated monomials); `upper` from the per-selection upper prices `SelUpper`
  (**`upper_of_sel`**). `ops` stays an input (for the aggregated data).
* **`mean_of_sel`**: `MD.mean` (#22) from the selection-level mean `SelMean` (the retained
  positive terms of the mean expansion with per-selection coefficients `μ_ω`), when
  `diagB(lab) · wt ≤ μ_ω`. With `wtP`, the `F²` part of this is family (i)'s `4/(H_*² C(j+2,2))`
  per pair (`familyI_coef`): **the labelling aggregation is chosen consistently with family (i)**.
* **`alloc_of_sel`**: `MD.alloc` (#33) from the per-selection booking at the formal objects
  (`hbook_of_form`, `u` is the aggregated monomial by definition), the completion (proved), the
  upper-free evaluation `SeriesBound` and the kernel room `upperFree_room`.
* **`mdInputsOfSel`**, **`classPartsOfCM`**: the constructors into `MDInputsE4B` and
  `ClassPartsE4B`; `hcard` (`N = |K|`) and `hv0` are proved; **`jointBound_ofCM`**: `JB`.
* `selMean_of_mean`: the reduction of #22 is lossless at `μ = diagB · wt`.

The remaining inputs are exactly: `ops` (B11's steps for the aggregated data), `SelUpper`,
`SelMean` with `hμ`, `hZs` (or the inputs of `MeanAlloc.selMean_of_allocation`), `hw`, `hwW`,
`hvV`, `E1`, and for the gate the letters `ℓ`, the per-selection residual coefficients `r`, `hρ`,
`hRc`, the totals `hX`, `R ≥ 0` and the evaluation `SeriesBound` (or the inputs of
`Evaluation.seriesBound_ledger`).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MeanCredit

open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper Sarkozy.ClassData Sarkozy.MainFinal2
open Sarkozy.MainFinalF1b
open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.JointClosing
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.Comparison (remainder energyMean)
open Sarkozy.BlockFrame
open Sarkozy.Param (Params)
open Sarkozy.PartVLaws (paperAtomMap)
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.GramBracketPaper

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

/-- The comparison data of the class group of `main_goal_theta1k`. -/
abbrev CD (blockOf : PaperJ0 → B) : Type 1 :=
  TheoremCBlock.ComparisonData targetDecay paperM0 (paperAtomMap blockOf) paperTail paperPr
    paperH Chamber

/-- **The per-selection upper prices** (`lem:bracket-energy` for the diagonal of each labelled
selection, relative form): `Z_ω ≤ (π_ω + ε₃ π_ω) Y + r_ω`, with the remainders summed against the
labelled class weights. *Hypothesis* (analytic). -/
def SelUpper (D : CD blockOf) (cd : ClassData D.CL) {K : Type} [Fintype K]
    (labS : ∀ L, Choice (D.CL.T L) → Option K) (wt : K → ℝ)
    (Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ) (wc : ∀ L, cd.ι L → K → ℝ) : Prop :=
  ∃ ε₃ : ℕ → ℝ, (∀ L, 0 ≤ ε₃ L) ∧ Tendsto ε₃ atTop (𝓝 0) ∧ ∃ c₃ : ℝ, 0 ≤ c₃ ∧
    ∃ rs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ, (∀ L A ω, 0 ≤ rs L A ω) ∧
    Param.AtCounterexamples (Params.ofDecay targetDecay) D.Y (fun L A =>
      ∀ ω ∈ cd.sel L, labS L ω ≠ none →
        Zs L A ω ≤ (monomial (D.CL.π L) ω + ε₃ L * monomial (D.CL.π L) ω) * D.Y L A + rs L A ω) ∧
    Param.AtCounterexamples (Params.ofDecay targetDecay) D.Y (fun L A =>
      ∑ ω ∈ cd.sel L, coefOf (fun j => ∑ i, wc L i j) wt (labS L ω) * rs L A ω ≤
        remainder c₃ L A)

/-- **The selection-level mean** (`prop:record:mean-credit` Steps 1–3 with the one-block credits
`m₁`, and `prop:joint-middle-mean` families (i)–(iv) at energy level): the mean energies retain
`∑_ω μ_ω Z_ω` besides `(m₁ − o(1)) Y`, with the per-selection mean coefficients `μ_ω`
(family (i): `4/(H_*² C(n,2))` per selected fold pair). *Hypothesis* (analytic). -/
def SelMean (D : CD blockOf) (cd : ClassData D.CL) (μ : ∀ L, Choice (D.CL.T L) → ℝ)
    (Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ) : Prop :=
  ∃ ε₂ : ℕ → ℝ, Tendsto ε₂ atTop (𝓝 0) ∧ ∃ c₂ : ℝ, 0 ≤ c₂ ∧
    Param.AtCounterexamples (Params.ofDecay targetDecay) D.Y fun L A =>
      (targetLedger.m₁ - ε₂ L) * D.Y L A + ∑ ω ∈ cd.sel L, μ L ω * Zs L A ω -
          remainder c₂ L A ≤
        (energyMean (blockLift paperM0 (paperAtomMap blockOf) paperTail) D.ME.ML L A +
          energyMean (blockLift paperM0 (paperAtomMap blockOf) paperTail) D.ME.MR L A) / 2

section Agg

variable {D : CD blockOf} {cd : ClassData D.CL} {K : Type} [Fintype K] [DecidableEq K]

/-- **The aggregated upper prices** (`lem:bracket-energy`): `SelUpper` gives `upper` for the
aggregated diagonals `Z := agg Zs`, `u := agg π_ω`, with remainders `agg r_ω`. -/
theorem upper_of_sel (labS : ∀ L, Choice (D.CL.T L) → Option K) (wt : K → ℝ)
    (hwt : ∀ j, 0 ≤ wt j) (Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ)
    (wc : ∀ L, cd.ι L → K → ℝ) (hup : SelUpper D cd labS wt Zs wc) :
    ∃ ε₃ : ℕ → ℝ, (∀ L, 0 ≤ ε₃ L) ∧ Tendsto ε₃ atTop (𝓝 0) ∧ ∃ c₃ : ℝ, 0 ≤ c₃ ∧
    ∃ r : ℕ → Finset ℤ → K → ℝ, (∀ L A j, 0 ≤ r L A j) ∧
    Param.AtCounterexamples (Params.ofDecay targetDecay) D.Y (fun L A =>
      ∀ j, agg (cd.sel L) (labS L) wt (Zs L A) j ≤
        (agg (cd.sel L) (labS L) wt (monomial (D.CL.π L)) j +
          ε₃ L * agg (cd.sel L) (labS L) wt (monomial (D.CL.π L)) j) * D.Y L A + r L A j) ∧
    Param.AtCounterexamples (Params.ofDecay targetDecay) D.Y (fun L A =>
      ∑ j, (∑ i, wc L i j) * r L A j ≤ remainder c₃ L A) := by
  obtain ⟨ε₃, hε0, hε, c₃, hc₃, rs, hrs0, h1, h2⟩ := hup
  refine ⟨ε₃, hε0, hε, c₃, hc₃, fun L A => agg (cd.sel L) (labS L) wt (rs L A),
    fun L A j => agg_nonneg _ _ hwt (fun ω _ => hrs0 L A ω) j, ?_, ?_⟩
  · filter_upwards [h1] with L hL
    intro C hC hind A hA hcount j
    have h := hL C hC hind A hA hcount
    have hle := agg_le_agg (cd.sel L) (labS L) hwt h j
    have e : agg (cd.sel L) (labS L) wt (fun ω => (monomial (D.CL.π L) ω +
          ε₃ L * monomial (D.CL.π L) ω) * D.Y L A + rs L A ω) j =
        (agg (cd.sel L) (labS L) wt (monomial (D.CL.π L)) j +
          ε₃ L * agg (cd.sel L) (labS L) wt (monomial (D.CL.π L)) j) * D.Y L A +
          agg (cd.sel L) (labS L) wt (rs L A) j := by
      unfold agg
      rw [mul_sum, ← sum_add_distrib, sum_mul, ← sum_add_distrib]
      exact sum_congr rfl fun ω _ => by ring
    rw [e] at hle
    exact hle
  · filter_upwards [h2] with L hL
    intro C hC hind A hA hcount
    rw [sum_mul_agg]
    exact hL C hC hind A hA hcount

/-- **The class energies with aggregated labelled diagonals**: `Θ_L := K`, `Z := agg Zs`,
`u := agg π_ω`; `upper` from `SelUpper` (`upper_of_sel`). *Inputs*: `ops` (B11's steps for the
aggregated data), `SelUpper`. -/
noncomputable def ESInputsE4B.ofAgg (cd : ClassData D.CL) (K : Type) [Fintype K] [DecidableEq K]
    (labS : ∀ L, Choice (D.CL.T L) → Option K) (wt : K → ℝ) (hwt : ∀ j, 0 ≤ wt j)
    (Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ)
    (wc : ∀ L, cd.ι L → K → ℝ) (wc_nonneg : ∀ L i j, 0 ≤ wc L i j)
    (ρ : ∀ L, Choice (D.CL.T L) → ℝ)
    (ops : ClassStepsOps cd (fun _ => K) (fun L A => agg (cd.sel L) (labS L) wt (Zs L A)) wc ρ)
    (hup : SelUpper D cd labS wt Zs wc) : ESInputsE4B D cd where
  Θ _ := K
  Z L A := agg (cd.sel L) (labS L) wt (Zs L A)
  u L := agg (cd.sel L) (labS L) wt (monomial (D.CL.π L))
  wc := wc
  wc_nonneg := wc_nonneg
  ρ := ρ
  ops := ops
  upper := upper_of_sel labS wt hwt Zs wc hup

variable (labS : ∀ L, Choice (D.CL.T L) → Option K) (wt : K → ℝ) (hwt : ∀ j, 0 ≤ wt j)
  (Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ)
  (wc : ∀ L, cd.ι L → K → ℝ) (wc_nonneg : ∀ L i j, 0 ≤ wc L i j)
  (ρ : ∀ L, Choice (D.CL.T L) → ℝ)
  (ops : ClassStepsOps cd (fun _ => K) (fun L A => agg (cd.sel L) (labS L) wt (Zs L A)) wc ρ)
  (hup : SelUpper D cd labS wt Zs wc)

/-- The class energies of `ESInputsE4B.ofAgg`. -/
noncomputable abbrev aggED : ClassEnergyDataB D cd :=
  (ESInputsE4B.ofAgg cd K labS wt hwt Zs wc wc_nonneg ρ ops hup).toED

local notation "ED₀" => aggED labS wt hwt Zs wc wc_nonneg ρ ops hup

/-- **`MD.mean` (#22) from the selection-level mean** (`prop:record:mean-credit`,
`prop:joint-middle-mean`): if every labelled selection's coefficient `diagB(labK j) · wt_j` is at
most its retained mean coefficient `μ_ω`, and the selection diagonals are nonnegative, `SelMean`
gives the mean field for the aggregated diagonals, labelled by `labK`. -/
theorem mean_of_sel (labK : K → PaperDiag) (μ : ∀ L, Choice (D.CL.T L) → ℝ)
    (hμ : ∀ L, ∀ ω ∈ cd.sel L, coefOf (fun j => (diagB (labK j) : ℝ)) wt (labS L ω) ≤ μ L ω)
    (hZs : ∀ L A ω, 0 ≤ Zs L A ω) (hm : SelMean D cd μ Zs) :
    ∃ ε₂ : ℕ → ℝ, Tendsto ε₂ atTop (𝓝 0) ∧ ∃ c₂ : ℝ, 0 ≤ c₂ ∧
      Param.AtCounterexamples (Params.ofDecay targetDecay) D.Y fun L A =>
        (targetLedger.m₁ - ε₂ L) * D.Y L A +
            ∑ j, (diagB (labK j) : ℝ) *
              (ED₀).Z L A j -
            remainder c₂ L A ≤
          (energyMean (blockLift paperM0 (paperAtomMap blockOf) paperTail) D.ME.ML L A +
            energyMean (blockLift paperM0 (paperAtomMap blockOf) paperTail) D.ME.MR L A) / 2 := by
  obtain ⟨ε₂, hε, c₂, hc₂, h⟩ := hm
  refine ⟨ε₂, hε, c₂, hc₂, ?_⟩
  filter_upwards [h] with L hL
  intro C hC hind A hA hcount
  have h1 := hL C hC hind A hA hcount
  have e : ∑ j, (diagB (labK j) : ℝ) *
      (ED₀).Z L A j =
      ∑ ω ∈ cd.sel L, coefOf (fun j => (diagB (labK j) : ℝ)) wt (labS L ω) * Zs L A ω :=
    sum_mul_agg (cd.sel L) (labS L) wt (fun j => (diagB (labK j) : ℝ)) (Zs L A)
  have h2 : ∑ ω ∈ cd.sel L, coefOf (fun j => (diagB (labK j) : ℝ)) wt (labS L ω) * Zs L A ω ≤
      ∑ ω ∈ cd.sel L, μ L ω * Zs L A ω :=
    sum_le_sum fun ω hω => mul_le_mul_of_nonneg_right (hμ L ω hω) (hZs L A ω)
  rw [e]
  linarith

/-- **`SelMean` is no stronger than the formal mean field** (non-vacuity of the reduction of #22):
the mean field for the aggregated diagonals gives `SelMean` with `μ_ω := diagB(labK) · wt` on the
labelled selections (`0` on the others). So `mean_of_sel` at this `μ` is an equivalence, and a
larger `μ` (the paper's family coefficients) only strengthens the input. -/
theorem selMean_of_mean (labK : K → PaperDiag)
    (hm : ∃ ε₂ : ℕ → ℝ, Tendsto ε₂ atTop (𝓝 0) ∧ ∃ c₂ : ℝ, 0 ≤ c₂ ∧
      Param.AtCounterexamples (Params.ofDecay targetDecay) D.Y fun L A =>
        (targetLedger.m₁ - ε₂ L) * D.Y L A + ∑ j, (diagB (labK j) : ℝ) * (ED₀).Z L A j -
            remainder c₂ L A ≤
          (energyMean (blockLift paperM0 (paperAtomMap blockOf) paperTail) D.ME.ML L A +
            energyMean (blockLift paperM0 (paperAtomMap blockOf) paperTail) D.ME.MR L A) / 2) :
    SelMean D cd (fun L ω => coefOf (fun j => (diagB (labK j) : ℝ)) wt (labS L ω)) Zs := by
  obtain ⟨ε₂, hε, c₂, hc₂, h⟩ := hm
  refine ⟨ε₂, hε, c₂, hc₂, ?_⟩
  filter_upwards [h] with L hL
  intro C hC hind A hA hcount
  have h1 := hL C hC hind A hA hcount
  have e : ∑ j, (diagB (labK j) : ℝ) * (ED₀).Z L A j =
      ∑ ω ∈ cd.sel L, coefOf (fun j => (diagB (labK j) : ℝ)) wt (labS L ω) * Zs L A ω :=
    sum_mul_agg (cd.sel L) (labS L) wt (fun j => (diagB (labK j) : ℝ)) (Zs L A)
  rw [e] at h1
  exact h1

/-- **`MD.alloc` (#33) from the per-selection booking and the upper-free evaluation**
(`cor:joint-closing`, `prop:joint-middle-mean`, `eq:final-joint-closing`): `hbook_of_form` at the
formal objects (the aggregated prices are the `hu` of the booking by definition),
`completion_le`, `SeriesBound` at `M = 63 𝓔_h − 64 Δ_mid^{ledger} + δ`, `upperFree_room`. -/
theorem alloc_of_sel (labK : K → PaperDiag)
    (hw : ∀ L j, (diagW (labK j) : ℝ) ≤
      (ED₀).w L j)
    (Λ : Type) [Fintype Λ] [DecidableEq Λ] (ℓ : ∀ L, Entry (D.CL.T L) → Λ)
    (R : (Λ → ℕ) → ℝ) (hR0 : ∀ d, 0 ≤ R d) (X : Λ → ℝ)
    (hX : ∀ L l, letterTotal (ℓ L) (D.CL.π L) l ≤ X l)
    (r : ∀ L, Choice (D.CL.T L) → ℝ)
    (hρ : ∀ L, ∀ ω ∈ cd.sel L, cd.cls L ω ≠ none → ρ L ω ≤ r L ω * monomial (D.CL.π L) ω)
    (hRc : ∀ L, ∀ ω ∈ cd.sel L, (if cd.cls L ω = none then 63 * D.B else 63 * r L ω) +
      coefOf (fun j => 63 * (ED₀).w L j - (diagB (labK j) : ℝ)) wt (labS L ω) ≤ R (deg (ℓ L) ω))
    (δ : ℝ) (hδ : δ ≤ 12 / 5)
    (hser : SeriesBound R X (63 * (harnessE : ℝ) - 64 * (ledgerMid : ℝ) + δ)) :
    AllocJB (ED₀) fun _ j => (diagB (labK j) : ℝ) := by
  have hres : ∀ L (j : K), 0 ≤ 63 * (ED₀).w L j - (diagB (labK j) : ℝ) := by
    intro L j
    have h1 : ((diagB (labK j) + 2366 / 100 : ℚ) : ℝ) < ((63 * diagW (labK j) : ℚ) : ℝ) := by
      exact_mod_cast diag_resid (labK j)
    push_cast at h1
    linarith [hw L j]
  refine allocJB_of_booking_upperFree
    ED₀ (fun _ j => (diagB (labK j) : ℝ)) Λ R X δ hδ hR0 hser
    fun L => ?_
  letI : DecidableEq ((ED₀).Θ L) := inferInstanceAs (DecidableEq K)
  exact
    { J' := _
      T' := D.CL.T L
      π' := D.CL.π L
      π'_nonneg := cd.π_nonneg L
      ℓ := ℓ L
      S := cd.sel L
      hX := hX L
      hbook := hbook_of_form ED₀ (fun _ j => (diagB (labK j) : ℝ)) L (ℓ L) R (labS L) wt (r L)
        (hres L) (fun _ => le_rfl) (hρ L) (hRc L) }

/-! ## The constructors into the class group -/

/-- **The mean data of the class group from the selection-level inputs** (`MDInputsE4B` at the
aggregated class energies): `lab := labK`, `N := |K|` (`hcard` by `rfl`), `hv0` proved (the
aggregated monomials are nonnegative), `mean` by `mean_of_sel` (#22), `alloc` by `alloc_of_sel`
(#33). *Inputs*: `hw`, `W`, `Vv` with `hwW`, `hvV`; `SelMean` with `hμ`, `hZs`; the booking
(`ℓ`, `R ≥ 0`, `X`, `hX`, `r`, `hρ`, `hRc`) and the evaluation `SeriesBound`. -/
noncomputable def mdInputsOfSel (labK : K → PaperDiag)
    (hw : ∀ L j, (diagW (labK j) : ℝ) ≤ (ED₀).w L j)
    (W Vv : ℝ) (hW0 : 0 ≤ W) (hVv : 0 ≤ Vv) (hwW : ∀ L j, (ED₀).w L j ≤ W)
    (hvV : ∀ L j, (ED₀).v L j ≤ Vv)
    (μ : ∀ L, Choice (D.CL.T L) → ℝ)
    (hμ : ∀ L, ∀ ω ∈ cd.sel L, coefOf (fun j => (diagB (labK j) : ℝ)) wt (labS L ω) ≤ μ L ω)
    (hZs : ∀ L A ω, 0 ≤ Zs L A ω) (hm : SelMean D cd μ Zs)
    (Λ : Type) [Fintype Λ] [DecidableEq Λ] (ℓ : ∀ L, Entry (D.CL.T L) → Λ)
    (R : (Λ → ℕ) → ℝ) (hR0 : ∀ d, 0 ≤ R d) (X : Λ → ℝ)
    (hX : ∀ L l, letterTotal (ℓ L) (D.CL.π L) l ≤ X l)
    (r : ∀ L, Choice (D.CL.T L) → ℝ)
    (hρ : ∀ L, ∀ ω ∈ cd.sel L, cd.cls L ω ≠ none → ρ L ω ≤ r L ω * monomial (D.CL.π L) ω)
    (hRc : ∀ L, ∀ ω ∈ cd.sel L, (if cd.cls L ω = none then 63 * D.B else 63 * r L ω) +
      coefOf (fun j => 63 * (ED₀).w L j - (diagB (labK j) : ℝ)) wt (labS L ω) ≤ R (deg (ℓ L) ω))
    (δ : ℝ) (hδ : δ ≤ 12 / 5)
    (hser : SeriesBound R X (63 * (harnessE : ℝ) - 64 * (ledgerMid : ℝ) + δ)) :
    MDInputsE4B (ED₀) where
  lab _ := labK
  hw := hw
  N := Fintype.card K
  W := W
  Vv := Vv
  hW0 := hW0
  hVv := hVv
  hcard _ := le_rfl
  hwW := hwW
  hv0 L j := agg_nonneg _ _ hwt (fun ω _ => monomial_nonneg (cd.π_nonneg L) ω) j
  hvV := hvV
  mean := mean_of_sel labS wt hwt Zs wc wc_nonneg ρ ops hup labK μ hμ hZs hm
  alloc := alloc_of_sel labS wt hwt Zs wc wc_nonneg ρ ops hup labK hw Λ ℓ R hR0 X hX r hρ hRc δ hδ
    hser

end Agg

/-- **The class group of `main_goal_theta1k` from the selection-level inputs**
(`MainFinalF1b.ClassPartsE4B`): `ES := ESInputsE4B.ofAgg …`, `MD` from `mdInputsOfSel`, `E1` given.
`ClassPartsE4B.jointBound` then gives `JB` (`cor:joint-closing`). -/
noncomputable def classPartsOfCM (D : CD blockOf) (cd : ClassData D.CL) (K : Type) [Fintype K]
    [DecidableEq K] (labS : ∀ L, Choice (D.CL.T L) → Option K) (wt : K → ℝ) (hwt : ∀ j, 0 ≤ wt j)
    (Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ)
    (wc : ∀ L, cd.ι L → K → ℝ) (wc_nonneg : ∀ L i j, 0 ≤ wc L i j)
    (ρ : ∀ L, Choice (D.CL.T L) → ℝ)
    (ops : ClassStepsOps cd (fun _ => K) (fun L A => agg (cd.sel L) (labS L) wt (Zs L A)) wc ρ)
    (hup : SelUpper D cd labS wt Zs wc) (E1 : E1InputsAgg D)
    (MD : MDInputsE4B (aggED labS wt hwt Zs wc wc_nonneg ρ ops hup)) : ClassPartsE4B D where
  cd := cd
  ES := ESInputsE4B.ofAgg cd K labS wt hwt Zs wc wc_nonneg ρ ops hup
  E1 := E1
  MD := MD

/-- **`JB` on the CM route** (`cor:joint-closing`, `eq:final-joint-closing`): the joint bound of
`main_goal_theta1k`'s class group from `classPartsOfCM` (`ClassPartsE4B.jointBound`). -/
theorem jointBound_ofCM (D : CD blockOf) (cd : ClassData D.CL) (K : Type) [Fintype K]
    [DecidableEq K] (labS : ∀ L, Choice (D.CL.T L) → Option K) (wt : K → ℝ) (hwt : ∀ j, 0 ≤ wt j)
    (Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ)
    (wc : ∀ L, cd.ι L → K → ℝ) (wc_nonneg : ∀ L i j, 0 ≤ wc L i j)
    (ρ : ∀ L, Choice (D.CL.T L) → ℝ)
    (ops : ClassStepsOps cd (fun _ => K) (fun L A => agg (cd.sel L) (labS L) wt (Zs L A)) wc ρ)
    (hup : SelUpper D cd labS wt Zs wc) (E1 : E1InputsAgg D)
    (MD : MDInputsE4B (aggED labS wt hwt Zs wc wc_nonneg ρ ops hup)) :
    JointBound D targetLedger.jointConstant :=
  (classPartsOfCM D cd K labS wt hwt Zs wc wc_nonneg ρ ops hup E1 MD).jointBound

end Sarkozy.MeanCredit
