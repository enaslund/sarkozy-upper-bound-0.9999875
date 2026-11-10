module

public import Sarkozy.OpsVariance.Conjunct
public import Sarkozy.E1Closure.Main

@[expose] public section

/-!
# The variance conjunct at the data of the companion obligations

`paper/sections/22_variance.tex`, `prop:background-variance`(a), `lem:var-gain`(b);
`paper/sections/10_comparison_lemmas.tex`, (E1), `lem:bracket-energy`, "Fixed selections and summed
remainders" (ll. 126–140).

At the data `D = (F.X hB hRR).data` of `CompanionObligationsEC` (`main_goal_rebased_ec`):

* `envelopeBoundNonneg_ec`: (E1) for the envelope laws of **all** selections is proved (EC's
  `E1Sub`, `E1Coup`, `E1Rem` through F1P's `E1InputsAgg.toE1`). This is the same statement as
  OPS-S's `OpsSteps.envelopeBoundNonneg_front`, re-derived here from EC's lemmas so that this
  directory does not depend on files in progress;
* `hWZ_agg`: the diagonal part `∑_j wc_{v,j} agg_j(Z_s)` of a variance class is nonnegative, from
  the side conditions `wc ≥ 0`, `Z_s ≥ 0` of the obligations (`wc_nonneg`, `hZs`);
* **`varConjunct_front`**: the variance conjunct of `ClassStepsOps.H` (any class data `cd`, any
  choice `cr` of the credit classes), with (E1) **discharged**: there are `ε_E → 0`, `c_E ≥ 0` and
  remainders `r_E ≥ 0` with `∑_ω π̃_ω r_E(ω) ≤ c_E L^{-σ} α` such that the conjunct holds for every
  `z ≥ ε_E`, `K ≥ 3`, residuals `ρ` carrying the class costs and remainders `rr` dominating
  `π̃_ω r_E(ω)` (plus the credit remainders), given, on the credit classes only, the zero
  marginals, `hJN` and `hres` of `varConjunct`;
* **`varConjunct_noCredit_front`**: the same with no credit class: the conjunct is then **proved**
  outright, up to the shared choices `z`, `K`, `ρ`, `rr` (and `hWZ`).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.OpsVariance

open Sarkozy.E1Closure Sarkozy.SharpFirst Sarkozy.TheoremCBlock Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.EnvelopeInputs Sarkozy.DensityChain2 Sarkozy.CancellationSteps Sarkozy.BlockFrame
  Sarkozy.Functional Sarkozy.BlockAnchor
open Sarkozy.ClassInputsPaper Sarkozy.ClassBoundsPaper Sarkozy.TheoremC
  Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice Sarkozy.EnvelopeSteps
open Sarkozy.Param (Params)
open Sarkozy.CompanionND (CompanionFrontND)
open Sarkozy.UpperCapsPaper (UpperRecordTables)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.MeanCredit (agg)
open Sarkozy.ClassSlack (wtHalf wtHalf_nonneg)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {UpT : UpperRecordTables}

/-- **(E1) for the envelope laws of all selections at the obligations' data** (EC's `E1Sub`,
`E1Coup`, `E1Rem` at `ε_E = u_L` and the canonical remainders, through `E1InputsAgg.toE1`; the
paper-data facts of EC's `subS`, `coupS`, `large`). -/
theorem envelopeBoundNonneg_ec (F : CompanionFrontND hW hMR hFour UpT) (hB : Target.BMOR)
    (hRR : Target.ThetaSmallRR) : (F.X hB hRR).data.EnvelopeBoundNonneg := by
  obtain ⟨c₁, hc₁, h1⟩ := e1SubSmall_proved (F.X hB hRR).data paper_pairwise
    TargetLedger.targetDecay_nonneg
    (DensityChain2.parity_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
    (DensityChain2.hsel_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
    (ThetaOne.paperAtomMap_paperBlockOf_surjective f1Cell)
  obtain ⟨c₂, hc₂, h2⟩ := e1CoupSmall_proved (F.X hB hRR).data paper_pairwise
    TargetLedger.targetDecay_nonneg
    (DensityChain2.parity_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
    (DensityChain2.hsel_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
    (ThetaOne.paperAtomMap_paperBlockOf_surjective f1Cell)
  obtain ⟨c₃, hc₃, h3⟩ := e1Large_proved (F.X hB hRR).data TargetLedger.targetDecay_nonneg
  exact (Companion.E1InputsAgg.ofFields (F.X hB hRR).data (sfEps _) (sfEps_nonneg _)
    (tendsto_sfEps _) (c₁ + c₂ + c₃) (add_nonneg (add_nonneg hc₁ hc₂) hc₃) (r0X _ (sfEps _))
    (rX _ (sfEps _)) (e1Sub_r0X _ (sfEps _)) (e1Coup_rX _ (sfEps _))
    (e1RemX_of_split _ (sfEps_nonneg _) h1 h2 h3) (rX_nonneg _ (sfEps _))
    (r0X_nonneg _ (sfEps _))).toE1

/-- **The diagonal part of a class at the obligations' aggregated diagonals is nonnegative**:
`∑_j wc_{i,j} agg_j(Z_s) ≥ 0` from `wc ≥ 0` and `Z_s ≥ 0` (`agg` at the weights `1/2`). The field
`hWZ` of `VarStepsAt` at the data of `CompanionObligationsEC.ops`. -/
theorem hWZ_agg {σ K : Type} [Fintype K] [DecidableEq K] (S : Finset σ) (lab : σ → Option K)
    (Zs : σ → ℝ) (hZs : ∀ ω, 0 ≤ Zs ω) (w : K → ℝ) (hw : ∀ j, 0 ≤ w j) :
    0 ≤ ∑ j, w j * agg S lab (wtHalf K) Zs j :=
  sum_nonneg fun j _ => mul_nonneg (hw j)
    (sum_nonneg fun ω _ => mul_nonneg (wtHalf_nonneg K j) (hZs ω))

/-- **The variance conjunct of `ClassStepsOps.H` at the obligations' data, with (E1) discharged**
(`varConjunct` with `envelopeBoundNonneg_ec`). There are `ε_E ≥ 0`, `ε_E → 0`, `c_E ≥ 0` and
remainders `r_E ≥ 0` with `∑_ω π̃_ω r_E(ω) ≤ c_E L^{-σ} α` at every least counterexample, such that
for any class data `cd`, credit choice `cr`, and shared numbers `z ≥ ε_E`, `K ≥ 3`, the conjunct
holds given, on the credit classes, the zero marginals `hzm`, the comparison `hJN` and the
restoration `hres`, and, on all variance classes, the residuals `hρ`, the remainders `hrr` and
`hWZ`. -/
theorem varConjunct_front (F : CompanionFrontND hW hMR hFour UpT) (hB : Target.BMOR)
    (hRR : Target.ThetaSmallRR) :
    ∃ εE : ℕ → ℝ, (∀ L, 0 ≤ εE L) ∧ Tendsto εE atTop (𝓝 0) ∧ ∃ cE : ℝ, 0 ≤ cE ∧
    ∃ rE : ∀ L, Finset ℤ → Choice ((F.X hB hRR).data.CL.T L) → ℝ, (∀ L A ω, 0 ≤ rE L A ω) ∧
    Param.AtCounterexamples (Params.ofDecay TargetLedger.targetDecay) (F.X hB hRR).data.Y
      (fun L A => ∑ ω ∈ univ.filter (fun ω : Choice ((F.X hB hRR).data.CL.T L) => IsSelection ω),
        monomial ((F.X hB hRR).data.CL.πt L) ω * rE L A ω ≤ Comparison.remainder cE L A) ∧
    ∀ (cd : ClassData (F.X hB hRR).data.CL) {Θ : ℕ → Type} [∀ L, Fintype (Θ L)]
      (Z : ∀ L, Finset ℤ → Θ L → ℝ) (wc : ∀ L, cd.ι L → Θ L → ℝ)
      (ρ : ∀ L, Choice ((F.X hB hRR).data.CL.T L) → ℝ) (z : ℕ → ℝ) (K : ℝ)
      (rr : ∀ L, Finset ℤ → Choice ((F.X hB hRR).data.CL.T L) → ℝ),
      (∀ L, εE L ≤ z L) → (∀ L, 0 ≤ z L) → 3 ≤ K →
      ∀ (cr : ∀ L, cd.V L → Bool) (bt : ∀ L, cd.V L → ℝ) (Rstar : ℝ),
      (F.X hB hRR).data.GB.Rerr ≤ Rstar →
      ∀ (rJ : ∀ L, Finset ℤ → Choice ((F.X hB hRR).data.CL.T L) → ℝ)
        (r₀ : ∀ L, Finset ℤ → cd.V L → ℝ), (∀ L A v, 0 ≤ r₀ L A v) → (∀ L A ω, 0 ≤ rJ L A ω) →
      (∀ L (v : cd.V L), cr L v = true → ∀ ω ∈ cd.clsSel L (.inr v),
        RecordsZeroMarginal (F.X hB hRR).data L ω) →
      Param.AtCounterexamples (Params.ofDecay TargetLedger.targetDecay) (F.X hB hRR).data.Y
        (fun L A => ∀ v : cd.V L, cr L v = true → ∀ ω ∈ cd.clsSel L (.inr v),
          varJ0 (F.X hB hRR).data L A ω (envM (F.X hB hRR).data L ω) -
              ((F.X hB hRR).data.GB.Rerr + z L) * selProd (F.X hB hRR).data L ω *
                (F.X hB hRR).data.Y L A - rJ L A ω ≤
            varJ (F.X hB hRR).data L A ω (envM (F.X hB hRR).data L ω)) →
      Param.AtCounterexamples (Params.ofDecay TargetLedger.targetDecay) (F.X hB hRR).data.Y
        (fun L A => ∀ v : cd.V L, cr L v = true →
          (bt L v - z L) * (∑ ω ∈ cd.clsSel L (.inr v), monomial ((F.X hB hRR).data.CL.π L) ω) *
              (F.X hB hRR).data.Y L A - r₀ L A v ≤
            ∑ ω ∈ cd.clsSel L (.inr v), monomial ((F.X hB hRR).data.CL.πt L) ω *
              varJ0 (F.X hB hRR).data L A ω (envM (F.X hB hRR).data L ω)) →
      (∀ L (v : cd.V L), ∀ ω ∈ cd.clsSel L (.inr v),
        ((F.X hB hRR).data.B - (if cr L v then max 0 (bt L v - Rstar) else 0)) *
          monomial ((F.X hB hRR).data.CL.π L) ω ≤ ρ L ω) →
      (∀ L A (v : cd.V L),
        ∑ ω ∈ cd.clsSel L (.inr v), monomial ((F.X hB hRR).data.CL.πt L) ω *
            (rE L A ω + (if cr L v then rJ L A ω else 0)) +
          (if cr L v then r₀ L A v else 0) ≤ ∑ ω ∈ cd.clsSel L (.inr v), rr L A ω) →
      (∀ L A (v : cd.V L), 0 ≤ ∑ j, wc L (.inr v) j * Z L A j) →
      Param.AtCounterexamples (Params.ofDecay TargetLedger.targetDecay) (F.X hB hRR).data.Y
        fun L A => ∀ v : cd.V L,
          Nonempty (VarStepsAt (cd.clsSel L (.inr v)) (termAt (D := (F.X hB hRR).data) L A)
            (fun ω => monomial ((F.X hB hRR).data.CL.π L) ω) (ρ L) (rr L A)
            (∑ j, wc L (.inr v) j * Z L A j) ((F.X hB hRR).data.Y L A) (z L) K) := by
  obtain ⟨εE, hε0, hεt, cE, hcE, rE, hrE0, h1, h2⟩ := envelopeBoundNonneg_ec F hB hRR
  refine ⟨εE, hε0, hεt, cE, hcE, rE, hrE0, h2, ?_⟩
  intro cd Θ _ Z wc ρ z K rr hzE hz0 hK cr bt Rstar hRs rJ r₀ hr₀ hrJ hzm hJN hres hρ hrr hWZ
  exact varConjunct cd Z wc ρ z K rr h1 hzE hz0 hK cr bt Rstar hRs rJ r₀ hr₀ hrJ hzm hJN hres hρ
    hrr hWZ

/-- **The variance conjunct with no credit at the obligations' data: proved** up to the shared
choices. There are `ε_E ≥ 0`, `ε_E → 0`, `c_E ≥ 0` and remainders `r_E ≥ 0` with
`∑_ω π̃_ω r_E(ω) ≤ c_E L^{-σ} α`, such that for any class data `cd`, `z ≥ ε_E`, `K ≥ 3`, residuals
`ρ ≥ B π` on the variance classes and remainders with `∑_R π̃ r_E ≤ ∑_R rr`, the conjunct holds. -/
theorem varConjunct_noCredit_front (F : CompanionFrontND hW hMR hFour UpT) (hB : Target.BMOR)
    (hRR : Target.ThetaSmallRR) :
    ∃ εE : ℕ → ℝ, (∀ L, 0 ≤ εE L) ∧ Tendsto εE atTop (𝓝 0) ∧ ∃ cE : ℝ, 0 ≤ cE ∧
    ∃ rE : ∀ L, Finset ℤ → Choice ((F.X hB hRR).data.CL.T L) → ℝ, (∀ L A ω, 0 ≤ rE L A ω) ∧
    Param.AtCounterexamples (Params.ofDecay TargetLedger.targetDecay) (F.X hB hRR).data.Y
      (fun L A => ∑ ω ∈ univ.filter (fun ω : Choice ((F.X hB hRR).data.CL.T L) => IsSelection ω),
        monomial ((F.X hB hRR).data.CL.πt L) ω * rE L A ω ≤ Comparison.remainder cE L A) ∧
    ∀ (cd : ClassData (F.X hB hRR).data.CL) {Θ : ℕ → Type} [∀ L, Fintype (Θ L)]
      (Z : ∀ L, Finset ℤ → Θ L → ℝ) (wc : ∀ L, cd.ι L → Θ L → ℝ)
      (ρ : ∀ L, Choice ((F.X hB hRR).data.CL.T L) → ℝ) (z : ℕ → ℝ) (K : ℝ)
      (rr : ∀ L, Finset ℤ → Choice ((F.X hB hRR).data.CL.T L) → ℝ),
      (∀ L, εE L ≤ z L) → (∀ L, 0 ≤ z L) → 3 ≤ K →
      (∀ L (v : cd.V L), ∀ ω ∈ cd.clsSel L (.inr v),
        (F.X hB hRR).data.B * monomial ((F.X hB hRR).data.CL.π L) ω ≤ ρ L ω) →
      (∀ L A (v : cd.V L), ∑ ω ∈ cd.clsSel L (.inr v),
          monomial ((F.X hB hRR).data.CL.πt L) ω * rE L A ω ≤
        ∑ ω ∈ cd.clsSel L (.inr v), rr L A ω) →
      (∀ L A (v : cd.V L), 0 ≤ ∑ j, wc L (.inr v) j * Z L A j) →
      Param.AtCounterexamples (Params.ofDecay TargetLedger.targetDecay) (F.X hB hRR).data.Y
        fun L A => ∀ v : cd.V L,
          Nonempty (VarStepsAt (cd.clsSel L (.inr v)) (termAt (D := (F.X hB hRR).data) L A)
            (fun ω => monomial ((F.X hB hRR).data.CL.π L) ω) (ρ L) (rr L A)
            (∑ j, wc L (.inr v) j * Z L A j) ((F.X hB hRR).data.Y L A) (z L) K) := by
  obtain ⟨εE, hε0, hεt, cE, hcE, rE, hrE0, h1, h2⟩ := envelopeBoundNonneg_ec F hB hRR
  refine ⟨εE, hε0, hεt, cE, hcE, rE, hrE0, h2, ?_⟩
  intro cd Θ _ Z wc ρ z K rr hzE hz0 hK hρ hrr hWZ
  exact varConjunct_noCredit cd Z wc ρ z K rr h1 hzE hz0 hK hρ hrr hWZ

end Sarkozy.OpsVariance
