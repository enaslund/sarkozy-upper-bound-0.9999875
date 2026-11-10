module

public import Sarkozy.OpsVariance.Front

@[expose] public section

/-!
# The variance conjunct at any diagonal budget and at `ρ = r π`

`paper/sections/22_variance.tex`, `prop:background-variance`(a), `lem:var-gain`(b).

`VarStepsAt` sees the diagonal budget `WZ` only through `0 ≤ WZ`, and the residuals only through
`hρ`. OPS-L's canonical data put `WZ = 0` and `ρ = r π` on the variance classes (`OpsCore`,
`OpsInputs`). This file states the variance conjunct for **any** budget `WZ ≥ 0` (`varConjunctW`,
at the obligations' data `varConjunctW_front`), and turns a lower bound on the residual coefficient
`r_ω` into `hρ` at `ρ = r π` (`hρ_of_coeff`). On a no-credit class the condition is `B ≤ r_ω`, on
a credit class `B − [b̃ − R_*]_+ ≤ r_ω` (the class cost of `cor:variance:final`(i)).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.OpsVariance

open Sarkozy.ClassInputsPaper Sarkozy.ClassBoundsPaper Sarkozy.TheoremC Sarkozy.TheoremCBlock
  Sarkozy.BlockFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice Sarkozy.EnvelopeSteps
  Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame
open Sarkozy.Param (Params)
open Sarkozy.CompanionND (CompanionFrontND)
open Sarkozy.UpperCapsPaper (UpperRecordTables)

section Generic

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}

omit [DecidableEq P] in
/-- **`hρ` at `ρ = r π`** from a lower bound `c ≤ r_ω` on the class (the field `hρ` of
`varStepsAt_noCredit` with `c = B`, of `varStepsAt_credit` with `c = B − [b̃ − R_*]_+`). -/
theorem hρ_of_coeff {L : ℕ} (R : Finset (Choice (D.CL.T L))) (r : Choice (D.CL.T L) → ℝ) {c : ℝ}
    (hr : ∀ ω ∈ R, c ≤ r ω) :
    ∀ ω ∈ R, c * monomial (D.CL.π L) ω ≤ r ω * monomial (D.CL.π L) ω := fun ω hω =>
  mul_le_mul_of_nonneg_right (hr ω hω) (monomial_π_nonneg L ω)

omit [DecidableEq P] in
/-- **The variance conjunct of `ClassStepsOps.H` at any diagonal budget `WZ ≥ 0`** (`varConjunct`
with the budget `WZ L A v` in place of `∑_j wc_{v,j} Z_j`; e.g. OPS-L's `WZ = 0`). -/
theorem varConjunctW (cd : ClassData D.CL) (WZ : ∀ L, Finset ℤ → cd.V L → ℝ)
    (ρ : ∀ L, Choice (D.CL.T L) → ℝ) (z : ℕ → ℝ) (K : ℝ)
    (rr : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ)
    {εE : ℕ → ℝ} {rE : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ}
    (hE : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ ω : Choice (D.CL.T L), IsSelection ω →
        envEnergy D L A ω ≤ (D.B + εE L) * selProd D L ω * D.Y L A + rE L A ω))
    (hzE : ∀ L, εE L ≤ z L) (hz0 : ∀ L, 0 ≤ z L) (hK : 3 ≤ K)
    (cr : ∀ L, cd.V L → Bool) (bt : ∀ L, cd.V L → ℝ) (Rstar : ℝ) (hRs : D.GB.Rerr ≤ Rstar)
    (rJ : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ) (r₀ : ∀ L, Finset ℤ → cd.V L → ℝ)
    (hr₀ : ∀ L A v, 0 ≤ r₀ L A v) (hrJ : ∀ L A ω, 0 ≤ rJ L A ω)
    (hzm : ∀ L (v : cd.V L), cr L v = true → ∀ ω ∈ cd.clsSel L (.inr v),
      RecordsZeroMarginal D L ω)
    (hJN : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ v : cd.V L,
      cr L v = true → ∀ ω ∈ cd.clsSel L (.inr v),
        varJ0 D L A ω (envM D L ω) - (D.GB.Rerr + z L) * selProd D L ω * D.Y L A - rJ L A ω ≤
          varJ D L A ω (envM D L ω)))
    (hres : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ v : cd.V L,
      cr L v = true →
        (bt L v - z L) * (∑ ω ∈ cd.clsSel L (.inr v), monomial (D.CL.π L) ω) * D.Y L A -
            r₀ L A v ≤
          ∑ ω ∈ cd.clsSel L (.inr v), monomial (D.CL.πt L) ω * varJ0 D L A ω (envM D L ω)))
    (hρ : ∀ L (v : cd.V L), ∀ ω ∈ cd.clsSel L (.inr v),
      (D.B - (if cr L v then max 0 (bt L v - Rstar) else 0)) * monomial (D.CL.π L) ω ≤ ρ L ω)
    (hrr : ∀ L A (v : cd.V L),
      ∑ ω ∈ cd.clsSel L (.inr v),
          monomial (D.CL.πt L) ω * (rE L A ω + (if cr L v then rJ L A ω else 0)) +
        (if cr L v then r₀ L A v else 0) ≤ ∑ ω ∈ cd.clsSel L (.inr v), rr L A ω)
    (hWZ : ∀ L A (v : cd.V L), 0 ≤ WZ L A v) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A => ∀ v : cd.V L,
      Nonempty (VarStepsAt (cd.clsSel L (.inr v)) (termAt (D := D) L A)
        (fun ω => monomial (D.CL.π L) ω) (ρ L) (rr L A) (WZ L A v) (D.Y L A) (z L) K) := by
  filter_upwards [hE, hJN, hres] with L hEL hJNL hresL
  intro C hC hind A hA hcount v
  have hY : 0 ≤ D.Y L A := (TheoremCParam.counterexample_pos hC hcount).le
  have hEv : ∀ ω ∈ cd.clsSel L (.inr v),
      envEnergy D L A ω ≤ (D.B + z L) * selProd D L ω * D.Y L A + rE L A ω := fun ω hω =>
    env_le_of_le hY (hzE L) (hEL C hC hind A hA hcount ω (isSelection_of_mem_clsSel hω))
  have hρv := hρ L v
  have hrrv := hrr L A v
  cases hv : cr L v
  · simp only [hv, Bool.false_eq_true, ↓reduceIte, sub_zero, add_zero] at hρv hrrv
    exact varStepsAt_noCredit _ (ρ L) (rr L A) (rE L A) (hz0 L) hY hEv (hWZ L A v) hρv hK hrrv
  · simp only [hv, ↓reduceIte] at hρv hrrv
    exact varStepsAt_credit _ (fun ω hω => isSelection_of_mem_clsSel hω) (ρ L) (rr L A) (rE L A)
      (rJ L A) (r₀ L A v) Rstar (bt L v) (hr₀ L A v) (fun ω _ => hrJ L A ω) hRs (hzm L v hv) hEv
      (hJNL C hC hind A hA hcount v hv) (hresL C hC hind A hA hcount v hv) (hWZ L A v) hρv hK
      hrrv

end Generic

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {UpT : UpperRecordTables}

/-- **`varConjunctW` at the obligations' data, with (E1) discharged** (`envelopeBoundNonneg_ec`):
there are `ε_E → 0`, `c_E ≥ 0`, `r_E ≥ 0` with `∑_ω π̃_ω r_E(ω) ≤ c_E L^{-σ} α` such that the
variance conjunct holds at every budget `WZ ≥ 0`, for every `z ≥ ε_E`, `K ≥ 3`, given the credit
inputs `hzm`, `hJN`, `hres` on the credit classes, the residuals `hρ` and the remainders `hrr`. -/
theorem varConjunctW_front (F : CompanionFrontND hW hMR hFour UpT) (hB : Target.BMOR)
    (hRR : Target.ThetaSmallRR) :
    ∃ εE : ℕ → ℝ, (∀ L, 0 ≤ εE L) ∧ Tendsto εE atTop (𝓝 0) ∧ ∃ cE : ℝ, 0 ≤ cE ∧
    ∃ rE : ∀ L, Finset ℤ → Choice ((F.X hB hRR).data.CL.T L) → ℝ, (∀ L A ω, 0 ≤ rE L A ω) ∧
    Param.AtCounterexamples (Params.ofDecay TargetLedger.targetDecay) (F.X hB hRR).data.Y
      (fun L A => ∑ ω ∈ univ.filter (fun ω : Choice ((F.X hB hRR).data.CL.T L) => IsSelection ω),
        monomial ((F.X hB hRR).data.CL.πt L) ω * rE L A ω ≤ Comparison.remainder cE L A) ∧
    ∀ (cd : ClassData (F.X hB hRR).data.CL) (WZ : ∀ L, Finset ℤ → cd.V L → ℝ)
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
      (∀ L A (v : cd.V L), 0 ≤ WZ L A v) →
      Param.AtCounterexamples (Params.ofDecay TargetLedger.targetDecay) (F.X hB hRR).data.Y
        fun L A => ∀ v : cd.V L,
          Nonempty (VarStepsAt (cd.clsSel L (.inr v)) (termAt (D := (F.X hB hRR).data) L A)
            (fun ω => monomial ((F.X hB hRR).data.CL.π L) ω) (ρ L) (rr L A) (WZ L A v)
            ((F.X hB hRR).data.Y L A) (z L) K) := by
  obtain ⟨εE, hε0, hεt, cE, hcE, rE, hrE0, h1, h2⟩ := envelopeBoundNonneg_ec F hB hRR
  refine ⟨εE, hε0, hεt, cE, hcE, rE, hrE0, h2, ?_⟩
  intro cd WZ ρ z K rr hzE hz0 hK cr bt Rstar hRs rJ r₀ hr₀ hrJ hzm hJN hres hρ hrr hWZ
  exact varConjunctW cd WZ ρ z K rr h1 hzE hz0 hK cr bt Rstar hRs rJ r₀ hr₀ hrJ hzm hJN hres hρ
    hrr hWZ

end Sarkozy.OpsVariance
