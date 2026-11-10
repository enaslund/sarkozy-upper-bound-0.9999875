module

public import Sarkozy.TheoremC.FirstStage
public import Sarkozy.TheoremCParam.Defs

@[expose] public section



open Filter Finset
open scoped Topology BigOperators

namespace Sarkozy.TheoremCParam

open Sarkozy.TheoremC
open Sarkozy.Param (Params)

variable {a : ℝ}

open Sarkozy.Comparison Sarkozy.RecordExpansion

/-- At a counterexample the reference energy is nonnegative: it exceeds
`C L^{-a} α^θ ≥ 0`. -/
theorem energy_nonneg_of_counter {Y : ℕ → Finset ℤ → ℝ} {C : ℝ} (hC : 1 ≤ C) {L : ℕ}
    {A : Finset ℤ}
    (h : C * (L : ℝ) ^ (-a) * density (blockScale * L) A ^ densityExponent < Y L A) :
    0 ≤ Y L A := by
  have h1 : 0 ≤ C * (L : ℝ) ^ (-a) * density (blockScale * L) A ^ densityExponent :=
    mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg L) _))
      (Real.rpow_nonneg (density_nonneg _ _) _)
  linarith

variable {Atom : ℕ → Type} [∀ L, Fintype (Atom L)] [∀ L, DecidableEq (Atom L)]
  {Xb : ∀ L, Atom L → Type} [∀ L b, Fintype (Xb L b)] [∀ L b, DecidableEq (Xb L b)]

/-- **`lem:record:first-stage`, robust form** (the field `firstStage` of
`ClosingEstimates`, with `εfirst L = ε(L) L₀`). Step 1 is (R2) of (CP1) at `ϑ₀` and
(CP2)(a); Step 2 is the summation of `lem:sharp-first` over the tagged differences of
(CP2)(b), with the per-term bounds `hterm` (`K = (1 + ε(L)) Y`) and the aggregate remainder
`hr` as hypotheses. The totals at every scale are at most the totals `P`, `dT`, `vT`. -/
theorem firstStage_estimate (ϑ₀ : ReflectionCut Slot)
    (μ ρ lam : ∀ L b, ((Slot → Xb L b) → ℝ) →ₗ[ℝ] ℝ) (F : ∀ L, Finset ℤ → (∀ b, Xb L b) → ℝ)
    (hμ : ∀ L b, ϑ₀.Positive (μ L b)) (hρ : ∀ L b, ϑ₀.Below (μ L b) (ρ L b))
    {I : ∀ L, Atom L → Type} [∀ L b, Fintype (I L b)] [∀ L b, DecidableEq (I L b)]
    (δ : ∀ L b, I L b → ((Slot → Xb L b) → ℝ) →ₗ[ℝ] ℝ)
    (hlam : ∀ L b, lam L b = ρ L b + ∑ i, δ L b i)
    {Tag : Type} [Fintype Tag] [DecidableEq Tag] (tag : ∀ L b, I L b → Tag)
    (d v : ∀ L b, I L b → ℝ) (hd : ∀ L b i, 0 ≤ d L b i) (hv : ∀ L b i, 0 ≤ v L b i)
    (pv : ∀ L, Atom L → ℝ) (hpv : ∀ L b, 0 ≤ pv L b)
    {P : ℝ} {dT vT : Tag → ℝ} (hP : ∀ L, ∑ b, pv L b ≤ P)
    (hdT : ∀ L j, tagTotal (tag L) (d L) j ≤ dT j)
    (hvT : ∀ L j, tagTotal (tag L) (v L) j ≤ vT j)
    (ε : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ ε L)
    (r : ∀ L, Finset ℤ → (∀ b, Option (I L b)) → ℝ) (c : ℝ)
    (hterm : Param.AtCounterexamples (Params.ofDecay a) (energyFirst μ F) fun L A =>
      ∀ σ, σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (tag L) σ j →
        |diagonalIntegral (tensorLaw (fun b => (σ b).elim (ρ L b) (δ L b))) (F L A)| ≤
          (1 + ε L) * energyFirst μ F L A * tagWeight (tag L) (d L) (v L) (pv L) j σ +
            r L A σ)
    (hr : Param.AtCounterexamples (Params.ofDecay a) (energyFirst μ F) fun L A =>
      ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (I L b)) => σ ≠ fun _ => none), r L A σ ≤
        remainder c L A) :
    Param.AtCounterexamples (Params.ofDecay a) (energyFirst μ F) fun L A =>
      (1 - firstStageCost P dT vT - ε L * firstStageCost P dT vT) * energyFirst μ F L A -
          remainder c L A ≤ energyFirst lam F L A := by
  filter_upwards [hterm, hr] with L hterm' hr'
  intro C hC hind A hA hcounter
  have hY : 0 ≤ energyFirst μ F L A := energy_nonneg_of_counter hC hcounter
  have hK : 0 ≤ (1 + ε L) * energyFirst μ F L A :=
    mul_nonneg (by linarith [hε0 L]) hY
  -- Steps 1 and 2 at the scale `L`
  have hmain := first_stage_lower_bound ϑ₀ (μ L) (ρ L) (hμ L) (hρ L) (δ L) (F L A) (tag L)
    (hd L) (hv L) (hpv L) hK (r L A) (hterm' C hC hind A hA hcounter)
  have hlamL : (fun b => ρ L b + ∑ i, δ L b i) = lam L := funext fun b => (hlam L b).symm
  rw [hlamL, ← energyFirst_eq_diagonalIntegral, ← energyFirst_eq_diagonalIntegral] at hmain
  -- the cost at the scale `L` is at most `L₀`
  have hdL : ∀ j, 0 ≤ tagTotal (tag L) (d L) j := tagTotal_nonneg (tag L) (hd L)
  have hvL : ∀ j, 0 ≤ tagTotal (tag L) (v L) j := tagTotal_nonneg (tag L) (hv L)
  have hcost : Real.exp (∑ b, pv L b) * tagSeries (tagTotal (tag L) (d L)) (tagTotal (tag L)
      (v L)) ≤
      firstStageCost P dT vT :=
    mul_le_mul (Real.exp_le_exp.mpr (hP L)) (tagSeries_mono hdL hvL (hdT L) (hvT L))
      (tagSeries_nonneg hdL hvL) (Real.exp_pos P).le
  have hKcost := mul_le_mul_of_nonneg_left hcost hK
  have hrem := hr' C hC hind A hA hcounter
  have hexpand : (1 - firstStageCost P dT vT - ε L * firstStageCost P dT vT) *
      energyFirst μ F L A = energyFirst μ F L A -
        (1 + ε L) * energyFirst μ F L A * firstStageCost P dT vT := by
    ring
  rw [hexpand]
  have hassoc : (1 + ε L) * energyFirst μ F L A * Real.exp (∑ b, pv L b) *
      tagSeries (tagTotal (tag L) (d L)) (tagTotal (tag L) (v L)) =
      (1 + ε L) * energyFirst μ F L A * (Real.exp (∑ b, pv L b) *
        tagSeries (tagTotal (tag L) (d L)) (tagTotal (tag L) (v L))) := by
    ring
  rw [hassoc] at hmain
  linarith

end Sarkozy.TheoremCParam
