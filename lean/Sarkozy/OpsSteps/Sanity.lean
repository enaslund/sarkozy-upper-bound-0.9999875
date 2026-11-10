module

public import Sarkozy.OpsSteps.Coupling
public import Sarkozy.OpsSteps.Step3
public import Sarkozy.OpsSteps.E1Diag
public import Sarkozy.OpsSteps.Bridges

@[expose] public section

/-!
# Sanity checks for OPS-S (non-vacuity and the unit tables)

* `toy_orbit_coupon`: the hypotheses of `orbit_coupon_rem` hold with a positive saving `s` and a
  positive orbit mass (two couplings exchanged by the reflection, coefficients `1`, `2`, `M = 3`,
  `M_h = 2`), so the improved bound is not vacuous;
* the unit tables of `lem:oct24:mask-schur`(a) (`foldUnit`, `matchUnit`) at sample entries: the
  singleton unit `e₀₁ ↦ M₀₁ − 𝒥`, the scalar unit `e₃₃ ↦ Q₁₂` (coefficient `(1 − ρ)/(1 + ρ)` on
  `𝒥`, `−1/(1 + ρ)` on `P₁ = M₁₁`), and a unit off the blocks of `𝒜_F` (`e₀₃ ↦ 0`);
* `fold_fixed_cases`: the fixed folds `F₁ ∘ R₃ = F₁`, `F₂ ∘ R₁ = F₂` that `extra_ha_blocks` needs;
* `mul_remainder`: a constant times `c L^{-σ} α` is `(K c) L^{-σ} α`, for summing the (E1)
  remainders of the classes (`E1Diag.sum_rem_le`) into the field `∑ rr ≤ c₀ L^{-σ} α` of
  `ClassStepsOps`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsSteps

open Sarkozy.Envelopes

/-- **Non-vacuity of the orbit coupon with remainders**: two couplings exchanged by the reflection,
with coefficients `1`, `2` and placed errors `±1`; the orbit average has error `0 ≤ R − s`. The
conclusion `|K| = 1 ≤ M R − M_h s = 3 − 2 · ½`. -/
theorem toy_orbit_coupon :
    |(LinearMap.id : ℝ →ₗ[ℝ] ℝ) (∑ C, ![(1 : ℝ), 2] C • ![(1 : ℝ), -1] C)| ≤
      couplingMass ![(1 : ℝ), 2] * 1 -
        orbitMass (Equiv.swap (0 : Fin 2) 1) ![(1 : ℝ), 2] * (1 / 2) +
        ∑ C, |![(1 : ℝ), 2] C| * 0 := by
  refine orbit_coupon_rem (h := Equiv.swap (0 : Fin 2) 1) (fun C => Equiv.swap_apply_self _ _ C)
    ![(1 : ℝ), 2] ![(1 : ℝ), -1] LinearMap.id (fun _ => 0) (fun C => ?_) (fun C => ?_)
  · fin_cases C <;> simp
  · fin_cases C <;> norm_num [Equiv.swap_apply_left, Equiv.swap_apply_right]

/-- The singleton unit `e₀₁` of a fold factor is `M₀₁ − 𝒥`. -/
example (ρ : ℝ) : foldUnit ρ 0 1 (FoldCpl.M 0 1) = 1 ∧ foldUnit ρ 0 1 FoldCpl.J = -1 ∧
    foldUnit ρ 0 1 FoldCpl.P12 = 0 := by
  simp [foldUnit]

/-- The scalar unit `e₃₃` of a fold factor is `Q₁₂`. -/
example (ρ : ℝ) : foldUnit ρ 3 3 FoldCpl.J = (1 - ρ) / (1 + ρ) ∧
    foldUnit ρ 3 3 (FoldCpl.M 1 1) = -(1 / (1 + ρ)) ∧ foldUnit ρ 3 3 FoldCpl.P12 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [foldUnit, qUnit]

/-- A unit off the blocks `{0,1,2}, {3}, {4}` of `𝒜_F` is not lifted. -/
example (ρ : ℝ) (k : FoldCpl) : foldUnit ρ 0 3 k = 0 := by
  simp [foldUnit]

/-- The matching unit `e₁₂` is `M₁₂ − 𝒥`. -/
example : matchUnit 1 2 (MatchCpl.M 1 2) = 1 ∧ matchUnit 1 2 MatchCpl.J = -1 := by
  simp [matchUnit]

/-- `K · c L^{-σ} α = (K c) L^{-σ} α`. -/
theorem mul_remainder (K c : ℝ) (L : ℕ) (A : Finset ℤ) :
    K * Comparison.remainder c L A = Comparison.remainder (K * c) L A := by
  unfold Comparison.remainder
  ring

/-- **The hypothesis of `extra_ha_blocks` holds for the paper's cases**: `F₁ ∘ R₃ = F₁` and
`F₂ ∘ R₁ = F₂` (`lem:reflection-averaging`(a), the fixed folds; W2's `fold_reflection_table`). -/
theorem fold_fixed_cases (u : ZMod 6) :
    Labellings.fold 1 (Labellings.chamberRefl 3 u) = Labellings.fold 1 u ∧
      Labellings.fold 2 (Labellings.chamberRefl 1 u) = Labellings.fold 2 u :=
  ⟨(fold_reflection_table u).2.1.2.1, (fold_reflection_table u).1.2.2⟩

end Sarkozy.OpsSteps
