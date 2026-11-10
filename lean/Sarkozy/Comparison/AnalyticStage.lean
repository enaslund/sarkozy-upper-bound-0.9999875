module

public import Sarkozy.Parameters

/-!
# The analytic stage and its exact parameter inequalities

`def:record:analytic-stage` and the stage inequalities (S1)–(S5) of
`paper/sections/08_scale_comparison.tex`, which `cert:record:analytic-stage`
checks in exact rational arithmetic, together with the slack used in
`prop:density:production` (`31_density_induction_upgrade.tex`) and the kernel triple
of `cor:kernel20` (`07_kernel_statement.tex`). Here they are checked by `norm_num`.
(S6) is the admissibility of the kernel triple, recorded below; (S7) concerns the
tail laws and is not included.
-/

@[expose] public section

namespace Sarkozy.AnalyticStage

/-- Exponent of the functional's cutoff `Q = N^β`. -/
noncomputable def β : ℝ := 1 / 20
/-- Major-arc exponent of the kernel. -/
noncomputable def η : ℝ := 17 / 100
/-- One-slot and pair mixing exponent at the tail primes. -/
noncomputable def γ : ℝ := 255 / 1024
/-- Selected sets of field primes have product at most `N^τ`. -/
noncomputable def τ : ℝ := 1 / 201
/-- Truncation exponent of pair supports in the cancellation. -/
noncomputable def tan : ℝ := 1 / 60
/-- Error exponent. -/
noncomputable def σ : ℝ := 1 / 825
/-- Moment loss per slot. -/
noncomputable def δ : ℝ := 1 / 10000000000
/-- Moment loss of the large-product estimate. -/
noncomputable def ℓ₀ : ℝ := 1 / 100000000

/-- The error exponent is the project's `cancellationDecay`. -/
theorem σ_eq : σ = cancellationDecay := by norm_num [σ, cancellationDecay]

theorem S1 : γ * β / 2 - τ - 72 * δ - σ > 0 := by norm_num [γ, β, τ, δ, σ]
theorem S2 : γ * tan - 72 * δ - σ > 0 := by norm_num [γ, tan, δ, σ]
theorem S3 : β / 6 - tan * (1 / 2 - γ) - 72 * δ - σ > 0 := by norm_num [β, tan, γ, δ, σ]
theorem S4 : τ / 4 - ℓ₀ - σ > 0 := by norm_num [τ, ℓ₀, σ]
theorem S5 : 1 - 2 * τ - 6 * β > 0 ∧ β / 2 - τ > 0 ∧ β / 2 - tan > 0 ∧
    β * (1 - 2 * τ) - β / 2 > 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [τ, β, tan]

/-- The two saving exponents of the accepted-pair cancellation are both `17/4096`. -/
theorem cancellation_savings : γ * tan = 17 / 4096 ∧ β / 6 - tan * (1 / 2 - γ) = 17 / 4096 := by
  constructor <;> norm_num [γ, tan, β]

/-- The slack of (S1) that absorbs the summed raw comparison errors in
`prop:density:production`. -/
theorem production_slack : γ * β / 2 - 72 * δ - τ - σ = 2260122363 / 58960000000000 := by
  norm_num [γ, β, δ, τ, σ]

/-- (S6): the kernel triple `(β, κ, η) = (1/20, 1/20, 17/100)` of `cor:kernel20` is
admissible (`def:kernel-conditions`), with the seven slacks of the corollary. -/
theorem S6 :
    let κ : ℝ := 1 / 20
    (-(β / 6)) - (κ + β / 2 - η / 2) = 1 / 600 ∧
    (-(β / 6)) - (κ + β - η) = 37 / 600 ∧
    (-(β / 6)) - (η + 2 * κ + 3 * β / 2 - 1) = 97 / 150 ∧
    (-(β / 6)) - (2 * η + 2 * κ + β - 1 / 2) = 1 / 600 ∧
    1 - 3 * η = 49 / 100 ∧
    η - (κ + β / 2) = 19 / 200 ∧
    1 - (2 * η + κ + β / 2) = 117 / 200 := by
  intro κ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [κ, β, η]

end Sarkozy.AnalyticStage
