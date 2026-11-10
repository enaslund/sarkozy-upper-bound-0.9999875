module

public import Sarkozy.Certificates.EdgeGateBands
public import Sarkozy.DensityUpgrade.StrongF
public import Sarkozy.Moments.Energy

/-!
# The square-pair moment from its gate (`lem:density:edge-moment`)

`paper/sections/30_density_moment_upgrade.tex`. For an odd prime `p` let `L = (p + 1)/(p − 1)`
and `ρ = 1/(√p − 1)`. Since `p − 1 = (√p − 1)(√p + 1)`, this `ρ` equals `(√p + 1)/(p − 1)`.

The paper's argument has three steps.
1. The centred bilinear form of a uniform strict square pair (or nonsquare pair) has norm at
   most `L` on `L¹ × L¹` and at most `ρ` on `L² × L²`.
2. Bilinear interpolation at `r = 1 + 1/j` gives the centred `L^r` bound
   `β = L^{(j−1)/(j+1)} ρ^{2/(j+1)}`.
3. Under the gate `eq:density:edge-integer-gate`, `j^{j+1} L^{j−1} ρ² ≤ 1`, so `β ≤ r − 1`.
   Then uniform convexity gives unit mixed `L^r`.

Proved here:
* `beta_le_of_gate`: step 3's inequality `β ≤ 1/j`;
* `edge_moment_of_interpolation`: the pair law has unit mixed `L^{1+1/j}`. It assumes the
  interpolated centred bound of step 2, and uses WP-P's `strongF_pair_unit_mixed` for the
  uniform-convexity step;
* `edge_moment_band`: on each of the 31 clique bands, the gate holds at every `p ≥ 2^b`
  (`EdgeGate.edge_gate_band`), so the conclusion holds there with `j = j_b`, given the
  interpolated bound.

`mixedLpBound_iff_conditioningUnitMixed` identifies WP-FI's weight-based `conditioningUnitMixed`
with the `FiniteLaw` notion `MixedLpBound … 1`. Through it, the conclusion feeds
`InvariantPair.invariant_pair_mixedLpBound` and the other `MixedLpBound` lemmas.

Not formalized: steps 1 and 2. Bilinear Riesz–Thorin is not in Mathlib (FEASIBILITY.md,
"Mathlib gaps"). The step 2 bound is the one named hypothesis.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.EdgeGate

/-- **The gate gives `β ≤ 1/j`**: if `j^{j+1} L^{j−1} ρ² ≤ 1` with `L, ρ ≥ 0` and `j ≥ 1`, then
`L^{(j−1)/(j+1)} ρ^{2/(j+1)} ≤ 1/j`. -/
theorem beta_le_of_gate {j : ℕ} (hj : 1 ≤ j) {L ρ : ℝ} (hL : 0 ≤ L) (hρ : 0 ≤ ρ)
    (hgate : (j : ℝ) ^ (j + 1) * L ^ (j - 1) * ρ ^ 2 ≤ 1) :
    L ^ (((j : ℝ) - 1) / ((j : ℝ) + 1)) * ρ ^ ((2 : ℝ) / ((j : ℝ) + 1)) ≤ 1 / j := by
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by linarith
  set β := L ^ (((j : ℝ) - 1) / ((j : ℝ) + 1)) * ρ ^ ((2 : ℝ) / ((j : ℝ) + 1)) with hβ
  have hβ0 : 0 ≤ β := mul_nonneg (Real.rpow_nonneg hL _) (Real.rpow_nonneg hρ _)
  -- `β^{j+1} = L^{j−1} ρ²`
  have hpow : β ^ (j + 1) = L ^ (j - 1) * ρ ^ 2 := by
    rw [hβ, mul_pow, ← Real.rpow_natCast (L ^ _), ← Real.rpow_natCast (ρ ^ _),
      ← Real.rpow_mul hL, ← Real.rpow_mul hρ]
    have e1 : ((j : ℝ) - 1) / ((j : ℝ) + 1) * ((j + 1 : ℕ) : ℝ) = ((j - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hj]
      push_cast
      field_simp
    have e2 : (2 : ℝ) / ((j : ℝ) + 1) * ((j + 1 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) := by
      push_cast
      field_simp
    rw [e1, e2, Real.rpow_natCast, Real.rpow_natCast]
  -- compare `(j β)^{j+1} ≤ 1`
  have hjb : ((j : ℝ) * β) ^ (j + 1) ≤ 1 := by
    rw [mul_pow, hpow, ← mul_assoc]
    exact hgate
  have hjb0 : 0 ≤ (j : ℝ) * β := mul_nonneg hjpos.le hβ0
  have : (j : ℝ) * β ≤ 1 := by
    by_contra h
    push Not at h
    have : 1 < ((j : ℝ) * β) ^ (j + 1) := one_lt_pow₀ h (by omega)
    linarith
  rw [le_div_iff₀ hjpos]
  linarith

theorem one_le_bandJ : ∀ i : Fin 31, 1 ≤ bandJ i := by decide

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- **`lem:density:edge-moment` from the interpolated bound.** If a pair law with uniform
coordinates has centred bilinear `L^{1+1/j}` norm at most `β = L^{(j−1)/(j+1)} ρ^{2/(j+1)}`, and the
gate `j^{j+1} L^{j−1} ρ² ≤ 1` holds, then it has unit mixed `L^{1+1/j}`. -/
theorem edge_moment_of_interpolation (π : (Fin 2 → X) → ℝ) (hπ : ∀ x, 0 ≤ π x)
    (hπu : DensityUpgrade.conditioningUniformCoords π) {j : ℕ} (hj : 1 ≤ j) {L ρ : ℝ}
    (hL : 0 ≤ L) (hρ : 0 ≤ ρ) (hgate : (j : ℝ) ^ (j + 1) * L ^ (j - 1) * ρ ^ 2 ≤ 1)
    (hinterp : ∀ f g : X → ℝ, ∑ a, f a = 0 → ∑ a, g a = 0 →
      |∑ x, π x * (f (x 0) * g (x 1))| ≤
        L ^ (((j : ℝ) - 1) / ((j : ℝ) + 1)) * ρ ^ ((2 : ℝ) / ((j : ℝ) + 1)) *
          DensityUpgrade.conditioningNorm (1 + 1 / (j : ℝ)) f *
          DensityUpgrade.conditioningNorm (1 + 1 / (j : ℝ)) g) :
    DensityUpgrade.conditioningUnitMixed π (1 + 1 / (j : ℝ)) := by
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  apply DensityUpgrade.strongF_pair_unit_mixed π hπ hπu
    (by have := one_div_pos.mpr hjpos; linarith)
    (by have : 1 / (j : ℝ) ≤ 1 := by rw [div_le_one hjpos]; exact hj1
        linarith)
    (c := L ^ (((j : ℝ) - 1) / ((j : ℝ) + 1)) * ρ ^ ((2 : ℝ) / ((j : ℝ) + 1)))
    (by have := beta_le_of_gate hj hL hρ hgate; linarith)
    hinterp

/-- **On each clique band**: at every `p ≥ 2^b`, the gate holds with `j = j_b`,
`L = (p + 1)/(p − 1)` and `ρ = 1/(√p − 1)`. So the interpolated bound gives unit mixed
`L^{1+1/j_b}` for the pair law. -/
theorem edge_moment_band (i : Fin 31) {p : ℝ} (hp : (2 : ℝ) ^ bandB i ≤ p)
    (π : (Fin 2 → X) → ℝ) (hπ : ∀ x, 0 ≤ π x) (hπu : DensityUpgrade.conditioningUniformCoords π)
    (hinterp : ∀ f g : X → ℝ, ∑ a, f a = 0 → ∑ a, g a = 0 →
      |∑ x, π x * (f (x 0) * g (x 1))| ≤
        ((p + 1) / (p - 1)) ^ (((bandJ i : ℝ) - 1) / ((bandJ i : ℝ) + 1)) *
          (1 / (Real.sqrt p - 1)) ^ ((2 : ℝ) / ((bandJ i : ℝ) + 1)) *
          DensityUpgrade.conditioningNorm (1 + 1 / (bandJ i : ℝ)) f *
          DensityUpgrade.conditioningNorm (1 + 1 / (bandJ i : ℝ)) g) :
    DensityUpgrade.conditioningUnitMixed π (1 + 1 / (bandJ i : ℝ)) := by
  have hb : (2 : ℝ) ^ (16 : ℕ) ≤ (2 : ℝ) ^ bandB i :=
    pow_le_pow_right₀ (by norm_num) (by unfold bandB; omega)
  have hp1 : 1 < p := by
    have : (1 : ℝ) < (2 : ℝ) ^ (16 : ℕ) := by norm_num
    linarith
  have hsq : 1 ≤ Real.sqrt p := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hp1.le
  have hj : 1 ≤ bandJ i := one_le_bandJ i
  have hgate := edge_gate_band i hp
  have hgate' : (bandJ i : ℝ) ^ (bandJ i + 1) * ((p + 1) / (p - 1)) ^ (bandJ i - 1) *
      (1 / (Real.sqrt p - 1)) ^ 2 ≤ 1 := by
    rw [one_div_pow]
    exact hgate
  exact edge_moment_of_interpolation π hπ hπu hj (div_nonneg (by linarith) (by linarith))
    (one_div_nonneg.mpr (by linarith)) hgate' hinterp

omit [DecidableEq X] in
/-- **The two unit-mixed notions agree**: for a finite law `μ` on `Fin d → X`, WP-FI's
`conditioningUnitMixed μ.weight r` is `MixedLpBound μ r 1`. -/
theorem mixedLpBound_iff_conditioningUnitMixed {d : ℕ} (μ : FiniteLaw (Fin d → X)) (r : ℝ) :
    MixedLpBound μ r 1 ↔ DensityUpgrade.conditioningUnitMixed μ.weight r := by
  unfold MixedLpBound DensityUpgrade.conditioningUnitMixed
  simp only [one_mul, DensityUpgrade.conditioningNorm_eq_lpNorm]
  rfl

end Sarkozy.EdgeGate
