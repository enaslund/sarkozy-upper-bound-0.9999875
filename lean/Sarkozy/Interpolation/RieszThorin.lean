module

public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Bilinear Riesz–Thorin interpolation on finite measure spaces

The interpolation step of `lem:density:edge-moment`
(`paper/sections/30_density_moment_upgrade.tex`): a bilinear form bounded on `L^{p₀} × L^{q₀}`
with constant `M₀` and on `L^{p₁} × L^{q₁}` with constant `M₁` is bounded on `L^p × L^q` with
constant `M₀^{1−t} M₁^t`, where `1/p = (1−t)/p₀ + t/p₁` and `1/q = (1−t)/q₀ + t/q₁`.

Setting: finite types `X`, `Y` with nonnegative weights `μ`, `ν` (any finite measures; the
uniform probability is `μ = 1/|X|`). Every bilinear form on `(X → ℂ) × (Y → ℂ)` is
`bil K u v = ∑ x, ∑ y, K x y · u x · v y` for its kernel `K`. The norms are
`wNorm μ r u = (∑ x, μ x ‖u x‖^r)^{1/r}`.

The proof is the complex method. For `u, v` fix the entire family
`u_z = |u|^{α(z)} · u/|u|`, `α(z) = p(1−z)/p₀ + pz/p₁` (`family`; zero where `u = 0`), and
similarly `v_z`. The function `F(z) = bil K u_z v_z` is a finite sum of exponentials, hence
entire and bounded on the strip `0 ≤ Re z ≤ 1`. On `Re z = 0` the moduli are
`|u_z| = |u|^{p/p₀}`, so `‖u_z‖_{p₀} = ‖u‖_p^{p/p₀}` (`wNorm_eq_rpow`). On `Re z = 1` similarly.
At `z = t`, `u_t = u`. Hadamard's three-lines theorem
(`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'`) gives the bound.

Only positivity of the exponents is used (no convexity, so `p < 1` is allowed); the constant
is exactly `M₀^{1−t} M₁^t`.

Main result: `riesz_thorin_bilinear`.
-/

@[expose] public section

open scoped BigOperators
open Complex Complex.HadamardThreeLines

namespace Sarkozy.Interpolation

variable {X Y : Type*}

section Family

/-- The interpolating family `u_z = |u|^{a + z (b − a)} · u/|u|` (zero where `u` vanishes). -/
noncomputable def family (a b : ℝ) (u : X → ℂ) (z : ℂ) (x : X) : ℂ :=
  if u x = 0 then 0 else
    cexp (((a : ℂ) + z * ((b : ℂ) - a)) * (Real.log ‖u x‖ : ℂ)) * (u x / (‖u x‖ : ℂ))

theorem family_differentiable (a b : ℝ) (u : X → ℂ) (x : X) :
    Differentiable ℂ (fun z => family a b u z x) := by
  unfold family
  split_ifs
  · exact differentiable_const _
  · fun_prop

/-- Where the exponent `a + Re z (b − a)` is positive, `|u_z| = |u|^{a + Re z (b − a)}`. -/
theorem norm_family (a b : ℝ) (u : X → ℂ) (z : ℂ) (x : X) (h : 0 < a + z.re * (b - a)) :
    ‖family a b u z x‖ = ‖u x‖ ^ (a + z.re * (b - a)) := by
  unfold family
  split_ifs with hx
  · rw [hx, norm_zero, Real.zero_rpow h.ne']
  · have hpos : 0 < ‖u x‖ := norm_pos_iff.mpr hx
    rw [norm_mul, Complex.norm_exp, Complex.norm_div, Complex.norm_real, norm_norm,
      div_self hpos.ne', mul_one, Real.rpow_def_of_pos hpos]
    congr 1
    simp [Complex.mul_re]
    ring

/-- On the closed strip, `|u_z| ≤ e^{a log|u|} + e^{b log|u|}`, uniformly in `z`. -/
theorem norm_family_le (a b : ℝ) (u : X → ℂ) {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) (x : X) :
    ‖family a b u z x‖ ≤ Real.exp (a * Real.log ‖u x‖) + Real.exp (b * Real.log ‖u x‖) := by
  unfold family
  split_ifs with hx
  · rw [norm_zero]
    positivity
  · have hpos : 0 < ‖u x‖ := norm_pos_iff.mpr hx
    rw [norm_mul, Complex.norm_exp, Complex.norm_div, Complex.norm_real, norm_norm,
      div_self hpos.ne', mul_one]
    have hre : (((a : ℂ) + z * ((b : ℂ) - a)) * (Real.log ‖u x‖ : ℂ)).re =
        (1 - z.re) * (a * Real.log ‖u x‖) + z.re * (b * Real.log ‖u x‖) := by
      simp [Complex.mul_re]
      ring
    rw [hre]
    have hA := Real.exp_pos (a * Real.log ‖u x‖)
    have hB := Real.exp_pos (b * Real.log ‖u x‖)
    rcases le_total (a * Real.log ‖u x‖) (b * Real.log ‖u x‖) with h | h
    · have : (1 - z.re) * (a * Real.log ‖u x‖) + z.re * (b * Real.log ‖u x‖) ≤
          b * Real.log ‖u x‖ := by nlinarith
      have := Real.exp_le_exp.mpr this
      linarith
    · have : (1 - z.re) * (a * Real.log ‖u x‖) + z.re * (b * Real.log ‖u x‖) ≤
          a * Real.log ‖u x‖ := by nlinarith
      have := Real.exp_le_exp.mpr this
      linarith

/-- At a real point where the exponent is `1`, the family returns `u`. -/
theorem family_eq_self (a b : ℝ) (u : X → ℂ) {t : ℝ} (h : a + t * (b - a) = 1) :
    family a b u (t : ℂ) = u := by
  funext x
  unfold family
  split_ifs with hx
  · exact hx.symm
  · have hpos : 0 < ‖u x‖ := norm_pos_iff.mpr hx
    have h' : ((a : ℂ) + (t : ℂ) * ((b : ℂ) - a)) = 1 := by
      have := congrArg (fun r : ℝ => (r : ℂ)) h
      push_cast at this
      exact this
    have hne : ((‖u x‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
    rw [h', one_mul, ← Complex.ofReal_exp, Real.exp_log hpos]
    field_simp

end Family

variable [Fintype X] [Fintype Y]

/-- The weighted `L^r` (quasi)norm `(∑ x, μ x ‖u x‖^r)^{1/r}` of a complex function on a finite
type. With `μ = 1/|X|` it is the uniform `L^r` norm of the paper. -/
noncomputable def wNorm (μ : X → ℝ) (r : ℝ) (u : X → ℂ) : ℝ :=
  (∑ x, μ x * ‖u x‖ ^ r) ^ r⁻¹

/-- The bilinear form `∑ x, ∑ y, K x y · u x · v y` of a kernel `K`. -/
noncomputable def bil (K : X → Y → ℂ) (u : X → ℂ) (v : Y → ℂ) : ℂ :=
  ∑ x, ∑ y, K x y * u x * v y

theorem wNorm_nonneg (μ : X → ℝ) (r : ℝ) (u : X → ℂ) (hμ : ∀ x, 0 ≤ μ x) :
    0 ≤ wNorm μ r u :=
  Real.rpow_nonneg (Finset.sum_nonneg fun x _ =>
    mul_nonneg (hμ x) (Real.rpow_nonneg (norm_nonneg _) _)) _

theorem norm_bil_le (K : X → Y → ℂ) (u : X → ℂ) (v : Y → ℂ) :
    ‖bil K u v‖ ≤ ∑ x, ∑ y, ‖K x y‖ * ‖u x‖ * ‖v y‖ := by
  unfold bil
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
    (le_of_eq (Finset.sum_congr rfl fun y _ => ?_)))
  rw [norm_mul, norm_mul]

/-- **Norms of powers.** If `|w| = |u|^s` pointwise with `s r = p`, then
`‖w‖_r = ‖u‖_p^s`. -/
theorem wNorm_eq_rpow (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) {r p s : ℝ} (hr : r ≠ 0) (hp : p ≠ 0)
    (hsr : s * r = p) {u w : X → ℂ} (hw : ∀ x, ‖w x‖ = ‖u x‖ ^ s) :
    wNorm μ r w = wNorm μ p u ^ s := by
  unfold wNorm
  have hsum : ∑ x, μ x * ‖w x‖ ^ r = ∑ x, μ x * ‖u x‖ ^ p := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hw, ← Real.rpow_mul (norm_nonneg _), hsr]
  rw [hsum, ← Real.rpow_mul (Finset.sum_nonneg fun x _ =>
    mul_nonneg (hμ x) (Real.rpow_nonneg (norm_nonneg _) _))]
  have hs : s ≠ 0 := by
    rintro rfl
    exact hp (by rw [← hsr, zero_mul])
  congr 1
  rw [← hsr]
  field_simp

/-- The exponent algebra of the three-lines bound. -/
theorem interp_algebra {M₀ M₁ A B a b c d t : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hab : a * (1 - t) + b * t = 1) (hcd : c * (1 - t) + d * t = 1) :
    (M₀ * A ^ a * B ^ c) ^ (1 - t) * (M₁ * A ^ b * B ^ d) ^ t =
      M₀ ^ (1 - t) * M₁ ^ t * A * B := by
  have hAa := Real.rpow_nonneg hA a
  have hAb := Real.rpow_nonneg hA b
  have hBc := Real.rpow_nonneg hB c
  have hBd := Real.rpow_nonneg hB d
  rw [Real.mul_rpow (mul_nonneg hM₀ hAa) hBc, Real.mul_rpow hM₀ hAa,
    Real.mul_rpow (mul_nonneg hM₁ hAb) hBd, Real.mul_rpow hM₁ hAb,
    ← Real.rpow_mul hA, ← Real.rpow_mul hB, ← Real.rpow_mul hA, ← Real.rpow_mul hB]
  have e1 : A ^ (a * (1 - t)) * A ^ (b * t) = A := by
    rw [← Real.rpow_add' hA (by rw [hab]; norm_num), hab, Real.rpow_one]
  have e2 : B ^ (c * (1 - t)) * B ^ (d * t) = B := by
    rw [← Real.rpow_add' hB (by rw [hcd]; norm_num), hcd, Real.rpow_one]
  calc M₀ ^ (1 - t) * A ^ (a * (1 - t)) * B ^ (c * (1 - t)) *
        (M₁ ^ t * A ^ (b * t) * B ^ (d * t))
      = M₀ ^ (1 - t) * M₁ ^ t * (A ^ (a * (1 - t)) * A ^ (b * t)) *
          (B ^ (c * (1 - t)) * B ^ (d * t)) := by ring
    _ = M₀ ^ (1 - t) * M₁ ^ t * A * B := by rw [e1, e2]

/-- Positivity of an interpolated exponent. -/
theorem interp_exponent_pos {p₀ p₁ p t : ℝ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hpt : 1 / p = (1 - t) / p₀ + t / p₁) : 0 < p := by
  have h : 0 < (1 - t) / p₀ + t / p₁ := by
    rcases eq_or_lt_of_le ht1 with h | h
    · subst h
      simp only [sub_self, zero_div, zero_add]
      exact div_pos one_pos hp₁
    · have h1 : 0 < (1 - t) / p₀ := div_pos (by linarith) hp₀
      have h2 : 0 ≤ t / p₁ := div_nonneg ht0 hp₁.le
      linarith
  rw [← hpt] at h
  exact one_div_pos.mp h

/-- The interpolated exponent identity `(p/p₀)(1 − t) + (p/p₁) t = 1`. -/
theorem interp_exponent_eq {p₀ p₁ p t : ℝ} (hp : p ≠ 0) (hpt : 1 / p = (1 - t) / p₀ + t / p₁) :
    p / p₀ * (1 - t) + p / p₁ * t = 1 := by
  have : p / p₀ * (1 - t) + p / p₁ * t = p * ((1 - t) / p₀ + t / p₁) := by ring
  rw [this, ← hpt, mul_one_div_cancel hp]

/-- **Bilinear Riesz–Thorin on finite measure spaces** (the interpolation step of
`lem:density:edge-moment`). Let `K` be a complex kernel on `X × Y`, with weights `μ, ν ≥ 0`. If
`‖bil K u v‖ ≤ M₀ ‖u‖_{p₀} ‖v‖_{q₀}` and `‖bil K u v‖ ≤ M₁ ‖u‖_{p₁} ‖v‖_{q₁}` for all complex
`u, v`, then for `0 ≤ t ≤ 1`, `1/p = (1−t)/p₀ + t/p₁` and `1/q = (1−t)/q₀ + t/q₁`,
`‖bil K u v‖ ≤ M₀^{1−t} M₁^t ‖u‖_p ‖v‖_q`. All exponents need only be positive. -/
theorem riesz_thorin_bilinear (μ : X → ℝ) (ν : Y → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ y, 0 ≤ ν y)
    (K : X → Y → ℂ) {p₀ q₀ p₁ q₁ p q t M₀ M₁ : ℝ}
    (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hpt : 1 / p = (1 - t) / p₀ + t / p₁) (hqt : 1 / q = (1 - t) / q₀ + t / q₁)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (h₀ : ∀ u v, ‖bil K u v‖ ≤ M₀ * wNorm μ p₀ u * wNorm ν q₀ v)
    (h₁ : ∀ u v, ‖bil K u v‖ ≤ M₁ * wNorm μ p₁ u * wNorm ν q₁ v) (u : X → ℂ) (v : Y → ℂ) :
    ‖bil K u v‖ ≤ M₀ ^ (1 - t) * M₁ ^ t * wNorm μ p u * wNorm ν q v := by
  have hp : 0 < p := interp_exponent_pos hp₀ hp₁ ht0 ht1 hpt
  have hq : 0 < q := interp_exponent_pos hq₀ hq₁ ht0 ht1 hqt
  have hab := interp_exponent_eq hp.ne' hpt
  have hcd := interp_exponent_eq hq.ne' hqt
  have ha : 0 < p / p₀ := div_pos hp hp₀
  have hb : 0 < p / p₁ := div_pos hp hp₁
  have hc : 0 < q / q₀ := div_pos hq hq₀
  have hd : 0 < q / q₁ := div_pos hq hq₁
  set a := p / p₀ with ha_def
  set b := p / p₁ with hb_def
  set c := q / q₀ with hc_def
  set d := q / q₁ with hd_def
  set F : ℂ → ℂ := fun z => bil K (family a b u z) (family c d v z) with hF_def
  -- `F` is entire
  have hFd : Differentiable ℂ F := by
    rw [hF_def]
    unfold bil
    refine Differentiable.fun_sum fun x _ => Differentiable.fun_sum fun y _ => ?_
    exact ((differentiable_const _).mul (family_differentiable a b u x)).mul
      (family_differentiable c d v y)
  -- `F` at `t`
  have hFt : F (t : ℂ) = bil K u v := by
    rw [hF_def]
    simp only
    rw [family_eq_self a b u (by linarith), family_eq_self c d v (by linarith)]
  -- `F` is bounded on the strip
  have hBdd : BddAbove ((norm ∘ F) '' verticalClosedStrip 0 1) := by
    refine ⟨∑ x, ∑ y, ‖K x y‖ *
      (Real.exp (a * Real.log ‖u x‖) + Real.exp (b * Real.log ‖u x‖)) *
      (Real.exp (c * Real.log ‖v y‖) + Real.exp (d * Real.log ‖v y‖)), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simp only [verticalClosedStrip, Set.mem_preimage, Set.mem_Icc] at hz
    refine (norm_bil_le K _ _).trans (Finset.sum_le_sum fun x _ => Finset.sum_le_sum
      fun y _ => ?_)
    have h1 := norm_family_le a b u hz.1 hz.2 x
    have h2 := norm_family_le c d v hz.1 hz.2 y
    have h3 := norm_nonneg (K x y)
    have h4 := norm_nonneg (family a b u z x)
    have h5 := norm_nonneg (family c d v z y)
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 h3) h2 h5
      (mul_nonneg h3 (h4.trans h1))
  set Nu := wNorm μ p u with hNu
  set Nv := wNorm ν q v with hNv
  -- the line `Re z = 0`
  have hline0 : ∀ z ∈ re ⁻¹' {(0 : ℝ)}, ‖F z‖ ≤ M₀ * Nu ^ a * Nv ^ c := by
    intro z hz
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
    have hu : ∀ x, ‖family a b u z x‖ = ‖u x‖ ^ a := by
      intro x
      rw [norm_family a b u z x (by rw [hz]; simpa using ha), hz, zero_mul, add_zero]
    have hv : ∀ y, ‖family c d v z y‖ = ‖v y‖ ^ c := by
      intro y
      rw [norm_family c d v z y (by rw [hz]; simpa using hc), hz, zero_mul, add_zero]
    calc ‖F z‖ ≤ M₀ * wNorm μ p₀ (family a b u z) * wNorm ν q₀ (family c d v z) := h₀ _ _
      _ = M₀ * Nu ^ a * Nv ^ c := by
        rw [wNorm_eq_rpow μ hμ hp₀.ne' hp.ne' (by rw [ha_def]; field_simp) hu,
          wNorm_eq_rpow ν hν hq₀.ne' hq.ne' (by rw [hc_def]; field_simp) hv]
  -- the line `Re z = 1`
  have hline1 : ∀ z ∈ re ⁻¹' {(1 : ℝ)}, ‖F z‖ ≤ M₁ * Nu ^ b * Nv ^ d := by
    intro z hz
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
    have hu : ∀ x, ‖family a b u z x‖ = ‖u x‖ ^ b := by
      intro x
      rw [norm_family a b u z x (by rw [hz]; simpa using hb), hz, one_mul, add_sub_cancel]
    have hv : ∀ y, ‖family c d v z y‖ = ‖v y‖ ^ d := by
      intro y
      rw [norm_family c d v z y (by rw [hz]; simpa using hd), hz, one_mul, add_sub_cancel]
    calc ‖F z‖ ≤ M₁ * wNorm μ p₁ (family a b u z) * wNorm ν q₁ (family c d v z) := h₁ _ _
      _ = M₁ * Nu ^ b * Nv ^ d := by
        rw [wNorm_eq_rpow μ hμ hp₁.ne' hp.ne' (by rw [hb_def]; field_simp) hu,
          wNorm_eq_rpow ν hν hq₁.ne' hq.ne' (by rw [hd_def]; field_simp) hv]
  -- three lines
  have hz : (t : ℂ) ∈ verticalClosedStrip 0 1 := by
    simp only [verticalClosedStrip, Set.mem_preimage, Complex.ofReal_re, Set.mem_Icc]
    exact ⟨ht0, ht1⟩
  have key := norm_le_interp_of_mem_verticalClosedStrip₀₁' F hz hFd.diffContOnCl hBdd
    hline0 hline1
  rw [hFt, Complex.ofReal_re] at key
  rw [← interp_algebra hM₀ hM₁ (wNorm_nonneg μ p u hμ) (wNorm_nonneg ν q v hν) hab hcd]
  exact key

end Sarkozy.Interpolation
