module

public import Sarkozy.Variance.Interpolation

/-!
# Centred norms from quadratic bounds

The centred norms of Section 22 (`κ_F(𝔅)` of `lem:record:old-f-marginal`(c), `κ_E(𝔅) = 3/(b - 3)`
of `lem:record:paired-e-bridge`(b)) are norms of self-adjoint operators, and they are proved as
bounds of quadratic forms on the mean-zero functions (for example
`TraceMixing.tripleOp_abs_le`). This file turns such a bound into the bilinear form
`CentredNormLe` used by (P3) (`Interpolation.lean`):

* `form_self_eq_centred`: for `π` symmetric with half marginal `m`,
  `Q_π(F, F) = Q_π(F₀, F₀) + a² ∑ m`, where `a = E_m F` and `F₀ = F - a`;
* `centredNormLe_of_quadratic`: if `|Q_π(f, f)| ≤ κ ∑ m f²` for every `f` of `m`-mean zero, then
  `CentredNormLe c π m κ`, that is `‖T - 𝒥‖ ≤ κ` on `L²(m)`. The proof is by Cauchy–Schwarz
  for the two positive forms `κ Diag(m) ± (π - J(m))`; no spectral theorem is used.
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

variable {W Y : Type*} [Fintype W] [DecidableEq W] [Fintype Y]

omit [Fintype Y] in
/-- The form of a linear functional is bilinear: sums and scalars in each argument. -/
theorem form_add_left (c : ReflectionCut W) (π : ((W → Y) → ℝ) →ₗ[ℝ] ℝ)
    (G H K : (c.Half → Y) → ℝ) : c.form π (G + H) K = c.form π G K + c.form π H K := by
  change π _ = π _ + π _
  rw [← map_add]
  congr 1
  funext z
  simp only [Pi.add_apply]
  ring

omit [Fintype Y] in
theorem form_add_right (c : ReflectionCut W) (π : ((W → Y) → ℝ) →ₗ[ℝ] ℝ)
    (G H K : (c.Half → Y) → ℝ) : c.form π K (G + H) = c.form π K G + c.form π K H := by
  change π _ = π _ + π _
  rw [← map_add]
  congr 1
  funext z
  simp only [Pi.add_apply]
  ring

omit [Fintype Y] in
theorem form_smul_left (c : ReflectionCut W) (π : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) (t : ℝ)
    (G K : (c.Half → Y) → ℝ) : c.form π (t • G) K = t * c.form π G K := by
  change π _ = t • π _
  rw [← map_smul]
  congr 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype Y] in
theorem form_smul_right (c : ReflectionCut W) (π : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) (t : ℝ)
    (G K : (c.Half → Y) → ℝ) : c.form π K (t • G) = t * c.form π K G := by
  change π _ = t • π _
  rw [← map_smul]
  congr 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- For `π` symmetric with half marginal `m`: `Q_π(F, F) = Q_π(F - a, F - a) + a² ∑ m` whenever
`∑ m F = a ∑ m` (that is, `a = E_m F`). -/
theorem form_self_eq_centred (c : ReflectionCut W) {π : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    {m : (c.Half → Y) → ℝ}
    (hsymm : ∀ F G : (c.Half → Y) → ℝ, c.form π F G = c.form π G F)
    (hplus : ∀ F : (c.Half → Y) → ℝ, c.form π F 1 = ∑ x, m x * F x) (F : (c.Half → Y) → ℝ)
    (a : ℝ) (ha : ∑ x, m x * F x = a * ∑ x, m x) :
    c.form π F F = c.form π (fun x => F x - a) (fun x => F x - a) + a ^ 2 * ∑ x, m x := by
  have hmean0 : ∑ x, m x * (F x - a) = 0 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul]
    rw [ha]
    ring
  have hF : F = (fun x => F x - a) + a • (1 : (c.Half → Y) → ℝ) := by
    funext x
    simp
  have h1 : c.form π (fun x => F x - a) 1 = 0 := by rw [hplus, hmean0]
  have h2 : c.form π 1 (fun x => F x - a) = 0 := by rw [hsymm, h1]
  have h3 : c.form π 1 1 = ∑ x, m x := by
    rw [hplus]
    simp
  conv_lhs => rw [hF]
  rw [form_add_left, form_add_right, form_add_right, form_smul_left, form_smul_right,
    form_smul_left, form_smul_right, h1, h2, h3]
  ring

/-- **Centred norms from quadratic bounds**: if `π` is symmetric at `c` with half marginal
`m ≥ 0` (`∑ m > 0`) and `|Q_π(f, f)| ≤ κ ∑ m f²` for every `f` of `m`-mean zero (`κ ≥ 0`), then
`CentredNormLe c π m κ`. -/
theorem centredNormLe_of_quadratic (c : ReflectionCut W) {π : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    {m : (c.Half → Y) → ℝ} (hm : ∀ x, 0 ≤ m x) (hmpos : 0 < ∑ x, m x)
    (hsymm : ∀ F G : (c.Half → Y) → ℝ, c.form π F G = c.form π G F)
    (hplus : ∀ F : (c.Half → Y) → ℝ, c.form π F 1 = ∑ x, m x * F x) {κ : ℝ} (hκ : 0 ≤ κ)
    (hq : ∀ f : (c.Half → Y) → ℝ, ∑ x, m x * f x = 0 →
      |c.form π f f| ≤ κ * ∑ x, m x * f x ^ 2) :
    CentredNormLe c π m κ := by
  set S := ∑ x, m x with hS
  set A := π - indepLaw c m with hA
  have hformA : ∀ f g, c.form A f g =
      c.form π f g - (∑ x, m x * f x) * (∑ y, m y * g y) / S := by
    intro f g
    change c.form π f g - c.form (indepLaw c m) f g = _
    rw [form_indepLaw]
  -- the diagonal of `A` is the centred quadratic form, bounded by `κ ‖f‖²`
  have hdiag : ∀ f, |c.form A f f| ≤ κ * ∑ x, m x * f x ^ 2 := by
    intro f
    have hSne : S ≠ 0 := ne_of_gt hmpos
    have hsum : ∑ x, m x * f x = ((∑ y, m y * f y) / S) * S := by field_simp
    have heq := form_self_eq_centred c hsymm hplus f ((∑ y, m y * f y) / S) hsum
    have h0 : ∑ x, m x * (f x - (∑ y, m y * f y) / S) = 0 := by
      simp only [mul_sub, sum_sub_distrib, ← sum_mul]
      rw [← hS]
      field_simp
      ring
    have hA' : c.form A f f = c.form π (fun x => f x - (∑ y, m y * f y) / S)
        (fun x => f x - (∑ y, m y * f y) / S) := by
      have key : ((∑ y, m y * f y) / S) ^ 2 * ∑ x, m x =
          (∑ x, m x * f x) * (∑ y, m y * f y) / S := by
        rw [← hS]
        field_simp
      rw [hformA, heq, key]
      ring
    rw [hA']
    refine (hq _ h0).trans (mul_le_mul_of_nonneg_left ?_ hκ)
    -- `∑ m f₀² = ∑ m f² - a² S ≤ ∑ m f²`
    have hvar : ∑ x, m x * (f x - (∑ y, m y * f y) / S) ^ 2 =
        ∑ x, m x * f x ^ 2 - ((∑ y, m y * f y) / S) ^ 2 * S := by
      have hpt : ∀ x, m x * (f x - (∑ y, m y * f y) / S) ^ 2 =
          m x * f x ^ 2 - 2 * ((∑ y, m y * f y) / S) * (m x * f x) +
            ((∑ y, m y * f y) / S) ^ 2 * m x := by
        intro x
        ring
      simp_rw [hpt]
      rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← hS]
      field_simp
      ring
    rw [hvar]
    nlinarith [sq_nonneg ((∑ y, m y * f y) / S), hmpos]
  -- the two positive forms `κ Diag(m) ± A`
  have hAsymm : ∀ f g, c.form A f g = c.form A g f := by
    intro f g
    rw [hformA, hformA, hsymm]
    ring
  have hDform : ∀ f g, c.form (κ • c.diagonalLaw m) f g = κ * ∑ x, m x * (f x * g x) := by
    intro f g
    change κ * c.form (c.diagonalLaw m) f g = _
    rw [c.form_diagonalLaw]
  have hplusP : c.Positive (κ • c.diagonalLaw m + A) := by
    constructor
    · intro f g
      change c.form (κ • c.diagonalLaw m) f g + c.form A f g =
        c.form (κ • c.diagonalLaw m) g f + c.form A g f
      rw [hDform, hDform, hAsymm]
      congr 2
      exact sum_congr rfl fun x _ => by ring
    · intro f
      change 0 ≤ c.form (κ • c.diagonalLaw m) f f + c.form A f f
      rw [hDform]
      have := neg_abs_le (c.form A f f)
      have h := hdiag f
      have e : ∑ x, m x * (f x * f x) = ∑ x, m x * f x ^ 2 := sum_congr rfl fun x _ => by ring
      rw [e]
      linarith
  have hminusP : c.Positive (κ • c.diagonalLaw m - A) := by
    constructor
    · intro f g
      change c.form (κ • c.diagonalLaw m) f g - c.form A f g =
        c.form (κ • c.diagonalLaw m) g f - c.form A g f
      rw [hDform, hDform, hAsymm]
      congr 2
      exact sum_congr rfl fun x _ => by ring
    · intro f
      change 0 ≤ c.form (κ • c.diagonalLaw m) f f - c.form A f f
      rw [hDform]
      have := le_abs_self (c.form A f f)
      have h := hdiag f
      have e : ∑ x, m x * (f x * f x) = ∑ x, m x * f x ^ 2 := sum_congr rfl fun x _ => by ring
      rw [e]
      linarith
  -- Cauchy–Schwarz for both, and `√(xy) + √(uv) ≤ √((x+u)(y+v))`
  intro f g
  rw [← hformA]
  have cs1 := hplusP.cauchy_schwarz_sq f g
  have cs2 := hminusP.cauchy_schwarz_sq f g
  set P := κ * ∑ x, m x * (f x * g x)
  set a := c.form A f g
  set Ff := κ * ∑ x, m x * f x ^ 2
  set Gg := κ * ∑ x, m x * g x ^ 2
  set af := c.form A f f
  set ag := c.form A g g
  have ef : ∀ h : (c.Half → Y) → ℝ, κ * ∑ x, m x * (h x * h x) = κ * ∑ x, m x * h x ^ 2 :=
    fun h => by congr 1; exact sum_congr rfl fun x _ => by ring
  have e1 : c.form (κ • c.diagonalLaw m + A) f g = P + a := by
    change c.form (κ • c.diagonalLaw m) f g + c.form A f g = _
    rw [hDform]
  have e2 : c.form (κ • c.diagonalLaw m - A) f g = P - a := by
    change c.form (κ • c.diagonalLaw m) f g - c.form A f g = _
    rw [hDform]
  have e3 : c.form (κ • c.diagonalLaw m + A) f f = Ff + af := by
    change c.form (κ • c.diagonalLaw m) f f + c.form A f f = _
    rw [hDform, ef]
  have e4 : c.form (κ • c.diagonalLaw m + A) g g = Gg + ag := by
    change c.form (κ • c.diagonalLaw m) g g + c.form A g g = _
    rw [hDform, ef]
  have e5 : c.form (κ • c.diagonalLaw m - A) f f = Ff - af := by
    change c.form (κ • c.diagonalLaw m) f f - c.form A f f = _
    rw [hDform, ef]
  have e6 : c.form (κ • c.diagonalLaw m - A) g g = Gg - ag := by
    change c.form (κ • c.diagonalLaw m) g g - c.form A g g = _
    rw [hDform, ef]
  rw [e1, e3, e4] at cs1
  rw [e2, e5, e6] at cs2
  have hx : 0 ≤ Ff + af := by have := neg_abs_le af; have := hdiag f; linarith
  have hy : 0 ≤ Gg + ag := by have := neg_abs_le ag; have := hdiag g; linarith
  have hu : 0 ≤ Ff - af := by have := le_abs_self af; have := hdiag f; linarith
  have hv : 0 ≤ Gg - ag := by have := le_abs_self ag; have := hdiag g; linarith
  -- square roots
  set A1 := Real.sqrt (Ff + af)
  set B1 := Real.sqrt (Gg + ag)
  set A2 := Real.sqrt (Ff - af)
  set B2 := Real.sqrt (Gg - ag)
  have hA1 : A1 * A1 = Ff + af := Real.mul_self_sqrt hx
  have hB1 : B1 * B1 = Gg + ag := Real.mul_self_sqrt hy
  have hA2 : A2 * A2 = Ff - af := Real.mul_self_sqrt hu
  have hB2 : B2 * B2 = Gg - ag := Real.mul_self_sqrt hv
  have hA10 : 0 ≤ A1 := Real.sqrt_nonneg _
  have hB10 : 0 ≤ B1 := Real.sqrt_nonneg _
  have hA20 : 0 ≤ A2 := Real.sqrt_nonneg _
  have hB20 : 0 ≤ B2 := Real.sqrt_nonneg _
  have hpa : |P + a| ≤ A1 * B1 := by
    have h : |P + a| ^ 2 ≤ (A1 * B1) ^ 2 := by
      calc |P + a| ^ 2 ≤ (Ff + af) * (Gg + ag) := cs1
        _ = (A1 * B1) ^ 2 := by rw [← hA1, ← hB1]; ring
    exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hA10 hB10)).mp h
  have hma : |P - a| ≤ A2 * B2 := by
    have h : |P - a| ^ 2 ≤ (A2 * B2) ^ 2 := by
      calc |P - a| ^ 2 ≤ (Ff - af) * (Gg - ag) := cs2
        _ = (A2 * B2) ^ 2 := by rw [← hA2, ← hB2]; ring
    exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hA20 hB20)).mp h
  -- `A1 B1 + A2 B2 ≤ √((A1² + A2²)(B1² + B2²)) = 2 √(Ff Gg)`
  have hsum2 : A1 * B1 + A2 * B2 ≤ 2 * Real.sqrt (Ff * Gg) := by
    have hFG : 0 ≤ Ff * Gg := by
      have h1 : 0 ≤ Ff := by linarith
      have h2 : 0 ≤ Gg := by linarith
      exact mul_nonneg h1 h2
    have hsq : (A1 * B1 + A2 * B2) ^ 2 ≤ (2 * Real.sqrt (Ff * Gg)) ^ 2 := by
      have hs := Real.sq_sqrt hFG
      have e4 : (2 * Real.sqrt (Ff * Gg)) ^ 2 = 4 * (Ff * Gg) := by rw [mul_pow, hs]; ring
      have e5 : 4 * (Ff * Gg) = (A1 * A1 + A2 * A2) * (B1 * B1 + B2 * B2) := by
        rw [hA1, hA2, hB1, hB2]
        ring
      have hid : (A1 * A1 + A2 * A2) * (B1 * B1 + B2 * B2) - (A1 * B1 + A2 * B2) ^ 2 =
          (A1 * B2 - A2 * B1) ^ 2 := by ring
      have := sq_nonneg (A1 * B2 - A2 * B1)
      rw [e4, e5]
      linarith
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  have habs : |a| ≤ Real.sqrt (Ff * Gg) := by
    rw [abs_le]
    constructor
    · have := neg_abs_le (P + a)
      have := le_abs_self (P - a)
      linarith
    · have := le_abs_self (P + a)
      have := neg_abs_le (P - a)
      linarith
  refine habs.trans (le_of_eq ?_)
  have hf0 : 0 ≤ ∑ x, m x * f x ^ 2 := sum_nonneg fun x _ => mul_nonneg (hm x) (sq_nonneg _)
  have hg0 : 0 ≤ ∑ x, m x * g x ^ 2 := sum_nonneg fun x _ => mul_nonneg (hm x) (sq_nonneg _)
  simp only [Ff, Gg]
  rw [show (κ * ∑ x, m x * f x ^ 2) * (κ * ∑ x, m x * g x ^ 2) =
      κ ^ 2 * ((∑ x, m x * f x ^ 2) * ∑ x, m x * g x ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg κ), Real.sqrt_sq hκ, Real.sqrt_mul hf0]
  ring

end Sarkozy.Variance
