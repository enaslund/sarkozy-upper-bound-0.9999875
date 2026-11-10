module

public import Sarkozy.Interpolation.RieszThorin
public import Sarkozy.DensityUpgrade.ConditioningRange

/-!
# Real bilinear forms: the `L¹`/`L²` endpoints and their interpolation

The interpolation step of `lem:density:edge-moment`
(`paper/sections/30_density_moment_upgrade.tex`) is applied to a *real* bilinear form, with
endpoint bounds stated for real functions. The complex method (`riesz_thorin_bilinear`) needs
the endpoint bounds for complex functions. For a real kernel these follow with the *same*
constants at the two endpoints the paper uses:

* `L¹ × L¹` (`complex_L1_of_real`): testing on point masses bounds every kernel entry,
  `|k x y| ≤ L μ x ν y`, and the triangle inequality gives the complex bound;
* `L² × L²` (`complex_L2_of_real`): rotate so that the value is real, split into real and
  imaginary parts, and apply Cauchy–Schwarz in `ℝ²`.

(For general exponents the complexification of a real form can have a larger norm; it does
not at these two endpoints.)

Main results:
* `interp_L1_L2`: weighted form. If `|B(f,g)| ≤ L ‖f‖₁ ‖g‖₁` and `|B(f,g)| ≤ ρ ‖f‖₂ ‖g‖₂` for
  all real `f, g`, then `|B(f,g)| ≤ L^{1−t} ρ^t ‖f‖_r ‖g‖_r` for `1/r = (1−t) + t/2`;
* `interp_L1_L2_uniform`: the same with the uniform norms `DensityUpgrade.conditioningNorm`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Interpolation

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The weighted real `L^r` (quasi)norm `(∑ x, μ x |f x|^r)^{1/r}`. -/
noncomputable def rNorm (μ : X → ℝ) (r : ℝ) (f : X → ℝ) : ℝ :=
  (∑ x, μ x * |f x| ^ r) ^ r⁻¹

/-- The real bilinear form `∑ x, ∑ y, k x y · f x · g y` of a real kernel. -/
noncomputable def rbil (k : X → Y → ℝ) (f : X → ℝ) (g : Y → ℝ) : ℝ :=
  ∑ x, ∑ y, k x y * f x * g y

/-- The complexified kernel. -/
noncomputable def cK (k : X → Y → ℝ) : X → Y → ℂ := fun x y => (k x y : ℂ)

theorem rNorm_nonneg (μ : X → ℝ) (r : ℝ) (f : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) : 0 ≤ rNorm μ r f :=
  Real.rpow_nonneg (Finset.sum_nonneg fun x _ =>
    mul_nonneg (hμ x) (Real.rpow_nonneg (abs_nonneg _) _)) _

theorem wNorm_ofReal (μ : X → ℝ) (r : ℝ) (f : X → ℝ) :
    wNorm μ r (fun x => (f x : ℂ)) = rNorm μ r f := by
  simp [wNorm, rNorm, Complex.norm_real]

theorem bil_ofReal (k : X → Y → ℝ) (f : X → ℝ) (g : Y → ℝ) :
    bil (cK k) (fun x => (f x : ℂ)) (fun y => (g y : ℂ)) = (rbil k f g : ℂ) := by
  simp [bil, rbil, cK]

theorem wNorm_one (μ : X → ℝ) (u : X → ℂ) : wNorm μ 1 u = ∑ x, μ x * ‖u x‖ := by
  simp [wNorm]

theorem rNorm_one (μ : X → ℝ) (f : X → ℝ) : rNorm μ 1 f = ∑ x, μ x * |f x| := by
  simp [rNorm]

/-- `(S^{1/2})² = S` for `S ≥ 0`. -/
theorem rpow_inv_two_sq {S : ℝ} (hS : 0 ≤ S) : (S ^ (2 : ℝ)⁻¹) ^ 2 = S := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hS]
  norm_num

theorem wNorm_two_sq (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (u : X → ℂ) :
    wNorm μ 2 u ^ 2 = rNorm μ 2 (fun x => (u x).re) ^ 2 + rNorm μ 2 (fun x => (u x).im) ^ 2 := by
  unfold wNorm rNorm
  rw [rpow_inv_two_sq (Finset.sum_nonneg fun x _ =>
      mul_nonneg (hμ x) (Real.rpow_nonneg (norm_nonneg _) _)),
    rpow_inv_two_sq (Finset.sum_nonneg fun x _ =>
      mul_nonneg (hμ x) (Real.rpow_nonneg (abs_nonneg _) _)),
    rpow_inv_two_sq (Finset.sum_nonneg fun x _ =>
      mul_nonneg (hμ x) (Real.rpow_nonneg (abs_nonneg _) _)), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Real.rpow_two, sq_abs, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The real part of the complexified form: `Re B(u, v) = B(Re u, Re v) − B(Im u, Im v)`. -/
theorem re_bil_cK (k : X → Y → ℝ) (u : X → ℂ) (v : Y → ℂ) :
    (bil (cK k) u v).re = rbil k (fun x => (u x).re) (fun y => (v y).re) -
      rbil k (fun x => (u x).im) (fun y => (v y).im) := by
  simp only [bil, rbil, cK, Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **The `L¹ × L¹` kernel bound**: testing on point masses, `|k x y| ≤ L μ x ν y`. -/
theorem kernel_le_of_L1 (μ : X → ℝ) (ν : Y → ℝ) (k : X → Y → ℝ) {L : ℝ}
    (h : ∀ f g, |rbil k f g| ≤ L * rNorm μ 1 f * rNorm ν 1 g) (x : X) (y : Y) :
    |k x y| ≤ L * μ x * ν y := by
  classical
  have hxy := h (fun x' => if x' = x then 1 else 0) (fun y' => if y' = y then 1 else 0)
  have e1 : rbil k (fun x' => if x' = x then 1 else 0) (fun y' => if y' = y then 1 else 0) =
      k x y := by
    simp [rbil]
  have e2 : rNorm μ 1 (fun x' => if x' = x then 1 else 0) = μ x := by
    simp [rNorm_one, apply_ite]
  have e3 : rNorm ν 1 (fun y' => if y' = y then 1 else 0) = ν y := by
    simp [rNorm_one, apply_ite]
  rwa [e1, e2, e3] at hxy

/-- **The `L¹ × L¹` bound from a kernel bound** (the converse of `kernel_le_of_L1`). -/
theorem L1_of_kernel_le (μ : X → ℝ) (ν : Y → ℝ) (k : X → Y → ℝ) {L : ℝ}
    (hk : ∀ x y, |k x y| ≤ L * μ x * ν y) (f : X → ℝ) (g : Y → ℝ) :
    |rbil k f g| ≤ L * rNorm μ 1 f * rNorm ν 1 g := by
  rw [rNorm_one, rNorm_one]
  calc |rbil k f g| ≤ ∑ x, ∑ y, |k x y| * |f x| * |g y| := by
        unfold rbil
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun y _ => ?_)))
        rw [abs_mul, abs_mul]
    _ ≤ ∑ x, ∑ y, (L * μ x * ν y) * |f x| * |g y| := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hk x y) (abs_nonneg _))
          (abs_nonneg _)
    _ = L * (∑ x, μ x * |f x|) * (∑ y, ν y * |g y|) := by
        rw [mul_assoc L, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring

/-- **Complexification at `L¹ × L¹`**: a real kernel bounded by `L` on real `L¹ × L¹` is bounded
by `L` on complex `L¹ × L¹`. -/
theorem complex_L1_of_real (μ : X → ℝ) (ν : Y → ℝ) (k : X → Y → ℝ) {L : ℝ}
    (h : ∀ f g, |rbil k f g| ≤ L * rNorm μ 1 f * rNorm ν 1 g)
    (u : X → ℂ) (v : Y → ℂ) : ‖bil (cK k) u v‖ ≤ L * wNorm μ 1 u * wNorm ν 1 v := by
  have hk := kernel_le_of_L1 μ ν k h
  rw [wNorm_one, wNorm_one]
  calc ‖bil (cK k) u v‖ ≤ ∑ x, ∑ y, ‖cK k x y‖ * ‖u x‖ * ‖v y‖ := norm_bil_le _ _ _
    _ ≤ ∑ x, ∑ y, (L * μ x * ν y) * ‖u x‖ * ‖v y‖ := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        have hxy : ‖cK k x y‖ ≤ L * μ x * ν y := by
          simpa [cK, Complex.norm_real] using hk x y
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hxy (norm_nonneg _))
          (norm_nonneg _)
    _ = L * (∑ x, μ x * ‖u x‖) * (∑ y, ν y * ‖v y‖) := by
        rw [mul_assoc L, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring

/-- **Complexification at `L² × L²`**: a real kernel bounded by `ρ` on real `L² × L²` is
bounded by `ρ` on complex `L² × L²`. -/
theorem complex_L2_of_real (μ : X → ℝ) (ν : Y → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ y, 0 ≤ ν y)
    (k : X → Y → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ f g, |rbil k f g| ≤ ρ * rNorm μ 2 f * rNorm ν 2 g)
    (u : X → ℂ) (v : Y → ℂ) : ‖bil (cK k) u v‖ ≤ ρ * wNorm μ 2 u * wNorm ν 2 v := by
  set w := bil (cK k) u v with hw_def
  have hNu := wNorm_nonneg μ 2 u hμ
  have hNv := wNorm_nonneg ν 2 v hν
  by_cases hw : w = 0
  · rw [hw, norm_zero]
    positivity
  -- rotate so that the value is real and nonnegative
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set ζ : ℂ := (starRingEnd ℂ) w / (‖w‖ : ℂ) with hζ_def
  have hwne : ((‖w‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hwpos.ne'
  have hζ : ‖ζ‖ = 1 := by
    rw [hζ_def, Complex.norm_div, Complex.norm_conj, Complex.norm_real, norm_norm,
      div_self hwpos.ne']
  have hζw : ζ * w = (‖w‖ : ℂ) := by
    rw [hζ_def, div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    field_simp
    push_cast
    ring
  set u' : X → ℂ := fun x => ζ * u x with hu'_def
  have hbil : bil (cK k) u' v = ζ * w := by
    rw [hw_def]
    simp only [bil, hu'_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  have hnorm : wNorm μ 2 u' = wNorm μ 2 u := by
    simp only [wNorm, hu'_def, norm_mul, hζ, one_mul]
  have hre : ‖w‖ = (bil (cK k) u' v).re := by
    rw [hbil, hζw, Complex.ofReal_re]
  set A := rNorm μ 2 (fun x => (u' x).re)
  set B := rNorm μ 2 (fun x => (u' x).im)
  set C := rNorm ν 2 (fun y => (v y).re)
  set D := rNorm ν 2 (fun y => (v y).im)
  have hA : 0 ≤ A := rNorm_nonneg _ _ _ hμ
  have hB : 0 ≤ B := rNorm_nonneg _ _ _ hμ
  have hC : 0 ≤ C := rNorm_nonneg _ _ _ hν
  have hD : 0 ≤ D := rNorm_nonneg _ _ _ hν
  have hu2 : wNorm μ 2 u ^ 2 = A ^ 2 + B ^ 2 := by
    rw [← hnorm]
    exact wNorm_two_sq μ hμ u'
  have hv2 : wNorm ν 2 v ^ 2 = C ^ 2 + D ^ 2 := wNorm_two_sq ν hν v
  -- Cauchy–Schwarz in `ℝ²`
  have hcs : A * C + B * D ≤ wNorm μ 2 u * wNorm ν 2 v := by
    have hsq : (A * C + B * D) ^ 2 ≤ (wNorm μ 2 u * wNorm ν 2 v) ^ 2 := by
      rw [mul_pow, hu2, hv2]
      nlinarith [sq_nonneg (A * D - B * C)]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  have h1 := h (fun x => (u' x).re) (fun y => (v y).re)
  have h2 := h (fun x => (u' x).im) (fun y => (v y).im)
  rw [hre, re_bil_cK]
  calc rbil k (fun x => (u' x).re) (fun y => (v y).re) - rbil k (fun x => (u' x).im)
        (fun y => (v y).im)
      ≤ |rbil k (fun x => (u' x).re) (fun y => (v y).re)| +
          |rbil k (fun x => (u' x).im) (fun y => (v y).im)| := by
        have := le_abs_self (rbil k (fun x => (u' x).re) (fun y => (v y).re))
        have := neg_abs_le (rbil k (fun x => (u' x).im) (fun y => (v y).im))
        linarith
    _ ≤ ρ * A * C + ρ * B * D := add_le_add h1 h2
    _ = ρ * (A * C + B * D) := by ring
    _ ≤ ρ * (wNorm μ 2 u * wNorm ν 2 v) := mul_le_mul_of_nonneg_left hcs hρ
    _ = ρ * wNorm μ 2 u * wNorm ν 2 v := by ring

/-- **Bilinear interpolation between `L¹ × L¹` and `L² × L²`, real form** (the interpolation
step of `lem:density:edge-moment`, weighted version). If a real kernel satisfies
`|B(f,g)| ≤ L ‖f‖₁ ‖g‖₁` and `|B(f,g)| ≤ ρ ‖f‖₂ ‖g‖₂` for all real `f, g`, then for `0 ≤ t ≤ 1`
and `1/r = (1 − t) + t/2`, `|B(f,g)| ≤ L^{1−t} ρ^t ‖f‖_r ‖g‖_r`. -/
theorem interp_L1_L2 (μ : X → ℝ) (ν : Y → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ y, 0 ≤ ν y)
    (k : X → Y → ℝ) {L ρ t r : ℝ} (hL : 0 ≤ L) (hρ : 0 ≤ ρ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr : 1 / r = (1 - t) / 1 + t / 2)
    (h1 : ∀ f g, |rbil k f g| ≤ L * rNorm μ 1 f * rNorm ν 1 g)
    (h2 : ∀ f g, |rbil k f g| ≤ ρ * rNorm μ 2 f * rNorm ν 2 g) (f : X → ℝ) (g : Y → ℝ) :
    |rbil k f g| ≤ L ^ (1 - t) * ρ ^ t * rNorm μ r f * rNorm ν r g := by
  have key := riesz_thorin_bilinear μ ν hμ hν (cK k) one_pos one_pos two_pos two_pos ht0 ht1
    hr hr hL hρ (complex_L1_of_real μ ν k h1) (complex_L2_of_real μ ν hμ hν k hρ h2)
    (fun x => (f x : ℂ)) (fun y => (g y : ℂ))
  rwa [bil_ofReal, Complex.norm_real, Real.norm_eq_abs, wNorm_ofReal, wNorm_ofReal] at key

/-- The uniform weight `1/|X|` gives the norm `DensityUpgrade.conditioningNorm`. -/
theorem rNorm_uniform (r : ℝ) (f : X → ℝ) :
    rNorm (fun _ => (Fintype.card X : ℝ)⁻¹) r f = DensityUpgrade.conditioningNorm r f := by
  unfold rNorm DensityUpgrade.conditioningNorm
  rw [Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [div_eq_inv_mul]

/-- **Bilinear interpolation between `L¹ × L¹` and `L² × L²`, uniform norms** (the
interpolation step of `lem:density:edge-moment`). The norms are the uniform `L^r` norms
`DensityUpgrade.conditioningNorm` on `X` and on `Y`. -/
theorem interp_L1_L2_uniform (k : X → Y → ℝ) {L ρ t r : ℝ} (hL : 0 ≤ L) (hρ : 0 ≤ ρ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hr : 1 / r = (1 - t) / 1 + t / 2)
    (h1 : ∀ f g, |rbil k f g| ≤
      L * DensityUpgrade.conditioningNorm 1 f * DensityUpgrade.conditioningNorm 1 g)
    (h2 : ∀ f g, |rbil k f g| ≤
      ρ * DensityUpgrade.conditioningNorm 2 f * DensityUpgrade.conditioningNorm 2 g)
    (f : X → ℝ) (g : Y → ℝ) :
    |rbil k f g| ≤ L ^ (1 - t) * ρ ^ t * DensityUpgrade.conditioningNorm r f *
      DensityUpgrade.conditioningNorm r g := by
  have hμ : ∀ _ : X, (0 : ℝ) ≤ (Fintype.card X : ℝ)⁻¹ := fun _ => by positivity
  have hν : ∀ _ : Y, (0 : ℝ) ≤ (Fintype.card Y : ℝ)⁻¹ := fun _ => by positivity
  have key := interp_L1_L2 (fun _ => (Fintype.card X : ℝ)⁻¹) (fun _ => (Fintype.card Y : ℝ)⁻¹)
    hμ hν k hL hρ ht0 ht1 hr (by simpa only [rNorm_uniform] using h1)
    (by simpa only [rNorm_uniform] using h2) f g
  simpa only [rNorm_uniform] using key

/-- The `L¹ × L¹` bound for the uniform norms from a kernel bound
`|k x y| ≤ L / (|X| |Y|)`. -/
theorem L1_uniform_of_kernel_le (k : X → Y → ℝ) {L : ℝ}
    (hk : ∀ x y, |k x y| ≤ L * (Fintype.card X : ℝ)⁻¹ * (Fintype.card Y : ℝ)⁻¹)
    (f : X → ℝ) (g : Y → ℝ) :
    |rbil k f g| ≤
      L * DensityUpgrade.conditioningNorm 1 f * DensityUpgrade.conditioningNorm 1 g := by
  simpa only [rNorm_uniform] using L1_of_kernel_le _ _ k hk f g

/-- The uniform `L²` norm as a square root. -/
theorem conditioningNorm_two (f : X → ℝ) :
    DensityUpgrade.conditioningNorm 2 f = Real.sqrt ((∑ a, f a ^ 2) / Fintype.card X) := by
  unfold DensityUpgrade.conditioningNorm
  rw [Real.sqrt_eq_rpow]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Real.rpow_two, sq_abs]
  · norm_num

end Sarkozy.Interpolation
