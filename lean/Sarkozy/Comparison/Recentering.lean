module

public import Sarkozy.FiniteProbability
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Recentring (`lem:recentering`)

`paper/sections/13_cuts_correlations.tex`. Finite probability spaces `(X, μ_X)`, `(Y, μ_Y)`;
`⟪f, g⟫_μ = E_μ[f g]`; `P₀ f = f - E_μ f`.

* `recentering_identity` is (a): for a bilinear form `𝔟` with `𝔟(1, 1) = 1` represented on the
  constants by densities `ρ_L`, `ρ_R` (`𝔟(f, 1) = ⟪f, ρ_L⟫`, `𝔟(1, h) = ⟪ρ_R, h⟫`), and `f`, `h`
  centred against `ρ_L`, `ρ_R`,
  `𝔟(f, h) = 𝔟(P₀f, P₀h) - ⟪ρ_L - 1, P₀f⟫ ⟪ρ_R - 1, P₀h⟫`.
* `recentering_bound` is the norm form of (b): if moreover `|𝔟(P₀f, P₀h)| ≤ c' ‖P₀f‖‖P₀h‖` and
  `‖ρ_L - 1‖ ≤ m_L`, `‖ρ_R - 1‖ ≤ m_R`, then `|𝔟(f, h)| ≤ (c' + m_L m_R) ‖f‖ ‖h‖`. For the
  kernel of (b), `c' = c/z ≤ c/(1-ε)` and `m_• = M_•/z ≤ M_•/(1-ε)`, which gives the paper's
  constant `c/(1-ε) + M_L M_R/(1-ε)²`; `norm_le_of_density_ge` converts reference norms to
  norms in the actual marginals at the cost `e^{l/2}` when the marginal density is `≥ e^{-l}`.
* `density_sub_density` is (c): `ρ₁ - ρ₂ = (m₁ - m₂)/z₁ - (z₁ - z₂) m₂/(z₁ z₂)`, and the norm
  bound that follows.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Recentering

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- `⟪f, g⟫_μ = E_μ[f g]`. -/
noncomputable def ip (μ : FiniteLaw X) (f g : X → ℝ) : ℝ := μ.expect (fun x => f x * g x)

/-- `‖f‖_μ = √(E_μ f²)`. -/
noncomputable def nrm (μ : FiniteLaw X) (f : X → ℝ) : ℝ := Real.sqrt (ip μ f f)

/-- The centring `P₀ f = f - E_μ f`. -/
noncomputable def center (μ : FiniteLaw X) (f : X → ℝ) : X → ℝ := fun x => f x - μ.expect f

theorem ip_comm (μ : FiniteLaw X) (f g : X → ℝ) : ip μ f g = ip μ g f := by
  unfold ip; exact μ.expect_congr fun x => mul_comm _ _

theorem ip_add_left (μ : FiniteLaw X) (f f' g : X → ℝ) :
    ip μ (fun x => f x + f' x) g = ip μ f g + ip μ f' g := by
  unfold ip; rw [← μ.expect_add]; exact μ.expect_congr fun x => by ring

theorem ip_smul_left (μ : FiniteLaw X) (a : ℝ) (f g : X → ℝ) :
    ip μ (fun x => a * f x) g = a * ip μ f g := by
  unfold ip; rw [← μ.expect_const_mul]; exact μ.expect_congr fun x => by ring

theorem ip_one_left (μ : FiniteLaw X) (g : X → ℝ) : ip μ (fun _ => 1) g = μ.expect g := by
  unfold ip; exact μ.expect_congr fun x => one_mul _

theorem expect_one (μ : FiniteLaw X) : μ.expect (fun _ => (1 : ℝ)) = 1 := by
  unfold FiniteLaw.expect; simp [μ.total]

theorem expect_center (μ : FiniteLaw X) (f : X → ℝ) : μ.expect (center μ f) = 0 := by
  unfold center
  rw [μ.expect_sub, show (fun _ : X => μ.expect f) = fun _ => μ.expect f * 1 from by
    funext; ring, μ.expect_const_mul, expect_one]
  ring

theorem ip_center_one (μ : FiniteLaw X) (f : X → ℝ) : ip μ (center μ f) (fun _ => 1) = 0 := by
  unfold ip; simpa using expect_center μ f

/-- **`lem:recentering`(a).** -/
theorem recentering_identity (μX : FiniteLaw X) (μY : FiniteLaw Y)
    (𝔟 : (X → ℝ) →ₗ[ℝ] (Y → ℝ) →ₗ[ℝ] ℝ) (ρL : X → ℝ) (ρR : Y → ℝ)
    (h11 : 𝔟 (fun _ => 1) (fun _ => 1) = 1)
    (hL : ∀ f, 𝔟 f (fun _ => 1) = ip μX f ρL) (hR : ∀ h, 𝔟 (fun _ => 1) h = ip μY ρR h)
    {f : X → ℝ} {h : Y → ℝ} (hf : ip μX f ρL = 0) (hh : ip μY ρR h = 0) :
    𝔟 f h = 𝔟 (center μX f) (center μY h) -
      ip μX (fun x => ρL x - 1) (center μX f) * ip μY (fun y => ρR y - 1) (center μY h) := by
  set f₀ := center μX f
  set h₀ := center μY h
  set a := μX.expect f
  set b := μY.expect h
  have hfdec : f = f₀ + a • (fun _ : X => (1 : ℝ)) := by
    funext x; simp only [f₀, center, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hhdec : h = h₀ + b • (fun _ : Y => (1 : ℝ)) := by
    funext y; simp only [h₀, center, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  -- `⟪1, ρ_L⟫ = 1` and `⟪ρ_R, 1⟫ = 1`
  have hρL1 : ip μX (fun _ => 1) ρL = 1 := by rw [← hL, h11]
  have hρR1 : ip μY ρR (fun _ => 1) = 1 := by rw [← hR, h11]
  -- the constants `a, b` in terms of the centred parts
  have hf₀1 : ip μX f₀ (fun _ => 1) = 0 := ip_center_one μX f
  have hh₀1 : ip μY (fun _ => 1) h₀ = 0 := by rw [ip_comm]; exact ip_center_one μY h
  have hipL : ip μX f₀ ρL = ip μX (fun x => ρL x - 1) f₀ := by
    rw [ip_comm μX (fun x => ρL x - 1) f₀]
    have : ip μX f₀ (fun x => ρL x - 1) = ip μX f₀ ρL - ip μX f₀ (fun _ => 1) := by
      unfold ip; rw [← μX.expect_sub]; exact μX.expect_congr fun x => by ring
    rw [this, hf₀1, sub_zero]
  have hipR : ip μY ρR h₀ = ip μY (fun y => ρR y - 1) h₀ := by
    have : ip μY (fun y => ρR y - 1) h₀ = ip μY ρR h₀ - ip μY (fun _ => 1) h₀ := by
      unfold ip; rw [← μY.expect_sub]; exact μY.expect_congr fun y => by ring
    rw [this, hh₀1, sub_zero]
  have ha : a = -ip μX (fun x => ρL x - 1) f₀ := by
    have h0 : ip μX f ρL = ip μX f₀ ρL + a * ip μX (fun _ => 1) ρL := by
      rw [hfdec, show f₀ + a • (fun _ : X => (1 : ℝ)) = fun x => f₀ x + a * 1 from by
        funext x; simp [smul_eq_mul], ip_add_left, ip_smul_left]
    rw [hρL1, mul_one, hf, hipL] at h0
    linarith
  have hb : b = -ip μY (fun y => ρR y - 1) h₀ := by
    have h0 : ip μY ρR h = ip μY ρR h₀ + b * ip μY ρR (fun _ => 1) := by
      rw [hhdec, ip_comm μY ρR, ip_comm μY ρR (fun _ => 1), ip_comm μY ρR h₀,
        show h₀ + b • (fun _ : Y => (1 : ℝ)) = fun y => h₀ y + b * 1 from by
          funext y; simp [smul_eq_mul], ip_add_left, ip_smul_left]
    rw [hρR1, mul_one, hh, hipR] at h0
    linarith
  have hb1 : 𝔟 f₀ (fun _ => 1) = -a := by rw [hL, hipL, ha, neg_neg]
  have hb2 : 𝔟 (fun _ => 1) h₀ = -b := by rw [hR, hipR, hb, neg_neg]
  rw [hfdec, hhdec]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hb1, hb2, h11, ha, hb]
  ring

/-- Cauchy–Schwarz for `ip`. -/
theorem abs_ip_le (μ : FiniteLaw X) (f g : X → ℝ) : |ip μ f g| ≤ nrm μ f * nrm μ g := by
  unfold nrm ip
  have hcs := μ.cauchy_schwarz_sq f g
  rw [← Real.sqrt_mul (μ.expect_nonneg fun x => mul_self_nonneg (f x))]
  apply Real.abs_le_sqrt
  have h1 : μ.expect (fun x => f x * f x) = μ.expect (fun x => f x ^ 2) :=
    μ.expect_congr fun x => by ring
  have h2 : μ.expect (fun x => g x * g x) = μ.expect (fun x => g x ^ 2) :=
    μ.expect_congr fun x => by ring
  rw [h1, h2]
  exact hcs

theorem nrm_center_le (μ : FiniteLaw X) (f : X → ℝ) : nrm μ (center μ f) ≤ nrm μ f := by
  unfold nrm
  apply Real.sqrt_le_sqrt
  have := μ.expect_sq_sub_mean f
  unfold ip center
  have h1 : μ.expect (fun x => (f x - μ.expect f) * (f x - μ.expect f)) =
      μ.expect (fun x => (f x - μ.expect f) ^ 2) := μ.expect_congr fun x => by ring
  have h2 : μ.expect (fun x => f x * f x) = μ.expect (fun x => f x ^ 2) :=
    μ.expect_congr fun x => by ring
  rw [h1, h2, this]
  nlinarith [sq_nonneg (μ.expect f)]

/-- **`lem:recentering`(b), norm form.** -/
theorem recentering_bound (μX : FiniteLaw X) (μY : FiniteLaw Y)
    (𝔟 : (X → ℝ) →ₗ[ℝ] (Y → ℝ) →ₗ[ℝ] ℝ) (ρL : X → ℝ) (ρR : Y → ℝ)
    (h11 : 𝔟 (fun _ => 1) (fun _ => 1) = 1)
    (hL : ∀ f, 𝔟 f (fun _ => 1) = ip μX f ρL) (hR : ∀ h, 𝔟 (fun _ => 1) h = ip μY ρR h)
    {c' mL mR : ℝ} (hc' : 0 ≤ c')
    (hcen : ∀ f h, |𝔟 (center μX f) (center μY h)| ≤ c' * nrm μX (center μX f) *
      nrm μY (center μY h))
    (hmL : nrm μX (fun x => ρL x - 1) ≤ mL) (hmR : nrm μY (fun y => ρR y - 1) ≤ mR)
    {f : X → ℝ} {h : Y → ℝ} (hf : ip μX f ρL = 0) (hh : ip μY ρR h = 0) :
    |𝔟 f h| ≤ (c' + mL * mR) * nrm μX f * nrm μY h := by
  rw [recentering_identity μX μY 𝔟 ρL ρR h11 hL hR hf hh]
  have hnf := nrm_center_le μX f
  have hnh := nrm_center_le μY h
  have hf0 : 0 ≤ nrm μX (center μX f) := Real.sqrt_nonneg _
  have hh0 : 0 ≤ nrm μY (center μY h) := Real.sqrt_nonneg _
  have hmL0 : 0 ≤ mL := le_trans (Real.sqrt_nonneg _) hmL
  have hmR0 : 0 ≤ mR := le_trans (Real.sqrt_nonneg _) hmR
  have h1 := hcen f h
  have h2 : |ip μX (fun x => ρL x - 1) (center μX f) * ip μY (fun y => ρR y - 1) (center μY h)| ≤
      mL * nrm μX (center μX f) * (mR * nrm μY (center μY h)) := by
    rw [abs_mul]
    apply mul_le_mul _ _ (abs_nonneg _) (by positivity)
    · exact (abs_ip_le μX _ _).trans (mul_le_mul_of_nonneg_right hmL hf0)
    · exact (abs_ip_le μY _ _).trans (mul_le_mul_of_nonneg_right hmR hh0)
  calc |𝔟 (center μX f) (center μY h) - ip μX (fun x => ρL x - 1) (center μX f) *
          ip μY (fun y => ρR y - 1) (center μY h)|
      ≤ |𝔟 (center μX f) (center μY h)| + |ip μX (fun x => ρL x - 1) (center μX f) *
          ip μY (fun y => ρR y - 1) (center μY h)| := abs_sub _ _
    _ ≤ c' * nrm μX (center μX f) * nrm μY (center μY h) +
          mL * nrm μX (center μX f) * (mR * nrm μY (center μY h)) := add_le_add h1 h2
    _ = (c' + mL * mR) * (nrm μX (center μX f) * nrm μY (center μY h)) := by ring
    _ ≤ (c' + mL * mR) * (nrm μX f * nrm μY h) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hnf hnh hh0 (Real.sqrt_nonneg _))
          (add_nonneg hc' (mul_nonneg hmL0 hmR0))
    _ = (c' + mL * mR) * nrm μX f * nrm μY h := by ring

/-- Norms in a reference law against norms in a law with density `≥ e^{-l}`:
`‖f‖_μ ≤ e^{l/2} ‖f‖_{ρμ}`. -/
theorem norm_le_of_density_ge (μ : FiniteLaw X) (ρ : X → ℝ) {l : ℝ}
    (hρ : ∀ x, Real.exp (-l) ≤ ρ x) (f : X → ℝ) :
    nrm μ f ≤ Real.exp (l / 2) * Real.sqrt (μ.expect (fun x => ρ x * f x ^ 2)) := by
  unfold nrm ip
  have hmono : μ.expect (fun x => f x * f x) ≤ Real.exp l * μ.expect (fun x => ρ x * f x ^ 2) := by
    rw [← μ.expect_const_mul]
    refine μ.expect_mono fun x => ?_
    have h1 : 1 ≤ Real.exp l * ρ x := by
      have := mul_le_mul_of_nonneg_left (hρ x) (Real.exp_pos l).le
      rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this
    nlinarith [sq_nonneg (f x)]
  calc Real.sqrt (μ.expect (fun x => f x * f x))
      ≤ Real.sqrt (Real.exp l * μ.expect (fun x => ρ x * f x ^ 2)) := Real.sqrt_le_sqrt hmono
    _ = Real.exp (l / 2) * Real.sqrt (μ.expect (fun x => ρ x * f x ^ 2)) := by
        rw [Real.sqrt_mul (Real.exp_pos l).le, ← Real.exp_half]

omit [Fintype X] in
/-- **`lem:recentering`(c).** -/
theorem density_sub_density (m₁ m₂ : X → ℝ) {z₁ z₂ : ℝ} (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) (x : X) :
    (1 + m₁ x / z₁) - (1 + m₂ x / z₂) = (m₁ x - m₂ x) / z₁ - (z₁ - z₂) * m₂ x / (z₁ * z₂) := by
  field_simp
  ring

end Sarkozy.Recentering
