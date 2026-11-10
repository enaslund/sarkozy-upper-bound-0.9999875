module

public import Sarkozy.Comparison.Recentering






@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.Structured

open Sarkozy.Recentering

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The bilinear form `𝔟(h, k) = ∫ h k dν̃`, `dν̃ = (1 + f + g) dν`. -/
noncomputable def reweightForm (ν : FiniteLaw (X × Y)) (f : X → ℝ) (g : Y → ℝ) :
    (X → ℝ) →ₗ[ℝ] (Y → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun h k => ν.expect (fun p => (1 + f p.1 + g p.2) * (h p.1 * k p.2)))
    (fun h h' k => by rw [← ν.expect_add]; exact ν.expect_congr fun p => by simp; ring)
    (fun a h k => by
      simp only [smul_eq_mul]
      rw [← ν.expect_const_mul]
      exact ν.expect_congr fun p => by simp; ring)
    (fun h k k' => by rw [← ν.expect_add]; exact ν.expect_congr fun p => by simp; ring)
    (fun a h k => by
      simp only [smul_eq_mul]
      rw [← ν.expect_const_mul]
      exact ν.expect_congr fun p => by simp; ring)

theorem reweightForm_apply (ν : FiniteLaw (X × Y)) (f : X → ℝ) (g : Y → ℝ) (h : X → ℝ)
    (k : Y → ℝ) :
    reweightForm ν f g h k = ν.expect (fun p => (1 + f p.1 + g p.2) * (h p.1 * k p.2)) := rfl

/-- `‖φ h‖ ≤ F ‖h‖` for `|φ| ≤ F`. -/
theorem nrm_mul_le (μ : FiniteLaw X) (φ h : X → ℝ) {F : ℝ} (hF : 0 ≤ F) (hφ : ∀ x, |φ x| ≤ F) :
    nrm μ (fun x => φ x * h x) ≤ F * nrm μ h := by
  unfold nrm ip
  rw [show F = Real.sqrt (F ^ 2) from (Real.sqrt_sq hF).symm, ← Real.sqrt_mul (sq_nonneg F)]
  apply Real.sqrt_le_sqrt
  rw [← μ.expect_const_mul]
  apply μ.expect_mono
  intro x
  have h1 : (φ x) ^ 2 ≤ F ^ 2 := by
    have := abs_le.mp (hφ x)
    nlinarith
  nlinarith [sq_nonneg (h x)]

/-- **`lem:record:additive-cancellation`.** -/
theorem additive_cancellation (ν : FiniteLaw (X × Y)) (νX : FiniteLaw X) (νY : FiniteLaw Y)
    (hmX : ∀ φ : X → ℝ, ν.expect (fun p => φ p.1) = νX.expect φ)
    (hmY : ∀ φ : Y → ℝ, ν.expect (fun p => φ p.2) = νY.expect φ)
    (A : (Y → ℝ) →ₗ[ℝ] (X → ℝ)) (B : (X → ℝ) →ₗ[ℝ] (Y → ℝ))
    (hA : ∀ h k, ν.expect (fun p => h p.1 * k p.2) = ip νX h (A k))
    (hB : ∀ h k, ν.expect (fun p => h p.1 * k p.2) = ip νY (B h) k)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hAρ : ∀ k, νY.expect k = 0 → nrm νX (A k) ≤ ρ * nrm νY k)
    (hBρ : ∀ h, νX.expect h = 0 → nrm νY (B h) ≤ ρ * nrm νX h)
    (f : X → ℝ) (g : Y → ℝ) (hf0 : νX.expect f = 0) (hg0 : νY.expect g = 0)
    (u : X → ℝ) (v : Y → ℝ)
    (hu : ∀ φ : X → ℝ, reweightForm ν f g φ (fun _ => 1) = ip νX φ (fun x => 1 + u x))
    (hv : ∀ φ : Y → ℝ, reweightForm ν f g (fun _ => 1) φ = ip νY (fun y => 1 + v y) φ)
    {UX UY eX eY FX FY : ℝ} (hUX : UX < 1) (hUY : UY < 1) (huU : ∀ x, -UX ≤ u x)
    (hvU : ∀ y, -UY ≤ v y) (he : nrm νX u * nrm νY v ≤ eX * eY)
    (hFX : 0 ≤ FX) (hFY : 0 ≤ FY) (hfF : ∀ x, |f x| ≤ FX) (hgF : ∀ y, |g y| ≤ FY)
    (h : X → ℝ) (k : Y → ℝ) (hh : ip νX h (fun x => 1 + u x) = 0)
    (hk : ip νY (fun y => 1 + v y) k = 0) :
    |reweightForm ν f g h k| ≤
      (ρ * (1 + FX + FY) + eX * eY) / Real.sqrt ((1 - UX) * (1 - UY)) *
        Real.sqrt (νX.expect (fun x => (1 + u x) * h x ^ 2)) *
        Real.sqrt (νY.expect (fun y => (1 + v y) * k y ^ 2)) := by
  set 𝔟 := reweightForm ν f g with h𝔟
  -- `𝔟(1, 1) = 1`
  have h11 : 𝔟 (fun _ => 1) (fun _ => 1) = 1 := by
    rw [h𝔟, reweightForm_apply]
    have : (fun p : X × Y => (1 + f p.1 + g p.2) * (1 * 1)) =
        fun p => 1 + (f p.1 + g p.2) := by funext p; ring
    rw [this, ν.expect_add, ν.expect_const, ν.expect_add, hmX f, hmY g, hf0, hg0]
    ring
  -- the recentering identity
  have hrec := recentering_identity νX νY 𝔟 (fun x => 1 + u x) (fun y => 1 + v y) h11 hu hv hh hk
  set h0 := center νX h with hh0
  set k0 := center νY k with hk0
  have hh0c : νX.expect h0 = 0 := expect_center νX h
  have hk0c : νY.expect k0 = 0 := expect_center νY k
  -- the three terms of `𝔟(h₀, k₀)`
  have hsplit : 𝔟 h0 k0 = ν.expect (fun p => h0 p.1 * k0 p.2) +
      ν.expect (fun p => f p.1 * h0 p.1 * k0 p.2) +
      ν.expect (fun p => h0 p.1 * (g p.2 * k0 p.2)) := by
    rw [h𝔟, reweightForm_apply, ← ν.expect_add, ← ν.expect_add]
    exact ν.expect_congr fun p => by ring
  have hn0 : 0 ≤ nrm νX h0 := Real.sqrt_nonneg _
  have hm0 : 0 ≤ nrm νY k0 := Real.sqrt_nonneg _
  have hAk := hAρ k0 hk0c
  have hBh := hBρ h0 hh0c
  have t1 : |ν.expect (fun p => h0 p.1 * k0 p.2)| ≤ ρ * (nrm νX h0 * nrm νY k0) := by
    rw [hA]
    calc |ip νX h0 (A k0)| ≤ nrm νX h0 * nrm νX (A k0) := abs_ip_le _ _ _
      _ ≤ nrm νX h0 * (ρ * nrm νY k0) := mul_le_mul_of_nonneg_left hAk hn0
      _ = ρ * (nrm νX h0 * nrm νY k0) := by ring
  have t2 : |ν.expect (fun p => f p.1 * h0 p.1 * k0 p.2)| ≤
      FX * ρ * (nrm νX h0 * nrm νY k0) := by
    rw [hA (fun x => f x * h0 x) k0]
    calc |ip νX (fun x => f x * h0 x) (A k0)| ≤ nrm νX (fun x => f x * h0 x) * nrm νX (A k0) :=
          abs_ip_le _ _ _
      _ ≤ (FX * nrm νX h0) * (ρ * nrm νY k0) :=
          mul_le_mul (nrm_mul_le νX f h0 hFX hfF) hAk (Real.sqrt_nonneg _)
            (mul_nonneg hFX hn0)
      _ = FX * ρ * (nrm νX h0 * nrm νY k0) := by ring
  have t3 : |ν.expect (fun p => h0 p.1 * (g p.2 * k0 p.2))| ≤
      FY * ρ * (nrm νX h0 * nrm νY k0) := by
    rw [hB h0 (fun y => g y * k0 y)]
    calc |ip νY (B h0) (fun y => g y * k0 y)| ≤ nrm νY (B h0) * nrm νY (fun y => g y * k0 y) :=
          abs_ip_le _ _ _
      _ ≤ (ρ * nrm νX h0) * (FY * nrm νY k0) :=
          mul_le_mul hBh (nrm_mul_le νY g k0 hFY hgF) (Real.sqrt_nonneg _)
            (mul_nonneg hρ hn0)
      _ = FY * ρ * (nrm νX h0 * nrm νY k0) := by ring
  -- the correction term
  have hcorr : |ip νX (fun x => (1 + u x) - 1) h0 * ip νY (fun y => (1 + v y) - 1) k0| ≤
      eX * eY * (nrm νX h0 * nrm νY k0) := by
    have e1 : (fun x => (1 + u x) - 1) = u := by funext x; ring
    have e2 : (fun y => (1 + v y) - 1) = v := by funext y; ring
    rw [e1, e2, abs_mul]
    calc |ip νX u h0| * |ip νY v k0| ≤ (nrm νX u * nrm νX h0) * (nrm νY v * nrm νY k0) :=
          mul_le_mul (abs_ip_le _ _ _) (abs_ip_le _ _ _) (abs_nonneg _)
            (mul_nonneg (Real.sqrt_nonneg _) hn0)
      _ = (nrm νX u * nrm νY v) * (nrm νX h0 * nrm νY k0) := by ring
      _ ≤ eX * eY * (nrm νX h0 * nrm νY k0) :=
          mul_le_mul_of_nonneg_right he (mul_nonneg hn0 hm0)
  have hmain : |𝔟 h k| ≤ (ρ * (1 + FX + FY) + eX * eY) * (nrm νX h0 * nrm νY k0) := by
    rw [hrec, hsplit]
    calc |ν.expect (fun p => h0 p.1 * k0 p.2) +
          ν.expect (fun p => f p.1 * h0 p.1 * k0 p.2) +
          ν.expect (fun p => h0 p.1 * (g p.2 * k0 p.2)) -
          ip νX (fun x => (1 + u x) - 1) h0 * ip νY (fun y => (1 + v y) - 1) k0|
        ≤ |ν.expect (fun p => h0 p.1 * k0 p.2)| +
          |ν.expect (fun p => f p.1 * h0 p.1 * k0 p.2)| +
          |ν.expect (fun p => h0 p.1 * (g p.2 * k0 p.2))| +
          |ip νX (fun x => (1 + u x) - 1) h0 * ip νY (fun y => (1 + v y) - 1) k0| := by
          have := abs_sub (ν.expect (fun p => h0 p.1 * k0 p.2) +
            ν.expect (fun p => f p.1 * h0 p.1 * k0 p.2) +
            ν.expect (fun p => h0 p.1 * (g p.2 * k0 p.2)))
            (ip νX (fun x => (1 + u x) - 1) h0 * ip νY (fun y => (1 + v y) - 1) k0)
          have h2 := abs_add_le (ν.expect (fun p => h0 p.1 * k0 p.2) +
            ν.expect (fun p => f p.1 * h0 p.1 * k0 p.2))
            (ν.expect (fun p => h0 p.1 * (g p.2 * k0 p.2)))
          have h3 := abs_add_le (ν.expect (fun p => h0 p.1 * k0 p.2))
            (ν.expect (fun p => f p.1 * h0 p.1 * k0 p.2))
          linarith
      _ ≤ ρ * (nrm νX h0 * nrm νY k0) + FX * ρ * (nrm νX h0 * nrm νY k0) +
          FY * ρ * (nrm νX h0 * nrm νY k0) + eX * eY * (nrm νX h0 * nrm νY k0) := by
          linarith
      _ = (ρ * (1 + FX + FY) + eX * eY) * (nrm νX h0 * nrm νY k0) := by ring
  -- the norms of `h₀`, `k₀` against the reweighted marginals
  have hUX' : 0 < 1 - UX := by linarith
  have hUY' : 0 < 1 - UY := by linarith
  have hnh : nrm νX h0 * Real.sqrt (1 - UX) ≤
      Real.sqrt (νX.expect (fun x => (1 + u x) * h x ^ 2)) := by
    have h1 : nrm νX h0 ≤ nrm νX h := nrm_center_le νX h
    have h2 : nrm νX h * Real.sqrt (1 - UX) ≤
        Real.sqrt (νX.expect (fun x => (1 + u x) * h x ^ 2)) := by
      unfold nrm ip
      rw [← Real.sqrt_mul (νX.expect_nonneg fun x => mul_self_nonneg (h x))]
      apply Real.sqrt_le_sqrt
      rw [← νX.expect_mul_const]
      apply νX.expect_mono
      intro x
      have := huU x
      nlinarith [sq_nonneg (h x), mul_self_nonneg (h x)]
    calc nrm νX h0 * Real.sqrt (1 - UX) ≤ nrm νX h * Real.sqrt (1 - UX) :=
          mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
      _ ≤ _ := h2
  have hnk : nrm νY k0 * Real.sqrt (1 - UY) ≤
      Real.sqrt (νY.expect (fun y => (1 + v y) * k y ^ 2)) := by
    have h1 : nrm νY k0 ≤ nrm νY k := nrm_center_le νY k
    have h2 : nrm νY k * Real.sqrt (1 - UY) ≤
        Real.sqrt (νY.expect (fun y => (1 + v y) * k y ^ 2)) := by
      unfold nrm ip
      rw [← Real.sqrt_mul (νY.expect_nonneg fun y => mul_self_nonneg (k y))]
      apply Real.sqrt_le_sqrt
      rw [← νY.expect_mul_const]
      apply νY.expect_mono
      intro y
      have := hvU y
      nlinarith [sq_nonneg (k y), mul_self_nonneg (k y)]
    calc nrm νY k0 * Real.sqrt (1 - UY) ≤ nrm νY k * Real.sqrt (1 - UY) :=
          mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
      _ ≤ _ := h2
  have hK : 0 ≤ ρ * (1 + FX + FY) + eX * eY := by
    have : 0 ≤ nrm νX u * nrm νY v := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith
  have hsq : Real.sqrt ((1 - UX) * (1 - UY)) = Real.sqrt (1 - UX) * Real.sqrt (1 - UY) :=
    Real.sqrt_mul hUX'.le _
  have hpos : 0 < Real.sqrt (1 - UX) * Real.sqrt (1 - UY) :=
    mul_pos (Real.sqrt_pos.mpr hUX') (Real.sqrt_pos.mpr hUY')
  have hprod : nrm νX h0 * nrm νY k0 ≤
      Real.sqrt (νX.expect (fun x => (1 + u x) * h x ^ 2)) *
        Real.sqrt (νY.expect (fun y => (1 + v y) * k y ^ 2)) /
        (Real.sqrt (1 - UX) * Real.sqrt (1 - UY)) := by
    rw [le_div_iff₀ hpos]
    calc nrm νX h0 * nrm νY k0 * (Real.sqrt (1 - UX) * Real.sqrt (1 - UY)) =
          (nrm νX h0 * Real.sqrt (1 - UX)) * (nrm νY k0 * Real.sqrt (1 - UY)) := by ring
      _ ≤ Real.sqrt (νX.expect (fun x => (1 + u x) * h x ^ 2)) *
          Real.sqrt (νY.expect (fun y => (1 + v y) * k y ^ 2)) :=
          mul_le_mul hnh hnk (mul_nonneg hm0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  calc |𝔟 h k| ≤ (ρ * (1 + FX + FY) + eX * eY) * (nrm νX h0 * nrm νY k0) := hmain
    _ ≤ (ρ * (1 + FX + FY) + eX * eY) *
        (Real.sqrt (νX.expect (fun x => (1 + u x) * h x ^ 2)) *
          Real.sqrt (νY.expect (fun y => (1 + v y) * k y ^ 2)) /
          (Real.sqrt (1 - UX) * Real.sqrt (1 - UY))) := mul_le_mul_of_nonneg_left hprod hK
    _ = (ρ * (1 + FX + FY) + eX * eY) / Real.sqrt ((1 - UX) * (1 - UY)) *
        Real.sqrt (νX.expect (fun x => (1 + u x) * h x ^ 2)) *
        Real.sqrt (νY.expect (fun y => (1 + v y) * k y ^ 2)) := by
        rw [hsq]
        ring

end Sarkozy.Structured
