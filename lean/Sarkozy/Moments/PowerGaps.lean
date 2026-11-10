module

public import Sarkozy.Moments.UniformConvexity
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Power deficits on a bounded alphabet

Comparison of the convex and concave power deficits supplies the scalar
estimate in the typed-mixture argument. The estimates are proved by calculus.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace Sarkozy

theorem convexOn_min_of_deriv_zero {S : Set ℝ} {F : ℝ → ℝ} (hF : ConvexOn ℝ S F)
    {a : ℝ} (ha : a ∈ S) (hder : HasDerivAt F 0 a) {x : ℝ} (hx : x ∈ S) : F a ≤ F x := by
  rcases lt_trichotomy a x with h | h | h
  · have hs := hF.le_slope_of_hasDerivAt ha hx h hder
    rw [slope_def_field] at hs
    have hh := (le_div_iff₀ (sub_pos.mpr h)).mp hs
    linarith
  · rw [h]
  · have hs := hF.slope_le_of_hasDerivAt hx ha h hder
    rw [slope_def_field] at hs
    have hh := (div_le_iff₀ (sub_pos.mpr h)).mp hs
    linarith

noncomputable def powerGap (p t : ℝ) : ℝ := t ^ p - p * t + p - 1

noncomputable def concavePowerGap (p t : ℝ) : ℝ := p * t + 1 - p - t ^ p

theorem concavePowerGap_eq_neg (p t : ℝ) : concavePowerGap p t = -powerGap p t := by
  unfold concavePowerGap powerGap
  ring

@[simp] theorem powerGap_one (p : ℝ) : powerGap p 1 = 0 := by
  simp only [powerGap, Real.one_rpow, mul_one]
  ring

@[simp] theorem concavePowerGap_one (p : ℝ) : concavePowerGap p 1 = 0 := by
  rw [concavePowerGap_eq_neg, powerGap_one, neg_zero]

theorem powerGap_nonneg {p t : ℝ} (hp : 1 ≤ p) (ht : 0 ≤ t) : 0 ≤ powerGap p t := by
  have hh := one_add_mul_self_le_rpow_one_add (s := t - 1) (by linarith) hp
  rw [show 1 + (t - 1) = t by ring] at hh
  unfold powerGap
  linarith

theorem concavePowerGap_nonneg {p t : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (ht : 0 ≤ t) :
    0 ≤ concavePowerGap p t := by
  have hh := rpow_one_add_le_one_add_mul_self (s := t - 1) (by linarith) hp hp1
  rw [show 1 + (t - 1) = t by ring] at hh
  unfold concavePowerGap
  linarith

theorem continuous_powerGap {p : ℝ} (hp : 0 ≤ p) : Continuous (powerGap p) :=
  (((Real.continuous_rpow_const hp).sub (continuous_const.mul continuous_id)).add
    continuous_const).sub continuous_const

theorem hasDerivAt_powerGap (p : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (powerGap p) (p * t ^ (p - 1) - p) t := by
  unfold powerGap
  have hh := (((Real.hasDerivAt_rpow_const (p := p) (Or.inl ht)).fun_sub
    ((hasDerivAt_id t).const_mul p)).add_const p).sub_const 1
  simpa only [id_eq, mul_one] using hh

theorem hasDerivAt_powerGap_deriv (p : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun x => p * x ^ (p - 1) - p) (p * (p - 1) * t ^ (p - 2)) t := by
  have hh := ((Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl ht)).const_mul p).sub_const p
  convert hh using 1
  rw [show p - 1 - 1 = p - 2 by ring]
  ring

/-- A bounded-interval comparison from the ratio of the second derivatives. -/
theorem powerGap_le_curvature {κ ℓ Q t : ℝ} (hκ : 0 < κ) (hκ1 : κ < 1)
    (hℓ : 1 < ℓ) (hQ : 1 ≤ Q) (ht : 0 ≤ t) (htQ : t ≤ Q) :
    powerGap ℓ t ≤ (ℓ * (ℓ - 1) / (κ * (1 - κ)) * Q ^ (ℓ - κ)) * concavePowerGap κ t := by
  let C := ℓ * (ℓ - 1) / (κ * (1 - κ)) * Q ^ (ℓ - κ)
  let F : ℝ → ℝ := fun x => -C * powerGap κ x - powerGap ℓ x
  let F' : ℝ → ℝ := fun x => -C * (κ * x ^ (κ - 1) - κ) - (ℓ * x ^ (ℓ - 1) - ℓ)
  let F'' : ℝ → ℝ := fun x => -C * (κ * (κ - 1) * x ^ (κ - 2)) -
    ℓ * (ℓ - 1) * x ^ (ℓ - 2)
  have hfirst (x : ℝ) (hx : 0 < x) : HasDerivAt F (F' x) x :=
    ((hasDerivAt_powerGap κ hx.ne').const_mul (-C)).fun_sub (hasDerivAt_powerGap ℓ hx.ne')
  have hsecond (x : ℝ) (hx : 0 < x) : HasDerivAt F' (F'' x) x :=
    ((hasDerivAt_powerGap_deriv κ hx.ne').const_mul (-C)).fun_sub
      (hasDerivAt_powerGap_deriv ℓ hx.ne')
  have hcoeff : C * κ * (1 - κ) = ℓ * (ℓ - 1) * Q ^ (ℓ - κ) := by
    dsimp only [C]
    field_simp [hκ.ne', (sub_pos.mpr hκ1).ne']
  have hcurv (x : ℝ) (hx : x ∈ Ioo 0 Q) : 0 ≤ F'' x := by
    have hp := Real.rpow_le_rpow hx.1.le hx.2.le (by linarith : 0 ≤ ℓ - κ)
    have hm := mul_le_mul_of_nonneg_left hp
      (mul_nonneg (mul_nonneg (by linarith) (sub_nonneg.mpr hℓ.le))
        (Real.rpow_nonneg hx.1.le _) : 0 ≤ ℓ * (ℓ - 1) * x ^ (κ - 2))
    have he : x ^ (κ - 2) * x ^ (ℓ - κ) = x ^ (ℓ - 2) := by
      rw [← Real.rpow_add hx.1]
      congr 1
      ring
    have hmain : ℓ * (ℓ - 1) * x ^ (ℓ - 2) ≤
        C * κ * (1 - κ) * x ^ (κ - 2) := by
      rw [hcoeff]
      calc
        _ = (ℓ * (ℓ - 1) * x ^ (κ - 2)) * x ^ (ℓ - κ) := by rw [← he]; ring
        _ ≤ _ := by simpa only [mul_assoc, mul_comm, mul_left_comm] using hm
    dsimp only [F'']
    nlinarith
  have hconv : ConvexOn ℝ (Icc 0 Q) F := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 Q)
      (((continuous_powerGap hκ.le).const_mul (-C)).sub
        (continuous_powerGap (by linarith : 0 ≤ ℓ))).continuousOn (f' := F') (f'' := F'')
    · intro x hx
      have hx' : x ∈ Ioo 0 Q := by simpa only [interior_Icc] using hx
      exact (hfirst x hx'.1).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Ioo 0 Q := by simpa only [interior_Icc] using hx
      exact (hsecond x hx'.1).hasDerivWithinAt
    · intro x hx
      exact hcurv x (by simpa only [interior_Icc] using hx)
  have hzero : HasDerivAt F 0 1 := by
    simpa only [F', Real.one_rpow, mul_one, sub_self, mul_zero] using hfirst 1 (by norm_num)
  have hmin := convexOn_min_of_deriv_zero hconv (show (1 : ℝ) ∈ Icc 0 Q from ⟨by norm_num, hQ⟩)
    hzero (show t ∈ Icc 0 Q from ⟨ht, htQ⟩)
  simp only [F, powerGap_one, mul_zero, sub_zero] at hmin
  rw [concavePowerGap_eq_neg]
  dsimp only [C] at hmin
  nlinarith

end Sarkozy
