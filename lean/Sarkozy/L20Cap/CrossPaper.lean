module

public import Sarkozy.L20Cap.PrimeCapsX1

/-!
# The formal cross constant is below the paper's `x_g` (`prop:l20-pair-gap`)

`paper/sections/20_middle_reference.tex`, `prop:l20-pair-gap`: `x_g = 2rw_g + τ_gN_A` with
`w_g = √30 rρ_{𝐳𝐰}/√g_𝐯 + e_g`, `e_g = √30 r(η + 15q)√g_𝐳/((1 - q)√g_𝐯)`,
`ρ_{𝐳𝐰} = 2r(1 + 𝔪₊)/(√15(1 - q))`, `g_𝐳 = (1 + 14𝔪₊/15)/(1 - q)`, `g_𝐯 = (1 - 2q)/(1 - q)`.

* **`xG_le_xPaper`**: for `p ≥ 2²⁰` and `𝔪₊ ≥ 0`, the formal cross constant `xG` of
  `l20_prime_caps_X1` is at most the paper's `x_g` (`xPaper`). So `hxg` holds with the paper's
  `x_g`, and the gates of `cert:l20-grid` can be used as they are. (The proof bounds the second
  term of `xG` by `98qr/(1 - q)²` and the paper's `2re_g` alone from below by `118qr`.)
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

/-- `g_𝐯 = (1 - 2q)/(1 - q)`. -/
noncomputable def gV (F : Type*) [Fintype F] : ℝ :=
  (1 - 2 * (Fintype.card F : ℝ)⁻¹) / (1 - (Fintype.card F : ℝ)⁻¹)

/-- `g_𝐳 = (1 + 14𝔪₊/15)/(1 - q)`. -/
noncomputable def gZ (F : Type*) [Fintype F] (m : ℝ) : ℝ :=
  (1 + 14 / 15 * m) / (1 - (Fintype.card F : ℝ)⁻¹)

/-- `ρ_{𝐳𝐰} = 2r(1 + 𝔪₊)/(√15(1 - q))`. -/
noncomputable def rhoZW (F : Type*) [Fintype F] (m : ℝ) : ℝ :=
  2 * (Real.sqrt (Fintype.card F))⁻¹ * (1 + m) / (Real.sqrt 15 * (1 - (Fintype.card F : ℝ)⁻¹))

/-- `e_g = √30 r(η + 15q)√g_𝐳/((1 - q)√g_𝐯)`. -/
noncomputable def eG (F : Type*) [Fintype F] (m : ℝ) : ℝ :=
  Real.sqrt 30 * (Real.sqrt (Fintype.card F))⁻¹ * (etaL F + 15 * (Fintype.card F : ℝ)⁻¹) *
    Real.sqrt (gZ F m) / ((1 - (Fintype.card F : ℝ)⁻¹) * Real.sqrt (gV F))

/-- `w_g = √30 rρ_{𝐳𝐰}/√g_𝐯 + e_g`. -/
noncomputable def wG (F : Type*) [Fintype F] (m : ℝ) : ℝ :=
  Real.sqrt 30 * (Real.sqrt (Fintype.card F))⁻¹ * rhoZW F m / Real.sqrt (gV F) + eG F m

/-- **The paper's `x_g = 2rw_g + τ_gN_A`** (`prop:l20-pair-gap`). -/
noncomputable def xPaper (F : Type*) [Fintype F] (m NA : ℝ) : ℝ :=
  2 * (Real.sqrt (Fintype.card F))⁻¹ * wG F m + tauG F m * NA

/-- **`xG ≤ x_g`** for `p ≥ 2²⁰` and `𝔪₊ ≥ 0`. -/
theorem xG_le_xPaper (F : Type*) [Fintype F] {m : ℝ} (hm0 : 0 ≤ m) (NA : ℝ)
    (h20 : (2 : ℝ) ^ 20 ≤ Fintype.card F) : xG F m NA ≤ xPaper F m NA := by
  set P : ℝ := (Fintype.card F : ℝ) with hP
  have hP0 : 0 < P := by linarith [show (0 : ℝ) < 2 ^ 20 by norm_num]
  set s := Real.sqrt P with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hP0
  have hss : s * s = P := Real.mul_self_sqrt hP0.le
  have hs1024 : 1024 ≤ s := by
    rw [hs, show (1024 : ℝ) = Real.sqrt (2 ^ 20) by
      rw [show ((2 : ℝ) ^ 20) = 1024 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt h20
  set q := P⁻¹ with hq
  set r := s⁻¹ with hr
  have hr0 : 0 < r := inv_pos.mpr hs0
  have hqr : q = r * r := by rw [hq, hr, ← hss, mul_inv]
  have hr1 : r ≤ 1 / 1024 := by rw [hr, one_div]; exact inv_anti₀ (by norm_num) hs1024
  have hq1 : q ≤ 1 / 1024 * (1 / 1024) := by rw [hqr]; exact mul_le_mul hr1 hr1 hr0.le (by norm_num)
  have hq0 : 0 < q := inv_pos.mpr hP0
  have h1q : 0 < 1 - q := by linarith
  have h12q : 0 < 1 - 2 * q := by linarith
  have hη : etaL F = 2 * q + 11 * r := by
    unfold etaL
    rw [← hP, ← hs, hq, hr]
    ring
  -- the second term of `xG`
  set T2 := 128 * (etaL F + 1 + 16 * q) / ((1 - q) * (P - 1)) / P *
    Real.sqrt (P * (1 - q) / (2 * (1 - 2 * q))) with hT2
  have hxG : xG F m NA = tauG F m * NA + T2 := by
    unfold xG
    rfl
  have hsq : Real.sqrt (P * (1 - q) / (2 * (1 - 2 * q))) ≤ s * (3 / 4) := by
    rw [show P * (1 - q) / (2 * (1 - 2 * q)) = P * ((1 - q) / (2 * (1 - 2 * q))) by ring,
      Real.sqrt_mul hP0.le]
    refine mul_le_mul_of_nonneg_left ?_ hs0.le
    rw [show (3 / 4 : ℝ) = Real.sqrt ((3 / 4) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hP1 : 0 < P - 1 := by linarith [show (1 : ℝ) < 2 ^ 20 by norm_num]
  have hPm1 : 1 / (P - 1) = q / (1 - q) := by
    rw [hq]
    field_simp
  have hT2le : T2 ≤ 96 * (etaL F + 1 + 16 * q) * q * r / (1 - q) ^ 2 := by
    have hA : 0 ≤ 128 * (etaL F + 1 + 16 * q) / ((1 - q) * (P - 1)) / P := by
      rw [hη]; positivity
    calc T2 ≤ 128 * (etaL F + 1 + 16 * q) / ((1 - q) * (P - 1)) / P * (s * (3 / 4)) :=
          mul_le_mul_of_nonneg_left hsq hA
      _ = 96 * (etaL F + 1 + 16 * q) * (1 / (P - 1)) * (s / P) / (1 - q) := by
          field_simp
          ring
      _ = 96 * (etaL F + 1 + 16 * q) * q * r / (1 - q) ^ 2 := by
          rw [hPm1, show s / P = r by rw [hr, ← hss]; field_simp]
          field_simp
  -- the paper's `2re_g`
  have hgv : 0 < gV F := by unfold gV; rw [← hP, ← hq]; positivity
  have hgv1 : gV F ≤ 1 := by
    unfold gV; rw [← hP, ← hq, div_le_one h1q]; linarith
  have hgz : 1 ≤ gZ F m := by
    unfold gZ; rw [← hP, ← hq, le_div_iff₀ h1q]; nlinarith
  have hsz : 1 ≤ Real.sqrt (gZ F m) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hgz
  have hsv : Real.sqrt (gV F) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hgv1
  have hsv0 : 0 < Real.sqrt (gV F) := Real.sqrt_pos.mpr hgv
  have h30 : (27 / 5 : ℝ) ≤ Real.sqrt 30 := by
    rw [show (27 / 5 : ℝ) = Real.sqrt ((27 / 5) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have heg : 27 / 5 * r * (etaL F + 15 * q) ≤ eG F m := by
    unfold eG
    rw [← hP, ← hs, ← hq, ← hr]
    have hηq : 0 ≤ etaL F + 15 * q := by rw [hη]; positivity
    rw [le_div_iff₀ (mul_pos h1q hsv0)]
    have h1 : 27 / 5 * r * (etaL F + 15 * q) * ((1 - q) * Real.sqrt (gV F)) ≤
        27 / 5 * r * (etaL F + 15 * q) := by
      have : (1 - q) * Real.sqrt (gV F) ≤ 1 := by nlinarith
      have h0 : 0 ≤ 27 / 5 * r * (etaL F + 15 * q) := by positivity
      nlinarith
    have h2 : 27 / 5 * r * (etaL F + 15 * q) ≤
        Real.sqrt 30 * r * (etaL F + 15 * q) * Real.sqrt (gZ F m) := by
      have h0 : 0 ≤ r * (etaL F + 15 * q) := by positivity
      calc 27 / 5 * r * (etaL F + 15 * q) = 27 / 5 * (r * (etaL F + 15 * q)) * 1 := by ring
        _ ≤ Real.sqrt 30 * (r * (etaL F + 15 * q)) * Real.sqrt (gZ F m) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right h30 h0) hsz (by norm_num)
            positivity
        _ = _ := by ring
    linarith
  have hrho : 0 ≤ rhoZW F m := by unfold rhoZW; rw [← hP, ← hq]; positivity
  have hwg : eG F m ≤ wG F m := by
    unfold wG
    have : 0 ≤ Real.sqrt 30 * (Real.sqrt (Fintype.card F))⁻¹ * rhoZW F m / Real.sqrt (gV F) := by
      positivity
    linarith
  have hxP : xPaper F m NA = 2 * r * wG F m + tauG F m * NA := by
    unfold xPaper; rfl
  rw [hxG, hxP]
  -- `T2 ≤ 97qr ≤ 118qr ≤ 2re_g ≤ 2rw_g`
  have hfinal : 96 * (etaL F + 1 + 16 * q) * q * r / (1 - q) ^ 2 ≤ 2 * r * (27 / 5 * r *
      (etaL F + 15 * q)) := by
    rw [div_le_iff₀ (by positivity), hη, hqr]
    have hrr1 : r * r ≤ 1 / 1024 * r := mul_le_mul_of_nonneg_right hr1 hr0.le
    have hA : 96 * (18 * (r * r) + 11 * r + 1) ≤ 98 := by linarith
    have h2 : r * r ≤ 1 / 1024 * (1 / 1024) := mul_le_mul hr1 hr1 hr0.le (by norm_num)
    have h1 : 1 - 2 * (r * r) ≤ (1 - r * r) ^ 2 := by nlinarith [sq_nonneg (r * r)]
    have h3 : 0 ≤ 1 - 2 * (r * r) := by linarith
    have hB : 118 ≤ 54 / 5 * (17 * r + 11) * (1 - r * r) ^ 2 := by
      calc (118 : ℝ) ≤ 54 / 5 * 11 * (1 - 2 * (r * r)) := by linarith
        _ ≤ 54 / 5 * (17 * r + 11) * (1 - r * r) ^ 2 :=
          mul_le_mul (by linarith) h1 h3 (by positivity)
    have hr3 : 0 ≤ r * r * r := by positivity
    have eL : 96 * (2 * (r * r) + 11 * r + 1 + 16 * (r * r)) * (r * r) * r =
        96 * (18 * (r * r) + 11 * r + 1) * (r * r * r) := by ring
    have eR : 2 * r * (27 / 5 * r * (2 * (r * r) + 11 * r + 15 * (r * r))) * (1 - r * r) ^ 2 =
        54 / 5 * (17 * r + 11) * (1 - r * r) ^ 2 * (r * r * r) := by ring
    rw [eL, eR]
    exact mul_le_mul_of_nonneg_right (by linarith) hr3
  have h2r : 0 ≤ 2 * r := mul_nonneg (by norm_num) hr0.le
  have hT : T2 ≤ 2 * r * wG F m :=
    hT2le.trans (hfinal.trans ((mul_le_mul_of_nonneg_left heg h2r).trans
      (mul_le_mul_of_nonneg_left hwg h2r)))
  exact (add_le_add (le_refl (tauG F m * NA)) hT).trans (le_of_eq (add_comm _ _))

end Sarkozy.L20Cap
