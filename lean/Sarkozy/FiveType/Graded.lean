module

public import Sarkozy.FiveType.Criteria

/-!
# The criteria of `lem:five-type` for graded weights

Source: `paper/sections/17_completion_repair.tex`, `lem:five-type`(b), (c), (f), the graded forms
("For `r > 0` and the graded weights `(w_L, w_D r, w_S r, w_R r², w_C r³)` ... the conditions
read ...").

End-to-end versions of `Datum.full_norm_rp`, `Datum.schur_rp`, `Datum.joint_schur_rp` for the
graded weights `graded w r`: the graded conditions on `w` give reflection positivity of
`𝒬_{graded w r}` at every chamber cut. These are the forms checked by the certificates
(`rem:five-type-certificates`).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiveType

namespace Datum

variable {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛] (D : Datum 𝔛)

theorem graded_nonneg {w : Ty → ℝ} (hw : ∀ t, 0 ≤ w t) {r : ℝ} (hr : 0 < r) (t : Ty) :
    0 ≤ graded w r t :=
  mul_nonneg (hw t) (pow_nonneg hr.le _)

/-- The root hypothesis in graded form: `w_L = 0`, or the root envelope with `δ = d r` and
`w_D ≥ d w_L`. -/
theorem graded_root {w : Ty → ℝ} {r d : ℝ} (hr : 0 < r)
    (hroot : w .L = 0 ∨ ((chamberCut 0).Below (-(d * r) • D.compF 0) D.compL ∧ d * w .L ≤ w .D)) :
    graded w r .L = 0 ∨
      ((chamberCut 0).Below (-(d * r) • D.compF 0) D.compL ∧
        (d * r) * graded w r .L ≤ graded w r .D) := by
  rcases hroot with h | ⟨henv, hd⟩
  · left; rw [graded_L]; exact h
  · right
    refine ⟨henv, ?_⟩
    exact ((graded_full_norm w (f := 0) (h := 0) hr).1).mpr hd

/-- **`lem:five-type`(b) in graded form**: with `e_F = f r`, `e_E = h r`, `δ = d r` (`f ≥ 0`),
the conditions `w_D ≥ d w_L` (or `w_L = 0`), `w_S ≥ w_D`, `w_R ≥ f w_D + h w_S`,
`w_C w_S ≥ w_R²` make `𝒬_{graded w r}` reflection positive at every chamber cut. -/
theorem full_norm_rp_graded {w : Ty → ℝ} (hw : ∀ t, 0 ≤ w t) {r f h d : ℝ} (hr : 0 < r)
    (hf : 0 ≤ f)
    (hF : ∀ b, D.nu.weight b ≠ 0 → NormBound (D.nub b) (D.TF b) (f * r))
    (hE : ∀ b, D.nu.weight b ≠ 0 → NormBound (D.nub b) (D.TE b) (h * r))
    (h1 : w .D ≤ w .S) (h2 : f * w .D + h * w .S ≤ w .R) (h3 : w .R ^ 2 ≤ w .C * w .S)
    (hroot : w .L = 0 ∨ ((chamberCut 0).Below (-(d * r) • D.compF 0) D.compL ∧ d * w .L ≤ w .D)) :
    RPAll (D.Q (graded w r)) := by
  obtain ⟨-, g1, g2, g3⟩ := graded_full_norm w (f := f) (h := h) (d := d) hr
  exact D.full_norm_rp (graded w r) (graded_nonneg hw hr) (mul_nonneg hf hr.le) hF hE
    (g1.mpr h1) (g2.mpr h2) (g3.mpr h3) (D.graded_root hr hroot)

/-- **`lem:five-type`(c) in graded form**: with `ρ_E = h r` and
`f_al = (q⊥ + β²/t_Y)/r`, the conditions `w_D ≥ d w_L` (or `w_L = 0`),
`w_S ≥ (H + t_Y) w_D`, `w_R ≥ f_al w_D + h w_S`, `w_C w_S ≥ w_R²`, `t_Y ≤ H⁻¹` make
`𝒬_{graded w r}` reflection positive at every chamber cut. -/
theorem schur_rp_graded {w : Ty → ℝ} (hw : ∀ t, 0 ≤ w t) (hwD : 0 < w .D) {r h d H β qperp tY : ℝ}
    (hr : 0 < r) (hq : 0 ≤ qperp)
    (hTE : ∀ b, D.nu.weight b ≠ 0 → ExactMarginals (D.nub b) (D.TE b))
    (hρ : ∀ b, D.nu.weight b ≠ 0 → NormBound (D.nub b) (D.TE b) (h * r))
    (hK : ∀ b, D.nu.weight b ≠ 0 → FoldData (D.nub b) (D.TF b) H β qperp)
    (htY : 0 < tY) (htH : tY ≤ H⁻¹) (hS : (H + tY) * w .D ≤ w .S)
    (hR : (qperp + β ^ 2 / tY) / r * w .D + h * w .S ≤ w .R) (hC : w .R ^ 2 ≤ w .C * w .S)
    (hroot : w .L = 0 ∨ ((chamberCut 0).Below (-(d * r) • D.compF 0) D.compL ∧ d * w .L ≤ w .D)) :
    RPAll (D.Q (graded w r)) := by
  have hR' : (qperp + β ^ 2 / tY) / r * w .D + (h * r) / r * w .S ≤ w .R := by
    rwa [mul_div_cancel_right₀ h hr.ne']
  obtain ⟨c1, c2, c3⟩ := graded_schur w (ρE := h * r) hr hwD hS hR' hC
  have haD : 0 < graded w r .D := by rw [graded_D]; exact mul_pos hwD hr
  exact D.schur_rp (graded w r) (graded_nonneg hw hr) haD hq hTE hρ hK htY c1 htH c2 c3
    (D.graded_root hr hroot)

/-- **`lem:five-type`(f) in graded form**: with `ε_E = h r`, `κ_J = k_J r` (`h ≥ 0`, `ε_T ≥ 0`)
and `f_J = fJ H k_J h r ε_T t_Y υ`, the conditions `w_D ≥ d w_L` (or `w_L = 0`),
`w_S ≥ (H + t_Y) w_D`, `w_R ≥ f_J w_D + h w_S`, `w_C w_S ≥ w_R²`, `t_Y ≤ H⁻¹` make
`𝒬_{graded w r}` reflection positive at every chamber cut. -/
theorem joint_rp_graded {w : Ty → ℝ} (hw : ∀ t, 0 ≤ w t) (hwD : 0 < w .D)
    {r h d H υ εT kJ tY : ℝ} (hr : 0 < r) (hh : 0 ≤ h) (hεT : 0 ≤ εT)
    (hTE : ∀ b, D.nu.weight b ≠ 0 → ExactMarginals (D.nub b) (D.TE b))
    (hJ : ∀ b, D.nu.weight b ≠ 0 →
      JointData (D.nub b) (D.TE b) (D.TF b) H υ εT (h * r) (kJ * r))
    (htY : 0 < tY) (htH : tY ≤ H⁻¹) (hS : (H + tY) * w .D ≤ w .S)
    (hR : fJ H kJ h r εT tY υ * w .D + h * w .S ≤ w .R) (hC : w .R ^ 2 ≤ w .C * w .S)
    (hroot : w .L = 0 ∨ ((chamberCut 0).Below (-(d * r) • D.compF 0) D.compL ∧ d * w .L ≤ w .D)) :
    RPAll (D.Q (graded w r)) := by
  have hR0 : (0 + (0 : ℝ) ^ 2 / tY) / r * w .D + 0 / r * w .S ≤ w .R := by
    have h0 : 0 ≤ w .R := hw .R
    simpa using h0
  obtain ⟨c1, -, c3⟩ := graded_schur w (qperp := 0) (β := 0) (ρE := 0) hr hwD hS hR0 hC
  have c2 := graded_joint w hr hwD hR
  have haD : 0 < graded w r .D := by rw [graded_D]; exact mul_pos hwD hr
  exact D.joint_schur_rp (graded w r) (graded_nonneg hw hr) haD hεT (mul_nonneg hh hr.le) hTE hJ
    htY htH c1 c2 c3 (D.graded_root hr hroot)

end Datum

end Sarkozy.FiveType
