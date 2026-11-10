module

public import Sarkozy.FiveType.RowJoint

/-!
# The five-type completion criteria (`lem:five-type`(a)–(c), (f))

Source: `paper/sections/17_completion_repair.tex`, `lem:five-type` and its proof.

* `Datum.form_diff_eq`: the cut form at `ϑ₀` of `𝒬_a - a_L Π_L - a_D Π_{F_0}` at `g` is
  `E_b Φ_b` (the sum of the cut forms of (a), `phiRow`).
* `Datum.below_of_rows`: if `Φ_b ≥ 0` for every `b ∈ supp ν` and every `g`, then
  `𝒬_a - a_L Π_L ⪰_{ϑ₀} a_D Π_{F_0}`; the cut matrix is symmetric because `𝒬_a` and `Π_L` are
  `ϑ₀`-invariant and `Π_{F_0}` is fixed samplewise by `ϑ₀`.
* `Datum.rpAll_of_below`: with the root envelope `Π_L ⪰_{ϑ₀} -δ Π_{F_0}` and `a_D ≥ δ a_L`
  (no condition if `a_L = 0`), `𝒬_a` is reflection positive at every chamber cut `ϑ_i`,
  `i ∈ ℤ/6ℤ` (`lem:commoncut`(i) and chamber transport).
* **(b)** `Datum.full_norm_criterion`, `Datum.full_norm_rp`; graded form `graded_full_norm`.
* **(c)** `Datum.schur_criterion`, `Datum.schur_rp`; `t_Y = 1/2` (`schur_half`); graded form
  `graded_schur`.
* **(f)** `Datum.joint_schur_criterion`, `Datum.joint_schur_rp`; graded form `graded_joint`.

The weights of (c) and (f) enter through `M = a_S/a_D`, `s = a_R/a_D`, `k = a_C/a_D`, as in the
paper. The graded weights are `graded w r t = w_t r^{deg t}`, i.e.
`(w_L, w_D r, w_S r, w_R r², w_C r³)`.

Implicit hypotheses made explicit: `a ≥ 0` (all five weights; the paper's `a ≥ 0`), `e_F ≥ 0`,
`q⊥ ≥ 0`, `ε_T ≥ 0`, `ε_E ≥ 0` (norm or order bounds), `t_Y > 0` (stated).
`e_E ≥ 0` is not needed.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiveType

open Sarkozy.Labellings

namespace Datum

variable {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛] (D : Datum 𝔛)

/-- **`Φ_b`** for the datum: the integrand of the cut form of `𝒬_a - a_L Π_L - a_D Π_{F_0}`. -/
noncomputable def Phi (a : Ty → ℝ) (G : (Half0 → 𝔛) → ℝ) (b : 𝔛) : ℝ :=
  phiRow (D.nub b) (D.TF b) (D.TE b) a (Uf G b) (Vf G b) (zf G b)

/-- **The cut form of `𝒬_a - a_L Π_L - a_D Π_{F_0}` at `ϑ₀` is `E_b Φ_b`** (`lem:five-type`(a),
summed over the components). -/
theorem form_diff_eq (a : Ty → ℝ) (G : (Half0 → 𝔛) → ℝ) :
    (chamberCut 0).form (D.Q a - a .L • D.compL - a .D • D.compF 0) G G =
      D.nu.expect (D.Phi a G) := by
  have hQ : (chamberCut 0).form (D.Q a) G G =
      a .L * (chamberCut 0).form D.compL G G +
      a .D * ((chamberCut 0).form (D.compF 0) G G + (chamberCut 0).form (D.compF 1) G G +
        (chamberCut 0).form (D.compF 2) G G) +
      a .S * ((chamberCut 0).form (D.compE 0) G G + (chamberCut 0).form (D.compE 1) G G) +
      a .R * (((chamberCut 0).form (D.compG 0 0) G G + (chamberCut 0).form (D.compG 0 1) G G +
          (chamberCut 0).form (D.compG 0 2) G G) +
        ((chamberCut 0).form (D.compG 1 0) G G + (chamberCut 0).form (D.compG 1 1) G G +
          (chamberCut 0).form (D.compG 1 2) G G)) +
      a .C * ((chamberCut 0).form D.compC G G + (chamberCut 0).form D.compC G G) := by
    simp only [Datum.Q, sum_Ty, Datum.piT, Fin.sum_univ_three, Fin.sum_univ_two, form_add,
      form_smul]
  rw [form_sub, form_sub, form_smul, form_smul, hQ, D.form_F1, D.form_F2, D.form_E0, D.form_E1,
    D.form_G00, D.form_G01, D.form_G02, D.form_G10, D.form_G11, D.form_G12, D.form_C]
  unfold Datum.Phi phiRow
  simp only [FiniteLaw.expect_add, FiniteLaw.expect_const_mul]
  ring

/-- The difference `𝒬_a - a_L Π_L - a_D Π_{F_0}` is invariant under `ϑ₀`. -/
theorem diff_flip_inv (a : Ty → ℝ) (f : (ZMod 6 → 𝔛) → ℝ) :
    (D.Q a - a .L • D.compL - a .D • D.compF 0) (fun z => f (z ∘ (chamberCut 0).flip)) =
      (D.Q a - a .L • D.compL - a .D • D.compF 0) f := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [flip_inv_of_inv6 (D.Q_inv6 a), flip_inv_of_inv6 D.compL_inv6, D.compF0_flip_inv]

/-- **`𝒬_a - a_L Π_L ⪰_{ϑ₀} a_D Π_{F_0}`** as soon as `Φ_b ≥ 0` on the support of `ν`. -/
theorem below_of_rows (a : Ty → ℝ)
    (hrow : ∀ (G : (Half0 → 𝔛) → ℝ) (b : 𝔛), D.nu.weight b ≠ 0 → 0 ≤ D.Phi a G b) :
    (chamberCut 0).Below (a .D • D.compF 0) (D.Q a - a .L • D.compL) := by
  constructor
  · intro F G
    exact form_symm_of_flip_inv (chamberCut 0) (D.diff_flip_inv a) F G
  · intro G
    change 0 ≤ (chamberCut 0).form (D.Q a - a .L • D.compL - a .D • D.compF 0) G G
    rw [form_diff_eq]
    exact expect_nonneg_supp D.nu fun b hb => hrow G b hb

/-- **From the first claim of (b), (c), (f) to reflection positivity at every chamber cut**, under
the root envelope `Π_L ⪰_{ϑ₀} -δ Π_{F_0}` and `a_D ≥ δ a_L` (no condition if `a_L = 0`). -/
theorem rpAll_of_below (a : Ty → ℝ) (ha : ∀ t, 0 ≤ a t)
    (hB : (chamberCut 0).Below (a .D • D.compF 0) (D.Q a - a .L • D.compL)) {δ : ℝ}
    (hroot : a .L = 0 ∨ ((chamberCut 0).Below (-δ • D.compF 0) D.compL ∧ δ * a .L ≤ a .D)) :
    RPAll (D.Q a) := by
  apply rpAll_of_inv6 (D.Q_inv6 a)
  have hF0 := D.compF0_positive
  rcases hroot with h0 | ⟨henv, hδ⟩
  · have hsum := ReflectionCut.Positive.add hB (hF0.smul (ha .D))
    have he : D.Q a - a .L • D.compL - a .D • D.compF 0 + a .D • D.compF 0 = D.Q a := by
      rw [h0]
      apply LinearMap.ext
      intro f
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        zero_mul]
      ring
    change (chamberCut 0).Positive (D.Q a - a .L • D.compL - a .D • D.compF 0) at hB
    rw [he] at hsum
    exact hsum
  · change (chamberCut 0).Positive (D.compL - -δ • D.compF 0) at henv
    change (chamberCut 0).Positive (D.Q a - a .L • D.compL - a .D • D.compF 0) at hB
    have hsum := (hB.add (henv.smul (ha .L))).add (hF0.smul (by linarith : 0 ≤ a .D - δ * a .L))
    have he : D.Q a - a .L • D.compL - a .D • D.compF 0 + a .L • (D.compL - -δ • D.compF 0) +
        (a .D - δ * a .L) • D.compF 0 = D.Q a := by
      apply LinearMap.ext
      intro f
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    rw [he] at hsum
    exact hsum

/-! ## (b) The full-norm criterion -/

/-- **`lem:five-type`(b), first claim** (full-norm criterion): if `‖T_F^b - J‖ ≤ e_F` and
`‖T_E^b - J‖ ≤ e_E` for every `b ∈ supp ν`, and `a_S ≥ a_D`, `a_R ≥ e_F a_D + e_E a_S`,
`a_C a_S ≥ a_R²`, then `𝒬_a - a_L Π_L ⪰_{ϑ₀} a_D Π_{F_0}`. -/
theorem full_norm_criterion (a : Ty → ℝ) (ha : ∀ t, 0 ≤ a t) {eF eE : ℝ} (heF : 0 ≤ eF)
    (hF : ∀ b, D.nu.weight b ≠ 0 → NormBound (D.nub b) (D.TF b) eF)
    (hE : ∀ b, D.nu.weight b ≠ 0 → NormBound (D.nub b) (D.TE b) eE)
    (h1 : a .D ≤ a .S) (h2 : eF * a .D + eE * a .S ≤ a .R) (h3 : a .R ^ 2 ≤ a .C * a .S) :
    (chamberCut 0).Below (a .D • D.compF 0) (D.Q a - a .L • D.compL) :=
  D.below_of_rows a fun _ b hb =>
    row_full_norm (hF b hb) (hE b hb) heF (ha .D) (ha .C) h1 h2 h3 _ _ _

/-- **`lem:five-type`(b), second claim**: with the root envelope and `a_D ≥ δ a_L` (no
condition if `a_L = 0`), `𝒬_a` is reflection positive at every chamber cut `ϑ_i`. -/
theorem full_norm_rp (a : Ty → ℝ) (ha : ∀ t, 0 ≤ a t) {eF eE : ℝ} (heF : 0 ≤ eF)
    (hF : ∀ b, D.nu.weight b ≠ 0 → NormBound (D.nub b) (D.TF b) eF)
    (hE : ∀ b, D.nu.weight b ≠ 0 → NormBound (D.nub b) (D.TE b) eE)
    (h1 : a .D ≤ a .S) (h2 : eF * a .D + eE * a .S ≤ a .R) (h3 : a .R ^ 2 ≤ a .C * a .S)
    {δ : ℝ} (hroot : a .L = 0 ∨ ((chamberCut 0).Below (-δ • D.compF 0) D.compL ∧ δ * a .L ≤ a .D)) :
    RPAll (D.Q a) :=
  D.rpAll_of_below a ha (D.full_norm_criterion a ha heF hF hE h1 h2 h3) hroot

/-! ## (c) The Schur criterion -/

/-- **`lem:five-type`(c), first claim** (Schur criterion): exact marginals of `T_E^b` with
`‖T_E^b - J‖ ≤ ρ_E`, the fold data of `K_b = T_F^b`, and, with `M = a_S/a_D`, `s = a_R/a_D`,
`k = a_C/a_D` and `t_Y > 0`: `M ≥ H + t_Y`, `t_Y ≤ H⁻¹`, `s ≥ q⊥ + Mρ_E + β²/t_Y`, `kM ≥ s²`.
Then `𝒬_a - a_L Π_L ⪰_{ϑ₀} a_D Π_{F_0}`. -/
theorem schur_criterion (a : Ty → ℝ) (ha : ∀ t, 0 ≤ a t) (haD : 0 < a .D)
    {H β qperp ρE tY : ℝ} (hq : 0 ≤ qperp)
    (hTE : ∀ b, D.nu.weight b ≠ 0 → ExactMarginals (D.nub b) (D.TE b))
    (hρ : ∀ b, D.nu.weight b ≠ 0 → NormBound (D.nub b) (D.TE b) ρE)
    (hK : ∀ b, D.nu.weight b ≠ 0 → FoldData (D.nub b) (D.TF b) H β qperp)
    (htY : 0 < tY) (hM : H + tY ≤ a .S / a .D) (htH : tY ≤ H⁻¹)
    (hs : qperp + a .S / a .D * ρE + β ^ 2 / tY ≤ a .R / a .D)
    (hkM : (a .R / a .D) ^ 2 ≤ a .C / a .D * (a .S / a .D)) :
    (chamberCut 0).Below (a .D • D.compF 0) (D.Q a - a .L • D.compL) := by
  have hne : a .D ≠ 0 := haD.ne'
  refine D.below_of_rows a fun G b hb => row_schur (hTE b hb) (hρ b hb) (hK b hb) hq haD
    (by field_simp) (by field_simp) (by field_simp) htY hM htH hs
    (div_nonneg (ha .C) haD.le) hkM _ _ _

/-- **`lem:five-type`(c), second claim**: under the root envelope and `a_D ≥ δ a_L`, `𝒬_a` is
reflection positive at every chamber cut. -/
theorem schur_rp (a : Ty → ℝ) (ha : ∀ t, 0 ≤ a t) (haD : 0 < a .D)
    {H β qperp ρE tY : ℝ} (hq : 0 ≤ qperp)
    (hTE : ∀ b, D.nu.weight b ≠ 0 → ExactMarginals (D.nub b) (D.TE b))
    (hρ : ∀ b, D.nu.weight b ≠ 0 → NormBound (D.nub b) (D.TE b) ρE)
    (hK : ∀ b, D.nu.weight b ≠ 0 → FoldData (D.nub b) (D.TF b) H β qperp)
    (htY : 0 < tY) (hM : H + tY ≤ a .S / a .D) (htH : tY ≤ H⁻¹)
    (hs : qperp + a .S / a .D * ρE + β ^ 2 / tY ≤ a .R / a .D)
    (hkM : (a .R / a .D) ^ 2 ≤ a .C / a .D * (a .S / a .D))
    {δ : ℝ} (hroot : a .L = 0 ∨ ((chamberCut 0).Below (-δ • D.compF 0) D.compL ∧ δ * a .L ≤ a .D)) :
    RPAll (D.Q a) :=
  D.rpAll_of_below a ha (D.schur_criterion a ha haD hq hTE hρ hK htY hM htH hs hkM) hroot

/-! ## (f) The joint Schur criterion -/

/-- **`lem:five-type`(f), first claim** (joint Schur criterion): exact marginals of `T_E^b`, the
joint data of `K_b = T_F^b`, and, with `M, s, k` as in (c) and `t_Y > 0`: `t_Y ≤ H⁻¹`,
`M ≥ H + t_Y`, `s ≥ s_J = Mε_E + H(κ_J - ε_E)_+ + Hε_T + (H + H²/t_Y)υ²`, `kM ≥ s²`. Then
`𝒬_a - a_L Π_L ⪰_{ϑ₀} a_D Π_{F_0}`. -/
theorem joint_schur_criterion (a : Ty → ℝ) (ha : ∀ t, 0 ≤ a t) (haD : 0 < a .D)
    {H υ εT εE κJ tY : ℝ} (hεT : 0 ≤ εT) (hεE : 0 ≤ εE)
    (hTE : ∀ b, D.nu.weight b ≠ 0 → ExactMarginals (D.nub b) (D.TE b))
    (hJ : ∀ b, D.nu.weight b ≠ 0 → JointData (D.nub b) (D.TE b) (D.TF b) H υ εT εE κJ)
    (htY : 0 < tY) (htH : tY ≤ H⁻¹) (hM : H + tY ≤ a .S / a .D)
    (hs : a .S / a .D * εE + H * max (κJ - εE) 0 + H * εT + (H + H ^ 2 / tY) * υ ^ 2 ≤
      a .R / a .D)
    (hkM : (a .R / a .D) ^ 2 ≤ a .C / a .D * (a .S / a .D)) :
    (chamberCut 0).Below (a .D • D.compF 0) (D.Q a - a .L • D.compL) := by
  have hne : a .D ≠ 0 := haD.ne'
  refine D.below_of_rows a fun G b hb => row_joint (hTE b hb) (hJ b hb) hεT hεE haD
    (by field_simp) (by field_simp) (by field_simp) htY htH hM hs
    (div_nonneg (ha .C) haD.le) hkM _ _ _

/-- **`lem:five-type`(f), second claim**: the conclusions of (c) hold. -/
theorem joint_schur_rp (a : Ty → ℝ) (ha : ∀ t, 0 ≤ a t) (haD : 0 < a .D)
    {H υ εT εE κJ tY : ℝ} (hεT : 0 ≤ εT) (hεE : 0 ≤ εE)
    (hTE : ∀ b, D.nu.weight b ≠ 0 → ExactMarginals (D.nub b) (D.TE b))
    (hJ : ∀ b, D.nu.weight b ≠ 0 → JointData (D.nub b) (D.TE b) (D.TF b) H υ εT εE κJ)
    (htY : 0 < tY) (htH : tY ≤ H⁻¹) (hM : H + tY ≤ a .S / a .D)
    (hs : a .S / a .D * εE + H * max (κJ - εE) 0 + H * εT + (H + H ^ 2 / tY) * υ ^ 2 ≤
      a .R / a .D)
    (hkM : (a .R / a .D) ^ 2 ≤ a .C / a .D * (a .S / a .D))
    {δ : ℝ} (hroot : a .L = 0 ∨ ((chamberCut 0).Below (-δ • D.compF 0) D.compL ∧ δ * a .L ≤ a .D)) :
    RPAll (D.Q a) :=
  D.rpAll_of_below a ha (D.joint_schur_criterion a ha haD hεT hεE hTE hJ htY htH hM hs hkM) hroot

end Datum

/-! ## Graded weights -/

/-- **The graded weights** `(w_L, w_D r, w_S r, w_R r², w_C r³)`: `w_t r^{deg t}`. -/
noncomputable def graded (w : Ty → ℝ) (r : ℝ) (t : Ty) : ℝ := w t * r ^ t.deg

theorem graded_L (w : Ty → ℝ) (r : ℝ) : graded w r .L = w .L := by simp [graded, Ty.deg]
theorem graded_D (w : Ty → ℝ) (r : ℝ) : graded w r .D = w .D * r := by simp [graded, Ty.deg]
theorem graded_S (w : Ty → ℝ) (r : ℝ) : graded w r .S = w .S * r := by simp [graded, Ty.deg]
theorem graded_R (w : Ty → ℝ) (r : ℝ) : graded w r .R = w .R * r ^ 2 := by simp [graded, Ty.deg]
theorem graded_C (w : Ty → ℝ) (r : ℝ) : graded w r .C = w .C * r ^ 3 := by simp [graded, Ty.deg]

/-- **(b), graded form**: for `r > 0`, `e_F = f r`, `e_E = h r`, `δ = d r`, the conditions of (b)
for the graded weights are equivalent to `w_D ≥ d w_L`, `w_S ≥ w_D`, `w_R ≥ f w_D + h w_S`,
`w_C w_S ≥ w_R²` (the last since `3 + 1 = 2 + 2`). -/
theorem graded_full_norm (w : Ty → ℝ) {r f h d : ℝ} (hr : 0 < r) :
    ((d * r) * graded w r .L ≤ graded w r .D ↔ d * w .L ≤ w .D) ∧
    (graded w r .D ≤ graded w r .S ↔ w .D ≤ w .S) ∧
    ((f * r) * graded w r .D + (h * r) * graded w r .S ≤ graded w r .R ↔
      f * w .D + h * w .S ≤ w .R) ∧
    (graded w r .R ^ 2 ≤ graded w r .C * graded w r .S ↔ w .R ^ 2 ≤ w .C * w .S) := by
  simp only [graded_L, graded_D, graded_S, graded_R, graded_C]
  have hr2 : 0 < r ^ 2 := by positivity
  have hr4 : 0 < r ^ 4 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show d * r * w .L = d * w .L * r by ring]
    exact mul_le_mul_iff_of_pos_right hr
  · exact mul_le_mul_iff_of_pos_right hr
  · rw [show f * r * (w .D * r) + h * r * (w .S * r) = (f * w .D + h * w .S) * r ^ 2 by ring]
    exact mul_le_mul_iff_of_pos_right hr2
  · rw [show (w .R * r ^ 2) ^ 2 = w .R ^ 2 * r ^ 4 by ring,
      show w .C * r ^ 3 * (w .S * r) = w .C * w .S * r ^ 4 by ring]
    exact mul_le_mul_iff_of_pos_right hr4

/-- **(c), `t_Y = 1/2`**: `H ≤ 3/2`, `M ≥ 2`, `s ≥ q⊥ + Mρ_E + 2β²` give the conditions of (c). -/
theorem schur_half {H M s qperp ρE β : ℝ} (hH : 0 < H) (hH32 : H ≤ 3 / 2) (hM : 2 ≤ M)
    (hs : qperp + M * ρE + 2 * β ^ 2 ≤ s) :
    H + 1 / 2 ≤ M ∧ (1 / 2 : ℝ) ≤ H⁻¹ ∧ qperp + M * ρE + β ^ 2 / (1 / 2) ≤ s := by
  refine ⟨by linarith, ?_, by rw [div_div_eq_mul_div, div_one]; linarith⟩
  rw [le_inv_comm₀ (by norm_num) hH]
  linarith

/-- **(c), graded form**: for graded weights with `w_D > 0`, `r > 0`, `h = ρ_E/r` and
`f_al = (q⊥ + β²/t_Y)/r`, the conditions `w_S ≥ (H + t_Y)w_D`, `w_R ≥ f_al w_D + h w_S`,
`w_C w_S ≥ w_R²` give `M ≥ H + t_Y`, `s ≥ q⊥ + Mρ_E + β²/t_Y`, `kM ≥ s²` for
`M = a_S/a_D`, `s = a_R/a_D`, `k = a_C/a_D`. -/
theorem graded_schur (w : Ty → ℝ) {r H tY qperp β ρE : ℝ} (hr : 0 < r) (hwD : 0 < w .D)
    (hS : (H + tY) * w .D ≤ w .S)
    (hR : (qperp + β ^ 2 / tY) / r * w .D + ρE / r * w .S ≤ w .R)
    (hC : w .R ^ 2 ≤ w .C * w .S) :
    H + tY ≤ graded w r .S / graded w r .D ∧
    qperp + graded w r .S / graded w r .D * ρE + β ^ 2 / tY ≤ graded w r .R / graded w r .D ∧
    (graded w r .R / graded w r .D) ^ 2 ≤
      graded w r .C / graded w r .D * (graded w r .S / graded w r .D) := by
  simp only [graded_D, graded_S, graded_R, graded_C]
  have hrne : r ≠ 0 := hr.ne'
  have hwne : w .D ≠ 0 := hwD.ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [show w .S * r / (w .D * r) = w .S / w .D by field_simp]
    rw [le_div_iff₀ hwD]
    linarith
  · rw [show w .S * r / (w .D * r) = w .S / w .D by field_simp,
      show w .R * r ^ 2 / (w .D * r) = w .R * r / w .D by field_simp, le_div_iff₀ hwD]
    have h1 : ((qperp + β ^ 2 / tY) / r * w .D + ρE / r * w .S) * r ≤ w .R * r :=
      mul_le_mul_of_nonneg_right hR hr.le
    have h2 : ((qperp + β ^ 2 / tY) / r * w .D + ρE / r * w .S) * r =
        (qperp + w .S / w .D * ρE + β ^ 2 / tY) * w .D := by
      field_simp
      ring
    linarith
  · have e1 : (w .R * r ^ 2 / (w .D * r)) ^ 2 = w .R ^ 2 * r ^ 2 / w .D ^ 2 := by
      field_simp
    have e2 : w .C * r ^ 3 / (w .D * r) * (w .S * r / (w .D * r)) =
        w .C * w .S * r ^ 2 / w .D ^ 2 := by
      field_simp
    rw [e1, e2]
    exact (div_le_div_iff_of_pos_right (by positivity)).mpr
      (mul_le_mul_of_nonneg_right hC (by positivity))

/-- **(f), graded form**: for graded weights with `w_D > 0`, `r > 0`, `ε_E = h r`, `κ_J = k_J r`,
the condition `w_R ≥ f_J w_D + h w_S` (with `f_J = fJ H k_J h r ε_T t_Y υ`) gives `s ≥ s_J`;
the other conditions read as in (c) (`graded_schur`). -/
theorem graded_joint (w : Ty → ℝ) {r H tY h kJ εT υ : ℝ} (hr : 0 < r) (hwD : 0 < w .D)
    (hR : fJ H kJ h r εT tY υ * w .D + h * w .S ≤ w .R) :
    graded w r .S / graded w r .D * (h * r) + H * max (kJ * r - h * r) 0 + H * εT +
      (H + H ^ 2 / tY) * υ ^ 2 ≤ graded w r .R / graded w r .D := by
  simp only [graded_D, graded_S, graded_R]
  have hrne : r ≠ 0 := hr.ne'
  have hwne : w .D ≠ 0 := hwD.ne'
  have hmax : max (kJ * r - h * r) 0 = max (kJ - h) 0 * r := by
    rw [show kJ * r - h * r = (kJ - h) * r by ring]
    rcases le_total (kJ - h) 0 with hk | hk
    · rw [max_eq_right hk, max_eq_right (mul_nonpos_of_nonpos_of_nonneg hk hr.le), zero_mul]
    · rw [max_eq_left hk, max_eq_left (mul_nonneg hk hr.le)]
  rw [hmax, show w .S * r / (w .D * r) = w .S / w .D by field_simp,
    show w .R * r ^ 2 / (w .D * r) = w .R * r / w .D by field_simp, le_div_iff₀ hwD]
  have h1 := mul_le_mul_of_nonneg_right hR hr.le
  have h2 : (fJ H kJ h r εT tY υ * w .D + h * w .S) * r =
      (w .S / w .D * (h * r) + H * (max (kJ - h) 0 * r) + H * εT + (H + H ^ 2 / tY) * υ ^ 2) *
        w .D := by
    unfold fJ
    field_simp
    ring
  linarith

end Sarkozy.FiveType
