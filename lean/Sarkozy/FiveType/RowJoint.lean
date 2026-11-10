module

public import Sarkozy.FiveType.Rows

/-!
# The row inequality of `lem:five-type`(f) (joint Schur criterion)

Source: `paper/sections/17_completion_repair.tex`, proof of `lem:five-type`(f);
`cor:joint-row-split` (`paper/sections/16_extraction.tex`).

* `joint_block_split`: the form version of `cor:joint-row-split` (first assertion). If
  `E ⪰ -hI`, `(E C; C* E) ⪰ -κ I` and `0 ≤ m ≤ H`, `a_S ≥ H a_D ≥ 0`, then
  `a_S(⟨Φ, EΦ⟩ + ⟨Ψ, EΨ⟩) + 2 m a_D ⟨Φ, CΨ⟩ ≥ -(a_S h + H a_D (κ - h)_+)(‖Φ‖² + ‖Ψ‖²)`.
  The paper applies `cor:joint-row-split` with `𝗄 = max(κ_J, ε_E)`; the proof is the same
  (`m a_D` copies of the joint block plus `a_S - m a_D` copies of `diag(E, E)`). The matrix
  version is `Extraction.joint_row_split`.
* `row_joint`: `Φ_b ≥ 0` under the hypotheses of (f).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiveType

variable {𝔛 : Type*} [Fintype 𝔛]

/-- **`cor:joint-row-split`, form version**, with `𝗄 = max(κ, h)`. -/
theorem joint_block_split {eU eV c SU SV h κ m H aS aD : ℝ} (hSU : 0 ≤ SU) (hSV : 0 ≤ SV)
    (hEU : -h * SU ≤ eU) (hEV : -h * SV ≤ eV) (hJ : -κ * (SU + SV) ≤ eU + 2 * c + eV)
    (hm0 : 0 ≤ m) (hmH : m ≤ H) (haD : 0 ≤ aD) (haS : H * aD ≤ aS) :
    -(aS * h + H * aD * max (κ - h) 0) * (SU + SV) ≤ aS * (eU + eV) + 2 * (m * aD) * c := by
  have hmaD : 0 ≤ m * aD := mul_nonneg hm0 haD
  have hrest : 0 ≤ aS - m * aD := by nlinarith
  have hJ' : -(max κ h) * (SU + SV) ≤ eU + 2 * c + eV := by
    have : κ ≤ max κ h := le_max_left _ _
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left hJ' hmaD
  have h2 := mul_le_mul_of_nonneg_left (add_le_add hEU hEV) hrest
  have hmax : max κ h - h = max (κ - h) 0 := by
    rcases le_total κ h with hk | hk
    · rw [max_eq_right hk, max_eq_right (by linarith)]; ring
    · rw [max_eq_left hk, max_eq_left (by linarith)]
  have h3 : m * aD * (max κ h - h) * (SU + SV) ≤ H * aD * max (κ - h) 0 * (SU + SV) := by
    rw [hmax]
    have hk0 : 0 ≤ max (κ - h) 0 := le_max_right _ _
    have : m * aD ≤ H * aD := mul_le_mul_of_nonneg_right hmH haD
    have := mul_le_mul_of_nonneg_right this (mul_nonneg hk0 (add_nonneg hSU hSV))
    nlinarith
  nlinarith [h1, h2, h3]

/-- **The row inequality of (f)** (joint Schur criterion). The weights enter through
`M = a_S/a_D`, `s = a_R/a_D`, `k = a_C/a_D`, written `a_S = M a_D`, `a_R = s a_D`, `a_C = k a_D`;
`s_J = Mε_E + H(κ_J - ε_E)_+ + Hε_T + (H + H²/t_Y)υ²`. -/
theorem row_joint {μ : FiniteLaw 𝔛} {K TE : 𝔛 → 𝔛 → ℝ} {H υ εT εE κJ : ℝ}
    (hTE : ExactMarginals μ TE) (J : JointData μ TE K H υ εT εE κJ) (hεT : 0 ≤ εT)
    (hεE : 0 ≤ εE)
    {a : Ty → ℝ} {M s k tY : ℝ} (haD : 0 < a .D) (hMa : a .S = M * a .D)
    (hsa : a .R = s * a .D) (hka : a .C = k * a .D) (htY : 0 < tY) (htH : tY ≤ H⁻¹)
    (hM : H + tY ≤ M)
    (hs : M * εE + H * max (κJ - εE) 0 + H * εT + (H + H ^ 2 / tY) * υ ^ 2 ≤ s)
    (hk : 0 ≤ k) (hkM : s ^ 2 ≤ k * M) (U V : 𝔛 → ℝ) (z : ℝ) :
    0 ≤ phiRow μ K TE a U V z := by
  unfold phiRow
  set u := μ.expect U
  set v := μ.expect V
  have hcU := expect_cen μ U
  have hcV := expect_cen μ V
  set σU := nrm μ (cen μ U)
  set σV := nrm μ (cen μ V)
  have hσU : 0 ≤ σU := nrm_nonneg _ _
  have hσV : 0 ≤ σV := nrm_nonneg _ _
  have hH : 0 < H := inv_pos.mp (lt_of_lt_of_le htY htH)
  have hm0 : 0 ≤ J.m := le_trans (inv_nonneg.mpr hH.le) J.m_lower
  have hυ : 0 ≤ υ := le_trans (nrm_nonneg _ _) J.dev0
  -- the fold term
  set α := ip μ (cen μ U) (fun x => J.φ0 x - 1)
  set α' := ip μ (fun x => J.φ2 x - 1) (cen μ V)
  have hUφ : μ.expect (fun x => U x * J.φ0 x) = u + α := by
    have h1 : μ.expect (fun x => U x * J.φ0 x) =
        u * μ.expect J.φ0 + μ.expect (fun x => cen μ U x * J.φ0 x) := by
      rw [← FiniteLaw.expect_const_mul, ← FiniteLaw.expect_add]
      exact μ.expect_congr fun x => by simp only [cen]; ring
    have h2 : μ.expect (fun x => cen μ U x * J.φ0 x) = α := by
      change _ = μ.expect (fun x => cen μ U x * (J.φ0 x - 1))
      have : μ.expect (fun x => cen μ U x * (J.φ0 x - 1)) =
          μ.expect (fun x => cen μ U x * J.φ0 x) - μ.expect (cen μ U) := by
        rw [← FiniteLaw.expect_sub]
        exact μ.expect_congr fun x => by ring
      rw [this, hcU, sub_zero]
    rw [h1, h2, J.mean0, mul_one]
  have hVφ : μ.expect (fun y => J.φ2 y * V y) = v + α' := by
    have h1 : μ.expect (fun y => J.φ2 y * V y) =
        v * μ.expect J.φ2 + μ.expect (fun y => J.φ2 y * cen μ V y) := by
      rw [← FiniteLaw.expect_const_mul, ← FiniteLaw.expect_add]
      exact μ.expect_congr fun y => by simp only [cen]; ring
    have h2 : μ.expect (fun y => J.φ2 y * cen μ V y) = α' := by
      change _ = μ.expect (fun y => (J.φ2 y - 1) * cen μ V y)
      have : μ.expect (fun y => (J.φ2 y - 1) * cen μ V y) =
          μ.expect (fun y => J.φ2 y * cen μ V y) - μ.expect (cen μ V) := by
        rw [← FiniteLaw.expect_sub]
        exact μ.expect_congr fun y => by ring
      rw [this, hcV, sub_zero]
    rw [h1, h2, J.mean2, mul_one]
  have hprod : kf μ (fun x y => J.φ0 x * J.φ2 y) U V =
      μ.expect (fun x => U x * J.φ0 x) * μ.expect (fun y => J.φ2 y * V y) := by
    simp only [kf, FiniteLaw.expect, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  have hlin : kf μ K U V = J.m * (kf μ (fun x y => J.φ0 x * J.φ2 y) U V + kf μ J.C U V +
      kf μ J.R U V) := by
    simp only [kf, J.decomp, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  have hKUV : kf μ K U V = J.m * ((u + α) * (v + α') + kf μ J.C (cen μ U) (cen μ V) +
      kf μ J.R (cen μ U) (cen μ V)) := by
    rw [hlin, hprod, hUφ, hVφ, kf_annihilates J.annC U V, kf_annihilates J.annR U V]
  have hα : |α| ≤ σU * υ := (abs_ip_le _ _ _).trans (mul_le_mul_of_nonneg_left J.dev0 hσU)
  have hα' : |α'| ≤ υ * σV := (abs_ip_le _ _ _).trans (mul_le_mul_of_nonneg_right J.dev2 hσV)
  have hR : |kf μ J.R (cen μ U) (cen μ V)| ≤ εT * σU * σV := J.normR _ _
  -- the matching terms and the joint block
  have hEU : kf μ TE U U = u ^ 2 + eform μ TE (cen μ U) := by
    rw [kf_exact hTE U]; unfold eform; rw [hcU]; ring
  have hEV : kf μ TE V V = v ^ 2 + eform μ TE (cen μ V) := by
    rw [kf_exact hTE V]; unfold eform; rw [hcV]; ring
  have hipU : ip μ U U = u ^ 2 + σU ^ 2 := by rw [ip_self_split, ip_self_eq]
  have hipV : ip μ V V = v ^ 2 + σV ^ 2 := by rw [ip_self_split, ip_self_eq]
  have hblock := joint_block_split (aS := a .S) (aD := a .D) (sq_nonneg σU) (sq_nonneg σV)
    (J.lowerE (cen μ U)) (J.lowerE (cen μ V)) (J.joint (cen μ U) (cen μ V)) hm0 J.m_upper haD.le
    (by rw [hMa]; nlinarith)
  -- scalar bounds
  have hmH := J.m_upper
  have y1 : 2 * |u| * (H * υ * σV) ≤ tY * |u| ^ 2 + (H * υ * σV) ^ 2 / tY := young htY
  have y2 : 2 * |v| * (H * υ * σU) ≤ tY * |v| ^ 2 + (H * υ * σU) ^ 2 / tY := young htY
  rw [sq_abs, show (H * υ * σV) ^ 2 / tY = H ^ 2 / tY * υ ^ 2 * σV ^ 2 by ring] at y1
  rw [sq_abs, show (H * υ * σU) ^ 2 / tY = H ^ 2 / tY * υ ^ 2 * σU ^ 2 by ring] at y2
  have c1 : -(|u| * (H * υ * σV)) ≤ J.m * (u * α') := by
    have h' : |J.m * (u * α')| ≤ |u| * (H * υ * σV) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hm0]
      calc J.m * (|u| * |α'|) ≤ H * (|u| * (υ * σV)) :=
            mul_le_mul hmH (mul_le_mul_of_nonneg_left hα' (abs_nonneg u))
              (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hH.le
        _ = |u| * (H * υ * σV) := by ring
    linarith [neg_abs_le (J.m * (u * α'))]
  have c2 : -(|v| * (H * υ * σU)) ≤ J.m * (v * α) := by
    have h' : |J.m * (v * α)| ≤ |v| * (H * υ * σU) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hm0]
      calc J.m * (|v| * |α|) ≤ H * (|v| * (σU * υ)) :=
            mul_le_mul hmH (mul_le_mul_of_nonneg_left hα (abs_nonneg v))
              (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hH.le
        _ = |v| * (H * υ * σU) := by ring
    linarith [neg_abs_le (J.m * (v * α))]
  have c3 : -(H * (υ ^ 2 + εT) * (σU ^ 2 + σV ^ 2)) ≤
      2 * J.m * (α * α' + kf μ J.R (cen μ U) (cen μ V)) := by
    have h1 : |α * α' + kf μ J.R (cen μ U) (cen μ V)| ≤ (υ ^ 2 + εT) * σU * σV := by
      calc |α * α' + kf μ J.R (cen μ U) (cen μ V)|
          ≤ |α| * |α'| + |kf μ J.R (cen μ U) (cen μ V)| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ (σU * υ) * (υ * σV) + εT * σU * σV := by
            gcongr
        _ = (υ ^ 2 + εT) * σU * σV := by ring
    have hB : 0 ≤ υ ^ 2 + εT := by positivity
    have h2 : 2 * ((υ ^ 2 + εT) * σU * σV) ≤ (υ ^ 2 + εT) * (σU ^ 2 + σV ^ 2) := by
      have h0 := mul_nonneg hB (sq_nonneg (σU - σV))
      have : (υ ^ 2 + εT) * (σU - σV) ^ 2 = (υ ^ 2 + εT) * (σU ^ 2 + σV ^ 2) -
          2 * ((υ ^ 2 + εT) * σU * σV) := by ring
      linarith
    have hP : -((υ ^ 2 + εT) * σU * σV) ≤ α * α' + kf μ J.R (cen μ U) (cen μ V) := by
      linarith [neg_abs_le (α * α' + kf μ J.R (cen μ U) (cen μ V))]
    have g1 := mul_le_mul_of_nonneg_left hP (by linarith : 0 ≤ 2 * J.m)
    have g2 := mul_le_mul_of_nonneg_left h2 hm0
    have g3 := mul_le_mul_of_nonneg_right hmH
      (mul_nonneg hB (add_nonneg (sq_nonneg σU) (sq_nonneg σV)))
    linarith
  -- the fluctuation coefficient and the mean part
  have hs0 : 0 ≤ s := by
    have hM0 : 0 ≤ M := by linarith
    have h1 : 0 ≤ (H + H ^ 2 / tY) * υ ^ 2 := by positivity
    have h2 : 0 ≤ H * max (κJ - εE) 0 := mul_nonneg hH.le (le_max_right _ _)
    have h3 := mul_nonneg hM0 hεE
    have h4 := mul_nonneg hH.le hεT
    linarith
  have hfl : 0 ≤ (s - (M * εE + H * max (κJ - εE) 0 + H * εT + (H + H ^ 2 / tY) * υ ^ 2)) *
      (σU ^ 2 + σV ^ 2) := mul_nonneg (by linarith) (by positivity)
  have hmean := mean_part_nonneg (u := u) (v := v) (z := z) J.m_lower hmH htY hM htH hs0 hk hkM
  have key := mul_nonneg haD.le (add_nonneg hfl hmean)
  rw [hKUV, hEU, hEV, hipU, hipV, hMa, hsa, hka]
  rw [hMa] at hblock
  have e1 := mul_le_mul_of_nonneg_left c1 haD.le
  have e2 := mul_le_mul_of_nonneg_left c2 haD.le
  have e3 := mul_le_mul_of_nonneg_left c3 haD.le
  have e5 := mul_le_mul_of_nonneg_left y1 haD.le
  have e6 := mul_le_mul_of_nonneg_left y2 haD.le
  linarith [key, e1, e2, e3, e5, e6, hblock]

end Sarkozy.FiveType
