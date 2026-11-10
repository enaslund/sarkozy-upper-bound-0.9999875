module

public import Sarkozy.FiveType.Invariance

/-!
# The row inequalities of `lem:five-type`(b), (c), (f)

Source: `paper/sections/17_completion_repair.tex`, proof of `lem:five-type`(b), (c), (f), and
`cor:joint-row-split` (`paper/sections/16_extraction.tex`), used in (f) in its form version.

Fix a middle value `b` and write `μ = ν^b`. The integrand of the cut form of
`𝒬_a - a_L Π_L - a_D Π_{F_0}` at `b` (`lem:five-type`(a)) is

  `Φ_b = 2a_D⟨U, T_F V⟩ + a_S(⟨U, T_E U⟩ + ⟨V, T_E V⟩) + a_R(‖U‖² + ‖V‖² + 2z(u + v)) + 2a_C z²`

(`phiRow`, written with the products distributed). This file proves `Φ_b ≥ 0`:
* `row_full_norm`: under the hypotheses of (b) (`‖T_F - J‖ ≤ e_F`, `‖T_E - J‖ ≤ e_E`,
  `a_S ≥ a_D`, `a_R ≥ e_F a_D + e_E a_S`, `a_C a_S ≥ a_R²`);
* `row_schur`: under the hypotheses of (c) (exact marginals of `T_E`, `‖T_E - J‖ ≤ ρ_E`, the fold
  data, and `M ≥ H + t_Y`, `t_Y ≤ H⁻¹`, `s ≥ q⊥ + Mρ_E + β²/t_Y`, `kM ≥ s²`);
* `row_joint`: under the hypotheses of (f) (exact marginals of `T_E`, the joint data, and
  `t_Y ≤ H⁻¹`, `M ≥ H + t_Y`, `s ≥ s_J`, `kM ≥ s²`).

The decomposition `U = u + U°` is `cen`; the scalar steps are `binary_nonneg` (a binary form
with nonnegative diagonal and nonnegative determinant), `young`, and `mean_part_nonneg` (the mean
part of (c) and (f), after the rotation `w_± = (u ± v)/√2`, written with `u ± v`).

Implicit hypotheses made explicit: `q⊥ ≥ 0` (a norm bound), and in `RowJoint.lean` `ε_T ≥ 0`,
`ε_E ≥ 0` (a norm bound and an order bound). `H > 0` is not assumed: it follows from
`0 < t_Y ≤ H⁻¹`. `ρ_E ≥ 0` follows from `‖T_E - J‖ ≤ ρ_E` at `Φ = Ψ = 𝟙`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiveType

/-! ## Scalar lemmas -/

/-- A binary form `A x² + 2B xy + C y²` with `A, C ≥ 0` and `B² ≤ AC` is nonnegative. -/
theorem binary_nonneg {A B C x y : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : B ^ 2 ≤ A * C) :
    0 ≤ A * x ^ 2 + 2 * B * x * y + C * y ^ 2 := by
  rcases hA.eq_or_lt with h | h
  · subst h
    have hB0 : B = 0 := by nlinarith [sq_nonneg B]
    subst hB0
    nlinarith [sq_nonneg y]
  · have key : A * (A * x ^ 2 + 2 * B * x * y + C * y ^ 2) =
        (A * x + B * y) ^ 2 + (A * C - B ^ 2) * y ^ 2 := by ring
    have hprod : 0 ≤ A * (A * x ^ 2 + 2 * B * x * y + C * y ^ 2) := by
      rw [key]
      exact add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))
    exact (mul_nonneg_iff_of_pos_left h).mp hprod

/-- Young's inequality with an allowance `t > 0`: `2ab ≤ t a² + b²/t`. -/
theorem young {t a b : ℝ} (ht : 0 < t) : 2 * a * b ≤ t * a ^ 2 + b ^ 2 / t := by
  have key : t * a ^ 2 + b ^ 2 / t - 2 * a * b = (t * a - b) ^ 2 / t := by
    field_simp
    ring
  have : 0 ≤ (t * a - b) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
  linarith

/-- **The mean part of (c) and (f)**: with `A = M + s - t_Y`, the form
`A(u² + v²) + 2muv + 2sz(u + v) + 2kz²` is nonnegative when `m ∈ [H⁻¹, H]`, `M ≥ H + t_Y`,
`t_Y ≤ H⁻¹`, `s, k ≥ 0` and `kM ≥ s²`. In the paper's rotation: `A - m ≥ s ≥ 0`,
`A + m ≥ M`, and the form in `(w_+, z)` has determinant `≥ 2(kM - s²) ≥ 0`. -/
theorem mean_part_nonneg {H M tY m s k u v z : ℝ} (hm1 : H⁻¹ ≤ m) (hm2 : m ≤ H)
    (htY0 : 0 < tY) (hM : H + tY ≤ M) (htY : tY ≤ H⁻¹) (hs : 0 ≤ s) (hk : 0 ≤ k)
    (hkM : s ^ 2 ≤ k * M) :
    0 ≤ (M + s - tY) * (u ^ 2 + v ^ 2) + 2 * m * u * v + 2 * s * z * (u + v) + 2 * k * z ^ 2 := by
  have hAm : 0 ≤ M + s - tY - m := by linarith
  have hAp : M ≤ M + s - tY + m := by linarith
  have hM0 : 0 ≤ M := by
    have hH : 0 < H := inv_pos.mp (lt_of_lt_of_le htY0 htY)
    linarith
  have hbin : 0 ≤ (1 / 2 * (M + s - tY + m)) * (u + v) ^ 2 + 2 * s * (u + v) * z +
      (2 * k) * z ^ 2 := by
    apply binary_nonneg (by linarith) (by linarith)
    nlinarith
  have hdiff : 0 ≤ 1 / 2 * (M + s - tY - m) * (u - v) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  nlinarith [hbin, hdiff]

/-! ## `L²(μ)` facts -/

section L2

variable {𝔛 : Type*} [Fintype 𝔛]

theorem ip_self_eq (μ : FiniteLaw 𝔛) (U : 𝔛 → ℝ) : ip μ U U = nrm μ U ^ 2 := by
  unfold nrm
  rw [Real.sq_sqrt (show 0 ≤ ip μ U U from μ.expect_nonneg fun x => mul_self_nonneg (U x))]

theorem nrm_nonneg (μ : FiniteLaw 𝔛) (U : 𝔛 → ℝ) : 0 ≤ nrm μ U := Real.sqrt_nonneg _

/-- Cauchy–Schwarz in `L²(μ)`. -/
theorem abs_ip_le (μ : FiniteLaw 𝔛) (U V : 𝔛 → ℝ) : |ip μ U V| ≤ nrm μ U * nrm μ V := by
  have h := μ.abs_expect_mul_le U V
  simp only [sq] at h
  exact h

theorem expect_cen (μ : FiniteLaw 𝔛) (U : 𝔛 → ℝ) : μ.expect (cen μ U) = 0 := by
  unfold cen
  rw [FiniteLaw.expect_sub, FiniteLaw.expect_const]
  ring

theorem eq_add_cen (μ : FiniteLaw 𝔛) (U : 𝔛 → ℝ) : U = fun x => μ.expect U + cen μ U x := by
  funext x
  unfold cen
  ring

/-- `‖U‖² = u² + ‖U°‖²`. -/
theorem ip_self_split (μ : FiniteLaw 𝔛) (U : 𝔛 → ℝ) :
    ip μ U U = μ.expect U ^ 2 + ip μ (cen μ U) (cen μ U) := by
  unfold ip cen
  have h := μ.expect_sq_sub_mean U
  simp only [sq] at h
  rw [h]
  ring

/-- Two functions that agree on the support of `μ` have the same expectation. -/
theorem expect_congr_supp (μ : FiniteLaw 𝔛) {f g : 𝔛 → ℝ}
    (h : ∀ x, μ.weight x ≠ 0 → f x = g x) : μ.expect f = μ.expect g := by
  unfold FiniteLaw.expect
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : μ.weight x = 0
  · rw [hx, zero_mul, zero_mul]
  · rw [h x hx]

/-- A function nonnegative on the support has a nonnegative expectation. -/
theorem expect_nonneg_supp (μ : FiniteLaw 𝔛) {f : 𝔛 → ℝ}
    (h : ∀ x, μ.weight x ≠ 0 → 0 ≤ f x) : 0 ≤ μ.expect f := by
  unfold FiniteLaw.expect
  refine Finset.sum_nonneg fun x _ => ?_
  by_cases hx : μ.weight x = 0
  · rw [hx, zero_mul]
  · exact mul_nonneg (μ.nonneg x) (h x hx)

/-- Bilinear expansion of `⟨u + P, T(v + R)⟩`. -/
theorem kf_add_const (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) (u v : ℝ) (P R : 𝔛 → ℝ) :
    kf μ T (fun x => u + P x) (fun y => v + R y) =
      u * v * kf μ T (fun _ => 1) (fun _ => 1) + u * kf μ T (fun _ => 1) R +
        v * kf μ T P (fun _ => 1) + kf μ T P R := by
  simp only [kf, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

/-- `⟨𝟙, TR⟩ = ⟨T*𝟙, R⟩`. -/
theorem kf_one_left (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) (R : 𝔛 → ℝ) :
    kf μ T (fun _ => 1) R = ip μ (kone' μ T) R := by
  simp only [kf, ip, kone', FiniteLaw.expect, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  ring

/-- `⟨P, T𝟙⟩`. -/
theorem kf_one_right (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) (P : 𝔛 → ℝ) :
    kf μ T P (fun _ => 1) = ip μ P (kone μ T) := by
  simp only [kf, ip, kone, FiniteLaw.expect, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

/-- Against a centred function, a function may be replaced by its centred part. -/
theorem ip_cen_left (μ : FiniteLaw 𝔛) (f R : 𝔛 → ℝ) (hR : μ.expect R = 0) :
    ip μ f R = ip μ (cen μ f) R := by
  unfold ip cen
  have : μ.expect (fun x => (f x - μ.expect f) * R x) =
      μ.expect (fun x => f x * R x) - μ.expect f * μ.expect R := by
    rw [← FiniteLaw.expect_const_mul, ← FiniteLaw.expect_sub]
    exact μ.expect_congr fun x => by ring
  rw [this, hR, mul_zero, sub_zero]

theorem ip_comm (μ : FiniteLaw 𝔛) (f g : 𝔛 → ℝ) : ip μ f g = ip μ g f :=
  μ.expect_congr fun _ => mul_comm _ _

/-- A kernel that annihilates the constants sees only centred parts. -/
theorem kf_annihilates {μ : FiniteLaw 𝔛} {C : 𝔛 → 𝔛 → ℝ} (hC : Annihilates μ C) (U V : 𝔛 → ℝ) :
    kf μ C U V = kf μ C (cen μ U) (cen μ V) := by
  have hl : kf μ C (fun _ => 1) (cen μ V) = 0 := by
    rw [kf_one_left]
    exact (expect_congr_supp μ fun y hy => by rw [hC.2 y hy, zero_mul]).trans
      (μ.expect_const 0)
  have hr : kf μ C (cen μ U) (fun _ => 1) = 0 := by
    rw [kf_one_right]
    exact (expect_congr_supp μ fun x hx => by rw [hC.1 x hx, mul_zero]).trans
      (μ.expect_const 0)
  have h11 : kf μ C (fun _ => 1) (fun _ => 1) = 0 := by
    rw [kf_one_left]
    exact (expect_congr_supp μ fun y hy => by rw [hC.2 y hy, zero_mul]).trans
      (μ.expect_const 0)
  conv_lhs => rw [eq_add_cen μ U, eq_add_cen μ V]
  rw [kf_add_const, hl, hr, h11]
  ring

/-- With exact marginals, `⟨U, TU⟩ = u² + ⟨U°, TU°⟩`. -/
theorem kf_exact {μ : FiniteLaw 𝔛} {T : 𝔛 → 𝔛 → ℝ} (hT : ExactMarginals μ T) (U : 𝔛 → ℝ) :
    kf μ T U U = μ.expect U ^ 2 + kf μ T (cen μ U) (cen μ U) := by
  have hc := expect_cen μ U
  have hl : kf μ T (fun _ => 1) (cen μ U) = 0 := by
    rw [kf_one_left]
    exact (expect_congr_supp μ fun y hy => by rw [hT.2 y hy, one_mul]).trans hc
  have hr : kf μ T (cen μ U) (fun _ => 1) = 0 := by
    rw [kf_one_right]
    exact (expect_congr_supp μ fun x hx => by rw [hT.1 x hx, mul_one]).trans hc
  have h11 : kf μ T (fun _ => 1) (fun _ => 1) = 1 := by
    rw [kf_one_left]
    exact (expect_congr_supp μ fun y hy => by rw [hT.2 y hy, one_mul]).trans
      (μ.expect_const 1)
  conv_lhs => rw [eq_add_cen μ U]
  rw [kf_add_const, hl, hr, h11]
  ring

end L2

/-! ## The integrand at one middle value -/

variable {𝔛 : Type*} [Fintype 𝔛]

/-- **`Φ_b`**, the integrand of the cut form of `𝒬_a - a_L Π_L - a_D Π_{F_0}` at `b`
(proof of `lem:five-type`(b)), on `L²(μ)`, `μ = ν^b`, with `U = U_b`, `V = V_b`, `z = z_b`. -/
noncomputable def phiRow (μ : FiniteLaw 𝔛) (TF TE : 𝔛 → 𝔛 → ℝ) (a : Ty → ℝ) (U V : 𝔛 → ℝ)
    (z : ℝ) : ℝ :=
  2 * a .D * kf μ TF U V + a .S * kf μ TE U U + a .S * kf μ TE V V + a .R * ip μ U U +
    a .R * ip μ V V + 2 * a .R * (z * μ.expect U) + 2 * a .R * (z * μ.expect V) +
    2 * a .C * z ^ 2

/-- **The row inequality of (b)** (full-norm criterion). -/
theorem row_full_norm {μ : FiniteLaw 𝔛} {TF TE : 𝔛 → 𝔛 → ℝ} {eF eE : ℝ}
    (hF : NormBound μ TF eF) (hE : NormBound μ TE eE) (heF : 0 ≤ eF)
    {a : Ty → ℝ} (haD : 0 ≤ a .D) (haC : 0 ≤ a .C) (h1 : a .D ≤ a .S)
    (h2 : eF * a .D + eE * a .S ≤ a .R) (h3 : a .R ^ 2 ≤ a .C * a .S) (U V : 𝔛 → ℝ) (z : ℝ) :
    0 ≤ phiRow μ TF TE a U V z := by
  unfold phiRow
  set u := μ.expect U
  set v := μ.expect V
  set nU := nrm μ U
  set nV := nrm μ V
  have hnU : 0 ≤ nU := nrm_nonneg μ U
  have hnV : 0 ≤ nV := nrm_nonneg μ V
  have hipU : ip μ U U = nU ^ 2 := ip_self_eq μ U
  have hipV : ip μ V V = nV ^ 2 := ip_self_eq μ V
  have kF := hF.lower U V
  have kEU := hE.lower U U
  have kEV := hE.lower V V
  have haS : 0 ≤ a .S := le_trans haD h1
  have t1 : 2 * a .D * (u * v - eF * nU * nV) ≤ 2 * a .D * kf μ TF U V :=
    mul_le_mul_of_nonneg_left kF (by linarith)
  have t2 : a .S * (u * u - eE * nU * nU) ≤ a .S * kf μ TE U U :=
    mul_le_mul_of_nonneg_left kEU haS
  have t3 : a .S * (v * v - eE * nV * nV) ≤ a .S * kf μ TE V V :=
    mul_le_mul_of_nonneg_left kEV haS
  have t4 : 2 * (a .D * eF) * nU * nV ≤ (a .D * eF) * (nU ^ 2 + nV ^ 2) := by
    have h0 : 0 ≤ a .D * eF := mul_nonneg haD heF
    nlinarith [sq_nonneg (nU - nV), mul_nonneg h0 (sq_nonneg (nU - nV))]
  have t5 : 0 ≤ (a .R - eF * a .D - eE * a .S) * (nU ^ 2 + nV ^ 2) :=
    mul_nonneg (by linarith) (by positivity)
  have t6 : 0 ≤ 1 / 2 * a .D * (u + v) ^ 2 + 1 / 2 * (a .S - a .D) * (u - v) ^ 2 :=
    add_nonneg (mul_nonneg (by linarith) (sq_nonneg _))
      (mul_nonneg (by linarith) (sq_nonneg _))
  have t7 : 0 ≤ (1 / 2 * a .S) * (u + v) ^ 2 + 2 * a .R * (u + v) * z + (2 * a .C) * z ^ 2 :=
    binary_nonneg (by linarith) (by linarith) (by nlinarith)
  rw [hipU, hipV]
  nlinarith [t1, t2, t3, t4, t5, t6, t7]

/-- **The row inequality of (c)** (Schur criterion). The weights enter through
`M = a_S/a_D`, `s = a_R/a_D`, `k = a_C/a_D`, written `a_S = M a_D`, `a_R = s a_D`, `a_C = k a_D`. -/
theorem row_schur {μ : FiniteLaw 𝔛} {K TE : 𝔛 → 𝔛 → ℝ} {H β qperp ρE : ℝ}
    (hTE : ExactMarginals μ TE) (hρ : NormBound μ TE ρE) (hK : FoldData μ K H β qperp)
    (hq : 0 ≤ qperp) {a : Ty → ℝ} {M s k tY : ℝ} (haD : 0 < a .D) (hMa : a .S = M * a .D)
    (hsa : a .R = s * a .D) (hka : a .C = k * a .D) (htY : 0 < tY) (hM : H + tY ≤ M)
    (htH : tY ≤ H⁻¹) (hs : qperp + M * ρE + β ^ 2 / tY ≤ s) (hk : 0 ≤ k) (hkM : s ^ 2 ≤ k * M)
    (U V : 𝔛 → ℝ) (z : ℝ) : 0 ≤ phiRow μ K TE a U V z := by
  unfold phiRow
  set u := μ.expect U
  set v := μ.expect V
  set m := kf μ K (fun _ => 1) (fun _ => 1)
  have hcU := expect_cen μ U
  have hcV := expect_cen μ V
  set σU := nrm μ (cen μ U)
  set σV := nrm μ (cen μ V)
  have hσU : 0 ≤ σU := nrm_nonneg _ _
  have hσV : 0 ≤ σV := nrm_nonneg _ _
  have hβ : 0 ≤ β := le_trans (nrm_nonneg _ _) hK.row
  -- the fold term
  have hKUV : kf μ K U V = u * v * m + u * ip μ (cen μ (kone' μ K)) (cen μ V) +
      v * ip μ (cen μ U) (cen μ (kone μ K)) + kf μ K (cen μ U) (cen μ V) := by
    conv_lhs => rw [eq_add_cen μ U, eq_add_cen μ V]
    rw [kf_add_const, kf_one_left μ K (cen μ V), kf_one_right μ K (cen μ U),
      ip_cen_left μ (kone' μ K) (cen μ V) hcV, ip_comm μ (cen μ U) (kone μ K),
      ip_cen_left μ (kone μ K) (cen μ U) hcU, ip_comm μ (cen μ (kone μ K)) (cen μ U)]
  have hb1 : |ip μ (cen μ (kone' μ K)) (cen μ V)| ≤ β * σV :=
    (abs_ip_le _ _ _).trans (mul_le_mul_of_nonneg_right hK.col hσV)
  have hb2 : |ip μ (cen μ U) (cen μ (kone μ K))| ≤ σU * β :=
    (abs_ip_le _ _ _).trans (mul_le_mul_of_nonneg_left hK.row hσU)
  have hb3 : |kf μ K (cen μ U) (cen μ V)| ≤ qperp * σU * σV := hK.perp _ _ hcU hcV
  -- the matching terms
  have hEU : kf μ TE U U = u ^ 2 + kf μ TE (cen μ U) (cen μ U) := kf_exact hTE U
  have hEV : kf μ TE V V = v ^ 2 + kf μ TE (cen μ V) (cen μ V) := kf_exact hTE V
  have hEU' := hρ.lower (cen μ U) (cen μ U)
  have hEV' := hρ.lower (cen μ V) (cen μ V)
  rw [hcU] at hEU'
  rw [hcV] at hEV'
  have hipU : ip μ U U = u ^ 2 + σU ^ 2 := by rw [ip_self_split, ip_self_eq]
  have hipV : ip μ V V = v ^ 2 + σV ^ 2 := by rw [ip_self_split, ip_self_eq]
  -- scalar bounds
  have hm1 : H⁻¹ ≤ m := hK.mass_lower
  have hm2 : m ≤ H := hK.mass_upper
  have y1 : 2 * |u| * (β * σV) ≤ tY * |u| ^ 2 + (β * σV) ^ 2 / tY := young htY
  have y2 : 2 * |v| * (β * σU) ≤ tY * |v| ^ 2 + (β * σU) ^ 2 / tY := young htY
  have hu2 : |u| ^ 2 = u ^ 2 := sq_abs u
  have hv2 : |v| ^ 2 = v ^ 2 := sq_abs v
  have c1 : -(|u| * (β * σV)) ≤ u * ip μ (cen μ (kone' μ K)) (cen μ V) := by
    have := abs_mul u (ip μ (cen μ (kone' μ K)) (cen μ V))
    have h' : |u * ip μ (cen μ (kone' μ K)) (cen μ V)| ≤ |u| * (β * σV) := by
      rw [this]; exact mul_le_mul_of_nonneg_left hb1 (abs_nonneg u)
    linarith [neg_abs_le (u * ip μ (cen μ (kone' μ K)) (cen μ V))]
  have c2 : -(|v| * (β * σU)) ≤ v * ip μ (cen μ U) (cen μ (kone μ K)) := by
    have := abs_mul v (ip μ (cen μ U) (cen μ (kone μ K)))
    have h' : |v * ip μ (cen μ U) (cen μ (kone μ K))| ≤ |v| * (β * σU) := by
      rw [this, mul_comm σU β] at *; exact mul_le_mul_of_nonneg_left hb2 (abs_nonneg v)
    linarith [neg_abs_le (v * ip μ (cen μ U) (cen μ (kone μ K)))]
  have c3 : -(qperp * σU * σV) ≤ kf μ K (cen μ U) (cen μ V) := by
    linarith [neg_abs_le (kf μ K (cen μ U) (cen μ V))]
  have c4 : 2 * qperp * σU * σV ≤ qperp * (σU ^ 2 + σV ^ 2) := by
    nlinarith [mul_nonneg hq (sq_nonneg (σU - σV))]
  -- the fluctuation coefficient and the mean part
  have hfl : 0 ≤ (s - qperp - M * ρE - β ^ 2 / tY) * (σU ^ 2 + σV ^ 2) :=
    mul_nonneg (by linarith) (by positivity)
  have hs0 : 0 ≤ s := by
    have : 0 ≤ β ^ 2 / tY := div_nonneg (sq_nonneg _) htY.le
    have hM0 : 0 ≤ M := by
      have hH : 0 < H := by
        by_contra hH
        push Not at hH
        have : H⁻¹ ≤ 0 := inv_nonpos.mpr hH
        linarith
      linarith
    have hρ0 : 0 ≤ ρE := by
      have h11 := hρ (fun _ => 1) (fun _ => 1)
      have hn : nrm μ (fun _ => (1 : ℝ)) = 1 := by
        unfold nrm ip
        simp only [mul_one, FiniteLaw.expect_const, Real.sqrt_one]
      rw [hn] at h11
      linarith [abs_nonneg (kf μ TE (fun _ => 1) (fun _ => 1) -
        μ.expect (fun _ => 1) * μ.expect (fun _ => 1))]
    linarith [mul_nonneg hM0 hρ0]
  have hmean := mean_part_nonneg (u := u) (v := v) (z := z) hm1 hm2 htY hM htH hs0 hk hkM
  have hY : 0 ≤ (s - qperp - M * ρE - β ^ 2 / tY) * (σU ^ 2 + σV ^ 2) +
      ((M + s - tY) * (u ^ 2 + v ^ 2) + 2 * m * u * v + 2 * s * z * (u + v) + 2 * k * z ^ 2) :=
    add_nonneg hfl hmean
  -- assemble: Φ ≥ a_D · Y
  rw [hKUV, hEU, hEV, hipU, hipV, hMa, hsa, hka]
  have hdiv1 : (β * σV) ^ 2 / tY = β ^ 2 / tY * σV ^ 2 := by ring
  have hdiv2 : (β * σU) ^ 2 / tY = β ^ 2 / tY * σU ^ 2 := by ring
  rw [hdiv1, hu2] at y1
  rw [hdiv2, hv2] at y2
  have key : 0 ≤ a .D * ((s - qperp - M * ρE - β ^ 2 / tY) * (σU ^ 2 + σV ^ 2) +
      ((M + s - tY) * (u ^ 2 + v ^ 2) + 2 * m * u * v + 2 * s * z * (u + v) + 2 * k * z ^ 2)) :=
    mul_nonneg haD.le hY
  have e1 := mul_le_mul_of_nonneg_left c1 haD.le
  have e2 := mul_le_mul_of_nonneg_left c2 haD.le
  have e3 := mul_le_mul_of_nonneg_left c3 haD.le
  have e4 := mul_le_mul_of_nonneg_left c4 haD.le
  have e5 := mul_le_mul_of_nonneg_left y1 haD.le
  have e6 := mul_le_mul_of_nonneg_left y2 haD.le
  have hMn : 0 ≤ M * a .D := by
    have : 0 ≤ a .S := by
      rw [hMa]
      have hH : 0 < H := by
        by_contra hH
        push Not at hH
        have : H⁻¹ ≤ 0 := inv_nonpos.mpr hH
        linarith
      exact mul_nonneg (by linarith) haD.le
    rwa [hMa] at this
  have e7 := mul_le_mul_of_nonneg_left hEU' hMn
  have e8 := mul_le_mul_of_nonneg_left hEV' hMn
  linarith [key, e1, e2, e3, e4, e5, e6, e7, e8]

end Sarkozy.FiveType
