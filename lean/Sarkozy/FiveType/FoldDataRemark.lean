module

public import Sarkozy.FiveType.Rows

/-!
# Fold data from marginal densities (`rem:five-type-fold-data`)

Source: `paper/sections/17_completion_repair.tex`, `rem:five-type-fold-data`.

Fix `b ∈ supp ν` and write `μ = ν^b`, `K = T_F^b ≥ 0`. The middle density is
`m_b = ⟨𝟙, K𝟙⟩`, the conditional law of `(ω₀, ω₂)` given `ω₁ = b` has the density `K/m_b`
relative to `μ ⊗ μ`, and its marginal densities are `φ₀ = K𝟙/m_b`, `φ₂ = K*𝟙/m_b` (`margL`,
`margR`). The covariance kernel is `c_b = K/m_b - φ₀ ⊗ φ₂` (`covKernel`), so that
`⟨h, c_b h'⟩ = Cov(h(ω₀), h'(ω₂) | ω₁ = b)` and `K = m_b(φ₀ ⊗ φ₂ + c_b)`.

`foldData_of_marginals`: if `m_b ∈ [H⁻¹, H]`, `φ_o ≤ R_m` on the support, `‖φ_o - 𝟙‖ ≤ υ`, and the
maximal correlation of the conditional law relative to its own marginals is at most `ρ_F`, i.e.
`|Cov(h(ω₀), h'(ω₂))| ≤ ρ_F √Var_{φ₀μ}(h) √Var_{φ₂μ}(h')`, then the fold data of
`lem:five-type`(c) hold with `β = Hυ` and `q⊥ = H(R_m ρ_F + υ²)`. As in the paper:
`(I - J)K𝟙 = m_b(φ₀ - 𝟙)`, the perpendicular block is
`m_b((φ₀ - 𝟙) ⊗ (φ₂ - 𝟙) + (I - J)c_b(I - J))`, and `‖c_b‖ ≤ R_m ρ_F` because
`‖h‖²_{φ_o μ} ≤ R_m ‖h‖²`. `f_al_of_marginals` is the resulting coefficient
`f_al = (H R_m ρ_F + (H + H²/t_Y)υ²)/r`.

Implicit hypotheses made explicit: `H > 0` and `ρ_F ≥ 0`. The kernel is nonnegative, as
`T_F^b` is in `def:five-type-datum`; it makes the marginal densities nonnegative.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiveType

variable {𝔛 : Type*} [Fintype 𝔛]

/-- The marginal density `φ₀ = K𝟙/m` of the conditional law. -/
noncomputable def margL (μ : FiniteLaw 𝔛) (K : 𝔛 → 𝔛 → ℝ) (x : 𝔛) : ℝ :=
  kone μ K x / kf μ K (fun _ => 1) (fun _ => 1)

/-- The marginal density `φ₂ = K*𝟙/m` of the conditional law. -/
noncomputable def margR (μ : FiniteLaw 𝔛) (K : 𝔛 → 𝔛 → ℝ) (y : 𝔛) : ℝ :=
  kone' μ K y / kf μ K (fun _ => 1) (fun _ => 1)

/-- The covariance kernel `c = K/m - φ₀ ⊗ φ₂`. -/
noncomputable def covKernel (μ : FiniteLaw 𝔛) (K : 𝔛 → 𝔛 → ℝ) (x y : 𝔛) : ℝ :=
  K x y / kf μ K (fun _ => 1) (fun _ => 1) - margL μ K x * margR μ K y

/-- The variance of `h` under the law with density `φ` relative to `μ`. -/
noncomputable def wvar (μ : FiniteLaw 𝔛) (φ h : 𝔛 → ℝ) : ℝ :=
  μ.expect (fun x => φ x * h x ^ 2) - μ.expect (fun x => φ x * h x) ^ 2

theorem nrm_smul (μ : FiniteLaw 𝔛) (a : ℝ) (f : 𝔛 → ℝ) :
    nrm μ (fun x => a * f x) = |a| * nrm μ f := by
  unfold nrm ip
  rw [show (fun x => a * f x * (a * f x)) = fun x => a ^ 2 * (f x * f x) from
    funext fun x => by ring, FiniteLaw.expect_const_mul, Real.sqrt_mul (sq_nonneg a),
    Real.sqrt_sq_eq_abs]

theorem kf_one_one (μ : FiniteLaw 𝔛) (K : 𝔛 → 𝔛 → ℝ) :
    kf μ K (fun _ => 1) (fun _ => 1) = μ.expect (kone μ K) := by
  simp only [kf, kone, FiniteLaw.expect, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem kf_one_one' (μ : FiniteLaw 𝔛) (K : 𝔛 → 𝔛 → ℝ) :
    kf μ K (fun _ => 1) (fun _ => 1) = μ.expect (kone' μ K) := by
  rw [kf_one_left]
  unfold ip
  exact μ.expect_congr fun y => by ring

/-- **`rem:five-type-fold-data`**: the fold data of `lem:five-type`(c) from marginal densities
and a maximal correlation bound, with `β = Hυ` and `q⊥ = H(R_m ρ_F + υ²)`. -/
theorem foldData_of_marginals {μ : FiniteLaw 𝔛} {K : 𝔛 → 𝔛 → ℝ} {H υ Rm ρF : ℝ}
    (hH : 0 < H) (hm1 : H⁻¹ ≤ kf μ K (fun _ => 1) (fun _ => 1))
    (hm2 : kf μ K (fun _ => 1) (fun _ => 1) ≤ H)
    (hK0 : ∀ x y, 0 ≤ K x y)
    (hRL : ∀ x, μ.weight x ≠ 0 → margL μ K x ≤ Rm) (hRR : ∀ x, μ.weight x ≠ 0 → margR μ K x ≤ Rm)
    (hυL : nrm μ (fun x => margL μ K x - 1) ≤ υ) (hυR : nrm μ (fun x => margR μ K x - 1) ≤ υ)
    (hρ : 0 ≤ ρF)
    (hmc : ∀ h h' : 𝔛 → ℝ, |kf μ (covKernel μ K) h h'| ≤
      ρF * Real.sqrt (wvar μ (margL μ K) h) * Real.sqrt (wvar μ (margR μ K) h')) :
    FoldData μ K H (H * υ) (H * (Rm * ρF + υ ^ 2)) := by
  set m := kf μ K (fun _ => 1) (fun _ => 1) with hmdef
  have hm0 : 0 < m := lt_of_lt_of_le (inv_pos.mpr hH) hm1
  have hmne : m ≠ 0 := hm0.ne'
  have hυ : 0 ≤ υ := le_trans (nrm_nonneg _ _) hυL
  have hL0 : ∀ x, 0 ≤ margL μ K x := fun x =>
    div_nonneg (Finset.sum_nonneg fun y _ => mul_nonneg (μ.nonneg y) (hK0 x y)) hm0.le
  have hR0 : ∀ y, 0 ≤ margR μ K y := fun y =>
    div_nonneg (Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonneg x) (hK0 x y)) hm0.le
  -- the marginal densities
  have hL : ∀ x, margL μ K x = kone μ K x / m := fun _ => rfl
  have hR : ∀ y, margR μ K y = kone' μ K y / m := fun _ => rfl
  have hKL : ∀ x, kone μ K x = m * margL μ K x := fun x => by
    rw [hL]; field_simp
  have hKR : ∀ y, kone' μ K y = m * margR μ K y := fun y => by
    rw [hR]; field_simp
  have hEL : μ.expect (margL μ K) = 1 := by
    have : μ.expect (kone μ K) = m := (kf_one_one μ K).symm
    rw [show margL μ K = fun x => m⁻¹ * kone μ K x from funext fun x => by
      rw [hL]; field_simp, FiniteLaw.expect_const_mul, this, inv_mul_cancel₀ hmne]
  have hER : μ.expect (margR μ K) = 1 := by
    have : μ.expect (kone' μ K) = m := (kf_one_one' μ K).symm
    rw [show margR μ K = fun y => m⁻¹ * kone' μ K y from funext fun y => by
      rw [hR]; field_simp, FiniteLaw.expect_const_mul, this, inv_mul_cancel₀ hmne]
  have hRm : 1 ≤ Rm := by
    have := FiniteLaw.expect_mono μ (f := fun x => if μ.weight x = 0 then 0 else margL μ K x)
      (g := fun _ => Rm) fun x => by
        by_cases hx : μ.weight x = 0
        · simp only [hx, ↓reduceIte]
          have h1 := hRL
          -- any support point gives `0 ≤ Rm`
          obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
            (f := μ.weight) (by rw [μ.total]; exact one_ne_zero)
          exact le_trans (hL0 y) (h1 y hy)
        · simp only [hx, ↓reduceIte]; exact hRL x hx
    rw [FiniteLaw.expect_const] at this
    have he : μ.expect (fun x => if μ.weight x = 0 then 0 else margL μ K x) =
        μ.expect (margL μ K) :=
      expect_congr_supp μ fun x hx => by simp only [hx, ↓reduceIte]
    rw [he, hEL] at this
    exact this
  -- the decomposition `K = m(φ₀ ⊗ φ₂ + c)`
  have hc : ∀ x y, covKernel μ K x y = K x y / m - margL μ K x * margR μ K y := fun _ _ => rfl
  have hdec : ∀ x y, K x y = m * (margL μ K x * margR μ K y + covKernel μ K x y) := by
    intro x y
    rw [hc]
    field_simp
    ring
  -- `c` annihilates the constants
  have hc1 : ∀ x, kone μ (covKernel μ K) x = 0 := by
    intro x
    unfold kone
    simp only [hc]
    have : ∑ y, μ.weight y * (K x y / m - margL μ K x * margR μ K y) =
        kone μ K x / m - margL μ K x * μ.expect (margR μ K) := by
      unfold kone FiniteLaw.expect
      rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [this, hER, mul_one, hL]
    ring
  have hc2 : ∀ y, kone' μ (covKernel μ K) y = 0 := by
    intro y
    unfold kone'
    simp only [hc]
    have : ∑ x, μ.weight x * (K x y / m - margL μ K x * margR μ K y) =
        kone' μ K y / m - μ.expect (margL μ K) * margR μ K y := by
      unfold kone' FiniteLaw.expect
      rw [Finset.sum_div, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [this, hEL, one_mul, hR]
    ring
  have hann : Annihilates μ (covKernel μ K) := ⟨fun x _ => hc1 x, fun y _ => hc2 y⟩
  -- the covariance kernel is bounded by `R_m ρ_F`
  have hvar : ∀ (φ : 𝔛 → ℝ), (∀ x, 0 ≤ φ x) → (∀ x, μ.weight x ≠ 0 → φ x ≤ Rm) →
      ∀ h : 𝔛 → ℝ, Real.sqrt (wvar μ φ h) ≤ Real.sqrt Rm * nrm μ h := by
    intro φ hφ0 hφR h
    have h1 : wvar μ φ h ≤ Rm * ip μ h h := by
      unfold wvar ip
      have h2 : μ.expect (fun x => φ x * h x ^ 2) ≤ μ.expect (fun x => Rm * (h x * h x)) := by
        unfold FiniteLaw.expect
        refine Finset.sum_le_sum fun x _ => ?_
        by_cases hx : μ.weight x = 0
        · rw [hx, zero_mul, zero_mul]
        · have hle : φ x * h x ^ 2 ≤ Rm * (h x * h x) := by
            rw [sq]
            exact mul_le_mul_of_nonneg_right (hφR x hx) (mul_self_nonneg _)
          exact mul_le_mul_of_nonneg_left hle (μ.nonneg x)
      rw [FiniteLaw.expect_const_mul] at h2
      nlinarith [sq_nonneg (μ.expect (fun x => φ x * h x))]
    calc Real.sqrt (wvar μ φ h) ≤ Real.sqrt (Rm * ip μ h h) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt Rm * nrm μ h := by unfold nrm; rw [Real.sqrt_mul (by linarith)]
  have hcov : ∀ Φ Ψ : 𝔛 → ℝ, |kf μ (covKernel μ K) Φ Ψ| ≤ Rm * ρF * nrm μ Φ * nrm μ Ψ := by
    intro Φ Ψ
    have hsR : Real.sqrt Rm * Real.sqrt Rm = Rm := Real.mul_self_sqrt (by linarith)
    calc |kf μ (covKernel μ K) Φ Ψ|
        ≤ ρF * Real.sqrt (wvar μ (margL μ K) Φ) * Real.sqrt (wvar μ (margR μ K) Ψ) := hmc Φ Ψ
      _ ≤ ρF * (Real.sqrt Rm * nrm μ Φ) * (Real.sqrt Rm * nrm μ Ψ) := by
          have a1 := hvar _ hL0 hRL Φ
          have a2 := hvar _ hR0 hRR Ψ
          have a3 : Real.sqrt (wvar μ (margL μ K) Φ) * Real.sqrt (wvar μ (margR μ K) Ψ) ≤
              (Real.sqrt Rm * nrm μ Φ) * (Real.sqrt Rm * nrm μ Ψ) :=
            mul_le_mul a1 a2 (Real.sqrt_nonneg _)
              (mul_nonneg (Real.sqrt_nonneg _) (nrm_nonneg _ _))
          have := mul_le_mul_of_nonneg_left a3 hρ
          linarith
      _ = ρF * (Real.sqrt Rm * Real.sqrt Rm) * nrm μ Φ * nrm μ Ψ := by ring
      _ = Rm * ρF * nrm μ Φ * nrm μ Ψ := by rw [hsR]; ring
  refine ⟨hm1, hm2, ?_, ?_, ?_⟩
  · -- `(I - J)K𝟙 = m(φ₀ - 𝟙)`
    have he : cen μ (kone μ K) = fun x => m * (margL μ K x - 1) := by
      funext x
      unfold cen
      rw [← kf_one_one, hKL]
      ring
    rw [he, nrm_smul, abs_of_pos hm0]
    exact mul_le_mul hm2 hυL (nrm_nonneg _ _) hH.le
  · have he : cen μ (kone' μ K) = fun x => m * (margR μ K x - 1) := by
      funext x
      unfold cen
      rw [← kf_one_one', hKR]
      ring
    rw [he, nrm_smul, abs_of_pos hm0]
    exact mul_le_mul hm2 hυR (nrm_nonneg _ _) hH.le
  · -- the perpendicular block
    intro Φ Ψ hΦ hΨ
    have hsplit : kf μ K Φ Ψ = m * (ip μ Φ (fun x => margL μ K x - 1) *
        ip μ (fun y => margR μ K y - 1) Ψ + kf μ (covKernel μ K) Φ Ψ) := by
      have hprod : kf μ (fun x y => margL μ K x * margR μ K y) Φ Ψ =
          μ.expect (fun x => Φ x * margL μ K x) * μ.expect (fun y => margR μ K y * Ψ y) := by
        simp only [kf, FiniteLaw.expect, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        ring
      have hlin : kf μ K Φ Ψ = m * (kf μ (fun x y => margL μ K x * margR μ K y) Φ Ψ +
          kf μ (covKernel μ K) Φ Ψ) := by
        simp only [kf, hdec, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        ring
      have h1 : kf μ K Φ Ψ = m * (μ.expect (fun x => Φ x * margL μ K x) *
          μ.expect (fun y => margR μ K y * Ψ y) + kf μ (covKernel μ K) Φ Ψ) := by
        rw [hlin, hprod]
      have h2 : μ.expect (fun x => Φ x * margL μ K x) = ip μ Φ (fun x => margL μ K x - 1) := by
        unfold ip
        rw [show (fun x => Φ x * (margL μ K x - 1)) = fun x => Φ x * margL μ K x - Φ x from
          funext fun x => by ring, FiniteLaw.expect_sub, hΦ, sub_zero]
      have h3 : μ.expect (fun y => margR μ K y * Ψ y) = ip μ (fun y => margR μ K y - 1) Ψ := by
        unfold ip
        rw [show (fun y => (margR μ K y - 1) * Ψ y) = fun y => margR μ K y * Ψ y - Ψ y from
          funext fun y => by ring, FiniteLaw.expect_sub, hΨ, sub_zero]
      rw [h1, h2, h3]
    have b1 : |ip μ Φ (fun x => margL μ K x - 1)| ≤ nrm μ Φ * υ :=
      (abs_ip_le _ _ _).trans (mul_le_mul_of_nonneg_left hυL (nrm_nonneg _ _))
    have b2 : |ip μ (fun y => margR μ K y - 1) Ψ| ≤ υ * nrm μ Ψ :=
      (abs_ip_le _ _ _).trans (mul_le_mul_of_nonneg_right hυR (nrm_nonneg _ _))
    have b3 := hcov Φ Ψ
    have hnΦ := nrm_nonneg μ Φ
    have hnΨ := nrm_nonneg μ Ψ
    rw [hsplit, abs_mul, abs_of_pos hm0]
    have hin : |ip μ Φ (fun x => margL μ K x - 1) * ip μ (fun y => margR μ K y - 1) Ψ +
        kf μ (covKernel μ K) Φ Ψ| ≤ (Rm * ρF + υ ^ 2) * nrm μ Φ * nrm μ Ψ := by
      calc _ ≤ |ip μ Φ (fun x => margL μ K x - 1)| * |ip μ (fun y => margR μ K y - 1) Ψ| +
            |kf μ (covKernel μ K) Φ Ψ| := by rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ (nrm μ Φ * υ) * (υ * nrm μ Ψ) + Rm * ρF * nrm μ Φ * nrm μ Ψ := by
            gcongr
        _ = (Rm * ρF + υ ^ 2) * nrm μ Φ * nrm μ Ψ := by ring
    have hpos : 0 ≤ (Rm * ρF + υ ^ 2) * nrm μ Φ * nrm μ Ψ :=
      mul_nonneg (mul_nonneg (by nlinarith) hnΦ) hnΨ
    calc m * |ip μ Φ (fun x => margL μ K x - 1) * ip μ (fun y => margR μ K y - 1) Ψ +
          kf μ (covKernel μ K) Φ Ψ|
        ≤ H * ((Rm * ρF + υ ^ 2) * nrm μ Φ * nrm μ Ψ) :=
          mul_le_mul hm2 hin (abs_nonneg _) hH.le
      _ = H * (Rm * ρF + υ ^ 2) * nrm μ Φ * nrm μ Ψ := by ring

/-- **`rem:five-type-fold-data`, the row coefficient**: with `β = Hυ` and
`q⊥ = H(R_m ρ_F + υ²)`, `f_al = (q⊥ + β²/t_Y)/r = (H R_m ρ_F + (H + H²/t_Y)υ²)/r`. -/
theorem f_al_of_marginals (H υ Rm ρF tY r : ℝ) :
    (H * (Rm * ρF + υ ^ 2) + (H * υ) ^ 2 / tY) / r =
      (H * Rm * ρF + (H + H ^ 2 / tY) * υ ^ 2) / r := by
  congr 1
  ring

end Sarkozy.FiveType
