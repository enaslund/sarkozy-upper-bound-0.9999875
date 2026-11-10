module

public import Sarkozy.PartVLaws.UpperRP
public import Sarkozy.FiveType.FoldDataRemark

@[expose] public section

/-!
# Schur rows of the tail datum are valid rows (`it:record:upper-F5`(b))

`paper/sections/25_upper_reference.tex`, `def:record:upper-bands`, item (F5)(b) ("Schur rows (tail
datum)"): with the fold kernel's mass `m_b ∈ [H⁻¹, H]`, marginal densities bounded by `R_m` and
within `υ` of `𝟙`, maximal correlation `ρ_F`, and the matching kernel's exact marginals with
`‖T_E^b - J‖ ≤ ρ_E`,
`f_Schur = (H R_m ρ_F + (H + 50H²) υ²)/r` and `h = ρ_E/r` are valid row coefficients
(`lem:five-type`(c) with `rem:five-type-fold-data` at `t_Y = 1/50`).

`validRows_of_schurRows` proves this in the form of `ValidRows` ((V2), Schur branch), through
C1's `foldData_of_marginals`, for any mean allowance `M ≥ H + 1/50` with `H ≤ 50`. The tail
datum records `M = 21/20`, so it needs `H ≤ 103/100`. The constants `H, υ, R_m, ρ_F, ρ_E` at a
prime come from `(F1)`–`(F4)` of the same definition, which are not formalized here.
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.FiveType

variable {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛]

/-- **The Schur-row data at one middle value** (the hypotheses of `rem:five-type-fold-data` for
the fold kernel `K = T_F^b`, and exact marginals with `‖T_E^b - J‖ ≤ ρ_E` for the matching
kernel). -/
structure SchurRowData (μ : FiniteLaw 𝔛) (K TE : 𝔛 → 𝔛 → ℝ) (H υ Rm ρF ρE : ℝ) : Prop where
  mass_lower : H⁻¹ ≤ kf μ K (fun _ => 1) (fun _ => 1)
  mass_upper : kf μ K (fun _ => 1) (fun _ => 1) ≤ H
  nonneg : ∀ x y, 0 ≤ K x y
  margL_le : ∀ x, μ.weight x ≠ 0 → margL μ K x ≤ Rm
  margR_le : ∀ x, μ.weight x ≠ 0 → margR μ K x ≤ Rm
  devL : nrm μ (fun x => margL μ K x - 1) ≤ υ
  devR : nrm μ (fun x => margR μ K x - 1) ≤ υ
  corr : ∀ h h' : 𝔛 → ℝ, |kf μ (covKernel μ K) h h'| ≤
    ρF * Real.sqrt (wvar μ (margL μ K) h) * Real.sqrt (wvar μ (margR μ K) h')
  exactE : ExactMarginals μ TE
  normE : NormBound μ TE ρE

/-- **`it:record:upper-F5`(b): the Schur rows are valid rows.** If at every middle value the rows
have the Schur-row data with constants `H, υ, R_m, ρ_F, ρ_E`, then the row data are valid in the
sense of (V2) with `f = f_Schur = (H R_m ρ_F + (H + 50H²)υ²)/r`, `h = ρ_E/r` and any
`M ≥ H + 1/50`, provided `0 < H ≤ 50`, `R_m, ρ_F ≥ 0`. -/
theorem validRows_of_schurRows (D : Datum 𝔛) {r H υ Rm ρF ρE M : ℝ} (hr : 0 < r) (hH : 0 < H)
    (hH50 : H ≤ 50) (hRm : 0 ≤ Rm) (hρF : 0 ≤ ρF) (hM : H + 1 / 50 ≤ M)
    (hb : ∀ b, D.nu.weight b ≠ 0 → SchurRowData (D.nub b) (D.TF b) (D.TE b) H υ Rm ρF ρE) :
    ValidRows D r ((H * Rm * ρF + (H + 50 * H ^ 2) * υ ^ 2) / r) (ρE / r) M := by
  right
  left
  refine ⟨H, H * υ, H * (Rm * ρF + υ ^ 2), 1 / 50, ?_, by norm_num, ?_, hM, ?_, fun b hb' => ?_⟩
  · exact mul_nonneg hH.le (add_nonneg (mul_nonneg hRm hρF) (sq_nonneg υ))
  · rw [← one_div]
    exact one_div_le_one_div_of_le hH hH50
  · rw [f_al_of_marginals]
    have : H ^ 2 / (1 / 50) = 50 * H ^ 2 := by ring
    rw [this]
  · obtain ⟨h1, h2, h0, hL, hR, hυL, hυR, hmc, hE, hN⟩ := hb b hb'
    refine ⟨hE, ?_, foldData_of_marginals hH h1 h2 h0 hL hR hυL hυR hρF hmc⟩
    rwa [div_mul_cancel₀ ρE hr.ne']

end Sarkozy.PartVLaws
