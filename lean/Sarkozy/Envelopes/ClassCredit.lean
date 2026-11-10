module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

/-!
# Variance credit inside a positive envelope (`lem:class-credit`)

`paper/sections/23_envelopes.tex`, `lem:class-credit`: the operator step, the energy step and the
gates.

**Proved here.**
* `envelope_le_sub_constants` (the operator step of the proof): if `D ⪰ 0` annihilates every
  vector with a constant factor (`D = PDP`, `P` the projection onto a subspace `W` orthogonal to the
  constants), `‖D‖ ≤ c_ω` and `0 ≤ c ≤ c_ω`, then `D ⪯ c_ω I - c J` (as quadratic forms), `J` the
  projection onto the constants. In the paper `P = ⊗_𝔅(I - J_𝔅)` and `W = ran P`.
* `credit_energy_step` (the energy step, abstract): with the placed energies as real numbers
  satisfying `Y[D̄^μ_ω] ≤ c_ω Y[Diag_ω] - c Y[J_ω]` (from the operator step and (E2)), the
  restoration hypothesis `∑_{𝒞'} Y[J_ω] ≥ |𝒞'| (l̄ - z) C_X Y` and `Y[J_ω] ≥ 0`, the class sum is
  lowered by `|𝒞'| π̃ (cg - cz) C_X Y` for every `0 ≤ g ≤ max(l̄, 0)`.
* The gates: `credit_gate` (`C_{n,m} ≥ κ_b e^{tU_inv}` and `cg < C_{n,m}` for `c = κ_b`),
  `credit_gate_E4` (the numerical gate of the quartic matching class:
  `κ_b(E4) e^{tU_inv} > 1.122 > κ_{4,E} > cg` from `κ_b(E4) > 0.4817590234`, `κ_{4,E} < 0.6667`
  and `tU_inv ≥ 0.84688`, with `exp_gt_233`: `e^{0.84688} > 2.33`), and `credit_gate_average`
  (`p c g < κ_b` when `pc ≤ κ_b`).

The identification of the paper's energies with the real numbers of the energy step, and the gains
`g` (the final variance corollary), are inputs (section 22).
-/

namespace Sarkozy.Envelopes

open scoped RealInnerProductSpace

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- `‖P x‖² + ‖J x‖² ≤ ‖x‖²` for projections onto orthogonal subspaces `W ≤ Cstᗮ`. -/
theorem norm_sq_proj_add_le {W Cst : Submodule ℝ E} (hW : W ≤ Cstᗮ) (x : E) :
    ‖W.starProjection x‖ ^ 2 + ‖Cst.starProjection x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have h0 : ⟪W.starProjection x, x - W.starProjection x⟫ = 0 := by
    rw [real_inner_comm]
    exact W.starProjection_inner_eq_zero x _ (W.starProjection_apply_mem x)
  have hpy : ‖x‖ ^ 2 = ‖W.starProjection x‖ ^ 2 + ‖x - W.starProjection x‖ ^ 2 := by
    have e : x = W.starProjection x + (x - W.starProjection x) := by abel
    conv_lhs => rw [e]
    rw [norm_add_sq_real, h0, mul_zero, add_zero]
  have hJP : Cst.starProjection (W.starProjection x) = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact hW (W.starProjection_apply_mem x)
  have hJ : Cst.starProjection x = Cst.starProjection (x - W.starProjection x) := by
    rw [map_sub, hJP, sub_zero]
  have hle : ‖Cst.starProjection x‖ ≤ ‖x - W.starProjection x‖ := by
    rw [hJ]; exact Cst.norm_starProjection_apply_le _
  have : ‖Cst.starProjection x‖ ^ 2 ≤ ‖x - W.starProjection x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  linarith

/-- **`lem:class-credit`, the operator step.** Let `W ≤ Cstᗮ` (the vectors with no constant factor
lie in the orthogonal complement of the constants), and let `D` satisfy `⟪Dx, x⟫ = ⟪D(Px), Px⟫`
(`D = PDP` for `P` the projection onto `W`) and `⟪Dy, y⟫ ≤ c_ω ‖y‖²` (`‖D‖ ≤ c_ω`). Then for
`0 ≤ c ≤ c_ω`, `D ⪯ c_ω I - c J`: `⟪Dx, x⟫ ≤ c_ω ‖x‖² - c ⟪Jx, x⟫`. -/
theorem envelope_le_sub_constants {W Cst : Submodule ℝ E} (hW : W ≤ Cstᗮ) (D : E →ₗ[ℝ] E)
    {cω c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ cω)
    (hP : ∀ x, ⟪D x, x⟫ = ⟪D (W.starProjection x), W.starProjection x⟫)
    (hD : ∀ y, ⟪D y, y⟫ ≤ cω * ‖y‖ ^ 2) (x : E) :
    ⟪D x, x⟫ ≤ cω * ‖x‖ ^ 2 - c * ⟪Cst.starProjection x, x⟫ := by
  have hJx : ⟪Cst.starProjection x, x⟫ = ‖Cst.starProjection x‖ ^ 2 := by
    have h := Cst.starProjection_inner_eq_zero x (Cst.starProjection x)
      (Cst.starProjection_apply_mem x)
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at h
    rw [real_inner_comm]; linarith
  have h1 := hD (W.starProjection x)
  have h2 := norm_sq_proj_add_le hW x
  have hcω : 0 ≤ cω := hc0.trans hc
  rw [hP x, hJx]
  have h3 : cω * ‖W.starProjection x‖ ^ 2 ≤ cω * (‖x‖ ^ 2 - ‖Cst.starProjection x‖ ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hcω
  have h4 : c * ‖Cst.starProjection x‖ ^ 2 ≤ cω * ‖Cst.starProjection x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hc (sq_nonneg _)
  linarith

end Operator

/-! ### The energy step -/

/-- **`lem:class-credit`, the energy step (abstract).** Over a finite set `𝒞'` of selections with a
common raw-arm coefficient `π̃ ≥ 0`, suppose the averaged envelope energies on the `μ` branch
satisfy
`Y[D̄^μ_ω] ≤ c_ω Y[Diag_ω] - c Y[J_ω]` (operator step and (E2)), `Y[J_ω] ≥ 0`, and the restoration
`∑_{𝒞'} Y[J_ω] ≥ |𝒞'| (l̄ - z) C_X Y` with `z, C_X Y ≥ 0`. Then for `c ≥ 0` and
`0 ≤ g ≤ max(l̄, 0)`,
`∑_{𝒞'} π̃ Y[D̄^μ_ω] ≤ ∑_{𝒞'} π̃ c_ω Y[Diag_ω] - |𝒞'| π̃ (cg - cz) C_X Y`. -/
theorem credit_energy_step {Ω : Type*} (C' : Finset Ω) (YD YDiag YJ cω : Ω → ℝ)
    {π c g l z CY : ℝ} (hπ : 0 ≤ π) (hc : 0 ≤ c) (hg0 : 0 ≤ g) (hg : g ≤ max l 0)
    (hz : 0 ≤ z) (hCY : 0 ≤ CY) (hstep : ∀ ω ∈ C', YD ω ≤ cω ω * YDiag ω - c * YJ ω)
    (hJ0 : ∀ ω ∈ C', 0 ≤ YJ ω) (hrest : (C'.card : ℝ) * ((l - z) * CY) ≤ ∑ ω ∈ C', YJ ω) :
    ∑ ω ∈ C', π * YD ω ≤
      ∑ ω ∈ C', π * (cω ω * YDiag ω) - (C'.card : ℝ) * π * ((c * g - c * z) * CY) := by
  -- `c ∑ Y[J] ≥ |𝒞'| (cg - cz) C_X Y`
  have hkey : (C'.card : ℝ) * ((c * g - c * z) * CY) ≤ c * ∑ ω ∈ C', YJ ω := by
    have hcard : (0 : ℝ) ≤ C'.card := Nat.cast_nonneg _
    rcases le_or_gt l 0 with hl | hl
    · have hg' : g = 0 := le_antisymm (by simpa [max_eq_right hl] using hg) hg0
      subst hg'
      have : 0 ≤ c * ∑ ω ∈ C', YJ ω := mul_nonneg hc (Finset.sum_nonneg hJ0)
      have h2 : (C'.card : ℝ) * ((c * 0 - c * z) * CY) ≤ 0 := by
        have : (c * 0 - c * z) * CY ≤ 0 := by nlinarith [mul_nonneg hc hz]
        exact mul_nonpos_of_nonneg_of_nonpos hcard this
      linarith
    · have hgl : g ≤ l := by simpa [max_eq_left hl.le] using hg
      have h1 : (C'.card : ℝ) * ((c * g - c * z) * CY) ≤ c * ((C'.card : ℝ) * ((l - z) * CY)) := by
        have : (c * g - c * z) * CY ≤ c * ((l - z) * CY) := by
          have : c * g ≤ c * l := mul_le_mul_of_nonneg_left hgl hc
          nlinarith
        nlinarith
      exact h1.trans (mul_le_mul_of_nonneg_left hrest hc)
  have hsum : ∑ ω ∈ C', π * YD ω ≤ ∑ ω ∈ C', π * (cω ω * YDiag ω - c * YJ ω) :=
    Finset.sum_le_sum fun ω hω => mul_le_mul_of_nonneg_left (hstep ω hω) hπ
  have e : ∑ ω ∈ C', π * (cω ω * YDiag ω - c * YJ ω) =
      ∑ ω ∈ C', π * (cω ω * YDiag ω) - π * (c * ∑ ω ∈ C', YJ ω) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    ring
  rw [e] at hsum
  have := mul_le_mul_of_nonneg_left hkey hπ
  nlinarith

/-! ### The gates -/

/-- **`lem:class-credit`, gates.** With `0 ≤ t U_inv ≤ U_0`, `κ_H ≥ 0` and the coupon gate
`M R_err ≥ M^inv e^{tU_inv} tδ_s`, the base cost
`C_{n,m} = κ_H e^{U_0} - (κ_H - κ_b) e^{tU_inv} + M R_err - M^inv e^{tU_inv} tδ_s` is at least
`κ_b e^{tU_inv}`; and if `c = κ_b > 0` and the gain is below `1` (the gains are in `[0, 1)`),
then `cg < C_{n,m}`. -/
theorem credit_gate {κH κb U0 tU MR coupon g : ℝ} (htU : 0 ≤ tU) (hU : tU ≤ U0) (hκH : 0 ≤ κH)
    (hcoup : coupon ≤ MR) (hκb : 0 < κb) (hg1 : g < 1) :
    κb * Real.exp tU ≤ κH * Real.exp U0 - (κH - κb) * Real.exp tU + (MR - coupon) ∧
      κb * g < κH * Real.exp U0 - (κH - κb) * Real.exp tU + (MR - coupon) := by
  have e1 : Real.exp tU ≤ Real.exp U0 := Real.exp_le_exp.2 hU
  have h1 : κH * Real.exp tU ≤ κH * Real.exp U0 := mul_le_mul_of_nonneg_left e1 hκH
  have hge : κb * Real.exp tU ≤ κH * Real.exp U0 - (κH - κb) * Real.exp tU + (MR - coupon) := by
    nlinarith
  refine ⟨hge, ?_⟩
  have h2 : 1 ≤ Real.exp tU := Real.one_le_exp htU
  have hgk : κb * g < κb := by nlinarith
  have : κb ≤ κb * Real.exp tU := by nlinarith
  linarith

/-- `e^{0.84688} > 2.33`, from the Taylor polynomial of degree five. -/
theorem exp_gt_233 : (2.33 : ℝ) < Real.exp 0.84688 := by
  have h := Real.sum_le_exp_of_nonneg (x := (0.84688 : ℝ)) (by norm_num) 6
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  linarith

/-- **`lem:class-credit`, the numerical gate of E4.** If `κ_b(E4) > 0.4817590234`,
`κ_{4,E} < 0.6667`, `0 ≤ c ≤ κ_{4,E}`, `g < 1` and `t U_inv ≥ 0.84688`, then
`c g < 0.6667 < 1.122 < κ_b(E4) e^{tU_inv}`, and so `cg < C_{n,m}` for every base cost
`C_{n,m} ≥ κ_b(E4) e^{tU_inv}`. -/
theorem credit_gate_E4 {κbE4 κ4E c g tU Cnm : ℝ} (hκb : 0.4817590234 < κbE4) (hκ4 : κ4E < 0.6667)
    (hc0 : 0 ≤ c) (hc : c ≤ κ4E) (hg1 : g < 1) (htU : 0.84688 ≤ tU)
    (hC : κbE4 * Real.exp tU ≤ Cnm) :
    c * g < 0.6667 ∧ (1.122 : ℝ) < κbE4 * Real.exp tU ∧ c * g < Cnm := by
  have he : (2.33 : ℝ) < Real.exp tU :=
    exp_gt_233.trans_le (Real.exp_le_exp.2 htU)
  have h1 : c * g < 0.6667 := by
    have : c * g ≤ c := by nlinarith
    linarith
  have h2 : (1.122 : ℝ) < κbE4 * Real.exp tU := by nlinarith
  exact ⟨h1, h2, by linarith⟩

/-- **`lem:class-credit`, the class-average gate.** If the credited selections form the fraction
`p` of the class and `p c ≤ κ_b` with `κ_b > 0`, then the averaged credit `p c g` is below `κ_b`
for every gain `g < 1`. -/
theorem credit_gate_average {p c g κb : ℝ} (hp : 0 ≤ p) (hc : 0 ≤ c) (hpc : p * c ≤ κb)
    (hκb : 0 < κb) (hg1 : g < 1) : p * c * g < κb := by
  have h0 : 0 ≤ p * c := mul_nonneg hp hc
  rcases h0.lt_or_eq with h | h
  · have : p * c * g < p * c := by nlinarith
    linarith
  · rw [← h, zero_mul]; exact hκb

end Sarkozy.Envelopes
