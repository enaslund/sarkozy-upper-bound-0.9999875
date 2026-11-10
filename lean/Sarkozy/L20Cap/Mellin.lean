module

public import Sarkozy.L20Cap.Mass
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# The squared cubic trace `H_u` (`lem:rectangle-mellin`, elementary part)

`paper/sections/20a_rectangle_gram.tex`, `lem:rectangle-mellin`. `F` is a finite field of odd
characteristic, `p = |F|`, `q = 1/p`, `χ` its quadratic character (`chi`). For `u ∈ F`, on
counting measure,
`T_u(v, w) = E_y χ(u - y)χ(v - y)χ(w - y)` (`Tu`) and `H_u = T_u ⊙ T_u` (the entrywise square:
"powers denote pointwise products", `Hu`).

Proved:
* `Tu_form_le`: `‖T_u‖ ≤ 1` (on all of `F`, hence on `F ∖ {u}`): `T_u` is a compression of
  `qC diag(χ(u - y))C^*` with `CC^* = pI - J`;
* `Hu_row`: the row sums of the nonnegative matrix `H_u` on `F ∖ {u}` are `1 - 2q - 2q²`, and
  `Hu_form_le`: `‖H_u‖ ≤ 1 - 2q - 2q²` (Schur test);
* `Tu_transl`, `T0_dil`: `T_u(v, w) = T_0(v - u, w - u)` and `T_0(v, w) = χ(v)T_0(1, w/v)`, so
  `H_0(v, w) = h(w/v)` is a multiplicative convolution on `F^×`;
* `H0_eigen`: every multiplicative character `ρ` is an eigenvector of `H_0` on `F^×`, with
  eigenvalue `λ_ρ = ∑_{t ≠ 0} h(t)ρ(t)`;
* **`eigen_formula`**: for `ρ ≠ 1`,
  `λ_ρ = -q + q² + p^{-2} ∑_{t ≠ 0, 1} ρ(t)(T_t² - p)`, `T_t = ∑_y χ(y(y - 1)(y - t))`
  (`legT`, equal to `Target.legendreSum` on `𝔽_p`); for `ρ = 1`, `λ_1 = 1 - 2q - 2q²`.

The ℓ-adic bound `|∑_{t ≠ 0,1} ρ(t)(T_t² - p)| ≤ 3p^{3/2}` (the proposed H7,
`Target.SymSquareMellin`) then gives `λ_ρ ≥ -(3r + q - q²)` (`eigen_lower`).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `T_u(v, w) = E_y χ(u - y)χ(v - y)χ(w - y)`. -/
noncomputable def Tu (u v w : F) : ℝ :=
  (Fintype.card F : ℝ)⁻¹ * ∑ y, chi (u - y) * chi (v - y) * chi (w - y)

/-- `H_u = T_u ⊙ T_u`, the entrywise square. -/
noncomputable def Hu (u v w : F) : ℝ := Tu u v w ^ 2

theorem chi_sq_le_one (y : F) : chi y ^ 2 ≤ 1 := by
  by_cases h : y = 0
  · subst h; simp [chi_zero]
  · rw [chi_sq_of_ne h]

theorem abs_chi_le_one (y : F) : |chi y| ≤ 1 := by
  have := chi_sq_le_one y
  nlinarith [abs_nonneg (chi y), sq_abs (chi y)]

/-- `∑_y χ(v - y)χ(v' - y) = p𝟙_{v = v'} - 1`. -/
theorem sum_chi_rev (hF : ringChar F ≠ 2) (v v' : F) :
    ∑ y, chi (v - y) * chi (v' - y) = if v = v' then (Fintype.card F : ℝ) - 1 else -1 := by
  rw [← sum_chi_mul_chi hF v v']
  refine sum_congr rfl fun y _ => ?_
  rw [← chi_mul, ← chi_mul]
  congr 1
  ring

/-- `∑_y (∑_v f(v)χ(v - y))² = p∑f² - (∑f)² ≤ p∑f²`. -/
theorem sum_conv_sq_le (hF : ringChar F ≠ 2) (f : F → ℝ) :
    ∑ y, (∑ v, f v * chi (v - y)) ^ 2 ≤ Fintype.card F * ∑ v, f v ^ 2 := by
  have e : ∑ y, (∑ v, f v * chi (v - y)) ^ 2 =
      ∑ v, ∑ v', f v * f v' * (if v = v' then (Fintype.card F : ℝ) - 1 else -1) := by
    have : ∀ y, (∑ v, f v * chi (v - y)) ^ 2 =
        ∑ v, ∑ v', f v * f v' * (chi (v - y) * chi (v' - y)) := by
      intro y
      rw [sq, sum_mul_sum]
      exact sum_congr rfl fun v _ => sum_congr rfl fun v' _ => by ring
    rw [sum_congr rfl fun y _ => this y, sum_comm]
    refine sum_congr rfl fun v _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun v' _ => ?_
    rw [← mul_sum, sum_chi_rev hF]
  rw [e]
  have e2 : ∀ v : F, ∑ v', f v * f v' * (if v = v' then (Fintype.card F : ℝ) - 1 else -1) =
      Fintype.card F * f v ^ 2 - f v * ∑ v', f v' := by
    intro v
    have : ∀ v', f v * f v' * (if v = v' then (Fintype.card F : ℝ) - 1 else -1) =
        (if v = v' then (Fintype.card F : ℝ) * (f v * f v') else 0) - f v * f v' := by
      intro v'; split_ifs <;> ring
    rw [sum_congr rfl fun v' _ => this v', sum_sub_distrib, sum_ite_eq univ v, ← mul_sum]
    simp only [mem_univ, ↓reduceIte]
    ring
  rw [sum_congr rfl fun v _ => e2 v, sum_sub_distrib, ← mul_sum, ← sum_mul]
  nlinarith [sq_nonneg (∑ v', f v')]

/-- **`‖T_u‖ ≤ 1`** (`lem:rectangle-mellin`): `|∑_{v,w} f(v)T_u(v, w)g(w)| ≤ ‖f‖‖g‖` on counting
measure (on `F`, hence on `F ∖ {u}`). -/
theorem Tu_form_le (hF : ringChar F ≠ 2) (u : F) (f g : F → ℝ) :
    |∑ v, ∑ w, f v * Tu u v w * g w| ≤
      Real.sqrt (∑ v, f v ^ 2) * Real.sqrt (∑ w, g w ^ 2) := by
  have hp0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  set bf : F → ℝ := fun y => ∑ v, f v * chi (v - y)
  set bg : F → ℝ := fun y => ∑ w, g w * chi (w - y)
  have e : ∑ v, ∑ w, f v * Tu u v w * g w =
      (Fintype.card F : ℝ)⁻¹ * ∑ y, chi (u - y) * bf y * bg y := by
    have e1 : ∀ v w, f v * Tu u v w * g w = (Fintype.card F : ℝ)⁻¹ *
        ∑ y, chi (u - y) * (f v * chi (v - y)) * (g w * chi (w - y)) := by
      intro v w
      simp only [Tu, mul_sum]
      rw [sum_mul]
      exact sum_congr rfl fun y _ => by ring
    have e2 : ∀ y, chi (u - y) * bf y * bg y =
        ∑ v, ∑ w, chi (u - y) * (f v * chi (v - y)) * (g w * chi (w - y)) := by
      intro y
      simp only [bf, bg]
      rw [mul_assoc, sum_mul_sum, mul_sum]
      exact sum_congr rfl fun v _ => by rw [mul_sum]; exact sum_congr rfl fun w _ => by ring
    rw [sum_congr rfl fun v _ => sum_congr rfl fun w _ => e1 v w]
    simp only [← mul_sum]
    rw [sum_congr rfl fun y _ => e2 y]
    congr 1
    symm
    rw [sum_comm]
    refine sum_congr rfl fun v _ => ?_
    rw [sum_comm]
  rw [e, abs_mul, abs_of_pos (inv_pos.mpr hp0), inv_mul_le_iff₀ hp0]
  have h1 : |∑ y, chi (u - y) * bf y * bg y| ≤ ∑ y, |bf y| * |bg y| := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun y _ => ?_)
    rw [abs_mul, abs_mul]
    have := abs_chi_le_one (u - y)
    nlinarith [abs_nonneg (bf y), abs_nonneg (bg y),
      mul_nonneg (abs_nonneg (bf y)) (abs_nonneg (bg y))]
  have h2 : ∑ y, |bf y| * |bg y| ≤ Real.sqrt (∑ y, bf y ^ 2) * Real.sqrt (∑ y, bg y ^ 2) := by
    have cs := sum_mul_sq_le_sq_mul_sq univ (fun y => |bf y|) (fun y => |bg y|)
    simp only [sq_abs] at cs
    rw [← Real.sqrt_mul (sum_nonneg fun y _ => sq_nonneg _)]
    exact Real.le_sqrt_of_sq_le cs
  have h3 : Real.sqrt (∑ y, bf y ^ 2) ≤ Real.sqrt (Fintype.card F) * Real.sqrt (∑ v, f v ^ 2) := by
    rw [← Real.sqrt_mul hp0.le]
    exact Real.sqrt_le_sqrt (sum_conv_sq_le hF f)
  have h4 : Real.sqrt (∑ y, bg y ^ 2) ≤ Real.sqrt (Fintype.card F) * Real.sqrt (∑ w, g w ^ 2) := by
    rw [← Real.sqrt_mul hp0.le]
    exact Real.sqrt_le_sqrt (sum_conv_sq_le hF g)
  have hs : Real.sqrt (Fintype.card F) * Real.sqrt (Fintype.card F) = Fintype.card F :=
    Real.mul_self_sqrt hp0.le
  calc |∑ y, chi (u - y) * bf y * bg y|
      ≤ Real.sqrt (∑ y, bf y ^ 2) * Real.sqrt (∑ y, bg y ^ 2) := h1.trans h2
    _ ≤ (Real.sqrt (Fintype.card F) * Real.sqrt (∑ v, f v ^ 2)) *
          (Real.sqrt (Fintype.card F) * Real.sqrt (∑ w, g w ^ 2)) :=
        mul_le_mul h3 h4 (Real.sqrt_nonneg _) (by positivity)
    _ = Fintype.card F * (Real.sqrt (∑ v, f v ^ 2) * Real.sqrt (∑ w, g w ^ 2)) := by
        rw [show Real.sqrt (Fintype.card F) * Real.sqrt (∑ v, f v ^ 2) *
            (Real.sqrt (Fintype.card F) * Real.sqrt (∑ w, g w ^ 2)) =
            (Real.sqrt (Fintype.card F) * Real.sqrt (Fintype.card F)) *
              (Real.sqrt (∑ v, f v ^ 2) * Real.sqrt (∑ w, g w ^ 2)) by ring, hs]

/-! ## The row sums of `H_u` -/

/-- The exact form: `∑_y (∑_v f(v)χ(v - y))² = p∑f² - (∑f)²`. -/
theorem sum_conv_sq_eq (hF : ringChar F ≠ 2) (f : F → ℝ) :
    ∑ y, (∑ v, f v * chi (v - y)) ^ 2 = Fintype.card F * ∑ v, f v ^ 2 - (∑ v, f v) ^ 2 := by
  have e : ∀ y, (∑ v, f v * chi (v - y)) ^ 2 =
      ∑ v, ∑ v', f v * f v' * (chi (v - y) * chi (v' - y)) := by
    intro y
    rw [sq, sum_mul_sum]
    exact sum_congr rfl fun v _ => sum_congr rfl fun v' _ => by ring
  rw [sum_congr rfl fun y _ => e y, sum_comm]
  have e2 : ∀ v : F, ∑ y, ∑ v', f v * f v' * (chi (v - y) * chi (v' - y)) =
      Fintype.card F * f v ^ 2 - f v * ∑ v', f v' := by
    intro v
    rw [sum_comm]
    have : ∀ v', ∑ y, f v * f v' * (chi (v - y) * chi (v' - y)) =
        (if v = v' then (Fintype.card F : ℝ) * (f v * f v') else 0) - f v * f v' := by
      intro v'
      rw [← mul_sum, sum_chi_rev hF]
      split_ifs <;> ring
    rw [sum_congr rfl fun v' _ => this v', sum_sub_distrib, sum_ite_eq univ v, ← mul_sum]
    simp only [mem_univ, ↓reduceIte]
    ring
  rw [sum_congr rfl fun v _ => e2 v, sum_sub_distrib, ← mul_sum, ← sum_mul]
  ring

theorem chi_neg_one_sq : chi (-1 : F) ^ 2 = 1 := chi_sq_of_ne (neg_ne_zero.mpr one_ne_zero)

/-- `T_u(v, w) = q ∑_y a_y χ(y - w)·χ(-1)` with `a_y = χ(u - y)χ(v - y)`. -/
theorem Tu_sq_eq (u v w : F) :
    Tu u v w ^ 2 = (Fintype.card F : ℝ)⁻¹ ^ 2 *
      (∑ y, (chi (u - y) * chi (v - y)) * chi (y - w)) ^ 2 := by
  unfold Tu
  have e : ∑ y, chi (u - y) * chi (v - y) * chi (w - y) =
      chi (-1 : F) * ∑ y, (chi (u - y) * chi (v - y)) * chi (y - w) := by
    rw [mul_sum]
    refine sum_congr rfl fun y _ => ?_
    have : chi (w - y) = chi (-1 : F) * chi (y - w) := by
      rw [← chi_mul]; congr 1; ring
    rw [this]; ring
  rw [e, mul_pow, mul_pow, chi_neg_one_sq, one_mul]

/-- **The row sums of `H_u`** (`lem:rectangle-mellin`): for `v ≠ u`,
`∑_{w ≠ u} H_u(v, w) = 1 - 2q - 2q²`. -/
theorem Hu_row (hF : ringChar F ≠ 2) {u v : F} (huv : v ≠ u) :
    ∑ w ∈ univ.erase u, Hu u v w =
      1 - 2 * (Fintype.card F : ℝ)⁻¹ - 2 * (Fintype.card F : ℝ)⁻¹ ^ 2 := by
  have hp0 : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  set a : F → ℝ := fun y => chi (u - y) * chi (v - y)
  -- the full row sum
  have hall : ∑ w, Hu u v w = (Fintype.card F : ℝ)⁻¹ ^ 2 *
      (Fintype.card F * ∑ y, a y ^ 2 - (∑ y, a y) ^ 2) := by
    simp only [Hu, Tu_sq_eq, ← mul_sum]
    congr 1
    exact sum_conv_sq_eq hF a
  have ha2 : ∑ y, a y ^ 2 = Fintype.card F - 2 := by
    have : ∀ y, a y ^ 2 = 1 - (if y = u then 1 else 0) - (if y = v then 1 else 0) := by
      intro y
      simp only [a, mul_pow]
      by_cases h1 : y = u
      · subst h1; simp [chi_zero, Ne.symm huv]
      · by_cases h2 : y = v
        · subst h2; simp [chi_zero, h1]
        · rw [chi_sq_of_ne (sub_ne_zero.mpr (Ne.symm h1)),
            chi_sq_of_ne (sub_ne_zero.mpr (Ne.symm h2))]
          simp [h1, h2]
    rw [sum_congr rfl fun y _ => this y, sum_sub_distrib, sum_sub_distrib, sum_ite_eq', sum_ite_eq']
    simp
    ring
  have ha1 : ∑ y, a y = -1 := by
    simp only [a]
    rw [sum_chi_rev hF]
    simp [Ne.symm huv]
  have hdiag : Hu u v u = (Fintype.card F : ℝ)⁻¹ ^ 2 := by
    unfold Hu Tu
    have : ∑ y, chi (u - y) * chi (v - y) * chi (u - y) = -chi (v - u) := by
      have e : ∀ y, chi (u - y) * chi (v - y) * chi (u - y) =
          chi (v - y) - if y = u then chi (v - y) else 0 := by
        intro y
        by_cases h : y = u
        · subst h; simp [chi_zero]
        · simp only [h, ↓reduceIte, sub_zero]
          have := chi_sq_of_ne (sub_ne_zero.mpr (Ne.symm h) : u - y ≠ 0)
          rw [show chi (u - y) * chi (v - y) * chi (u - y) = chi (u - y) ^ 2 * chi (v - y) by ring,
            this, one_mul]
      rw [sum_congr rfl fun y _ => e y, sum_sub_distrib, sum_ite_eq' univ u]
      simp only [mem_univ, ↓reduceIte]
      have h0 : ∑ y, chi (v - y) = 0 := by
        have := sum_chi_shift (F := F) hF 0
        rw [← this]
        exact Fintype.sum_equiv ((Equiv.neg F).trans (Equiv.addRight v)) _ _ fun y => by
          simp only [Equiv.trans_apply, Equiv.neg_apply, Equiv.coe_addRight, sub_zero]
          ring_nf
      rw [h0, zero_sub]
    rw [this, mul_pow, neg_sq, chi_sq_of_ne (sub_ne_zero.mpr huv), mul_one]
  have hsplit := sum_erase_add univ (Hu u v) (mem_univ u)
  rw [hall, hdiag, ha2, ha1] at hsplit
  have : ∑ w ∈ univ.erase u, Hu u v w = (Fintype.card F : ℝ)⁻¹ ^ 2 *
      (Fintype.card F * (Fintype.card F - 2) - (-1) ^ 2) - (Fintype.card F : ℝ)⁻¹ ^ 2 := by
    linarith
  rw [this]
  field_simp
  ring

theorem Tu_symm (u v w : F) : Tu u v w = Tu u w v := by
  unfold Tu
  congr 1
  exact sum_congr rfl fun y _ => by ring

/-- **`‖H_u‖ ≤ 1 - 2q - 2q²`** on `F ∖ {u}` (`lem:rectangle-mellin`; Schur test for the
nonnegative symmetric matrix `H_u` with constant row sums). -/
theorem Hu_form_le (hF : ringChar F ≠ 2) (u : F) (f : F → ℝ) :
    |∑ v ∈ univ.erase u, ∑ w ∈ univ.erase u, f v * Hu u v w * f w| ≤
      (1 - 2 * (Fintype.card F : ℝ)⁻¹ - 2 * (Fintype.card F : ℝ)⁻¹ ^ 2) *
        ∑ v ∈ univ.erase u, f v ^ 2 := by
  set R := 1 - 2 * (Fintype.card F : ℝ)⁻¹ - 2 * (Fintype.card F : ℝ)⁻¹ ^ 2
  have hH0 : ∀ v w, 0 ≤ Hu u v w := fun v w => sq_nonneg _
  have hrow : ∀ v ∈ univ.erase u, ∑ w ∈ univ.erase u, Hu u v w = R :=
    fun v hv => Hu_row hF (ne_of_mem_erase hv)
  have hcol : ∀ w ∈ univ.erase u, ∑ v ∈ univ.erase u, Hu u v w = R := by
    intro w hw
    rw [← hrow w hw]
    exact sum_congr rfl fun v _ => by unfold Hu; rw [Tu_symm]
  have key : ∀ v w, |f v * Hu u v w * f w| ≤ Hu u v w * (f v ^ 2 + f w ^ 2) / 2 := by
    intro v w
    rw [abs_mul, abs_mul, abs_of_nonneg (hH0 v w)]
    have h1 : |f v| * |f w| ≤ (f v ^ 2 + f w ^ 2) / 2 := by
      nlinarith [sq_nonneg (|f v| - |f w|), sq_abs (f v), sq_abs (f w)]
    nlinarith [hH0 v w]
  calc |∑ v ∈ univ.erase u, ∑ w ∈ univ.erase u, f v * Hu u v w * f w|
      ≤ ∑ v ∈ univ.erase u, ∑ w ∈ univ.erase u, |f v * Hu u v w * f w| :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun v _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ v ∈ univ.erase u, ∑ w ∈ univ.erase u, Hu u v w * (f v ^ 2 + f w ^ 2) / 2 :=
        sum_le_sum fun v _ => sum_le_sum fun w _ => key v w
    _ = R * ∑ v ∈ univ.erase u, f v ^ 2 := by
        simp only [mul_add, add_div, sum_add_distrib]
        have p1 : ∀ v ∈ univ.erase u,
            ∑ w ∈ univ.erase u, Hu u v w * f v ^ 2 / 2 = R * f v ^ 2 / 2 := by
          intro v hv
          rw [← sum_div, ← sum_mul, hrow v hv]
        have p2 : ∀ w ∈ univ.erase u,
            ∑ v ∈ univ.erase u, Hu u v w * f w ^ 2 / 2 = R * f w ^ 2 / 2 := by
          intro w hw
          rw [← sum_div, ← sum_mul, hcol w hw]
        rw [sum_congr rfl p1, sum_comm (f := fun v w => Hu u v w * f w ^ 2 / 2),
          sum_congr rfl p2, ← sum_add_distrib, mul_sum]
        exact sum_congr rfl fun v _ => by ring

/-! ## Translation and dilation: `H_0` is a multiplicative convolution -/

theorem Tu_transl (u v w : F) : Tu u v w = Tu 0 (v - u) (w - u) := by
  unfold Tu
  congr 1
  refine Fintype.sum_equiv (Equiv.subRight u) _ _ fun y => ?_
  simp only [Equiv.subRight_apply]
  ring_nf

theorem chi_cube (v : F) (hv : v ≠ 0) : chi v * chi v * chi v = chi v := by
  have := chi_sq_of_ne hv
  rw [show chi v * chi v * chi v = chi v ^ 2 * chi v by ring, this, one_mul]

/-- **Dilation**: `T_0(v, w) = χ(v)T_0(1, w/v)` for `v ≠ 0`. -/
theorem T0_dil {v : F} (hv : v ≠ 0) (w : F) : Tu 0 v w = chi v * Tu 0 1 (w / v) := by
  unfold Tu
  rw [(Equiv.sum_comp (Equiv.mulLeft₀ v hv)
    (fun y => chi (0 - y) * chi (v - y) * chi (w - y))).symm]
  show (Fintype.card F : ℝ)⁻¹ * ∑ y, chi (0 - v * y) * chi (v - v * y) * chi (w - v * y) = _
  have e : ∀ y : F, chi (0 - v * y) * chi (v - v * y) * chi (w - v * y) =
      chi v * (chi (0 - y) * chi (1 - y) * chi (w / v - y)) := by
    intro y
    have e1 : 0 - v * y = v * (0 - y) := by ring
    have e2 : v - v * y = v * (1 - y) := by ring
    have e3 : w - v * y = v * (w / v - y) := by field_simp
    rw [e1, e2, e3, chi_mul, chi_mul, chi_mul]
    have := chi_cube v hv
    linear_combination (chi (0 - y) * chi (1 - y) * chi (w / v - y)) * this
  rw [sum_congr rfl fun y _ => e y, ← mul_sum]
  ring

/-- `H_0(v, w) = H_0(1, w/v)` for `v ≠ 0`. -/
theorem H0_dil {v : F} (hv : v ≠ 0) (w : F) : Hu 0 v w = Hu 0 1 (w / v) := by
  unfold Hu
  rw [T0_dil hv, mul_pow, chi_sq_of_ne hv, one_mul]

/-- **The characters are eigenvectors of `H_0`** on `F^×` (`lem:rectangle-mellin`, proof): for a
multiplicative character `ρ` and `v ≠ 0`, `∑_w H_0(v, w)ρ(w) = λ_ρ ρ(v)`,
`λ_ρ = ∑_t H_0(1, t)ρ(t)` (`ρ(0) = 0`, so the sums are over `F^×`). -/
theorem H0_eigen (ρ : MulChar F ℂ) {v : F} (hv : v ≠ 0) :
    ∑ w, (Hu 0 v w : ℂ) * ρ w = (∑ t, (Hu 0 1 t : ℂ) * ρ t) * ρ v := by
  calc ∑ w, (Hu 0 v w : ℂ) * ρ w = ∑ t, (Hu 0 v (v * t) : ℂ) * ρ (v * t) :=
        (Equiv.sum_comp (Equiv.mulLeft₀ v hv) (fun w => (Hu 0 v w : ℂ) * ρ w)).symm
    _ = ∑ t, (Hu 0 1 t : ℂ) * ρ t * ρ v := by
        refine sum_congr rfl fun t _ => ?_
        rw [H0_dil hv, mul_div_cancel_left₀ t hv, map_mul]
        ring
    _ = _ := by rw [sum_mul]

/-! ## The eigenvalues -/

/-- `T_t = ∑_y χ(y(y - 1)(y - t))` (`Target.legendreSum` on `𝔽_p`). -/
noncomputable def legT (t : F) : ℤ := ∑ y, quadraticChar F (y * (y - 1) * (y - t))

theorem Hu01_eq (t : F) :
    Hu 0 1 t = (Fintype.card F : ℝ)⁻¹ ^ 2 * ((legT t : ℤ) : ℝ) ^ 2 := by
  unfold Hu Tu legT
  have e : ∑ y, chi (0 - y) * chi (1 - y) * chi (t - y) =
      chi (-1 : F) * ((∑ y, quadraticChar F (y * (y - 1) * (y - t)) : ℤ) : ℝ) := by
    rw [Int.cast_sum, mul_sum]
    refine sum_congr rfl fun y _ => ?_
    rw [← chi_mul, ← chi_mul]
    show chi _ = chi (-1 : F) * chi (y * (y - 1) * (y - t))
    rw [← chi_mul]
    congr 1
    ring
  rw [e, mul_pow, mul_pow, chi_neg_one_sq, one_mul]

theorem legT_one (hF : ringChar F ≠ 2) : legT (1 : F) = -1 := by
  unfold legT
  have e : ∀ y : F, quadraticChar F (y * (y - 1) * (y - 1)) =
      quadraticChar F y - if y = 1 then quadraticChar F y else 0 := by
    intro y
    by_cases h : y = 1
    · subst h; simp
    · simp only [h, ↓reduceIte, sub_zero]
      have h1 : quadraticChar F (y - 1) * quadraticChar F (y - 1) = 1 := by
        rw [← sq]; exact quadraticChar_sq_one (sub_ne_zero.mpr h)
      rw [map_mul, map_mul, mul_assoc, h1, mul_one]
  rw [sum_congr rfl fun y _ => e y, sum_sub_distrib, sum_ite_eq' univ (1 : F),
    quadraticChar_sum_zero hF]
  simp

theorem filter_ne01 : (univ.filter fun t : F => t ≠ 0 ∧ t ≠ 1) = (univ.erase 0).erase 1 := by
  ext t
  simp only [mem_filter, mem_univ, true_and, mem_erase, ne_eq]
  tauto

/-- **The eigenvalue at a nontrivial character** (`lem:rectangle-mellin`, proof):
`λ_ρ = -q + q² + p^{-2} ∑_{t ≠ 0,1} ρ(t)(T_t² - p)`. -/
theorem eigen_formula (hF : ringChar F ≠ 2) {ρ : MulChar F ℂ} (hρ : ρ ≠ 1) :
    ∑ t, (Hu 0 1 t : ℂ) * ρ t =
      -((Fintype.card F : ℝ)⁻¹ : ℂ) + ((Fintype.card F : ℝ)⁻¹ : ℂ) ^ 2 +
        ((Fintype.card F : ℝ)⁻¹ : ℂ) ^ 2 * ∑ t ∈ univ.filter (fun t : F => t ≠ 0 ∧ t ≠ 1),
          ρ t * ((legT t ^ 2 - (Fintype.card F : ℤ) : ℤ) : ℂ) := by
  have hp0 : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h01 : (0 : F) ≠ 1 := zero_ne_one
  have hsum : ∑ t, ρ t = 0 := MulChar.sum_eq_zero_of_ne_one hρ
  -- the full sum, split at `0` and `1`
  have split : ∀ g : F → ℂ, ∑ t, g t = g 0 + g 1 +
      ∑ t ∈ univ.filter (fun t : F => t ≠ 0 ∧ t ≠ 1), g t := by
    intro g
    rw [filter_ne01, ← add_sum_erase _ _ (mem_univ 0),
      ← add_sum_erase _ _ (mem_erase.mpr ⟨h01.symm, mem_univ 1⟩)]
    ring
  have hρ0 : ρ 0 = 0 := MulChar.map_nonunit ρ not_isUnit_zero
  have hρ1 : ρ 1 = 1 := map_one ρ
  have hrest : ∑ t ∈ univ.filter (fun t : F => t ≠ 0 ∧ t ≠ 1), ρ t = -1 := by
    have := split (fun t => ρ t)
    rw [hsum, hρ0, hρ1] at this
    linear_combination -this
  simp only [Hu01_eq]
  push_cast
  rw [split (fun t => ((Fintype.card F : ℂ)⁻¹ ^ 2 * (legT t : ℂ) ^ 2) * ρ t), legT_one hF, hρ0, hρ1]
  have e : ∀ t, ρ t * (((legT t : ℂ)) ^ 2 - (Fintype.card F : ℂ)) =
      ρ t * (legT t : ℂ) ^ 2 - (Fintype.card F : ℂ) * ρ t := fun t => by ring
  simp only [e, sum_sub_distrib, ← mul_sum, hrest]
  have e2 : ∑ t ∈ univ.filter (fun t : F => t ≠ 0 ∧ t ≠ 1),
      (Fintype.card F : ℂ)⁻¹ ^ 2 * (legT t : ℂ) ^ 2 * ρ t =
      (Fintype.card F : ℂ)⁻¹ ^ 2 * ∑ t ∈ univ.filter (fun t : F => t ≠ 0 ∧ t ≠ 1),
        ρ t * (legT t : ℂ) ^ 2 := by
    rw [mul_sum]; exact sum_congr rfl fun t _ => by ring
  rw [e2]
  field_simp
  ring

end Sarkozy.L20Cap
