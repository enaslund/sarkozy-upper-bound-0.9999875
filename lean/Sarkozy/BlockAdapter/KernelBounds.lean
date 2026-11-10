module

public import Sarkozy.Spectral.GlueCut

@[expose] public section

/-!
# Two elementary bounds for normalized kernel operators

For a finite law `μ`, a symmetric kernel `K ≥ 0` and `Z > 0`, the operator
`A = kernelOp μ (K/Z)` on `EuclideanSpace ℝ Ω` (WP-A's realization of `T_{K/Z}` on `L²(μ)`):

* `kernel_quad_upper` (Schur test): if every row mean `∑_y μ(y) K(x, y)` at a point of positive
  mass is at most `Z`, then `A ⪯ 1`;
* `kernel_quad_lower` (collision bound): if `K ≤ 1` and `1 - K ≤ C` for a kernel `C` whose row
  and column means are at most `c₀`, then `A ⪰ -c₀/Z`.

Used for the cut E21 (`E21.lean`), whose kernel is the disjointness indicator.
-/

open scoped InnerProductSpace
open Finset

namespace Sarkozy.BlockAdapter

open Sarkozy

variable {Ω : Type*} [Fintype Ω]

theorem norm_sq_eq_sum (v : EuclideanSpace ℝ Ω) : ‖v‖ ^ 2 = ∑ x, v.ofLp x ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]

/-- `|√m u| |√m' u'| ≤ (u² m' + u'² m)/2`. -/
theorem amgm_sqrt {m m' u u' : ℝ} (hm : 0 ≤ m) (hm' : 0 ≤ m') :
    (√m * u) * (√m' * u') ≤ (u ^ 2 * m' + u' ^ 2 * m) / 2 := by
  have h1 := Real.sq_sqrt hm
  have h2 := Real.sq_sqrt hm'
  nlinarith [sq_nonneg (√m' * u - √m * u')]

theorem abs_amgm_sqrt {m m' u u' : ℝ} (hm : 0 ≤ m) (hm' : 0 ≤ m') :
    |√m * u| * |√m' * u'| ≤ (u ^ 2 * m' + u' ^ 2 * m) / 2 := by
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg m), abs_of_nonneg (Real.sqrt_nonneg m')]
  have h := amgm_sqrt (u := |u|) (u' := |u'|) hm hm'
  simpa only [sq_abs] using h

theorem split_sum (C : Ω → Ω → ℝ) (u m : Ω → ℝ) :
    ∑ x, ∑ y, C x y * ((u x ^ 2 * m y + u y ^ 2 * m x) / 2) =
      (∑ x, u x ^ 2 * ∑ y, m y * C x y + ∑ y, u y ^ 2 * ∑ x, m x * C x y) / 2 := by
  calc ∑ x, ∑ y, C x y * ((u x ^ 2 * m y + u y ^ 2 * m x) / 2)
      = (∑ x, ∑ y, u x ^ 2 * (m y * C x y) + ∑ x, ∑ y, u y ^ 2 * (m x * C x y)) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ = _ := by
        rw [Finset.sum_comm (f := fun x y => u y ^ 2 * (m x * C x y))]
        simp only [← Finset.mul_sum]

/-- **The Schur test for a normalized kernel**: if `K ≥ 0` is symmetric and every row mean
`∑_y μ(y) K(x, y)` at a point of positive mass is at most `Z > 0`, then
`⟨v, kernelOp μ (K/Z) v⟩ ≤ ‖v‖²`. -/
theorem kernel_quad_upper (μ : FiniteLaw Ω) (K : Ω → Ω → ℝ) (hK0 : ∀ x y, 0 ≤ K x y)
    (hKs : ∀ x y, K y x = K x y) {Z : ℝ} (hZ : 0 < Z)
    (hrow : ∀ x, μ.weight x ≠ 0 → ∑ y, μ.weight y * K x y ≤ Z) (v : EuclideanSpace ℝ Ω) :
    ⟪v, Spectral.kernelOp μ (fun x y => K x y / Z) v⟫_ℝ ≤ ‖v‖ ^ 2 := by
  classical
  rw [Spectral.inner_kernelOp, norm_sq_eq_sum]
  set w : Ω → ℝ := fun x => if μ.weight x = 0 then 0 else v.ofLp x with hw
  have ha : ∀ x, √(μ.weight x) * v.ofLp x = √(μ.weight x) * w x := by
    intro x
    by_cases h : μ.weight x = 0
    · simp [hw, h]
    · simp [hw, h]
  have hterm : ∀ x y, v.ofLp x * (√(μ.weight x) * (K x y / Z) * √(μ.weight y)) * v.ofLp y ≤
      K x y * ((w x ^ 2 * μ.weight y + w y ^ 2 * μ.weight x) / 2) / Z := by
    intro x y
    have e : v.ofLp x * (√(μ.weight x) * (K x y / Z) * √(μ.weight y)) * v.ofLp y =
        K x y * ((√(μ.weight x) * w x) * (√(μ.weight y) * w y)) / Z := by
      rw [← ha x, ← ha y]
      ring
    rw [e]
    have h := mul_le_mul_of_nonneg_left (amgm_sqrt (u := w x) (u' := w y) (μ.nonneg x)
      (μ.nonneg y)) (hK0 x y)
    exact div_le_div_of_nonneg_right h hZ.le
  have hw2 : ∀ x, w x ^ 2 * ∑ y, μ.weight y * K x y ≤ w x ^ 2 * Z := by
    intro x
    by_cases h : μ.weight x = 0
    · simp [hw, h]
    · exact mul_le_mul_of_nonneg_left (hrow x h) (sq_nonneg _)
  have hw2' : ∀ y, w y ^ 2 * ∑ x, μ.weight x * K x y ≤ w y ^ 2 * Z := by
    intro y
    have e : ∑ x, μ.weight x * K x y = ∑ x, μ.weight x * K y x :=
      Finset.sum_congr rfl fun x _ => by rw [hKs y x]
    rw [e]
    exact hw2 y
  have hwv : ∀ x, w x ^ 2 ≤ v.ofLp x ^ 2 := by
    intro x
    by_cases h : μ.weight x = 0
    · have h0 : w x = 0 := by simp [hw, h]
      rw [h0]
      nlinarith [sq_nonneg (v.ofLp x)]
    · simp [hw, h]
  calc ∑ x, ∑ y, v.ofLp x * (√(μ.weight x) * (K x y / Z) * √(μ.weight y)) * v.ofLp y
      ≤ ∑ x, ∑ y, K x y * ((w x ^ 2 * μ.weight y + w y ^ 2 * μ.weight x) / 2) / Z :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y
    _ = (∑ x, w x ^ 2 * ∑ y, μ.weight y * K x y + ∑ y, w y ^ 2 * ∑ x, μ.weight x * K x y) /
          2 / Z := by
        rw [← split_sum, Finset.sum_div]
        exact Finset.sum_congr rfl fun x _ => by rw [Finset.sum_div]
    _ ≤ (∑ x, w x ^ 2 * Z + ∑ y, w y ^ 2 * Z) / 2 / Z := by
        apply div_le_div_of_nonneg_right _ hZ.le
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact add_le_add (Finset.sum_le_sum fun x _ => hw2 x)
          (Finset.sum_le_sum fun y _ => hw2' y)
    _ = ∑ x, w x ^ 2 := by
        rw [← Finset.sum_mul]
        field_simp
        ring
    _ ≤ ∑ x, v.ofLp x ^ 2 := Finset.sum_le_sum fun x _ => hwv x

/-- **The collision bound for a normalized kernel**: if `K ≤ 1`, `1 - K ≤ C` and the row and
column means of `C` are at most `c₀`, then `⟨v, kernelOp μ (K/Z) v⟩ ≥ -(c₀/Z) ‖v‖²`. -/
theorem kernel_quad_lower (μ : FiniteLaw Ω) (K C : Ω → Ω → ℝ) (hK1 : ∀ x y, K x y ≤ 1)
    (hC : ∀ x y, 1 - K x y ≤ C x y) {Z c₀ : ℝ} (hZ : 0 < Z)
    (hrow : ∀ x, ∑ y, μ.weight y * C x y ≤ c₀) (hcol : ∀ y, ∑ x, μ.weight x * C x y ≤ c₀)
    (v : EuclideanSpace ℝ Ω) :
    -(c₀ / Z) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.kernelOp μ (fun x y => K x y / Z) v⟫_ℝ := by
  rw [Spectral.inner_kernelOp, norm_sq_eq_sum]
  set a : Ω → ℝ := fun x => √(μ.weight x) * v.ofLp x with ha
  have e : ∑ x, ∑ y, v.ofLp x * (√(μ.weight x) * (K x y / Z) * √(μ.weight y)) * v.ofLp y =
      ((∑ x, a x) ^ 2 - ∑ x, ∑ y, (1 - K x y) * (a x * a y)) / Z := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [ha]
    field_simp
    ring
  have hterm : ∀ x y, (1 - K x y) * (a x * a y) ≤
      C x y * ((v.ofLp x ^ 2 * μ.weight y + v.ofLp y ^ 2 * μ.weight x) / 2) := by
    intro x y
    have h0 : 0 ≤ 1 - K x y := by linarith [hK1 x y]
    have hC0 : 0 ≤ C x y := le_trans h0 (hC x y)
    calc (1 - K x y) * (a x * a y) ≤ (1 - K x y) * (|a x| * |a y|) := by
          rw [← abs_mul]
          exact mul_le_mul_of_nonneg_left (le_abs_self _) h0
      _ ≤ C x y * (|a x| * |a y|) :=
          mul_le_mul_of_nonneg_right (hC x y) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ ≤ C x y * ((v.ofLp x ^ 2 * μ.weight y + v.ofLp y ^ 2 * μ.weight x) / 2) :=
          mul_le_mul_of_nonneg_left (abs_amgm_sqrt (μ.nonneg x) (μ.nonneg y)) hC0
  have hcoll : ∑ x, ∑ y, (1 - K x y) * (a x * a y) ≤ c₀ * ∑ x, v.ofLp x ^ 2 := by
    calc ∑ x, ∑ y, (1 - K x y) * (a x * a y)
        ≤ ∑ x, ∑ y, C x y * ((v.ofLp x ^ 2 * μ.weight y + v.ofLp y ^ 2 * μ.weight x) / 2) :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y
      _ = (∑ x, v.ofLp x ^ 2 * ∑ y, μ.weight y * C x y +
            ∑ y, v.ofLp y ^ 2 * ∑ x, μ.weight x * C x y) / 2 := split_sum _ _ _
      _ ≤ (∑ x, v.ofLp x ^ 2 * c₀ + ∑ y, v.ofLp y ^ 2 * c₀) / 2 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact add_le_add
            (Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hrow x) (sq_nonneg _))
            (Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hcol y) (sq_nonneg _))
      _ = c₀ * ∑ x, v.ofLp x ^ 2 := by
          rw [← Finset.sum_mul]
          ring
  rw [e]
  have hsq : 0 ≤ (∑ x, a x) ^ 2 := sq_nonneg _
  have key : ((∑ x, a x) ^ 2 - ∑ x, ∑ y, (1 - K x y) * (a x * a y)) / Z -
      (-(c₀ / Z) * ∑ x, v.ofLp x ^ 2) =
      ((∑ x, a x) ^ 2 - ∑ x, ∑ y, (1 - K x y) * (a x * a y) + c₀ * ∑ x, v.ofLp x ^ 2) / Z := by
    field_simp
    ring
  have hnn : 0 ≤ ((∑ x, a x) ^ 2 - ∑ x, ∑ y, (1 - K x y) * (a x * a y) +
      c₀ * ∑ x, v.ofLp x ^ 2) / Z := div_nonneg (by linarith) hZ.le
  linarith

end Sarkozy.BlockAdapter
