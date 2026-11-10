module

public import Sarkozy.JointRows.ChartBound

/-! A normalized covariance bound transfers to the actual marginal variances. -/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows

open Finset Sarkozy.FiveType

variable {X : Type*} [Fintype X]

theorem expect_dens1 (μ : FiniteLaw X) (K : X → X → ℝ) (hZ : RowsA.mass μ K ≠ 0) :
    μ.expect (RowsA.dens1 μ K) = 1 := by
  unfold RowsA.dens1
  simp_rw [div_eq_mul_inv]
  rw [FiniteLaw.expect_mul_const, ← kf_one_one]
  exact mul_inv_cancel₀ hZ

theorem expect_dens2 (μ : FiniteLaw X) (K : X → X → ℝ) (hZ : RowsA.mass μ K ≠ 0) :
    μ.expect (RowsA.dens2 μ K) = 1 := by
  unfold RowsA.dens2
  simp_rw [div_eq_mul_inv]
  rw [FiniteLaw.expect_mul_const, ← kf_one_one']
  exact mul_inv_cancel₀ hZ

theorem chart_form (μ : FiniteLaw X) (K : X → X → ℝ) (f g : X → ℝ) :
    kf μ (RowsA.chartKernel μ K) f g = kf μ K f g / RowsA.mass μ K -
      μ.expect (fun x => RowsA.dens1 μ K x * f x) *
        μ.expect (fun y => RowsA.dens2 μ K y * g y) := by
  simp only [kf, RowsA.chartKernel, FiniteLaw.expect, sum_div, sum_mul_sum,
    ← sum_sub_distrib]
  exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring

theorem dens1_moment (μ : FiniteLaw X) (K : X → X → ℝ) (f : X → ℝ) :
    μ.expect (fun x => RowsA.dens1 μ K x * f x) =
      kf μ K f (fun _ => 1) / RowsA.mass μ K := by
  rw [kf_one_right]
  simp only [ip, RowsA.dens1, FiniteLaw.expect, sum_div]
  exact sum_congr rfl fun x _ => by ring

theorem dens2_moment (μ : FiniteLaw X) (K : X → X → ℝ) (g : X → ℝ) :
    μ.expect (fun y => RowsA.dens2 μ K y * g y) =
      kf μ K (fun _ => 1) g / RowsA.mass μ K := by
  rw [kf_one_left]
  simp only [ip, RowsA.dens2, FiniteLaw.expect, sum_div]
  exact sum_congr rfl fun x _ => by ring

theorem chart_shift (μ : FiniteLaw X) (K : X → X → ℝ)
    (hZ : RowsA.mass μ K ≠ 0) (f g : X → ℝ) (a b : ℝ) :
    kf μ (RowsA.chartKernel μ K) (fun x => f x - a) (fun y => g y - b) =
      kf μ (RowsA.chartKernel μ K) f g := by
  have hleft (g : X → ℝ) : kf μ (RowsA.chartKernel μ K) (fun _ => 1) g = 0 := by
    rw [chart_form]
    simp only [mul_one, expect_dens1 μ K hZ, one_mul, dens2_moment, sub_self]
  have hright (f : X → ℝ) : kf μ (RowsA.chartKernel μ K) f (fun _ => 1) = 0 := by
    rw [chart_form]
    simp only [mul_one, expect_dens2 μ K hZ, dens1_moment, sub_self]
  have hf : (fun x => f x - a) = fun x => -a + f x := funext fun _ => by ring
  have hg : (fun y => g y - b) = fun y => -b + g y := funext fun _ => by ring
  rw [hf, hg, kf_add_const, hleft, hleft, hright]
  ring

theorem weighted_center_variance (μ : FiniteLaw X) (φ f : X → ℝ) (hφ : μ.expect φ = 1) :
    μ.expect (fun x => φ x * (f x - μ.expect (fun t => φ t * f t)) ^ 2) = wvar μ φ f := by
  let m := μ.expect (fun t => φ t * f t)
  have he : (fun x => φ x * (f x - m) ^ 2) =
      fun x => (φ x * f x ^ 2 - (2 * m) * (φ x * f x)) + m ^ 2 * φ x :=
    funext fun _ => by ring
  change μ.expect (fun x => φ x * (f x - m) ^ 2) = _
  rw [he, FiniteLaw.expect_add, FiniteLaw.expect_sub,
    FiniteLaw.expect_const_mul, FiniteLaw.expect_const_mul, hφ]
  unfold wvar
  dsimp [m]
  ring

theorem weighted_center_norm (μ : FiniteLaw X) (φ f : X → ℝ) {R : ℝ}
    (hR : 0 < R) (hφ : μ.expect φ = 1)
    (hlower : ∀ x, μ.weight x ≠ 0 → R⁻¹ ≤ φ x) :
    nrm μ (fun x => f x - μ.expect (fun t => φ t * f t)) ≤
      Real.sqrt R * Real.sqrt (wvar μ φ f) := by
  let v := fun x => f x - μ.expect (fun t => φ t * f t)
  have hpoint (x : X) (hx : μ.weight x ≠ 0) : 1 ≤ R * φ x := by
    have h := mul_le_mul_of_nonneg_left (hlower x hx) hR.le
    simpa only [mul_inv_cancel₀ hR.ne'] using h
  have hm : μ.expect (fun x => v x ^ 2) ≤ R * μ.expect (fun x => φ x * v x ^ 2) := by
    rw [← FiniteLaw.expect_const_mul]
    unfold FiniteLaw.expect
    apply sum_le_sum
    intro x _
    by_cases hx : μ.weight x = 0
    · simp [hx]
    · apply mul_le_mul_of_nonneg_left _ (μ.nonneg x)
      nlinarith [mul_le_mul_of_nonneg_right (hpoint x hx) (sq_nonneg (v x))]
  rw [weighted_center_variance μ φ f hφ] at hm
  unfold nrm ip
  simp only [← sq]
  exact (Real.sqrt_le_sqrt hm).trans_eq (Real.sqrt_mul hR.le _)

theorem chart_variance_bound (μ : FiniteLaw X) (K : X → X → ℝ) {s R : ℝ}
    (hZ : RowsA.mass μ K ≠ 0) (hs : FormBound μ (RowsA.chartKernel μ K) s)
    (hR : 0 < R)
    (hL : ∀ x, μ.weight x ≠ 0 → R⁻¹ ≤ RowsA.dens1 μ K x)
    (hM : ∀ y, μ.weight y ≠ 0 → R⁻¹ ≤ RowsA.dens2 μ K y) (f g : X → ℝ) :
    |kf μ (RowsA.chartKernel μ K) f g| ≤
      (s * R) * Real.sqrt (wvar μ (RowsA.dens1 μ K) f) *
        Real.sqrt (wvar μ (RowsA.dens2 μ K) g) := by
  have hs0 := RowsA.FormBound.nonneg' hs
  let a := μ.expect (fun x => RowsA.dens1 μ K x * f x)
  let b := μ.expect (fun y => RowsA.dens2 μ K y * g y)
  rw [← chart_shift μ K hZ f g a b]
  apply (hs _ _).trans
  have hf := weighted_center_norm μ _ f hR (expect_dens1 μ K hZ) hL
  have hg := weighted_center_norm μ _ g hR (expect_dens2 μ K hZ) hM
  have hn : 0 ≤ nrm μ (fun y => g y - b) := FiveType.nrm_nonneg _ _
  have h := mul_le_mul (mul_le_mul_of_nonneg_left hf hs0) hg hn
    (mul_nonneg hs0 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  apply h.trans_eq
  calc s * (Real.sqrt R * Real.sqrt (wvar μ (RowsA.dens1 μ K) f)) *
      (Real.sqrt R * Real.sqrt (wvar μ (RowsA.dens2 μ K) g)) =
      s * (Real.sqrt R * Real.sqrt R) * Real.sqrt (wvar μ (RowsA.dens1 μ K) f) *
        Real.sqrt (wvar μ (RowsA.dens2 μ K) g) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hR.le]

end Sarkozy.JointRows
