module

public import Sarkozy.JointRows.CorrelationTransport

/-! A constant rescaling of the weighted joint kernel disappears on normalization. -/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows

open Finset Sarkozy.FiveType

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem kf_eq_scaled (μ : FiniteLaw X) (ν : FiniteLaw Y)
    (K : X → X → ℝ) (T : Y → Y → ℝ) (e : X ≃ Y) (a : ℝ)
    (h : ∀ x y, μ.weight x * μ.weight y * K x y =
      a * (ν.weight (e x) * ν.weight (e y) * T (e x) (e y))) (f g : Y → ℝ) :
    kf μ K (fun x => f (e x)) (fun x => g (e x)) = a * kf ν T f g := by
  unfold kf
  rw [← e.sum_comp (fun x => ∑ y, ν.weight x * ν.weight y * (f x * T x y * g y))]
  simp_rw [← e.sum_comp (fun y => ν.weight _ * ν.weight y * (f _ * T _ y * g y))]
  rw [mul_sum]
  apply sum_congr rfl
  intro x _
  rw [mul_sum]
  apply sum_congr rfl
  intro y _
  calc μ.weight x * μ.weight y * (f (e x) * K x y * g (e y)) =
      (μ.weight x * μ.weight y * K x y) * f (e x) * g (e y) := by ring
    _ = _ := by rw [h]; ring

theorem normalized_form_of_scaled (μ : FiniteLaw X) (ν : FiniteLaw Y)
    (K : X → X → ℝ) (T : Y → Y → ℝ) (e : X ≃ Y) {a : ℝ} (ha : a ≠ 0)
    (h : ∀ x y, μ.weight x * μ.weight y * K x y =
      a * (ν.weight (e x) * ν.weight (e y) * T (e x) (e y))) (f g : Y → ℝ) :
    kf ν T f g / RowsA.mass ν T =
      kf μ K (fun x => f (e x)) (fun x => g (e x)) / RowsA.mass μ K := by
  have hm : RowsA.mass μ K = a * RowsA.mass ν T :=
    kf_eq_scaled μ ν K T e a h (fun _ => 1) (fun _ => 1)
  rw [kf_eq_scaled μ ν K T e a h f g, hm, mul_div_mul_left _ _ ha]

end Sarkozy.JointRows
