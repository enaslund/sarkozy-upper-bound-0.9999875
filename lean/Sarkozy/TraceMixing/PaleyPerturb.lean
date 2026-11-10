module

public import Sarkozy.TraceMixing.Kernel

/-!
# Density perturbation (`lem:paley-triple`(f))

`paper/sections/12_labellings.tex`, `lem:paley-triple`(f), on any finite set: let `m = g ν` with
`|g - 1| ≤ e` on the support of `ν` (stated as `|m(x) - ν(x)| ≤ e ν(x)`). Then for all
`F, G`

* `inner_perturb`: `|⟨F, G⟩_m - ⟨F, G⟩_ν| ≤ e ‖F‖_ν ‖G‖_ν`;
* `norm_perturb`: `(1 - e) ‖F‖²_ν ≤ ‖F‖²_m ≤ (1 + e) ‖F‖²_ν`.

With `F = V_i f`, `G = V_j h` (or `G = A h`), and uniform coordinate marginals under both laws
(so `‖V_i f‖_m = ‖f‖ = ‖V_i f‖_ν`), these are the remaining assertions of (f): the
correlations `⟨V_i f, V_j h⟩` differ by at most `e ‖f‖ ‖h‖`, and
`|⟨f, (V^*_{i,m} - V^*_{i,ν}) A h⟩| = |⟨V_i f, A h⟩_m - ⟨V_i f, A h⟩_ν| ≤ e ‖f‖ ‖A h‖_ν`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.TraceMixing

variable {Ω : Type*} [Fintype Ω]

/-- **`|⟨F, G⟩_m - ⟨F, G⟩_ν| ≤ e ‖F‖_ν ‖G‖_ν`.** -/
theorem inner_perturb {ν m : Ω → ℝ} (hν : ∀ x, 0 ≤ ν x) {e : ℝ} (he : 0 ≤ e)
    (hm : ∀ x, |m x - ν x| ≤ e * ν x) (F G : Ω → ℝ) :
    |∑ x, m x * (F x * G x) - ∑ x, ν x * (F x * G x)| ≤
      e * (Real.sqrt (∑ x, ν x * F x ^ 2) * Real.sqrt (∑ x, ν x * G x ^ 2)) := by
  rw [← Finset.sum_sub_distrib]
  have h1 : |∑ x, (m x * (F x * G x) - ν x * (F x * G x))| ≤
      e * ∑ x, ν x * (|F x| * |G x|) := by
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [← sub_mul, abs_mul, abs_mul]
    calc |m x - ν x| * (|F x| * |G x|) ≤ e * ν x * (|F x| * |G x|) :=
          mul_le_mul_of_nonneg_right (hm x) (by positivity)
      _ = e * (ν x * (|F x| * |G x|)) := by ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ (fun x => Real.sqrt (ν x) * |F x|)
    (fun x => Real.sqrt (ν x) * |G x|)
  have he1 (x : Ω) : Real.sqrt (ν x) * |F x| * (Real.sqrt (ν x) * |G x|) =
      ν x * (|F x| * |G x|) := by
    rw [show Real.sqrt (ν x) * |F x| * (Real.sqrt (ν x) * |G x|) =
      (Real.sqrt (ν x) * Real.sqrt (ν x)) * (|F x| * |G x|) by ring, Real.mul_self_sqrt (hν x)]
  have he2 (x : Ω) (H : Ω → ℝ) : (Real.sqrt (ν x) * |H x|) ^ 2 = ν x * H x ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (hν x), sq_abs]
  simp only [he1, he2] at hcs
  have hS0 : 0 ≤ ∑ x, ν x * (|F x| * |G x|) :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (hν x) (by positivity))
  have hA : 0 ≤ ∑ x, ν x * F x ^ 2 := Finset.sum_nonneg (fun x _ => mul_nonneg (hν x) (sq_nonneg _))
  have h2 : ∑ x, ν x * (|F x| * |G x|) ≤
      Real.sqrt (∑ x, ν x * F x ^ 2) * Real.sqrt (∑ x, ν x * G x ^ 2) := by
    rw [← Real.sqrt_mul hA]
    exact Real.le_sqrt_of_sq_le hcs
  calc _ ≤ e * ∑ x, ν x * (|F x| * |G x|) := h1
    _ ≤ e * (Real.sqrt (∑ x, ν x * F x ^ 2) * Real.sqrt (∑ x, ν x * G x ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 he

/-- **`(1 - e) ‖F‖²_ν ≤ ‖F‖²_m ≤ (1 + e) ‖F‖²_ν`.** -/
theorem norm_perturb {ν m : Ω → ℝ} {e : ℝ}
    (hm : ∀ x, |m x - ν x| ≤ e * ν x) (F : Ω → ℝ) :
    (1 - e) * ∑ x, ν x * F x ^ 2 ≤ ∑ x, m x * F x ^ 2 ∧
      ∑ x, m x * F x ^ 2 ≤ (1 + e) * ∑ x, ν x * F x ^ 2 := by
  have hpt (x : Ω) : (1 - e) * (ν x * F x ^ 2) ≤ m x * F x ^ 2 ∧
      m x * F x ^ 2 ≤ (1 + e) * (ν x * F x ^ 2) := by
    have h := abs_le.mp (hm x)
    have hF : 0 ≤ F x ^ 2 := sq_nonneg _
    constructor <;> nlinarith [h.1, h.2]
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun x _ => (hpt x).1)
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun x _ => (hpt x).2)

end Sarkozy.TraceMixing
