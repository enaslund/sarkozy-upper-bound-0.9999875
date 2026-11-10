module

public import Sarkozy.PositiveRoots.FiniteMatrixBound

/-! Quadratic lower bounds are preserved by convex combinations of matrices. -/

@[expose] public section

namespace Sarkozy.PositiveRoots

open Finset Sarkozy.SpectralC

variable {U : Type*} [Fintype U]

theorem qform_add (A B : U → U → ℂ) (x : U → ℂ) :
    qform (fun i j => A i j + B i j) x = qform A x + qform B x :=
  bform_add A B x x

theorem lower_bound_convex (A B : U → U → ℂ) {a g h : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hA : ∀ x, -g * ∑ i, ‖x i‖ ^ 2 ≤ (qform A x).re)
    (hB : ∀ x, -h * ∑ i, ‖x i‖ ^ 2 ≤ (qform B x).re) (x : U → ℂ) :
    -((1 - a) * g + a * h) * ∑ i, ‖x i‖ ^ 2 ≤
      (qform (fun i j => ((1 - a : ℝ) : ℂ) * A i j + (a : ℂ) * B i j) x).re := by
  rw [qform_add, CoherentMatrix.qform_scalar, CoherentMatrix.qform_scalar,
    Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have h0 := mul_le_mul_of_nonneg_left (hA x) (sub_nonneg.mpr ha1)
  have h1 := mul_le_mul_of_nonneg_left (hB x) ha
  nlinarith

theorem lower_bound_scalar (A : U → U → ℂ) {s g : ℝ} (hs : 0 ≤ s)
    (hA : ∀ x, -g * ∑ i, ‖x i‖ ^ 2 ≤ (qform A x).re) (x : U → ℂ) :
    -(s * g) * ∑ i, ‖x i‖ ^ 2 ≤ (qform (fun i j => (s : ℂ) * A i j) x).re := by
  rw [CoherentMatrix.qform_scalar, Complex.re_ofReal_mul]
  have h := mul_le_mul_of_nonneg_left (hA x) hs
  nlinarith

end Sarkozy.PositiveRoots
