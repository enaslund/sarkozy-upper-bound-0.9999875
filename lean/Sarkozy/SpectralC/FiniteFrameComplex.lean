module

public import Sarkozy.SpectralC.FiniteFrame

/-! Real feature analysis bounds extend to complex test functions component by component. -/

@[expose] public section

namespace Sarkozy.SpectralC

open Finset
open scoped BigOperators

variable {I X : Type*} [Fintype I] [Fintype X]

noncomputable def complexFeatureAdj (μ : FiniteLaw X) (W : I → X → ℝ)
    (f : X → ℂ) (a : I) : ℂ := ∑ x, (μ.weight x : ℂ) * (W a x : ℂ) * f x

omit [Fintype I] in
theorem complexFeatureAdj_re (μ : FiniteLaw X) (W : I → X → ℝ) (f : X → ℂ) (a : I) :
    (complexFeatureAdj μ W f a).re = μ.expect (fun x => W a x * (f x).re) := by
  simp only [complexFeatureAdj, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.mul_im, add_zero,
    FiniteLaw.expect, mul_assoc]

omit [Fintype I] in
theorem complexFeatureAdj_im (μ : FiniteLaw X) (W : I → X → ℝ) (f : X → ℂ) (a : I) :
    (complexFeatureAdj μ W f a).im = μ.expect (fun x => W a x * (f x).im) := by
  simp only [complexFeatureAdj, Complex.im_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.mul_im, add_zero,
    FiniteLaw.expect, mul_assoc]

theorem finiteFrame_complex_analysis (μ : FiniteLaw X) (W : I → X → ℝ) {κ : ℝ}
    (hF : ∀ f : X → ℝ, (∑ a, (μ.expect (fun x => W a x * f x)) ^ 2) ≤
      κ * μ.expect (fun x => f x ^ 2)) (f : X → ℂ) :
    (∑ a, ‖complexFeatureAdj μ W f a‖ ^ 2) ≤ κ * ∑ x, μ.weight x * ‖f x‖ ^ 2 := by
  have hr := hF (fun x => (f x).re)
  have hi := hF (fun x => (f x).im)
  simp only [Complex.sq_norm, Complex.normSq_apply, ← pow_two, complexFeatureAdj_re,
    complexFeatureAdj_im, sum_add_distrib, mul_add]
  simpa only [FiniteLaw.expect, mul_add] using add_le_add hr hi

end Sarkozy.SpectralC
