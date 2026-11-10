module

public import Sarkozy.SpectralD.StarMatrix

/-! Orthogonal averaging over simultaneous translations of all labels. -/

@[expose] public section

namespace Sarkozy.SpectralD.StarMatrix

open Finset Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

noncomputable def translationAverage (f : (U → ZMod p) → ℂ) (x : U → ZMod p) : ℂ :=
  (p : ℂ)⁻¹ * ∑ c : ZMod p, f (affLab 1 c x)

noncomputable def translationResidual (f : (U → ZMod p) → ℂ) (x : U → ZMod p) : ℂ :=
  f x - translationAverage f x

omit [Fintype U] [DecidableEq U] in
theorem affLab_one_comp (c d : ZMod p) (x : U → ZMod p) :
    affLab 1 c (affLab 1 d x) = affLab 1 (c + d) x := by
  funext j
  simp only [affLab, one_mul]
  ring

omit [Fintype U] [DecidableEq U] in
theorem translationAverage_invariant (f : (U → ZMod p) → ℂ) (d : ZMod p)
    (x : U → ZMod p) : translationAverage f (affLab 1 d x) = translationAverage f x := by
  unfold translationAverage
  simp_rw [affLab_one_comp]
  congr 1
  exact (Equiv.addRight d).bijective.sum_comp (fun c => f (affLab 1 c x))

omit [Fintype U] [DecidableEq U] in
theorem translationAverage_fixed (f : (U → ZMod p) → ℂ)
    (hf : ∀ c x, f (affLab 1 c x) = f x) : translationAverage f = f := by
  funext x
  simp only [translationAverage, hf, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  field_simp [p_ne_zero_C (p := p)]

noncomputable def weightedPair (μ : (U → ZMod p) → ℝ) (g f : (U → ZMod p) → ℂ) : ℂ :=
  ∑ x, (μ x : ℂ) * conj (g x) * f x

theorem weightedPair_average (μ : (U → ZMod p) → ℝ)
    (hμ : ∀ c x, μ (affLab 1 c x) = μ x) (v f : (U → ZMod p) → ℂ)
    (hv : ∀ c x, v (affLab 1 c x) = v x) :
    weightedPair μ v (translationAverage f) = weightedPair μ v f := by
  have hs (c : ZMod p) :
      (∑ x, (μ x : ℂ) * conj (v x) * f (affLab 1 c x)) = weightedPair μ v f := by
    conv_rhs =>
      unfold weightedPair
      rw [← (affLab_bijective (U := U) (one_ne_zero (α := ZMod p)) c).sum_comp]
    apply sum_congr rfl
    intro x _
    rw [hμ, hv]
  calc
    _ = (p : ℂ)⁻¹ * ∑ c : ZMod p, ∑ x, (μ x : ℂ) * conj (v x) * f (affLab 1 c x) := by
      unfold weightedPair translationAverage
      simp only [mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun c _ => sum_congr rfl fun x _ => by ring
    _ = _ := by
      simp only [hs, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
      field_simp [p_ne_zero_C (p := p)]

theorem weightedPair_residual (μ : (U → ZMod p) → ℝ)
    (hμ : ∀ c x, μ (affLab 1 c x) = μ x) (v f : (U → ZMod p) → ℂ)
    (hv : ∀ c x, v (affLab 1 c x) = v x) :
    weightedPair μ v (translationResidual f) = 0 := by
  unfold translationResidual weightedPair
  rw [show (∑ x, (μ x : ℂ) * conj (v x) * (f x - translationAverage f x)) =
      weightedPair μ v f - weightedPair μ v (translationAverage f) by
    simp only [weightedPair, mul_sub, sum_sub_distrib]]
  rw [weightedPair_average μ hμ v f hv, sub_self]

theorem translation_energy_split (μ : (U → ZMod p) → ℝ)
    (hμ : ∀ c x, μ (affLab 1 c x) = μ x) (f : (U → ZMod p) → ℂ) :
    (∑ x, μ x * ‖translationResidual f x‖ ^ 2) +
      (∑ x, μ x * ‖translationAverage f x‖ ^ 2) = ∑ x, μ x * ‖f x‖ ^ 2 := by
  have ho := congrArg Complex.re
    (weightedPair_residual μ hμ (translationAverage f) f (translationAverage_invariant f))
  simp only [weightedPair, Complex.re_sum, Complex.zero_re, mul_assoc,
    Complex.re_ofReal_mul] at ho
  have he (x : U → ZMod p) :
      μ x * ‖translationResidual f x‖ ^ 2 + μ x * ‖translationAverage f x‖ ^ 2 =
        μ x * ‖f x‖ ^ 2 - 2 *
          (μ x * (conj (translationAverage f x) * translationResidual f x).re) := by
    simp only [translationResidual, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re,
      Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im]
    ring
  rw [← sum_add_distrib, sum_congr rfl (fun x _ => he x), sum_sub_distrib, ← mul_sum, ho,
    mul_zero, sub_zero]

end Sarkozy.SpectralD.StarMatrix
