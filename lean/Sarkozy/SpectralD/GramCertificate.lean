module

public import Sarkozy.SpectralD.MatrixCertificate

/-!
# Positive quadratic forms from explicit Gram factors

Finite certificates may supply approximate factors and leave a residual
matrix. Positivity of the residual together with the exact factor identity
proves positivity of the original matrix.
-/

@[expose] public section

namespace Sarkozy.SpectralD

open Finset Complex Sarkozy.SpectralC
open scoped ComplexConjugate

variable {U K : Type*} [Fintype U] [Fintype K]

def factorGram (B : K → U → ℂ) (i j : U) : ℂ := ∑ k, conj (B k i) * B k j

theorem factorGram_qform (B : K → U → ℂ) (x : U → ℂ) :
    qform (factorGram B) x = ((∑ k, ‖∑ i, B k i * x i‖ ^ 2 : ℝ) : ℂ) := by
  have hx (k : K) : ((‖∑ i, B k i * x i‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ∑ j, conj (x i) * (conj (B k i) * B k j) * x j := by
    have he : conj (∑ i, B k i * x i) * (∑ i, B k i * x i) =
        ((‖∑ i, B k i * x i‖ ^ 2 : ℝ) : ℂ) := by
      simp only [RCLike.conj_mul, Complex.ofReal_pow]
      rfl
    rw [← he]
    simp only [map_sum, map_mul, sum_mul, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  rw [Complex.ofReal_sum]
  simp_rw [hx]
  unfold qform factorGram
  symm
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [mul_sum, sum_mul]

theorem factorGram_nonneg (B : K → U → ℂ) (x : U → ℂ) :
    0 ≤ (qform (factorGram B) x).re := by
  rw [factorGram_qform, Complex.ofReal_re]
  exact sum_nonneg fun _ _ => sq_nonneg _

theorem qform_nonneg_of_factor_residual (A R : U → U → ℂ) (B : K → U → ℂ)
    {s : ℝ} (hs : 0 < s)
    (h : ∀ i j, (s : ℂ) * A i j = R i j + factorGram B i j)
    (hR : ∀ x, 0 ≤ (qform R x).re) (x : U → ℂ) : 0 ≤ (qform A x).re := by
  have he : (s : ℂ) * qform A x = qform R x + qform (factorGram B) x := by
    unfold qform
    simp_rw [mul_sum]
    calc _ = ∑ i, ∑ j, conj (x i) * ((s : ℂ) * A i j) * x j := by
          apply sum_congr rfl
          intro i _
          apply sum_congr rfl
          intro j _
          ring
      _ = _ := by simp_rw [h, mul_add, add_mul, sum_add_distrib]
  have heR := congrArg Complex.re he
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.add_re] at heR
  have h0 := add_nonneg (hR x) (factorGram_nonneg B x)
  rw [← heR] at h0
  exact (mul_nonneg_iff_of_pos_left hs).mp h0

end Sarkozy.SpectralD
