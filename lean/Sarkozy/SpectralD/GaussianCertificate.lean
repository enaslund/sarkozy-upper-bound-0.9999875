module

public import Sarkozy.SpectralD.GramCertificate

/-!
# Integer certificates for complex Hermitian matrices

The real and imaginary parts are integers. A Gram factor and a residual
row bound give an exact certificate; the method used to find the factor
is not part of the trusted proof.
-/

@[expose] public section

namespace Sarkozy.SpectralD

open Finset Complex Sarkozy.SpectralC
open scoped ComplexConjugate

def gaussian (a b : ℤ) : ℂ := ⟨(a : ℝ), (b : ℝ)⟩

variable {U K : Type*} [Fintype U] [DecidableEq U] [Fintype K]

theorem qform_shift (A : U → U → ℂ) (C : ℝ) (x : U → ℂ) :
    (qform (fun i j => (if i = j then (C : ℂ) else 0) - A i j) x).re =
      C * ∑ i, ‖x i‖ ^ 2 - (qform A x).re := by
  have hd : (∑ i, ∑ j, conj (x i) * (if i = j then (C : ℂ) else 0) * x j) =
      ((C * ∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [mul_ite, mul_zero, ite_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]
    rw [mul_sum, Complex.ofReal_sum]
    apply sum_congr rfl
    intro i _
    rw [Complex.ofReal_mul, mul_comm (conj (x i)), mul_assoc]
    congr 1
    simp only [RCLike.conj_mul, Complex.ofReal_pow]
    rfl
  unfold qform
  simp_rw [mul_sub, sub_mul, sum_sub_distrib]
  rw [hd, Complex.sub_re, Complex.ofReal_re]

theorem qform_nonneg_of_gaussian_rows (R I : U → U → ℤ)
    (hR : ∀ i j, R i j = R j i) (hI : ∀ i j, I i j = -I j i) (C : ℤ)
    (hrow : ∀ i, ∑ j, (|(if i = j then C else 0) - R i j| + |I i j|) ≤ C)
    (x : U → ℂ) : 0 ≤ (qform (fun i j => gaussian (R i j) (I i j)) x).re := by
  let A : U → U → ℂ := fun i j => gaussian (R i j) (I i j)
  let B : U → U → ℝ := fun i j =>
    |(if i = j then (C : ℝ) else 0) - R i j| + |(I i j : ℝ)|
  have hb : ∀ i j, B i j = B j i := by
    intro i j
    dsimp [B]
    rw [hR i j, hI i j, Int.cast_neg, abs_neg]
    by_cases h : i = j
    · subst j; rfl
    · simp only [h, Ne.symm h, ite_false]
  have h := PaleyB.qform_re_le_of_rowsum
    (fun i j => (if i = j then ((C : ℝ) : ℂ) else 0) - A i j) B
    (fun _ _ => by dsimp [B]; positivity) hb (fun i j => ?_) (lam := (C : ℝ)) (fun i => ?_) x
  · rw [qform_shift] at h
    linarith
  · have hh := norm_le_abs_re_add_abs_im
      ((if i = j then ((C : ℝ) : ℂ) else 0) - A i j)
    simpa only [A, B, gaussian, Complex.sub_re, Complex.sub_im, apply_ite Complex.re,
      apply_ite Complex.im, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re,
      Complex.zero_im, ite_self, zero_sub, abs_neg] using hh
  · dsimp [B]
    exact_mod_cast hrow i

def gramReal (R I : K → U → ℤ) (i j : U) : ℤ :=
  ∑ k, (R k i * R k j + I k i * I k j)

def gramImag (R I : K → U → ℤ) (i j : U) : ℤ :=
  ∑ k, (R k i * I k j - I k i * R k j)

omit [Fintype U] [DecidableEq U] in
theorem gaussian_gram (R I : K → U → ℤ) (i j : U) :
    gaussian (gramReal R I i j) (gramImag R I i j) =
      factorGram (fun k i => gaussian (R k i) (I k i)) i j := by
  apply Complex.ext
  · simp only [gaussian, gramReal, factorGram, Complex.re_sum, Complex.mul_re,
      Complex.conj_re, Complex.conj_im, Int.cast_sum, Int.cast_add, Int.cast_mul]
    apply sum_congr rfl
    intro k _
    ring
  · simp only [gaussian, gramImag, factorGram, Complex.im_sum, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Int.cast_sum, Int.cast_sub, Int.cast_mul]
    apply sum_congr rfl
    intro k _
    ring

theorem qform_nonneg_of_gaussian_factor (R I : U → U → ℤ) (BR BI : K → U → ℤ)
    (s C : ℤ) (hs : 0 < s)
    (hR : ∀ i j, s * R i j - gramReal BR BI i j = s * R j i - gramReal BR BI j i)
    (hI : ∀ i j, s * I i j - gramImag BR BI i j = -(s * I j i - gramImag BR BI j i))
    (hrow : ∀ i, ∑ j,
      (|(if i = j then C else 0) - (s * R i j - gramReal BR BI i j)| +
        |s * I i j - gramImag BR BI i j|) ≤ C) (x : U → ℂ) :
    0 ≤ (qform (fun i j => gaussian (R i j) (I i j)) x).re := by
  apply qform_nonneg_of_factor_residual _
    (fun i j => gaussian (s * R i j - gramReal BR BI i j)
      (s * I i j - gramImag BR BI i j))
    (fun k i => gaussian (BR k i) (BI k i)) (s := (s : ℝ))
    (by exact_mod_cast hs) _ (qform_nonneg_of_gaussian_rows _ _ hR hI C hrow) x
  intro i j
  rw [← gaussian_gram]
  apply Complex.ext <;>
    simp only [gaussian, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_re, Complex.add_im, Int.cast_sub, Int.cast_mul] <;> ring

end Sarkozy.SpectralD
