module

public import Sarkozy.SpectralD.FiniteRowTest

/-!
# Clearing denominators in the finite spectral test

A positive integer matrix certifies the finite test after multiplication
by 2000 times the positive parameter s. The Gram term is kept in the
certificate, so cancellation with the coverable correction is preserved.
-/

@[expose] public section

namespace Sarkozy.SpectralD

open Finset Sarkozy.SpectralC
open scoped ComplexConjugate Matrix

variable {U : Type*} [Fintype U] [DecidableEq U]

def integerTestMatrix (D H : U → U → ℤ) (b t ε : ℤ) (i j : U) : ℤ :=
  (if i = j then b else 0) + ε * t * D i j +
    2000 * ε ^ 2 * (∑ k, D k i * D k j) - 2000 * H i j

def integerMatrix (D : U → U → ℤ) : Matrix U U ℂ := fun i j => D i j

def integerMode (D : U → U → ℤ) (ε : ℤ) : Matrix U U ℂ := fun i j => (ε : ℂ) * D i j

omit [DecidableEq U] in
theorem integer_gram (D : U → U → ℤ) (ε : ℤ) :
    (integerMatrix (fun i j => ε ^ 2 * ∑ k, D k i * D k j)) =
      (integerMode D ε)ᴴ * (integerMode D ε) := by
  ext i j
  simp only [integerMatrix, integerMode, Matrix.mul_apply, Matrix.conjTranspose_apply,
    star_mul, star_intCast, Int.cast_mul, Int.cast_pow, Int.cast_sum, mul_sum]
  apply sum_congr rfl
  intro k _
  ring

theorem integerTestMatrix_cast (D H : U → U → ℤ) (b t ε : ℤ) {s a : ℝ}
    (ht : (t : ℝ) = 2000 * s) (hb : (b : ℝ) = 2000 * a) :
    integerMatrix (integerTestMatrix D H b t ε) =
      (2000 : ℂ) • ((s : ℂ) • (integerMode D ε) -
        ((integerMatrix H) -
          (integerMode D ε)ᴴ * (integerMode D ε)) +
        (a : ℂ) • (1 : Matrix U U ℂ)) := by
  rw [← integer_gram]
  have htC : (t : ℂ) = 2000 * (s : ℂ) := by exact_mod_cast ht
  have hbC : (b : ℂ) = 2000 * (a : ℂ) := by exact_mod_cast hb
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [integerMatrix, integerTestMatrix, integerMode, Int.cast_sub, Int.cast_add,
    Int.cast_mul, Int.cast_ofNat,
    Matrix.one_apply, htC, apply_ite (fun z : ℤ => (z : ℂ)), Int.cast_zero]
  by_cases h : i = j <;> simp only [h, ite_true, ite_false, hbC] <;> ring

theorem finiteTest_of_integer (D H : U → U → ℤ) (b t ε : ℤ)
    {s c ηQ ηB : ℝ} (hs : 0 < s) (ht : (t : ℝ) = 2000 * s)
    (hb : (b : ℝ) = 2000 * (s * (c + s - ηQ) - ηB))
    (hpos : ∀ x, 0 ≤ (qform (fun i j => (integerTestMatrix D H b t ε i j : ℂ)) x).re) :
    Spectral.FiniteTest (fun x => (qform (integerMode D ε) x).re)
      (fun x => Spectral.qform (integerMatrix H) x x -
        Spectral.sqn ((integerMode D ε) *ᵥ x)) c s ηQ ηB := by
  intro x
  have h := hpos x
  change 0 ≤ (qform (fun i j => integerMatrix (integerTestMatrix D H b t ε) i j) x).re at h
  rw [integerTestMatrix_cast D H b t ε ht hb] at h
  rw [← spectral_qform_eq] at h
  have hform : ∀ (A B : Matrix U U ℂ) (a : ℝ),
      Spectral.qform ((2000 : ℂ) • ((s : ℂ) • A - B +
        (a : ℂ) • (1 : Matrix U U ℂ))) x x =
        2000 * (s * Spectral.qform A x x - Spectral.qform B x x +
          a * Spectral.sqn x) := by
    intro A B a
    rw [show (2000 : ℂ) = ((2000 : ℝ) : ℂ) by norm_num]
    simp only [Spectral.qform, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.one_mulVec, dotProduct_smul, dotProduct_add, dotProduct_sub, smul_eq_mul,
      RCLike.re_to_complex, Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hx : (star x ⬝ᵥ x).re = Spectral.sqn x := Spectral.re_star_dotProduct_self x
    rw [hx]
  rw [hform, Spectral.qform_sub_conjTranspose_mul] at h
  have hq := spectral_qform_eq (fun i j => integerMode D ε i j) x
  change Spectral.qform (integerMode D ε) x x = _ at hq
  rw [hq] at h
  change 0 ≤ (qform _ x).re - _ / s + (c + s - ηQ - ηB / s) * Spectral.sqn x
  apply (mul_nonneg_iff_of_pos_left hs).mp
  field_simp
  nlinarith

end Sarkozy.SpectralD
