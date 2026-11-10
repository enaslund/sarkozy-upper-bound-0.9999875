module

public import Sarkozy.SpectralD.IntegerFiniteTest
public import Sarkozy.SpectralD.GaussianCertificate

/-!
# Finite spectral tests from complex integer certificates

This version permits either a real or an imaginary Fourier mode and an
arbitrary positive denominator-clearing factor.
-/

@[expose] public section

namespace Sarkozy.SpectralD

open Finset Sarkozy.SpectralC
open scoped Matrix ComplexConjugate

variable {U : Type*} [Fintype U] [DecidableEq U]

theorem finiteTest_of_scaled_matrix (A H M : Matrix U U ℂ)
    {s c ηQ ηB scale : ℝ} (hs : 0 < s) (hscale : 0 < scale)
    (hM : M = (scale : ℂ) • ((s : ℂ) • A - (H - Aᴴ * A) +
      ((s * (c + s - ηQ) - ηB : ℝ) : ℂ) • (1 : Matrix U U ℂ)))
    (hpos : ∀ x, 0 ≤ (qform (fun i j => M i j) x).re) :
    Spectral.FiniteTest (fun x => (qform (fun i j => A i j) x).re)
      (fun x => Spectral.qform H x x - Spectral.sqn (A *ᵥ x)) c s ηQ ηB := by
  intro x
  have h := hpos x
  rw [hM, ← spectral_qform_eq] at h
  have hform : ∀ (B : Matrix U U ℂ) (a : ℝ),
      Spectral.qform ((scale : ℂ) • ((s : ℂ) • A - B +
        (a : ℂ) • (1 : Matrix U U ℂ))) x x =
        scale * (s * Spectral.qform A x x - Spectral.qform B x x +
          a * Spectral.sqn x) := by
    intro B a
    simp only [Spectral.qform, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.one_mulVec, dotProduct_smul, dotProduct_add, dotProduct_sub, smul_eq_mul,
      RCLike.re_to_complex, Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hx : (star x ⬝ᵥ x).re = Spectral.sqn x := Spectral.re_star_dotProduct_self x
    rw [hx]
  rw [hform, Spectral.qform_sub_conjTranspose_mul] at h
  have hh := (mul_nonneg_iff_of_pos_left hscale).mp h
  have hq := spectral_qform_eq (fun i j => A i j) x
  change Spectral.qform A x x = _ at hq
  rw [hq] at hh
  change 0 ≤ (qform _ x).re - _ / s + (c + s - ηQ - ηB / s) * Spectral.sqn x
  apply (mul_nonneg_iff_of_pos_left hs).mp
  field_simp
  nlinarith

def phase (a : Fin 2) : ℂ := if a = 0 then 1 else Complex.I

def phaseMode (D : U → U → ℤ) (ε : ℤ) (a : Fin 2) : Matrix U U ℂ :=
  fun i j => (ε : ℂ) * phase a * D i j

omit [DecidableEq U] in
theorem phaseMode_gram (D : U → U → ℤ) (ε : ℤ) (a : Fin 2) :
    integerMatrix (fun i j => ε ^ 2 * ∑ k, D k i * D k j) =
      (phaseMode D ε a)ᴴ * (phaseMode D ε a) := by
  have ha : conj (phase a) * phase a = 1 := by
    unfold phase
    split_ifs <;> norm_num
  ext i j
  simp only [integerMatrix, phaseMode, Matrix.mul_apply, Matrix.conjTranspose_apply,
    star_mul, star_intCast, Int.cast_mul, Int.cast_pow, Int.cast_sum, mul_sum]
  apply sum_congr rfl
  intro k _
  simp only [show star (phase a) = conj (phase a) from rfl]
  calc _ = ((ε : ℂ) ^ 2 * ((D k i : ℂ) * D k j)) * (conj (phase a) * phase a) := by
        rw [ha]
        ring
    _ = _ := by ring

def complexTest (D H : U → U → ℤ) (scale b t ε : ℤ) (a : Fin 2) : Matrix U U ℂ :=
  fun i j => (if i = j then (b : ℂ) else 0) + (ε : ℂ) * t * phase a * D i j +
    (scale : ℂ) * ε ^ 2 * (∑ k, (D k i : ℂ) * D k j) - (scale : ℂ) * H i j

theorem complexTest_cast (D H : U → U → ℤ) (scale b t ε : ℤ) (a : Fin 2)
    {s c ηQ ηB : ℝ} (ht : (t : ℝ) = scale * s)
    (hb : (b : ℝ) = scale * (s * (c + s - ηQ) - ηB)) :
    complexTest D H scale b t ε a =
      (scale : ℂ) • ((s : ℂ) • phaseMode D ε a -
        (integerMatrix H - (phaseMode D ε a)ᴴ * phaseMode D ε a) +
        ((s * (c + s - ηQ) - ηB : ℝ) : ℂ) • (1 : Matrix U U ℂ)) := by
  rw [← phaseMode_gram]
  have htC : (t : ℂ) = scale * (s : ℂ) := by exact_mod_cast ht
  have hbC : (b : ℂ) = scale * ((s * (c + s - ηQ) - ηB : ℝ) : ℂ) := by
    exact_mod_cast hb
  ext i j
  simp only [complexTest, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, phaseMode, integerMatrix, Int.cast_mul, Int.cast_pow, Int.cast_sum,
    Matrix.one_apply, htC]
  by_cases h : i = j <;> simp only [h, ite_true, ite_false, hbC] <;> ring

end Sarkozy.SpectralD
