module

public import Sarkozy.SpectralD.CouplingInputs

/-!
# Positive quadratic forms from scaled row certificates

For a real symmetric matrix A, certify a row norm bound for
C I - diag(w) A diag(w), with every weight nonzero. The Schur test then
proves that A is positive semidefinite. This permits exact rational
certificates with small integer scaling weights.
-/

@[expose] public section

namespace Sarkozy.SpectralD

open Finset Complex Sarkozy.SpectralC
open scoped ComplexConjugate

variable {U : Type*} [Fintype U] [DecidableEq U]

noncomputable def shiftedScale (A : U → U → ℝ) (w : U → ℝ) (C : ℝ) (i j : U) : ℝ :=
  (if i = j then C else 0) - w i * A i j * w j

omit [Fintype U] in
theorem shiftedScale_symm (A : U → U → ℝ) (hA : ∀ i j, A i j = A j i)
    (w : U → ℝ) (C : ℝ) (i j : U) : shiftedScale A w C i j = shiftedScale A w C j i := by
  unfold shiftedScale
  rw [hA i j]
  by_cases h : i = j
  · subst j; rfl
  · simp only [h, Ne.symm h, ite_false]
    ring

theorem shiftedScale_qform (A : U → U → ℝ) (w : U → ℝ) (C : ℝ) (z : U → ℂ) :
    (qform (fun i j => (shiftedScale A w C i j : ℂ)) z).re =
      C * ∑ i, ‖z i‖ ^ 2 -
        (qform (fun i j => (A i j : ℂ)) (fun i => (w i : ℂ) * z i)).re := by
  have hdiag : (∑ i, ∑ j, conj (z i) * (if i = j then (C : ℂ) else 0) * z j) =
      ((C * ∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [mul_ite, mul_zero, ite_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]
    rw [mul_sum, Complex.ofReal_sum]
    apply sum_congr rfl
    intro i _
    rw [Complex.ofReal_mul, mul_comm (conj (z i)), mul_assoc]
    congr 1
    simp only [RCLike.conj_mul, Complex.ofReal_pow]
    rfl
  have hscale : ∑ i, ∑ j, conj (z i) * ((w i : ℂ) * A i j * w j) * z j =
      qform (fun i j => (A i j : ℂ)) (fun i => (w i : ℂ) * z i) := by
    unfold qform
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [map_mul, Complex.conj_ofReal]
    ring
  unfold qform shiftedScale
  simp only [Complex.ofReal_sub, Complex.ofReal_mul]
  simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_zero]
  simp_rw [mul_sub, sub_mul, sum_sub_distrib]
  rw [hdiag, hscale, Complex.sub_re, Complex.ofReal_re]
  rfl

theorem qform_nonneg_of_scaled_rows (A : U → U → ℝ) (hA : ∀ i j, A i j = A j i)
    (w : U → ℝ) (hw : ∀ i, w i ≠ 0) (C : ℝ)
    (hrow : ∀ i, ∑ j, |shiftedScale A w C i j| ≤ C) (x : U → ℂ) :
    0 ≤ (qform (fun i j => (A i j : ℂ)) x).re := by
  let z : U → ℂ := fun i => x i / (w i : ℂ)
  have h := PaleyB.qform_re_le_of_rowsum
    (fun i j => (shiftedScale A w C i j : ℂ)) (fun i j => |shiftedScale A w C i j|)
    (fun _ _ => abs_nonneg _) (fun i j => congrArg abs (shiftedScale_symm A hA w C i j))
    (fun i j => by rw [Complex.norm_real, Real.norm_eq_abs]) hrow z
  rw [shiftedScale_qform] at h
  have hz : (fun i => (w i : ℂ) * z i) = x := by
    funext i
    have hwi : (w i : ℂ) ≠ 0 := by exact_mod_cast hw i
    dsimp [z]
    exact mul_div_cancel₀ (x i) hwi
  rw [hz] at h
  linarith

theorem qform_nonneg_of_integer_rows (A : U → U → ℤ) (hA : ∀ i j, A i j = A j i)
    (w : U → ℤ) (hw : ∀ i, w i ≠ 0) (C : ℤ)
    (hrow : ∀ i, ∑ j, |(if i = j then C else 0) - w i * A i j * w j| ≤ C)
    (x : U → ℂ) : 0 ≤ (qform (fun i j => (A i j : ℂ)) x).re := by
  have h := qform_nonneg_of_scaled_rows (fun i j => (A i j : ℝ))
    (fun i j => congrArg (fun z : ℤ => (z : ℝ)) (hA i j)) (fun i => (w i : ℝ))
    (fun i => by exact_mod_cast hw i) (C : ℝ) (fun i => ?_) x
  · simpa only [Complex.ofReal_intCast] using h
  · unfold shiftedScale
    dsimp only
    exact_mod_cast hrow i

omit [DecidableEq U] in
theorem qform_le_of_integer_rows (A : U → U → ℤ) (hA : ∀ i j, A i j = A j i)
    (L : ℤ) (hrow : ∀ i, ∑ j, |A i j| ≤ L) (x : U → ℂ) :
    (qform (fun i j => (A i j : ℂ)) x).re ≤ (L : ℝ) * ∑ i, ‖x i‖ ^ 2 := by
  apply PaleyB.qform_re_le_of_rowsum (fun i j => (A i j : ℂ))
    (fun i j => |(A i j : ℝ)|)
  · intro i j; exact abs_nonneg _
  · intro i j; rw [hA i j]
  · intro i j
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  · intro i
    exact_mod_cast hrow i

end Sarkozy.SpectralD
