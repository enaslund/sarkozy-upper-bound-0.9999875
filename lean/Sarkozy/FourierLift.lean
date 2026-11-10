module

public import Sarkozy.Definitions
public import Sarkozy.ProbabilityConstructions
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.Analysis.Complex.Basic

/-!
# Finite truncated Fourier lifts

The coefficient at χ is `N⁻¹ ∑ a∈A conj(χ(ρ(a)))`, where ρ maps integers
to the finite label group. Retaining any finite set of characters containing
the trivial character preserves the mean |A|/N. The lift used here is the real
part of the truncated series. Identifying the paper's precise frequency set
and label group remains a separate construction task.
-/

@[expose] public section

open scoped BigOperators ComplexConjugate

namespace Sarkozy

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def fourierCoefficient (ρ : ℤ →+ G) (N : ℕ) (A : Finset ℤ)
    (χ : AddChar G ℂ) : ℂ := (∑ a ∈ A, star (χ (ρ a))) / (N : ℂ)

noncomputable def complexLift (ρ : ℤ →+ G) (N : ℕ) (A : Finset ℤ)
    (T : Finset (AddChar G ℂ)) (x : G) : ℂ :=
  ∑ χ ∈ T, fourierCoefficient ρ N A χ * χ x

noncomputable def fourierLift (ρ : ℤ →+ G) (N : ℕ) (A : Finset ℤ)
    (T : Finset (AddChar G ℂ)) (x : G) : ℝ := (complexLift ρ N A T x).re

omit [Fintype G] in
theorem fourierCoefficient_one (ρ : ℤ →+ G) (N : ℕ) (A : Finset ℤ) :
    fourierCoefficient ρ N A 1 = (density N A : ℂ) := by
  simp [fourierCoefficient, density]

theorem sum_complexLift (ρ : ℤ →+ G) (N : ℕ) (A : Finset ℤ)
    (T : Finset (AddChar G ℂ)) (hT : (1 : AddChar G ℂ) ∈ T) :
    (∑ x, complexLift ρ N A T x) = (Fintype.card G : ℂ) * (density N A : ℂ) := by
  classical
  unfold complexLift
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hsum (χ : AddChar G ℂ) :
      (∑ x, χ x) = if χ = 1 then (Fintype.card G : ℂ) else 0 := by
    by_cases hχ : χ = 1
    · simp [hχ]
    · simp [hχ, AddChar.sum_eq_zero_of_ne_one hχ]
  simp_rw [hsum, mul_ite, mul_zero]
  simp [hT, fourierCoefficient_one, mul_comm]

/-- Character orthogonality proves the mean identity for every truncation
containing the trivial character; there is no estimate hypothesis here. -/
theorem mean_fourierLift (ρ : ℤ →+ G) (N : ℕ) (A : Finset ℤ)
    (T : Finset (AddChar G ℂ)) (hT : (1 : AddChar G ℂ) ∈ T) :
    (FiniteLaw.uniform G).expect (fourierLift ρ N A T) = density N A := by
  have hsum := congrArg Complex.re (sum_complexLift ρ N A T hT)
  have hc : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hr : (∑ x, fourierLift ρ N A T x) = (Fintype.card G : ℝ) * density N A := by
    simpa only [Complex.re_sum, Complex.mul_re, Complex.natCast_re,
      Complex.ofReal_re, Complex.natCast_im, Complex.ofReal_im, zero_mul,
      sub_zero, fourierLift] using hsum
  rw [FiniteLaw.expect_uniform, hr, mul_div_cancel_left₀ _ hc]

omit [Fintype G] in
@[simp] theorem fourierCoefficient_empty (ρ : ℤ →+ G) (N : ℕ) (χ : AddChar G ℂ) :
    fourierCoefficient ρ N ∅ χ = 0 := by simp [fourierCoefficient]

omit [Fintype G] in
@[simp] theorem fourierLift_empty (ρ : ℤ →+ G) (N : ℕ)
    (T : Finset (AddChar G ℂ)) (x : G) : fourierLift ρ N ∅ T x = 0 := by
  simp [fourierLift, complexLift]

theorem finite_addChar_norm (χ : AddChar G ℂ) (x : G) : ‖χ x‖ = 1 := by
  have hp : χ x ^ Fintype.card G = 1 := by
    rw [← χ.map_nsmul_eq_pow, card_nsmul_eq_zero, χ.map_zero_eq_one]
  have hn := congrArg norm hp
  apply (pow_left_inj₀ (norm_nonneg _) zero_le_one
    (show Fintype.card G ≠ 0 from Fintype.card_ne_zero)).mp
  simpa only [norm_pow, norm_one, one_pow] using hn

theorem norm_fourierCoefficient_le (ρ : ℤ →+ G) (N : ℕ) (A : Finset ℤ)
    (χ : AddChar G ℂ) : ‖fourierCoefficient ρ N A χ‖ ≤ density N A := by
  have hsum : ‖∑ a ∈ A, star (χ (ρ a))‖ ≤ (A.card : ℝ) := by
    calc
      _ ≤ ∑ a ∈ A, ‖star (χ (ρ a))‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_star, finite_addChar_norm, Finset.sum_const,
        nsmul_eq_mul, mul_one]
  simpa only [fourierCoefficient, norm_div, Complex.norm_natCast, density] using
    div_le_div_of_nonneg_right hsum (Nat.cast_nonneg N)

theorem norm_complexLift_le (ρ : ℤ →+ G) (N : ℕ) (A : Finset ℤ)
    (T : Finset (AddChar G ℂ)) (x : G) :
    ‖complexLift ρ N A T x‖ ≤ (T.card : ℝ) * density N A := by
  calc
    _ ≤ ∑ χ ∈ T, ‖fourierCoefficient ρ N A χ * χ x‖ := norm_sum_le _ _
    _ ≤ ∑ _χ ∈ T, density N A := by
      apply Finset.sum_le_sum
      intro χ _
      simpa only [norm_mul, finite_addChar_norm, mul_one] using
        norm_fourierCoefficient_le ρ N A χ
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

/-- The elementary pointwise estimate used for finite initialization in the paper. -/
theorem abs_fourierLift_le (ρ : ℤ →+ G) (N : ℕ) (A : Finset ℤ)
    (T : Finset (AddChar G ℂ)) (x : G) :
    |fourierLift ρ N A T x| ≤ (T.card : ℝ) * density N A :=
  (Complex.abs_re_le_norm _).trans (norm_complexLift_le ρ N A T x)

end Sarkozy
