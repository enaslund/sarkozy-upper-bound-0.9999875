module

public import Sarkozy.FourierSymmetry

/-!
# Orthogonality and the exact second moment of the Fourier lift

Distinct characters are orthogonal under the uniform law. Expanding the
finite sum therefore gives Parseval's identity for every truncation, without
requiring the full character group or an identification of its dual.
-/

@[expose] public section

open scoped BigOperators ComplexConjugate

namespace Sarkozy

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem sum_character_pair (χ ψ : AddChar G ℂ) :
    (∑ x, χ x * star (ψ x)) = if χ = ψ then (Fintype.card G : ℂ) else 0 := by
  classical
  simp only [← finite_addChar_inv, ← AddChar.mul_apply]
  by_cases h : χ = ψ
  · simp [h]
  · rw [AddChar.sum_eq_zero_of_ne_one (fun hmul => h (eq_of_mul_inv_eq_one hmul)), ite_eq_right h]

theorem sum_character_expansion_sq (T : Finset (AddChar G ℂ)) (a : AddChar G ℂ → ℂ) :
    (∑ x, (∑ χ ∈ T, a χ * χ x) * star (∑ χ ∈ T, a χ * χ x)) =
      (Fintype.card G : ℂ) * ∑ χ ∈ T, a χ * star (a χ) := by
  classical
  simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Finset.sum_comm]
  have he (ψ : AddChar G ℂ) (x : G) :
      a ψ * ψ x * (star (χ x) * star (a χ)) =
        (a ψ * star (a χ)) * (ψ x * star (χ x)) := by ring
  simp_rw [he, ← Finset.mul_sum, sum_character_pair]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq', ite_eq_left hχ]
  ring

theorem sum_normSq_character_expansion (T : Finset (AddChar G ℂ)) (a : AddChar G ℂ → ℂ) :
    (∑ x, Complex.normSq (∑ χ ∈ T, a χ * χ x)) =
      (Fintype.card G : ℝ) * ∑ χ ∈ T, Complex.normSq (a χ) := by
  have h := sum_character_expansion_sq T a
  simp only [show ∀ z : ℂ, z * star z = (Complex.normSq z : ℂ) from Complex.mul_conj] at h
  have hr := congrArg Complex.re h
  simpa only [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.ofReal_re,
    Complex.natCast_im, zero_mul, sub_zero] using hr

theorem mean_normSq_complexLift (ρ : ℤ →+ G) (N : ℕ) (A : Finset ℤ)
    (T : Finset (AddChar G ℂ)) :
    (FiniteLaw.uniform G).expect (fun x => Complex.normSq (complexLift ρ N A T x)) =
      ∑ χ ∈ T, Complex.normSq (fourierCoefficient ρ N A χ) := by
  rw [FiniteLaw.expect_uniform]
  change (∑ x, Complex.normSq (∑ χ ∈ T, fourierCoefficient ρ N A χ * χ x)) /
    (Fintype.card G : ℝ) = _
  rw [sum_normSq_character_expansion]
  have hc : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact mul_div_cancel_left₀ _ hc

/-- Parseval for the real Fourier lift when its frequency set is symmetric. -/
theorem mean_sq_fourierLift (ρ : ℤ →+ G) (N : ℕ) (A : Finset ℤ)
    (T : Finset (AddChar G ℂ)) (hT : ∀ χ ∈ T, χ⁻¹ ∈ T) :
    (FiniteLaw.uniform G).expect (fun x => fourierLift ρ N A T x ^ 2) =
      ∑ χ ∈ T, ‖fourierCoefficient ρ N A χ‖ ^ 2 := by
  have h := mean_normSq_complexLift ρ N A T
  have he (x : G) : Complex.normSq (complexLift ρ N A T x) = fourierLift ρ N A T x ^ 2 := by
    rw [← ofReal_fourierLift ρ N A T hT x, Complex.normSq_ofReal]
    ring
  simpa only [he, Complex.normSq_eq_norm_sq] using h

end Sarkozy
