module

public import Sarkozy.FourierLift

/-!
# Reality of symmetric Fourier truncations

For a set of characters closed under inversion, the truncated Fourier sum is
already real. Thus taking its real part in `fourierLift` agrees exactly with
the paper's real Fourier lift; it is not a relaxation of the Fourier sum.
-/

@[expose] public section

open scoped BigOperators ComplexConjugate

namespace Sarkozy

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem finite_addChar_inv (χ : AddChar G ℂ) (x : G) : χ⁻¹ x = star (χ x) := by
  rw [AddChar.inv_apply', Complex.inv_eq_conj (finite_addChar_norm χ x)]
  rfl

theorem fourierCoefficient_inv (ρ : ℤ →+ G) (N : ℕ) (A : Finset ℤ)
    (χ : AddChar G ℂ) : fourierCoefficient ρ N A χ⁻¹ = star (fourierCoefficient ρ N A χ) := by
  simp only [fourierCoefficient, finite_addChar_inv, star_star, star_div₀,
    star_sum, star_natCast]

theorem complexLift_self_conjugate (ρ : ℤ →+ G) (N : ℕ) (A : Finset ℤ)
    (T : Finset (AddChar G ℂ)) (hT : ∀ χ ∈ T, χ⁻¹ ∈ T) (x : G) :
    star (complexLift ρ N A T x) = complexLift ρ N A T x := by
  classical
  calc
    _ = ∑ χ ∈ T, fourierCoefficient ρ N A χ⁻¹ * χ⁻¹ x := by
      simp only [complexLift, star_sum, star_mul, ← fourierCoefficient_inv,
        ← finite_addChar_inv, mul_comm]
    _ = ∑ χ ∈ T, fourierCoefficient ρ N A χ * χ x := by
      apply Finset.sum_bij (fun χ _ => χ⁻¹)
      · exact hT
      · intro χ _ ψ _ h
        exact inv_injective h
      · intro χ hχ
        exact ⟨χ⁻¹, hT χ hχ, inv_inv χ⟩
      · intro χ _
        rfl
    _ = _ := rfl

/-- With a symmetric frequency set, the complex sum equals the real lift. -/
theorem ofReal_fourierLift (ρ : ℤ →+ G) (N : ℕ) (A : Finset ℤ)
    (T : Finset (AddChar G ℂ)) (hT : ∀ χ ∈ T, χ⁻¹ ∈ T) (x : G) :
    (fourierLift ρ N A T x : ℂ) = complexLift ρ N A T x :=
  Complex.conj_eq_iff_re.mp (complexLift_self_conjugate ρ N A T hT x)

theorem complexLift_im_zero (ρ : ℤ →+ G) (N : ℕ) (A : Finset ℤ)
    (T : Finset (AddChar G ℂ)) (hT : ∀ χ ∈ T, χ⁻¹ ∈ T) (x : G) :
    (complexLift ρ N A T x).im = 0 :=
  Complex.conj_eq_iff_im.mp (complexLift_self_conjugate ρ N A T hT x)

end Sarkozy
