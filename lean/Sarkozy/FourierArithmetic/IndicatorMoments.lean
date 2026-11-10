module

public import Sarkozy.FourierArithmetic.Indicator

/-!
# Density-retaining moments of indicator lifts

The arithmetic moment theorem is now applied to the same explicit Fourier
lift used in the energy. The extra endpoint in the integer range costs only
a fixed factor 2^(2r), and the bound retains one power of the density.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.FourierArithmetic

theorem uniform_indicator_moment (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ)
      [∀ j, NeZero (p j)], (Pairwise fun i j => (p i).Coprime (p j)) → Function.Injective p →
      ∀ (F : Finset (Finset J)) (Q : ℕ), 0 < Q → (∀ U ∈ F, ∏ j ∈ U, p j ≤ Q) →
      ∀ N : ℕ, 0 < N → 2 * (Q : ℝ) ≤ (N + 1 : ℕ) → (Q : ℝ) ^ 5 ≤ (N + 1 : ℕ) →
      ∀ A : Finset ℤ, A ⊆ Icc 0 (N : ℤ) →
      (FiniteLaw.uniform (ResidueSpace p)).moment (2 * r : ℕ)
        (fourierLift (integerResidue p) N A (supportCharacters p F)) ≤
          C * (Q : ℝ) ^ ε * density N A := by
  obtain ⟨C, hC, hbound⟩ := uniform_lift_moment_density r hr ε hε
  refine ⟨C * 2 ^ (2 * r), by positivity, ?_⟩
  intro J _ _ p _ hp hinj F Q hQ hden N hN hsmall hsmall' A hA
  let B : ℝ := ((N + 1 : ℕ) : ℝ) / N
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hB0 : 0 ≤ B := by positivity
  have hB : B ≤ 2 := by
    apply (div_le_iff₀ hN').2
    push_cast
    linarith
  have hmass : ((N + 1 : ℕ) : ℝ)⁻¹ * A.card ≤ density N A := by
    rw [mul_comm, ← div_eq_mul_inv, density]
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hN'
    exact_mod_cast Nat.le_succ N
  have hm := hbound p hp hinj F Q hQ hden (N + 1) (by omega) hsmall hsmall'
    (integerIndicator A) 1 (by norm_num) (fun n _ => integerIndicator_bound A n)
  simp only [one_pow, mul_one, integerIndicator_square_mass N A hA] at hm
  have hm' := hm.trans (mul_le_mul_of_nonneg_left hmass
    (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
  calc
    (FiniteLaw.uniform (ResidueSpace p)).moment (2 * r : ℕ)
        (fourierLift (integerResidue p) N A (supportCharacters p F)) =
      B ^ (2 * r) * (𝔼 x, (∑ U ∈ F, liftPiece p (N + 1) (integerIndicator A) U x) ^ (2 * r)) := by
        rw [FiniteLaw.moment_nat, uniform_expect_eq_expect]
        simp only [pow_abs_two_mul, fourierLift_eq_indicator_pieces p N hN A hA F,
          mul_pow, ← mul_expect, B]
    _ ≤ 2 ^ (2 * r) * (C * (Q : ℝ) ^ ε * density N A) :=
      mul_le_mul (pow_le_pow_left₀ hB0 hB _) hm'
        (expect_nonneg (fun x _ => Even.pow_nonneg ⟨r, by omega⟩ _)) (by positivity)
    _ = (C * 2 ^ (2 * r)) * (Q : ℝ) ^ ε * density N A := by ring

end Sarkozy.FourierArithmetic
