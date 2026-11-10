module

public import Sarkozy.FourierArithmetic.PrefixBridge

/-!
# Moments of indicator lifts with a finite prefix

The moment estimate is expressed entirely in terms of the character lift
used by the energy, including character-dependent whole-support families.
-/

@[expose] public section

open Finset Complex
open scoped BigOperators

namespace Sarkozy.FourierArithmetic

theorem uniform_prefixed_indicator_moment (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {J X₀ : Type} [Fintype J] [DecidableEq J]
      [AddCommGroup X₀] [Fintype X₀] (p : J → ℕ) [∀ j, NeZero (p j)]
      (ρ : ℤ →+ X₀), (Pairwise fun i j => (p i).Coprime (p j)) → Function.Injective p →
      ∀ (H : Finset (AddChar X₀ ℂ)) (F : AddChar X₀ ℂ → Finset (Finset J)) (Q : ℕ),
      0 < Q → (∀ χ ∈ H, ∀ U ∈ F χ, ∏ j ∈ U, p j ≤ Q) →
      ∀ N : ℕ, 0 < N → 2 * (Q : ℝ) ≤ (N + 1 : ℕ) → (Q : ℝ) ^ 5 ≤ (N + 1 : ℕ) →
      ∀ A : Finset ℤ, A ⊆ Icc 0 (N : ℤ) →
      (FiniteLaw.uniform (X₀ × ResidueSpace p)).moment (2 * r : ℕ)
        (fourierLift (ρ.prod (integerResidue p)) N A (prefixCharacters p H F)) ≤
          (H.card : ℝ) ^ (2 * r) * C * (Q : ℝ) ^ ε * density N A := by
  obtain ⟨C, hC, hc⟩ := uniform_prefix_moment r hr ε hε
  refine ⟨2 ^ (2 * r) * C, by positivity, ?_⟩
  intro J X₀ _ _ _ _ p _ ρ hp hinj H F Q hQ hden N hN hsmall hsmall' A hA
  let G := prefixSupportLift p ρ (N + 1) (fun n => (integerIndicator A n : ℂ)) H F
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
  have hsingle (z₀ : X₀) :
      (FiniteLaw.uniform (ResidueSpace p)).expect (fun x => ‖G (z₀, x)‖ ^ (2 * r)) ≤
        (H.card : ℝ) ^ (2 * r) * (C * (Q : ℝ) ^ ε * density N A) := by
    have h := hc p ρ hp hinj H F Q hQ hden (N + 1) (by omega) hsmall hsmall'
      (fun n => (integerIndicator A n : ℂ)) 1 (by norm_num)
      (fun n _ => by simpa only [Complex.norm_real, Real.norm_eq_abs] using integerIndicator_bound A n) z₀
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, one_pow, mul_one,
      integerIndicator_square_mass N A hA] at h
    rw [uniform_expect_eq_expect]
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left hmass (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hfull : (FiniteLaw.uniform (X₀ × ResidueSpace p)).expect (fun z => ‖G z‖ ^ (2 * r)) ≤
      (H.card : ℝ) ^ (2 * r) * (C * (Q : ℝ) ^ ε * density N A) := by
    rw [← FiniteLaw.uniform_product, FiniteLaw.expect_product]
    exact (FiniteLaw.uniform X₀).expect_le_const hsingle
  have hpoint (z : X₀ × ResidueSpace p) :
      |fourierLift (ρ.prod (integerResidue p)) N A (prefixCharacters p H F) z| ^ (2 * r) ≤
        B ^ (2 * r) * ‖G z‖ ^ (2 * r) := by
    apply (pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) (2 * r)).trans_eq
    rw [complexLift_eq_prefix_indicator p ρ N hN A hA H F z, norm_mul, norm_div,
      Complex.norm_natCast, Complex.norm_natCast, mul_pow]
  rw [FiniteLaw.moment_nat]
  apply ((FiniteLaw.uniform (X₀ × ResidueSpace p)).expect_mono hpoint).trans
  rw [FiniteLaw.expect_const_mul]
  have hstep := mul_le_mul (pow_le_pow_left₀ hB0 hB (2 * r)) hfull
    ((FiniteLaw.uniform (X₀ × ResidueSpace p)).expect_nonneg (fun z => pow_nonneg (norm_nonneg _) _))
    (by positivity : (0 : ℝ) ≤ 2 ^ (2 * r))
  apply hstep.trans_eq
  ring

end Sarkozy.FourierArithmetic
