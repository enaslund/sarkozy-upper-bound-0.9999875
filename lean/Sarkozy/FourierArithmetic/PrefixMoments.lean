module

public import Sarkozy.FourierArithmetic.ComplexMoments
public import Sarkozy.Moments.Product

/-!
# Finite prefixes in the lift moment estimate

A finite collection of prefix characters costs only its cardinality to the
moment power. The bound is uniform even at a fixed prefix label. Each prefix
character may have a different family of allowed tail supports.
-/

@[expose] public section

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Sarkozy.FourierArithmetic

theorem norm_sum_pow_le {I : Type*} (S : Finset I) (f : I → ℂ) (n : ℕ) (hn : 1 ≤ n) :
    ‖∑ i ∈ S, f i‖ ^ n ≤ (S.card : ℝ) ^ (n - 1) * ∑ i ∈ S, ‖f i‖ ^ n := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg S (f := fun i => ‖f i‖)
    (p := (n : ℝ)) (by exact_mod_cast hn) (fun i _ => norm_nonneg _)
  have he : (n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hn]; norm_num
  rw [he] at h
  simp only [Real.rpow_natCast] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) n).trans h

variable {J X₀ : Type*} [Fintype J] [DecidableEq J]
    [AddCommGroup X₀] [Fintype X₀] (p : J → ℕ) [∀ j, NeZero (p j)]

noncomputable def prefixModulation (ρ : ℤ →+ X₀) (χ : AddChar X₀ ℂ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  f n * star (χ (ρ n))

theorem prefixModulation_norm (ρ : ℤ →+ X₀) (χ : AddChar X₀ ℂ) (f : ℕ → ℂ) (n : ℕ) :
    ‖prefixModulation ρ χ f n‖ = ‖f n‖ := by
  simp only [prefixModulation, norm_mul, norm_star, finite_addChar_norm, mul_one]

noncomputable def prefixSupportLift (ρ : ℤ →+ X₀) (L : ℕ) (f : ℕ → ℂ)
    (H : Finset (AddChar X₀ ℂ)) (F : AddChar X₀ ℂ → Finset (Finset J))
    (z : X₀ × ResidueSpace p) : ℂ :=
  ∑ χ ∈ H, χ z.1 * complexSupportLift p L (prefixModulation ρ χ f) (F χ) z.2

theorem prefix_moment_of_component_bounds (ρ : ℤ →+ X₀) (L : ℕ) (f : ℕ → ℂ)
    (H : Finset (AddChar X₀ ℂ)) (F : AddChar X₀ ℂ → Finset (Finset J))
    (n : ℕ) (hn : 1 ≤ n) {B : ℝ}
    (hb : ∀ χ ∈ H, (𝔼 x, ‖complexSupportLift p L (prefixModulation ρ χ f) (F χ) x‖ ^ n) ≤ B)
    (z₀ : X₀) :
    (𝔼 x, ‖prefixSupportLift p ρ L f H F (z₀, x)‖ ^ n) ≤ (H.card : ℝ) ^ n * B := by
  have hpoint (x : ResidueSpace p) := norm_sum_pow_le H
    (fun χ => χ z₀ * complexSupportLift p L (prefixModulation ρ χ f) (F χ) x) n hn
  simp only [norm_mul, finite_addChar_norm, one_mul] at hpoint
  have hmean := expect_le_expect (s := univ) (fun x _ => hpoint x)
  change (𝔼 x, ‖prefixSupportLift p ρ L f H F (z₀, x)‖ ^ n) ≤ _ at hmean
  rw [← mul_expect, expect_sum_comm] at hmean
  apply hmean.trans
  calc
    (H.card : ℝ) ^ (n - 1) * ∑ χ ∈ H,
        (𝔼 x, ‖complexSupportLift p L (prefixModulation ρ χ f) (F χ) x‖ ^ n) ≤
      (H.card : ℝ) ^ (n - 1) * ∑ _χ ∈ H, B :=
        mul_le_mul_of_nonneg_left (sum_le_sum hb) (by positivity)
    _ = (H.card : ℝ) ^ n * B := by
      rw [sum_const, nsmul_eq_mul, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel hn]

theorem uniform_prefix_moment (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {J X₀ : Type} [Fintype J] [DecidableEq J]
      [AddCommGroup X₀] [Fintype X₀] (p : J → ℕ) [∀ j, NeZero (p j)]
      (ρ : ℤ →+ X₀), (Pairwise fun i j => (p i).Coprime (p j)) → Function.Injective p →
      ∀ (H : Finset (AddChar X₀ ℂ)) (F : AddChar X₀ ℂ → Finset (Finset J)) (Q : ℕ),
      0 < Q → (∀ χ ∈ H, ∀ U ∈ F χ, ∏ j ∈ U, p j ≤ Q) →
      ∀ L : ℕ, 0 < L → 2 * (Q : ℝ) ≤ L → (Q : ℝ) ^ 5 ≤ L →
      ∀ (f : ℕ → ℂ) (M : ℝ), 0 ≤ M → (∀ n < L, ‖f n‖ ≤ M) → ∀ z₀ : X₀,
      (𝔼 x, ‖prefixSupportLift p ρ L f H F (z₀, x)‖ ^ (2 * r)) ≤
        (H.card : ℝ) ^ (2 * r) *
          (C * (Q : ℝ) ^ ε * M ^ (2 * (r - 1)) * ((L : ℝ)⁻¹ * ∑ n ∈ range L, ‖f n‖ ^ 2)) := by
  obtain ⟨C, hC, hc⟩ := uniform_complex_support_moment r hr ε hε
  refine ⟨C, hC, ?_⟩
  intro J X₀ _ _ _ _ p _ ρ hp hinj H F Q hQ hden L hL hsmall hsmall' f M hM hf z₀
  apply prefix_moment_of_component_bounds p ρ L f H F (2 * r) (by omega) _ z₀
  intro χ hχ
  have h := hc p hp hinj (F χ) Q hQ (hden χ hχ) L hL hsmall hsmall'
    (prefixModulation ρ χ f) M hM (fun n hn => by simpa only [prefixModulation_norm] using hf n hn)
  simpa only [prefixModulation_norm] using h

end Sarkozy.FourierArithmetic
