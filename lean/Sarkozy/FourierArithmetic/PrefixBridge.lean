module

public import Sarkozy.FourierArithmetic.PrefixMoments
public import Sarkozy.FourierArithmetic.Indicator

/-!
# Prefix characters and whole-support families

This identifies a Fourier truncation with different tail-support families for
different prefix characters. It is the representation used for the finite
prime-power prefix in the paper.
-/

@[expose] public section

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Sarkozy.FourierArithmetic

variable {J X₀ : Type*} [Fintype J] [DecidableEq J]
    [AddCommGroup X₀] [Fintype X₀] (p : J → ℕ) [∀ j, NeZero (p j)]

noncomputable def prefixCharacter (χ : AddChar X₀ ℂ) (a : ResidueSpace p) :
    AddChar (X₀ × ResidueSpace p) ℂ where
  toFun z := χ z.1 * prodChar p a z.2
  map_zero_eq_one' := by simp only [Prod.fst_zero, Prod.snd_zero, AddChar.map_zero_eq_one,
    prodChar_zero_right, mul_one]
  map_add_eq_mul' z w := by
    simp only [Prod.fst_add, Prod.snd_add, AddChar.map_add_eq_mul, prodChar_add_right]
    ring

omit [DecidableEq J] [Fintype X₀] in
@[simp] theorem prefixCharacter_apply (χ : AddChar X₀ ℂ) (a : ResidueSpace p)
    (z : X₀ × ResidueSpace p) : prefixCharacter p χ a z = χ z.1 * prodChar p a z.2 := rfl

omit [Fintype X₀] in
theorem prefixCharacter_injective :
    Function.Injective (fun t : AddChar X₀ ℂ × ResidueSpace p => prefixCharacter p t.1 t.2) := by
  rintro ⟨χ, a⟩ ⟨ψ, b⟩ h
  apply Prod.ext
  · ext x
    have hh := congrArg (fun κ : AddChar (X₀ × ResidueSpace p) ℂ => κ (x, 0)) h
    simpa only [prefixCharacter_apply, prodChar_zero_right, mul_one] using hh
  · apply productCharacter_injective p
    ext x
    change prodChar p a x = prodChar p b x
    have hh := congrArg (fun κ : AddChar (X₀ × ResidueSpace p) ℂ => κ (0, x)) h
    simpa only [prefixCharacter_apply, AddChar.map_zero_eq_one, one_mul] using hh

noncomputable def prefixFrequencies (H : Finset (AddChar X₀ ℂ))
    (F : AddChar X₀ ℂ → Finset (Finset J)) : Finset (AddChar X₀ ℂ × ResidueSpace p) :=
  (H ×ˢ univ).filter (fun t => primeSupport p t.2 ∈ F t.1)

noncomputable def prefixCharacters (H : Finset (AddChar X₀ ℂ))
    (F : AddChar X₀ ℂ → Finset (Finset J)) : Finset (AddChar (X₀ × ResidueSpace p) ℂ) :=
  (prefixFrequencies p H F).image (fun t => prefixCharacter p t.1 t.2)

omit [Fintype X₀] in
theorem sum_prefixCharacters (H : Finset (AddChar X₀ ℂ))
    (F : AddChar X₀ ℂ → Finset (Finset J)) (g : AddChar (X₀ × ResidueSpace p) ℂ → ℂ) :
    ∑ κ ∈ prefixCharacters p H F, g κ =
      ∑ χ ∈ H, ∑ a ∈ supportFrequencies p (F χ), g (prefixCharacter p χ a) := by
  classical
  unfold prefixCharacters
  rw [sum_image (fun a _ b _ h => prefixCharacter_injective p h)]
  simp only [prefixFrequencies, supportFrequencies, sum_filter, sum_product]

omit [Fintype X₀] in
theorem prefixCharacters_one {H : Finset (AddChar X₀ ℂ)}
    {F : AddChar X₀ ℂ → Finset (Finset J)} (hH : 1 ∈ H) (hF : ∅ ∈ F 1) :
    (1 : AddChar (X₀ × ResidueSpace p) ℂ) ∈ prefixCharacters p H F := by
  classical
  apply mem_image.mpr
  refine ⟨(1, 0), ?_, ?_⟩
  · simp only [prefixFrequencies, mem_filter, mem_product, mem_univ, hH,
      primeSupport, Pi.zero_apply, ne_eq, not_true_eq_false, filter_false, hF, and_self]
  · ext z
    simp only [prefixCharacter_apply, AddChar.one_apply, prodChar_zero, mul_one]

omit [Fintype X₀] in
theorem prefix_coefficient_indicator (ρ : ℤ →+ X₀) (N : ℕ) (hN : 0 < N)
    (A : Finset ℤ) (hA : A ⊆ Icc 0 (N : ℤ)) (χ : AddChar X₀ ℂ) (a : ResidueSpace p) :
    fourierCoefficient (ρ.prod (integerResidue p)) N A (prefixCharacter p χ a) =
      (((N + 1 : ℕ) : ℂ) / (N : ℂ)) *
        gateCoefficient p (N + 1) (prefixModulation ρ χ (fun n => (integerIndicator A n : ℂ))) ∅ 0 a := by
  have hphase (n : ℕ) : star (prefixCharacter p χ a ((ρ.prod (integerResidue p)) (n : ℤ))) =
      star (χ (ρ n)) * expPhase (-(n : ℝ) * frequencyAngle p a) := by
    change star (χ (ρ n) * prodChar p a (fun j => ((n : ℤ) : ZMod (p j)))) = _
    simp only [Int.cast_natCast, prodChar_nat_diagonal, star_mul, neg_mul, expPhase_neg]
    exact mul_comm _ _
  have he (n : ℕ) : prefixModulation ρ χ (fun n => (integerIndicator A n : ℂ)) n *
      expPhase (-(n : ℝ) * frequencyAngle p a) =
        if (n : ℤ) ∈ A then star (prefixCharacter p χ a ((ρ.prod (integerResidue p)) (n : ℤ))) else 0 := by
    unfold prefixModulation
    rw [mul_assoc, ← hphase]
    by_cases hn : (n : ℤ) ∈ A
    · simp only [integerIndicator, ite_eq_left hn, Complex.ofReal_one, one_mul]
    · simp only [integerIndicator, ite_eq_right hn, Complex.ofReal_zero, zero_mul]
  have hsum := sum_range_int_indicator N A hA
    (fun b => star (prefixCharacter p χ a ((ρ.prod (integerResidue p)) b)))
  simp only [fourierCoefficient, gateCoefficient, exactGate, prod_empty, Complex.ofReal_one, mul_one,
    he, hsum]
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hN1 : ((N + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

omit [Fintype X₀] in
theorem complexLift_eq_prefix_indicator (ρ : ℤ →+ X₀) (N : ℕ) (hN : 0 < N)
    (A : Finset ℤ) (hA : A ⊆ Icc 0 (N : ℤ)) (H : Finset (AddChar X₀ ℂ))
    (F : AddChar X₀ ℂ → Finset (Finset J)) (z : X₀ × ResidueSpace p) :
    complexLift (ρ.prod (integerResidue p)) N A (prefixCharacters p H F) z =
      (((N + 1 : ℕ) : ℂ) / (N : ℂ)) *
        prefixSupportLift p ρ (N + 1) (fun n => (integerIndicator A n : ℂ)) H F z := by
  unfold complexLift
  rw [sum_prefixCharacters]
  simp only [prefix_coefficient_indicator p ρ N hN A hA, prefixCharacter_apply,
    prefixSupportLift, complexSupportLift_fourier, mul_sum]
  apply sum_congr rfl
  intro χ _
  apply sum_congr rfl
  intro a _
  ring

end Sarkozy.FourierArithmetic
