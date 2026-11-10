module

public import Sarkozy.FourierArithmetic.CharacterBridge

/-!
# Integer indicators and the character lift

An indicator of a subset of [1,N] is viewed on the range [0,N]. The extra zero
at the left endpoint lets the arithmetic moment theorem apply directly.
The harmless change of normalization is recorded exactly.
-/

@[expose] public section

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Sarkozy.FourierArithmetic

theorem sum_range_int_indicator {E : Type*} [AddCommMonoid E]
    (N : ℕ) (A : Finset ℤ) (hA : A ⊆ Icc 0 (N : ℤ)) (f : ℤ → E) :
    (∑ n ∈ range (N + 1), if (n : ℤ) ∈ A then f n else 0) = ∑ a ∈ A, f a := by
  classical
  rw [← sum_filter]
  apply sum_bij (fun (n : ℕ) _ => (n : ℤ))
  · intro n hn
    exact (mem_filter.mp hn).2
  · intro n _ m _ h
    exact_mod_cast h
  · intro a ha
    have hab := mem_Icc.mp (hA ha)
    refine ⟨a.toNat, mem_filter.mpr ⟨mem_range.mpr ?_, ?_⟩, ?_⟩
    · omega
    · simpa only [Int.toNat_of_nonneg hab.1] using ha
    · exact Int.toNat_of_nonneg hab.1
  · intro n _
    rfl

noncomputable def integerIndicator (A : Finset ℤ) (n : ℕ) : ℝ :=
  if (n : ℤ) ∈ A then 1 else 0

theorem integerIndicator_bound (A : Finset ℤ) (n : ℕ) : |integerIndicator A n| ≤ 1 := by
  unfold integerIndicator
  split_ifs <;> norm_num

theorem integerIndicator_square_mass (N : ℕ) (A : Finset ℤ) (hA : A ⊆ Icc 0 (N : ℤ)) :
    (∑ n ∈ range (N + 1), integerIndicator A n ^ 2) = (A.card : ℝ) := by
  have h := sum_range_int_indicator N A hA (fun _ => (1 : ℝ))
  simpa only [integerIndicator, ite_pow, one_pow, zero_pow (by decide : 2 ≠ 0),
    sum_const, nsmul_eq_mul, mul_one] using h

variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀ j, NeZero (p j)]

theorem coefficient_indicator (N : ℕ) (hN : 0 < N) (A : Finset ℤ)
    (hA : A ⊆ Icc 0 (N : ℤ)) (a : ResidueSpace p) :
    fourierCoefficient (integerResidue p) N A (productCharacter p a) =
      (((N + 1 : ℕ) : ℂ) / (N : ℂ)) *
        gateCoefficient p (N + 1) (fun n => (integerIndicator A n : ℂ)) ∅ 0 a := by
  have hphase (n : ℕ) : expPhase (-(n : ℝ) * frequencyAngle p a) =
      star (productCharacter p a (integerResidue p (n : ℤ))) := by
    change _ = conj (prodChar p a (fun j => ((n : ℤ) : ZMod (p j))))
    simp only [Int.cast_natCast]
    rw [prodChar_nat_diagonal, neg_mul, expPhase_neg]
  have hsum : (∑ n ∈ range (N + 1), (integerIndicator A n : ℂ) *
      expPhase (-(n : ℝ) * frequencyAngle p a)) =
        ∑ b ∈ A, star (productCharacter p a (integerResidue p b)) := by
    simp only [integerIndicator, apply_ite, Complex.ofReal_one, Complex.ofReal_zero,
      ite_mul, one_mul, zero_mul, hphase]
    exact sum_range_int_indicator N A hA
      (fun b => star (productCharacter p a (integerResidue p b)))
  simp only [fourierCoefficient, gateCoefficient, exactGate, prod_empty,
    Complex.ofReal_one, mul_one, hsum]
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hN1 : ((N + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

theorem fourierLift_eq_indicator_pieces (N : ℕ) (hN : 0 < N) (A : Finset ℤ)
    (hA : A ⊆ Icc 0 (N : ℤ)) (F : Finset (Finset J)) (x : ResidueSpace p) :
    fourierLift (integerResidue p) N A (supportCharacters p F) x =
      (((N + 1 : ℕ) : ℝ) / (N : ℝ)) * ∑ U ∈ F, liftPiece p (N + 1) (integerIndicator A) U x := by
  have he : complexLift (integerResidue p) N A (supportCharacters p F) x =
      ((((N + 1 : ℕ) : ℝ) / (N : ℝ)) * ∑ U ∈ F, liftPiece p (N + 1) (integerIndicator A) U x : ℝ) := by
    rw [Complex.ofReal_mul, supportPieces_fourier, mul_sum]
    unfold complexLift supportCharacters
    rw [sum_image (fun a _ b _ hab => productCharacter_injective p hab)]
    apply sum_congr rfl
    intro a _
    rw [coefficient_indicator p N hN A hA a]
    change (((N + 1 : ℕ) : ℂ) / (N : ℂ)) *
      gateCoefficient p (N + 1) (fun n => (integerIndicator A n : ℂ)) ∅ 0 a *
        prodChar p a x = _
    simp only [Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  have hr := congrArg Complex.re he
  simpa only [fourierLift, Complex.ofReal_re] using hr

end Sarkozy.FourierArithmetic
