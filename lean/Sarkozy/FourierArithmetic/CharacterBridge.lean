module

public import Sarkozy.FourierArithmetic.MassMoments
public import Sarkozy.FourierSymmetry
public import Sarkozy.Moments.Basic

/-!
# Identifying support pieces with the paper's Fourier lift

The character expansion and the exact-support kernel expansion describe the
same finite Fourier sum. This bridge connects the arithmetic moment estimate
to the energy's explicit character-based definition.
-/

@[expose] public section

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Sarkozy.FourierArithmetic

variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀ j, NeZero (p j)]

noncomputable def productCharacter (a : ResidueSpace p) : AddChar (ResidueSpace p) ℂ where
  toFun := prodChar p a
  map_zero_eq_one' := prodChar_zero_right p a
  map_add_eq_mul' := prodChar_add_right p a

noncomputable def integerResidue : ℤ →+ ResidueSpace p where
  toFun n := fun j => (n : ZMod (p j))
  map_zero' := by ext j; simp
  map_add' := by intro a b; ext j; simp

theorem productCharacter_single (a : ResidueSpace p) (j : J) :
    productCharacter p a (Pi.single j 1) = ZMod.stdAddChar (a j) := by
  change prodChar p a (Pi.single j 1) = _
  unfold prodChar
  rw [prod_eq_single j]
  · simp only [Pi.single_eq_same, mul_one]
  · intro i _ hij
    simp only [Pi.single_eq_of_ne hij, mul_zero, AddChar.map_zero_eq_one]
  · simp

theorem productCharacter_injective : Function.Injective (productCharacter p) := by
  intro a b hab
  funext j
  have h := congrArg (fun χ : AddChar (ResidueSpace p) ℂ => χ (Pi.single j 1)) hab
  simp only [productCharacter_single] at h
  exact ZMod.injective_stdAddChar h

omit [DecidableEq J] in
@[simp] theorem productCharacter_zero : productCharacter p 0 = 1 := by
  ext z
  exact prodChar_zero p z

theorem productCharacter_neg (a : ResidueSpace p) :
    productCharacter p (-a) = (productCharacter p a)⁻¹ := by
  ext z
  rw [finite_addChar_inv]
  exact prodChar_neg p a z

noncomputable def supportFrequencies (F : Finset (Finset J)) : Finset (ResidueSpace p) :=
  univ.filter (fun a => primeSupport p a ∈ F)

noncomputable def supportCharacters (F : Finset (Finset J)) : Finset (AddChar (ResidueSpace p) ℂ) :=
  (supportFrequencies p F).image (productCharacter p)

theorem supportCharacters_one {F : Finset (Finset J)} (hF : ∅ ∈ F) :
    (1 : AddChar (ResidueSpace p) ℂ) ∈ supportCharacters p F := by
  apply mem_image.mpr
  refine ⟨0, ?_, productCharacter_zero p⟩
  simp only [supportFrequencies, mem_filter, mem_univ, true_and, primeSupport, Pi.zero_apply,
    ne_eq, not_true_eq_false, filter_false]
  exact hF

theorem supportCharacters_inverse (F : Finset (Finset J)) :
    ∀ χ ∈ supportCharacters p F, χ⁻¹ ∈ supportCharacters p F := by
  intro χ hχ
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hχ
  apply mem_image.mpr
  refine ⟨-a, ?_, productCharacter_neg p a⟩
  have he : primeSupport p (-a) = primeSupport p a := by
    ext j
    simp only [primeSupport, mem_filter, mem_univ, true_and, Pi.neg_apply, neg_ne_zero]
  simpa only [supportFrequencies, mem_filter, mem_univ, true_and, he] using ha

omit [Fintype J] [∀ j, NeZero (p j)] in
theorem coordinateFreeze_empty (z x : ResidueSpace p) : coordinateFreeze p ∅ z x = x := by
  ext j
  simp only [coordinateFreeze, Finset.notMem_empty, ite_false]

theorem liftPiece_fourier (L : ℕ) (f : ℕ → ℝ) (U : Finset J) (x : ResidueSpace p) :
    (liftPiece p L f U x : ℂ) =
      ∑ a ∈ univ.filter (fun a => primeSupport p a = U),
        gateCoefficient p L (fun n => (f n : ℂ)) ∅ 0 a * prodChar p a x := by
  have h := liftPiece_freeze_fourier p L f U ∅ 0 x
  simpa only [coordinateFreeze_empty, sdiff_empty, inter_empty, fourierPolynomial,
    ite_mul, zero_mul, ← sum_filter] using h

theorem supportPieces_fourier (L : ℕ) (f : ℕ → ℝ) (F : Finset (Finset J)) (x : ResidueSpace p) :
    ((∑ U ∈ F, liftPiece p L f U x : ℝ) : ℂ) =
      ∑ a ∈ supportFrequencies p F,
        gateCoefficient p L (fun n => (f n : ℂ)) ∅ 0 a * prodChar p a x := by
  rw [Complex.ofReal_sum]
  simp only [liftPiece_fourier]
  exact sum_fiberwise_eq_sum_filter univ F (primeSupport p) _

theorem uniform_expect_eq_expect {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) :
    (FiniteLaw.uniform X).expect f = 𝔼 x, f x := by
  rw [FiniteLaw.expect_uniform, expect_eq_sum_div_card, card_univ]

end Sarkozy.FourierArithmetic
