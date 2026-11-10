module

public import Sarkozy.FourierArithmetic.CharacterBridge

/-!
# Complex support lifts

Modulating an integer input by a prefix character produces a complex input.
Splitting into real and imaginary parts extends the density-retaining moment
bound with a fixed constant, while retaining exactly the input square mass.
-/

@[expose] public section

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Sarkozy.FourierArithmetic

variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀ j, NeZero (p j)]

noncomputable def complexPiece (L : ℕ) (f : ℕ → ℂ) (U : Finset J) (x : ResidueSpace p) : ℂ :=
  (L : ℂ)⁻¹ * ∑ n ∈ range L, f n * (exactGate p U (x - fun j => (n : ZMod (p j))) : ℂ)

noncomputable def complexSupportLift (L : ℕ) (f : ℕ → ℂ) (F : Finset (Finset J))
    (x : ResidueSpace p) : ℂ := ∑ U ∈ F, complexPiece p L f U x

omit [Fintype J] [∀ j, NeZero (p j)] in
theorem complexPiece_re (L : ℕ) (f : ℕ → ℂ) (U : Finset J) (x : ResidueSpace p) :
    (complexPiece p L f U x).re = liftPiece p L (fun n => (f n).re) U x := by
  simp only [complexPiece, liftPiece, Complex.mul_re, Complex.inv_re, Complex.inv_im,
    Complex.natCast_re, Complex.natCast_im, Complex.normSq_natCast,
    Complex.re_sum, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    neg_zero, zero_div, zero_mul]
  by_cases hL : L = 0
  · simp [hL]
  · have hc : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL
    field_simp

omit [Fintype J] [∀ j, NeZero (p j)] in
theorem complexPiece_im (L : ℕ) (f : ℕ → ℂ) (U : Finset J) (x : ResidueSpace p) :
    (complexPiece p L f U x).im = liftPiece p L (fun n => (f n).im) U x := by
  simp only [complexPiece, liftPiece, Complex.mul_im, Complex.inv_re, Complex.inv_im,
    Complex.natCast_re, Complex.natCast_im, Complex.normSq_natCast,
    Complex.im_sum, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
    neg_zero, zero_div, zero_mul, add_zero]
  by_cases hL : L = 0
  · simp [hL]
  · have hc : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL
    field_simp

omit [Fintype J] [∀ j, NeZero (p j)] in
theorem complexSupportLift_re (L : ℕ) (f : ℕ → ℂ) (F : Finset (Finset J)) (x : ResidueSpace p) :
    (complexSupportLift p L f F x).re = ∑ U ∈ F, liftPiece p L (fun n => (f n).re) U x := by
  simp only [complexSupportLift, Complex.re_sum, complexPiece_re]

omit [Fintype J] [∀ j, NeZero (p j)] in
theorem complexSupportLift_im (L : ℕ) (f : ℕ → ℂ) (F : Finset (Finset J)) (x : ResidueSpace p) :
    (complexSupportLift p L f F x).im = ∑ U ∈ F, liftPiece p L (fun n => (f n).im) U x := by
  simp only [complexSupportLift, Complex.im_sum, complexPiece_im]

theorem complexPiece_fourier (L : ℕ) (f : ℕ → ℂ) (U : Finset J) (x : ResidueSpace p) :
    complexPiece p L f U x =
      ∑ a ∈ univ.filter (fun a => primeSupport p a = U),
        gateCoefficient p L f ∅ 0 a * prodChar p a x := by
  have he (n : ℕ) : (exactGate p U (x - fun j => (n : ZMod (p j))) : ℂ) =
      ∑ a ∈ univ.filter (fun a => primeSupport p a = U),
        prodChar p a x * conj (expPhase ((n : ℝ) * frequencyAngle p a)) := by
    rw [exactGate_fourier]
    simp only [prodChar_sub_right, prodChar_nat_diagonal]
  unfold complexPiece
  simp only [he]
  simp only [gateCoefficient, exactGate, prod_empty,
    Complex.ofReal_one, mul_one, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [sum_mul]
  apply sum_congr rfl
  intro n _
  rw [neg_mul, expPhase_neg]
  ring

theorem complexSupportLift_fourier (L : ℕ) (f : ℕ → ℂ) (F : Finset (Finset J)) (x : ResidueSpace p) :
    complexSupportLift p L f F x = ∑ a ∈ supportFrequencies p F,
      gateCoefficient p L f ∅ 0 a * prodChar p a x := by
  simp only [complexSupportLift, complexPiece_fourier]
  exact sum_fiberwise_eq_sum_filter univ F (primeSupport p) _

theorem norm_pow_le_parts (z : ℂ) (n : ℕ) :
    ‖z‖ ^ n ≤ 2 ^ n * (|z.re| ^ n + |z.im| ^ n) := by
  have hm : ‖z‖ ≤ 2 * max |z.re| |z.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im z
    linarith [le_max_left |z.re| |z.im|, le_max_right |z.re| |z.im|]
  have hpow : (max |z.re| |z.im|) ^ n ≤ |z.re| ^ n + |z.im| ^ n := by
    rcases le_total |z.re| |z.im| with h | h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (pow_nonneg (abs_nonneg _) _)
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right (pow_nonneg (abs_nonneg _) _)
  calc
    ‖z‖ ^ n ≤ (2 * max |z.re| |z.im|) ^ n := pow_le_pow_left₀ (norm_nonneg _) hm n
    _ ≤ 2 ^ n * (|z.re| ^ n + |z.im| ^ n) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hpow (by positivity)

theorem uniform_complex_support_moment (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ)
      [∀ j, NeZero (p j)], (Pairwise fun i j => (p i).Coprime (p j)) → Function.Injective p →
      ∀ (F : Finset (Finset J)) (Q : ℕ), 0 < Q → (∀ U ∈ F, ∏ j ∈ U, p j ≤ Q) →
      ∀ L : ℕ, 0 < L → 2 * (Q : ℝ) ≤ L → (Q : ℝ) ^ 5 ≤ L →
      ∀ (f : ℕ → ℂ) (M : ℝ), 0 ≤ M → (∀ n < L, ‖f n‖ ≤ M) →
      (𝔼 x, ‖complexSupportLift p L f F x‖ ^ (2 * r)) ≤
        C * (Q : ℝ) ^ ε * M ^ (2 * (r - 1)) * ((L : ℝ)⁻¹ * ∑ n ∈ range L, ‖f n‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := uniform_lift_moment_density r hr ε hε
  refine ⟨2 ^ (2 * r) * C, by positivity, ?_⟩
  intro J _ _ p _ hp hinj F Q hQ hden L hL hsmall hsmall' f M hM hf
  have hre := hbound p hp hinj F Q hQ hden L hL hsmall hsmall' (fun n => (f n).re) M hM
    (fun n hn => (Complex.abs_re_le_norm _).trans (hf n hn))
  have him := hbound p hp hinj F Q hQ hden L hL hsmall hsmall' (fun n => (f n).im) M hM
    (fun n hn => (Complex.abs_im_le_norm _).trans (hf n hn))
  have hparts := expect_le_expect (s := univ)
    (fun x _ => norm_pow_le_parts (complexSupportLift p L f F x) (2 * r))
  simp only [complexSupportLift_re, complexSupportLift_im, pow_abs_two_mul,
    ← mul_expect, expect_add_distrib] at hparts
  apply hparts.trans
  apply (mul_le_mul_of_nonneg_left (add_le_add hre him) (by positivity : (0 : ℝ) ≤ 2 ^ (2 * r))).trans_eq
  rw [← mul_add, ← mul_add, ← sum_add_distrib]
  have hnorm (n : ℕ) : (f n).re ^ 2 + (f n).im ^ 2 = ‖f n‖ ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using (Complex.sq_norm (f n)).symm
  simp only [hnorm]
  ring

end Sarkozy.FourierArithmetic
