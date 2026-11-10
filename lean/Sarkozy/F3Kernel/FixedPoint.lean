module

public import Sarkozy.F3Kernel.Checker
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

/-!
# Soundness of the certificate's fixed-point arithmetic

The checker rounds each product upwards at scale `2^64`. These lemmas turn its integer
calculations into real upper bounds, including the final factor `sqrt (2^ex)`.
No correctness assumption about the generated factor tables is made here: the table entries
must separately bound the intended real factors.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

/-- The real value represented by a nonnegative fixed-point integer. -/
noncomputable def value64 (a : ℕ) : ℝ := a / 2 ^ 64

/-- Exactly the upward-rounded multiplication used by `uLoop` and `cLoop`. -/
def mul64 (a b : ℕ) : ℕ := Nat.shiftRight (a * b + FULL64) 64

theorem value64_nonneg (a : ℕ) : 0 ≤ value64 a := by
  unfold value64
  positivity

@[simp] theorem value64_one : value64 (2 ^ 64) = 1 := by
  norm_num [value64]

/-- The integer rounding inequality, before any coercion to the reals. -/
theorem mul64_upper (a b : ℕ) : a * b ≤ mul64 a b * 2 ^ 64 := by
  unfold mul64 FULL64
  change a * b ≤ ((a * b + 18446744073709551615) >>> 64) * 2 ^ 64
  rw [Nat.shiftRight_eq_div_pow]
  have h := Nat.mod_lt (a * b + 18446744073709551615)
    (by norm_num : 0 < (2 : ℕ) ^ 64)
  have he := Nat.mod_add_div (a * b + 18446744073709551615) (2 ^ 64)
  norm_num at h he ⊢
  omega

theorem value64_mul_le (a b : ℕ) :
    value64 a * value64 b ≤ value64 (mul64 a b) := by
  have h : (a : ℝ) * b ≤ (mul64 a b : ℝ) * 2 ^ 64 := by
    exact_mod_cast mul64_upper a b
  unfold value64
  norm_num at h ⊢
  nlinarith

/-- Multiplying upper bounds preserves the upper-bound invariant. -/
theorem mul64_sound {a b : ℕ} {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ha : x ≤ value64 a) (hb : y ≤ value64 b) :
    x * y ≤ value64 (mul64 a b) :=
  (mul_le_mul ha hb hy (le_trans hx ha)).trans (value64_mul_le a b)

/-- An integer square comparison suffices to certify a square-root table entry. -/
theorem sqrt_le_value64 {x : ℝ} {a : ℕ}
    (h : x * (2 : ℝ) ^ 128 ≤ (a : ℝ) ^ 2) :
    Real.sqrt x ≤ value64 a := by
  apply (Real.sqrt_le_iff).2
  refine ⟨value64_nonneg _, ?_⟩
  unfold value64
  norm_num at h ⊢
  nlinarith

/-- Integer left shift exactly multiplies a fixed-point value by a power of two. -/
theorem value64_shiftLeft (a n : ℕ) :
    value64 (Nat.shiftLeft a n) = value64 a * (2 : ℝ) ^ n := by
  change value64 (a <<< n) = value64 a * (2 : ℝ) ^ n
  simp only [value64, Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- The final odd-exponent correction and left shift of `leafCheck`. -/
def pow64 (sq2 ex a : ℕ) : ℕ :=
  Nat.shiftLeft (if Nat.land ex 1 = 1 then mul64 a sq2 else a) (ex / 2)

theorem sqrt_two_pow (ex : ℕ) :
    Real.sqrt ((2 : ℝ) ^ ex) =
      (if ex % 2 = 1 then Real.sqrt 2 else 1) * (2 : ℝ) ^ (ex / 2) := by
  have he : ex = (ex / 2) * 2 + ex % 2 := by omega
  conv_lhs => rw [he, pow_add, pow_mul]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hr := Nat.mod_lt ex (by decide : 0 < 2)
  interval_cases ex % 2 <;> simp [mul_comm]

/-- Soundness of the final power-of-two adjustment, including odd exponents. -/
theorem pow64_sound {sq2 ex a : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (ha : x ≤ value64 a) (hsq : Real.sqrt 2 ≤ value64 sq2) :
    Real.sqrt ((2 : ℝ) ^ ex) * x ≤ value64 (pow64 sq2 ex a) := by
  rw [sqrt_two_pow]
  unfold pow64
  rw [show Nat.land ex 1 = ex &&& 1 from rfl, Nat.and_one_is_mod, value64_shiftLeft]
  split_ifs with h
  · have hm := mul64_sound hx (Real.sqrt_nonneg 2) ha hsq
    nlinarith [mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ (2 : ℝ) ^ (ex / 2))]
  · simpa [mul_comm] using
      mul_le_mul_of_nonneg_right ha (by positivity : 0 ≤ (2 : ℝ) ^ (ex / 2))

end Sarkozy.F3Kernel
