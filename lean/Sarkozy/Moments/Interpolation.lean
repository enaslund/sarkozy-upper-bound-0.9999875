module

public import Sarkozy.Moments.Holder

/-!
# Weighted geometric interpolation

The reverse weighted Hölder estimate below is the Hessian inequality for
the square of an Lp norm when 1 < p ≤ 2.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiniteLaw

variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)

theorem expect_pos_of_pos {f : Ω → ℝ} (hf : ∀ x, 0 < f x) : 0 < μ.expect f := by
  by_contra! h
  have hz : μ.expect f = 0 := le_antisymm h (μ.expect_nonneg (fun x => (hf x).le))
  have hterm (x : Ω) : μ.weight x * f x = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => mul_nonneg (μ.nonneg y) (hf y).le)).mp
      hz x (Finset.mem_univ _)
  have hw (x : Ω) : μ.weight x = 0 := (mul_eq_zero.mp (hterm x)).resolve_right (hf x).ne'
  have ht := μ.total
  simp only [hw, Finset.sum_const_zero] at ht
  norm_num at ht

theorem lpNorm_inv_rpow {a : ℝ} (ha : 0 < a) (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) :
    μ.lpNorm (1 / a) (fun x => f x ^ a) = μ.expect f ^ a := by
  unfold lpNorm moment
  simp only [abs_of_nonneg (Real.rpow_nonneg (hf _) _), ← Real.rpow_mul (hf _),
    mul_one_div_cancel ha.ne', Real.rpow_one, one_div_one_div]

theorem expect_mul_rpow_le {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (f g : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    μ.expect (fun x => f x ^ a * g x ^ (1 - a)) ≤
      μ.expect f ^ a * μ.expect g ^ (1 - a) := by
  let p : Fin 2 → ℝ := ![1 / a, 1 / (1 - a)]
  let k : Fin 2 → Ω → ℝ := ![fun x => f x ^ a, fun x => g x ^ (1 - a)]
  have hp : ∀ i, 0 < p i := by
    intro i
    fin_cases i <;> dsimp [p] <;> positivity
  have hs : ∑ i, 1 / p i = 1 := by
    simp only [Fin.sum_univ_two, p, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_div_one_div]
    ring
  have hh := μ.abs_expect_prod_le_lpNorm p hp hs k
  simp only [Fin.prod_univ_two, k, p, Matrix.cons_val_zero, Matrix.cons_val_one,
    μ.lpNorm_inv_rpow ha f hf, μ.lpNorm_inv_rpow (sub_pos.mpr ha1) g hg] at hh
  exact (le_abs_self _).trans hh

theorem lpNorm_sq_eq_moment_rpow {p : ℝ} (f : Ω → ℝ) :
    μ.lpNorm p f ^ 2 = μ.moment p f ^ (2 / p) := by
  rw [lpNorm, ← Real.rpow_natCast (μ.moment p f ^ (1 / p)) 2,
    ← Real.rpow_mul (μ.moment_nonneg p f)]
  congr 1
  norm_num
  ring

/-- Hölder in the form needed to bound the second derivative of the norm. -/
theorem reverse_holder_hessian {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2)
    (g h : Ω → ℝ) (hg : ∀ x, 0 < g x) :
    μ.lpNorm p h ^ 2 ≤
      μ.expect (fun x => g x ^ p) ^ (2 / p - 1) *
        μ.expect (fun x => g x ^ (p - 2) * h x ^ 2) := by
  have hA : 0 < μ.expect (fun x => g x ^ p) :=
    μ.expect_pos_of_pos (fun x => Real.rpow_pos_of_pos (hg x) _)
  by_cases heq : p = 2
  · subst p
    simp only [div_self (by norm_num : (2 : ℝ) ≠ 0), sub_self, Real.rpow_zero, one_mul]
    simpa only [sq_abs, Nat.cast_ofNat] using (μ.lpNorm_nat_pow (by norm_num : (2 : ℕ) ≠ 0) h).le
  have hplt : p < 2 := lt_of_le_of_ne hp2 heq
  let A := μ.expect (fun x => g x ^ p)
  let B := μ.expect (fun x => g x ^ (p - 2) * h x ^ 2)
  have hB : 0 ≤ B := μ.expect_nonneg (fun x =>
    mul_nonneg (Real.rpow_nonneg (hg x).le _) (sq_nonneg _))
  have he (x : Ω) : (g x ^ (p - 2) * h x ^ 2) ^ (p / 2) *
      (g x ^ p) ^ (1 - p / 2) = |h x| ^ p := by
    rw [Real.mul_rpow (Real.rpow_nonneg (hg x).le _) (sq_nonneg _),
      ← Real.rpow_mul (hg x).le, ← Real.rpow_mul (hg x).le,
      ← sq_abs, ← Real.rpow_natCast |h x| 2, ← Real.rpow_mul (abs_nonneg _)]
    rw [mul_right_comm, ← Real.rpow_add (hg x)]
    ring_nf
    rw [Real.rpow_zero, one_mul]
  have hh := μ.expect_mul_rpow_le (by positivity : 0 < p / 2) (by linarith : p / 2 < 1)
    (fun x => g x ^ (p - 2) * h x ^ 2) (fun x => g x ^ p)
    (fun x => mul_nonneg (Real.rpow_nonneg (hg x).le _) (sq_nonneg _))
    (fun x => Real.rpow_nonneg (hg x).le _)
  simp only [he] at hh
  have hpow := Real.rpow_le_rpow (μ.moment_nonneg p h) hh (by positivity : 0 ≤ 2 / p)
  rw [← μ.lpNorm_sq_eq_moment_rpow] at hpow
  change μ.lpNorm p h ^ 2 ≤ (B ^ (p / 2) * A ^ (1 - p / 2)) ^ (2 / p) at hpow
  rw [Real.mul_rpow (Real.rpow_nonneg hB _) (Real.rpow_nonneg hA.le _),
    ← Real.rpow_mul hB, ← Real.rpow_mul hA.le,
    show p / 2 * (2 / p) = 1 by field_simp,
    show (1 - p / 2) * (2 / p) = 2 / p - 1 by field_simp,
    Real.rpow_one, mul_comm] at hpow
  exact hpow

end Sarkozy.FiniteLaw
