module

public import Sarkozy.PaperNumbers.Histogram

@[expose] public section

/-!
# Rational upper bounds for `exp`, `log(1+u)` and `1 - e^{-y}`

Elementary tools for the cell bounds of `eq:record:cell-charge` (`lem:record:block-charge`(i)) at
`a_T`, all checked by rational arithmetic in the kernel.

* `ceilScaled D q` is `⌈D q⌉` (for `q ≥ 0`) as a natural number; `roundUpQ q` rounds `q` up to the
  grid `2^{-256}` (`le_roundUpQ`).
* **`exp_le_expUpQ`**: `exp φ ≤ expUpQ φ` for rational `|φ| ≤ 64`. The bound is the Taylor
  polynomial of degree 15 at `φ/64` plus Mathlib's remainder (`Real.exp_bound`), rounded up to the
  grid and raised to the power 64 by N1's rounded-up binary powering `PaperNumbers.powUp`.
* **`log_one_add_le_logUp`**: `log(1+u) ≤ u - u²/2 + u³/(1-u)` for `0 ≤ u < 1`
  (`Real.abs_log_sub_add_sum_range_le`).
* **`one_sub_exp_neg_le_kappa`**: `1 - e^{-y} ≤ y - y²/2 + y³/6 + 5y⁴/96` for `0 ≤ y ≤ 1`
  (`Real.exp_bound`).
-/

open Finset

namespace Sarkozy.AnalyticCells

open Sarkozy.Certificates Sarkozy.PaperNumbers

/-- The fixed-point scale `2²⁵⁶`. -/
def scale : ℕ := 2 ^ 256

theorem scale_pos : 0 < scale := by unfold scale; positivity

/-- `⌈D q⌉` for `q ≥ 0`, as a natural number (`0` if `q < 0`). -/
def ceilScaled (D : ℕ) (q : ℚ) : ℕ := ((q.num * D + q.den - 1) / (q.den : ℤ)).toNat

theorem le_ceilScaled (D : ℕ) (q : ℚ) : q * D ≤ (ceilScaled D q : ℚ) := by
  unfold ceilScaled
  set N : ℤ := q.num * D + q.den - 1 with hN
  have hd : (0 : ℤ) < q.den := by exact_mod_cast q.den_pos
  have h1 := Int.emod_add_mul_ediv N (q.den : ℤ)
  have h2 := Int.emod_lt_of_pos N hd
  have hk : q.num * D ≤ (q.den : ℤ) * (N / q.den) := by linarith
  have hkQ : ((q.num * D : ℤ) : ℚ) ≤ (((q.den : ℤ) * (N / q.den) : ℤ) : ℚ) := by exact_mod_cast hk
  push_cast at hkQ
  have hq : q * D = (q.num : ℚ) * D / q.den := by
    rw [mul_comm (q.num : ℚ), mul_div_assoc, mul_comm]
    congr 1
    exact (Rat.num_div_den q).symm
  have hdQ : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have h3 : q * D ≤ ((N / q.den : ℤ) : ℚ) := by
    rw [hq, div_le_iff₀ hdQ]
    linarith
  have h4 : (N / q.den : ℤ) ≤ ((N / q.den).toNat : ℤ) := Int.self_le_toNat _
  have h4' : ((N / q.den : ℤ) : ℚ) ≤ (((N / q.den).toNat : ℤ) : ℚ) := by exact_mod_cast h4
  have h5 : (((N / q.den).toNat : ℤ) : ℚ) = (((N / q.den).toNat : ℕ) : ℚ) := by push_cast; rfl
  linarith

/-- `q` rounded up to the grid `2^{-256}`. -/
def roundUpQ (q : ℚ) : ℚ := (ceilScaled scale q : ℚ) / scale

theorem le_roundUpQ (q : ℚ) : q ≤ roundUpQ q := by
  unfold roundUpQ
  have hs : (0 : ℚ) < scale := by exact_mod_cast scale_pos
  rw [le_div_iff₀ hs]
  exact le_ceilScaled scale q

theorem le_roundUpQ_real (q : ℚ) : (q : ℝ) ≤ (roundUpQ q : ℝ) := by exact_mod_cast le_roundUpQ q

/-! ## The exponential -/

/-- The Taylor upper bound `∑_{i<16} q^i/i! + R₁₆(q)` (valid for `|q| ≤ 1`). -/
def taylorUp (q : ℚ) : ℚ := expSeries q 16 + expRemainder q 16

theorem exp_le_taylorUp {q : ℚ} (hq : |q| ≤ 1) : Real.exp q ≤ (taylorUp q : ℝ) := by
  have hs : |(q : ℝ)| ≤ 1 := by exact_mod_cast hq
  have ht := Real.exp_bound hs (n := 16) (by norm_num)
  have h1 : (taylorUp q : ℝ) = (∑ m ∈ range 16, (q : ℝ) ^ m / m.factorial) +
      |(q : ℝ)| ^ 16 * ((Nat.succ 16 : ℕ) / ((Nat.factorial 16 : ℕ) * (16 : ℕ)) : ℝ) := by
    unfold taylorUp
    push_cast
    rw [cast_expSeries, cast_expRemainder]
    push_cast
    ring
  rw [h1]
  have := (abs_le.mp ht).2
  push_cast at this ⊢
  linarith

/-- **An upper bound of `exp φ`**: `(⌈2²⁵⁶ taylorUp(φ/64)⌉/2²⁵⁶)^64`, by rounded-up powering. -/
def expUpQ (φ : ℚ) : ℚ := (powUp scale 7 (ceilScaled scale (taylorUp (φ / 64))) 64 : ℚ) / scale

theorem exp_le_expUpQ {φ : ℚ} (hφ : |φ| ≤ 64) : Real.exp φ ≤ (expUpQ φ : ℝ) := by
  have hq : |φ / 64| ≤ 1 := by
    rw [abs_div]
    norm_num
    linarith
  have h1 := exp_le_taylorUp hq
  have hsR : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  have h2 : (taylorUp (φ / 64) : ℝ) ≤ (ceilScaled scale (taylorUp (φ / 64)) : ℝ) / scale := by
    rw [le_div_iff₀ hsR]
    exact_mod_cast le_ceilScaled scale (taylorUp (φ / 64))
  have he : Real.exp (φ : ℝ) = Real.exp ((φ / 64 : ℚ) : ℝ) ^ 64 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he]
  have h3 : Real.exp ((φ / 64 : ℚ) : ℝ) ^ 64 ≤
      ((ceilScaled scale (taylorUp (φ / 64)) : ℝ) / scale) ^ 64 :=
    pow_le_pow_left₀ (Real.exp_pos _).le (h1.trans h2) 64
  have h4 := powUp_spec scale_pos (ceilScaled scale (taylorUp (φ / 64))) 7 64 (by norm_num)
  have h5 : (expUpQ φ : ℝ) = (powUp scale 7 (ceilScaled scale (taylorUp (φ / 64))) 64 : ℝ) /
      scale := by
    unfold expUpQ
    push_cast
    rfl
  rw [h5]
  exact h3.trans h4

/-- `exp x ≤ expUpQ φ` for real `x ≤ φ`. -/
theorem exp_le_expUpQ_of_le {x : ℝ} {φ : ℚ} (hx : x ≤ φ) (hφ : |φ| ≤ 64) :
    Real.exp x ≤ (expUpQ φ : ℝ) :=
  (Real.exp_le_exp.mpr hx).trans (exp_le_expUpQ hφ)

/-! ## `log (1 + u)` and `1 - e^{-y}` -/

/-- `u - u²/2 + u³/(1-u)`. -/
def logUp (u : ℚ) : ℚ := u - u ^ 2 / 2 + u ^ 3 / (1 - u)

theorem log_one_add_le_logUp {u : ℚ} (h0 : 0 ≤ u) (h1 : u < 1) :
    Real.log (1 + (u : ℝ)) ≤ (logUp u : ℝ) := by
  have h0' : (0 : ℝ) ≤ u := by exact_mod_cast h0
  have h1' : (u : ℝ) < 1 := by exact_mod_cast h1
  have habs : |(-(u : ℝ))| < 1 := by rw [abs_neg, abs_of_nonneg h0']; exact h1'
  have h := Real.abs_log_sub_add_sum_range_le habs 2
  rw [abs_neg, abs_of_nonneg h0'] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_neg_eq_add] at h
  have h2 := (abs_le.mp h).2
  have h3 : (logUp u : ℝ) = (u : ℝ) - (u : ℝ) ^ 2 / 2 + (u : ℝ) ^ 3 / (1 - (u : ℝ)) := by
    unfold logUp
    push_cast
    ring
  rw [h3]
  norm_num at h2
  linarith

/-- `y - y²/2 + y³/6 + 5y⁴/96`. -/
def kappa (y : ℚ) : ℚ := y - y ^ 2 / 2 + y ^ 3 / 6 + 5 * y ^ 4 / 96

theorem one_sub_exp_neg_le_kappa {y : ℚ} (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    1 - Real.exp (-(y : ℝ)) ≤ (kappa y : ℝ) := by
  have h0' : (0 : ℝ) ≤ y := by exact_mod_cast h0
  have habs : |(-(y : ℝ))| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg h0']
    exact_mod_cast h1
  have h := Real.exp_bound habs (n := 4) (by norm_num)
  rw [abs_neg, abs_of_nonneg h0'] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have h2 := (abs_le.mp h).1
  have h3 : (kappa y : ℝ) = (y : ℝ) - (y : ℝ) ^ 2 / 2 + (y : ℝ) ^ 3 / 6 + 5 * (y : ℝ) ^ 4 / 96 := by
    unfold kappa
    push_cast
    ring
  rw [h3]
  norm_num [Nat.factorial] at h2
  nlinarith [h2]

end Sarkozy.AnalyticCells
