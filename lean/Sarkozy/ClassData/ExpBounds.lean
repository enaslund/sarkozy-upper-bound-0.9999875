module

public import Sarkozy.Certificates.Exponential
public import Sarkozy.ClassBoundsPaper.Savings

@[expose] public section

/-!
# Kernel-evaluable bounds for `exp` at a rational point

The class costs of `def:closing-quantities`(7) contain `e^{U₀}` and `e^{tU_inv}` with
`U₀ ≈ tU_inv ≈ 0.8163`. B4's rounded costs `C_{n,m}` (`ClassBoundsPaper.cQ`) exceed the harness's
upper ends by at least `5·10⁻³²` only, so the exponentials are needed to about `10⁻⁴⁰`.

* `psGo q r k s t`: the Taylor partial sum, computed forward with the running term
  `t = q^k/k!` (one multiplication and one division per term, no factorials, no recomputation),
  so that `decide +kernel` evaluates 50 terms of 60-digit rationals quickly.
* `psGo_eq`: `psGo q n 0 0 1 = expSeries q n` (the series of `Sarkozy.Certificates`).
* `remQ`: `expRemainder` for `q ≥ 0`, with B4's exposed factorial `fct`.
* **`exp_le_of_ps`**, **`le_exp_of_ps`**: `Real.exp_bound` (Mathlib) in this form.
-/

open scoped BigOperators

namespace Sarkozy.ClassData

open Sarkozy.Certificates
open Sarkozy.ClassBoundsPaper (fct fct_eq)

/-- The Taylor partial sum of `exp q`, computed forward: `r` more terms, from index `k`, with
running sum `s` and running term `t`. -/
def psGo (q : ℚ) : ℕ → ℕ → ℚ → ℚ → ℚ
  | 0, _, s, _ => s
  | r + 1, k, s, t => psGo q r (k + 1) (s + t) (t * q / ((k + 1 : ℕ) : ℚ))

theorem psGo_step (q : ℚ) (r k : ℕ) :
    psGo q r k (expSeries q k) (q ^ k / (k.factorial : ℚ)) = expSeries q (k + r) := by
  induction r generalizing k with
  | zero => rfl
  | succ r ih =>
    have hs : expSeries q k + q ^ k / (k.factorial : ℚ) = expSeries q (k + 1) := by
      unfold expSeries
      rw [Finset.sum_range_succ]
    have ht : q ^ k / (k.factorial : ℚ) * q / ((k + 1 : ℕ) : ℚ) =
        q ^ (k + 1) / ((k + 1).factorial : ℚ) := by
      rw [Nat.factorial_succ, pow_succ]
      push_cast
      have h1 : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
      have h2 : (k : ℚ) + 1 ≠ 0 := by positivity
      field_simp
    have e : k + (r + 1) = k + 1 + r := by omega
    simp only [psGo]
    rw [hs, ht, ih (k + 1), e]

/-- `psGo q n 0 0 1` is the Taylor partial sum `∑_{i<n} q^i/i!`. -/
theorem psGo_eq (q : ℚ) (n : ℕ) : psGo q n 0 0 1 = expSeries q n := by
  have h := psGo_step q n 0
  simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, div_one, zero_add] at h
  have h0 : expSeries q 0 = 0 := by simp [expSeries]
  rw [h0] at h
  exact h

/-- The Lagrange-type remainder of `Real.exp_bound` for `q ≥ 0`, with the exposed factorial. -/
def remQ (q : ℚ) (n : ℕ) : ℚ := q ^ n * ((n + 1 : ℕ) : ℚ) / ((fct n : ℚ) * (n : ℚ))

theorem remQ_eq {q : ℚ} (hq : 0 ≤ q) (n : ℕ) : remQ q n = expRemainder q n := by
  unfold remQ expRemainder
  rw [abs_of_nonneg hq, fct_eq]

/-- The two-sided Taylor bound at a rational point of `[0, 1]`. -/
theorem exp_bounds_ps {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {n : ℕ} (hn : 0 < n) :
    ((psGo q n 0 0 1 - remQ q n : ℚ) : ℝ) ≤ Real.exp (q : ℝ) ∧
      Real.exp (q : ℝ) ≤ ((psGo q n 0 0 1 + remQ q n : ℚ) : ℝ) := by
  have hs : |(q : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (by exact_mod_cast hq0)]
    exact_mod_cast hq1
  have ht := Real.exp_bound hs hn
  rw [← cast_expSeries] at ht
  have herr : |(q : ℝ)| ^ n * ((n.succ : ℝ) / ((n.factorial : ℝ) * n)) =
      (expRemainder q n : ℝ) := by
    rw [cast_expRemainder]
    simp only [Nat.succ_eq_add_one]
    push_cast
    ring
  rw [herr] at ht
  rw [psGo_eq, remQ_eq hq0]
  push_cast
  constructor
  · linarith [(abs_le.mp ht).1]
  · linarith [(abs_le.mp ht).2]

/-- **An upper bound for `exp q`** from a kernel check `psGo + remQ ≤ hi`. -/
theorem exp_le_of_ps {q hi : ℚ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {n : ℕ} (hn : 0 < n)
    (h : psGo q n 0 0 1 + remQ q n ≤ hi) : Real.exp (q : ℝ) ≤ (hi : ℝ) :=
  (exp_bounds_ps hq0 hq1 hn).2.trans (by exact_mod_cast h)

/-- **A lower bound for `exp q`** from a kernel check `lo ≤ psGo − remQ`. -/
theorem le_exp_of_ps {q lo : ℚ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {n : ℕ} (hn : 0 < n)
    (h : lo ≤ psGo q n 0 0 1 - remQ q n) : (lo : ℝ) ≤ Real.exp (q : ℝ) :=
  (show (lo : ℝ) ≤ ((psGo q n 0 0 1 - remQ q n : ℚ) : ℝ) by exact_mod_cast h).trans
    (exp_bounds_ps hq0 hq1 hn).1

end Sarkozy.ClassData
