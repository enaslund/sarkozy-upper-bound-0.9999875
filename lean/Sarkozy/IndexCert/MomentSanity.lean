module

public import Sarkozy.IndexCert.Moment

@[expose] public section



namespace Sarkozy.IndexCert

open Finset Real

/-- The number of primes `p ≡ 3 (mod 4)` below `2^{14}` found by `noDiv2`. -/
theorem smallCount_eq : smallSum (fun _ => 1) 4096 = 958 := by decide +kernel

/-- `log x ≤ 2√x` for `x > 0`. -/
theorem log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [← Real.log_rpow hs, Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
    norm_num
  have h2 := Real.log_le_sub_one_of_pos hs
  linarith

/-- **`ThetaUpper` is satisfiable**: the trivial bound `θ(x; 4, 3) ≤ (x + 1) · 2√x` gives
`ThetaUpper 10^{11}`. -/
theorem thetaUpper_trivial : ThetaUpper (10 ^ 11) := by
  intro x hx1 hx
  have hx0 : 0 < x := by linarith
  have hlog : ∀ p ∈ (range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p % 4 = 3),
      Real.log p ≤ 2 * Real.sqrt x := by
    intro p hp
    have hp' := mem_range.mp (mem_filter.mp hp).1
    have hp1 : 1 ≤ p := (mem_filter.mp hp).2.1.one_lt.le
    have hpx : (p : ℝ) ≤ x := by
      have : p ≤ ⌊x⌋₊ := by omega
      exact (Nat.cast_le.mpr this).trans (Nat.floor_le hx0.le)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
    exact (Real.log_le_log hp0 hpx).trans (log_le_two_sqrt hx0)
  have hsum := sum_le_sum hlog
  rw [sum_const, nsmul_eq_mul] at hsum
  have hcard : (((range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p % 4 = 3)).card : ℝ) ≤ x + 1 := by
    have h1 := card_filter_le (range (⌊x⌋₊ + 1)) (fun p => p.Prime ∧ p % 4 = 3)
    rw [card_range] at h1
    have h2 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ x + 1 := by
      push_cast
      linarith [Nat.floor_le hx0.le]
    exact (Nat.cast_le.mpr h1).trans h2
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  unfold Target.theta4
  have : (x + 1) * (2 * Real.sqrt x) ≤ x / 2 + 10 ^ 11 * Real.sqrt x := by
    nlinarith
  calc ∑ p ∈ (range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p % 4 = 3), Real.log p
      ≤ (((range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p % 4 = 3)).card : ℝ) *
          (2 * Real.sqrt x) := hsum
    _ ≤ (x + 1) * (2 * Real.sqrt x) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ x / 2 + 10 ^ 11 * Real.sqrt x := this

end Sarkozy.IndexCert
