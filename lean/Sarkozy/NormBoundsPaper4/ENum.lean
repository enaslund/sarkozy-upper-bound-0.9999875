module

public import Sarkozy.NormBoundsPaper4.EOrth
public import Sarkozy.NormBoundsPaper3.EsPaper

@[expose] public section

/-!
# The constants of `lem:record:e-orthogonal`(c) against the paper's `s^E_p` (FD)

`paper/sections/21_middle_records.tex`, `lem:record:e-law`(b),(d), `lem:record:e-orthogonal`(b),(c):
with `D₀ = (p − 3)(p − 4)(p − 5)` (`z^E_0 = D₀/(p(p − 1)(p − 2))`, exact) and
`D₁ = (p − 2)(p² − 3p + 4)` (`z₁ = D₁/(p(p − 1)(p − 2))`, exact), the constants of `eorth_unnorm`
are below the paper's terms of `s^E_p` (NB3's `sEpaper`):

* `num_star`: `p(p − 2)((1 + √2)/D₀ + |1/D₀ − 1/D₁|) ≤ 𝔰_p` (the paper's `z^E_0 ≥ 1 − 9q`,
  `z₁ − z^E_0 ≤ 7q/Z`, `z₁ ≥ 1 − 2q`);
* `num_cd`: `p/(p² − 3p + 4) ≤ 𝔰_p` (`‖𝖢𝖣‖/z₁ ≤ q/((1 − q)(1 − 2q)) ≤ 𝔰_p`);
* `num_e`: the constant of `‖𝖢𝖣H‖/z₁` is at most `e_E/(1 − 2q)`;
* `num_zz`: `1/(p² − 3p + 4) ≤ q²/((1 − q)(1 − 2q))`;
* `num_eps`: `18(p − 2)/D₀ ≤ 18q²/((1 − q)(1 − 9q))`.

Each is reduced to a polynomial inequality, checked for `p ≥ 10` by writing `p = 10 + n` (all
coefficients then nonnegative).
-/

open Finset

namespace Sarkozy.NormBoundsPaper4

open Sarkozy.NormBoundsPaper3 (frakS eEc sEpaper)

section Num

variable {P : ℝ}

theorem frakS_eq (hP : 10 ≤ P) :
    frakS (1 / P) = (1 + Real.sqrt 2) * P / ((P - 1) * (P - 9)) +
      7 * P ^ 3 / ((P - 1) ^ 2 * (P - 2) ^ 2 * (P - 9)) := by
  unfold frakS
  have h0 : P ≠ 0 := by linarith
  have h1 : P - 1 ≠ 0 := by linarith
  have h2 : P - 2 ≠ 0 := by linarith
  have h9 : P - 9 ≠ 0 := by linarith
  have e1 : 1 - 1 / P = (P - 1) / P := by field_simp
  have e2 : 1 - 2 * (1 / P) = (P - 2) / P := by field_simp
  have e9 : 1 - 9 * (1 / P) = (P - 9) / P := by field_simp
  rw [e1, e2, e9]
  field_simp

/-- `(p − 2)(p − 1)(p − 9) ≤ D₀`. -/
theorem num_d0 (hP : 10 ≤ P) :
    (P - 2) * (P - 1) * (P - 9) ≤ (P - 3) * (P - 4) * (P - 5) := by nlinarith

theorem num_star (hP : 10 ≤ P) :
    P * (P - 2) * ((1 + Real.sqrt 2) / ((P - 3) * (P - 4) * (P - 5)) +
      |1 / ((P - 3) * (P - 4) * (P - 5)) - 1 / ((P - 2) * (P ^ 2 - 3 * P + 4))|) ≤
      frakS (1 / P) := by
  rw [frakS_eq hP]
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hD0 : 0 < (P - 3) * (P - 4) * (P - 5) := by
    have : 0 < P - 3 := by linarith
    have : 0 < P - 4 := by linarith
    have : 0 < P - 5 := by linarith
    positivity
  have hq : 0 < P ^ 2 - 3 * P + 4 := by nlinarith
  have hD1 : 0 < (P - 2) * (P ^ 2 - 3 * P + 4) := by
    have : 0 < P - 2 := by linarith
    positivity
  have hle : (P - 3) * (P - 4) * (P - 5) ≤ (P - 2) * (P ^ 2 - 3 * P + 4) := by nlinarith
  have habs : |1 / ((P - 3) * (P - 4) * (P - 5)) - 1 / ((P - 2) * (P ^ 2 - 3 * P + 4))| =
      1 / ((P - 3) * (P - 4) * (P - 5)) - 1 / ((P - 2) * (P ^ 2 - 3 * P + 4)) := by
    refine abs_of_nonneg (sub_nonneg.mpr ?_)
    exact one_div_le_one_div_of_le hD0 hle
  rw [habs]
  have h19 : 0 < (P - 1) * (P - 9) := by
    have : 0 < P - 1 := by linarith
    have : 0 < P - 9 := by linarith
    positivity
  -- the `1 + √2` terms
  have t1 : P * (P - 2) * ((1 + Real.sqrt 2) / ((P - 3) * (P - 4) * (P - 5))) ≤
      (1 + Real.sqrt 2) * P / ((P - 1) * (P - 9)) := by
    rw [mul_div_assoc', div_le_div_iff₀ hD0 h19]
    have := num_d0 hP
    have hP0 : 0 ≤ P := by linarith
    have : 0 ≤ (1 + Real.sqrt 2) * P := by positivity
    nlinarith
  -- the correction
  have t2 : P * (P - 2) * (1 / ((P - 3) * (P - 4) * (P - 5)) -
      1 / ((P - 2) * (P ^ 2 - 3 * P + 4))) ≤ 7 * P ^ 3 / ((P - 1) ^ 2 * (P - 2) ^ 2 * (P - 9)) := by
    have e : P * (P - 2) * (1 / ((P - 3) * (P - 4) * (P - 5)) -
        1 / ((P - 2) * (P ^ 2 - 3 * P + 4))) =
        P * (7 * P ^ 2 - 37 * P + 52) / ((P - 3) * (P - 4) * (P - 5) * (P ^ 2 - 3 * P + 4)) := by
      rw [div_sub_div _ _ hD0.ne' hD1.ne', mul_div_assoc',
        div_eq_div_iff (mul_pos hD0 hD1).ne' (mul_pos hD0 hq).ne']
      ring
    rw [e]
    have hden : 0 < (P - 3) * (P - 4) * (P - 5) * (P ^ 2 - 3 * P + 4) := mul_pos hD0 hq
    have hden2 : 0 < (P - 1) ^ 2 * (P - 2) ^ 2 * (P - 9) := by
      have h9 : 0 < P - 9 := by linarith
      have h2 : 0 < P - 2 := by linarith
      have h1 : 0 < P - 1 := by linarith
      exact mul_pos (mul_pos (pow_pos h1 2) (pow_pos h2 2)) h9
    rw [div_le_div_iff₀ hden hden2]
    obtain ⟨y, hy, rfl⟩ : ∃ y, 0 ≤ y ∧ P = 10 + y := ⟨P - 10, by linarith, by ring⟩
    have key : 0 ≤ 8897712 + 6767824 * y + 2146874 * y ^ 2 + 363295 * y ^ 3 + 34569 * y ^ 4 +
        1753 * y ^ 5 + 37 * y ^ 6 := by positivity
    have hP0 : 0 ≤ 10 + y := by linarith
    nlinarith [mul_nonneg hP0 key]
  linarith

theorem num_cd (hP : 10 ≤ P) : P / (P ^ 2 - 3 * P + 4) ≤ frakS (1 / P) := by
  rw [frakS_eq hP]
  have hq : 0 < P ^ 2 - 3 * P + 4 := by nlinarith
  have h19 : 0 < (P - 1) * (P - 9) := by
    have : 0 < P - 1 := by linarith
    have : 0 < P - 9 := by linarith
    positivity
  have hs : 1 ≤ 1 + Real.sqrt 2 := by have := Real.sqrt_nonneg 2; linarith
  have t1 : P / (P ^ 2 - 3 * P + 4) ≤ (1 + Real.sqrt 2) * P / ((P - 1) * (P - 9)) := by
    rw [div_le_div_iff₀ hq h19]
    have hP0 : 0 ≤ P := by linarith
    have h1 : (P - 1) * (P - 9) ≤ P ^ 2 - 3 * P + 4 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs (mul_nonneg hP0 hq.le)]
  have t2 : 0 ≤ 7 * P ^ 3 / ((P - 1) ^ 2 * (P - 2) ^ 2 * (P - 9)) := by
    have : 0 < P - 9 := by linarith
    have : 0 ≤ P := by linarith
    positivity
  linarith

theorem num_zz (hP : 10 ≤ P) :
    1 / (P ^ 2 - 3 * P + 4) ≤ (1 / P) ^ 2 / ((1 - 1 / P) * (1 - 2 * (1 / P))) := by
  have h0 : P ≠ 0 := by linarith
  have e : (1 / P) ^ 2 / ((1 - 1 / P) * (1 - 2 * (1 / P))) = 1 / ((P - 1) * (P - 2)) := by
    have h1 : P - 1 ≠ 0 := by linarith
    have h2 : P - 2 ≠ 0 := by linarith
    field_simp
  rw [e]
  have h12 : 0 < (P - 1) * (P - 2) := by
    have : 0 < P - 1 := by linarith
    have : 0 < P - 2 := by linarith
    positivity
  exact one_div_le_one_div_of_le h12 (by nlinarith)

theorem num_eps (hP : 10 ≤ P) :
    18 * (P - 2) / ((P - 3) * (P - 4) * (P - 5)) ≤
      18 * (1 / P) ^ 2 / ((1 - 1 / P) * (1 - 9 * (1 / P))) := by
  have h0 : P ≠ 0 := by linarith
  have e : 18 * (1 / P) ^ 2 / ((1 - 1 / P) * (1 - 9 * (1 / P))) = 18 / ((P - 1) * (P - 9)) := by
    have h1 : P - 1 ≠ 0 := by linarith
    have h9 : P - 9 ≠ 0 := by linarith
    field_simp
  rw [e]
  have hD0 : 0 < (P - 3) * (P - 4) * (P - 5) := by
    have : 0 < P - 3 := by linarith
    have : 0 < P - 4 := by linarith
    have : 0 < P - 5 := by linarith
    positivity
  have h19 : 0 < (P - 1) * (P - 9) := by
    have : 0 < P - 1 := by linarith
    have : 0 < P - 9 := by linarith
    positivity
  rw [div_le_div_iff₀ hD0 h19]
  nlinarith [num_d0 hP]

/-- The constant of `‖𝖢𝖣 H‖/z₁` is at most the paper's `e_E/(1 − 2q)`. -/
theorem num_e (hP : 10 ≤ P) :
    Real.sqrt P * Real.sqrt ((2 * (P - 2) ^ 2 + 4) / ((P - 2) * (P - 3))) /
      (P ^ 2 - 3 * P + 4) ≤ eEc (1 / P) (1 / Real.sqrt P) / (1 - 2 * (1 / P)) := by
  have hP0 : 0 < P := by linarith
  have h1 : 0 < P - 1 := by linarith
  have h2 : 0 < P - 2 := by linarith
  have h3 : 0 < P - 3 := by linarith
  have hq : 0 < P ^ 2 - 3 * P + 4 := by nlinarith
  have hG : 0 ≤ (2 * (P - 2) ^ 2 + 4) / ((P - 2) * (P - 3)) := by positivity
  have hA : 0 < (1 - 1 / P) * (1 - 3 * (1 / P)) := by
    have : 1 - 1 / P = (P - 1) / P := by field_simp
    have : 1 - 3 * (1 / P) = (P - 3) / P := by field_simp
    rw [‹1 - 1 / P = _›, this]; positivity
  have hB : 0 ≤ 2 + 4 * (1 / P) ^ 2 / (1 - 2 * (1 / P)) ^ 2 := by positivity
  have h2q : 0 < 1 - 2 * (1 / P) := by
    have : 1 - 2 * (1 / P) = (P - 2) / P := by field_simp
    rw [this]; positivity
  have hL0 : 0 ≤ Real.sqrt P * Real.sqrt ((2 * (P - 2) ^ 2 + 4) / ((P - 2) * (P - 3))) /
      (P ^ 2 - 3 * P + 4) := by positivity
  have hR0 : 0 ≤ eEc (1 / P) (1 / Real.sqrt P) / (1 - 2 * (1 / P)) := by
    unfold eEc; positivity
  refine (pow_le_pow_iff_left₀ hL0 hR0 two_ne_zero).mp ?_
  have eL : (Real.sqrt P * Real.sqrt ((2 * (P - 2) ^ 2 + 4) / ((P - 2) * (P - 3))) /
      (P ^ 2 - 3 * P + 4)) ^ 2 =
      P * (2 * (P - 2) ^ 2 + 4) / ((P - 2) * (P - 3) * (P ^ 2 - 3 * P + 4) ^ 2) := by
    rw [div_pow, mul_pow, Real.sq_sqrt hP0.le, Real.sq_sqrt hG]
    field_simp
  have eR : (eEc (1 / P) (1 / Real.sqrt P) / (1 - 2 * (1 / P))) ^ 2 =
      P * (2 * (P - 2) ^ 2 + 4) / ((P - 1) * (P - 3) * (P - 2) ^ 4) := by
    unfold eEc
    have hr2 : (1 / Real.sqrt P) ^ 2 = 1 / P := by rw [div_pow, one_pow, Real.sq_sqrt hP0.le]
    rw [div_pow, mul_pow, div_pow, mul_pow, Real.sq_sqrt hB, Real.sq_sqrt hA.le, hr2]
    have hP' : P ≠ 0 := hP0.ne'
    have e1 : 1 - 1 / P = (P - 1) / P := by field_simp
    have e3 : 1 - 3 * (1 / P) = (P - 3) / P := by field_simp
    have e2 : 1 - 2 * (1 / P) = (P - 2) / P := by field_simp
    rw [e1, e3, e2]
    have h1' : P - 1 ≠ 0 := h1.ne'
    have h2' : P - 2 ≠ 0 := h2.ne'
    have h3' : P - 3 ≠ 0 := h3.ne'
    field_simp
  rw [eL, eR]
  have hN : 0 ≤ P * (2 * (P - 2) ^ 2 + 4) := by positivity
  refine div_le_div_of_nonneg_left hN (by positivity) ?_
  -- `(p − 1)(p − 2)³ ≤ (p² − 3p + 4)²`
  have key : (P - 1) * (P - 2) ^ 3 ≤ (P ^ 2 - 3 * P + 4) ^ 2 := by nlinarith
  have h23 : 0 ≤ (P - 2) * (P - 3) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left key h23]

end Num

end Sarkozy.NormBoundsPaper4
