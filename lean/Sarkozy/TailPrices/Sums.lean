module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Sarkozy.PartV.Parameters

@[expose] public section

/-!
# Sums of `n^{-w}` over the integers `n ≥ P` (`lem:tail-prices`(iv))

`paper/sections/27_tail_index.tex`, proof of `lem:tail-prices`(iv): "For `w > 1` and an integer
`P ≥ 2`, `∑_{n ≥ P} n^{-w} ≤ P^{-w} + P^{1-w}/(w-1)`". Here `w = c + 1` with `0 < c ≤ 1` (the
paper uses `w = 3/2 - 2a` and `w = 5/4 - 2a`), and the sum runs over any finite set of integers
`n ≥ P` (the tail primes at a scale). The proof is elementary, by telescoping, instead of the
integral comparison:

* `rpow_step`: `c x^{-(c+1)} ≤ (x-1)^{-c} - x^{-c}` for `x > 1` (Bernoulli's inequality
  `(1 - 1/x)^c ≤ 1 - c/x`);
* `sum_Icc_rpow_le`, **`sum_rpow_le_of_ge`**: the paper's bound `Φ = P^{-w} + P^{1-w}/(w-1)`;
* **`phi_P4_le`**, `phi_P4_le'`: at `P = P₄ = 2^{512}`, for `a ≤ 1/1024`,
  `Φ(3/2 - 2a) ≤ 2^{-253}` and `Φ(5/4 - 2a) ≤ 2^{-124}`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.TailPrices

/-- **The telescoping step**: for `0 < c ≤ 1` and `x > 1`, `c x^{-(c+1)} ≤ (x-1)^{-c} - x^{-c}`
(from Bernoulli's inequality `(1 - 1/x)^c ≤ 1 - c/x`). -/
theorem rpow_step {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {x : ℝ} (hx : 1 < x) :
    c * x ^ (-(c + 1)) ≤ (x - 1) ^ (-c) - x ^ (-c) := by
  have hx0 : 0 < x := by linarith
  set y := x⁻¹ with hy
  have hy0 : 0 < y := inv_pos.mpr hx0
  have hy1 : y < 1 := inv_lt_one_of_one_lt₀ hx
  have h1y : 0 < 1 - y := by linarith
  have hxy : x - 1 = x * (1 - y) := by
    rw [hy, mul_sub, mul_one, mul_inv_cancel₀ hx0.ne']
  have ht : (1 - y) ^ c ≤ 1 - c * y := by
    have := rpow_one_add_le_one_add_mul_self (s := -y) (by linarith) hc0.le hc1
    rw [← sub_eq_add_neg, mul_neg, ← sub_eq_add_neg] at this
    exact this
  have htpos : 0 < (1 - y) ^ c := Real.rpow_pos_of_pos h1y c
  have hinv : 1 + c * y ≤ 1 / (1 - y) ^ c := by
    rw [le_div_iff₀ htpos]
    have hcy : 0 ≤ c * y := by positivity
    nlinarith [mul_le_mul_of_nonneg_left ht (by linarith : (0 : ℝ) ≤ 1 + c * y)]
  have hX : 0 < x ^ (-c) := Real.rpow_pos_of_pos hx0 _
  have e1 : (x - 1) ^ (-c) = x ^ (-c) * (1 / (1 - y) ^ c) := by
    rw [hxy, Real.mul_rpow hx0.le h1y.le, Real.rpow_neg h1y.le, one_div]
  have e2 : x ^ (-(c + 1)) = x ^ (-c) * y := by
    rw [show -(c + 1) = -c + -1 by ring, Real.rpow_add hx0, Real.rpow_neg_one]
  rw [e1, e2]
  nlinarith [mul_le_mul_of_nonneg_left hinv hX.le]

/-- **Telescoping over `[P, M]`**: `∑_{P ≤ n ≤ M} n^{-(c+1)} ≤ P^{-(c+1)} + (P^{-c} - M^{-c})/c`
for `0 < c ≤ 1` and `P ≥ 2`. -/
theorem sum_Icc_rpow_le {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {P : ℕ} (hP : 2 ≤ P) (M : ℕ)
    (hM : P ≤ M) :
    ∑ n ∈ Icc P M, (n : ℝ) ^ (-(c + 1)) ≤
      (P : ℝ) ^ (-(c + 1)) + ((P : ℝ) ^ (-c) - (M : ℝ) ^ (-c)) / c := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hPM ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hP.trans hPM
    have hs := rpow_step hc0 hc1 (x := ((M + 1 : ℕ) : ℝ)) (by push_cast; linarith)
    have hcast : ((M + 1 : ℕ) : ℝ) - 1 = (M : ℝ) := by push_cast; ring
    rw [hcast] at hs
    have key : ((M + 1 : ℕ) : ℝ) ^ (-(c + 1)) ≤
        ((M : ℝ) ^ (-c) - ((M + 1 : ℕ) : ℝ) ^ (-c)) / c := by
      rw [le_div_iff₀ hc0]
      linarith
    have : ((P : ℝ) ^ (-c) - (M : ℝ) ^ (-c)) / c +
        ((M : ℝ) ^ (-c) - ((M + 1 : ℕ) : ℝ) ^ (-c)) / c =
          ((P : ℝ) ^ (-c) - ((M + 1 : ℕ) : ℝ) ^ (-c)) / c := by
      field_simp
      ring
    linarith

/-- **`lem:tail-prices`(iv), the series bound**: for `0 < c ≤ 1`, an integer `P ≥ 2` and any finite
set `s` of integers `n ≥ P`, `∑_{n ∈ s} n^{-(c+1)} ≤ P^{-(c+1)} + P^{-c}/c`, i.e.
`∑ n^{-w} ≤ P^{-w} + P^{1-w}/(w-1)` with `w = c + 1`. -/
theorem sum_rpow_le_of_ge {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {P : ℕ} (hP : 2 ≤ P)
    (s : Finset ℕ) (hs : ∀ n ∈ s, P ≤ n) :
    ∑ n ∈ s, (n : ℝ) ^ (-(c + 1)) ≤ (P : ℝ) ^ (-(c + 1)) + (P : ℝ) ^ (-c) / c := by
  set M := max P (s.sup id) with hMdef
  have hsub : s ⊆ Icc P M := by
    intro n hn
    rw [mem_Icc]
    exact ⟨hs n hn, le_max_of_le_right (le_sup (f := id) hn)⟩
  have h1 := sum_le_sum_of_subset_of_nonneg hsub
    (fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg n) (-(c + 1)))
  have h2 := sum_Icc_rpow_le hc0 hc1 hP M (le_max_left _ _)
  have h3 : 0 ≤ (M : ℝ) ^ (-c) / c := div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hc0.le
  have h4 : ((P : ℝ) ^ (-c) - (M : ℝ) ^ (-c)) / c = (P : ℝ) ^ (-c) / c - (M : ℝ) ^ (-c) / c := by
    rw [sub_div]
  linarith

/-- `(2^{512})^{-c} = 2^{-512 c}`. -/
theorem P4_rpow (c : ℝ) : (PartV.P4 : ℝ) ^ (-c) = (2 : ℝ) ^ (-(512 * c)) := by
  unfold PartV.P4
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  rw [Nat.cast_ofNat]
  ring

/-- **The paper's `Φ` at `P₄`, general form**: for `0 < c₀ ≤ c`,
`P₄^{-(c+1)} + P₄^{-c}/c ≤ 2^{-512 c₀} (1 + 1/c₀)`. -/
theorem phi_P4_le_gen {c c₀ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c) :
    (PartV.P4 : ℝ) ^ (-(c + 1)) + (PartV.P4 : ℝ) ^ (-c) / c ≤
      (2 : ℝ) ^ (-(512 * c₀)) * (1 + 1 / c₀) := by
  have hP1 : (1 : ℝ) ≤ PartV.P4 := by
    unfold PartV.P4
    exact_mod_cast Nat.one_le_two_pow
  have hc0 : 0 < c := lt_of_lt_of_le hc₀ hc
  have ha : (PartV.P4 : ℝ) ^ (-(c + 1)) ≤ (PartV.P4 : ℝ) ^ (-c) :=
    Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
  have hb : (PartV.P4 : ℝ) ^ (-c) ≤ (2 : ℝ) ^ (-(512 * c₀)) := by
    rw [← P4_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
  have hX : 0 ≤ (PartV.P4 : ℝ) ^ (-c) := Real.rpow_nonneg (by linarith) _
  have hd : (PartV.P4 : ℝ) ^ (-c) / c ≤ (2 : ℝ) ^ (-(512 * c₀)) / c₀ := by
    calc (PartV.P4 : ℝ) ^ (-c) / c ≤ (PartV.P4 : ℝ) ^ (-c) / c₀ :=
          div_le_div_of_nonneg_left hX hc₀ hc
      _ ≤ (2 : ℝ) ^ (-(512 * c₀)) / c₀ := div_le_div_of_nonneg_right hb hc₀.le
  calc (PartV.P4 : ℝ) ^ (-(c + 1)) + (PartV.P4 : ℝ) ^ (-c) / c ≤
      (2 : ℝ) ^ (-(512 * c₀)) + (2 : ℝ) ^ (-(512 * c₀)) / c₀ := by linarith
    _ = (2 : ℝ) ^ (-(512 * c₀)) * (1 + 1 / c₀) := by ring

/-- `2^{-k} = 1/2^k` for a natural `k`. -/
theorem two_rpow_neg_nat (k : ℕ) : (2 : ℝ) ^ (-(k : ℝ)) = 1 / 2 ^ k := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]

/-- **`Φ(3/2 - 2a)` at `P₄`** (`lem:tail-prices`(iv), the weight of the degree-three terms): for
`a ≤ 1/1024`, `P₄^{-w} + P₄^{1-w}/(w-1) ≤ 2^{-253}` with `w = 3/2 - 2a`. -/
theorem phi_P4_le {a : ℝ} (ha : a ≤ 1 / 1024) :
    (PartV.P4 : ℝ) ^ (-((1 / 2 - 2 * a) + 1)) + (PartV.P4 : ℝ) ^ (-(1 / 2 - 2 * a)) /
      (1 / 2 - 2 * a) ≤ 1 / 2 ^ 253 := by
  have h := phi_P4_le_gen (c := 1 / 2 - 2 * a) (c₀ := 255 / 512) (by norm_num) (by linarith)
  have e : (2 : ℝ) ^ (-(512 * (255 / 512 : ℝ))) = 1 / 2 ^ 255 := by
    rw [show (512 * (255 / 512 : ℝ)) = ((255 : ℕ) : ℝ) by norm_num, two_rpow_neg_nat]
  rw [e] at h
  refine h.trans ?_
  norm_num

/-- **`Φ(5/4 - 2a)` at `P₄`** (`lem:tail-prices`(iv), the `p^{1/4}`-weighted sum): for
`a ≤ 1/1024`, `P₄^{-w} + P₄^{1-w}/(w-1) ≤ 2^{-124}` with `w = 5/4 - 2a`. -/
theorem phi_P4_le' {a : ℝ} (ha : a ≤ 1 / 1024) :
    (PartV.P4 : ℝ) ^ (-((1 / 4 - 2 * a) + 1)) + (PartV.P4 : ℝ) ^ (-(1 / 4 - 2 * a)) /
      (1 / 4 - 2 * a) ≤ 1 / 2 ^ 124 := by
  have h := phi_P4_le_gen (c := 1 / 4 - 2 * a) (c₀ := 127 / 512) (by norm_num) (by linarith)
  have e : (2 : ℝ) ^ (-(512 * (127 / 512 : ℝ))) = 1 / 2 ^ 127 := by
    rw [show (512 * (127 / 512 : ℝ)) = ((127 : ℕ) : ℝ) by norm_num, two_rpow_neg_nat]
  rw [e] at h
  refine h.trans ?_
  norm_num

end Sarkozy.TailPrices
