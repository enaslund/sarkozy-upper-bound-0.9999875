module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Two self-contained steps of `lem:density:packets`

`paper/sections/31_density_induction_upgrade.tex`, Lemma "The selected packet gates"
(`lem:density:packets`). Most of the proof checks numerical gates over the `33` pieces and the
authenticated histograms (`cert:four-routes-closing`); those are not formalized here. Two
steps are self-contained:

* `packets_ratio_mono`: the symmetric bad fraction, after division by `r³`, has the form
  `(A r + B(r) r²)/(c + d r + A r + B(r) r²)` with `B` nondecreasing; it is nondecreasing in
  `r`. So the largest `r = b^{-1/2}` on a piece, that is its least prime, bounds the bad
  fraction. The paper computes the derivative numerator `Ac + 2Bcr + Bdr² + B'r²(c + dr)`;
  the proof here is derivative-free.
* `packets_skew_mono`: the skew bad fraction is nondecreasing in `r` as well.
* `packets_tail_gate`: at a tail atom `p ≥ 2^512`, with bad fraction at most `2^{100} p^{-3/2}`
  and mixture coefficient at most `3 p^{1/50}`, the gate `fraction · (1 + coefficient)` is
  below `2^{102} p^{-37/25} < 2^{-410}`.
-/

@[expose] public section

namespace Sarkozy.DensityUpgrade

/-- **`lem:density:packets`, monotonicity of the bad fraction.** For `A, c, d ≥ 0`,
`0 < r ≤ r'`, `c + d r > 0` and `0 ≤ B ≤ B'` (the values of a nonnegative nondecreasing `B` at
`r` and `r'`),
`(A r + B r²)/(c + d r + A r + B r²) ≤ (A r' + B' r'²)/(c + d r' + A r' + B' r'²)`. -/
theorem packets_ratio_mono {A B B' c d r r' : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hr : 0 < r) (hrr : r ≤ r') (hcd : 0 < c + d * r) (hB : 0 ≤ B) (hBB : B ≤ B') :
    (A * r + B * r ^ 2) / (c + d * r + A * r + B * r ^ 2) ≤
      (A * r' + B' * r' ^ 2) / (c + d * r' + A * r' + B' * r' ^ 2) := by
  have hr' : 0 < r' := lt_of_lt_of_le hr hrr
  have hcd' : 0 < c + d * r' := by nlinarith
  have hN : 0 ≤ A * r + B * r ^ 2 := by positivity
  have hN' : 0 ≤ A * r' + B' * r' ^ 2 := by nlinarith [sq_nonneg r', mul_nonneg hB (sq_nonneg r')]
  have hD : 0 < c + d * r + A * r + B * r ^ 2 := by linarith
  have hD' : 0 < c + d * r' + A * r' + B' * r' ^ 2 := by linarith
  rw [div_le_div_iff₀ hD hD']
  -- `N D' ≤ N' D` reduces to `N (c + d r') ≤ N' (c + d r)`
  have key : (A * r + B * r ^ 2) * (c + d * r') ≤ (A * r' + B' * r' ^ 2) * (c + d * r) := by
    -- `A r (c + d r') ≤ A r' (c + d r)` since `r c ≤ r' c`
    have h1 : A * r * (c + d * r') ≤ A * r' * (c + d * r) := by
      have : r * c ≤ r' * c := mul_le_mul_of_nonneg_right hrr hc
      nlinarith [mul_nonneg hA (sub_nonneg.2 this)]
    -- `B r² (c + d r') ≤ B' r'² (c + d r)`
    have h2 : B * r ^ 2 * (c + d * r') ≤ B' * r' ^ 2 * (c + d * r) := by
      have hrr2 : r * r' ≤ r' * r' := mul_le_mul_of_nonneg_right hrr hr'.le
      have e1 : r ^ 2 * (c + d * r') ≤ r' ^ 2 * (c + d * r) := by
        have : r ^ 2 * c ≤ r' ^ 2 * c :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hrr 2) hc
        have : r ^ 2 * (d * r') ≤ r' ^ 2 * (d * r) := by
          have h3 : r * (d * r * r') ≤ r' * (d * r * r') :=
            mul_le_mul_of_nonneg_right hrr (by positivity)
          nlinarith [h3]
        nlinarith
      calc B * r ^ 2 * (c + d * r') = B * (r ^ 2 * (c + d * r')) := by ring
        _ ≤ B * (r' ^ 2 * (c + d * r)) := mul_le_mul_of_nonneg_left e1 hB
        _ ≤ B' * (r' ^ 2 * (c + d * r)) :=
            mul_le_mul_of_nonneg_right hBB (mul_nonneg (sq_nonneg _) hcd.le)
        _ = B' * r' ^ 2 * (c + d * r) := by ring
    linarith
  nlinarith [key, mul_nonneg hN hN']

/-- **`lem:density:packets`, the tail gate.** For `p ≥ 2^512`:
`2^{100} p^{-3/2} (1 + 3 p^{1/50}) ≤ 2^{102} p^{-37/25} < 2^{-410}`. -/
theorem packets_tail_gate {p : ℝ} (hp : (2 : ℝ) ^ 512 ≤ p) :
    (2 : ℝ) ^ 100 * p ^ (-(3 / 2 : ℝ)) * (1 + 3 * p ^ (1 / 50 : ℝ)) ≤
        (2 : ℝ) ^ 102 * p ^ (-(37 / 25 : ℝ)) ∧
      (2 : ℝ) ^ 102 * p ^ (-(37 / 25 : ℝ)) < (2 : ℝ) ^ (-(410 : ℝ)) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have hp1 : 1 ≤ p := le_trans (one_le_pow₀ (by norm_num)) hp
  have hq : 1 ≤ p ^ (1 / 50 : ℝ) := Real.one_le_rpow hp1 (by norm_num)
  refine ⟨?_, ?_⟩
  · -- `1 + 3 q ≤ 4 q` and `p^{-3/2} p^{1/50} = p^{-37/25}`
    have h1 : 1 + 3 * p ^ (1 / 50 : ℝ) ≤ 4 * p ^ (1 / 50 : ℝ) := by linarith
    have e : p ^ (-(3 / 2 : ℝ)) * p ^ (1 / 50 : ℝ) = p ^ (-(37 / 25 : ℝ)) := by
      rw [← Real.rpow_add hp0]
      norm_num
    have hpos : 0 ≤ (2 : ℝ) ^ 100 * p ^ (-(3 / 2 : ℝ)) := by positivity
    calc (2 : ℝ) ^ 100 * p ^ (-(3 / 2 : ℝ)) * (1 + 3 * p ^ (1 / 50 : ℝ))
        ≤ (2 : ℝ) ^ 100 * p ^ (-(3 / 2 : ℝ)) * (4 * p ^ (1 / 50 : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 hpos
      _ = (2 : ℝ) ^ 102 * (p ^ (-(3 / 2 : ℝ)) * p ^ (1 / 50 : ℝ)) := by ring
      _ = (2 : ℝ) ^ 102 * p ^ (-(37 / 25 : ℝ)) := by rw [e]
  · -- `p^{-37/25} ≤ (2^512)^{-37/25} = 2^{-18944/25}`
    have h2 : p ^ (-(37 / 25 : ℝ)) ≤ ((2 : ℝ) ^ 512) ^ (-(37 / 25 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hp (by norm_num)
    have e2 : ((2 : ℝ) ^ 512) ^ (-(37 / 25 : ℝ)) = (2 : ℝ) ^ (-(18944 / 25 : ℝ)) := by
      rw [show ((2 : ℝ) ^ 512) = (2 : ℝ) ^ ((512 : ℕ) : ℝ) from (Real.rpow_natCast 2 512).symm,
        ← Real.rpow_mul (by norm_num)]
      norm_num
    have e3 : (2 : ℝ) ^ 102 * (2 : ℝ) ^ (-(18944 / 25 : ℝ)) = (2 : ℝ) ^ (-(16394 / 25 : ℝ)) := by
      rw [show ((2 : ℝ) ^ 102) = (2 : ℝ) ^ ((102 : ℕ) : ℝ) from (Real.rpow_natCast 2 102).symm,
        ← Real.rpow_add (by norm_num)]
      norm_num
    calc (2 : ℝ) ^ 102 * p ^ (-(37 / 25 : ℝ))
        ≤ (2 : ℝ) ^ 102 * ((2 : ℝ) ^ 512) ^ (-(37 / 25 : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (2 : ℝ) ^ (-(16394 / 25 : ℝ)) := by rw [e2, e3]
      _ < (2 : ℝ) ^ (-(410 : ℝ)) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)

/-- **`lem:density:packets`, the skew bad fraction is increasing.** After division by `r³`, the
skew fraction `B_A/(G_A + B_A)` with `B_A = 2 w_C r⁴/(1 - r²)`, `G_A = w_R g_A r³` is
`x/(K + x)` with `x = 2 w_C r/(1 - r²)` and `K = w_R g_A ≥ 0`. It is nondecreasing on
`0 < r < 1`. -/
theorem packets_skew_mono {w K r r' : ℝ} (hw : 0 ≤ w) (hK : 0 ≤ K) (hr : 0 < r) (hrr : r ≤ r')
    (hr1 : r' < 1) (hpos : 0 < K + 2 * w * r / (1 - r ^ 2)) :
    (2 * w * r / (1 - r ^ 2)) / (K + 2 * w * r / (1 - r ^ 2)) ≤
      (2 * w * r' / (1 - r' ^ 2)) / (K + 2 * w * r' / (1 - r' ^ 2)) := by
  have hr'0 : 0 < r' := lt_of_lt_of_le hr hrr
  have h1 : 0 < 1 - r ^ 2 := by nlinarith
  have h1' : 0 < 1 - r' ^ 2 := by nlinarith
  -- `x = 2 w r/(1 - r²)` is nondecreasing in `r`
  have hx : 2 * w * r / (1 - r ^ 2) ≤ 2 * w * r' / (1 - r' ^ 2) := by
    rw [div_le_div_iff₀ h1 h1']
    have : r * (1 - r' ^ 2) ≤ r' * (1 - r ^ 2) := by nlinarith [mul_pos hr hr'0]
    nlinarith [mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ 2 * w)]
  have hx0 : 0 ≤ 2 * w * r / (1 - r ^ 2) := div_nonneg (by positivity) h1.le
  set x := 2 * w * r / (1 - r ^ 2)
  set x' := 2 * w * r' / (1 - r' ^ 2)
  have hpos' : 0 < K + x' := by linarith
  rw [div_le_div_iff₀ hpos hpos']
  nlinarith [mul_le_mul_of_nonneg_left hx hK]

end Sarkozy.DensityUpgrade
