module

public import Sarkozy.PartVRecords.OneStageDelta

/-!
# The one-stage coefficients (`cert:record:one-stage`, the explicit part)

`paper/sections/D_certificates.tex`, `cert:record:one-stage`, for the coefficients of
`lem:record:one-stage-folded-e`: V3's `k_new` (`Sarkozy.PartVRecords.knew`) and
`s_fold(q, r) = ((1 + r)² + 4q)/(1 - 3q)² + q/(1 - 2q)²` (`sfold`), at `q = 1/X`, `r = X^{-1/2}`.

* `knew_Q3`, `knew_two_pow_45`: `k_new(Q₃) ≤ 1.0000003509` and `k_new(2^{45}) ≤ 1 + 2.0·10⁻¹³`;
* `sfold_Q3`, `sfold_two_pow_45`: `s_fold(Q₃) ≤ 1.000448358` and `s_fold(2^{45}) ≤ 1.000000338`;
* `knew_mono_r`, `knew_mono_q`, `sfold_mono_r`: both are nondecreasing in `(q, r)`, so they
  decrease along the pieces, as the certificate says;
* `one_stage_gates`: the gate `α_X² r_X + β_X² q_X r_X < k_new(X)` of
  `lem:record:one-stage-folded-e`(d) and the inequality `4q + 2r(1 - 2q)/(1 + q) < 1` of its
  proof hold for every `0 ≤ q ≤ 2^{-24}`, `0 ≤ r ≤ 2^{-12}`, hence at every piece start.

The square roots are enclosed by exact rationals (`√Q₃ ≥ 4466.719`, `√(2^{45}) ≥ 5931641`), and the
bounds are monotone in `r`. **Not checked:** the comparisons with the stored (rounded) coefficients
of the native source and the dependent price coefficients, which are not in the paper's text.
-/

@[expose] public section

namespace Sarkozy.MiddleRecords

open Sarkozy.PartVRecords

/-- `s_fold` of `lem:record:one-stage-folded-e`. -/
noncomputable def sfold (q r : ℝ) : ℝ :=
  ((1 + r) ^ 2 + 4 * q) / (1 - 3 * q) ^ 2 + q / (1 - 2 * q) ^ 2

/-- `k_new` is nondecreasing in `r`. -/
theorem knew_mono_r {q r r' : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 100) (hr : r ≤ r') :
    knew q r ≤ knew q r' := by
  unfold knew
  have h1 : 0 < (1 - 3 * q) * (1 - 2 * q) := by
    have : 0 < 1 - 3 * q := by linarith
    have : 0 < 1 - 2 * q := by linarith
    positivity
  have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr hq) h1.le
  linarith

/-- **`cert:record:one-stage`, at `X = Q₃`**: `k_new(Q₃) ≤ 1.0000003509`, with
`r_X = Q₃^{-1/2} ≤ 1/4466.71`. -/
theorem knew_Q3 : knew (1 / 19951586) (1 / Real.sqrt 19951586) ≤ 1.0000003509 := by
  have hs : (4466.71 : ℝ) ≤ Real.sqrt 19951586 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hr : 1 / Real.sqrt 19951586 ≤ 1 / 4466.71 :=
    one_div_le_one_div_of_le (by norm_num) hs
  refine (knew_mono_r (by norm_num) (by norm_num) hr).trans ?_
  unfold knew
  norm_num

/-- `s_fold` is nondecreasing in `r ≥ 0`. -/
theorem sfold_mono_r {q r r' : ℝ} (hq' : q ≤ 1 / 100) (hr0 : 0 ≤ r) (hr : r ≤ r') :
    sfold q r ≤ sfold q r' := by
  unfold sfold
  have h3 : 0 < (1 - 3 * q) ^ 2 := by
    have : 0 < 1 - 3 * q := by linarith
    positivity
  have : (1 + r) ^ 2 + 4 * q ≤ (1 + r') ^ 2 + 4 * q := by nlinarith
  have := div_le_div_of_nonneg_right this h3.le
  linarith

/-- **`cert:record:one-stage`, at `X = 2^{45}`**: `k_new(2^{45}) ≤ 1 + 2.0·10⁻¹³`. -/
theorem knew_two_pow_45 :
    knew (1 / 35184372088832) (1 / Real.sqrt 35184372088832) ≤ 1 + 2.0e-13 := by
  have hs : (5931641 : ℝ) ≤ Real.sqrt 35184372088832 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hr : 1 / Real.sqrt 35184372088832 ≤ 1 / 5931641 :=
    one_div_le_one_div_of_le (by norm_num) hs
  refine (knew_mono_r (by norm_num) (by norm_num) hr).trans ?_
  unfold knew
  norm_num

/-- **`cert:record:one-stage`, at `X = Q₃`**: `s_fold(Q₃) ≤ 1.000448358`. -/
theorem sfold_Q3 : sfold (1 / 19951586) (1 / Real.sqrt 19951586) ≤ 1.000448358 := by
  have hs : (4466.719 : ℝ) ≤ Real.sqrt 19951586 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hr : 1 / Real.sqrt 19951586 ≤ 1 / 4466.719 :=
    one_div_le_one_div_of_le (by norm_num) hs
  refine (sfold_mono_r (by norm_num) (by positivity) hr).trans ?_
  unfold sfold
  norm_num

/-- **`cert:record:one-stage`, at `X = 2^{45}`**: `s_fold(2^{45}) ≤ 1.000000338`. -/
theorem sfold_two_pow_45 :
    sfold (1 / 35184372088832) (1 / Real.sqrt 35184372088832) ≤ 1.000000338 := by
  have hs : (5931641 : ℝ) ≤ Real.sqrt 35184372088832 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hr : 1 / Real.sqrt 35184372088832 ≤ 1 / 5931641 :=
    one_div_le_one_div_of_le (by norm_num) hs
  refine (sfold_mono_r (by norm_num) (by positivity) hr).trans ?_
  unfold sfold
  norm_num

/-- **`cert:record:one-stage`, the gates on the whole middle range**: for `0 ≤ q ≤ 2^{-24}`,
`0 ≤ r ≤ 2^{-12}` (every piece start `X ≥ Q₃ > 2^{24}`, `r_X = X^{-1/2}`),
`α_X² r + β_X² q r < k_new` with `α_X = (1 + 3r)/(1 - 3q)`, `β_X = 1/(1 - 2q)`
(the hypothesis of `lem:record:one-stage-folded-e`(d)), and `4q + 2r(1 - 2q)/(1 + q) < 1`
(the inequality of its proof). -/
theorem one_stage_gates {q r : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 16777216) (hr : 0 ≤ r)
    (hr' : r ≤ 1 / 4096) :
    ((1 + 3 * r) / (1 - 3 * q)) ^ 2 * r + (1 / (1 - 2 * q)) ^ 2 * q * r < knew q r ∧
      4 * q + 2 * r * (1 - 2 * q) / (1 + q) < 1 := by
  have h3 : 0 < 1 - 3 * q := by linarith
  have h2 : 0 < 1 - 2 * q := by linarith
  have hα : (1 + 3 * r) / (1 - 3 * q) ≤ 2 := by
    rw [div_le_iff₀ h3]; linarith
  have hβ : 1 / (1 - 2 * q) ≤ 2 := by
    rw [div_le_iff₀ h2]; linarith
  have hα0 : 0 ≤ (1 + 3 * r) / (1 - 3 * q) := by positivity
  have hβ0 : 0 ≤ 1 / (1 - 2 * q) := by positivity
  have hknew : 1 ≤ knew q r := by
    unfold knew
    have h1 : 1 ≤ (1 + 5 * q) / ((1 - 3 * q) * (1 + q)) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have : 0 ≤ q * r / ((1 - 3 * q) * (1 - 2 * q)) := by positivity
    linarith
  constructor
  · have ha2 : ((1 + 3 * r) / (1 - 3 * q)) ^ 2 ≤ 4 := by nlinarith
    have hb2 : (1 / (1 - 2 * q)) ^ 2 ≤ 4 := by nlinarith
    have e1 : ((1 + 3 * r) / (1 - 3 * q)) ^ 2 * r ≤ 4 * r := mul_le_mul_of_nonneg_right ha2 hr
    have e2 : (1 / (1 - 2 * q)) ^ 2 * q * r ≤ 4 * q * r := by
      have := mul_le_mul_of_nonneg_right hb2 (mul_nonneg hq hr)
      nlinarith
    have : 4 * q * r ≤ 4 * r := by nlinarith
    linarith
  · have : 2 * r * (1 - 2 * q) / (1 + q) ≤ 2 * r := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith

/-- `k_new` is nondecreasing in `q` on `0 ≤ q ≤ 1/100`, `r ≥ 0`: so it decreases along the
pieces. -/
theorem knew_mono_q {q q' r : ℝ} (hq : 0 ≤ q) (hqq : q ≤ q') (hq' : q' ≤ 1 / 100)
    (hr : 0 ≤ r) :
    knew q r ≤ knew q' r := by
  unfold knew
  have a1 : 0 < 1 - 3 * q := by linarith
  have a2 : 0 < 1 - 3 * q' := by linarith
  have b1 : 0 < 1 - 2 * q := by linarith
  have b2 : 0 < 1 - 2 * q' := by linarith
  have c1 : 0 < 1 + q := by linarith
  have c2 : 0 < 1 + q' := by linarith
  have h1 : (1 + 5 * q) / ((1 - 3 * q) * (1 + q)) ≤
      (1 + 5 * q') / ((1 - 3 * q') * (1 + q')) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hqq) hq,
      mul_nonneg (sub_nonneg.mpr hqq) (by linarith : (0:ℝ) ≤ q'),
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hqq) hq) (by linarith : (0:ℝ) ≤ q')]
  have h2 : q * r / ((1 - 3 * q) * (1 - 2 * q)) ≤ q' * r / ((1 - 3 * q') * (1 - 2 * q')) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (1 - 3 * q') * (1 - 2 * q') ≤ (1 - 3 * q) * (1 - 2 * q) := by nlinarith
    have hqr : q * r ≤ q' * r := mul_le_mul_of_nonneg_right hqq hr
    have hqr0 : 0 ≤ q * r := mul_nonneg hq hr
    nlinarith [mul_le_mul hqr this (by positivity) (by nlinarith : (0:ℝ) ≤ q' * r)]
  linarith

end Sarkozy.MiddleRecords
