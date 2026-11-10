module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The negative cap of the reference fold record (`cert:record:old-f-cap`)

`paper/sections/D_certificates.tex`, `cert:record:old-f-cap`, at the first piece start
`X = Q₃ = 19951586`, for the cap `k_D(X, 585) = H̄_X [1 + (e_o(X) - 1) r_X]` of
`lem:old-f-law`(e), with `r_X = 1/⌊√X⌋ = 1/4466`, `q_X = 1/X`, `H̄_X = (1 - n_X e_X)⁻¹`,
`e_X = e₀(X) = 2q/((1 - 3q)(1 - 4q))` and the constant `e_o = r_o + n_o` of
`eq:signed-constants` (`eo`, built from `Γ_A`, `c_col`, `c_g`, `D_g`, `Z`, `h₀`).

* `nX_Q3`: `⌊585/log Q₃⌋ ≤ 34`, so `n_X = 34` is admissible (`log Q₃ > 16.72`, from
  `exp 1 < 2.7182818286` and `exp x < 1/(1 - x)`);
* `eo_Q3`: `e_o ≤ 7.62384415`; `eo_factor_Q3`: `1 + (e_o - 1) r_X ≤ 1.00148318`;
* `Hbar_Q3`: `H̄_X ≤ 1.00000341`; **`kD_Q3`: `k_D(Q₃, 585) < 1.001486585`**;
* `old_f_cap_hyps_Q3`: the hypotheses `n_X e_X < 1` and `[1 + (e_o - 1) r_X] r_X < 1`;
* `eo_ge`: `e_o ≥ 56119/10000 > 1` for `0 < q ≤ 1/1000` (a remark in the proof of
  `lem:old-f-law`(e));
* at the last start `X = 2^{45}`: `nX_two_pow_45` (`n_X = 18`, from `log 2 > 0.6931471803`) and
  **`kD_two_pow_45`: `k_D(2^{45}, 585) ≤ 1.000001115`** (margin about `3·10⁻¹³`).

The square roots in `e_o` are bounded by `√(1 + x) ≤ 1 + x/2` and `√(1 - e₀) ≥ 1 - e₀`
(`eo_le_bounds`), and the result is evaluated in exact rational arithmetic. The margins are small:
`k_D(Q₃) ≈ 1.00148658487` against `1.001486585`. **Not checked:** the other 31 piece starts (their
values are not printed), and the comparisons with the F21 caps and the protection gate (data of
`cert:layer12-grid` and the weights).
-/

@[expose] public section

namespace Sarkozy.MiddleRecords

/-- `log Q₃ > 16.72`, so `⌊585/log Q₃⌋ ≤ 34`. -/
theorem log_Q3_gt : (16.72 : ℝ) < Real.log 19951586 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : Real.exp 0.072 < 1 / (1 - 0.072) :=
    Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
  have e : Real.exp 16.72 = Real.exp 1 ^ 16 * Real.exp 0.072 ^ 10 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    norm_num
  rw [e]
  have h1' : Real.exp 1 ^ 16 < 2.7182818286 ^ 16 :=
    pow_lt_pow_left₀ h1 (Real.exp_pos 1).le (by norm_num)
  have h2' : Real.exp 0.072 ^ 10 < (1 / (1 - 0.072)) ^ 10 :=
    pow_lt_pow_left₀ h2 (Real.exp_pos _).le (by norm_num)
  calc Real.exp 1 ^ 16 * Real.exp 0.072 ^ 10 < 2.7182818286 ^ 16 * (1 / (1 - 0.072)) ^ 10 :=
        mul_lt_mul h1' h2'.le (by positivity) (by positivity)
    _ < 19951586 := by norm_num

/-- **`n_X = 34` is admissible at `Q₃`**: `⌊585/log Q₃⌋ ≤ 34`. -/
theorem nX_Q3 : ⌊(585 : ℝ) / Real.log 19951586⌋ ≤ 34 := by
  have hl := log_Q3_gt
  have hpos : 0 < Real.log 19951586 := by linarith
  have : (585 : ℝ) / Real.log 19951586 < 35 := by
    rw [div_lt_iff₀ hpos]; linarith
  have h := Int.floor_le ((585 : ℝ) / Real.log 19951586)
  have : (⌊(585 : ℝ) / Real.log 19951586⌋ : ℝ) < 35 := lt_of_le_of_lt h this
  exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast this)


/-- `e₀ = 2q/((1 - 3q)(1 - 4q))`. -/
noncomputable def eZero (q : ℝ) : ℝ := 2 * q / ((1 - 3 * q) * (1 - 4 * q))

/-- `Γ_A` with the two square roots as parameters `s₁ = √(1 + q)`, `s₂ = √(1 + 4q/(1 - 4q)²)`. -/
noncomputable def gammaAS (q r s₁ s₂ : ℝ) : ℝ :=
  1 + r * s₁ / (1 - q) + 2 * (q / (1 - q) * s₂) + q * r * (1 + 4 * q) / ((1 - q) * (1 - 4 * q)) +
    2 * q * r / (1 - q) + 4 * q ^ 2 / ((1 - q) * (1 - 4 * q))

/-- `c_col` of `eq:signed-constants`, with `s₃ = √(1 - e₀)` (so `(1 - e₀)^{3/2} = (1 - e₀) s₃`). -/
noncomputable def cColS (q r s₃ : ℝ) : ℝ :=
  (56119 / 10000 * (1 + 2 * (r + q) / (1 - q) + 2 * q * (1 + r) / ((1 - q) * (1 - 2 * q))) +
      2 / ((1 - q) * (1 - 2 * q)) * (12 * r + q) + 288 * q / (1 - q)) / (1 - eZero q) +
    17 * (2 * eZero q / ((1 - eZero q) * s₃) + eZero q ^ 2 / (1 - eZero q) ^ 2)

/-- `r_o` of `eq:signed-constants`, given `Γ_A` and `c_col`. -/
noncomputable def roS (q r gA cc : ℝ) : ℝ :=
  2 / ((1 - q) * (1 - 2 * q) * (1 - eZero q)) + cc + eZero q ^ 2 / (1 - eZero q) ^ 2 / q +
    (2 * eZero q + eZero q ^ 2) / (1 - eZero q) ^ 2 / q * gA * r

/-- `e_o = r_o + n_o`, `n_o = (14/h₀)(Γ_A + r_o r) r`, of `eq:signed-constants`. -/
noncomputable def eoS (q r gA cc : ℝ) : ℝ :=
  roS q r gA cc + 14 / (1 - 14 * q) * (gA + roS q r gA cc * r) * r

/-- The constant `e_o` of `eq:signed-constants` at `(q, r)`. -/
noncomputable def eo (q r : ℝ) : ℝ :=
  eoS q r (gammaAS q r (Real.sqrt (1 + q)) (Real.sqrt (1 + 4 * q / (1 - 4 * q) ^ 2)))
    (cColS q r (Real.sqrt (1 - eZero q)))

/-- `e_o` at `(q, r)` is at most its value with the square roots replaced by the rational bounds
`√(1 + x) ≤ 1 + x/2` and `√(1 - e₀) ≥ 1 - e₀` (for `0 < q ≤ 1/1000`, `r > 0`). -/
theorem eo_le_bounds {q r : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1 / 1000) (hr0 : 0 < r) :
    eo q r ≤ eoS q r (gammaAS q r (1 + q / 2) (1 + (4 * q / (1 - 4 * q) ^ 2) / 2))
      (cColS q r (1 - eZero q)) := by
  have h1q : 0 < 1 - q := by linarith
  have h2q : 0 < 1 - 2 * q := by linarith
  have h3q : 0 < 1 - 3 * q := by linarith
  have h4q : 0 < 1 - 4 * q := by linarith
  have he0 : 0 < eZero q := by unfold eZero; positivity
  have he1 : eZero q < 1 / 100 := by
    unfold eZero
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have h1e : 0 < 1 - eZero q := by linarith
  -- the square roots
  have hs1 : Real.sqrt (1 + q) ≤ 1 + q / 2 := by
    rw [Real.sqrt_le_iff]; constructor
    · positivity
    · nlinarith [sq_nonneg (q / 2)]
  have hx : 0 ≤ 4 * q / (1 - 4 * q) ^ 2 := by positivity
  have hs2 : Real.sqrt (1 + 4 * q / (1 - 4 * q) ^ 2) ≤ 1 + (4 * q / (1 - 4 * q) ^ 2) / 2 := by
    rw [Real.sqrt_le_iff]; constructor
    · positivity
    · nlinarith [sq_nonneg (4 * q / (1 - 4 * q) ^ 2 / 2)]
  have hs3 : 1 - eZero q ≤ Real.sqrt (1 - eZero q) := by
    rw [Real.le_sqrt h1e.le h1e.le]
    nlinarith
  -- monotonicity of the three layers
  have hgA : gammaAS q r (Real.sqrt (1 + q)) (Real.sqrt (1 + 4 * q / (1 - 4 * q) ^ 2)) ≤
      gammaAS q r (1 + q / 2) (1 + (4 * q / (1 - 4 * q) ^ 2) / 2) := by
    unfold gammaAS
    have t1 : r * Real.sqrt (1 + q) / (1 - q) ≤ r * (1 + q / 2) / (1 - q) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs1 hr0.le) h1q.le
    have t2 : q / (1 - q) * Real.sqrt (1 + 4 * q / (1 - 4 * q) ^ 2) ≤
        q / (1 - q) * (1 + (4 * q / (1 - 4 * q) ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left hs2 (by positivity)
    linarith
  have hcc : cColS q r (Real.sqrt (1 - eZero q)) ≤ cColS q r (1 - eZero q) := by
    unfold cColS
    have t : 2 * eZero q / ((1 - eZero q) * Real.sqrt (1 - eZero q)) ≤
        2 * eZero q / ((1 - eZero q) * (1 - eZero q)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hs3 h1e.le)
    linarith
  have hmono : ∀ gA gA' cc cc' : ℝ, gA ≤ gA' → cc ≤ cc' →
      eoS q r gA cc ≤ eoS q r gA' cc' := by
    intro gA gA' cc cc' hg hc
    have hcoef : 0 ≤ (2 * eZero q + eZero q ^ 2) / (1 - eZero q) ^ 2 / q := by positivity
    have hro : roS q r gA cc ≤ roS q r gA' cc' := by
      unfold roS
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hcoef) hr0.le
      linarith
    unfold eoS
    have h14 : 0 ≤ 14 / (1 - 14 * q) := by
      have : 0 < 1 - 14 * q := by linarith
      positivity
    have : gA + roS q r gA cc * r ≤ gA' + roS q r gA' cc' * r := by
      have := mul_le_mul_of_nonneg_right hro hr0.le
      linarith
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this h14) hr0.le
    linarith
  exact hmono _ _ _ _ hgA hcc

/-- The rational bound at `q = 1/Q₃`, `r = 1/4466`. -/
theorem eo_le_rational :
    eo (1 / 19951586) (1 / 4466) ≤
      eoS (1 / 19951586) (1 / 4466)
        (gammaAS (1 / 19951586) (1 / 4466) (1 + (1 / 19951586) / 2)
          (1 + (4 * (1 / 19951586) / (1 - 4 * (1 / 19951586)) ^ 2) / 2))
        (cColS (1 / 19951586) (1 / 4466) (1 - eZero (1 / 19951586))) :=
  eo_le_bounds (by norm_num) (by norm_num) (by norm_num)

/-- **`cert:record:old-f-cap` at `X = Q₃`**: `e_o ≤ 7.62384415` at `(q_X, r_X) = (1/Q₃, 1/4466)`. -/
theorem eo_Q3 : eo (1 / 19951586) (1 / 4466) ≤ 7.62384415 := by
  refine eo_le_rational.trans ?_
  unfold eoS roS gammaAS cColS eZero
  norm_num

/-- **`cert:record:old-f-cap` at `X = Q₃`**: `1 + (e_o - 1) r_X ≤ 1.00148318`. -/
theorem eo_factor_Q3 : 1 + (eo (1 / 19951586) (1 / 4466) - 1) * (1 / 4466) ≤ 1.00148318 := by
  have := eo_Q3
  nlinarith

/-- **`cert:record:old-f-cap` at `X = Q₃`**: `H̄_X = (1 - n_X e_X)⁻¹ ≤ 1.00000341` with
`n_X = 34`. -/
theorem Hbar_Q3 : 1 / (1 - 34 * eZero (1 / 19951586)) ≤ 1.00000341 := by
  unfold eZero
  norm_num

/-- **`cert:record:old-f-cap` at `X = Q₃`**:
`k_D(Q₃, 585) = H̄_X [1 + (e_o - 1) r_X] < 1.001486585`, with `n_X = 34` (admissible by `nX_Q3`). -/
theorem kD_Q3 :
    1 / (1 - 34 * eZero (1 / 19951586)) * (1 + (eo (1 / 19951586) (1 / 4466) - 1) * (1 / 4466)) <
      1.001486585 := by
  have hH : 0 < 1 / (1 - 34 * eZero (1 / 19951586)) := by unfold eZero; norm_num
  have h := eo_le_rational
  calc 1 / (1 - 34 * eZero (1 / 19951586)) * (1 + (eo (1 / 19951586) (1 / 4466) - 1) * (1 / 4466))
      ≤ 1 / (1 - 34 * eZero (1 / 19951586)) *
        (1 + (eoS (1 / 19951586) (1 / 4466)
          (gammaAS (1 / 19951586) (1 / 4466) (1 + (1 / 19951586) / 2)
            (1 + (4 * (1 / 19951586) / (1 - 4 * (1 / 19951586)) ^ 2) / 2))
          (cColS (1 / 19951586) (1 / 4466) (1 - eZero (1 / 19951586))) - 1) * (1 / 4466)) := by
        apply mul_le_mul_of_nonneg_left _ hH.le
        nlinarith
    _ < 1.001486585 := by
        unfold eoS roS gammaAS cColS eZero
        norm_num

/-- **The hypotheses of `lem:old-f-law`(e) at `Q₃`**: `n_X e_X < 1` and
`[1 + (e_o - 1) r_X] r_X < 1`. -/
theorem old_f_cap_hyps_Q3 :
    34 * eZero (1 / 19951586) < 1 ∧
      (1 + (eo (1 / 19951586) (1 / 4466) - 1) * (1 / 4466)) * (1 / 4466) < 1 := by
  constructor
  · unfold eZero; norm_num
  · have := eo_factor_Q3
    nlinarith

/-- **`e_o ≥ 56119/10000 > 1`** (used in the proof of `lem:old-f-law`(e)), for `0 < q ≤ 1/1000`,
`r ≥ 0`. -/
theorem eo_ge {q r : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1 / 1000) (hr0 : 0 ≤ r) :
    56119 / 10000 ≤ eo q r := by
  have h1q : 0 < 1 - q := by linarith
  have h2q : 0 < 1 - 2 * q := by linarith
  have h3q : 0 < 1 - 3 * q := by linarith
  have h4q : 0 < 1 - 4 * q := by linarith
  have h14 : 0 < 1 - 14 * q := by linarith
  have he0 : 0 < eZero q := by unfold eZero; positivity
  have he1 : eZero q < 1 / 100 := by
    unfold eZero
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have h1e : 0 < 1 - eZero q := by linarith
  have hs3 : 0 < Real.sqrt (1 - eZero q) := Real.sqrt_pos.mpr h1e
  set gA := gammaAS q r (Real.sqrt (1 + q)) (Real.sqrt (1 + 4 * q / (1 - 4 * q) ^ 2)) with hgA
  have hgA0 : 0 ≤ gA := by rw [hgA]; unfold gammaAS; positivity
  set cc := cColS q r (Real.sqrt (1 - eZero q)) with hcc
  -- `c_col ≥ c^ν_col/(1 - e₀) ≥ (56119/10000) Γ₅ ≥ 56119/10000`
  have hΓ5 : 1 ≤ 1 + 2 * (r + q) / (1 - q) + 2 * q * (1 + r) / ((1 - q) * (1 - 2 * q)) := by
    have : 0 ≤ 2 * (r + q) / (1 - q) := by positivity
    have : 0 ≤ 2 * q * (1 + r) / ((1 - q) * (1 - 2 * q)) := by positivity
    linarith
  have hnu : 56119 / 10000 ≤ 56119 / 10000 * (1 + 2 * (r + q) / (1 - q) +
      2 * q * (1 + r) / ((1 - q) * (1 - 2 * q))) + 2 / ((1 - q) * (1 - 2 * q)) * (12 * r + q) +
      288 * q / (1 - q) := by
    have : 0 ≤ 2 / ((1 - q) * (1 - 2 * q)) * (12 * r + q) := by positivity
    have : 0 ≤ 288 * q / (1 - q) := by positivity
    nlinarith
  have hcc0 : 56119 / 10000 ≤ cc := by
    rw [hcc]
    unfold cColS
    set N := 56119 / 10000 * (1 + 2 * (r + q) / (1 - q) +
      2 * q * (1 + r) / ((1 - q) * (1 - 2 * q))) +
      2 / ((1 - q) * (1 - 2 * q)) * (12 * r + q) + 288 * q / (1 - q) with hN
    have hdiv : N ≤ N / (1 - eZero q) := by
      rw [le_div_iff₀ h1e]
      have : 0 ≤ N := by linarith
      nlinarith
    have : 0 ≤ 17 * (2 * eZero q / ((1 - eZero q) * Real.sqrt (1 - eZero q)) +
        eZero q ^ 2 / (1 - eZero q) ^ 2) := by positivity
    linarith
  unfold eo
  rw [← hgA, ← hcc]
  unfold eoS roS
  have : 0 ≤ 2 / ((1 - q) * (1 - 2 * q) * (1 - eZero q)) := by positivity
  have : 0 ≤ eZero q ^ 2 / (1 - eZero q) ^ 2 / q := by positivity
  have : 0 ≤ (2 * eZero q + eZero q ^ 2) / (1 - eZero q) ^ 2 / q * gA * r := by positivity
  have hro : 0 ≤ 2 / ((1 - q) * (1 - 2 * q) * (1 - eZero q)) + cc +
      eZero q ^ 2 / (1 - eZero q) ^ 2 / q +
      (2 * eZero q + eZero q ^ 2) / (1 - eZero q) ^ 2 / q * gA * r := by linarith
  have : 0 ≤ 14 / (1 - 14 * q) * (gA + (2 / ((1 - q) * (1 - 2 * q) * (1 - eZero q)) + cc +
      eZero q ^ 2 / (1 - eZero q) ^ 2 / q +
      (2 * eZero q + eZero q ^ 2) / (1 - eZero q) ^ 2 / q * gA * r) * r) * r := by positivity
  linarith

/-! ## The last piece start `X = 2^{45}` -/

/-- **`n_X = 18` is admissible at `2^{45}`**: `⌊585/log 2^{45}⌋ ≤ 18`. -/
theorem nX_two_pow_45 : ⌊(585 : ℝ) / Real.log 35184372088832⌋ ≤ 18 := by
  have hlog : Real.log 35184372088832 = 45 * Real.log 2 := by
    rw [show (35184372088832 : ℝ) = 2 ^ 45 by norm_num, Real.log_pow]
    norm_num
  have h2 := Real.log_two_gt_d9
  have hpos : 0 < Real.log 35184372088832 := by rw [hlog]; linarith
  have : (585 : ℝ) / Real.log 35184372088832 < 19 := by
    rw [div_lt_iff₀ hpos, hlog]; linarith
  have h := Int.floor_le ((585 : ℝ) / Real.log 35184372088832)
  have : (⌊(585 : ℝ) / Real.log 35184372088832⌋ : ℝ) < 19 := lt_of_le_of_lt h this
  exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast this)

/-- **`cert:record:old-f-cap` at `X = 2^{45}`**: `k_D(2^{45}, 585) ≤ 1.000001115`, with
`n_X = 18` and `r_X = 1/⌊√(2^{45})⌋ = 1/5931641`. The margin is about `3·10⁻¹³`. -/
theorem kD_two_pow_45 :
    1 / (1 - 18 * eZero (1 / 35184372088832)) *
        (1 + (eo (1 / 35184372088832) (1 / 5931641) - 1) * (1 / 5931641)) ≤ 1.000001115 := by
  have hH : 0 < 1 / (1 - 18 * eZero (1 / 35184372088832)) := by unfold eZero; norm_num
  have h := eo_le_bounds (q := 1 / 35184372088832) (r := 1 / 5931641) (by norm_num) (by norm_num)
    (by norm_num)
  calc 1 / (1 - 18 * eZero (1 / 35184372088832)) *
        (1 + (eo (1 / 35184372088832) (1 / 5931641) - 1) * (1 / 5931641))
      ≤ 1 / (1 - 18 * eZero (1 / 35184372088832)) *
        (1 + (eoS (1 / 35184372088832) (1 / 5931641)
          (gammaAS (1 / 35184372088832) (1 / 5931641) (1 + (1 / 35184372088832) / 2)
            (1 + (4 * (1 / 35184372088832) / (1 - 4 * (1 / 35184372088832)) ^ 2) / 2))
          (cColS (1 / 35184372088832) (1 / 5931641) (1 - eZero (1 / 35184372088832))) - 1) *
            (1 / 5931641)) := by
        apply mul_le_mul_of_nonneg_left _ hH.le
        nlinarith
    _ ≤ 1.000001115 := by
        unfold eoS roS gammaAS cColS eZero
        norm_num

end Sarkozy.MiddleRecords
