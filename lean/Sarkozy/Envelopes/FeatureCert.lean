module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# The feature constants and the Perron gate (`cert:envelopes`(a), `lem:oct24:feature-block`)

`paper/sections/23_envelopes.tex`, `lem:oct24:feature-block` (the table of the four fold constants,
`eq:feature-perron`, `eq:oct24:feature-constants`) and `cert:envelopes`(a), checked in exact
rational arithmetic in the kernel (`norm_num`), with no floating point.

**The constants.** With `q = 1/b`, `r = b^{-1/2}`:
`ϱ₀₂ = r√(1+q)/(1-q)`, `ϱ₀₁ = q/(1-q) · (1 + 4q/(1-4q)²)^{1/2}`,
`ϱ₀₃ = q/(1-3q) + 2q²/((1-3q)(1-6q)) + 2qr/((1-6q)(1-2q))`, `ϱ₃₄ = (r + q + 4q²/(1-4q))/(1-6q)`.

**Proved.**
* `rho_mono`: the four constants are nondecreasing in `(q, r)` (for `q ≤ 1/8`);
* `feature_table`: for every `b ≥ Q₃ = 19951586`, the constants are at most the table values
  `2.23877949420725·10⁻⁴`, `5.01213362368300·10⁻⁸`, `5.01437833890212·10⁻⁸`,
  `2.23928121269334·10⁻⁴`, and `ϱ₀₁ ≤ ρ_pair = 50121336236829934606443·10⁻³⁰`;
* `feature_perron_gate`: for every `b ≥ Q₃`, `λ = Γ_F - 1` with
  `Γ_F = 500111979555137707696357560603/(5·10²⁹)` satisfies `λ > ϱ₃₄` and `eq:feature-perron`;
* `feature_constants_numbers`: `Γ_F < 1.000223959111`, `η_pair < 1.0024267248·10⁻⁷`,
  `ρ_pair < 5.0121336237·10⁻⁸`, `Γ_E = 1 + 1/(Q₃ - 1)`;
* `step3_gates`: the gates `ϱ_{0|12} < 1/2` and `2(ϱ̃₀₃/q) ϱ_{0|12} < 1` of Step 3, for every
  `q ≤ 2⁻²⁴`, `r ≤ 2⁻¹²` (every middle prime exceeds `Q₃ > 2²⁴`).

**Finding.** The Perron gate is extremely tight: at the exact constants of `b = Q₃` its value is
about `9.3·10⁻³⁰`, while at the fifteen-digit table entries it is negative (about `-2.6·10⁻¹⁸`). So
`Γ_F` is *not* certified by the displayed (rounded) table, contrary to the reading of "the rational
end of a bisection for `eq:feature-perron` with the rounded entries"; it is certified with entries
accurate to about `10⁻³³`, as here (rational square-root bounds with 45 decimals). The value of
`Γ_F` is correct.

What is not done: part (a) of `lem:oct24:feature-block` (the correlation bounds in the actual
laws, Steps 1–4 of its proof); the frame reduction of part (b) is in `FeatureFrame`;
the gate is the scalar input of that reduction.
-/

namespace Sarkozy.Envelopes

/-- `ϱ₀₂(q, r) = r√(1+q)/(1-q)` (`lem:oct24:feature-block`). -/
noncomputable def rho02 (q r : ℝ) : ℝ := r * Real.sqrt (1 + q) / (1 - q)

/-- `ϱ₀₁(q) = q/(1-q) · (1 + 4q/(1-4q)²)^{1/2}` (`lem:oct24:feature-block`). -/
noncomputable def rho01 (q : ℝ) : ℝ := q / (1 - q) * Real.sqrt (1 + 4 * q / (1 - 4 * q) ^ 2)

/-- `ϱ₀₃(q, r)` (`lem:oct24:feature-block`). -/
noncomputable def rho03 (q r : ℝ) : ℝ :=
  q / (1 - 3 * q) + 2 * q ^ 2 / ((1 - 3 * q) * (1 - 6 * q)) +
    2 * q * r / ((1 - 6 * q) * (1 - 2 * q))

/-- `ϱ₃₄(q, r) = (r + q + 4q²/(1-4q))/(1-6q)` (`lem:oct24:feature-block`). -/
noncomputable def rho34 (q r : ℝ) : ℝ := (r + q + 4 * q ^ 2 / (1 - 4 * q)) / (1 - 6 * q)

/-- The left side of `eq:feature-perron`, `λ - ϱ₀₂ - ϱ₀₃²/(λ - ϱ₃₄) - 2ϱ₀₁²/λ`. -/
noncomputable def perronGate (lam a02 a01 a03 a34 : ℝ) : ℝ :=
  lam - a02 - a03 ^ 2 / (lam - a34) - 2 * a01 ^ 2 / lam

/-- **The constants are nondecreasing in `(q, r)`** (the monotone majorants of Part II, as
used in `lem:oct24:feature-block`). -/
theorem rho_mono {q q₀ r r₀ : ℝ} (hq : 0 ≤ q) (hqq : q ≤ q₀) (hq₀ : q₀ ≤ 1 / 8) (hr : 0 ≤ r)
    (hrr : r ≤ r₀) :
    rho02 q r ≤ rho02 q₀ r₀ ∧ rho01 q ≤ rho01 q₀ ∧ rho03 q r ≤ rho03 q₀ r₀ ∧
      rho34 q r ≤ rho34 q₀ r₀ := by
  have h1 : 0 < 1 - q₀ := by linarith
  have h3 : 0 < 1 - 3 * q₀ := by linarith
  have h4 : 0 < 1 - 4 * q₀ := by linarith
  have h6 : 0 < 1 - 6 * q₀ := by linarith
  have h2 : 0 < 1 - 2 * q₀ := by linarith
  have hr₀ : 0 ≤ r₀ := hr.trans hrr
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold rho02
    have hs : Real.sqrt (1 + q) ≤ Real.sqrt (1 + q₀) := Real.sqrt_le_sqrt (by linarith)
    have : r * Real.sqrt (1 + q) ≤ r₀ * Real.sqrt (1 + q₀) :=
      mul_le_mul hrr hs (Real.sqrt_nonneg _) hr₀
    exact div_le_div₀ (by positivity) this (by linarith) (by linarith)
  · unfold rho01
    have hA : q / (1 - q) ≤ q₀ / (1 - q₀) := div_le_div₀ (by linarith) hqq h1 (by linarith)
    have hB : 4 * q / (1 - 4 * q) ^ 2 ≤ 4 * q₀ / (1 - 4 * q₀) ^ 2 := by
      have : (1 - 4 * q₀) ^ 2 ≤ (1 - 4 * q) ^ 2 := by
        have : 1 - 4 * q₀ ≤ 1 - 4 * q := by linarith
        exact pow_le_pow_left₀ h4.le this 2
      exact div_le_div₀ (by linarith) (by linarith) (by positivity) this
    have hs : Real.sqrt (1 + 4 * q / (1 - 4 * q) ^ 2) ≤
        Real.sqrt (1 + 4 * q₀ / (1 - 4 * q₀) ^ 2) := Real.sqrt_le_sqrt (by linarith)
    exact mul_le_mul hA hs (Real.sqrt_nonneg _) (div_nonneg (by linarith) h1.le)
  · unfold rho03
    have a1 : q / (1 - 3 * q) ≤ q₀ / (1 - 3 * q₀) :=
      div_le_div₀ (by linarith) hqq h3 (by linarith)
    have a2 : 2 * q ^ 2 / ((1 - 3 * q) * (1 - 6 * q)) ≤
        2 * q₀ ^ 2 / ((1 - 3 * q₀) * (1 - 6 * q₀)) := by
      have hn : 2 * q ^ 2 ≤ 2 * q₀ ^ 2 := by nlinarith
      have hd : (1 - 3 * q₀) * (1 - 6 * q₀) ≤ (1 - 3 * q) * (1 - 6 * q) :=
        mul_le_mul (by linarith) (by linarith) h6.le (by linarith)
      exact div_le_div₀ (by positivity) hn (mul_pos h3 h6) hd
    have a3 : 2 * q * r / ((1 - 6 * q) * (1 - 2 * q)) ≤
        2 * q₀ * r₀ / ((1 - 6 * q₀) * (1 - 2 * q₀)) := by
      have hn : 2 * q * r ≤ 2 * q₀ * r₀ := by
        have := mul_le_mul hqq hrr hr (hq.trans hqq)
        nlinarith
      have hd : (1 - 6 * q₀) * (1 - 2 * q₀) ≤ (1 - 6 * q) * (1 - 2 * q) :=
        mul_le_mul (by linarith) (by linarith) h2.le (by linarith)
      exact div_le_div₀ (mul_nonneg (mul_nonneg (by norm_num) (hq.trans hqq)) hr₀) hn
        (mul_pos h6 h2) hd
    linarith
  · unfold rho34
    have a1 : 4 * q ^ 2 / (1 - 4 * q) ≤ 4 * q₀ ^ 2 / (1 - 4 * q₀) :=
      div_le_div₀ (by positivity) (by nlinarith) h4 (by linarith)
    have hn : r + q + 4 * q ^ 2 / (1 - 4 * q) ≤ r₀ + q₀ + 4 * q₀ ^ 2 / (1 - 4 * q₀) := by
      linarith
    have hn0 : 0 ≤ r₀ + q₀ + 4 * q₀ ^ 2 / (1 - 4 * q₀) := by
      have : 0 ≤ 4 * q₀ ^ 2 / (1 - 4 * q₀) := div_nonneg (by positivity) h4.le
      linarith [hq.trans hqq]
    exact div_le_div₀ hn0 hn h6 (by linarith)

/-- The gate is antitone in the constants: if `a ≤ A` entrywise (`a ≥ 0`) and `λ > A₃₄`, then the
gate at `a` is at least the gate at `A`. -/
theorem perronGate_anti {lam a02 a01 a03 a34 A02 A01 A03 A34 : ℝ} (hlam : A34 < lam)
    (h02 : a02 ≤ A02) (h01 : a01 ≤ A01) (h03 : a03 ≤ A03) (h34 : a34 ≤ A34) (h01' : 0 ≤ a01)
    (h03' : 0 ≤ a03) (hlam0 : 0 < lam) :
    perronGate lam A02 A01 A03 A34 ≤ perronGate lam a02 a01 a03 a34 := by
  unfold perronGate
  have hd : 0 < lam - A34 := by linarith
  have k1 : a03 ^ 2 / (lam - a34) ≤ A03 ^ 2 / (lam - A34) :=
    div_le_div₀ (by positivity) (pow_le_pow_left₀ h03' h03 2) hd (by linarith)
  have k2 : 2 * a01 ^ 2 / lam ≤ 2 * A01 ^ 2 / lam := by
    have : a01 ^ 2 ≤ A01 ^ 2 := pow_le_pow_left₀ h01' h01 2
    exact div_le_div_of_nonneg_right (by linarith) hlam0.le
  linarith

/-- The rational square-root bounds at `Q₃` (45 decimals). -/
def rBar : ℚ := 223877932589134434375004044382138744234436 / 10 ^ 45
/-- An upper bound for `√(1 + 1/Q₃)`. -/
def sBar1 : ℚ := 1000000025060664036174070044411093281354254916 / 10 ^ 45
/-- An upper bound for `√(1 + 4q/(1-4q)²)` at `q = 1/Q₃`. -/
def sBar2 : ℚ := 1000000100242692570844875763835464977550311367 / 10 ^ 45

/-- `Γ_F` of `eq:oct24:feature-constants`. -/
def gammaF : ℚ := 500111979555137707696357560603 / (5 * 10 ^ 29)
/-- `ρ_pair` of `lem:oct24:feature-block`. -/
def rhoPair : ℚ := 50121336236829934606443 / 10 ^ 30

theorem sqrt_le_of_sq_le {x s : ℝ} (hs : 0 ≤ s) (h : x ≤ s ^ 2) : Real.sqrt x ≤ s := by
  rw [Real.sqrt_le_left hs]; exact h

/-- The constants at every `b ≥ Q₃` are bounded by their rational majorants at `Q₃`. -/
theorem rho_le_majorants {b : ℝ} (hb : 19951586 ≤ b) :
    rho02 (1 / b) (1 / Real.sqrt b) ≤ (rBar : ℝ) * sBar1 / (1 - 1 / 19951586) ∧
    rho01 (1 / b) ≤ (1 / 19951586) / (1 - 1 / 19951586) * (sBar2 : ℝ) ∧
    rho03 (1 / b) (1 / Real.sqrt b) ≤ rho03 (1 / 19951586) rBar ∧
    rho34 (1 / b) (1 / Real.sqrt b) ≤ rho34 (1 / 19951586) rBar := by
  have hb0 : 0 < b := by linarith
  have hq : 1 / b ≤ 1 / 19951586 := one_div_le_one_div_of_le (by norm_num) hb
  have hq0 : 0 ≤ 1 / b := by positivity
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  have hr : 1 / Real.sqrt b ≤ (rBar : ℝ) := by
    rw [div_le_iff₀ hsb]
    have hb' : (1 : ℝ) ≤ ((rBar : ℝ) * Real.sqrt b) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hb0.le]
      have : (1 : ℝ) ≤ (rBar : ℝ) ^ 2 * 19951586 := by
        simp only [rBar]; push_cast; norm_num
      nlinarith [sq_nonneg (rBar : ℝ)]
    have hpos : 0 ≤ (rBar : ℝ) * Real.sqrt b := by
      have : (0 : ℝ) ≤ rBar := by simp only [rBar]; push_cast; norm_num
      positivity
    nlinarith
  have hr0 : 0 ≤ 1 / Real.sqrt b := by positivity
  obtain ⟨m02, m01, m03, m34⟩ := rho_mono hq0 hq (by norm_num) hr0 hr
  refine ⟨m02.trans ?_, m01.trans ?_, m03, m34⟩
  · unfold rho02
    have hs : Real.sqrt (1 + 1 / 19951586) ≤ (sBar1 : ℝ) :=
      sqrt_le_of_sq_le (by simp only [sBar1]; push_cast; norm_num)
        (by simp only [sBar1]; push_cast; norm_num)
    have hrb : (0 : ℝ) ≤ rBar := by simp only [rBar]; push_cast; norm_num
    have := mul_le_mul_of_nonneg_left hs hrb
    exact div_le_div_of_nonneg_right this (by norm_num)
  · unfold rho01
    have hs : Real.sqrt (1 + 4 * (1 / 19951586) / (1 - 4 * (1 / 19951586)) ^ 2) ≤ (sBar2 : ℝ) :=
      sqrt_le_of_sq_le (by simp only [sBar2]; push_cast; norm_num)
        (by simp only [sBar2]; push_cast; norm_num)
    exact mul_le_mul_of_nonneg_left hs (by norm_num)

/-- **`cert:envelopes`(a), the table of `lem:oct24:feature-block`.** For every `b ≥ Q₃`, with
`q = 1/b` and `r = b^{-1/2}`, the four fold constants are at most the table values, and
`ϱ₀₁ ≤ ρ_pair`. -/
theorem feature_table {b : ℝ} (hb : 19951586 ≤ b) :
    rho02 (1 / b) (1 / Real.sqrt b) ≤ 2.23877949420725e-4 ∧
    rho01 (1 / b) ≤ 5.01213362368300e-8 ∧
    rho03 (1 / b) (1 / Real.sqrt b) ≤ 5.01437833890212e-8 ∧
    rho34 (1 / b) (1 / Real.sqrt b) ≤ 2.23928121269334e-4 ∧
    rho01 (1 / b) ≤ (rhoPair : ℝ) := by
  obtain ⟨h02, h01, h03, h34⟩ := rho_le_majorants hb
  refine ⟨h02.trans ?_, h01.trans ?_, h03.trans ?_, h34.trans ?_, h01.trans ?_⟩
  · simp only [rBar, sBar1]; push_cast; norm_num
  · simp only [sBar2]; push_cast; norm_num
  · simp only [rho03, rBar]; push_cast; norm_num
  · simp only [rho34, rBar]; push_cast; norm_num
  · simp only [sBar2, rhoPair]; push_cast; norm_num

/-- **`cert:envelopes`(a), the Perron gate `eq:feature-perron`.** For every `b ≥ Q₃`,
`λ = Γ_F - 1` satisfies `λ > ϱ₃₄` and
`λ - ϱ₀₂ - ϱ₀₃²/(λ - ϱ₃₄) - 2ϱ₀₁²/λ ≥ 0`; hence (by `lem:oct24:feature-block`(b)) the fold frame
bound `Γ_F` holds at every middle block, given the correlation bounds of part (a). -/
theorem feature_perron_gate {b : ℝ} (hb : 19951586 ≤ b) :
    rho34 (1 / b) (1 / Real.sqrt b) < (gammaF : ℝ) - 1 ∧
      0 ≤ perronGate ((gammaF : ℝ) - 1) (rho02 (1 / b) (1 / Real.sqrt b)) (rho01 (1 / b))
        (rho03 (1 / b) (1 / Real.sqrt b)) (rho34 (1 / b) (1 / Real.sqrt b)) := by
  obtain ⟨h02, h01, h03, h34⟩ := rho_le_majorants hb
  have hb0 : 0 < b := by linarith
  have hq0 : 0 ≤ 1 / b := by positivity
  have hr0 : 0 ≤ 1 / Real.sqrt b := by positivity
  have hq1 : 1 / b ≤ 1 / 8 := by
    rw [div_le_div_iff₀ hb0 (by norm_num)]; linarith
  have h01' : 0 ≤ rho01 (1 / b) := by
    unfold rho01
    exact mul_nonneg (div_nonneg hq0 (by linarith)) (Real.sqrt_nonneg _)
  have h03' : 0 ≤ rho03 (1 / b) (1 / Real.sqrt b) := by
    unfold rho03
    have a : 0 < 1 - 3 * (1 / b) := by linarith
    have c : 0 < 1 - 6 * (1 / b) := by linarith
    have d : 0 < 1 - 2 * (1 / b) := by linarith
    positivity
  have hM34 : rho34 (1 / 19951586) (rBar : ℝ) < (gammaF : ℝ) - 1 := by
    simp only [rho34, rBar, gammaF]; push_cast; norm_num
  have hgate : 0 ≤ perronGate ((gammaF : ℝ) - 1) ((rBar : ℝ) * sBar1 / (1 - 1 / 19951586))
      ((1 / 19951586) / (1 - 1 / 19951586) * (sBar2 : ℝ)) (rho03 (1 / 19951586) rBar)
      (rho34 (1 / 19951586) rBar) := by
    simp only [perronGate, rho03, rho34, rBar, sBar1, sBar2, gammaF]
    push_cast
    norm_num
  refine ⟨h34.trans_lt hM34, hgate.trans ?_⟩
  exact perronGate_anti hM34 h02 h01 h03 h34 h01' h03' (by simp only [gammaF]; norm_num)

/-- **`eq:oct24:feature-constants`, the numbers.** `Γ_F < 1.000223959111`,
`ρ_pair < 5.0121336237·10⁻⁸`, `η_pair = 2ρ_pair/(1 - ρ_pair²) < 1.0024267248·10⁻⁷`, and
`Γ_E = 19951586/19951585 = 1 + 1/(Q₃ - 1)`. -/
theorem feature_constants_numbers :
    gammaF < 1.000223959111 ∧ rhoPair < 5.0121336237e-8 ∧
      2 * rhoPair / (1 - rhoPair ^ 2) < 1.0024267248e-7 ∧
      (19951586 / 19951585 : ℚ) = 1 + 1 / (19951586 - 1) := by
  simp only [gammaF, rhoPair]
  norm_num

/-! ### The gates of Step 3 -/

/-- `e₀ = 2q/((1-3q)(1-4q))` (the old fold law, part (a)). -/
noncomputable def e0 (q : ℝ) : ℝ := 2 * q / ((1 - 3 * q) * (1 - 4 * q))

/-- `ϱ_{0|12} = [(r√(1+q) + 2q)/(1-3q) + e₀]/√(1 - e₀)` (proof of `lem:oct24:feature-block`). -/
noncomputable def rho0bar12 (q r : ℝ) : ℝ :=
  ((r * Real.sqrt (1 + q) + 2 * q) / (1 - 3 * q) + e0 q) / Real.sqrt (1 - e0 q)

/-- `ϱ̃₀₃/q = [2(1+ϱ)/(1-3q) + e₀/q]/√(1 - e₀)`, `ϱ = r√(1+q)/(1-q)`, `e₀/q = 2/((1-3q)(1-4q))`. -/
noncomputable def rho03tq (q r : ℝ) : ℝ :=
  (2 * (1 + r * Real.sqrt (1 + q) / (1 - q)) / (1 - 3 * q) + 2 / ((1 - 3 * q) * (1 - 4 * q))) /
    Real.sqrt (1 - e0 q)

/-- **`cert:envelopes`(a), the gates of Step 3** of `lem:oct24:feature-block`: for every
`0 ≤ q ≤ 2⁻²⁴` and `0 ≤ r ≤ 2⁻¹²` (every middle prime exceeds `Q₃ > 2²⁴`),
`ϱ_{0|12} < 1/2` and `2(ϱ̃₀₃/q) ϱ_{0|12} < 1`. -/
theorem step3_gates {q r : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1 / 2 ^ 24) (hr : 0 ≤ r)
    (hr1 : r ≤ 1 / 2 ^ 12) : rho0bar12 q r < 1 / 2 ∧ 2 * rho03tq q r * rho0bar12 q r < 1 := by
  have hq' : q ≤ 1 / 1000000 := hq1.trans (by norm_num)
  have h3 : 1 / 2 ≤ 1 - 3 * q := by linarith
  have h4 : 1 / 2 ≤ 1 - 4 * q := by linarith
  have h1 : 1 / 2 ≤ 1 - q := by linarith
  have hsq : Real.sqrt (1 + q) ≤ 2 := sqrt_le_of_sq_le (by norm_num) (by nlinarith)
  have he0 : 0 ≤ e0 q := by unfold e0; positivity
  have hprod : 1 / 4 ≤ (1 - 3 * q) * (1 - 4 * q) := by nlinarith
  have he1 : e0 q ≤ 8 * q := by
    unfold e0
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hprod (by linarith : (0 : ℝ) ≤ 8 * q)]
  have hsq2 : 1 / 2 ≤ Real.sqrt (1 - e0 q) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    nlinarith
  have hsq2p : 0 < Real.sqrt (1 - e0 q) := by linarith
  -- `ϱ_{0|12} ≤ 2(2(r·2 + 2q) + 8q) ≤ 1/100`
  have hnum : (r * Real.sqrt (1 + q) + 2 * q) / (1 - 3 * q) + e0 q ≤ 1 / 200 := by
    have a : r * Real.sqrt (1 + q) ≤ 2 * r := by nlinarith [Real.sqrt_nonneg (1 + q)]
    have b : (r * Real.sqrt (1 + q) + 2 * q) / (1 - 3 * q) ≤ 2 * (2 * r + 2 * q) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [Real.sqrt_nonneg (1 + q)]
    have c : 2 * (2 * r + 2 * q) ≤ 1 / 400 := by
      have : r ≤ 1 / 4096 := by norm_num at hr1; linarith
      linarith
    linarith
  have hnum0 : 0 ≤ (r * Real.sqrt (1 + q) + 2 * q) / (1 - 3 * q) + e0 q := by
    have : 0 ≤ (r * Real.sqrt (1 + q) + 2 * q) / (1 - 3 * q) := by
      apply div_nonneg _ (by linarith); positivity
    linarith
  have hρ : rho0bar12 q r ≤ 1 / 100 := by
    unfold rho0bar12
    rw [div_le_iff₀ hsq2p]
    nlinarith
  have hρ0 : 0 ≤ rho0bar12 q r := by unfold rho0bar12; positivity
  have ht : rho03tq q r ≤ 40 := by
    unfold rho03tq
    rw [div_le_iff₀ hsq2p]
    have a : r * Real.sqrt (1 + q) / (1 - q) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]
      have : r ≤ 1 / 4096 := by norm_num at hr1; linarith
      nlinarith [Real.sqrt_nonneg (1 + q)]
    have b : 2 * (1 + r * Real.sqrt (1 + q) / (1 - q)) / (1 - 3 * q) ≤ 8 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have c : 2 / ((1 - 3 * q) * (1 - 4 * q)) ≤ 8 := by
      rw [div_le_iff₀ (by nlinarith)]; nlinarith
    nlinarith
  refine ⟨by linarith, ?_⟩
  have ht0 : 0 ≤ rho03tq q r := by
    unfold rho03tq
    have a : 0 ≤ r * Real.sqrt (1 + q) / (1 - q) := by
      apply div_nonneg _ (by linarith); positivity
    have b : 0 < (1 - 3 * q) * (1 - 4 * q) := by nlinarith
    positivity
  nlinarith

end Sarkozy.Envelopes
