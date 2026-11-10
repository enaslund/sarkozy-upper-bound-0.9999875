module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The matching coefficients (`lem:record:exact-marginal-e`, `lem:oct24:matching-star`)

`paper/sections/21_middle_records.tex`, `subsec:record:e_side`: the arithmetic of
`lem:record:exact-marginal-e` and `lem:oct24:matching-star`, and the constants of
`lem:record:e-law`(c), (d) and `lem:record:e-orthogonal`(b), (c) that they use.

**The constants at one prime**, as real functions of `(q, r)` (at a prime `p`, `q = 1/p`,
`r = p^{-1/2}`; `√` is `Real.sqrt`): `Zq` (`Z = (1 - q)(1 - 2q)`), `frakS` (`𝔰_p`,
`lem:record:e-law`(d)), `eE` (`e_E`, `lem:record:e-orthogonal`(b)), `sEp` (`s^E_p`,
`lem:record:e-orthogonal`(c)), `aEp` (`a^E_p = r(1 + 2q)/((1 - q)(1 - 2q))`,
`lem:record:e-law`(c)), `kEp` (`k^E_p = 3q/(1 - 3q)`), `csE` (`c^s_E`, defined by
`c^s_E q = k^E_p + s^E_p`) and `kappaEp` (`κ^E_p = k^E_p + s^E_p + a^E_p`),
`lem:record:exact-marginal-e`(i).

**The piece coefficients** (`lem:record:exact-marginal-e`(ii), `lem:oct24:matching-star`). They
are "the quantities of (i) at `(q_X, r_X)`" after the powers of `r` are cancelled as in the proof
of (i) (`q/r = r` at a prime), exactly as the certificate's `e_bounds` evaluates them
(`cert:record:e-coefficients`; `r_X = 1/⌊√X⌋ ≥ X^{-1/2}`, so the reading matters, see the
report): `sEq` (`s^E_p/q`), `csEX` (`c^s_E(X) = 3/(1 - 3q) + s^E/q`),
`sEX` (`s_E(X) = s^E/r`, with `𝔰_p/r = r (𝔰_p/q)` and `q²/r = qr`), `aEX`
(`a_E(X) = a^E/r = (1 + 2q)/((1 - q)(1 - 2q))`), `kappaEX` (`κ_E(X) = κ^E/r =
3r/(1 - 3q) + s_E + a_E`), `rEX` (`r_E(X) = 2 c^s_E(X) a_E(X)`) and
`rEstar`, the formula `2(3/(1 - 3q) + s^E/q) a_E(X)` of `lem:oct24:matching-star`.
`sEp_div_q`, `csE_eq`, `sEp_div_r`, `aEp_div_r`, `kappaEp_div_r` identify them with the
quotients at a prime (`q = r²`), and `rEstar_eq` shows that the two printed formulas for `r_E`
agree.

**Proved here.**
* (i), last sentence: `sEX_mono`, `aEX_mono`, `csEX_mono`, `kappaEX_mono` (and `sEq_mono`,
  `rEX_mono`): nondecreasing in `(q, r)` on `0 ≤ q ≤ q' ≤ 1/100`, `0 ≤ r ≤ r'`.
* (ii), the per-prime bounds used on the singleton sectors (`prime_bounds`: for a prime of the
  block, `s^E_p ≤ s_E(X) r_p`, `a^E_p ≤ a_E(X) r_p`, `k^E_p + s^E_p ≤ c^s_E(X) q_p`,
  `κ^E_p ≤ κ_E(X) r_p`, `k^E_p ≤ (3 r_X/(1 - 3q_X)) r_p`), the sector bounds
  (`sector_two_sym`, `sector_two_skew`, `sector_three_skew`, `sector_three_sym`) and the final
  comparisons (`final_sym`: `s^E_{(2)}/b, s^E_{(3)}/b < 2/b ≤ s_E(X) b^{-1/2}`; `final_skew`:
  `r_E b^{-3/2} ≤ r_E r_X² b^{-1/2} < b^{-1/2} ≤ a_E b^{-1/2}`).
* (i), the centred parts: `kEp_eq` (`k^E_p = 3/(p - 3)`), `centred_K1` (`c^s_E q = k^E_p + s^E_p`
  and `κ^E_p` bound the centred symmetric part and the centred operator of `K_1`).
* `lem:oct24:matching-star`: `leading_norm_le`
  (`‖L_{E,p}‖ = r_p/(1 - q_p) ≤ b^{-1/2}/(1 - b^{-1})`),
  `z1_bounds` (`1 - 2q ≤ z_1 ≤ 1`), `matching_remainder_identity`
  and `matching_remainder` (`‖D^a_{E,p} - L_{E,p}‖ ≤ 4qr/((1 - q)(1 - 2q))`, from the norms of
  `lem:record:e-law`(c)), `matching_remainder_lt` (below `r_E(X) q_p r_p` by the gate
  `4/((1 - q)(1 - 2q)) < r_E`), `rEX_ge` (`r_E ≥ 2(4 + √2)`), `rEX_lt_eleven` (`r_E < 11` for
  `q ≤ 2^{-20}`, `r ≤ 2^{-10}`, by monotonicity and an outward rational evaluation at
  `(2^{-20}, 2^{-10})`), `frakS_ge` (`𝔰_p ≥ (1 + √2) q`).

* **The gates of (ii) hold on the whole middle range** (`gates_hold`, with `sEX_point_le`): for
  every `q_X ≤ 2^{-20}`, `r_X ≤ 2^{-10}`, i.e. at every piece start `X ≥ 2^{20}` with
  `r_X = 1/⌊√X⌋`; so the gate hypotheses of the sector lemmas below are satisfiable (non-vacuity)
  and in fact always satisfied on the middle pieces.

* **`lem:oct24:matching-star` on a block** (`matching_star_block`, with
  `matching_block_skew_sector`): `‖L_{E,𝔅}‖ ≤ b^{-1/2}/(1 - b^{-1})` and
  `‖R_{E,𝔅}‖ ≤ r_E(X) b^{-3/2}`, given the same sector data.
* **(ii) on a block, given the sector decomposition** (`matching_block_bounds`): with the bundle
  `MatchingSectorBounds` (the sector decomposition and the one-prime norms as hypotheses; toy
  instance `matchingSectorBounds_toy`), for a piece starting at `X ≥ 2^{20}` with
  `X^{-1/2} ≤ r_X ≤ 2^{-10}`, the block difference has symmetric part of norm at most
  `s_E(X) b^{-1/2}` and skew part of norm at most `a_E(X) b^{-1/2}`.

* **`cert:record:e-coefficients`, the two printed rows** (`cert_e_Q3`, `cert_e_two_pow_45`,
  with `isqrt_Q3`, `isqrt_two_pow_45`): the bounds on `s_E`, `a_E`, `κ_E`, `r_E` at `X = Q₃` and
  `X = 2^{45}` with `r_X = 1/⌊√X⌋`, and the gates `s^E_{(2)} ≤ 1.0000016`,
  `s^E_{(3)} ≤ 0.0002248` at
  `Q₃`, by outward rational evaluation (`coeff_bounds`); all hold as printed.

**Hypotheses, not proved here.** The operator inputs (`lem:record:e-law`(c), (d),
`lem:record:e-orthogonal`(c): the norms whose constants are defined here) and the sector
decomposition of the block difference (`lem:sector`(a), (b), (h): orthogonal sectors, the norm
of a tensor product of centred operators is the product of the norms) enter the sector lemmas as
real hypotheses on the norms. The tensor and sector structure itself is not formalized here.
-/

@[expose] public section

namespace Sarkozy.MiddleRecords

/-- Closes the positivity side goals of `gcongr` in this file. -/
syntax "mc_side" : tactic

macro_rules
  | `(tactic| mc_side) => `(tactic| first
      | assumption
      | linarith
      | positivity
      | exact Real.sqrt_nonneg _
      | (apply div_nonneg <;> mc_side)
      | (apply mul_nonneg <;> mc_side)
      | (apply add_nonneg <;> mc_side)
      | (apply div_pos <;> mc_side)
      | (apply mul_pos <;> mc_side)
      | nlinarith)

/-! ## The constants at one prime -/

/-- `Z = (1 - q)(1 - 2q)`. -/
noncomputable def Zq (q : ℝ) : ℝ := (1 - q) * (1 - 2 * q)

/-- `𝔰_p = q/(1 - q) [(1 + √2)/(1 - 9q) + 7q/(Z(1 - 9q)(1 - 2q))]` (`lem:record:e-law`(d)). -/
noncomputable def frakS (q : ℝ) : ℝ :=
  q / (1 - q) * ((1 + Real.sqrt 2) / (1 - 9 * q) + 7 * q / (Zq q * (1 - 9 * q) * (1 - 2 * q)))

/-- `e_E = qr/((1 - q)(1 - 3q))^{1/2} · (2 + 4q²/(1 - 2q)²)^{1/2}`
(`lem:record:e-orthogonal`(b)). -/
noncomputable def eE (q r : ℝ) : ℝ :=
  q * r / Real.sqrt ((1 - q) * (1 - 3 * q)) * Real.sqrt (2 + 4 * q ^ 2 / (1 - 2 * q) ^ 2)

/-- `s^E_p = 𝔰_p + 2e_E/(1 - 2q) + q²/((1 - q)(1 - 2q)) + 18q²/((1 - q)(1 - 9q))`
(`lem:record:e-orthogonal`(c)). -/
noncomputable def sEp (q r : ℝ) : ℝ :=
  frakS q + 2 * eE q r / (1 - 2 * q) + q ^ 2 / ((1 - q) * (1 - 2 * q)) +
    18 * q ^ 2 / ((1 - q) * (1 - 9 * q))

/-- `a^E_p = r(1 + 2q)/((1 - q)(1 - 2q))` (`lem:record:e-law`(c)). -/
noncomputable def aEp (q r : ℝ) : ℝ := r * (1 + 2 * q) / ((1 - q) * (1 - 2 * q))

/-- `k^E_p = 3/(p - 3) = 3q/(1 - 3q)` (`lem:record:exact-marginal-e`(i)). -/
noncomputable def kEp (q : ℝ) : ℝ := 3 * q / (1 - 3 * q)

/-- `c^s_E`, defined by `c^s_E q = k^E_p + s^E_p` (`lem:record:exact-marginal-e`(i)). -/
noncomputable def csE (q r : ℝ) : ℝ := (kEp q + sEp q r) / q

/-- `κ^E_p = k^E_p + s^E_p + a^E_p` (`lem:record:exact-marginal-e`(i)). -/
noncomputable def kappaEp (q r : ℝ) : ℝ := kEp q + sEp q r + aEp q r

/-! ## The piece coefficients (powers of `r` cancelled) -/

/-- `s^E_p/q`, the powers of `q` cancelled. -/
noncomputable def sEq (q r : ℝ) : ℝ :=
  1 / (1 - q) * ((1 + Real.sqrt 2) / (1 - 9 * q) + 7 * q / (Zq q * (1 - 9 * q) * (1 - 2 * q))) +
    2 * r / ((1 - 2 * q) * Real.sqrt ((1 - q) * (1 - 3 * q))) *
      Real.sqrt (2 + 4 * q ^ 2 / (1 - 2 * q) ^ 2) +
    q / ((1 - q) * (1 - 2 * q)) + 18 * q / ((1 - q) * (1 - 9 * q))

/-- `c^s_E(X) = 3/(1 - 3q) + s^E/q` at `(q_X, r_X)`. -/
noncomputable def csEX (q r : ℝ) : ℝ := 3 / (1 - 3 * q) + sEq q r

/-- `s_E(X) = s^E/r` at `(q_X, r_X)`, with `q/r` replaced by `r` in `𝔰_p/r` and `q²/r` by `qr`
(and `e_E/r = q (…)` exact): the formula of the certificate (`E_symmetric_over_r` of `e_bounds`). -/
noncomputable def sEX (q r : ℝ) : ℝ :=
  r * (1 / (1 - q) * ((1 + Real.sqrt 2) / (1 - 9 * q) +
      7 * q / (Zq q * (1 - 9 * q) * (1 - 2 * q)))) +
    2 * q / ((1 - 2 * q) * Real.sqrt ((1 - q) * (1 - 3 * q))) *
      Real.sqrt (2 + 4 * q ^ 2 / (1 - 2 * q) ^ 2) +
    q * r / ((1 - q) * (1 - 2 * q)) + 18 * q * r / ((1 - q) * (1 - 9 * q))

/-- `a_E(X) = a^E/r = (1 + 2q)/((1 - q)(1 - 2q))`. -/
noncomputable def aEX (q : ℝ) : ℝ := (1 + 2 * q) / ((1 - q) * (1 - 2 * q))

/-- `κ_E(X) = κ^E/r = 3r/(1 - 3q) + s_E(X) + a_E(X)` (`k^E/r` with `q/r` replaced by `r`). -/
noncomputable def kappaEX (q r : ℝ) : ℝ := 3 * r / (1 - 3 * q) + sEX q r + aEX q

/-- `r_E(X) = 2 c^s_E(X) a_E(X)` (`lem:record:exact-marginal-e`(ii)). -/
noncomputable def rEX (q r : ℝ) : ℝ := 2 * csEX q r * aEX q

/-- `r_E(X) = 2(3/(1 - 3q) + s^E/q) a_E(X)`, the formula of `lem:oct24:matching-star`. -/
noncomputable def rEstar (q r : ℝ) : ℝ := 2 * (3 / (1 - 3 * q) + sEp q r / q) * aEX q

/-! ## Identification with the quotients at a prime -/

/-- `s^E_p/q = sEq`. -/
theorem sEp_div_q {q : ℝ} (r : ℝ) (hq : 0 < q) (hq9 : q < 1 / 9) :
    sEp q r / q = sEq q r := by
  have h1 : 1 - q ≠ 0 := by linarith
  have h2 : 1 - 2 * q ≠ 0 := by linarith
  have h9 : 1 - 9 * q ≠ 0 := by linarith
  have hsq : 0 < (1 - q) * (1 - 3 * q) := by nlinarith
  have hs : Real.sqrt ((1 - q) * (1 - 3 * q)) ≠ 0 := (Real.sqrt_pos.mpr hsq).ne'
  unfold sEp sEq frakS eE Zq
  field_simp

/-- `c^s_E = c^s_E(X)` as functions: `(k^E + s^E)/q = 3/(1 - 3q) + s^E/q`. -/
theorem csE_eq {q : ℝ} (r : ℝ) (hq : 0 < q) (hq9 : q < 1 / 9) : csE q r = csEX q r := by
  have h3 : 1 - 3 * q ≠ 0 := by linarith
  unfold csE csEX
  rw [add_div, sEp_div_q r hq hq9]
  unfold kEp
  field_simp

/-- **`s^E_p/r = s_E`** at a prime (`q = r²`). -/
theorem sEp_div_r {q r : ℝ} (hr : 0 < r) (hqr : q = r ^ 2) (hq9 : q < 1 / 9) :
    sEp q r / r = sEX q r := by
  have hr0 : r ≠ 0 := hr.ne'
  have h1 : 1 - q ≠ 0 := by linarith
  have h2 : 1 - 2 * q ≠ 0 := by linarith
  have h9 : 1 - 9 * q ≠ 0 := by linarith
  unfold sEp sEX frakS eE Zq
  rw [hqr]
  field_simp

/-- `a^E_p/r = a_E`. -/
theorem aEp_div_r {q r : ℝ} (hr : r ≠ 0) : aEp q r / r = aEX q := by
  unfold aEp aEX
  field_simp

/-- **`κ^E_p/r = κ_E`** at a prime (`q = r²`). -/
theorem kappaEp_div_r {q r : ℝ} (hr : 0 < r) (hqr : q = r ^ 2) (hq9 : q < 1 / 9) :
    kappaEp q r / r = kappaEX q r := by
  have h3 : 1 - 3 * q ≠ 0 := by linarith
  unfold kappaEp kappaEX
  rw [← sEp_div_r hr hqr hq9, ← aEp_div_r hr.ne', add_div, add_div]
  congr 2
  unfold kEp
  rw [hqr]
  field_simp

/-- **The two printed formulas for `r_E(X)` agree** (`lem:record:exact-marginal-e`(ii) and
`lem:oct24:matching-star`). -/
theorem rEstar_eq {q : ℝ} (r : ℝ) (hq : 0 < q) (hq9 : q < 1 / 9) : rEstar q r = rEX q r := by
  unfold rEstar rEX csEX
  rw [sEp_div_q r hq hq9]

/-! ## Monotonicity (`lem:record:exact-marginal-e`(i), last sentence) -/

/-- `s^E/q` is nondecreasing in `(q, r)`. -/
theorem sEq_mono {q q' r r' : ℝ} (hq : 0 ≤ q) (hqq : q ≤ q') (hq' : q' ≤ 1 / 100) (hr : 0 ≤ r)
    (hrr : r ≤ r') : sEq q r ≤ sEq q' r' := by
  have h1 : 0 < 1 - q' := by linarith
  have h2 : 0 < 1 - 2 * q' := by linarith
  have h3 : 0 < 1 - 3 * q' := by linarith
  have h9 : 0 < 1 - 9 * q' := by linarith
  have h1' : 0 < 1 - q := by linarith
  have h2' : 0 < 1 - 2 * q := by linarith
  have h9' : 0 < 1 - 9 * q := by linarith
  have hZ : 0 < Zq q' := mul_pos h1 h2
  have hs : 0 < Real.sqrt ((1 - q') * (1 - 3 * q')) := Real.sqrt_pos.mpr (mul_pos h1 h3)
  unfold sEq Zq
  gcongr <;> mc_side

theorem csEX_mono {q q' r r' : ℝ} (hq : 0 ≤ q) (hqq : q ≤ q') (hq' : q' ≤ 1 / 100) (hr : 0 ≤ r)
    (hrr : r ≤ r') : csEX q r ≤ csEX q' r' := by
  have h3 : 0 < 1 - 3 * q' := by linarith
  unfold csEX
  gcongr ?_ + ?_
  · gcongr
  · exact sEq_mono hq hqq hq' hr hrr

theorem sEq_nonneg {q r : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 100) (hr : 0 ≤ r) : 0 ≤ sEq q r := by
  have h1 : 0 < 1 - q := by linarith
  have h2 : 0 < 1 - 2 * q := by linarith
  have h3 : 0 < 1 - 3 * q := by linarith
  have h9 : 0 < 1 - 9 * q := by linarith
  have hZ : 0 < Zq q := mul_pos h1 h2
  unfold sEq
  mc_side

theorem csEX_nonneg {q r : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 100) (hr : 0 ≤ r) : 0 ≤ csEX q r := by
  have h3 : 0 < 1 - 3 * q := by linarith
  unfold csEX
  exact add_nonneg (div_nonneg (by norm_num) h3.le) (sEq_nonneg hq hq' hr)

/-- **`s_E = s^E/r` is nondecreasing in `(q, r)`.** -/
theorem sEX_mono {q q' r r' : ℝ} (hq : 0 ≤ q) (hqq : q ≤ q') (hq' : q' ≤ 1 / 100) (hr : 0 ≤ r)
    (hrr : r ≤ r') : sEX q r ≤ sEX q' r' := by
  have h1 : 0 < 1 - q' := by linarith
  have h2 : 0 < 1 - 2 * q' := by linarith
  have h3 : 0 < 1 - 3 * q' := by linarith
  have h9 : 0 < 1 - 9 * q' := by linarith
  have hZ : 0 < Zq q' := mul_pos h1 h2
  have hs : 0 < Real.sqrt ((1 - q') * (1 - 3 * q')) := Real.sqrt_pos.mpr (mul_pos h1 h3)
  unfold sEX Zq
  gcongr <;> mc_side

/-- **`a_E = a^E/r` is nondecreasing in `q`.** -/
theorem aEX_mono {q q' : ℝ} (hq : 0 ≤ q) (hqq : q ≤ q') (hq' : q' ≤ 1 / 100) :
    aEX q ≤ aEX q' := by
  have h1 : 0 < 1 - q' := by linarith
  have h2 : 0 < 1 - 2 * q' := by linarith
  unfold aEX
  gcongr <;> mc_side

theorem aEX_nonneg {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 100) : 0 ≤ aEX q := by
  have h1 : 0 < 1 - q := by linarith
  have h2 : 0 < 1 - 2 * q := by linarith
  unfold aEX
  mc_side

/-- **`κ_E = κ^E/r` is nondecreasing in `(q, r)`.** -/
theorem kappaEX_mono {q q' r r' : ℝ} (hq : 0 ≤ q) (hqq : q ≤ q') (hq' : q' ≤ 1 / 100) (hr : 0 ≤ r)
    (hrr : r ≤ r') : kappaEX q r ≤ kappaEX q' r' := by
  have h3 : 0 < 1 - 3 * q' := by linarith
  have hk : 3 * r / (1 - 3 * q) ≤ 3 * r' / (1 - 3 * q') := by
    gcongr
    mc_side
  unfold kappaEX
  linarith [aEX_mono hq hqq hq', sEX_mono hq hqq hq' hr hrr]

/-- `r_E = 2 c^s_E a_E` is nondecreasing in `(q, r)`. -/
theorem rEX_mono {q q' r r' : ℝ} (hq : 0 ≤ q) (hqq : q ≤ q') (hq' : q' ≤ 1 / 100) (hr : 0 ≤ r)
    (hrr : r ≤ r') : rEX q r ≤ rEX q' r' := by
  unfold rEX
  have hc := csEX_mono hq hqq hq' hr hrr
  have hc0 := csEX_nonneg hq (le_trans hqq hq') hr
  have ha := aEX_mono hq hqq hq'
  have ha0 := aEX_nonneg hq (le_trans hqq hq')
  have ha0' := aEX_nonneg (le_trans hq hqq) hq'
  have hc0' := csEX_nonneg (le_trans hq hqq) hq' (le_trans hr hrr)
  have := mul_le_mul hc ha ha0 hc0'
  linarith

/-! ## Lower bounds -/

/-- `√2 ≥ 0`, `(√2)² = 2`. -/
theorem sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

/-- **`𝔰_p ≥ (1 + √2) q`.** -/
theorem frakS_ge {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 100) : (1 + Real.sqrt 2) * q ≤ frakS q := by
  have h1 : 0 < 1 - q := by linarith
  have h2 : 0 < 1 - 2 * q := by linarith
  have h9 : 0 < 1 - 9 * q := by linarith
  have hZ : 0 < Zq q := mul_pos h1 h2
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hA : 1 + Real.sqrt 2 ≤ (1 + Real.sqrt 2) / (1 - 9 * q) := by
    rw [le_div_iff₀ h9]
    nlinarith
  have hB : 0 ≤ 7 * q / (Zq q * (1 - 9 * q) * (1 - 2 * q)) := by mc_side
  have hC : (1 + Real.sqrt 2) ≤ 1 / (1 - q) * ((1 + Real.sqrt 2) / (1 - 9 * q) +
      7 * q / (Zq q * (1 - 9 * q) * (1 - 2 * q))) := by
    have hD : 1 ≤ 1 / (1 - q) := by
      rw [le_div_iff₀ h1]
      linarith
    have hE : 0 ≤ (1 + Real.sqrt 2) / (1 - 9 * q) +
        7 * q / (Zq q * (1 - 9 * q) * (1 - 2 * q)) := by
      have : 0 ≤ (1 + Real.sqrt 2) / (1 - 9 * q) := by mc_side
      linarith
    nlinarith
  have e : frakS q = q * (1 / (1 - q) * ((1 + Real.sqrt 2) / (1 - 9 * q) +
      7 * q / (Zq q * (1 - 9 * q) * (1 - 2 * q)))) := by
    unfold frakS
    ring
  rw [e]
  nlinarith

/-- `s^E/q ≥ 1 + √2`. -/
theorem sEq_ge {q r : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 100) (hr : 0 ≤ r) :
    1 + Real.sqrt 2 ≤ sEq q r := by
  have h1 : 0 < 1 - q := by linarith
  have h2 : 0 < 1 - 2 * q := by linarith
  have h3 : 0 < 1 - 3 * q := by linarith
  have h9 : 0 < 1 - 9 * q := by linarith
  have hZ : 0 < Zq q := mul_pos h1 h2
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hD : 1 ≤ 1 / (1 - q) := by
    rw [le_div_iff₀ h1]
    linarith
  have hA : 1 + Real.sqrt 2 ≤ (1 + Real.sqrt 2) / (1 - 9 * q) := by
    rw [le_div_iff₀ h9]
    nlinarith
  have hB : 0 ≤ 7 * q / (Zq q * (1 - 9 * q) * (1 - 2 * q)) := by mc_side
  have hT2 : 0 ≤ 2 * r / ((1 - 2 * q) * Real.sqrt ((1 - q) * (1 - 3 * q))) *
      Real.sqrt (2 + 4 * q ^ 2 / (1 - 2 * q) ^ 2) := by mc_side
  have hT3 : 0 ≤ q / ((1 - q) * (1 - 2 * q)) := by mc_side
  have hT4 : 0 ≤ 18 * q / ((1 - q) * (1 - 9 * q)) := by mc_side
  have hT1 : 1 + Real.sqrt 2 ≤ 1 / (1 - q) * ((1 + Real.sqrt 2) / (1 - 9 * q) +
      7 * q / (Zq q * (1 - 9 * q) * (1 - 2 * q))) := by
    have hE : 0 ≤ (1 + Real.sqrt 2) / (1 - 9 * q) := by mc_side
    nlinarith
  unfold sEq
  linarith

/-- `a_E ≥ 1`. -/
theorem aEX_ge_one {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 100) : 1 ≤ aEX q := by
  have h1 : 0 < 1 - q := by linarith
  have h2 : 0 < 1 - 2 * q := by linarith
  unfold aEX
  rw [le_div_iff₀ (mul_pos h1 h2)]
  nlinarith

/-- **`r_E(X) ≥ 2(4 + √2)`** (`lem:oct24:matching-star`). -/
theorem rEX_ge {q r : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 100) (hr : 0 ≤ r) :
    2 * (4 + Real.sqrt 2) ≤ rEX q r := by
  have h3 : 0 < 1 - 3 * q := by linarith
  have h3' : 3 ≤ 3 / (1 - 3 * q) := by
    rw [le_div_iff₀ h3]
    linarith
  have hs := sEq_ge hq hq' hr
  have ha := aEX_ge_one hq hq'
  have hc : 4 + Real.sqrt 2 ≤ csEX q r := by
    unfold csEX
    linarith
  have hc0 : 0 ≤ 4 + Real.sqrt 2 := by positivity
  unfold rEX
  nlinarith

/-! ## `r_E < 11` (`lem:oct24:matching-star`) -/

/-- **`r_E(2^{-20}, 2^{-10}) < 11`**, by an outward rational evaluation. -/
theorem rEX_point_lt : rEX (1 / 1048576) (1 / 1024) < 11 := by
  set q : ℝ := 1 / 1048576 with hq
  set r : ℝ := 1 / 1024 with hr
  have hs2 : Real.sqrt 2 ≤ 14143 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hsA : 99999 / 100000 ≤ Real.sqrt ((1 - q) * (1 - 3 * q)) := by
    rw [Real.le_sqrt (by norm_num) (by rw [hq]; norm_num)]
    rw [hq]
    norm_num
  have hsB : Real.sqrt (2 + 4 * q ^ 2 / (1 - 2 * q) ^ 2) ≤ 14143 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    rw [hq]
    norm_num
  have h1 : 0 < 1 - q := by rw [hq]; norm_num
  have h2 : 0 < 1 - 2 * q := by rw [hq]; norm_num
  have h3 : 0 < 1 - 3 * q := by rw [hq]; norm_num
  have h9 : 0 < 1 - 9 * q := by rw [hq]; norm_num
  have hZ : 0 < Zq q := mul_pos h1 h2
  have hrr : (0 : ℝ) ≤ r := by rw [hr]; norm_num
  have hqq : (0 : ℝ) ≤ q := by rw [hq]; norm_num
  have hbound : rEX q r ≤ 2 * (3 / (1 - 3 * q) +
      (1 / (1 - q) * ((1 + 14143 / 10000) / (1 - 9 * q) +
        7 * q / (Zq q * (1 - 9 * q) * (1 - 2 * q))) +
      2 * r / ((1 - 2 * q) * (99999 / 100000)) * (14143 / 10000) +
      q / ((1 - q) * (1 - 2 * q)) + 18 * q / ((1 - q) * (1 - 9 * q)))) * aEX q := by
    unfold rEX csEX sEq
    have ha0 : 0 ≤ aEX q := by unfold aEX; mc_side
    gcongr
  refine lt_of_le_of_lt hbound ?_
  unfold aEX Zq
  rw [hq, hr]
  norm_num

/-- **`r_E(X) < 11` when `q_X ≤ 2^{-20}` and `r_X ≤ 2^{-10}`** (`lem:oct24:matching-star`, last
sentence), by monotonicity (`rEX_mono`) and `rEX_point_lt`. -/
theorem rEX_lt_eleven {q r : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 1048576) (hr : 0 ≤ r)
    (hr' : r ≤ 1 / 1024) : rEX q r < 11 :=
  lt_of_le_of_lt (rEX_mono hq hq' (by norm_num) hr hr') rEX_point_lt

/-! ## The gates of `lem:record:exact-marginal-e`(ii) hold on the whole middle range -/

/-- `s_E(2^{-20}, 2^{-10}) ≤ 1/400`, by an outward rational evaluation. -/
theorem sEX_point_le : sEX (1 / 1048576) (1 / 1024) ≤ 1 / 400 := by
  set q : ℝ := 1 / 1048576 with hq
  set r : ℝ := 1 / 1024 with hr
  have hs2 : Real.sqrt 2 ≤ 14143 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hsA : 99999 / 100000 ≤ Real.sqrt ((1 - q) * (1 - 3 * q)) := by
    rw [Real.le_sqrt (by norm_num) (by rw [hq]; norm_num)]
    rw [hq]
    norm_num
  have hsB : Real.sqrt (2 + 4 * q ^ 2 / (1 - 2 * q) ^ 2) ≤ 14143 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    rw [hq]
    norm_num
  have h1 : 0 < 1 - q := by rw [hq]; norm_num
  have h2 : 0 < 1 - 2 * q := by rw [hq]; norm_num
  have h3 : 0 < 1 - 3 * q := by rw [hq]; norm_num
  have h9 : 0 < 1 - 9 * q := by rw [hq]; norm_num
  have hZ : 0 < Zq q := mul_pos h1 h2
  have hrr : (0 : ℝ) ≤ r := by rw [hr]; norm_num
  have hqq : (0 : ℝ) ≤ q := by rw [hq]; norm_num
  have hbound : sEX q r ≤ r * (1 / (1 - q) * ((1 + 14143 / 10000) / (1 - 9 * q) +
        7 * q / (Zq q * (1 - 9 * q) * (1 - 2 * q)))) +
      2 * q / ((1 - 2 * q) * (99999 / 100000)) * (14143 / 10000) +
      q * r / ((1 - q) * (1 - 2 * q)) + 18 * q * r / ((1 - q) * (1 - 9 * q)) := by
    unfold sEX
    gcongr
  refine le_trans hbound ?_
  unfold Zq
  rw [hq, hr]
  norm_num

/-- **The gates of `lem:record:exact-marginal-e`(ii) hold at every `(q_X, r_X)` with
`q_X ≤ 2^{-20}` and `r_X ≤ 2^{-10}`**, in particular at every piece start `X ≥ 2^{20}` with
`r_X = 1/⌊√X⌋` (so at the 33 middle piece starts, all `≥ Q₃ > 2^{24}`): `3q/(1 - 3q) < 1`,
`κ_E r < 1`, `r_E r² < 1`, `4/((1 - q)(1 - 2q)) < r_E`, `κ_E³ < r_E`,
`s^E_{(2)} = (6r/(1 - 3q)) s_E + s_E² + a_E² < 2` and
`s^E_{(3)} = [(3r/(1 - 3q))³ + κ_E³] r < 2`. By monotonicity (`sEX_mono`, `aEX_mono`,
`kappaEX_mono`, `rEX_lt_eleven`, `rEX_ge`) and one outward evaluation (`sEX_point_le`); the
certificate `cert:record:e-coefficients` checks the same gates at the 33 starts. -/
theorem gates_hold {q r : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 1048576) (hr : 0 ≤ r)
    (hr' : r ≤ 1 / 1024) :
    3 * q / (1 - 3 * q) < 1 ∧ kappaEX q r * r < 1 ∧ rEX q r * r ^ 2 < 1 ∧
      4 / ((1 - q) * (1 - 2 * q)) < rEX q r ∧ kappaEX q r ^ 3 < rEX q r ∧
      6 * r / (1 - 3 * q) * sEX q r + sEX q r ^ 2 + aEX q ^ 2 < 2 ∧
      ((3 * r / (1 - 3 * q)) ^ 3 + kappaEX q r ^ 3) * r < 2 := by
  have hq100 : q ≤ 1 / 100 := by linarith
  have h1 : 0 < 1 - q := by linarith
  have h2 : 0 < 1 - 2 * q := by linarith
  have h3 : 0 < 1 - 3 * q := by linarith
  -- upper bounds at the corner `(2^{-20}, 2^{-10})`
  have hsE : sEX q r ≤ 1 / 400 :=
    le_trans (sEX_mono hq hq' (by norm_num) hr hr') sEX_point_le
  have hsE0 : 0 ≤ sEX q r := by
    have h9 : 0 < 1 - 9 * q := by linarith
    have hZ : 0 < Zq q := mul_pos h1 h2
    unfold sEX
    mc_side
  have haE : aEX q ≤ 100001 / 100000 := by
    refine le_trans (aEX_mono hq hq' (by norm_num)) ?_
    unfold aEX
    norm_num
  have haE1 : 1 ≤ aEX q := aEX_ge_one hq hq100
  have hK : 3 * r / (1 - 3 * q) ≤ 3 / 1024 * (1048576 / 1048573) := by
    have hk1 : 1 / (1 - 3 * q) ≤ 1048576 / 1048573 := by
      rw [div_le_div_iff₀ h3 (by norm_num)]
      linarith
    calc 3 * r / (1 - 3 * q) = 3 * r * (1 / (1 - 3 * q)) := by ring
      _ ≤ 3 / 1024 * (1048576 / 1048573) := by
          apply mul_le_mul (by linarith) hk1 (by positivity) (by norm_num)
  have hK0 : 0 ≤ 3 * r / (1 - 3 * q) := div_nonneg (by linarith) h3.le
  have hκ : kappaEX q r ≤ 101 / 100 := by
    unfold kappaEX
    have : (3 : ℝ) / 1024 * (1048576 / 1048573) + 1 / 400 + 100001 / 100000 ≤ 101 / 100 := by
      norm_num
    linarith
  have hκ0 : 0 ≤ kappaEX q r := by
    unfold kappaEX
    linarith
  have hrE : rEX q r < 11 := rEX_lt_eleven hq hq' hr hr'
  have hrE' : 2 * (4 + Real.sqrt 2) ≤ rEX q r := rEX_ge hq hq100 hr
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hrE10 : 10 ≤ rEX q r := by linarith
  have hκ3 : kappaEX q r ^ 3 ≤ (101 / 100) ^ 3 := pow_le_pow_left₀ hκ0 hκ 3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [div_lt_one h3]
    linarith
  · calc kappaEX q r * r ≤ 101 / 100 * (1 / 1024) := mul_le_mul hκ hr' hr (by norm_num)
      _ < 1 := by norm_num
  · have hr2 : r ^ 2 ≤ (1 / 1024) ^ 2 := pow_le_pow_left₀ hr hr' 2
    calc rEX q r * r ^ 2 ≤ 11 * (1 / 1024) ^ 2 :=
          mul_le_mul hrE.le hr2 (sq_nonneg r) (by norm_num)
      _ < 1 := by norm_num
  · have h4 : 4 / ((1 - q) * (1 - 2 * q)) ≤ 5 := by
      rw [div_le_iff₀ (mul_pos h1 h2)]
      nlinarith
    linarith
  · have : ((101 : ℝ) / 100) ^ 3 < 10 := by norm_num
    linarith
  · have e1 : 6 * r / (1 - 3 * q) * sEX q r ≤ 2 * (3 / 1024 * (1048576 / 1048573)) * (1 / 400) := by
      have : 6 * r / (1 - 3 * q) = 2 * (3 * r / (1 - 3 * q)) := by ring
      rw [this]
      exact mul_le_mul (by linarith) hsE hsE0 (by positivity)
    have e2 : sEX q r ^ 2 ≤ (1 / 400) ^ 2 := pow_le_pow_left₀ hsE0 hsE 2
    have e3 : aEX q ^ 2 ≤ (100001 / 100000) ^ 2 := pow_le_pow_left₀ (by linarith) haE 2
    have : 2 * (3 / 1024 * (1048576 / 1048573)) * (1 / 400) + (1 / 400 : ℝ) ^ 2 +
        (100001 / 100000) ^ 2 < 2 := by norm_num
    linarith
  · have e1 : (3 * r / (1 - 3 * q)) ^ 3 ≤ (3 / 1024 * (1048576 / 1048573)) ^ 3 :=
      pow_le_pow_left₀ hK0 hK 3
    have hsum : (3 * r / (1 - 3 * q)) ^ 3 + kappaEX q r ^ 3 ≤
        (3 / 1024 * (1048576 / 1048573)) ^ 3 + (101 / 100) ^ 3 := by linarith
    calc ((3 * r / (1 - 3 * q)) ^ 3 + kappaEX q r ^ 3) * r
        ≤ ((3 / 1024 * (1048576 / 1048573)) ^ 3 + (101 / 100) ^ 3) * (1 / 1024) :=
          mul_le_mul hsum hr' hr (by positivity)
      _ < 2 := by norm_num

/-! ## The one-prime remainder of the matching star (`lem:oct24:matching-star`) -/

/-- **`1 - 2q ≤ z_1 ≤ 1`** for `z_1 = (p² - 3p + 4)/(p(p - 1))`, `q = 1/p`, `p ≥ 2`
(`lem:record:e-law`(b)). -/
theorem z1_bounds {p : ℝ} (hp : 2 ≤ p) :
    1 - 2 / p ≤ (p ^ 2 - 3 * p + 4) / (p * (p - 1)) ∧
      (p ^ 2 - 3 * p + 4) / (p * (p - 1)) ≤ 1 := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hpp : 0 < p * (p - 1) := mul_pos hp0 hp1
  constructor
  · rw [le_div_iff₀ hpp]
    have : (1 - 2 / p) * (p * (p - 1)) = (p - 2) * (p - 1) := by
      field_simp
    rw [this]
    nlinarith
  · rw [div_le_one hpp]
    nlinarith

/-- `(r/(1 - q))(2q/(1 - 2q)) + 2qr/((1 - q)(1 - 2q)) = 4qr/((1 - q)(1 - 2q))`. -/
theorem matching_remainder_identity (q r : ℝ) :
    r / (1 - q) * (2 * q / (1 - 2 * q)) + 2 * q * r / ((1 - q) * (1 - 2 * q)) =
      4 * q * r / ((1 - q) * (1 - 2 * q)) := by
  rw [div_mul_div_comm, ← add_div]
  ring

/-- **The one-prime remainder** (`lem:oct24:matching-star`, proof): by `lem:record:e-law`(c),
`D^a_{E,p} - L_{E,p} = (z_1^{-1} - 1)(C + D) - (δ_C D + δ_D C)/z_1` with `‖C + D‖ = r/(1 - q)` and
`‖δ_C D‖, ‖δ_D C‖ ≤ qr/(1 - q)`; with `1 - 2q ≤ z_1 ≤ 1` the triangle inequality gives the bound
`4qr/((1 - q)(1 - 2q))`. The norms are hypotheses (`nCD`, `nδ₁`, `nδ₂`). -/
theorem matching_remainder {q r z1 nCD nδ₁ nδ₂ : ℝ} (hq : 0 ≤ q) (hq2 : q < 1 / 2) (hr : 0 ≤ r)
    (hz1 : 1 - 2 * q ≤ z1) (hz1' : z1 ≤ 1) (hCD : nCD = r / (1 - q))
    (hδ₁ : nδ₁ ≤ q * r / (1 - q)) (hδ₂ : nδ₂ ≤ q * r / (1 - q)) :
    |1 / z1 - 1| * nCD + (nδ₁ + nδ₂) / z1 ≤ 4 * q * r / ((1 - q) * (1 - 2 * q)) := by
  have h1 : 0 < 1 - q := by linarith
  have h2 : 0 < 1 - 2 * q := by linarith
  have hz0 : 0 < z1 := lt_of_lt_of_le h2 hz1
  have habs : |1 / z1 - 1| ≤ 2 * q / (1 - 2 * q) := by
    have hge : 0 ≤ 1 / z1 - 1 := by
      rw [sub_nonneg, le_div_iff₀ hz0]
      linarith
    rw [abs_of_nonneg hge]
    have : 1 / z1 ≤ 1 / (1 - 2 * q) := one_div_le_one_div_of_le h2 hz1
    have e : 1 / (1 - 2 * q) - 1 = 2 * q / (1 - 2 * q) := by
      field_simp
      ring
    linarith
  have hCD0 : 0 ≤ nCD := by rw [hCD]; positivity
  have hsum : nδ₁ + nδ₂ ≤ 2 * (q * r / (1 - q)) := by linarith
  have hnum0 : 0 ≤ 2 * (q * r / (1 - q)) := by positivity
  have hdiv : (nδ₁ + nδ₂) / z1 ≤ 2 * (q * r / (1 - q)) / (1 - 2 * q) := by
    calc (nδ₁ + nδ₂) / z1 ≤ 2 * (q * r / (1 - q)) / z1 :=
          div_le_div_of_nonneg_right hsum hz0.le
      _ ≤ 2 * (q * r / (1 - q)) / (1 - 2 * q) :=
          div_le_div_of_nonneg_left hnum0 h2 hz1
  have hfirst : |1 / z1 - 1| * nCD ≤ 2 * q / (1 - 2 * q) * (r / (1 - q)) := by
    rw [← hCD]
    exact mul_le_mul_of_nonneg_right habs hCD0
  have e : 2 * q / (1 - 2 * q) * (r / (1 - q)) + 2 * (q * r / (1 - q)) / (1 - 2 * q) =
      4 * q * r / ((1 - q) * (1 - 2 * q)) := by
    field_simp
    ring
  linarith

/-- **The remainder is below `r_E(X) q_p r_p`** (`lem:oct24:matching-star`, proof): for a prime
with `0 ≤ q_p ≤ q_X < 1/2` and `r_p ≥ 0`, the gate `4/((1 - q_X)(1 - 2q_X)) < r_E` gives
`4 q_p r_p/((1 - q_p)(1 - 2q_p)) ≤ r_E q_p r_p` (and `q_p r_p = p^{-3/2} ≤ b^{-3/2}`). -/
theorem matching_remainder_lt {qp rp qX rE : ℝ} (hqp : 0 ≤ qp) (hqpX : qp ≤ qX) (hqX : qX < 1 / 2)
    (hrp : 0 ≤ rp) (hgate : 4 / ((1 - qX) * (1 - 2 * qX)) < rE) :
    4 * qp * rp / ((1 - qp) * (1 - 2 * qp)) ≤ rE * (qp * rp) := by
  have h1 : 0 < 1 - qX := by linarith
  have h2 : 0 < 1 - 2 * qX := by linarith
  have h1' : 0 < 1 - qp := by linarith
  have h2' : 0 < 1 - 2 * qp := by linarith
  have hmono : 4 / ((1 - qp) * (1 - 2 * qp)) ≤ 4 / ((1 - qX) * (1 - 2 * qX)) := by
    gcongr
  have e : 4 * qp * rp / ((1 - qp) * (1 - 2 * qp)) = 4 / ((1 - qp) * (1 - 2 * qp)) * (qp * rp) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_right (le_trans hmono hgate.le) (mul_nonneg hqp hrp)

/-- **The leading star** (`lem:oct24:matching-star`): `‖L_{E,p}‖ = r_p/(1 - q_p)` with
`q_p = r_p² ≤ B² < 1`, `B = b^{-1/2}`, is at most `B/(1 - B²) = b^{-1/2}/(1 - b^{-1})`. -/
theorem leading_norm_le {rp B : ℝ} (hrp : 0 ≤ rp) (hrpB : rp ≤ B) (hB1 : B ^ 2 < 1) :
    rp / (1 - rp ^ 2) ≤ B / (1 - B ^ 2) := by
  have hB0 : 0 ≤ B := le_trans hrp hrpB
  have h1 : 0 < 1 - B ^ 2 := by linarith
  have hsq : rp ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hrp hrpB 2
  have h2 : 0 < 1 - rp ^ 2 := by linarith
  rw [div_le_div_iff₀ h2 h1]
  nlinarith [mul_nonneg hrp hB0]

/-- `k^E_p = 3/(p - 3) = 3q/(1 - 3q)` at `q = 1/p` (`lem:record:exact-marginal-e`(i)). -/
theorem kEp_eq {p : ℝ} (hp : 3 < p) : kEp (1 / p) = 3 / (p - 3) := by
  have hp0 : p ≠ 0 := by linarith
  have hp3 : p - 3 ≠ 0 := by linarith
  unfold kEp
  field_simp

/-- **The centred parts of `K_1`** (`lem:record:exact-marginal-e`(i)): the centred operator of
`K^E_0` has norm `k^E_p`, the symmetric and skew parts of the difference have norms at most
`s^E_p` and `a^E_p` (hypotheses: `lem:record:e-law`(c), `lem:record:e-orthogonal`(c)); by the
triangle inequality the centred symmetric part of `K_1` has norm at most `c^s_E q = k^E_p + s^E_p`
and the centred operator of `K_1` norm at most `κ^E_p`. -/
theorem centred_K1 {q r nT nS nA nSymK1 nK1 : ℝ} (hq : 0 < q) (hT : nT ≤ kEp q)
    (hS : nS ≤ sEp q r) (hA : nA ≤ aEp q r) (hsym : nSymK1 ≤ nT + nS)
    (hK1 : nK1 ≤ nT + nS + nA) : nSymK1 ≤ csE q r * q ∧ nK1 ≤ kappaEp q r := by
  constructor
  · unfold csE
    rw [div_mul_cancel₀ _ hq.ne']
    linarith
  · unfold kappaEp
    linarith

/-! ## `lem:record:exact-marginal-e`(ii): the per-prime and sector bounds -/

/-- **The per-prime bounds** (`lem:record:exact-marginal-e`(ii), first sentence of the proof): for a
prime of the block, `q_p = r_p²`, `0 < q_p ≤ q_X ≤ 1/100`, `0 < r_p ≤ r_X`:
`s^E_p ≤ s_E(X) r_p`, `a^E_p ≤ a_E(X) r_p`, `k^E_p + s^E_p ≤ c^s_E(X) q_p` (the centred symmetric
part of `K_{1,p}`), `κ^E_p ≤ κ_E(X) r_p` and `k^E_p ≤ (3 r_X/(1 - 3 q_X)) r_p`. -/
theorem prime_bounds {qp rp qX rX : ℝ} (hrp : 0 < rp) (hqp : qp = rp ^ 2) (hqpX : qp ≤ qX)
    (hqX : qX ≤ 1 / 100) (hrpX : rp ≤ rX) :
    sEp qp rp ≤ sEX qX rX * rp ∧ aEp qp rp ≤ aEX qX * rp ∧
      kEp qp + sEp qp rp ≤ csEX qX rX * qp ∧ kappaEp qp rp ≤ kappaEX qX rX * rp ∧
      kEp qp ≤ 3 * rX / (1 - 3 * qX) * rp := by
  have hq0 : 0 < qp := by rw [hqp]; positivity
  have hq9 : qp < 1 / 9 := by linarith
  have hrp0 := hrp.le
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have e := sEp_div_r hrp hqp hq9
    have hm := sEX_mono hq0.le hqpX hqX hrp0 hrpX
    rw [div_eq_iff hrp.ne'] at e
    rw [e]
    exact mul_le_mul_of_nonneg_right hm hrp0
  · have e := aEp_div_r (q := qp) hrp.ne'
    have hm := aEX_mono hq0.le hqpX hqX
    rw [div_eq_iff hrp.ne'] at e
    rw [e]
    exact mul_le_mul_of_nonneg_right hm hrp0
  · have e := csE_eq rp hq0 hq9
    unfold csE at e
    rw [div_eq_iff hq0.ne'] at e
    rw [e]
    exact mul_le_mul_of_nonneg_right (csEX_mono hq0.le hqpX hqX hrp0 hrpX) hq0.le
  · have e := kappaEp_div_r hrp hqp hq9
    rw [div_eq_iff hrp.ne'] at e
    rw [e]
    exact mul_le_mul_of_nonneg_right (kappaEX_mono hq0.le hqpX hqX hrp0 hrpX) hrp0
  · have h3 : 0 < 1 - 3 * qX := by linarith
    have h3' : 0 < 1 - 3 * qp := by linarith
    have e : kEp qp = 3 * rp / (1 - 3 * qp) * rp := by
      unfold kEp
      rw [hqp]
      field_simp
    rw [e]
    apply mul_le_mul_of_nonneg_right _ hrp0
    gcongr
    mc_side

/-- **A sector of two primes, symmetric part** (`lem:record:exact-marginal-e`(ii)): with the centred
reference `‖T°_{0,p}‖ = t_p ≤ K r_p`, `K = 3 r_X/(1 - 3q_X)`, the symmetric and skew parts of the
prime difference `‖S°_p‖ = s_p ≤ s_E r_p`, `‖A°_p‖ = a_p ≤ a_E r_p` (and likewise at `p'`), the norm
bound `t_p s_{p'} + s_p t_{p'} + s_p s_{p'} + a_p a_{p'}` of
`T°_{0,p} ⊗ S°_{p'} + S°_p ⊗ T°_{0,p'} + S°_p ⊗ S°_{p'} + A°_p ⊗ A°_{p'}` (`lem:sector`(h), a
hypothesis) is at most `s^E_{(2)} r_p r_{p'}`, `s^E_{(2)} = 2K s_E + s_E² + a_E²`. -/
theorem sector_two_sym {K sE aE tp tp' sp sp' ap ap' rp rp' : ℝ} (hK : 0 ≤ K) (hsE : 0 ≤ sE)
    (haE : 0 ≤ aE) (hrp : 0 ≤ rp) (htp0' : 0 ≤ tp') (hsp0' : 0 ≤ sp') (hap0' : 0 ≤ ap')
    (htp : tp ≤ K * rp) (htp' : tp' ≤ K * rp') (hsp : sp ≤ sE * rp) (hsp' : sp' ≤ sE * rp')
    (hap : ap ≤ aE * rp) (hap' : ap' ≤ aE * rp') :
    tp * sp' + sp * tp' + sp * sp' + ap * ap' ≤ (2 * K * sE + sE ^ 2 + aE ^ 2) * (rp * rp') := by
  have e1 : tp * sp' ≤ K * rp * (sE * rp') := mul_le_mul htp hsp' hsp0' (by positivity)
  have e2 : sp * tp' ≤ sE * rp * (K * rp') := mul_le_mul hsp htp' htp0' (by positivity)
  have e3 : sp * sp' ≤ sE * rp * (sE * rp') := mul_le_mul hsp hsp' hsp0' (by positivity)
  have e4 : ap * ap' ≤ aE * rp * (aE * rp') := mul_le_mul hap hap' hap0' (by positivity)
  nlinarith

/-- **A sector of two primes, skew part**: `‖(T_{0,p} + S_p)°‖ ≤ c^s_E q_p`, `‖A°_p‖ ≤ a_E r_p`
give `c_p a_{p'} + a_p c_{p'} ≤ 2 c^s_E a_E b^{-3/2}` when `q_p ≤ 1/b`, `r_p ≤ b^{-1/2}` (here
`B = b^{-1/2}`, `B² = 1/b`). -/
theorem sector_two_skew {cs aE cp cp' ap ap' qp qp' rp rp' B : ℝ} (hcs : 0 ≤ cs) (haE : 0 ≤ aE)
    (hcp0' : 0 ≤ cp') (hap0' : 0 ≤ ap')
    (hqp0 : 0 ≤ qp) (hqp0' : 0 ≤ qp') (hrp0 : 0 ≤ rp) (hrp0' : 0 ≤ rp')
    (hcp : cp ≤ cs * qp) (hcp' : cp' ≤ cs * qp') (hap : ap ≤ aE * rp) (hap' : ap' ≤ aE * rp')
    (hqp : qp ≤ B ^ 2) (hqp' : qp' ≤ B ^ 2) (hrp : rp ≤ B) (hrp' : rp' ≤ B) :
    cp * ap' + ap * cp' ≤ 2 * cs * aE * B ^ 3 := by
  have hB : 0 ≤ B := le_trans hrp0 hrp
  have e1 : cp * ap' ≤ cs * qp * (aE * rp') := mul_le_mul hcp hap' hap0' (by positivity)
  have e2 : ap * cp' ≤ aE * rp * (cs * qp') := mul_le_mul hap hcp' hcp0' (by positivity)
  have f1 : qp * rp' ≤ B ^ 2 * B := mul_le_mul hqp hrp' hrp0' (sq_nonneg B)
  have f2 : rp * qp' ≤ B * B ^ 2 := mul_le_mul hrp hqp' hqp0' hB
  have g1 : cs * qp * (aE * rp') = cs * aE * (qp * rp') := by ring
  have g2 : aE * rp * (cs * qp') = cs * aE * (rp * qp') := by ring
  have hca : 0 ≤ cs * aE := mul_nonneg hcs haE
  have h1 := mul_le_mul_of_nonneg_left f1 hca
  have h2 := mul_le_mul_of_nonneg_left f2 hca
  have e : 2 * cs * aE * B ^ 3 = cs * aE * (B ^ 2 * B) + cs * aE * (B * B ^ 2) := by ring
  linarith

/-- **A sector of at least three primes, skew part**: the reference tensor is self-adjoint, so the
skew part is that of the new tensor, of norm at most `(κ_E B)³ = κ_E³ B³`, `B = b^{-1/2}`, which is
below `r_E B³` by the gate `κ_E³ < r_E`. -/
theorem sector_three_skew {κ rE B : ℝ} (hB : 0 < B) (hgate : κ ^ 3 < rE) :
    (κ * B) ^ 3 < rE * B ^ 3 := by
  rw [mul_pow]
  exact mul_lt_mul_of_pos_right hgate (pow_pos hB 3)

/-- **A sector of at least three primes, symmetric part**: at most the sum of the norms of the two
tensors, `(K B)³ + (κ_E B)³ = [K³ + κ_E³] B³ ≤ s^E_{(3)}/b` with `s^E_{(3)} = [K³ + κ_E³] r_X`,
`B ≤ r_X`, `B² = 1/b`. -/
theorem sector_three_sym {K κ B rX : ℝ} (hK : 0 ≤ K) (hκ : 0 ≤ κ) (hBr : B ≤ rX) :
    (K * B) ^ 3 + (κ * B) ^ 3 ≤ ((K ^ 3 + κ ^ 3) * rX) * B ^ 2 := by
  have e : (K * B) ^ 3 + (κ * B) ^ 3 = (K ^ 3 + κ ^ 3) * B * B ^ 2 := by ring
  rw [e]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg B)
  exact mul_le_mul_of_nonneg_left hBr (by positivity)

/-- **The final symmetric comparison** (`lem:record:exact-marginal-e`(ii), proof): since
`s^E_b ≥ 𝔰_b ≥ (1 + √2) q_b` (`frakS_ge`) and `s^E_b ≤ s_E(X) r_b` (`prime_bounds`), a sector
bound `s/b` with `s < 2` is below `s_E(X) b^{-1/2}`. Stated at the least prime `b` with
`q_b = 1/b = r_b²`. -/
theorem final_sym {qb rb qX rX s : ℝ} (hrb : 0 < rb) (hqb : qb = rb ^ 2) (hqbX : qb ≤ qX)
    (hqX : qX ≤ 1 / 100) (hrbX : rb ≤ rX) (hs : s < 2) :
    s * qb < sEX qX rX * rb := by
  have hq0 : 0 < qb := by rw [hqb]; positivity
  have h1 := frakS_ge hq0.le (le_trans hqbX hqX)
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h2 : frakS qb ≤ sEp qb rb := by
    have h1' : 0 < 1 - qb := by linarith
    have h2' : 0 < 1 - 2 * qb := by linarith
    have h3' : 0 < 1 - 3 * qb := by linarith
    have h9' : 0 < 1 - 9 * qb := by linarith
    have hT2 : 0 ≤ 2 * eE qb rb / (1 - 2 * qb) := by unfold eE; mc_side
    have hT3 : 0 ≤ qb ^ 2 / ((1 - qb) * (1 - 2 * qb)) := by mc_side
    have hT4 : 0 ≤ 18 * qb ^ 2 / ((1 - qb) * (1 - 9 * qb)) := by mc_side
    unfold sEp
    linarith
  have h3 := (prime_bounds hrb hqb hqbX hqX hrbX).1
  have h4 : s * qb < 2 * qb := mul_lt_mul_of_pos_right hs hq0
  nlinarith

/-- **The final skew comparison** (`lem:record:exact-marginal-e`(ii), proof):
`r_E B³ ≤ r_E r_X² B < B ≤ a_E B` for `B = b^{-1/2}`, `B² = 1/b ≤ r_X²`, under the gate
`r_E r_X² < 1` and `a_E ≥ 1`. -/
theorem final_skew {rE rX aE B : ℝ} (hrE : 0 ≤ rE) (hB : 0 < B) (hBr : B ^ 2 ≤ rX ^ 2)
    (hgate : rE * rX ^ 2 < 1) (haE : 1 ≤ aE) :
    rE * B ^ 3 ≤ rE * rX ^ 2 * B ∧ rE * rX ^ 2 * B < B ∧ B ≤ aE * B := by
  refine ⟨?_, ?_, ?_⟩
  · have e : rE * B ^ 3 = rE * B ^ 2 * B := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_right _ hB.le
    exact mul_le_mul_of_nonneg_left hBr hrE
  · nlinarith
  · nlinarith

/-! ## `lem:record:exact-marginal-e`(ii) on a block, given the sector decomposition -/

/-- `r_p = p^{-1/2}`, written `(√p)⁻¹`. -/
noncomputable def rP (p : ℝ) : ℝ := (Real.sqrt p)⁻¹

theorem rP_sq {p : ℝ} (hp : 0 < p) : rP p ^ 2 = 1 / p := by
  unfold rP
  rw [inv_pow, Real.sq_sqrt hp.le, one_div]

theorem rP_pos {p : ℝ} (hp : 0 < p) : 0 < rP p := inv_pos.mpr (Real.sqrt_pos.mpr hp)

theorem rP_anti {b p : ℝ} (hb : 0 < b) (hbp : b ≤ p) : rP p ≤ rP b := by
  unfold rP
  exact inv_anti₀ (Real.sqrt_pos.mpr hb) (Real.sqrt_le_sqrt hbp)

theorem kEp_nonneg {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 100) : 0 ≤ kEp q := by
  have h3 : 0 < 1 - 3 * q := by linarith
  unfold kEp
  mc_side

theorem sEp_nonneg {q r : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 100) (hr : 0 ≤ r) : 0 ≤ sEp q r := by
  have h1 : 0 < 1 - q := by linarith
  have h2 : 0 < 1 - 2 * q := by linarith
  have h3 : 0 < 1 - 3 * q := by linarith
  have h9 : 0 < 1 - 9 * q := by linarith
  have hZ : 0 < Zq q := mul_pos h1 h2
  unfold sEp frakS eE
  mc_side

theorem aEp_nonneg {q r : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 100) (hr : 0 ≤ r) : 0 ≤ aEp q r := by
  have h1 : 0 < 1 - q := by linarith
  have h2 : 0 < 1 - 2 * q := by linarith
  unfold aEp
  mc_side

/-- **The sector data of the block difference of a matching record**
(`lem:record:exact-marginal-e`(ii), proof), **with the sector decomposition and the one-prime
norms as hypotheses.** `S` is the set of primes of the block (as reals); `symN`, `skewN` are the
norms of the symmetric and skew parts of `⊗_p K_{1,p} - ⊗_p K^E_{0,p}` on `L²(⊗_p ν_{E,p})`, and
`symSec T`, `skewSec T` those of its restriction to the sector of exact support `T ≠ ∅`. Fields:
the block norms are at most every common bound of the sector norms (`lem:sector`(a), (b):
orthogonal invariant sectors); on a singleton the prime difference, with the norms `s^E_p`, `a^E_p`
of `lem:record:e-law`(c) and `lem:record:e-orthogonal`(c); on two primes the formulas of
`lem:sector`(h) with the norms `k^E_p` (centred reference), `s^E_p`, `a^E_p` and the centred
symmetric part `k^E_p + s^E_p` of `K_{1,p}` (norms of tensor products are products of norms); on
`≥ 3` primes the skew part is that of the new tensor (the reference tensor is self-adjoint), of
norm `∏ κ^E_p`, and the symmetric part is at most `∏ k^E_p + ∏ κ^E_p`. -/
structure MatchingSectorBounds (S : Finset ℝ) where
  symN : ℝ
  skewN : ℝ
  symSec : Finset ℝ → ℝ
  skewSec : Finset ℝ → ℝ
  sym_le : ∀ M : ℝ, 0 ≤ M → (∀ T ⊆ S, T.Nonempty → symSec T ≤ M) → symN ≤ M
  skew_le : ∀ M : ℝ, 0 ≤ M → (∀ T ⊆ S, T.Nonempty → skewSec T ≤ M) → skewN ≤ M
  sym_one : ∀ p ∈ S, symSec {p} ≤ sEp (1 / p) (rP p)
  skew_one : ∀ p ∈ S, skewSec {p} ≤ aEp (1 / p) (rP p)
  sym_two : ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → symSec {p, p'} ≤
    kEp (1 / p) * sEp (1 / p') (rP p') + sEp (1 / p) (rP p) * kEp (1 / p') +
      sEp (1 / p) (rP p) * sEp (1 / p') (rP p') + aEp (1 / p) (rP p) * aEp (1 / p') (rP p')
  skew_two : ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → skewSec {p, p'} ≤
    (kEp (1 / p) + sEp (1 / p) (rP p)) * aEp (1 / p') (rP p') +
      aEp (1 / p) (rP p) * (kEp (1 / p') + sEp (1 / p') (rP p'))
  skew_three : ∀ T ⊆ S, 3 ≤ T.card → skewSec T ≤ ∏ p ∈ T, kappaEp (1 / p) (rP p)
  sym_three : ∀ T ⊆ S, 3 ≤ T.card →
    symSec T ≤ (∏ p ∈ T, kEp (1 / p)) + ∏ p ∈ T, kappaEp (1 / p) (rP p)

/-- **`lem:record:exact-marginal-e`(ii), the block bounds, given the sector decomposition**: for a
block of a piece starting at `X ≥ 2^{20}` (`q_X = 1/X`), with `X^{-1/2} ≤ r_X ≤ 2^{-10}` (as for
`r_X = 1/⌊√X⌋` on the middle pieces) and every prime `p ≥ b ≥ X`, the symmetric and skew parts of
the block difference have norms at most `s_E(X) b^{-1/2}` and `a_E(X) b^{-1/2}`. The gates of (ii)
are discharged by `gates_hold`. -/
theorem matching_block_bounds {S : Finset ℝ} {b X rX : ℝ} (hX : 1048576 ≤ X) (hbX : X ≤ b)
    (hS : ∀ p ∈ S, b ≤ p) (hrX : rP X ≤ rX) (hrX' : rX ≤ 1 / 1024)
    (D : MatchingSectorBounds S) :
    D.symN ≤ sEX (1 / X) rX * rP b ∧ D.skewN ≤ aEX (1 / X) * rP b := by
  have hX0 : 0 < X := by linarith
  have hb0 : 0 < b := by linarith
  set qX : ℝ := 1 / X with hqXdef
  set B : ℝ := rP b with hBdef
  have hqX0 : 0 ≤ qX := by positivity
  have hqX : qX ≤ 1 / 1048576 := by
    rw [hqXdef]
    exact one_div_le_one_div_of_le (by norm_num) hX
  have hqX100 : qX ≤ 1 / 100 := by linarith
  have hB0 : 0 < B := rP_pos hb0
  have hBX : B ≤ rX := le_trans (rP_anti hX0 hbX) hrX
  have hrX0 : 0 ≤ rX := le_trans hB0.le hBX
  have hB2 : B ^ 2 = 1 / b := rP_sq hb0
  have hqbX : 1 / b ≤ qX := one_div_le_one_div_of_le hX0 hbX
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := gates_hold hqX0 hqX hrX0 hrX'
  -- per-prime data
  have hp0 : ∀ p ∈ S, 0 < p := fun p hp => lt_of_lt_of_le hb0 (hS p hp)
  have hpb : ∀ p ∈ S, rP p ≤ B := fun p hp => rP_anti hb0 (hS p hp)
  have hpq : ∀ p ∈ S, 1 / p ≤ qX := fun p hp =>
    le_trans (one_div_le_one_div_of_le hb0 (hS p hp)) hqbX
  have hpr : ∀ p ∈ S, rP p ≤ rX := fun p hp => le_trans (hpb p hp) hBX
  have hPB : ∀ p ∈ S, sEp (1 / p) (rP p) ≤ sEX qX rX * rP p ∧ aEp (1 / p) (rP p) ≤ aEX qX * rP p ∧
      kEp (1 / p) + sEp (1 / p) (rP p) ≤ csEX qX rX * (1 / p) ∧
      kappaEp (1 / p) (rP p) ≤ kappaEX qX rX * rP p ∧
      kEp (1 / p) ≤ 3 * rX / (1 - 3 * qX) * rP p := fun p hp =>
    prime_bounds (rP_pos (hp0 p hp)) (rP_sq (hp0 p hp)).symm (hpq p hp) hqX100 (hpr p hp)
  have hq0 : ∀ p ∈ S, 0 ≤ 1 / p := fun p hp => (one_div_pos.mpr (hp0 p hp)).le
  have hq100 : ∀ p ∈ S, 1 / p ≤ 1 / 100 := fun p hp => le_trans (hpq p hp) hqX100
  have hr0 : ∀ p ∈ S, 0 ≤ rP p := fun p hp => (rP_pos (hp0 p hp)).le
  have hk0 : ∀ p ∈ S, 0 ≤ kEp (1 / p) := fun p hp => kEp_nonneg (hq0 p hp) (hq100 p hp)
  have hs0 : ∀ p ∈ S, 0 ≤ sEp (1 / p) (rP p) := fun p hp =>
    sEp_nonneg (hq0 p hp) (hq100 p hp) (hr0 p hp)
  have ha0 : ∀ p ∈ S, 0 ≤ aEp (1 / p) (rP p) := fun p hp =>
    aEp_nonneg (hq0 p hp) (hq100 p hp) (hr0 p hp)
  have hκ0 : ∀ p ∈ S, 0 ≤ kappaEp (1 / p) (rP p) := fun p hp => by
    unfold kappaEp
    linarith [hk0 p hp, hs0 p hp, ha0 p hp]
  have hsE0 : 0 ≤ sEX qX rX := by
    have h1 : 0 < 1 - qX := by linarith
    have h2 : 0 < 1 - 2 * qX := by linarith
    have h3 : 0 < 1 - 3 * qX := by linarith
    have h9 : 0 < 1 - 9 * qX := by linarith
    have hZ : 0 < Zq qX := mul_pos h1 h2
    unfold sEX
    mc_side
  have haE1 : 1 ≤ aEX qX := aEX_ge_one hqX0 hqX100
  have hcs0 : 0 ≤ csEX qX rX := csEX_nonneg hqX0 hqX100 hrX0
  have h3X : 0 < 1 - 3 * qX := by linarith
  have hK0 : 0 ≤ 3 * rX / (1 - 3 * qX) := div_nonneg (by linarith) h3X.le
  have hκX0 : 0 ≤ kappaEX qX rX := by
    unfold kappaEX
    linarith
  have hrE0 : 0 ≤ rEX qX rX := by unfold rEX; positivity
  -- `κ_E B ≤ 1` and `K B ≤ 1`
  have hκB : kappaEX qX rX * B ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hBX hκX0
    linarith
  have hKB : 3 * rX / (1 - 3 * qX) * B ≤ 1 := by
    have hK1 : 3 * rX / (1 - 3 * qX) ≤ 1 := by
      rw [div_le_one h3X]
      linarith
    have := mul_le_mul hK1 hBX hB0.le zero_le_one
    linarith
  -- the final comparisons
  have hfs : ∀ s : ℝ, s < 2 → s * (1 / b) < sEX qX rX * B := fun s hs =>
    final_sym hB0 hB2.symm hqbX hqX100 hBX hs
  obtain ⟨fk1, fk2, fk3⟩ := final_skew hrE0 hB0 (pow_le_pow_left₀ hB0.le hBX 2) g3 haE1
  constructor
  · apply D.sym_le _ (mul_nonneg hsE0 hB0.le)
    intro T hT hne
    rcases Nat.lt_or_ge T.card 2 with h | h
    · have hc : T.card = 1 := by
        have := hne.card_pos
        omega
      obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hc
      have hp := hT (Finset.mem_singleton_self p)
      calc D.symSec {p} ≤ sEp (1 / p) (rP p) := D.sym_one p hp
        _ ≤ sEX qX rX * rP p := (hPB p hp).1
        _ ≤ sEX qX rX * B := mul_le_mul_of_nonneg_left (hpb p hp) hsE0
    · rcases Nat.lt_or_ge T.card 3 with h' | h'
      · have hc : T.card = 2 := by omega
        obtain ⟨p, p', hpp, rfl⟩ := Finset.card_eq_two.mp hc
        have hp : p ∈ S := hT (by simp)
        have hp' : p' ∈ S := hT (by simp)
        have hsec := sector_two_sym hK0 hsE0 (le_trans zero_le_one haE1) (hr0 p hp) (hk0 p' hp')
          (hs0 p' hp') (ha0 p' hp') (hPB p hp).2.2.2.2 (hPB p' hp').2.2.2.2 (hPB p hp).1
          (hPB p' hp').1 (hPB p hp).2.1 (hPB p' hp').2.1
        have hrr : rP p * rP p' ≤ 1 / b := by
          rw [← hB2, sq]
          exact mul_le_mul (hpb p hp) (hpb p' hp') (hr0 p' hp') hB0.le
        have hs2 : 0 ≤ 2 * (3 * rX / (1 - 3 * qX)) * sEX qX rX + sEX qX rX ^ 2 +
            aEX qX ^ 2 := by positivity
        have e6 : 2 * (3 * rX / (1 - 3 * qX)) * sEX qX rX = 6 * rX / (1 - 3 * qX) * sEX qX rX := by
          ring
        have hlt := hfs (2 * (3 * rX / (1 - 3 * qX)) * sEX qX rX + sEX qX rX ^ 2 + aEX qX ^ 2)
          (by rw [e6]; exact g6)
        calc D.symSec {p, p'} ≤ _ := D.sym_two p hp p' hp' hpp
          _ ≤ _ := hsec
          _ ≤ (2 * (3 * rX / (1 - 3 * qX)) * sEX qX rX + sEX qX rX ^ 2 + aEX qX ^ 2) *
              (1 / b) := mul_le_mul_of_nonneg_left hrr hs2
          _ ≤ sEX qX rX * B := hlt.le
      · have hprodK : ∏ p ∈ T, kEp (1 / p) ≤ (3 * rX / (1 - 3 * qX) * B) ^ 3 := by
          calc ∏ p ∈ T, kEp (1 / p) ≤ ∏ _p ∈ T, (3 * rX / (1 - 3 * qX) * B) :=
                Finset.prod_le_prod₀ (fun p hp => hk0 p (hT hp)) (fun p hp =>
                  le_trans (hPB p (hT hp)).2.2.2.2
                    (mul_le_mul_of_nonneg_left (hpb p (hT hp)) hK0))
            _ = (3 * rX / (1 - 3 * qX) * B) ^ T.card := Finset.prod_const _
            _ ≤ (3 * rX / (1 - 3 * qX) * B) ^ 3 :=
                pow_le_pow_of_le_one (mul_nonneg hK0 hB0.le) hKB h'
        have hprodκ : ∏ p ∈ T, kappaEp (1 / p) (rP p) ≤ (kappaEX qX rX * B) ^ 3 := by
          calc ∏ p ∈ T, kappaEp (1 / p) (rP p) ≤ ∏ _p ∈ T, (kappaEX qX rX * B) :=
                Finset.prod_le_prod₀ (fun p hp => hκ0 p (hT hp)) (fun p hp =>
                  le_trans (hPB p (hT hp)).2.2.2.1
                    (mul_le_mul_of_nonneg_left (hpb p (hT hp)) hκX0))
            _ = (kappaEX qX rX * B) ^ T.card := Finset.prod_const _
            _ ≤ (kappaEX qX rX * B) ^ 3 := pow_le_pow_of_le_one (mul_nonneg hκX0 hB0.le) hκB h'
        have h3s := sector_three_sym hK0 hκX0 hBX
        have hlt := hfs _ g7
        rw [hB2] at h3s
        calc D.symSec T ≤ _ := D.sym_three T hT h'
          _ ≤ (3 * rX / (1 - 3 * qX) * B) ^ 3 + (kappaEX qX rX * B) ^ 3 := add_le_add hprodK hprodκ
          _ ≤ _ := h3s
          _ ≤ sEX qX rX * B := hlt.le
  · apply D.skew_le _ (mul_nonneg (le_trans zero_le_one haE1) hB0.le)
    intro T hT hne
    rcases Nat.lt_or_ge T.card 2 with h | h
    · have hc : T.card = 1 := by
        have := hne.card_pos
        omega
      obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hc
      have hp := hT (Finset.mem_singleton_self p)
      calc D.skewSec {p} ≤ aEp (1 / p) (rP p) := D.skew_one p hp
        _ ≤ aEX qX * rP p := (hPB p hp).2.1
        _ ≤ aEX qX * B := mul_le_mul_of_nonneg_left (hpb p hp) (le_trans zero_le_one haE1)
    · rcases Nat.lt_or_ge T.card 3 with h' | h'
      · have hc : T.card = 2 := by omega
        obtain ⟨p, p', hpp, rfl⟩ := Finset.card_eq_two.mp hc
        have hp : p ∈ S := hT (by simp)
        have hp' : p' ∈ S := hT (by simp)
        have hqb : ∀ p ∈ S, 1 / p ≤ B ^ 2 := fun p hp => by
          rw [hB2]
          exact one_div_le_one_div_of_le hb0 (hS p hp)
        have hsec := sector_two_skew hcs0 (le_trans zero_le_one haE1)
          (add_nonneg (hk0 p' hp') (hs0 p' hp')) (ha0 p' hp') (hq0 p hp) (hq0 p' hp')
          (hr0 p hp) (hr0 p' hp') (hPB p hp).2.2.1 (hPB p' hp').2.2.1 (hPB p hp).2.1
          (hPB p' hp').2.1
          (hqb p hp) (hqb p' hp') (hpb p hp) (hpb p' hp')
        have e : 2 * csEX qX rX * aEX qX * B ^ 3 = rEX qX rX * B ^ 3 := by
          unfold rEX
          ring
        calc D.skewSec {p, p'} ≤ _ := D.skew_two p hp p' hp' hpp
          _ ≤ _ := hsec
          _ = rEX qX rX * B ^ 3 := e
          _ ≤ aEX qX * B := by linarith
      · have hprodκ : ∏ p ∈ T, kappaEp (1 / p) (rP p) ≤ (kappaEX qX rX * B) ^ 3 := by
          calc ∏ p ∈ T, kappaEp (1 / p) (rP p) ≤ ∏ _p ∈ T, (kappaEX qX rX * B) :=
                Finset.prod_le_prod₀ (fun p hp => hκ0 p (hT hp)) (fun p hp =>
                  le_trans (hPB p (hT hp)).2.2.2.1
                    (mul_le_mul_of_nonneg_left (hpb p (hT hp)) hκX0))
            _ = (kappaEX qX rX * B) ^ T.card := Finset.prod_const _
            _ ≤ (kappaEX qX rX * B) ^ 3 := pow_le_pow_of_le_one (mul_nonneg hκX0 hB0.le) hκB h'
        have h3k := sector_three_skew hB0 g5
        calc D.skewSec T ≤ _ := D.skew_three T hT h'
          _ ≤ (kappaEX qX rX * B) ^ 3 := hprodκ
          _ ≤ rEX qX rX * B ^ 3 := h3k.le
          _ ≤ aEX qX * B := by linarith

/-- **The skew part on a sector of at least two primes** (`lem:record:exact-marginal-e`(ii), proof):
at most `r_E(X) b^{-3/2}`. -/
theorem matching_block_skew_sector {S : Finset ℝ} {b X rX : ℝ} (hX : 1048576 ≤ X) (hbX : X ≤ b)
    (hS : ∀ p ∈ S, b ≤ p) (hrX : rP X ≤ rX) (hrX' : rX ≤ 1 / 1024)
    (D : MatchingSectorBounds S) (T : Finset ℝ) (hT : T ⊆ S) (h2 : 2 ≤ T.card) :
    D.skewSec T ≤ rEX (1 / X) rX * rP b ^ 3 := by
  have hX0 : 0 < X := by linarith
  have hb0 : 0 < b := by linarith
  set qX : ℝ := 1 / X with hqXdef
  set B : ℝ := rP b with hBdef
  have hqX0 : 0 ≤ qX := by positivity
  have hqX : qX ≤ 1 / 1048576 := by
    rw [hqXdef]
    exact one_div_le_one_div_of_le (by norm_num) hX
  have hqX100 : qX ≤ 1 / 100 := by linarith
  have hB0 : 0 < B := rP_pos hb0
  have hBX : B ≤ rX := le_trans (rP_anti hX0 hbX) hrX
  have hrX0 : 0 ≤ rX := le_trans hB0.le hBX
  have hB2 : B ^ 2 = 1 / b := rP_sq hb0
  have hqbX : 1 / b ≤ qX := one_div_le_one_div_of_le hX0 hbX
  obtain ⟨-, -, -, -, g5, -, -⟩ := gates_hold hqX0 hqX hrX0 hrX'
  have hp0 : ∀ p ∈ S, 0 < p := fun p hp => lt_of_lt_of_le hb0 (hS p hp)
  have hpb : ∀ p ∈ S, rP p ≤ B := fun p hp => rP_anti hb0 (hS p hp)
  have hpq : ∀ p ∈ S, 1 / p ≤ qX := fun p hp =>
    le_trans (one_div_le_one_div_of_le hb0 (hS p hp)) hqbX
  have hpr : ∀ p ∈ S, rP p ≤ rX := fun p hp => le_trans (hpb p hp) hBX
  have hPB : ∀ p ∈ S, sEp (1 / p) (rP p) ≤ sEX qX rX * rP p ∧ aEp (1 / p) (rP p) ≤ aEX qX * rP p ∧
      kEp (1 / p) + sEp (1 / p) (rP p) ≤ csEX qX rX * (1 / p) ∧
      kappaEp (1 / p) (rP p) ≤ kappaEX qX rX * rP p ∧
      kEp (1 / p) ≤ 3 * rX / (1 - 3 * qX) * rP p := fun p hp =>
    prime_bounds (rP_pos (hp0 p hp)) (rP_sq (hp0 p hp)).symm (hpq p hp) hqX100 (hpr p hp)
  have hq0 : ∀ p ∈ S, 0 ≤ 1 / p := fun p hp => (one_div_pos.mpr (hp0 p hp)).le
  have hq100 : ∀ p ∈ S, 1 / p ≤ 1 / 100 := fun p hp => le_trans (hpq p hp) hqX100
  have hr0 : ∀ p ∈ S, 0 ≤ rP p := fun p hp => (rP_pos (hp0 p hp)).le
  have hk0 : ∀ p ∈ S, 0 ≤ kEp (1 / p) := fun p hp => kEp_nonneg (hq0 p hp) (hq100 p hp)
  have hs0 : ∀ p ∈ S, 0 ≤ sEp (1 / p) (rP p) := fun p hp =>
    sEp_nonneg (hq0 p hp) (hq100 p hp) (hr0 p hp)
  have ha0 : ∀ p ∈ S, 0 ≤ aEp (1 / p) (rP p) := fun p hp =>
    aEp_nonneg (hq0 p hp) (hq100 p hp) (hr0 p hp)
  have hκ0 : ∀ p ∈ S, 0 ≤ kappaEp (1 / p) (rP p) := fun p hp => by
    unfold kappaEp
    linarith [hk0 p hp, hs0 p hp, ha0 p hp]
  have haE1 : 1 ≤ aEX qX := aEX_ge_one hqX0 hqX100
  have hcs0 : 0 ≤ csEX qX rX := csEX_nonneg hqX0 hqX100 hrX0
  have hsE0 : 0 ≤ sEX qX rX := by
    have h1 : 0 < 1 - qX := by linarith
    have h2 : 0 < 1 - 2 * qX := by linarith
    have h3 : 0 < 1 - 3 * qX := by linarith
    have h9 : 0 < 1 - 9 * qX := by linarith
    have hZ : 0 < Zq qX := mul_pos h1 h2
    unfold sEX
    mc_side
  have h3X : 0 < 1 - 3 * qX := by linarith
  have hκX0 : 0 ≤ kappaEX qX rX := by
    have hK0 : 0 ≤ 3 * rX / (1 - 3 * qX) := div_nonneg (by linarith) h3X.le
    unfold kappaEX
    linarith
  have hκB : kappaEX qX rX * B ≤ 1 := by
    obtain ⟨-, g2, -⟩ := gates_hold hqX0 hqX hrX0 hrX'
    have := mul_le_mul_of_nonneg_left hBX hκX0
    linarith
  rcases Nat.lt_or_ge T.card 3 with h' | h'
  · have hc : T.card = 2 := by omega
    obtain ⟨p, p', hpp, rfl⟩ := Finset.card_eq_two.mp hc
    have hp : p ∈ S := hT (by simp)
    have hp' : p' ∈ S := hT (by simp)
    have hqb : ∀ p ∈ S, 1 / p ≤ B ^ 2 := fun p hp => by
      rw [hB2]
      exact one_div_le_one_div_of_le hb0 (hS p hp)
    have hsec := sector_two_skew hcs0 (le_trans zero_le_one haE1)
      (add_nonneg (hk0 p' hp') (hs0 p' hp')) (ha0 p' hp') (hq0 p hp) (hq0 p' hp')
      (hr0 p hp) (hr0 p' hp') (hPB p hp).2.2.1 (hPB p' hp').2.2.1 (hPB p hp).2.1 (hPB p' hp').2.1
      (hqb p hp) (hqb p' hp') (hpb p hp) (hpb p' hp')
    have e : 2 * csEX qX rX * aEX qX * B ^ 3 = rEX qX rX * B ^ 3 := by
      unfold rEX
      ring
    calc D.skewSec {p, p'} ≤ _ := D.skew_two p hp p' hp' hpp
      _ ≤ _ := hsec
      _ = rEX qX rX * B ^ 3 := e
  · have hprodκ : ∏ p ∈ T, kappaEp (1 / p) (rP p) ≤ (kappaEX qX rX * B) ^ 3 := by
      calc ∏ p ∈ T, kappaEp (1 / p) (rP p) ≤ ∏ _p ∈ T, (kappaEX qX rX * B) :=
            Finset.prod_le_prod₀ (fun p hp => hκ0 p (hT hp)) (fun p hp =>
              le_trans (hPB p (hT hp)).2.2.2.1
                (mul_le_mul_of_nonneg_left (hpb p (hT hp)) hκX0))
        _ = (kappaEX qX rX * B) ^ T.card := Finset.prod_const _
        _ ≤ (kappaEX qX rX * B) ^ 3 := pow_le_pow_of_le_one (mul_nonneg hκX0 hB0.le) hκB h'
    have h3k := sector_three_skew hB0 g5
    calc D.skewSec T ≤ _ := D.skew_three T hT h'
      _ ≤ (kappaEX qX rX * B) ^ 3 := hprodκ
      _ ≤ rEX qX rX * B ^ 3 := h3k.le

/-- **`lem:oct24:matching-star` on a block, given the sector decomposition.** Write the skew part of
the block difference as `L_{E,𝔅} + R_{E,𝔅}`, where `L_{E,𝔅}` is `L_{E,p} = C + D` on the sector
`{p}` and zero on the other sectors. With the sector data `D` of `MatchingSectorBounds`, suppose
(hypotheses, with the paper's reasons) that the block norms of `L` and `R` are at most every common
bound of their sector norms `leadSec`, `remSec` (orthogonal sectors); that on a singleton
`‖L_{E,p}‖ = r_p/(1 - q_p)` (`lem:record:e-law`(c)) and `‖R‖ = ‖D^a_{E,p} - L_{E,p}‖ ≤
4 q_p r_p/((1 - q_p)(1 - 2q_p))` (`matching_remainder`); and that on the sectors of size `≥ 2`
`L` vanishes and `R` is the skew part of the difference. Then `‖L_{E,𝔅}‖ ≤ b^{-1/2}/(1 - b^{-1})`
and `‖R_{E,𝔅}‖ ≤ r_E(X) b^{-3/2}`. -/
theorem matching_star_block {S : Finset ℝ} {b X rX leadN remN : ℝ} (hX : 1048576 ≤ X)
    (hbX : X ≤ b) (hS : ∀ p ∈ S, b ≤ p) (hrX : rP X ≤ rX) (hrX' : rX ≤ 1 / 1024)
    (D : MatchingSectorBounds S) (leadSec remSec : Finset ℝ → ℝ)
    (hlead_le : ∀ M : ℝ, 0 ≤ M → (∀ T ⊆ S, T.Nonempty → leadSec T ≤ M) → leadN ≤ M)
    (hrem_le : ∀ M : ℝ, 0 ≤ M → (∀ T ⊆ S, T.Nonempty → remSec T ≤ M) → remN ≤ M)
    (hlead_one : ∀ p ∈ S, leadSec {p} = rP p / (1 - rP p ^ 2))
    (hlead_two : ∀ T ⊆ S, 2 ≤ T.card → leadSec T = 0)
    (hrem_one : ∀ p ∈ S, remSec {p} ≤ 4 * (1 / p) * rP p / ((1 - 1 / p) * (1 - 2 * (1 / p))))
    (hrem_two : ∀ T ⊆ S, 2 ≤ T.card → remSec T ≤ D.skewSec T) :
    leadN ≤ rP b / (1 - rP b ^ 2) ∧ remN ≤ rEX (1 / X) rX * rP b ^ 3 := by
  have hX0 : 0 < X := by linarith
  have hb0 : 0 < b := by linarith
  set qX : ℝ := 1 / X with hqXdef
  set B : ℝ := rP b with hBdef
  have hqX0 : 0 ≤ qX := by positivity
  have hqX : qX ≤ 1 / 1048576 := by
    rw [hqXdef]
    exact one_div_le_one_div_of_le (by norm_num) hX
  have hqX100 : qX ≤ 1 / 100 := by linarith
  have hB0 : 0 < B := rP_pos hb0
  have hBX : B ≤ rX := le_trans (rP_anti hX0 hbX) hrX
  have hrX0 : 0 ≤ rX := le_trans hB0.le hBX
  have hB2 : B ^ 2 = 1 / b := rP_sq hb0
  have hB21 : B ^ 2 < 1 := by
    rw [hB2, div_lt_one hb0]
    linarith
  have hqbX : 1 / b ≤ qX := one_div_le_one_div_of_le hX0 hbX
  obtain ⟨-, -, g3, g4, g5, -, -⟩ := gates_hold hqX0 hqX hrX0 hrX'
  have hrE0 : 0 ≤ rEX qX rX := by
    have := csEX_nonneg hqX0 hqX100 hrX0
    have := aEX_nonneg hqX0 hqX100
    unfold rEX
    positivity
  have hpb : ∀ p ∈ S, rP p ≤ B := fun p hp => rP_anti hb0 (hS p hp)
  have hp0 : ∀ p ∈ S, 0 < p := fun p hp => lt_of_lt_of_le hb0 (hS p hp)
  constructor
  · apply hlead_le _ (div_nonneg hB0.le (by linarith))
    intro T hT hne
    rcases Nat.lt_or_ge T.card 2 with h | h
    · have hc : T.card = 1 := by
        have := hne.card_pos
        omega
      obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hc
      have hp := hT (Finset.mem_singleton_self p)
      rw [hlead_one p hp]
      exact leading_norm_le (rP_pos (hp0 p hp)).le (hpb p hp) hB21
    · rw [hlead_two T hT h]
      exact div_nonneg hB0.le (by linarith)
  · apply hrem_le _ (mul_nonneg hrE0 (pow_nonneg hB0.le 3))
    intro T hT hne
    rcases Nat.lt_or_ge T.card 2 with h | h
    · have hc : T.card = 1 := by
        have := hne.card_pos
        omega
      obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hc
      have hp := hT (Finset.mem_singleton_self p)
      have hqp0 : 0 ≤ 1 / p := (one_div_pos.mpr (hp0 p hp)).le
      have hqpX : 1 / p ≤ qX := le_trans (one_div_le_one_div_of_le hb0 (hS p hp)) hqbX
      have hlt := matching_remainder_lt hqp0 hqpX (by linarith) (rP_pos (hp0 p hp)).le g4
      have hqr : 1 / p * rP p ≤ B ^ 3 := by
        have h1 : 1 / p ≤ B ^ 2 := by
          rw [hB2]
          exact one_div_le_one_div_of_le hb0 (hS p hp)
        calc 1 / p * rP p ≤ B ^ 2 * B :=
              mul_le_mul h1 (hpb p hp) (rP_pos (hp0 p hp)).le (sq_nonneg B)
          _ = B ^ 3 := by ring
      calc remSec {p} ≤ _ := hrem_one p hp
        _ ≤ rEX qX rX * (1 / p * rP p) := hlt
        _ ≤ rEX qX rX * B ^ 3 := mul_le_mul_of_nonneg_left hqr hrE0
    · -- on the sectors of size `≥ 2`, `R` is the skew part (`matching_block_skew_sector`)
      refine le_trans (hrem_two T hT h) ?_
      have hS' := matching_block_skew_sector hX hbX hS hrX hrX' D T hT h
      exact hS'

/-- **Non-vacuity of `MatchingSectorBounds`**: with every sector norm zero the bundle holds for any
set of primes `p ≥ 100`. -/
noncomputable def matchingSectorBounds_toy (S : Finset ℝ) (hS : ∀ p ∈ S, 100 ≤ p) :
    MatchingSectorBounds S :=
  have hq0 : ∀ p ∈ S, 0 ≤ 1 / p := fun p hp => by
    have : 0 < p := by linarith [hS p hp]
    positivity
  have hq1 : ∀ p ∈ S, 1 / p ≤ 1 / 100 := fun p hp =>
    one_div_le_one_div_of_le (by norm_num) (hS p hp)
  have hr0 : ∀ p ∈ S, 0 ≤ rP p := fun p hp => (rP_pos (by linarith [hS p hp])).le
  have hk : ∀ p ∈ S, 0 ≤ kEp (1 / p) := fun p hp => kEp_nonneg (hq0 p hp) (hq1 p hp)
  have hs : ∀ p ∈ S, 0 ≤ sEp (1 / p) (rP p) := fun p hp =>
    sEp_nonneg (hq0 p hp) (hq1 p hp) (hr0 p hp)
  have ha : ∀ p ∈ S, 0 ≤ aEp (1 / p) (rP p) := fun p hp =>
    aEp_nonneg (hq0 p hp) (hq1 p hp) (hr0 p hp)
  have hκ : ∀ p ∈ S, 0 ≤ kappaEp (1 / p) (rP p) := fun p hp => by
    unfold kappaEp
    linarith [hk p hp, hs p hp, ha p hp]
  { symN := 0
    skewN := 0
    symSec := fun _ => 0
    skewSec := fun _ => 0
    sym_le := fun _ hM _ => hM
    skew_le := fun _ hM _ => hM
    sym_one := fun p hp => hs p hp
    skew_one := fun p hp => ha p hp
    sym_two := fun p hp p' hp' _ => by
      have := mul_nonneg (hk p hp) (hs p' hp')
      have := mul_nonneg (hs p hp) (hk p' hp')
      have := mul_nonneg (hs p hp) (hs p' hp')
      have := mul_nonneg (ha p hp) (ha p' hp')
      linarith
    skew_two := fun p hp p' hp' _ => by
      have := mul_nonneg (add_nonneg (hk p hp) (hs p hp)) (ha p' hp')
      have := mul_nonneg (ha p hp) (add_nonneg (hk p' hp') (hs p' hp'))
      linarith
    skew_three := fun _ hT _ => Finset.prod_nonneg fun p hp => hκ p (hT hp)
    sym_three := fun _ hT _ => add_nonneg (Finset.prod_nonneg fun p hp => hk p (hT hp))
      (Finset.prod_nonneg fun p hp => hκ p (hT hp)) }

/-! ## `cert:record:e-coefficients`: the two printed rows -/

/-- `⌊√Q₃⌋ = 4466`, so `r_{Q₃} = 1/⌊√Q₃⌋ = 1/4466`. -/
theorem isqrt_Q3 : Nat.sqrt 19951586 = 4466 :=
  (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩).symm

/-- `⌊√(2^{45})⌋ = 5931641`. -/
theorem isqrt_two_pow_45 : Nat.sqrt (2 ^ 45) = 5931641 :=
  (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩).symm

/-- `√2 ≤ 1.41421356237310`. -/
theorem sqrt_two_le_tight : Real.sqrt 2 ≤ 141421356237310 / 100000000000000 := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num

/-- **Outward evaluation of the coefficients at a point** (used for the rows of
`cert:record:e-coefficients`): if `√((1 - q)(1 - 3q)) ≥ L` and `√(2 + 4q²/(1 - 2q)²) ≤ U`, the
coefficients `s_E` and `r_E` are at most the displayed rational expressions in `q, r, L, U`
(with `√2 ≤ 1.41421356237310`). -/
theorem coeff_bounds {q r L U : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 100) (hr : 0 ≤ r) (hL : 0 < L)
    (hLs : L ≤ Real.sqrt ((1 - q) * (1 - 3 * q)))
    (hUs : Real.sqrt (2 + 4 * q ^ 2 / (1 - 2 * q) ^ 2) ≤ U) :
    sEX q r ≤ r * (1 / (1 - q) * ((1 + 141421356237310 / 100000000000000) / (1 - 9 * q) +
        7 * q / ((1 - q) * (1 - 2 * q) * (1 - 9 * q) * (1 - 2 * q)))) +
      2 * q / ((1 - 2 * q) * L) * U +
      q * r / ((1 - q) * (1 - 2 * q)) + 18 * q * r / ((1 - q) * (1 - 9 * q)) ∧
    rEX q r ≤ 2 * (3 / (1 - 3 * q) +
      (1 / (1 - q) * ((1 + 141421356237310 / 100000000000000) / (1 - 9 * q) +
        7 * q / ((1 - q) * (1 - 2 * q) * (1 - 9 * q) * (1 - 2 * q))) +
      2 * r / ((1 - 2 * q) * L) * U +
      q / ((1 - q) * (1 - 2 * q)) + 18 * q / ((1 - q) * (1 - 9 * q)))) * aEX q := by
  have hs2 := sqrt_two_le_tight
  have h1 : 0 < 1 - q := by linarith
  have h2 : 0 < 1 - 2 * q := by linarith
  have h3 : 0 < 1 - 3 * q := by linarith
  have h9 : 0 < 1 - 9 * q := by linarith
  have hZ : 0 < Zq q := mul_pos h1 h2
  have ha0 : 0 ≤ aEX q := aEX_nonneg hq hq'
  constructor
  · unfold sEX Zq
    gcongr
  · unfold rEX csEX sEq Zq
    gcongr

theorem sEX_nonneg {q r : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 100) (hr : 0 ≤ r) : 0 ≤ sEX q r := by
  have h1 : 0 < 1 - q := by linarith
  have h2 : 0 < 1 - 2 * q := by linarith
  have h3 : 0 < 1 - 3 * q := by linarith
  have h9 : 0 < 1 - 9 * q := by linarith
  have hZ : 0 < Zq q := mul_pos h1 h2
  unfold sEX
  mc_side

theorem cert_e_Q3_aux {q r : ℝ} (hq : q = 1 / 19951586) (hr : r = 1 / 4466) :
    sEX q r ≤ 54071859 / 100000000000 ∧ aEX q ≤ 1 + 251 / 1000000000 ∧
      kappaEX q r ≤ 10012128 / 10000000 ∧ rEX q r ≤ 10829703 / 1000000 ∧
      6 * r / (1 - 3 * q) * sEX q r + sEX q r ^ 2 + aEX q ^ 2 ≤ 10000016 / 10000000 ∧
      ((3 * r / (1 - 3 * q)) ^ 3 + kappaEX q r ^ 3) * r ≤ 2248 / 10000000 := by
  have hq0 : 0 ≤ q := by rw [hq]; norm_num
  have hq1 : q ≤ 1 / 100 := by rw [hq]; norm_num
  have hr0 : 0 ≤ r := by rw [hr]; norm_num
  have hsA : 9999998 / 10000000 ≤ Real.sqrt ((1 - q) * (1 - 3 * q)) := by
    rw [Real.le_sqrt (by norm_num) (by rw [hq]; norm_num), hq]
    norm_num
  have hsB : Real.sqrt (2 + 4 * q ^ 2 / (1 - 2 * q) ^ 2) ≤ 14142136 / 10000000 := by
    rw [Real.sqrt_le_left (by norm_num), hq]
    norm_num
  obtain ⟨hb1, hb2⟩ := coeff_bounds hq0 hq1 hr0 (by norm_num) hsA hsB
  have hsE : sEX q r ≤ 54071859 / 100000000000 := by
    refine le_trans hb1 ?_
    rw [hq, hr]
    norm_num
  have hsE0 : 0 ≤ sEX q r := sEX_nonneg hq0 hq1 hr0
  have haE : aEX q ≤ 1 + 251 / 1000000000 := by
    unfold aEX
    rw [hq]
    norm_num
  have haE0 : 0 ≤ aEX q := aEX_nonneg hq0 hq1
  have hK : 3 * r / (1 - 3 * q) = 29927379 / 44551884839 := by
    rw [hq, hr]
    norm_num
  have hκ : kappaEX q r ≤ 10012128 / 10000000 := by
    unfold kappaEX
    rw [hK]
    have : (29927379 : ℝ) / 44551884839 + 54071859 / 100000000000 + (1 + 251 / 1000000000) ≤
        10012128 / 10000000 := by norm_num
    linarith
  have hκ0 : 0 ≤ kappaEX q r := by
    unfold kappaEX
    rw [hK]
    linarith
  refine ⟨hsE, haE, hκ, ?_, ?_, ?_⟩
  · refine le_trans hb2 ?_
    unfold aEX
    rw [hq, hr]
    norm_num
  · have e1 : 6 * r / (1 - 3 * q) = 2 * (29927379 / 44551884839) := by
      rw [← hK]
      ring
    rw [e1]
    have e2 : sEX q r ^ 2 ≤ (54071859 / 100000000000) ^ 2 := pow_le_pow_left₀ hsE0 hsE 2
    have e3 : aEX q ^ 2 ≤ (1 + 251 / 1000000000) ^ 2 := pow_le_pow_left₀ haE0 haE 2
    have e4 : 2 * ((29927379 : ℝ) / 44551884839) * sEX q r ≤
        2 * (29927379 / 44551884839) * (54071859 / 100000000000) :=
      mul_le_mul_of_nonneg_left hsE (by norm_num)
    have : 2 * ((29927379 : ℝ) / 44551884839) * (54071859 / 100000000000) +
        (54071859 / 100000000000) ^ 2 + (1 + 251 / 1000000000) ^ 2 ≤ 10000016 / 10000000 := by
      norm_num
    linarith
  · rw [hK]
    have e1 : kappaEX q r ^ 3 ≤ (10012128 / 10000000) ^ 3 := pow_le_pow_left₀ hκ0 hκ 3
    have : (((29927379 : ℝ) / 44551884839) ^ 3 + (10012128 / 10000000) ^ 3) * (1 / 4466) ≤
        2248 / 10000000 := by norm_num
    calc (((29927379 : ℝ) / 44551884839) ^ 3 + kappaEX q r ^ 3) * r
        ≤ (((29927379 : ℝ) / 44551884839) ^ 3 + (10012128 / 10000000) ^ 3) * r :=
          mul_le_mul_of_nonneg_right (by linarith) hr0
      _ = (((29927379 : ℝ) / 44551884839) ^ 3 + (10012128 / 10000000) ^ 3) * (1 / 4466) := by
          rw [hr]
      _ ≤ 2248 / 10000000 := this

/-- **`cert:record:e-coefficients`, the row `X = Q₃`** (`q = 1/Q₃`, `r = 1/⌊√Q₃⌋ = 1/4466`,
`isqrt_Q3`): `s_E ≤ 5.4071859·10⁻⁴`, `a_E ≤ 1 + 2.51·10⁻⁷`, `κ_E ≤ 1.0012128`,
`r_E ≤ 10.829703`, and the gates `s^E_{(2)} ≤ 1.0000016`, `s^E_{(3)} ≤ 0.0002248`, exactly as
printed. -/
theorem cert_e_Q3 :
    sEX (1 / 19951586) (1 / 4466) ≤ 54071859 / 100000000000 ∧
      aEX (1 / 19951586) ≤ 1 + 251 / 1000000000 ∧
      kappaEX (1 / 19951586) (1 / 4466) ≤ 10012128 / 10000000 ∧
      rEX (1 / 19951586) (1 / 4466) ≤ 10829703 / 1000000 ∧
      6 * (1 / 4466) / (1 - 3 * (1 / 19951586)) * sEX (1 / 19951586) (1 / 4466) +
          sEX (1 / 19951586) (1 / 4466) ^ 2 + aEX (1 / 19951586) ^ 2 ≤ 10000016 / 10000000 ∧
      ((3 * (1 / 4466) / (1 - 3 * (1 / 19951586))) ^ 3 +
          kappaEX (1 / 19951586) (1 / 4466) ^ 3) * (1 / 4466) ≤ 2248 / 10000000 :=
  cert_e_Q3_aux rfl rfl

theorem cert_e_two_pow_45_aux {q r : ℝ} (hq : q = 1 / 35184372088832) (hr : r = 1 / 5931641) :
    sEX q r ≤ 40700610 / 100000000000000 ∧ aEX q ≤ 1 + 15 / 100000000000000 ∧
      kappaEX q r ≤ 10000010 / 10000000 ∧ rEX q r ≤ 10828429 / 1000000 := by
  have hq0 : 0 ≤ q := by rw [hq]; norm_num
  have hq1 : q ≤ 1 / 100 := by rw [hq]; norm_num
  have hr0 : 0 ≤ r := by rw [hr]; norm_num
  have hsA : 99999999 / 100000000 ≤ Real.sqrt ((1 - q) * (1 - 3 * q)) := by
    rw [Real.le_sqrt (by norm_num) (by rw [hq]; norm_num), hq]
    norm_num
  have hsB : Real.sqrt (2 + 4 * q ^ 2 / (1 - 2 * q) ^ 2) ≤ 14142136 / 10000000 := by
    rw [Real.sqrt_le_left (by norm_num), hq]
    norm_num
  obtain ⟨hb1, hb2⟩ := coeff_bounds hq0 hq1 hr0 (by norm_num) hsA hsB
  have hsE : sEX q r ≤ 40700610 / 100000000000000 := by
    refine le_trans hb1 ?_
    rw [hq, hr]
    norm_num
  have haE : aEX q ≤ 1 + 15 / 100000000000000 := by
    unfold aEX
    rw [hq]
    norm_num
  refine ⟨hsE, haE, ?_, ?_⟩
  · unfold kappaEX
    have hK : 3 * r / (1 - 3 * q) ≤ 506 / 1000000000 := by
      rw [hq, hr]
      norm_num
    have : (506 : ℝ) / 1000000000 + 40700610 / 100000000000000 + (1 + 15 / 100000000000000) ≤
        10000010 / 10000000 := by norm_num
    linarith
  · refine le_trans hb2 ?_
    unfold aEX
    rw [hq, hr]
    norm_num

/-- **`cert:record:e-coefficients`, the row `X = 2^{45}`** (`q = 2^{-45}`,
`r = 1/⌊√(2^{45})⌋ = 1/5931641`, `isqrt_two_pow_45`): `s_E ≤ 4.0700610·10⁻⁷`,
`a_E ≤ 1 + 1.5·10⁻¹³`, `κ_E ≤ 1.0000010`, `r_E ≤ 10.828429`, exactly as printed. -/
theorem cert_e_two_pow_45 :
    sEX (1 / 35184372088832) (1 / 5931641) ≤ 40700610 / 100000000000000 ∧
      aEX (1 / 35184372088832) ≤ 1 + 15 / 100000000000000 ∧
      kappaEX (1 / 35184372088832) (1 / 5931641) ≤ 10000010 / 10000000 ∧
      rEX (1 / 35184372088832) (1 / 5931641) ≤ 10828429 / 1000000 :=
  cert_e_two_pow_45_aux rfl rfl

end Sarkozy.MiddleRecords
