module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The layer cut of a positive root, I: the constants (`subsec:positive-root-layer`)

`paper/sections/20b_positive_roots.tex`, subsection `subsec:positive-root-layer` (the constants
before (L1)–(L4)), `lem:native-pair-linear` and `prop:root-layer`. Everything is a real function
of `q` and `r`, the paper's `q = 1/p` and `r = p^{-1/2}` (`qr_of_ge`); the tilt parameter is `u`,
with `γ = u²`. At the endpoint `P = 2³⁰` both `q = 2⁻³⁰` and `r = 2⁻¹⁵` are rational, so every
numerical claim of the subsection is a rational inequality after the monotonicity in `q, r`.

* The constants of the two components: `d2` (`d₂`), `dMu` (`d_μ`), `kappa` (`κ = (√3 + √7)/2`),
  `bF` (`𝔟`), `nF` (`𝔫`), `MPhi` (`M_Φ`), `Zm` (`Z_-`), `hm` (`h_- = 1 - 9q`), `eF`
  (`e = 𝔟 - 6`) and `Cpair` (`C_pair`, `lem:native-pair-linear`).
* The constants of `prop:root-layer`: `BH` (`B_H = 2 + r`), `mU` (`m_u`), `FU` (`F_u`), `Cnn`,
  `Csc`, `Ccr`, `CU`, `Cin` (`C_{nn,u}`, `C_{sc,u}`, `C_{cr,u}`, `C_u`, `C_{in,u}`), `zI`
  (`z^ι_u`), `gI` (`g^ι_u`), `cI` (`c^ι_u`), `AI` (`A^ι_u`) and `cPlusI` (`c^{+,ι}_u`). The two
  constants of the chamber side that enter are `h0` (`h_0` of `lem:root-normalization`) and `c0`
  (`c_0 = 4/(1-q) + 2q` of `subsec:positive-root-chamber`).

**Numerical claims checked** (exact rational arithmetic, kernel-checked by `norm_num`):
* (L1), "In particular": `𝔟 ≤ 6 + 102/(1-q) + (32 + 112r)/(1-q²)` (`bF_le_maj`, all `0 ≤ q < 1`,
  `r`), `< 140.004` for `p ≥ 2³⁰` (`bF_lt`, `bF_lt_of_ge`), with limit `140` (`bF_zero`);
* `lem:native-pair-linear`: `C_pair < 2897` for `p ≥ 2³⁰` (`Cpair_lt`, `Cpair_lt_of_ge`);
* the gates used by `prop:root-layer`: `Z_- ≥ 0.99999` and `h_- > 0` for `p ≥ 2³⁰` (`Zm_ge`,
  `hm_pos`);
* (L1), "All these majorants are increasing in `q, r`": `bF_mono`, `nF_mono`, `MPhi_mono`,
  `dMu_mono`.

The values (Python, 50 digits): `𝔟(2⁻³⁰, 2⁻¹⁵) = 140.0034180…`, the majorant `140.0034180…`;
`C_pair(2⁻³⁰, 2⁻¹⁵) = 2895.714…`, and the rational majorant used here `2895.717`.
-/

@[expose] public section

namespace Sarkozy.PositiveRoots

namespace Layer

/-! ## The constants of the two components -/

/-- `d₂ = 2/(1 - q)`: the two-coordinate density of a uniform directed cyclic triangle
(`subsec:positive-root-layer`). -/
noncomputable def d2 (q : ℝ) : ℝ := 2 / (1 - q)

/-- `d_μ = 8/(1 - q²)`: the three-coordinate density of a uniform directed cyclic triangle
(`subsec:positive-root-layer`). -/
noncomputable def dMu (q : ℝ) : ℝ := 8 / (1 - q ^ 2)

/-- `κ = (√3 + √7)/2`, the norm of the coefficient matrix `[[iD_△, -I₃], [-I₃, 0]]` of the six
single edges and the six two-edge stars of a component (`subsec:positive-root-layer`, (L1)). -/
noncomputable def kappa : ℝ := (Real.sqrt 3 + Real.sqrt 7) / 2

/-- `𝔟 = 6 + 15d₂ + 18√(d₂d_μ) + 4d_μ + 14d_μ r` (`subsec:positive-root-layer`): the six star
means and the `51` remaining masks of the table of (L1). -/
noncomputable def bF (q r : ℝ) : ℝ :=
  6 + 15 * d2 q + 18 * Real.sqrt (d2 q * dMu q) + 4 * dMu q + 14 * dMu q * r

/-- `𝔫 = κ(1 + 5r)r + 𝔟q`, the bound `‖N_Φ‖ ≤ 𝔫` of (L1) (`subsec:positive-root-layer`). -/
noncomputable def nF (q r : ℝ) : ℝ := kappa * (1 + 5 * r) * r + bF q r * q

/-- `M_Φ = d_μ(1 + q)³`, the row bound of `Φ` of (L4) (`subsec:positive-root-layer`). -/
noncomputable def MPhi (q : ℝ) : ℝ := dMu q * (1 + q) ^ 3

/-- `Z_- = (1 - 𝔟q)² - q[18M_Φ² + 384M_Φ + 72d_μ²(1 + q)⁵]`, the lower bound of (L4) for the raw
mass of the uniform root relative to `ν ⊗ ν` (`subsec:positive-root-layer`). -/
noncomputable def Zm (q r : ℝ) : ℝ :=
  (1 - bF q r * q) ^ 2 - q * (18 * MPhi q ^ 2 + 384 * MPhi q + 72 * dMu q ^ 2 * (1 + q) ^ 5)

/-- `h_- = 1 - 9q`, the lower bound for the probability `h` that the six labels of the two
triangles are distinct (`subsec:positive-root-layer`). -/
noncomputable def hm (q : ℝ) : ℝ := 1 - 9 * q

/-- `e = 𝔟 - 6` (`lem:native-pair-linear`). -/
noncomputable def eF (q r : ℝ) : ℝ := bF q r - 6

/-- `C_pair = 2304 + 2κ(1 + 5r)(1 + e) + r(12 + 14e + e²)` (`lem:native-pair-linear`). -/
noncomputable def Cpair (q r : ℝ) : ℝ :=
  2304 + 2 * kappa * (1 + 5 * r) * (1 + eF q r) + r * (12 + 14 * eF q r + eF q r ^ 2)

/-! ## The constants of `prop:root-layer` -/

/-- `B_H = 2 + r`, the bound `|𝖧| ≤ B_H` of a score on four distinct labels (`prop:root-layer`,
from `thm:weil`(b)). -/
noncomputable def BH (r : ℝ) : ℝ := 2 + r

/-- `m_u = 1 + 2ur + γ` (`prop:root-layer`). -/
noncomputable def mU (u r : ℝ) : ℝ := 1 + 2 * u * r + u ^ 2

/-- `F_u = 1 + 2uB_H + γB_H²`, the bound `|Υ| ≤ F_u` (`prop:root-layer`). -/
noncomputable def FU (u r : ℝ) : ℝ := 1 + 2 * u * BH r + u ^ 2 * BH r ^ 2

/-- `C_{nn,u} = 3969 · 16 F_u`: the `63²` monomials of `N_Φ ⊗ N_Φ` at `16F_u q` each
(`prop:root-layer`). -/
noncomputable def Cnn (u r : ℝ) : ℝ := 3969 * 16 * FU u r

/-- `C_{sc,u} = 127[4(1 + 4ur + 4γq) + 2(q + 2ur + γ)]`: the selected-label coincidences
(`prop:root-layer`). -/
noncomputable def Csc (u q r : ℝ) : ℝ :=
  127 * (4 * (1 + 4 * u * r + 4 * u ^ 2 * q) + 2 * (q + 2 * u * r + u ^ 2))

/-- `C_{cr,u} = [256M_Φ + 64d_μ²(1 + q)⁵]F_u`: the other cross coincidences (`prop:root-layer`). -/
noncomputable def Ccr (u q : ℝ) (r : ℝ) : ℝ :=
  (256 * MPhi q + 64 * dMu q ^ 2 * (1 + q) ^ 5) * FU u r

/-- `C_u = C_{nn,u} + C_{sc,u} + C_{cr,u}` (`prop:root-layer`). -/
noncomputable def CU (u q r : ℝ) : ℝ := Cnn u r + Csc u q r + Ccr u q r

/-- `C_{in,u} = 127[9F_u + 2(q + 2ur + γ)]`: the input-half coincidences (`prop:root-layer`). -/
noncomputable def Cin (u q r : ℝ) : ℝ := 127 * (9 * FU u r + 2 * (q + 2 * u * r + u ^ 2))

/-- `h_0 = (72q + 37qr + 2qr/(1 - q))/(1 - 36q)`, the bound `|E_{Γ_{p,0}} H_j| ≤ h_0` of
`lem:root-normalization`(b). -/
noncomputable def h0 (q r : ℝ) : ℝ := (72 * q + 37 * q * r + 2 * q * r / (1 - q)) / (1 - 36 * q)

/-- `c_0 = 4/(1 - q) + 2q` (`subsec:positive-root-chamber`; the bound `‖P₀𝖧²P₀‖ ≤ c_0 q` of
`cor:raw-pair-maps`(b)). -/
noncomputable def c0 (q : ℝ) : ℝ := 4 / (1 - q) + 2 * q

/-- `z^ι_u = 1 + γ - γ[4q + 36qB_H² + 2q/(1 - q)] - 2uh_0`, the lower bound for the tilt mass
`E_{Γ_{p,0}} w_u` (`prop:root-layer`). -/
noncomputable def zI (u q r : ℝ) : ℝ :=
  1 + u ^ 2 - u ^ 2 * (4 * q + 36 * q * BH r ^ 2 + 2 * q / (1 - q)) - 2 * u * h0 q r

/-- `g^ι_u = (2𝔫m_u + C_u q)/(r z^ι_u h_- Z_-)` (`prop:root-layer`). -/
noncomputable def gI (u q r : ℝ) : ℝ :=
  (2 * nF q r * mU u r + CU u q r * q) / (r * zI u q r * hm q * Zm q r)

/-- `c^ι_u = (2ur + γc_0q + (2𝔫m_u + C_u q)/h_-)/(z^ι_u Z_-)` (`prop:root-layer`). -/
noncomputable def cI (u q r : ℝ) : ℝ :=
  (2 * u * r + u ^ 2 * c0 q * q + (2 * nF q r * mU u r + CU u q r * q) / hm q) /
    (zI u q r * Zm q r)

/-- `A^ι_u = (C_u + C_{in,u} + 910γ + 2(1 + γ)𝔟/h_-)/(z^ι_u h_- Z_-)` (`prop:root-layer`). -/
noncomputable def AI (u q r : ℝ) : ℝ :=
  (CU u q r + Cin u q r + 910 * u ^ 2 + 2 * (1 + u ^ 2) * bF q r / hm q) /
    (zI u q r * hm q * Zm q r)

/-- `c^{+,ι}_u = q(A^ι_u)²/(1 - c^ι_u)` (`prop:root-layer`). -/
noncomputable def cPlusI (u q r : ℝ) : ℝ := q * AI u q r ^ 2 / (1 - cI u q r)

/-! ## `q = 1/p` and `r = p^{-1/2}` for `p ≥ 2³⁰` -/

/-- For `p ≥ 2³⁰`, `q = 1/p` and `r = 1/√p` satisfy `0 ≤ q ≤ 2⁻³⁰`, `0 ≤ r ≤ 2⁻¹⁵`, and
`q = r²`. -/
theorem qr_of_ge {p : ℝ} (hp : 2 ^ 30 ≤ p) :
    0 ≤ 1 / p ∧ 1 / p ≤ 1 / 2 ^ 30 ∧ 0 ≤ 1 / Real.sqrt p ∧ 1 / Real.sqrt p ≤ 1 / 2 ^ 15 ∧
      1 / p = (1 / Real.sqrt p) ^ 2 := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hs : (2 : ℝ) ^ 15 ≤ Real.sqrt p := by
    rw [Real.le_sqrt (by norm_num) hp0.le]
    calc ((2 : ℝ) ^ 15) ^ 2 = 2 ^ 30 := by norm_num
      _ ≤ p := hp
  refine ⟨by positivity, one_div_le_one_div_of_le (by norm_num) hp, by positivity,
    one_div_le_one_div_of_le (by norm_num) hs, ?_⟩
  rw [div_pow, one_pow, Real.sq_sqrt hp0.le]

/-! ## (L1): `𝔟 < 140.004` -/

theorem one_sub_sq_pos {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) : 0 < 1 - q ^ 2 := by nlinarith

/-- `√(d₂d_μ) ≤ 4/(1 - q)`, as `d₂d_μ = 16/((1 - q)²(1 + q))`. -/
theorem sqrt_d2_dMu_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Real.sqrt (d2 q * dMu q) ≤ 4 / (1 - q) := by
  have h1 : 0 < 1 - q := by linarith
  have h2 := one_sub_sq_pos hq0 hq1
  rw [Real.sqrt_le_left (by positivity)]
  unfold d2 dMu
  rw [div_pow, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg hq0 (sq_nonneg (1 - q)), mul_nonneg hq0 h1.le]

/-- **(L1), "In particular", first inequality**: `𝔟 ≤ 6 + 102/(1 - q) + (32 + 112r)/(1 - q²)`
(`subsec:positive-root-layer`). -/
theorem bF_le_maj {q r : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    bF q r ≤ 6 + 102 / (1 - q) + (32 + 112 * r) / (1 - q ^ 2) := by
  have h := sqrt_d2_dMu_le hq0 hq1
  have key : 6 + 102 / (1 - q) + (32 + 112 * r) / (1 - q ^ 2) =
      6 + 15 * d2 q + 18 * (4 / (1 - q)) + 4 * dMu q + 14 * dMu q * r := by
    unfold d2 dMu
    ring
  rw [key]
  unfold bF
  linarith

/-- The majorant of `𝔟` at the gated domain `q ≤ 2⁻³⁰`, `r ≤ 2⁻¹⁵` is `< 140.004`. -/
theorem bMaj_lt {q r : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2 ^ 30) (hr : r ≤ 1 / 2 ^ 15) :
    6 + 102 / (1 - q) + (32 + 112 * r) / (1 - q ^ 2) < 140004 / 1000 := by
  have hpos : (0 : ℝ) < 1 - 1 / 2 ^ 30 := by norm_num
  have h1 : (1 : ℝ) - 1 / 2 ^ 30 ≤ 1 - q := by linarith
  have t1 : 102 / (1 - q) ≤ 102 / (1 - 1 / 2 ^ 30) :=
    div_le_div_of_nonneg_left (by norm_num) hpos h1
  have hpos2 : (0 : ℝ) < 1 - (1 / 2 ^ 30) ^ 2 := by norm_num
  have hq2 : q ^ 2 ≤ (1 / 2 ^ 30) ^ 2 := pow_le_pow_left₀ hq0 hq 2
  have h2 : (1 : ℝ) - (1 / 2 ^ 30) ^ 2 ≤ 1 - q ^ 2 := by linarith
  have hq1 : q < 1 := lt_of_le_of_lt hq (by norm_num)
  have h2' := one_sub_sq_pos hq0 hq1
  have t2 : (32 + 112 * r) / (1 - q ^ 2) ≤ (32 + 112 * (1 / 2 ^ 15)) / (1 - (1 / 2 ^ 30) ^ 2) := by
    calc (32 + 112 * r) / (1 - q ^ 2) ≤ (32 + 112 * (1 / 2 ^ 15)) / (1 - q ^ 2) := by
          apply div_le_div_of_nonneg_right _ h2'.le
          linarith
      _ ≤ (32 + 112 * (1 / 2 ^ 15)) / (1 - (1 / 2 ^ 30) ^ 2) :=
          div_le_div_of_nonneg_left (by norm_num) hpos2 h2
  have hnum : 6 + 102 / (1 - 1 / 2 ^ 30) + (32 + 112 * (1 / 2 ^ 15)) / (1 - (1 / 2 ^ 30) ^ 2) <
      (140004 / 1000 : ℝ) := by norm_num
  linarith

/-- **(L1), "In particular"**: `𝔟 < 140.004` on the gated domain `0 ≤ q ≤ 2⁻³⁰`, `0 ≤ r ≤ 2⁻¹⁵`
(`subsec:positive-root-layer`). -/
theorem bF_lt {q r : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2 ^ 30) (hr : r ≤ 1 / 2 ^ 15) :
    bF q r < 140004 / 1000 :=
  lt_of_le_of_lt (bF_le_maj hq0 (lt_of_le_of_lt hq (by norm_num))) (bMaj_lt hq0 hq hr)

/-- **(L1)**: `𝔟 < 140.004` for `p ≥ 2³⁰`, `q = 1/p`, `r = p^{-1/2}`
(`subsec:positive-root-layer`). -/
theorem bF_lt_of_ge {p : ℝ} (hp : 2 ^ 30 ≤ p) : bF (1 / p) (1 / Real.sqrt p) < 140004 / 1000 := by
  obtain ⟨h1, h2, -, h4, -⟩ := qr_of_ge hp
  exact bF_lt h1 h2 h4

/-- **(L1)**: the limit of `𝔟` is `140`. -/
theorem bF_zero : bF 0 0 = 140 := by
  unfold bF d2 dMu
  have : Real.sqrt ((2 : ℝ) / (1 - 0) * (8 / (1 - 0 ^ 2))) = 4 := by
    rw [show (2 : ℝ) / (1 - 0) * (8 / (1 - 0 ^ 2)) = 4 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [this]
  norm_num

theorem d2_nonneg {q : ℝ} (hq1 : q < 1) : 0 ≤ d2 q := by
  unfold d2
  have : 0 < 1 - q := by linarith
  positivity

theorem dMu_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) : 0 ≤ dMu q := by
  unfold dMu
  have := one_sub_sq_pos hq0 hq1
  positivity

/-- `𝔟 ≥ 6`, so `e = 𝔟 - 6 ≥ 0`. -/
theorem bF_ge_six {q r : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hr0 : 0 ≤ r) : 6 ≤ bF q r := by
  have h1 := d2_nonneg hq1
  have h2 := dMu_nonneg hq0 hq1
  have h3 := Real.sqrt_nonneg (d2 q * dMu q)
  unfold bF
  have : 0 ≤ 14 * dMu q * r := by positivity
  linarith

/-! ## (L1): monotonicity in `q, r` -/

theorem d2_mono {q q' : ℝ} (hqq : q ≤ q') (hq1 : q' < 1) : d2 q ≤ d2 q' := by
  unfold d2
  have h1 : 0 < 1 - q' := by linarith
  exact div_le_div_of_nonneg_left (by norm_num) h1 (by linarith)

theorem dMu_mono {q q' : ℝ} (hq0 : 0 ≤ q) (hqq : q ≤ q') (hq1 : q' < 1) : dMu q ≤ dMu q' := by
  unfold dMu
  have h1 := one_sub_sq_pos (le_trans hq0 hqq) hq1
  have : q ^ 2 ≤ q' ^ 2 := pow_le_pow_left₀ hq0 hqq 2
  exact div_le_div_of_nonneg_left (by norm_num) h1 (by linarith)

/-- **(L1), "All these majorants are increasing in `q, r`"**: `𝔟` is increasing in `q` and `r`
on `0 ≤ q < 1`, `r ≥ 0`. -/
theorem bF_mono {q q' r r' : ℝ} (hq0 : 0 ≤ q) (hqq : q ≤ q') (hq1 : q' < 1) (hr0 : 0 ≤ r)
    (hrr : r ≤ r') : bF q r ≤ bF q' r' := by
  have a1 := d2_mono hqq hq1
  have a2 := dMu_mono hq0 hqq hq1
  have a0 := dMu_nonneg hq0 (lt_of_le_of_lt hqq hq1)
  have b0 := d2_nonneg (lt_of_le_of_lt hqq hq1)
  have a3 : Real.sqrt (d2 q * dMu q) ≤ Real.sqrt (d2 q' * dMu q') :=
    Real.sqrt_le_sqrt (mul_le_mul a1 a2 a0 (le_trans b0 a1))
  have a4 : dMu q * r ≤ dMu q' * r' := mul_le_mul a2 hrr hr0 (le_trans a0 a2)
  unfold bF
  linarith

/-- `𝔫 = κ(1 + 5r)r + 𝔟q` is increasing in `q, r` (`subsec:positive-root-layer`, (L1)). -/
theorem nF_mono {q q' r r' : ℝ} (hq0 : 0 ≤ q) (hqq : q ≤ q') (hq1 : q' < 1) (hr0 : 0 ≤ r)
    (hrr : r ≤ r') : nF q r ≤ nF q' r' := by
  have hb := bF_mono hq0 hqq hq1 hr0 hrr
  have hb0 := bF_ge_six hq0 (lt_of_le_of_lt hqq hq1) hr0
  have hk : 0 ≤ kappa := by unfold kappa; positivity
  unfold nF
  have t1 : kappa * (1 + 5 * r) * r ≤ kappa * (1 + 5 * r') * r' := by
    have : 0 ≤ kappa * (1 + 5 * r') := mul_nonneg hk (by linarith)
    gcongr
  have t2 : bF q r * q ≤ bF q' r' * q' := mul_le_mul hb hqq hq0 (by linarith)
  linarith

/-- `M_Φ` is increasing in `q`. -/
theorem MPhi_mono {q q' : ℝ} (hq0 : 0 ≤ q) (hqq : q ≤ q') (hq1 : q' < 1) : MPhi q ≤ MPhi q' := by
  unfold MPhi
  have a2 := dMu_mono hq0 hqq hq1
  have a0 := dMu_nonneg hq0 (lt_of_le_of_lt hqq hq1)
  have : (1 + q) ^ 3 ≤ (1 + q') ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  exact mul_le_mul a2 this (by positivity) (le_trans a0 a2)

/-! ## `lem:native-pair-linear`: `C_pair < 2897` -/

/-- `κ ≤ 2.18890115` (`√3 ≤ 1.7320509`, `√7 ≤ 2.6457514`). -/
theorem kappa_le : kappa ≤ 218890115 / 10 ^ 8 := by
  have h3 : Real.sqrt 3 ≤ 17320509 / 10 ^ 7 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have h7 : Real.sqrt 7 ≤ 26457514 / 10 ^ 7 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  unfold kappa
  linarith

theorem kappa_nonneg : 0 ≤ kappa := by
  unfold kappa
  positivity

/-- **`lem:native-pair-linear`, the endpoint inequality**: `C_pair < 2897` on the gated domain
`0 ≤ q ≤ 2⁻³⁰`, `0 ≤ r ≤ 2⁻¹⁵` (the text: "The endpoint inequality uses `r ≤ 2⁻¹⁵` and the
rational upper bound for `𝔟` above"). -/
theorem Cpair_lt {q r : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2 ^ 30) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2 ^ 15) :
    Cpair q r < 2897 := by
  have hq1 : q < 1 := lt_of_le_of_lt hq (by norm_num)
  have he0 : 0 ≤ eF q r := by
    have := bF_ge_six hq0 hq1 hr0
    unfold eF
    linarith
  have he1 : eF q r ≤ 134004 / 1000 := by
    have := bF_lt hq0 hq hr
    unfold eF
    linarith
  have hk := kappa_le
  have hk0 := kappa_nonneg
  have t1 : 2 * kappa * (1 + 5 * r) * (1 + eF q r) ≤
      2 * (218890115 / 10 ^ 8) * (1 + 5 * (1 / 2 ^ 15)) * (1 + 134004 / 1000) := by
    gcongr
  have t2 : r * (12 + 14 * eF q r + eF q r ^ 2) ≤
      (1 / 2 ^ 15) * (12 + 14 * (134004 / 1000) + (134004 / 1000) ^ 2) := by
    gcongr
  have hnum : (2304 : ℝ) + 2 * (218890115 / 10 ^ 8) * (1 + 5 * (1 / 2 ^ 15)) * (1 + 134004 / 1000) +
      (1 / 2 ^ 15) * (12 + 14 * (134004 / 1000) + (134004 / 1000) ^ 2) < 2897 := by norm_num
  unfold Cpair
  linarith

/-- **`lem:native-pair-linear`**: `C_pair < 2897` for `p ≥ 2³⁰`, `q = 1/p`, `r = p^{-1/2}`. -/
theorem Cpair_lt_of_ge {p : ℝ} (hp : 2 ^ 30 ≤ p) : Cpair (1 / p) (1 / Real.sqrt p) < 2897 := by
  obtain ⟨h1, h2, h3, h4, -⟩ := qr_of_ge hp
  exact Cpair_lt h1 h2 h3 h4

/-! ## The gates `h_- > 0` and `Z_- > 0` for `p ≥ 2³⁰` -/

theorem hm_pos {q : ℝ} (hq : q ≤ 1 / 2 ^ 30) : 0 < hm q := by
  unfold hm
  have : (9 : ℝ) * (1 / 2 ^ 30) < 1 := by norm_num
  linarith

/-- `M_Φ ≤ 8.0000001` on the gated domain. -/
theorem MPhi_le {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2 ^ 30) : MPhi q ≤ 80000001 / 10 ^ 7 := by
  have h := MPhi_mono hq0 hq (by norm_num)
  have e : MPhi (1 / 2 ^ 30) ≤ 80000001 / 10 ^ 7 := by
    unfold MPhi dMu
    norm_num
  linarith

/-- `d_μ ≤ 8.0000001` on the gated domain. -/
theorem dMu_le {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2 ^ 30) : dMu q ≤ 80000001 / 10 ^ 7 := by
  have h := dMu_mono hq0 hq (by norm_num)
  have e : dMu (1 / 2 ^ 30) ≤ 80000001 / 10 ^ 7 := by
    unfold dMu
    norm_num
  linarith

/-- **The gate `Z_- > 0`** of `prop:root-layer`, quantitatively: `Z_- ≥ 0.99999` on the gated
domain `0 ≤ q ≤ 2⁻³⁰`, `0 ≤ r ≤ 2⁻¹⁵` (the value is `1 - 9112.0…q`). -/
theorem Zm_ge {q r : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2 ^ 30) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2 ^ 15) :
    99999 / 100000 ≤ Zm q r := by
  have hq1 : q < 1 := lt_of_le_of_lt hq (by norm_num)
  have hb := bF_lt hq0 hq hr
  have hb6 := bF_ge_six hq0 hq1 hr0
  have hM := MPhi_le hq0 hq
  have hM0 : 0 ≤ MPhi q := by
    unfold MPhi
    have := dMu_nonneg hq0 hq1
    positivity
  have hd := dMu_le hq0 hq
  have hd0 := dMu_nonneg hq0 hq1
  -- `1 - 𝔟q ≥ 1 - 140.004 · 2⁻³⁰`
  have hbq : bF q r * q ≤ 140004 / 1000 * (1 / 2 ^ 30) :=
    mul_le_mul hb.le hq hq0 (by norm_num)
  have hbq0 : 0 ≤ bF q r * q := mul_nonneg (by linarith) hq0
  have hsq : (1 - 140004 / 1000 * (1 / 2 ^ 30)) ^ 2 ≤ (1 - bF q r * q) ^ 2 := by
    apply pow_le_pow_left₀ (by norm_num) (by linarith)
  have hq5 : (1 + q) ^ 5 ≤ (1 + 1 / 2 ^ 30) ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
  have hbr : 18 * MPhi q ^ 2 + 384 * MPhi q + 72 * dMu q ^ 2 * (1 + q) ^ 5 ≤
      18 * (80000001 / 10 ^ 7) ^ 2 + 384 * (80000001 / 10 ^ 7) +
        72 * (80000001 / 10 ^ 7) ^ 2 * (1 + 1 / 2 ^ 30) ^ 5 := by
    gcongr
  have hbr0 : 0 ≤ 18 * MPhi q ^ 2 + 384 * MPhi q + 72 * dMu q ^ 2 * (1 + q) ^ 5 := by positivity
  have hmul : q * (18 * MPhi q ^ 2 + 384 * MPhi q + 72 * dMu q ^ 2 * (1 + q) ^ 5) ≤
      1 / 2 ^ 30 * (18 * (80000001 / 10 ^ 7) ^ 2 + 384 * (80000001 / 10 ^ 7) +
        72 * (80000001 / 10 ^ 7) ^ 2 * (1 + 1 / 2 ^ 30) ^ 5) :=
    mul_le_mul hq hbr hbr0 (by norm_num)
  have hnum : (99999 / 100000 : ℝ) ≤ (1 - 140004 / 1000 * (1 / 2 ^ 30)) ^ 2 -
      1 / 2 ^ 30 * (18 * (80000001 / 10 ^ 7) ^ 2 + 384 * (80000001 / 10 ^ 7) +
        72 * (80000001 / 10 ^ 7) ^ 2 * (1 + 1 / 2 ^ 30) ^ 5) := by norm_num
  unfold Zm
  linarith

theorem Zm_pos {q r : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2 ^ 30) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2 ^ 15) :
    0 < Zm q r :=
  lt_of_lt_of_le (by norm_num) (Zm_ge hq0 hq hr0 hr)

/-! ## Nonnegativity of the constants -/

theorem FU_nonneg {u r : ℝ} (hu : 0 ≤ u) (hr : 0 ≤ r) : 0 ≤ FU u r := by
  unfold FU BH
  positivity

theorem MPhi_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) : 0 ≤ MPhi q := by
  have := dMu_nonneg hq0 hq1
  unfold MPhi
  positivity

theorem CU_nonneg {u q r : ℝ} (hu : 0 ≤ u) (hq0 : 0 ≤ q) (hq1 : q < 1) (hr : 0 ≤ r) :
    0 ≤ CU u q r := by
  have h1 := FU_nonneg hu hr
  have h2 := MPhi_nonneg hq0 hq1
  have h3 := dMu_nonneg hq0 hq1
  unfold CU Cnn Csc Ccr
  positivity

theorem Cin_nonneg {u q r : ℝ} (hu : 0 ≤ u) (hq0 : 0 ≤ q) (hr : 0 ≤ r) : 0 ≤ Cin u q r := by
  have h1 := FU_nonneg hu hr
  unfold Cin
  positivity

theorem c0_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) : 0 ≤ c0 q := by
  have : 0 < 1 - q := by linarith
  unfold c0
  positivity

theorem nF_nonneg {q r : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hr : 0 ≤ r) : 0 ≤ nF q r := by
  have h1 := bF_ge_six hq0 hq1 hr
  have h2 := kappa_nonneg
  unfold nF
  have : 0 ≤ bF q r * q := mul_nonneg (by linarith) hq0
  positivity

/-! ## (L1): the mask table, by enumeration

The soft kernel of a component is `Φ(x, x') = ∏_{i ≠ j} (1 + (D_△)_{ij} χ(x'_j - x_i))`: one factor
for each of the six cross edges `x_i — x'_j`, `i ≠ j` (the six-cycle of the text), so `N_Φ = Φ - 1`
has `63` monomials, one for each nonempty set `M` of cross edges (a *mask*). A mask uses
`u = |{i}|` output and `v = |{j}|` input coordinates. Checked by `decide +kernel`
(`mask_table`): the `6` single edges, the `6` two-edge stars and the `51` remaining masks, which
split as in the table of (L1) into `15` of type `(2,2)`, `9 + 9` of types `(2,3), (3,2)` (all of
matching number two), and `18` of type `(3,3)`: `3` of matching number two (two disjoint
two-edge stars), `14` forests of matching number three, and the full six-cycle. Summing the
per-mask bounds of the table (`d₂q`, `√(d₂d_μ)q`, `d_μq`, `d_μrq`, `d_μq`) gives `(𝔟 - 6)q`
(`bF_eq_table`). The per-mask operator bounds themselves are analytic and not checked here. -/

/-- The six cross edges `(i, j)`, `i ≠ j`, of a component at the cut `ι`. -/
def crossEdges : Finset (Fin 3 × Fin 3) := Finset.univ.filter (fun e => e.1 ≠ e.2)

/-- The number `u` of output coordinates used by a mask. -/
def outCoords (M : Finset (Fin 3 × Fin 3)) : ℕ := (M.image Prod.fst).card

/-- The number `v` of input coordinates used by a mask. -/
def inCoords (M : Finset (Fin 3 × Fin 3)) : ℕ := (M.image Prod.snd).card

/-- A set of edges is a matching when its edges have distinct endpoints on both sides. -/
def isMatching (N : Finset (Fin 3 × Fin 3)) : Bool :=
  (N.image Prod.fst).card = N.card && (N.image Prod.snd).card = N.card

/-- The matching number of a mask. -/
def matchingNumber (M : Finset (Fin 3 × Fin 3)) : ℕ :=
  ((M.powerset.filter (fun N => isMatching N = true)).image Finset.card).sup id

/-- A two-edge star: two edges with a common endpoint. -/
def isStar2 (M : Finset (Fin 3 × Fin 3)) : Bool :=
  M.card = 2 && (outCoords M = 1 || inCoords M = 1)

/-- The `51` remaining masks: at least two edges, not a two-edge star. -/
def masks51 : Finset (Finset (Fin 3 × Fin 3)) :=
  crossEdges.powerset.filter (fun M => 2 ≤ M.card ∧ isStar2 M = false)

/-- **The mask table of (L1)** (`subsec:positive-root-layer`), by enumeration. -/
theorem mask_table :
    crossEdges.card = 6 ∧
    (crossEdges.powerset.filter (fun M => M.Nonempty)).card = 63 ∧
    (crossEdges.powerset.filter (fun M => M.card = 1)).card = 6 ∧
    (crossEdges.powerset.filter (fun M => isStar2 M = true)).card = 6 ∧
    masks51.card = 51 ∧
    (masks51.filter (fun M => outCoords M = 2 ∧ inCoords M = 2)).card = 15 ∧
    (masks51.filter (fun M => outCoords M = 2 ∧ inCoords M = 3)).card = 9 ∧
    (masks51.filter (fun M => outCoords M = 3 ∧ inCoords M = 2)).card = 9 ∧
    (masks51.filter (fun M => outCoords M = 3 ∧ inCoords M = 3)).card = 18 ∧
    (masks51.filter (fun M => outCoords M = 3 ∧ inCoords M = 3 ∧ matchingNumber M = 2)).card = 3 ∧
    (masks51.filter (fun M => outCoords M = 3 ∧ inCoords M = 3 ∧ matchingNumber M = 3 ∧
      M ≠ crossEdges)).card = 14 ∧
    crossEdges ∈ masks51 ∧ outCoords crossEdges = 3 ∧ inCoords crossEdges = 3 := by
  decide +kernel

/-- The masks of types `(2,3)` and `(3,2)` have matching number two; every mask of the `51` has
`u, v ∈ {2, 3}`. -/
theorem mask_types : ∀ M ∈ masks51,
    (outCoords M = 2 ∨ outCoords M = 3) ∧ (inCoords M = 2 ∨ inCoords M = 3) ∧
    ((outCoords M = 2 ∧ inCoords M = 3) ∨ (outCoords M = 3 ∧ inCoords M = 2) →
      matchingNumber M = 2) := by
  decide +kernel

/-- **(L1): the table sums to `𝔟 - 6`**: `15 d₂ + (9 + 9)√(d₂d_μ) + 3d_μ + 14d_μ r + 1 · d_μ`. -/
theorem bF_eq_table (q r : ℝ) :
    bF q r - 6 = 15 * d2 q + (9 + 9) * Real.sqrt (d2 q * dMu q) + 3 * dMu q + 14 * (dMu q * r) +
      1 * dMu q := by
  unfold bF
  ring

/-- `𝔟 ≤ 𝔟_cert = 6 + 51d_μ` (the remark after `cert:positive-root-caps`: "Since
`𝔟 ≤ 𝔟_cert`, these remain valid majorants"), for `0 ≤ q < 1`, `r ≤ 1`. -/
theorem bF_le_bcert {q r : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hr1 : r ≤ 1) :
    bF q r ≤ 6 + 51 * dMu q := by
  have h1 : 0 < 1 - q := by linarith
  have h2 := one_sub_sq_pos hq0 hq1
  have hd : d2 q ≤ dMu q := by
    unfold d2 dMu
    rw [div_le_div_iff₀ h1 h2]
    nlinarith
  have hd0 := d2_nonneg hq1
  have hm0 := dMu_nonneg hq0 hq1
  have hs : Real.sqrt (d2 q * dMu q) ≤ dMu q := by
    rw [Real.sqrt_le_left hm0]
    nlinarith
  have hr : dMu q * r ≤ dMu q := by nlinarith
  unfold bF
  nlinarith

/-! ## The gates `z^ι_u > 0` and `c^ι_u < 1` for `p ≥ 2³⁰` and `0 ≤ u ≤ 1`

All seven selected parameters `u` of `def:positive-root` lie in `[0, 1]` for the six
individual-square pieces (`711/4096, …, 4049/4096`). On the gated domain
`0 ≤ q ≤ 2⁻³⁰`, `0 < r ≤ 2⁻¹⁵`, `0 ≤ u ≤ 1` the two gates of `prop:root-layer` hold
(`zI_ge`, `cI_le`): `z^ι_u ≥ 0.9999998` and `c^ι_u ≤ 0.000914` (the value at `2³⁰`,
`u = 711/4096`, is about `0.00026`). -/

theorem FU_le {u r : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2 ^ 15) :
    FU u r ≤ 1 + 2 * (2 + 1 / 2 ^ 15) + (2 + 1 / 2 ^ 15) ^ 2 := by
  unfold FU BH
  have h1 : u * (2 + r) ≤ 1 * (2 + 1 / 2 ^ 15) :=
    mul_le_mul hu1 (by linarith) (by linarith) (by norm_num)
  have h2 : u ^ 2 * (2 + r) ^ 2 ≤ 1 ^ 2 * (2 + 1 / 2 ^ 15) ^ 2 := by
    have : 0 ≤ 2 + r := by linarith
    gcongr
  linarith

theorem CU_le {u q r : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2 ^ 30)
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2 ^ 15) : CU u q r ≤ 627607 := by
  have hF := FU_le hu0 hu1 hr0 hr
  have hF0 := FU_nonneg hu0 hr0
  have hM := MPhi_le hq0 hq
  have hM0 : 0 ≤ MPhi q := by
    unfold MPhi
    have := dMu_nonneg hq0 (lt_of_le_of_lt hq (by norm_num))
    positivity
  have hd := dMu_le hq0 hq
  have hd0 := dMu_nonneg hq0 (lt_of_le_of_lt hq (by norm_num))
  have hq5 : (1 + q) ^ 5 ≤ (1 + 1 / 2 ^ 30) ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
  have t1 : Cnn u r ≤ 3969 * 16 * (1 + 2 * (2 + 1 / 2 ^ 15) + (2 + 1 / 2 ^ 15) ^ 2) := by
    unfold Cnn
    linarith
  have t2 : Csc u q r ≤ 127 * (4 * (1 + 4 * 1 * (1 / 2 ^ 15) + 4 * 1 ^ 2 * (1 / 2 ^ 30)) +
      2 * (1 / 2 ^ 30 + 2 * 1 * (1 / 2 ^ 15) + 1 ^ 2)) := by
    unfold Csc
    gcongr
  have t3 : Ccr u q r ≤ (256 * (80000001 / 10 ^ 7) + 64 * (80000001 / 10 ^ 7) ^ 2 *
      (1 + 1 / 2 ^ 30) ^ 5) * (1 + 2 * (2 + 1 / 2 ^ 15) + (2 + 1 / 2 ^ 15) ^ 2) := by
    unfold Ccr
    gcongr
  have hnum : (3969 : ℝ) * 16 * (1 + 2 * (2 + 1 / 2 ^ 15) + (2 + 1 / 2 ^ 15) ^ 2) +
      127 * (4 * (1 + 4 * 1 * (1 / 2 ^ 15) + 4 * 1 ^ 2 * (1 / 2 ^ 30)) +
        2 * (1 / 2 ^ 30 + 2 * 1 * (1 / 2 ^ 15) + 1 ^ 2)) +
      (256 * (80000001 / 10 ^ 7) + 64 * (80000001 / 10 ^ 7) ^ 2 * (1 + 1 / 2 ^ 30) ^ 5) *
        (1 + 2 * (2 + 1 / 2 ^ 15) + (2 + 1 / 2 ^ 15) ^ 2) ≤ 627607 := by norm_num
  unfold CU
  linarith

theorem nF_le {q r : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2 ^ 30) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2 ^ 15) :
    nF q r ≤ 218890115 / 10 ^ 8 * (1 + 5 * (1 / 2 ^ 15)) * (1 / 2 ^ 15) +
      140004 / 1000 * (1 / 2 ^ 30) := by
  have hb := bF_lt hq0 hq hr
  have hb6 := bF_ge_six hq0 (lt_of_le_of_lt hq (by norm_num)) hr0
  have hk := kappa_le
  have hk0 := kappa_nonneg
  have t1 : kappa * (1 + 5 * r) * r ≤
      218890115 / 10 ^ 8 * (1 + 5 * (1 / 2 ^ 15)) * (1 / 2 ^ 15) := by
    gcongr
  have t2 : bF q r * q ≤ 140004 / 1000 * (1 / 2 ^ 30) :=
    mul_le_mul hb.le hq hq0 (by norm_num)
  unfold nF
  linarith

theorem h0_le {q r : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2 ^ 30) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2 ^ 15) :
    h0 q r ≤ (72 * (1 / 2 ^ 30) + 37 * (1 / 2 ^ 30) * (1 / 2 ^ 15) +
      2 * (1 / 2 ^ 30) * (1 / 2 ^ 15) / (1 - 1 / 2 ^ 30)) / (1 - 36 * (1 / 2 ^ 30)) := by
  unfold h0
  have h1 : (0 : ℝ) < 1 - 36 * (1 / 2 ^ 30) := by norm_num
  have h2 : 1 - 36 * (1 / 2 ^ 30) ≤ 1 - 36 * q := by linarith
  have h3 : (0 : ℝ) < 1 - 1 / 2 ^ 30 := by norm_num
  have h4 : 1 - 1 / 2 ^ 30 ≤ 1 - q := by linarith
  have hn : 72 * q + 37 * q * r + 2 * q * r / (1 - q) ≤
      72 * (1 / 2 ^ 30) + 37 * (1 / 2 ^ 30) * (1 / 2 ^ 15) +
        2 * (1 / 2 ^ 30) * (1 / 2 ^ 15) / (1 - 1 / 2 ^ 30) := by
    have t : 2 * q * r / (1 - q) ≤ 2 * (1 / 2 ^ 30) * (1 / 2 ^ 15) / (1 - 1 / 2 ^ 30) := by
      calc 2 * q * r / (1 - q) ≤ 2 * (1 / 2 ^ 30) * (1 / 2 ^ 15) / (1 - q) := by
            apply div_le_div_of_nonneg_right _ (by linarith)
            gcongr
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) h3 h4
    have t2 : 37 * q * r ≤ 37 * (1 / 2 ^ 30) * (1 / 2 ^ 15) := by gcongr
    linarith
  have hn0 : 0 ≤ 72 * q + 37 * q * r + 2 * q * r / (1 - q) := by
    have : 0 < 1 - q := by linarith
    positivity
  calc (72 * q + 37 * q * r + 2 * q * r / (1 - q)) / (1 - 36 * q)
      ≤ (72 * (1 / 2 ^ 30) + 37 * (1 / 2 ^ 30) * (1 / 2 ^ 15) +
          2 * (1 / 2 ^ 30) * (1 / 2 ^ 15) / (1 - 1 / 2 ^ 30)) / (1 - 36 * q) :=
        div_le_div_of_nonneg_right hn (by linarith)
    _ ≤ _ := div_le_div_of_nonneg_left (le_trans hn0 hn) h1 h2

/-- **The gate `z^ι_u > 0`**, quantitatively: `z^ι_u ≥ 0.9999998` for `u ≤ 1` on the gated
domain. -/
theorem zI_ge {u q r : ℝ} (hu1 : u ≤ 1) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2 ^ 30)
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2 ^ 15) : 9999998 / 10 ^ 7 ≤ zI u q r := by
  have hh := h0_le hq0 hq hr0 hr
  have hh0 : 0 ≤ h0 q r := by
    unfold h0
    have : (0 : ℝ) < 1 - q := by linarith [show q < 1 from lt_of_le_of_lt hq (by norm_num)]
    have : (0 : ℝ) < 1 - 36 * q := by
      have : (36 : ℝ) * (1 / 2 ^ 30) < 1 := by norm_num
      linarith
    positivity
  -- the bracket is at most `1`
  have hbr : 4 * q + 36 * q * BH r ^ 2 + 2 * q / (1 - q) ≤ 1 := by
    have h1 : BH r ^ 2 ≤ (2 + 1 / 2 ^ 15) ^ 2 := by
      unfold BH
      gcongr
    have h2 : 36 * q * BH r ^ 2 ≤ 36 * (1 / 2 ^ 30) * (2 + 1 / 2 ^ 15) ^ 2 := by
      have : 0 ≤ BH r ^ 2 := sq_nonneg _
      gcongr
    have h3 : 2 * q / (1 - q) ≤ 2 * (1 / 2 ^ 30) / (1 - 1 / 2 ^ 30) := by
      calc 2 * q / (1 - q) ≤ 2 * (1 / 2 ^ 30) / (1 - q) := by
            apply div_le_div_of_nonneg_right _ (by linarith)
            linarith
        _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have hnum : 4 * (1 / 2 ^ 30) + 36 * (1 / 2 ^ 30) * (2 + 1 / 2 ^ 15) ^ 2 +
        2 * (1 / 2 ^ 30) / (1 - 1 / 2 ^ 30) ≤ (1 : ℝ) := by norm_num
    linarith
  have hsq : 0 ≤ u ^ 2 - u ^ 2 * (4 * q + 36 * q * BH r ^ 2 + 2 * q / (1 - q)) := by
    have := mul_le_mul_of_nonneg_left hbr (sq_nonneg u)
    linarith
  have hu2 : 2 * u * h0 q r ≤ 2 * 1 * h0 q r := by gcongr
  have hnum : (9999998 / 10 ^ 7 : ℝ) ≤ 1 - 2 * 1 * ((72 * (1 / 2 ^ 30) +
      37 * (1 / 2 ^ 30) * (1 / 2 ^ 15) + 2 * (1 / 2 ^ 30) * (1 / 2 ^ 15) / (1 - 1 / 2 ^ 30)) /
        (1 - 36 * (1 / 2 ^ 30))) := by norm_num
  unfold zI
  nlinarith

theorem zI_pos {u q r : ℝ} (hu1 : u ≤ 1) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2 ^ 30)
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2 ^ 15) : 0 < zI u q r :=
  lt_of_lt_of_le (by norm_num) (zI_ge hu1 hq0 hq hr0 hr)

/-- **The gate `c^ι_u < 1`**, quantitatively: `c^ι_u ≤ 0.000914` for `0 ≤ u ≤ 1` on the gated
domain. -/
theorem cI_le {u q r : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2 ^ 30)
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2 ^ 15) : cI u q r ≤ 914 / 10 ^ 6 := by
  have hq1 : q < 1 := lt_of_le_of_lt hq (by norm_num)
  have hz := zI_ge hu1 hq0 hq hr0 hr
  have hZ := Zm_ge hq0 hq hr0 hr
  have hhm : 1 - 9 * (1 / 2 ^ 30) ≤ hm q := by
    unfold hm
    linarith
  have hhm0 : (0 : ℝ) < 1 - 9 * (1 / 2 ^ 30) := by norm_num
  have hC := CU_le hu0 hu1 hq0 hq hr0 hr
  have hC0 : 0 ≤ CU u q r := by
    have hF0 := FU_nonneg hu0 hr0
    have hM0 : 0 ≤ MPhi q := by
      unfold MPhi
      have := dMu_nonneg hq0 hq1
      positivity
    have hd0 := dMu_nonneg hq0 hq1
    unfold CU Cnn Csc Ccr
    positivity
  have hn := nF_le hq0 hq hr0 hr
  have hn0 : 0 ≤ nF q r := by
    have := bF_ge_six hq0 hq1 hr0
    have := kappa_nonneg
    unfold nF
    have : 0 ≤ bF q r * q := mul_nonneg (by linarith) hq0
    positivity
  have hm1 : mU u r ≤ 2 + 2 * (1 / 2 ^ 15) := by
    unfold mU
    have : u * r ≤ 1 * (1 / 2 ^ 15) := mul_le_mul hu1 hr hr0 (by norm_num)
    have : u ^ 2 ≤ 1 := by nlinarith
    linarith
  have hm0 : 0 ≤ mU u r := by
    unfold mU
    positivity
  have hc0 : c0 q ≤ 4 / (1 - 1 / 2 ^ 30) + 2 * (1 / 2 ^ 30) := by
    unfold c0
    have : 4 / (1 - q) ≤ 4 / (1 - 1 / 2 ^ 30) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    linarith
  have hc00 : 0 ≤ c0 q := by
    unfold c0
    have : 0 < 1 - q := by linarith
    positivity
  -- the numerator
  set ε := 2 * nF q r * mU u r + CU u q r * q with hε
  have hεle : ε ≤ 2 * (218890115 / 10 ^ 8 * (1 + 5 * (1 / 2 ^ 15)) * (1 / 2 ^ 15) +
      140004 / 1000 * (1 / 2 ^ 30)) * (2 + 2 * (1 / 2 ^ 15)) + 627607 * (1 / 2 ^ 30) := by
    rw [hε]
    have t1 : nF q r * mU u r ≤ (218890115 / 10 ^ 8 * (1 + 5 * (1 / 2 ^ 15)) * (1 / 2 ^ 15) +
        140004 / 1000 * (1 / 2 ^ 30)) * (2 + 2 * (1 / 2 ^ 15)) :=
      mul_le_mul hn hm1 hm0 (le_trans hn0 hn)
    have t2 : CU u q r * q ≤ 627607 * (1 / 2 ^ 30) := mul_le_mul hC hq hq0 (by norm_num)
    linarith
  have hε0 : 0 ≤ ε := by
    rw [hε]
    have : 0 ≤ CU u q r * q := mul_nonneg hC0 hq0
    have : 0 ≤ nF q r * mU u r := mul_nonneg hn0 hm0
    linarith
  have hεhm : ε / hm q ≤ (2 * (218890115 / 10 ^ 8 * (1 + 5 * (1 / 2 ^ 15)) * (1 / 2 ^ 15) +
      140004 / 1000 * (1 / 2 ^ 30)) * (2 + 2 * (1 / 2 ^ 15)) + 627607 * (1 / 2 ^ 30)) /
        (1 - 9 * (1 / 2 ^ 30)) := by
    calc ε / hm q ≤ ε / (1 - 9 * (1 / 2 ^ 30)) := div_le_div_of_nonneg_left hε0 hhm0 hhm
      _ ≤ _ := div_le_div_of_nonneg_right hεle hhm0.le
  have hur : 2 * u * r ≤ 2 * 1 * (1 / 2 ^ 15) := by gcongr
  have huc : u ^ 2 * c0 q * q ≤
      1 ^ 2 * (4 / (1 - 1 / 2 ^ 30) + 2 * (1 / 2 ^ 30)) * (1 / 2 ^ 30) := by
    gcongr
  have hnum0 : 0 ≤ 2 * u * r + u ^ 2 * c0 q * q + ε / hm q := by
    have : 0 ≤ ε / hm q := div_nonneg hε0 (le_trans hhm0.le hhm)
    positivity
  have hden : (9999998 / 10 ^ 7) * (99999 / 100000) ≤ zI u q r * Zm q r :=
    mul_le_mul hz hZ (by norm_num) (le_trans (by norm_num) hz)
  have hden0 : (0 : ℝ) < (9999998 / 10 ^ 7) * (99999 / 100000) := by norm_num
  unfold cI
  rw [← hε]
  calc (2 * u * r + u ^ 2 * c0 q * q + ε / hm q) / (zI u q r * Zm q r)
      ≤ (2 * u * r + u ^ 2 * c0 q * q + ε / hm q) / ((9999998 / 10 ^ 7) * (99999 / 100000)) :=
        div_le_div_of_nonneg_left hnum0 hden0 hden
    _ ≤ (2 * 1 * (1 / 2 ^ 15) + 1 ^ 2 * (4 / (1 - 1 / 2 ^ 30) + 2 * (1 / 2 ^ 30)) * (1 / 2 ^ 30) +
          (2 * (218890115 / 10 ^ 8 * (1 + 5 * (1 / 2 ^ 15)) * (1 / 2 ^ 15) +
            140004 / 1000 * (1 / 2 ^ 30)) * (2 + 2 * (1 / 2 ^ 15)) + 627607 * (1 / 2 ^ 30)) /
            (1 - 9 * (1 / 2 ^ 30))) / ((9999998 / 10 ^ 7) * (99999 / 100000)) := by
        apply div_le_div_of_nonneg_right _ hden0.le
        linarith
    _ ≤ 914 / 10 ^ 6 := by norm_num

theorem cI_lt_one {u q r : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2 ^ 30)
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2 ^ 15) : cI u q r < 1 :=
  lt_of_le_of_lt (cI_le hu0 hu1 hq0 hq hr0 hr) (by norm_num)

/-! ## Uniformity: the endpoint values bound every larger prime (`prop:root-layer`)

The text: "After the explicit factor `r` in `g^ι_u` is cancelled, all numerators are positive
increasing in `q, r` and all lower denominators positive decreasing, so evaluation at `q = 1/P`,
`r = P^{-1/2}` is uniform for `p ≥ P`." Here `q = r²`, and for `0 < r ≤ r' ≤ 2⁻¹⁵`, `u ≥ 0` and the
gates at the endpoint `r'` (`z^ι_u > 0`, `c^ι_u < 1`): `g^ι_u`, `c^ι_u`, `A^ι_u`, `c^{+,ι}_u` at
`r` are at most their values at `r'` (`gI_uniform`, `cI_uniform`, `AI_uniform`,
`cPlusI_uniform`). -/

section Uniformity

variable {u q q' r r' : ℝ}

theorem FU_mono (hu : 0 ≤ u) (hr0 : 0 ≤ r) (hrr : r ≤ r') : FU u r ≤ FU u r' := by
  have hr0' : 0 ≤ r' := le_trans hr0 hrr
  unfold FU BH
  gcongr

theorem mU_mono (hu : 0 ≤ u) (hrr : r ≤ r') : mU u r ≤ mU u r' := by
  unfold mU
  gcongr

theorem Csc_mono (hu : 0 ≤ u) (hqq : q ≤ q') (hrr : r ≤ r') : Csc u q r ≤ Csc u q' r' := by
  unfold Csc
  gcongr

theorem Ccr_mono (hu : 0 ≤ u) (hq0 : 0 ≤ q) (hqq : q ≤ q') (hq1 : q' < 1) (hr0 : 0 ≤ r)
    (hrr : r ≤ r') : Ccr u q r ≤ Ccr u q' r' := by
  have hq0' : 0 ≤ q' := le_trans hq0 hqq
  have hr0' : 0 ≤ r' := le_trans hr0 hrr
  have h1 := MPhi_mono hq0 hqq hq1
  have h2 := dMu_mono hq0 hqq hq1
  have h3 := FU_mono hu hr0 hrr
  have hq1' : q < 1 := lt_of_le_of_lt hqq hq1
  have a0 := dMu_nonneg hq0 hq1'
  have a1 := MPhi_nonneg hq0 hq1'
  have a2 := FU_nonneg hu hr0
  have b0 := dMu_nonneg (le_trans hq0 hqq) hq1
  have b1 := MPhi_nonneg (le_trans hq0 hqq) hq1
  unfold Ccr
  gcongr

theorem CU_mono (hu : 0 ≤ u) (hq0 : 0 ≤ q) (hqq : q ≤ q') (hq1 : q' < 1) (hr0 : 0 ≤ r)
    (hrr : r ≤ r') : CU u q r ≤ CU u q' r' := by
  have hq0' : 0 ≤ q' := le_trans hq0 hqq
  have hr0' : 0 ≤ r' := le_trans hr0 hrr
  have h1 : Cnn u r ≤ Cnn u r' := by
    have := FU_mono hu hr0 hrr
    unfold Cnn
    linarith
  have h2 := Csc_mono hu hqq hrr
  have h3 := Ccr_mono hu hq0 hqq hq1 hr0 hrr
  unfold CU
  linarith

theorem Cin_mono (hu : 0 ≤ u) (hqq : q ≤ q') (hr0 : 0 ≤ r) (hrr : r ≤ r') :
    Cin u q r ≤ Cin u q' r' := by
  have hr0' : 0 ≤ r' := le_trans hr0 hrr
  have := FU_mono hu hr0 hrr
  unfold Cin
  gcongr

theorem c0_mono (hqq : q ≤ q') (hq1 : q' < 1) : c0 q ≤ c0 q' := by
  unfold c0
  have : 4 / (1 - q) ≤ 4 / (1 - q') :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  linarith

theorem h0_mono (hq0 : 0 ≤ q) (hqq : q ≤ q') (hq' : q' ≤ 1 / 2 ^ 30) (hr0 : 0 ≤ r)
    (hrr : r ≤ r') : h0 q r ≤ h0 q' r' := by
  have hq0' : 0 ≤ q' := le_trans hq0 hqq
  have hr0' : 0 ≤ r' := le_trans hr0 hrr
  unfold h0
  have hq1 : q' < 1 := lt_of_le_of_lt hq' (by norm_num)
  have d1 : 0 < 1 - q' := by linarith
  have d36 : 0 < 1 - 36 * q' := by
    have : (36 : ℝ) * (1 / 2 ^ 30) < 1 := by norm_num
    linarith
  have hn : 72 * q + 37 * q * r + 2 * q * r / (1 - q) ≤
      72 * q' + 37 * q' * r' + 2 * q' * r' / (1 - q') := by
    have t : 2 * q * r / (1 - q) ≤ 2 * q' * r' / (1 - q') := by
      calc 2 * q * r / (1 - q) ≤ 2 * q' * r' / (1 - q) := by
            apply div_le_div_of_nonneg_right _ (by linarith)
            gcongr
        _ ≤ 2 * q' * r' / (1 - q') :=
            div_le_div_of_nonneg_left (by positivity) d1 (by linarith)
    have t2 : 37 * q * r ≤ 37 * q' * r' := by gcongr
    linarith
  have hn0 : 0 ≤ 72 * q + 37 * q * r + 2 * q * r / (1 - q) := by
    have : 0 < 1 - q := by linarith
    positivity
  calc (72 * q + 37 * q * r + 2 * q * r / (1 - q)) / (1 - 36 * q)
      ≤ (72 * q' + 37 * q' * r' + 2 * q' * r' / (1 - q')) / (1 - 36 * q) :=
        div_le_div_of_nonneg_right hn (by linarith)
    _ ≤ _ := div_le_div_of_nonneg_left (le_trans hn0 hn) d36 (by linarith)

theorem zI_anti (hu : 0 ≤ u) (hq0 : 0 ≤ q) (hqq : q ≤ q') (hq' : q' ≤ 1 / 2 ^ 30) (hr0 : 0 ≤ r)
    (hrr : r ≤ r') : zI u q' r' ≤ zI u q r := by
  have hq0' : 0 ≤ q' := le_trans hq0 hqq
  have hr0' : 0 ≤ r' := le_trans hr0 hrr
  have hq1 : q' < 1 := lt_of_le_of_lt hq' (by norm_num)
  have hbr : 4 * q + 36 * q * BH r ^ 2 + 2 * q / (1 - q) ≤
      4 * q' + 36 * q' * BH r' ^ 2 + 2 * q' / (1 - q') := by
    have t1 : 36 * q * BH r ^ 2 ≤ 36 * q' * BH r' ^ 2 := by
      unfold BH
      have : 0 ≤ 2 + r := by linarith
      gcongr
    have t2 : 2 * q / (1 - q) ≤ 2 * q' / (1 - q') := by
      calc 2 * q / (1 - q) ≤ 2 * q' / (1 - q) := by
            apply div_le_div_of_nonneg_right _ (by linarith)
            linarith
        _ ≤ 2 * q' / (1 - q') :=
            div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
    linarith
  have hh := h0_mono hq0 hqq hq' hr0 hrr
  have t1 := mul_le_mul_of_nonneg_left hbr (sq_nonneg u)
  have t2 := mul_le_mul_of_nonneg_left hh (by linarith : (0 : ℝ) ≤ 2 * u)
  unfold zI
  nlinarith

theorem hm_anti (hqq : q ≤ q') : hm q' ≤ hm q := by
  unfold hm
  linarith

theorem Zm_anti (hq0 : 0 ≤ q) (hqq : q ≤ q') (hq' : q' ≤ 1 / 2 ^ 30) (hr0 : 0 ≤ r)
    (hrr : r ≤ r') (hr' : r' ≤ 1 / 2 ^ 15) : Zm q' r' ≤ Zm q r := by
  have hq0' : 0 ≤ q' := le_trans hq0 hqq
  have hr0' : 0 ≤ r' := le_trans hr0 hrr
  have hq1 : q' < 1 := lt_of_le_of_lt hq' (by norm_num)
  have hq1' : q < 1 := lt_of_le_of_lt hqq hq1
  have hb := bF_mono hq0 hqq hq1 hr0 hrr
  have hb6 := bF_ge_six hq0 hq1' hr0
  have hbq : bF q r * q ≤ bF q' r' * q' := mul_le_mul hb hqq hq0 (by linarith)
  have hbq0 : 0 ≤ bF q r * q := mul_nonneg (by linarith) hq0
  have hbq1 : bF q' r' * q' ≤ 1 := by
    have := bF_lt (le_trans hq0 hqq) hq' hr'
    have : bF q' r' * q' ≤ 140004 / 1000 * (1 / 2 ^ 30) :=
      mul_le_mul this.le hq' (le_trans hq0 hqq) (by norm_num)
    linarith [show (140004 / 1000 : ℝ) * (1 / 2 ^ 30) ≤ 1 by norm_num]
  have hsq : (1 - bF q' r' * q') ^ 2 ≤ (1 - bF q r * q) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have a0 := dMu_nonneg hq0 hq1'
  have a1 := MPhi_nonneg hq0 hq1'
  have h1 := MPhi_mono hq0 hqq hq1
  have h2 := dMu_mono hq0 hqq hq1
  have hW : q * (18 * MPhi q ^ 2 + 384 * MPhi q + 72 * dMu q ^ 2 * (1 + q) ^ 5) ≤
      q' * (18 * MPhi q' ^ 2 + 384 * MPhi q' + 72 * dMu q' ^ 2 * (1 + q') ^ 5) := by
    gcongr
  unfold Zm
  linarith

/-- `g^ι_u` at `q = r²` with the factor `r` cancelled:
`(2(κ(1 + 5r) + 𝔟r)m_u + C_u r)/(z^ι_u h_- Z_-)`. -/
noncomputable def gIc (u r : ℝ) : ℝ :=
  (2 * (kappa * (1 + 5 * r) + bF (r ^ 2) r * r) * mU u r + CU u (r ^ 2) r * r) /
    (zI u (r ^ 2) r * hm (r ^ 2) * Zm (r ^ 2) r)

theorem gI_eq_gIc (hr : r ≠ 0) : gI u (r ^ 2) r = gIc u r := by
  unfold gI gIc
  have hn : 2 * nF (r ^ 2) r * mU u r + CU u (r ^ 2) r * r ^ 2 =
      r * (2 * (kappa * (1 + 5 * r) + bF (r ^ 2) r * r) * mU u r + CU u (r ^ 2) r * r) := by
    unfold nF
    ring
  have hd : r * zI u (r ^ 2) r * hm (r ^ 2) * Zm (r ^ 2) r =
      r * (zI u (r ^ 2) r * hm (r ^ 2) * Zm (r ^ 2) r) := by ring
  rw [hn, hd, mul_div_mul_left _ _ hr]

theorem sq_le_of_le (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2 ^ 15) : r ^ 2 ≤ 1 / 2 ^ 30 := by
  calc r ^ 2 ≤ (1 / 2 ^ 15) ^ 2 := pow_le_pow_left₀ hr0 hr 2
    _ = 1 / 2 ^ 30 := by norm_num

/-- The three denominators decrease, and are positive at the endpoint. -/
theorem denoms_anti (hu : 0 ≤ u) (hr0 : 0 ≤ r) (hrr : r ≤ r') (hr' : r' ≤ 1 / 2 ^ 15)
    (hz : 0 < zI u (r' ^ 2) r') :
    0 < zI u (r' ^ 2) r' ∧ zI u (r' ^ 2) r' ≤ zI u (r ^ 2) r ∧ 0 < hm (r' ^ 2) ∧
      hm (r' ^ 2) ≤ hm (r ^ 2) ∧ 0 < Zm (r' ^ 2) r' ∧ Zm (r' ^ 2) r' ≤ Zm (r ^ 2) r := by
  have hr0' : 0 ≤ r' := le_trans hr0 hrr
  have hr0' : 0 ≤ r' := le_trans hr0 hrr
  have hq' := sq_le_of_le hr0' hr'
  have hqq : r ^ 2 ≤ r' ^ 2 := pow_le_pow_left₀ hr0 hrr 2
  exact ⟨hz, zI_anti hu (sq_nonneg r) hqq hq' hr0 hrr, hm_pos hq', hm_anti hqq,
    Zm_pos (sq_nonneg r') hq' hr0' hr', Zm_anti (sq_nonneg r) hqq hq' hr0 hrr hr'⟩

/-- **Uniformity of `g^ι_u`** (`prop:root-layer`): for `0 < r ≤ r' ≤ 2⁻¹⁵` (`q = r²`), `u ≥ 0` and
`z^ι_u > 0` at `r'`, `g^ι_u(r) ≤ g^ι_u(r')`. -/
theorem gI_uniform (hu : 0 ≤ u) (hr : 0 < r) (hrr : r ≤ r') (hr' : r' ≤ 1 / 2 ^ 15)
    (hz : 0 < zI u (r' ^ 2) r') : gI u (r ^ 2) r ≤ gI u (r' ^ 2) r' := by
  have hr'0 : 0 < r' := lt_of_lt_of_le hr hrr
  rw [gI_eq_gIc hr.ne', gI_eq_gIc hr'0.ne']
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := denoms_anti hu hr.le hrr hr' hz
  have hq' := sq_le_of_le hr'0.le hr'
  have hqq : r ^ 2 ≤ r' ^ 2 := pow_le_pow_left₀ hr.le hrr 2
  have hq1 : r' ^ 2 < 1 := lt_of_le_of_lt hq' (by norm_num)
  have hb := bF_mono (sq_nonneg r) hqq hq1 hr.le hrr
  have hb6 := bF_ge_six (sq_nonneg r) (lt_of_le_of_lt hqq hq1) hr.le
  have hk := kappa_nonneg
  have hm1 := mU_mono hu hrr (r := r) (r' := r')
  have hm0 : 0 ≤ mU u r := by unfold mU; positivity
  have hC := CU_mono hu (sq_nonneg r) hqq hq1 hr.le hrr
  have hC0 := CU_nonneg hu (sq_nonneg r) (lt_of_le_of_lt hqq hq1) hr.le
  have hn : 2 * (kappa * (1 + 5 * r) + bF (r ^ 2) r * r) * mU u r + CU u (r ^ 2) r * r ≤
      2 * (kappa * (1 + 5 * r') + bF (r' ^ 2) r' * r') * mU u r' + CU u (r' ^ 2) r' * r' := by
    have t1 : kappa * (1 + 5 * r) + bF (r ^ 2) r * r ≤
        kappa * (1 + 5 * r') + bF (r' ^ 2) r' * r' := by
      have : kappa * (1 + 5 * r) ≤ kappa * (1 + 5 * r') := by gcongr
      have : bF (r ^ 2) r * r ≤ bF (r' ^ 2) r' * r' := mul_le_mul hb hrr hr.le (by linarith)
      linarith
    have t10 : 0 ≤ kappa * (1 + 5 * r) + bF (r ^ 2) r * r := by
      have : 0 ≤ bF (r ^ 2) r * r := mul_nonneg (by linarith) hr.le
      positivity
    have t2 : (kappa * (1 + 5 * r) + bF (r ^ 2) r * r) * mU u r ≤
        (kappa * (1 + 5 * r') + bF (r' ^ 2) r' * r') * mU u r' :=
      mul_le_mul t1 hm1 hm0 (le_trans t10 t1)
    have t3 : CU u (r ^ 2) r * r ≤ CU u (r' ^ 2) r' * r' := mul_le_mul hC hrr hr.le (by linarith)
    linarith
  have hn0 : 0 ≤ 2 * (kappa * (1 + 5 * r) + bF (r ^ 2) r * r) * mU u r + CU u (r ^ 2) r * r := by
    have : 0 ≤ bF (r ^ 2) r * r := mul_nonneg (by linarith) hr.le
    have : 0 ≤ CU u (r ^ 2) r * r := mul_nonneg hC0 hr.le
    positivity
  have hd : zI u (r' ^ 2) r' * hm (r' ^ 2) * Zm (r' ^ 2) r' ≤
      zI u (r ^ 2) r * hm (r ^ 2) * Zm (r ^ 2) r := by
    have := mul_le_mul a2 a4 a3.le (le_trans a1.le a2)
    exact mul_le_mul this a6 a5.le (mul_nonneg (le_trans a1.le a2) (le_trans a3.le a4))
  have hd0 : 0 < zI u (r' ^ 2) r' * hm (r' ^ 2) * Zm (r' ^ 2) r' := by positivity
  unfold gIc
  calc _ ≤ (2 * (kappa * (1 + 5 * r') + bF (r' ^ 2) r' * r') * mU u r' + CU u (r' ^ 2) r' * r') /
        (zI u (r ^ 2) r * hm (r ^ 2) * Zm (r ^ 2) r) :=
        div_le_div_of_nonneg_right hn (le_trans hd0.le hd)
    _ ≤ _ := div_le_div_of_nonneg_left (le_trans hn0 hn) hd0 hd

/-- The numerator `2𝔫m_u + C_u q` of the lower bound increases in `r` (`q = r²`). -/
theorem eps_mono (hu : 0 ≤ u) (hr0 : 0 ≤ r) (hrr : r ≤ r') (hr' : r' ≤ 1 / 2 ^ 15) :
    2 * nF (r ^ 2) r * mU u r + CU u (r ^ 2) r * r ^ 2 ≤
      2 * nF (r' ^ 2) r' * mU u r' + CU u (r' ^ 2) r' * r' ^ 2 := by
  have hr0' : 0 ≤ r' := le_trans hr0 hrr
  have hr0' : 0 ≤ r' := le_trans hr0 hrr
  have hq' := sq_le_of_le hr0' hr'
  have hqq : r ^ 2 ≤ r' ^ 2 := pow_le_pow_left₀ hr0 hrr 2
  have hq1 : r' ^ 2 < 1 := lt_of_le_of_lt hq' (by norm_num)
  have hn := nF_mono (sq_nonneg r) hqq hq1 hr0 hrr
  have hn0 := nF_nonneg (sq_nonneg r) (lt_of_le_of_lt hqq hq1) hr0
  have hm1 := mU_mono hu hrr (r := r) (r' := r')
  have hm0 : 0 ≤ mU u r := by unfold mU; positivity
  have hC := CU_mono hu (sq_nonneg r) hqq hq1 hr0 hrr
  have hC0 := CU_nonneg hu (sq_nonneg r) (lt_of_le_of_lt hqq hq1) hr0
  have t1 : nF (r ^ 2) r * mU u r ≤ nF (r' ^ 2) r' * mU u r' := mul_le_mul hn hm1 hm0 (by linarith)
  have t2 : CU u (r ^ 2) r * r ^ 2 ≤ CU u (r' ^ 2) r' * r' ^ 2 :=
    mul_le_mul hC hqq (sq_nonneg r) (by linarith)
  linarith

/-- **Uniformity of `c^ι_u`** (`prop:root-layer`). -/
theorem cI_uniform (hu : 0 ≤ u) (hr : 0 < r) (hrr : r ≤ r') (hr' : r' ≤ 1 / 2 ^ 15)
    (hz : 0 < zI u (r' ^ 2) r') : cI u (r ^ 2) r ≤ cI u (r' ^ 2) r' := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := denoms_anti hu hr.le hrr hr' hz
  have hr'0 : 0 ≤ r' := le_trans hr.le hrr
  have hq' := sq_le_of_le hr'0 hr'
  have hqq : r ^ 2 ≤ r' ^ 2 := pow_le_pow_left₀ hr.le hrr 2
  have hq1 : r' ^ 2 < 1 := lt_of_le_of_lt hq' (by norm_num)
  have he := eps_mono hu hr.le hrr hr'
  have he0 : 0 ≤ 2 * nF (r ^ 2) r * mU u r + CU u (r ^ 2) r * r ^ 2 := by
    have := nF_nonneg (sq_nonneg r) (lt_of_le_of_lt hqq hq1) hr.le
    have := CU_nonneg hu (sq_nonneg r) (lt_of_le_of_lt hqq hq1) hr.le
    have : 0 ≤ mU u r := by unfold mU; positivity
    positivity
  have hc := c0_mono hqq hq1
  have hc0 := c0_nonneg (sq_nonneg r) (lt_of_le_of_lt hqq hq1)
  have hc0' := c0_nonneg (sq_nonneg r') hq1
  have hnum : 2 * u * r + u ^ 2 * c0 (r ^ 2) * r ^ 2 +
        (2 * nF (r ^ 2) r * mU u r + CU u (r ^ 2) r * r ^ 2) / hm (r ^ 2) ≤
      2 * u * r' + u ^ 2 * c0 (r' ^ 2) * r' ^ 2 +
        (2 * nF (r' ^ 2) r' * mU u r' + CU u (r' ^ 2) r' * r' ^ 2) / hm (r' ^ 2) := by
    have t1 : 2 * u * r ≤ 2 * u * r' := by gcongr
    have t2 : u ^ 2 * c0 (r ^ 2) * r ^ 2 ≤ u ^ 2 * c0 (r' ^ 2) * r' ^ 2 := by gcongr
    have t3 : (2 * nF (r ^ 2) r * mU u r + CU u (r ^ 2) r * r ^ 2) / hm (r ^ 2) ≤
        (2 * nF (r' ^ 2) r' * mU u r' + CU u (r' ^ 2) r' * r' ^ 2) / hm (r' ^ 2) := by
      calc _ ≤ (2 * nF (r' ^ 2) r' * mU u r' + CU u (r' ^ 2) r' * r' ^ 2) / hm (r ^ 2) :=
            div_le_div_of_nonneg_right he (le_trans a3.le a4)
        _ ≤ _ := div_le_div_of_nonneg_left (le_trans he0 he) a3 a4
    linarith
  have hnum0 : 0 ≤ 2 * u * r + u ^ 2 * c0 (r ^ 2) * r ^ 2 +
      (2 * nF (r ^ 2) r * mU u r + CU u (r ^ 2) r * r ^ 2) / hm (r ^ 2) := by
    have : 0 ≤ (2 * nF (r ^ 2) r * mU u r + CU u (r ^ 2) r * r ^ 2) / hm (r ^ 2) :=
      div_nonneg he0 (le_trans a3.le a4)
    have : 0 ≤ u ^ 2 * c0 (r ^ 2) * r ^ 2 := by positivity
    have : 0 ≤ 2 * u * r := by positivity
    linarith
  have hd : zI u (r' ^ 2) r' * Zm (r' ^ 2) r' ≤ zI u (r ^ 2) r * Zm (r ^ 2) r :=
    mul_le_mul a2 a6 a5.le (le_trans a1.le a2)
  have hd0 : 0 < zI u (r' ^ 2) r' * Zm (r' ^ 2) r' := mul_pos a1 a5
  unfold cI
  calc _ ≤ (2 * u * r' + u ^ 2 * c0 (r' ^ 2) * r' ^ 2 +
        (2 * nF (r' ^ 2) r' * mU u r' + CU u (r' ^ 2) r' * r' ^ 2) / hm (r' ^ 2)) /
          (zI u (r ^ 2) r * Zm (r ^ 2) r) := div_le_div_of_nonneg_right hnum (le_trans hd0.le hd)
    _ ≤ _ := div_le_div_of_nonneg_left (le_trans hnum0 hnum) hd0 hd

/-- **Uniformity of `A^ι_u`** (`prop:root-layer`). -/
theorem AI_uniform (hu : 0 ≤ u) (hr : 0 < r) (hrr : r ≤ r') (hr' : r' ≤ 1 / 2 ^ 15)
    (hz : 0 < zI u (r' ^ 2) r') : AI u (r ^ 2) r ≤ AI u (r' ^ 2) r' := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := denoms_anti hu hr.le hrr hr' hz
  have hr'0 : 0 ≤ r' := le_trans hr.le hrr
  have hq' := sq_le_of_le hr'0 hr'
  have hqq : r ^ 2 ≤ r' ^ 2 := pow_le_pow_left₀ hr.le hrr 2
  have hq1 : r' ^ 2 < 1 := lt_of_le_of_lt hq' (by norm_num)
  have hq1' : r ^ 2 < 1 := lt_of_le_of_lt hqq hq1
  have hC := CU_mono hu (sq_nonneg r) hqq hq1 hr.le hrr
  have hC0 := CU_nonneg hu (sq_nonneg r) hq1' hr.le
  have hCi := Cin_mono hu hqq hr.le hrr (u := u)
  have hCi0 := Cin_nonneg hu (sq_nonneg r) hr.le (u := u)
  have hb := bF_mono (sq_nonneg r) hqq hq1 hr.le hrr
  have hb6 := bF_ge_six (sq_nonneg r) hq1' hr.le
  have hb6' := bF_ge_six (sq_nonneg r') hq1 hr'0
  have hbh : 2 * (1 + u ^ 2) * bF (r ^ 2) r / hm (r ^ 2) ≤
      2 * (1 + u ^ 2) * bF (r' ^ 2) r' / hm (r' ^ 2) := by
    have e1 : 2 * (1 + u ^ 2) * bF (r ^ 2) r ≤ 2 * (1 + u ^ 2) * bF (r' ^ 2) r' := by gcongr
    calc _ ≤ 2 * (1 + u ^ 2) * bF (r' ^ 2) r' / hm (r ^ 2) :=
          div_le_div_of_nonneg_right e1 (le_trans a3.le a4)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) a3 a4
  have hbh0 : 0 ≤ 2 * (1 + u ^ 2) * bF (r ^ 2) r / hm (r ^ 2) :=
    div_nonneg (by positivity) (le_trans a3.le a4)
  have hnum : CU u (r ^ 2) r + Cin u (r ^ 2) r + 910 * u ^ 2 +
        2 * (1 + u ^ 2) * bF (r ^ 2) r / hm (r ^ 2) ≤
      CU u (r' ^ 2) r' + Cin u (r' ^ 2) r' + 910 * u ^ 2 +
        2 * (1 + u ^ 2) * bF (r' ^ 2) r' / hm (r' ^ 2) := by linarith
  have hnum0 : 0 ≤ CU u (r ^ 2) r + Cin u (r ^ 2) r + 910 * u ^ 2 +
      2 * (1 + u ^ 2) * bF (r ^ 2) r / hm (r ^ 2) := by positivity
  have hd : zI u (r' ^ 2) r' * hm (r' ^ 2) * Zm (r' ^ 2) r' ≤
      zI u (r ^ 2) r * hm (r ^ 2) * Zm (r ^ 2) r := by
    have := mul_le_mul a2 a4 a3.le (le_trans a1.le a2)
    exact mul_le_mul this a6 a5.le (mul_nonneg (le_trans a1.le a2) (le_trans a3.le a4))
  have hd0 : 0 < zI u (r' ^ 2) r' * hm (r' ^ 2) * Zm (r' ^ 2) r' := by positivity
  unfold AI
  calc _ ≤ (CU u (r' ^ 2) r' + Cin u (r' ^ 2) r' + 910 * u ^ 2 +
        2 * (1 + u ^ 2) * bF (r' ^ 2) r' / hm (r' ^ 2)) /
          (zI u (r ^ 2) r * hm (r ^ 2) * Zm (r ^ 2) r) :=
        div_le_div_of_nonneg_right hnum (le_trans hd0.le hd)
    _ ≤ _ := div_le_div_of_nonneg_left (le_trans hnum0 hnum) hd0 hd

theorem AI_nonneg (hu : 0 ≤ u) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2 ^ 15) (hz : 0 < zI u (r ^ 2) r) :
    0 ≤ AI u (r ^ 2) r := by
  have hq := sq_le_of_le hr0 hr
  have hq1 : r ^ 2 < 1 := lt_of_le_of_lt hq (by norm_num)
  have hC0 := CU_nonneg hu (sq_nonneg r) hq1 hr0
  have hCi0 := Cin_nonneg hu (sq_nonneg r) hr0 (u := u)
  have hb6 := bF_ge_six (sq_nonneg r) hq1 hr0
  have hh := hm_pos hq
  have hZ := Zm_pos (sq_nonneg r) hq hr0 hr
  have : 0 ≤ 2 * (1 + u ^ 2) * bF (r ^ 2) r / hm (r ^ 2) := div_nonneg (by positivity) hh.le
  unfold AI
  positivity

/-- **Uniformity of `c^{+,ι}_u`** (`prop:root-layer`): with the gates `z^ι_u > 0` and
`c^ι_u < 1` at the endpoint `r'`, `c^{+,ι}_u(r) ≤ c^{+,ι}_u(r')`. -/
theorem cPlusI_uniform (hu : 0 ≤ u) (hr : 0 < r) (hrr : r ≤ r') (hr' : r' ≤ 1 / 2 ^ 15)
    (hz : 0 < zI u (r' ^ 2) r') (hc : cI u (r' ^ 2) r' < 1) :
    cPlusI u (r ^ 2) r ≤ cPlusI u (r' ^ 2) r' := by
  have hr'0 : 0 ≤ r' := le_trans hr.le hrr
  have hqq : r ^ 2 ≤ r' ^ 2 := pow_le_pow_left₀ hr.le hrr 2
  have hzr : 0 < zI u (r ^ 2) r :=
    lt_of_lt_of_le hz (denoms_anti hu hr.le hrr hr' hz).2.1
  have hA := AI_uniform hu hr hrr hr' hz
  have hA0 := AI_nonneg hu hr.le (le_trans hrr hr') hzr
  have hc1 := cI_uniform hu hr hrr hr' hz
  have hd0 : 0 < 1 - cI u (r' ^ 2) r' := by linarith
  have hd : 1 - cI u (r' ^ 2) r' ≤ 1 - cI u (r ^ 2) r := by linarith
  have hn : r ^ 2 * AI u (r ^ 2) r ^ 2 ≤ r' ^ 2 * AI u (r' ^ 2) r' ^ 2 := by gcongr
  have hn0 : 0 ≤ r ^ 2 * AI u (r ^ 2) r ^ 2 := by positivity
  unfold cPlusI
  calc _ ≤ r' ^ 2 * AI u (r' ^ 2) r' ^ 2 / (1 - cI u (r ^ 2) r) :=
        div_le_div_of_nonneg_right hn (le_trans hd0.le hd)
    _ ≤ _ := div_le_div_of_nonneg_left (le_trans hn0 hn) hd0 hd

end Uniformity

/-! ## The limit `g^ι_u → √3 + √7` (`prop:root-layer`) -/

/-- `g^ι_u` (with `r` cancelled, `q = r²`) is continuous at `r = 0`. -/
theorem gIc_continuousAt (u : ℝ) : ContinuousAt (fun r : ℝ => gIc u r) 0 := by
  have hN : ContinuousAt (fun r : ℝ => 2 * (kappa * (1 + 5 * r) + bF (r ^ 2) r * r) * mU u r +
      CU u (r ^ 2) r * r) 0 := by
    simp only [bF, d2, dMu, CU, Cnn, Csc, Ccr, FU, BH, MPhi, mU, kappa]
    fun_prop (disch := norm_num)
  have hD : ContinuousAt (fun r : ℝ => zI u (r ^ 2) r * hm (r ^ 2) * Zm (r ^ 2) r) 0 := by
    simp only [zI, h0, hm, Zm, bF, d2, dMu, MPhi, BH]
    fun_prop (disch := norm_num)
  have hD0 : zI u (0 ^ 2) 0 * hm (0 ^ 2) * Zm (0 ^ 2) 0 ≠ 0 := by
    simp [zI, h0, hm, Zm]
    positivity
  exact hN.div hD hD0

/-- At `r = 0`: `2κ(1 + γ)/(1 + γ) = 2κ = √3 + √7`. -/
theorem gIc_zero (u : ℝ) : gIc u 0 = Real.sqrt 3 + Real.sqrt 7 := by
  have h : (1 + u ^ 2) ≠ 0 := by positivity
  unfold gIc
  simp [zI, h0, hm, Zm, mU, kappa]
  field_simp

/-- **`prop:root-layer`: `g^ι_u → √3 + √7`** as `r = p^{-1/2} → 0⁺` (`q = r²`), for every `u`:
"As `q → 0`, `𝔫/r → κ` and `m_u` and `z^ι_u` tend to `1 + γ`, so `g^ι_u → 2κ = √3 + √7`." -/
theorem gI_tendsto (u : ℝ) :
    Filter.Tendsto (fun r => gI u (r ^ 2) r) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.sqrt 3 + Real.sqrt 7)) := by
  have h1 : Filter.Tendsto (fun r => gIc u r) (nhdsWithin 0 (Set.Ioi 0)) (nhds (gIc u 0)) :=
    (gIc_continuousAt u).tendsto.mono_left nhdsWithin_le_nhds
  rw [gIc_zero] at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (gI_eq_gIc (u := u) (Set.mem_Ioi.mp hr).ne').symm

/-- **`prop:root-layer`: `g^ι_u → √3 + √7` as `p → ∞`** (`q = 1/p`, `r = p^{-1/2}`). -/
theorem gI_tendsto_atTop (u : ℝ) :
    Filter.Tendsto (fun p : ℝ => gI u (1 / p) (1 / Real.sqrt p)) Filter.atTop
      (nhds (Real.sqrt 3 + Real.sqrt 7)) := by
  have hr : Filter.Tendsto (fun p : ℝ => 1 / Real.sqrt p) Filter.atTop
      (nhdsWithin 0 (Set.Ioi 0)) := by
    have h := tendsto_inv_atTop_nhdsGT_zero.comp Real.tendsto_sqrt_atTop
    exact Filter.Tendsto.congr (fun p => by simp [one_div]) h
  have h := (gI_tendsto u).comp hr
  refine h.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with p hp
  simp only [Function.comp]
  rw [div_pow, one_pow, Real.sq_sqrt hp.le]

end Layer

end Sarkozy.PositiveRoots
