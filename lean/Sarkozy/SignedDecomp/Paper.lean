module

public import Sarkozy.SignedDecomp.Poly
public import Sarkozy.PrimeGram.BlockRef
public import Sarkozy.MiddleRecords.OldFCapCert

@[expose] public section

/-!
# The paper's constants `c_col`, `e_sg`, `c_+` at a prime, and their majorants (SD2)

`paper/sections/21_middle_records.tex`, `eq:signed-constants`, `prop:signed-bounds`(c),
`lem:record:conditional-collision`(d), `lem:actual-features`(d); `lem:majorant`.

* **The literal formulas** of `eq:signed-constants` (`ncL`, `ccL`, `McL`, `rho02L`, `EcL`, `cpL`,
  `esgL`), with `c_g = cgC`, `D_g = DgC` (PG's), `t = tPaper = 127/500`, `k_col = 9/4` (the paper's
  value for `t ≥ 2/(p - 1)`, i.e. every `p ≥ 2²⁴` at this `t`).
* **At the prime `p_i` of a block**, at `(q, r) = (1/p, p^{-1/2})`, with `e₀ = e0 p` and
  `Γ_A = GammaA (1/p) (p^{-1/2})` (W6's `Γ_A` of `lem:actual-features`(d)):
  - `ccolP`: `c_col`, W6's `cColS` with `(1 - e₀)^{3/2} = (1 - e₀)√(1 - e₀)`;
  - `esgP`: `e_sg`;
  - `cpP`: `c_+`.
  These are the constants of the hypotheses `CollisionBound`, `NewDecomp` and the component norms.
* **Identification with the polynomial forms** at the atoms `atomsAt p Γ`
  (`esgL_eq`, `cpL_eq`, `eoC_eq`, `cColS_eq`, `GammaA_eq`).
* **The atoms decrease along the primes** (`atomsAt_le`): for `p ≥ X ≥ 2²⁴` and `s² ≤ X`, the atoms
  at `p` are below the rational atoms `atomsQ X s Γ'` evaluated at the piece start. This is the
  monotonicity `lem:majorant` (evaluation at the piece start bounds every larger prime).
-/

namespace Sarkozy.SignedDecomp

open Sarkozy.PrimeGram Sarkozy.MiddleRecords
open Sarkozy.SignedEstimates (e0)
open Sarkozy.MainFinal2 (tPaper)

/-! ## The literal formulas of `eq:signed-constants` -/

/-- `n_c = (18/Z + 3)/(1 - e₀) + (1 + 2q)c_g/q`, `Z = (1 - q)(1 - 2q)`. -/
noncomputable def ncL (q e : ℝ) : ℝ :=
  (18 / ((1 - q) * (1 - 2 * q)) + 3) / (1 - e) + (1 + 2 * q) * cgC e / q

/-- `c_c = √3 Γ_A + (n_c + (D_g/q)√3 Γ_A r) r`. -/
noncomputable def ccL (q r e Γ : ℝ) : ℝ :=
  √3 * Γ + (ncL q e + DgC e / q * √3 * Γ * r) * r

/-- `M_c = (2η_c + (1 + η_c)e₀)/(h_c(1 - e₀))`, `η_c = 10q`, `h_c = 1 - η_c`
(`lem:signed-components`(c)). -/
noncomputable def McL (q e : ℝ) : ℝ := (2 * (10 * q) + (1 + 10 * q) * e) / ((1 - 10 * q) * (1 - e))

/-- `ϱ₀₂ = r√(1 + q)/(1 - q)` (`lem:actual-features`(b)). -/
noncomputable def rho02L (q r : ℝ) : ℝ := r * √(1 + q) / (1 - q)

/-- `E_c = 10c_c r/h_c + (2M_c/q)(c_c r/h_c + 2ϱ₀₂)`. -/
noncomputable def EcL (q r e Γ : ℝ) : ℝ :=
  10 * ccL q r e Γ * r / (1 - 10 * q) +
    2 * McL q e / q * (ccL q r e Γ * r / (1 - 10 * q) + 2 * rho02L q r)

/-- **`c_+ = √3 Γ_A + (n_c + (D_g/q)√3 Γ_A r + E_c) r`** (`eq:signed-constants`). -/
noncomputable def cpL (q r e Γ : ℝ) : ℝ :=
  √3 * Γ + (ncL q e + DgC e / q * √3 * Γ * r + EcL q r e Γ) * r

/-- **`e_sg`** (`eq:signed-constants`) at `t = tPaper`, `k_col = 9/4`:
`((18 - 12t)/Z + k_col)/(1 - e₀) + (1 + 2q)c_g/q + (D_g/q)√(3 + 2t²)Γ_A r + (1 + t)E_c`. -/
noncomputable def esgL (q r e Γ : ℝ) : ℝ :=
  ((18 - 12 * tPaper) / ((1 - q) * (1 - 2 * q)) + 9 / 4) / (1 - e) + (1 + 2 * q) * cgC e / q +
    DgC e / q * √(3 + 2 * tPaper ^ 2) * Γ * r + (1 + tPaper) * EcL q r e Γ

/-! ## The constants at the primes of a block -/

section Prime

variable {ι : Type} (pr : ι → ℕ)

/-- `Γ_A(1/p_i, p_i^{-1/2})` (W6's `GammaA`). -/
noncomputable def GammaAP (i : ι) : ℝ := GammaA (pr i : ℝ)⁻¹ (rP pr i)

/-- **`c_col` at the prime `p_i`** (`eq:signed-constants`; W6's `cColS`). -/
noncomputable def ccolP (i : ι) : ℝ := cColS (pr i : ℝ)⁻¹ (rP pr i) (√(1 - eZero (pr i : ℝ)⁻¹))

/-- **`e_sg` at the prime `p_i`** (`eq:signed-constants`, `t = 127/500`, `k_col = 9/4`). -/
noncomputable def esgP (i : ι) : ℝ := esgL (pr i : ℝ)⁻¹ (rP pr i) (e0 (pr i : ℝ)) (GammaAP pr i)

/-- **`c_+` at the prime `p_i`** (`eq:signed-constants`). -/
noncomputable def cpP (i : ι) : ℝ := cpL (pr i : ℝ)⁻¹ (rP pr i) (e0 (pr i : ℝ)) (GammaAP pr i)

end Prime

/-! ## The atoms at a prime, and the identification -/

/-- **The atoms at `p = n`** with frame constant `Γ`. -/
noncomputable def atomsAt (n Γ : ℝ) : Atoms ℝ where
  q := n⁻¹
  r := (√n)⁻¹
  e := e0 n
  u := e0 n / n⁻¹
  Γ := Γ
  s1 := √(1 + n⁻¹)
  s3 := √3
  sa := √(3 + 2 * tPaper ^ 2)
  j1 := 1 / (1 - n⁻¹)
  j2 := 1 / (1 - 2 * n⁻¹)
  je := 1 / (1 - e0 n)
  j10 := 1 / (1 - 10 * n⁻¹)
  j14 := 1 / (1 - 14 * n⁻¹)
  k3 := 1 / √(1 - e0 n)

theorem McL_div {q e : ℝ} (hq : q ≠ 0) :
    McL q e / q = (20 + (1 + 10 * q) * (e / q)) * (1 / (1 - 10 * q) * (1 / (1 - e))) := by
  unfold McL
  field_simp
  ring

/-- `e_sg` is `esgPoly` at the atoms. -/
theorem esgL_eq {n : ℝ} (hn : 0 < n) (Γ : ℝ) :
    esgL n⁻¹ (√n)⁻¹ (e0 n) Γ = esgPoly (atomsAt n Γ) := by
  have hq : (n⁻¹ : ℝ) ≠ 0 := inv_ne_zero hn.ne'
  unfold esgL EcL
  rw [mul_div_assoc 2 (McL n⁻¹ (e0 n)), McL_div hq]
  simp only [esgPoly, ecPoly, ccPoly, ncPoly, mcqPoly, cgq, dgq, atomsAt, ccL, ncL, rho02L, cgC,
    DgC, tPaper]
  simp only [div_eq_mul_inv, mul_inv, ← inv_pow, inv_inv, one_mul]
  ring

/-- `c_+` is `cpPoly` at the atoms. -/
theorem cpL_eq {n : ℝ} (hn : 0 < n) (Γ : ℝ) :
    cpL n⁻¹ (√n)⁻¹ (e0 n) Γ = cpPoly (atomsAt n Γ) := by
  have hq : (n⁻¹ : ℝ) ≠ 0 := inv_ne_zero hn.ne'
  unfold cpL EcL
  rw [mul_div_assoc 2 (McL n⁻¹ (e0 n)), McL_div hq]
  simp only [cpPoly, ecPoly, ccPoly, ncPoly, mcqPoly, cgq, dgq, atomsAt, ccL, ncL, rho02L, cgC,
    DgC]
  simp only [div_eq_mul_inv, mul_inv, ← inv_pow, inv_inv, one_mul]
  ring

/-- PG's `e_o` is `eoPoly` at the atoms. -/
theorem eoC_eq (n Γ c : ℝ) : eoC n⁻¹ (√n)⁻¹ (e0 n) Γ c = eoPoly (atomsAt n Γ) c := by
  simp only [eoC, roC, noC, eoPoly, roPoly, cgq, dgq, atomsAt, cgC, DgC]
  simp only [div_eq_mul_inv, mul_inv, ← inv_pow, inv_inv, one_mul]
  ring

theorem eZero_inv {n : ℝ} (hn : 5 ≤ n) : eZero n⁻¹ = e0 n := by
  rw [Sarkozy.SignedEstimates.e0_eq_paper hn, eZero, one_div]

/-- W6's `c_col` is `ccolPoly` at the atoms. -/
theorem cColS_eq {n : ℝ} (hn : 5 ≤ n) (Γ : ℝ) :
    cColS n⁻¹ (√n)⁻¹ (√(1 - eZero n⁻¹)) = ccolPoly (atomsAt n Γ) := by
  rw [eZero_inv hn]
  simp only [cColS, ccolPoly, atomsAt, eZero_inv hn]
  simp only [div_eq_mul_inv, mul_inv, ← inv_pow, one_mul]

/-- W6's `Γ_A` is `gamPoly`. -/
theorem GammaA_eq (q r : ℝ) :
    GammaA q r = gamPoly q r √(1 + q) √(1 + 4 * q / (1 - 4 * q) ^ 2) (1 / (1 - q))
      (1 / (1 - 4 * q)) := by
  unfold GammaA gamPoly
  simp only [div_eq_mul_inv, mul_inv, ← inv_pow, one_mul]

/-! ## The rational atoms at a piece start -/

/-- `u_X = 2/((1 - 3q)(1 - 4q))` at `q = 1/X`. -/
def uQ (X : ℕ) : ℚ := 2 / ((1 - 3 / X) * (1 - 4 / X))

/-- `e₀(X) = q_X u_X`. -/
def eQ (X : ℕ) : ℚ := 1 / X * uQ X

/-- A rational upper bound for `√3`. -/
def s3U : ℚ := 17320508076 / 10 ^ 10

/-- A rational upper bound for `√(3 + 2t²)`, `t = 127/500`. -/
def saU : ℚ := 17689070072 / 10 ^ 10

/-- **The rational atoms at the piece start `X`**, with `r_X = 1/s` (`s² ≤ X`) and frame constant
`Γ`: `√(1 + q) ≤ 1 + q/2`, `1/√(1 - e₀) ≤ 1/(1 - e₀)`, `√3 ≤ s3U`, `√(3 + 2t²) ≤ saU`. -/
def atomsQ (X s : ℕ) (Γ : ℚ) : Atoms ℚ where
  q := 1 / X
  r := 1 / s
  e := eQ X
  u := uQ X
  Γ := Γ
  s1 := 1 + 1 / X / 2
  s3 := s3U
  sa := saU
  j1 := 1 / (1 - 1 / X)
  j2 := 1 / (1 - 2 / X)
  je := 1 / (1 - eQ X)
  j10 := 1 / (1 - 10 / X)
  j14 := 1 / (1 - 14 / X)
  k3 := 1 / (1 - eQ X)

/-- `j₄ = 1/(1 - 4q)` at `X`. -/
def j4Q (X : ℕ) : ℚ := 1 / (1 - 4 / X)

/-- **The rational majorant of `Γ_A` at the piece start**: `gamPoly` with `√(1 + q) ≤ 1 + q/2` and
`√(1 + 4q j₄²) ≤ 1 + 2q j₄²`. -/
def gamQ (X s : ℕ) : ℚ :=
  gamPoly (1 / X) (1 / s) (1 + 1 / X / 2) (1 + 4 * (1 / X) * j4Q X ^ 2 / 2) (1 / (1 - 1 / X))
    (j4Q X)

theorem sqrt3_le : √3 ≤ ((s3U : ℚ) : ℝ) := by
  rw [Real.sqrt_le_left (by norm_num [s3U])]
  norm_num [s3U]

theorem sqrtA_le : √(3 + 2 * tPaper ^ 2) ≤ ((saU : ℚ) : ℝ) := by
  rw [Real.sqrt_le_left (by norm_num [saU])]
  norm_num [saU, tPaper]

theorem sqrt_one_add_le {x : ℝ} (hx : 0 ≤ x) : √(1 + x) ≤ 1 + x / 2 := by
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith [sq_nonneg (x / 2)]

/-- `e₀(n) ≤ e₀(X)` for `n ≥ X ≥ 5` (`e₀ = 2n/((n - 3)(n - 4))` decreases). -/
theorem e0_le {n X : ℝ} (hX : 5 ≤ X) (hn : X ≤ n) : e0 n ≤ e0 X := by
  unfold e0
  rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hn) (by nlinarith : (0 : ℝ) ≤ n * X - 12)]

/-- `e₀(n)/q = 2n²/((n - 3)(n - 4))` decreases for `n ≥ X ≥ 5`. -/
theorem u_le {n X : ℝ} (hX : 5 ≤ X) (hn : X ≤ n) : e0 n / n⁻¹ ≤ e0 X / X⁻¹ := by
  unfold e0
  have hn0 : 0 < n := by linarith
  have hX0 : 0 < X := by linarith
  rw [div_inv_eq_mul, div_inv_eq_mul, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hn) (by nlinarith : (0 : ℝ) ≤ 7 * n * X - 12 * (X + n)),
    mul_pos hn0 hX0]

theorem eQ_cast {X : ℕ} (hX : 5 ≤ X) : ((eQ X : ℚ) : ℝ) = e0 (X : ℝ) := by
  have hX' : (5 : ℝ) ≤ X := by exact_mod_cast hX
  rw [Sarkozy.SignedEstimates.e0_eq_paper hX', eQ, uQ]
  push_cast
  ring

theorem uQ_cast {X : ℕ} (hX : 5 ≤ X) : ((uQ X : ℚ) : ℝ) = e0 (X : ℝ) / (X : ℝ)⁻¹ := by
  have hX' : (5 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (X : ℝ) ≠ 0 := by positivity
  rw [Sarkozy.SignedEstimates.e0_eq_paper hX', uQ]
  push_cast
  field_simp

theorem e0_lt {n : ℝ} (hn : 2 ^ 24 ≤ n) : e0 n ≤ 1 / 1000 := by
  unfold e0
  rw [div_le_iff₀ (by nlinarith)]
  nlinarith

theorem one_div_one_sub_le {a b : ℝ} (hb : b < 1) (hab : a ≤ b) : 1 / (1 - a) ≤ 1 / (1 - b) :=
  one_div_le_one_div_of_le (by linarith) (by linarith)

/-- **The atoms decrease along the primes** (`lem:majorant`): at `p = n ≥ X ≥ 2²⁴` with
`s² ≤ X`, `s ≥ 1`, and `0 ≤ Γ ≤ Γ'`, the atoms at `n` are below the rational atoms at `X`. -/
theorem atomsAt_le {n : ℝ} {X s : ℕ} {Γ : ℝ} {Γ' : ℚ} (hX : 2 ^ 24 ≤ X) (hXn : (X : ℝ) ≤ n)
    (hs : s ^ 2 ≤ X) (hs1 : 1 ≤ s) (hΓ0 : 0 ≤ Γ) (hΓ : Γ ≤ Γ') :
    (atomsAt n Γ).Le (atomsQ X s Γ').cast := by
  have hX' : (2 : ℝ) ^ 24 ≤ X := by exact_mod_cast hX
  have hX5 : (5 : ℕ) ≤ X := le_trans (by norm_num) hX
  have hn : (2 : ℝ) ^ 24 ≤ n := hX'.trans hXn
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (by norm_num) hX'
  have hq : n⁻¹ ≤ (X : ℝ)⁻¹ := inv_anti₀ hX0 hXn
  have hq0 : 0 ≤ n⁻¹ := inv_nonneg.mpr hn0.le
  have hqX : (X : ℝ)⁻¹ ≤ 1 / 2 ^ 24 := by rw [one_div]; exact inv_anti₀ (by norm_num) hX'
  have he := e0_le (by linarith) hXn
  have he0 : 0 ≤ e0 n := Sarkozy.SignedEstimates.e0_nonneg (by linarith)
  have heX : e0 (X : ℝ) ≤ 1 / 1000 := e0_lt hX'
  have hu := u_le (by linarith) hXn
  have hu0 : 0 ≤ e0 n / n⁻¹ := div_nonneg he0 hq0
  have hsX : (s : ℝ) ≤ √n := by
    rw [Real.le_sqrt (by positivity) hn0.le]
    have : ((s ^ 2 : ℕ) : ℝ) ≤ X := by exact_mod_cast hs
    push_cast at this
    linarith
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
  have hr : (√n)⁻¹ ≤ 1 / (s : ℝ) := by rw [one_div]; exact inv_anti₀ hs0 hsX
  have hsq : 1 - e0 n ≤ √(1 - e0 n) := by
    rw [Real.le_sqrt (by linarith) (by linarith)]
    nlinarith
  have hq' : n⁻¹ ≤ 1 / (X : ℝ) := by rw [one_div]; exact hq
  have hqX' : 1 / (X : ℝ) ≤ 1 / 2 ^ 24 := by rw [one_div]; exact hqX
  have h2X : (2 : ℝ) / X = 2 * (1 / X) := by ring
  have h10X : (10 : ℝ) / X = 10 * (1 / X) := by ring
  have h14X : (14 : ℝ) / X = 14 * (1 / X) := by ring
  simp only [Atoms.Le, atomsAt, atomsQ, Atoms.cast]
  push_cast
  rw [eQ_cast hX5, uQ_cast hX5]
  refine ⟨⟨hq0, hq'⟩, ⟨inv_nonneg.mpr (Real.sqrt_nonneg _), hr⟩,
    ⟨he0, he⟩, ⟨hu0, hu⟩, ⟨hΓ0, hΓ⟩, ⟨Real.sqrt_nonneg _, ?_⟩, ⟨Real.sqrt_nonneg _, sqrt3_le⟩,
    ⟨Real.sqrt_nonneg _, sqrtA_le⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · refine (sqrt_one_add_le hq0).trans ?_
    linarith
  · exact div_nonneg zero_le_one (by linarith)
  · exact one_div_one_sub_le (by linarith) (by linarith)
  · exact div_nonneg zero_le_one (by linarith)
  · exact one_div_one_sub_le (by linarith) (by linarith)
  · exact div_nonneg zero_le_one (by linarith)
  · exact one_div_one_sub_le (by linarith) he
  · exact div_nonneg zero_le_one (by linarith)
  · exact one_div_one_sub_le (by linarith) (by linarith)
  · exact div_nonneg zero_le_one (by linarith)
  · exact one_div_one_sub_le (by linarith) (by linarith)
  · exact div_nonneg zero_le_one (Real.sqrt_nonneg _)
  · exact one_div_le_one_div_of_le (by linarith) (by linarith)

theorem gamQ_cast (X s : ℕ) : ((gamQ X s : ℚ) : ℝ) =
    gamPoly (X : ℝ)⁻¹ (s : ℝ)⁻¹ (1 + (X : ℝ)⁻¹ / 2)
      (1 + 2 * (X : ℝ)⁻¹ * ((1 - 4 * (X : ℝ)⁻¹)⁻¹) ^ 2) (1 - (X : ℝ)⁻¹)⁻¹
      (1 - 4 * (X : ℝ)⁻¹)⁻¹ := by
  rw [gamQ, gamPoly_cast]
  unfold j4Q
  push_cast
  congr 1 <;> ring

/-- **`Γ_A` at `p = n ≥ X` is at most the rational majorant `gamQ X s`.** -/
theorem GammaA_le {n : ℝ} {X s : ℕ} (hX : 2 ^ 24 ≤ X) (hXn : (X : ℝ) ≤ n) (hs : s ^ 2 ≤ X)
    (hs1 : 1 ≤ s) : GammaA n⁻¹ (√n)⁻¹ ≤ ((gamQ X s : ℚ) : ℝ) := by
  have hX' : (2 : ℝ) ^ 24 ≤ X := by exact_mod_cast hX
  have hn : (2 : ℝ) ^ 24 ≤ n := hX'.trans hXn
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (by norm_num) hX'
  have hq : n⁻¹ ≤ (X : ℝ)⁻¹ := inv_anti₀ hX0 hXn
  have hq0 : 0 ≤ n⁻¹ := inv_nonneg.mpr hn0.le
  have hqX : (X : ℝ)⁻¹ ≤ 1 / 2 ^ 24 := by rw [one_div]; exact inv_anti₀ (by norm_num) hX'
  have hsX : (s : ℝ) ≤ √n := by
    rw [Real.le_sqrt (by positivity) hn0.le]
    have : ((s ^ 2 : ℕ) : ℝ) ≤ X := by exact_mod_cast hs
    push_cast at this
    linarith
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
  have hr : (√n)⁻¹ ≤ (s : ℝ)⁻¹ := inv_anti₀ hs0 hsX
  have hj4 : (1 - 4 * n⁻¹)⁻¹ ≤ (1 - 4 * (X : ℝ)⁻¹)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  have hj40 : 0 ≤ (1 - 4 * n⁻¹)⁻¹ := inv_nonneg.mpr (by linarith)
  have hx0 : 0 ≤ 4 * n⁻¹ / (1 - 4 * n⁻¹) ^ 2 := by positivity
  have hx : 4 * n⁻¹ / (1 - 4 * n⁻¹) ^ 2 / 2 ≤ 2 * (X : ℝ)⁻¹ * ((1 - 4 * (X : ℝ)⁻¹)⁻¹) ^ 2 := by
    rw [div_eq_mul_inv (4 * n⁻¹), ← inv_pow]
    have : (1 - 4 * n⁻¹)⁻¹ ^ 2 ≤ (1 - 4 * (X : ℝ)⁻¹)⁻¹ ^ 2 := pow_le_pow_left₀ hj40 hj4 2
    have h2 : 0 ≤ (1 - 4 * n⁻¹)⁻¹ ^ 2 := by positivity
    nlinarith [mul_le_mul hq this h2 (by positivity : (0 : ℝ) ≤ (X : ℝ)⁻¹)]
  rw [GammaA_eq, gamQ_cast]
  apply gamPoly_mono hq0 hq (inv_nonneg.mpr (Real.sqrt_nonneg _)) hr (Real.sqrt_nonneg _) ?_
    (Real.sqrt_nonneg _) ?_ (div_nonneg zero_le_one (by linarith)) ?_
    (div_nonneg zero_le_one (by linarith)) (by rw [one_div]; exact hj4)
  · refine (sqrt_one_add_le hq0).trans ?_
    linarith
  · refine (sqrt_one_add_le hx0).trans ?_
    linarith
  · rw [one_div]; exact inv_anti₀ (by linarith) (by linarith)

end Sarkozy.SignedDecomp
