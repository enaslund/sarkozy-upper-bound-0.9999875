module

public import Sarkozy.Spectral.RouteB
public import Sarkozy.Certificates.Majorant
public import Sarkozy.UpperReference.BlockCaps

/-!
# `lem:record:monotone-endpoint`: the Route B root caps from one endpoint

`paper/sections/25_upper_reference.tex`, `lem:record:monotone-endpoint`. The Schur witness
`(s_⋆, g_⋆)` of `eq:record:schur` is checked once, with the frame numbers of
`lem:record:frame-inputs` at an endpoint `r₀ = p₀^{-1/2}`; every frame number and every input
of `lem:record:direct-star-inputs` is, after division by its power of `r`, admissible on
`(0, r₀]`. The lemma says that then (H1)–(H3) of `thm:record:direct-star` hold at every prime
`p ≥ p₀` with the same `s_⋆, g_⋆`, that `g_root(p) ≤ g_root(p₀)` and
`B_top(p) ≤ B_top(p₀) = p₀ ε_ϱ(p₀)²/(1 - g_root(p₀) p₀^{-1/2})`, and that the block root
operator is at least `-d b^{-1/2}` with `d = g_root(p₀) exp(B_top(p₀) L/(X log X))`.

The file proves the lemma in three layers.

* `schur_test_mono`: **(H2) at `p` from (H2) at the endpoint** (the first paragraph of the
  proof, `lem:majorant`(d)): with smaller frame numbers `ε_V, ε_×, ε_𝐁`, the coefficient
  `g_⋆/α_⋆` does not decrease and `β_⋆` does not increase, so the test matrix only grows by a
  nonnegative multiple of `I`. `posDef_R_add`: `𝐑 + β_⋆ I ≻ 0` from `𝐑 ⪰ 0` and `β_⋆ > 0`.
* `endpoint_numbers`: **the numbers** (the second paragraph of the proof). In the normalized
  variables `M_⋆/r`, `z_⋆/r²`, `N_ns/r`, `D_col/r`, `ε_soft/r` (all admissible), `ε_Z`,
  `g_root`, `ε_ϱ/r` are at most their endpoint values, `g_root r < 1` on the box, and
  `B_top ≤ B_top(r₀)`. `nns_admissible` and `soft_admissible` give the admissibility of
  `N_ns/r = ∑_{k=2}^4 C_k r^{k-1}` and of `ε_soft/r` from their formulas; `gRoot_eq` identifies
  the normalized `g_root` with the formula of `thm:record:direct-star`.
* `monotone_endpoint_prime`: **the conclusion at one prime**, composed with
  `Sarkozy.Spectral.direct_star_explicit` (`thm:record:direct-star`, abstract form): if (H1)
  and the decomposition (b) hold at `p` with frame numbers at most the endpoint ones, the
  endpoint tests hold for both signs, and the inputs at `p` give `ε_Z < 1`,
  `g_root(p) ≤ g₀`, `ε_ϱ(p)/r ≤ e₀` with `g₀ r₀ < 1`, then `Op ⪰ -g₀ r`,
  `‖ϱ - 1‖ ≤ e₀ r` and `Op ⪯ (1 + B₀/p)` with `B₀ = e₀²/(1 - g₀ r₀) = p₀ ε_ϱ(p₀)²/(1 - g₀ r₀)`.
  The general form of the lemma (frame at `p₀`, inputs at `X ≥ p₀`) is the same statement
  with `e₀, g₀` taken at `X`: the frame and input comparisons are separate hypotheses.
* `monotone_endpoint`: the two combined on a box: the inputs at a point `x` of the box are
  `r(x)` times the admissible normalized inputs, and the constants are their endpoint values.
* The block statement is `Sarkozy.UpperReference.cut_block_cap` (`BlockCaps.lean`) with
  `g = g_root(p₀)` and `B = B_top(p₀)`; `monotone_endpoint_block` restates it for the root cut.

**What is a hypothesis.** (H1) at `p` (`lem:record:frame-inputs`, with the admissibility of the
frame numbers, `lem:spectral-monotone`(a)), the input bounds (H3) (`lem:record:direct-star-inputs`,
`cor:extraction-leaf`(b), `lem:oct24-collision`(e)) and the decomposition (b) of
`thm:record:direct-star` (`lem:spec:stars`, not formalized) are hypotheses, as in
`direct_star_explicit`. The positivity `ε_𝐁 > 0` (the paper: `ε_𝐁 ≥ ‖𝐇‖_row/(p-1) > 0`) is a
hypothesis. The passage from the complex mode realization of `Op` (class three) to the real cut
operator `cutOp` of `cut_block_cap` is not formalized: `monotone_endpoint_block` takes the
per-prime bounds of the real operator as hypotheses.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace ComplexConjugate Matrix ComplexOrder
open RCLike Sarkozy.Majorant

namespace Sarkozy.UpperReference

open Sarkozy Sarkozy.Spectral

section Schur

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
/-- A positive semidefinite matrix plus a nonnegative multiple of `I` is positive
semidefinite. -/
theorem posSemidef_add_smul_one {M : Matrix n n 𝕜} (hM : M.PosSemidef) {c : ℝ}
    (hc : 0 ≤ c) : (M + ((c : ℝ) : 𝕜) • (1 : Matrix n n 𝕜)).PosSemidef :=
  hM.add (Matrix.PosSemidef.one.smul (RCLike.ofReal_nonneg.mpr hc))

omit [Fintype n] in
/-- **`𝐑 + β_⋆ I ≻ 0`** (`lem:record:monotone-endpoint`, proof): from `𝐑 ⪰ 0` and `β_⋆ > 0`. -/
theorem posDef_R_add {R : Matrix n n 𝕜} (hR : R.PosSemidef) {β : ℝ} (hβ : 0 < β) :
    (R + ((β : ℝ) : 𝕜) • (1 : Matrix n n 𝕜)).PosDef :=
  Matrix.PosDef.posSemidef_add hR (Matrix.PosDef.one.smul (RCLike.ofReal_pos.mpr hβ))

/-- `β_⋆ = ε_𝐖 + ε_𝐄𝐖²/s_⋆` with `ε_𝐖 = ε_𝐁 + 2Λ_D ε_× + Λ_D² ε_V`, `ε_𝐄𝐖 = ε_× + Λ_D ε_V`
(`thm:record:direct-star` (H2)) is nondecreasing in the frame numbers. -/
theorem betaStar_mono {εV εx εB εV₀ εx₀ εB₀ Λ s : ℝ} (hs : 0 < s) (hΛ : 0 ≤ Λ) (hεV : 0 ≤ εV)
    (hεx : 0 ≤ εx) (hV : εV ≤ εV₀) (hx : εx ≤ εx₀) (hB : εB ≤ εB₀) :
    εB + 2 * Λ * εx + Λ ^ 2 * εV + (εx + Λ * εV) ^ 2 / s ≤
      εB₀ + 2 * Λ * εx₀ + Λ ^ 2 * εV₀ + (εx₀ + Λ * εV₀) ^ 2 / s := by
  have h0 : 0 ≤ εx + Λ * εV := add_nonneg hεx (mul_nonneg hΛ hεV)
  have h1 : εx + Λ * εV ≤ εx₀ + Λ * εV₀ := add_le_add hx (mul_le_mul_of_nonneg_left hV hΛ)
  have h2 : (εx + Λ * εV) ^ 2 / s ≤ (εx₀ + Λ * εV₀) ^ 2 / s :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ h0 h1 2) hs.le
  have h3 : 2 * Λ * εx ≤ 2 * Λ * εx₀ := mul_le_mul_of_nonneg_left hx (by positivity)
  have h4 : Λ ^ 2 * εV ≤ Λ ^ 2 * εV₀ := mul_le_mul_of_nonneg_left hV (sq_nonneg Λ)
  linarith

omit [Fintype n] in
/-- **(H2) transfers to smaller frame numbers** (`lem:record:monotone-endpoint`, proof, with
`lem:majorant`(d)). If the Schur test `eq:record:schur`,
`D + (g_⋆/α_⋆) I - (𝐑 + β_⋆ I)/g_⋆ ⪰ 0` (one sign, `D = ±ε_G Δ^E`), holds with the frame numbers
`ε_V⁰, ε_×⁰, ε_𝐁⁰` of the endpoint, it holds with any smaller nonnegative `ε_V, ε_×, ε_𝐁` and
the same `s_⋆, g_⋆`. -/
theorem schur_test_mono (D R : Matrix n n 𝕜) {g εV εx εB εV₀ εx₀ εB₀ Λ s : ℝ} (hg : 0 < g)
    (hs : 0 < s) (hΛ : 0 ≤ Λ) (hεV : 0 ≤ εV) (hεx : 0 ≤ εx) (hV : εV ≤ εV₀) (hx : εx ≤ εx₀)
    (hB : εB ≤ εB₀)
    (h₀ : (D + ((g / (1 + εV₀ + s) : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) - ((1 / g : ℝ) : 𝕜) •
      (R + ((εB₀ + 2 * Λ * εx₀ + Λ ^ 2 * εV₀ + (εx₀ + Λ * εV₀) ^ 2 / s : ℝ) : 𝕜) •
        (1 : Matrix n n 𝕜))).PosSemidef) :
    (D + ((g / (1 + εV + s) : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) - ((1 / g : ℝ) : 𝕜) •
      (R + ((εB + 2 * Λ * εx + Λ ^ 2 * εV + (εx + Λ * εV) ^ 2 / s : ℝ) : 𝕜) •
        (1 : Matrix n n 𝕜))).PosSemidef := by
  set β := εB + 2 * Λ * εx + Λ ^ 2 * εV + (εx + Λ * εV) ^ 2 / s with hβdef
  set β₀ := εB₀ + 2 * Λ * εx₀ + Λ ^ 2 * εV₀ + (εx₀ + Λ * εV₀) ^ 2 / s with hβ₀def
  have hβ : β ≤ β₀ := betaStar_mono hs hΛ hεV hεx hV hx hB
  have hα : g / (1 + εV₀ + s) ≤ g / (1 + εV + s) :=
    div_le_div_of_nonneg_left hg.le (by linarith) (by linarith)
  have hc : 0 ≤ (g / (1 + εV + s) - g / (1 + εV₀ + s)) + (β₀ - β) / g := by
    have := div_nonneg (sub_nonneg.mpr hβ) hg.le
    linarith
  have heq : D + ((g / (1 + εV + s) : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) - ((1 / g : ℝ) : 𝕜) •
      (R + ((β : ℝ) : 𝕜) • (1 : Matrix n n 𝕜)) =
      (D + ((g / (1 + εV₀ + s) : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) - ((1 / g : ℝ) : 𝕜) •
        (R + ((β₀ : ℝ) : 𝕜) • (1 : Matrix n n 𝕜))) +
      ((((g / (1 + εV + s) - g / (1 + εV₀ + s)) + (β₀ - β) / g : ℝ) : ℝ) : 𝕜) •
        (1 : Matrix n n 𝕜) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
        smul_eq_mul, mul_one]
      push_cast
      ring
    · simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hij,
        smul_eq_mul, mul_zero, add_zero]
  rw [heq]
  exact posSemidef_add_smul_one h₀ hc

end Schur

/-! ## The numbers on the box -/

section Numbers

variable {Δ : Type*} [Preorder Δ]

/-- `ε_Z = Z_⋆ + N_ns + D_col` with `Z_⋆ = 2 z_⋆` (`lem:record:direct-star-inputs`(ii)), in the
normalized variables `z_⋆ = r² nz`, `N_ns = r nN`, `D_col = r nD`. -/
def epsZ (r nz nN nD : Δ → ℝ) (x : Δ) : ℝ := 2 * (r x ^ 2 * nz x) + r x * nN x + r x * nD x

/-- `g_root = (g_⋆ + (N_ns + D_col + M_⋆² + z_⋆² + ε_soft)/r)/(1 - ε_Z)`
(`thm:record:direct-star`), in the normalized variables `M_⋆ = r nM`, `ε_soft = r nsoft`. -/
noncomputable def gRoot (g : ℝ) (r nM nz nN nD nsoft : Δ → ℝ) (x : Δ) : ℝ :=
  (g + (nN x + nD x + r x * nM x ^ 2 + r x ^ 3 * nz x ^ 2 + nsoft x)) /
    (1 - epsZ r nz nN nD x)

/-- `ε_ϱ/r = (M_⋆ + N_ns + D_col)/((1 - ε_Z) r)` in the normalized variables. -/
noncomputable def eRho (r nM nz nN nD : Δ → ℝ) (x : Δ) : ℝ :=
  (nM x + nN x + nD x) / (1 - epsZ r nz nN nD x)

/-- `B_top = p ε_ϱ²/(1 - g_root r) = (ε_ϱ/r)²/(1 - g_root r)`. -/
noncomputable def bTop (g : ℝ) (r nM nz nN nD nsoft : Δ → ℝ) (x : Δ) : ℝ :=
  eRho r nM nz nN nD x ^ 2 / (1 - gRoot g r nM nz nN nD nsoft x * r x)

omit [Preorder Δ] in
/-- **The normalized `g_root` is the formula of `thm:record:direct-star`**: with `r > 0`,
`M_⋆ = r nM`, `z_⋆ = r² nz`, `N_ns = r nN`, `D_col = r nD`, `ε_soft = r nsoft`, `Z_⋆ = 2 z_⋆`. -/
theorem gRoot_eq (g : ℝ) (r nM nz nN nD nsoft : Δ → ℝ) (x : Δ) (hr : 0 < r x) :
    gRoot g r nM nz nN nD nsoft x =
      (g + (r x * nN x + r x * nD x + (r x * nM x) ^ 2 + (r x ^ 2 * nz x) ^ 2 +
        r x * nsoft x) / r x) / (1 - (2 * (r x ^ 2 * nz x) + r x * nN x + r x * nD x)) := by
  unfold gRoot epsZ
  congr 2
  field_simp

omit [Preorder Δ] in
/-- **The normalized `ε_ϱ` is the formula of `thm:record:direct-star`**, divided by `r`. -/
theorem eRho_eq (r nM nz nN nD : Δ → ℝ) (x : Δ) (hr : 0 < r x) :
    eRho r nM nz nN nD x = (r x * nM x + r x * nN x + r x * nD x) /
      (1 - (2 * (r x ^ 2 * nz x) + r x * nN x + r x * nD x)) / r x := by
  unfold eRho epsZ
  rw [div_div, mul_comm (1 - _) (r x), ← div_div]
  congr 1
  field_simp

/-- **`lem:record:monotone-endpoint`, the numbers.** On a box with endpoint `xp`, let `r` and
the normalized inputs `M_⋆/r`, `z_⋆/r²`, `N_ns/r`, `D_col/r`, `ε_soft/r` be admissible, and
let `ε_Z(xp) < 1` and `g_root(xp) r(xp) < 1`. Then at every point of the box: `ε_Z < 1`,
`g_root ≤ g_root(xp)`, `ε_ϱ/r ≤ ε_ϱ(xp)/r(xp)`, `g_root r < 1` and `B_top ≤ B_top(xp)`. -/
theorem endpoint_numbers (g : ℝ) (hg : 0 ≤ g) (r nM nz nN nD nsoft : Δ → ℝ)
    (hr : Admissible r) (hM : Admissible nM) (hz : Admissible nz) (hN : Admissible nN)
    (hD : Admissible nD) (hsoft : Admissible nsoft) (xp : Δ) (hxp : ∀ x, x ≤ xp)
    (hZ1 : epsZ r nz nN nD xp < 1) (hgr : gRoot g r nM nz nN nD nsoft xp * r xp < 1) (x : Δ) :
    epsZ r nz nN nD x ≤ epsZ r nz nN nD xp ∧ epsZ r nz nN nD x < 1 ∧
      gRoot g r nM nz nN nD nsoft x ≤ gRoot g r nM nz nN nD nsoft xp ∧
      eRho r nM nz nN nD x ≤ eRho r nM nz nN nD xp ∧
      gRoot g r nM nz nN nD nsoft x * r x < 1 ∧
      bTop g r nM nz nN nD nsoft x ≤ bTop g r nM nz nN nD nsoft xp := by
  have hx := hxp x
  have r0 := hr.2 x
  have r1 := hr.1 hx
  have M0 := hM.2 x
  have M1 := hM.1 hx
  have z0 := hz.2 x
  have z1 := hz.1 hx
  have N0 := hN.2 x
  have N1 := hN.1 hx
  have D0 := hD.2 x
  have D1 := hD.1 hx
  have s0 := hsoft.2 x
  have s1 := hsoft.1 hx
  -- `ε_Z`
  have hZle : epsZ r nz nN nD x ≤ epsZ r nz nN nD xp := by
    unfold epsZ
    have a1 : r x ^ 2 * nz x ≤ r xp ^ 2 * nz xp :=
      mul_le_mul (pow_le_pow_left₀ r0 r1 2) z1 z0 (sq_nonneg _)
    have a2 : r x * nN x ≤ r xp * nN xp := mul_le_mul r1 N1 N0 (r0.trans r1)
    have a3 : r x * nD x ≤ r xp * nD xp := mul_le_mul r1 D1 D0 (r0.trans r1)
    linarith
  have hZ0 : 0 ≤ epsZ r nz nN nD x := by
    unfold epsZ
    have := mul_nonneg (sq_nonneg (r x)) z0
    have := mul_nonneg r0 N0
    have := mul_nonneg r0 D0
    linarith
  have hZx : epsZ r nz nN nD x < 1 := lt_of_le_of_lt hZle hZ1
  have hden : 0 < 1 - epsZ r nz nN nD xp := by linarith
  have hdenle : 1 - epsZ r nz nN nD xp ≤ 1 - epsZ r nz nN nD x := by linarith
  -- numerators
  have hnum : nN x + nD x + r x * nM x ^ 2 + r x ^ 3 * nz x ^ 2 + nsoft x ≤
      nN xp + nD xp + r xp * nM xp ^ 2 + r xp ^ 3 * nz xp ^ 2 + nsoft xp := by
    have a1 : r x * nM x ^ 2 ≤ r xp * nM xp ^ 2 :=
      mul_le_mul r1 (pow_le_pow_left₀ M0 M1 2) (sq_nonneg _) (r0.trans r1)
    have a2 : r x ^ 3 * nz x ^ 2 ≤ r xp ^ 3 * nz xp ^ 2 :=
      mul_le_mul (pow_le_pow_left₀ r0 r1 3) (pow_le_pow_left₀ z0 z1 2) (sq_nonneg _)
        (pow_nonneg (r0.trans r1) 3)
    linarith
  have hnum0 : 0 ≤ g + (nN x + nD x + r x * nM x ^ 2 + r x ^ 3 * nz x ^ 2 + nsoft x) := by
    have := mul_nonneg r0 (sq_nonneg (nM x))
    have := mul_nonneg (pow_nonneg r0 3) (sq_nonneg (nz x))
    linarith
  have hgle : gRoot g r nM nz nN nD nsoft x ≤ gRoot g r nM nz nN nD nsoft xp := by
    unfold gRoot
    exact div_le_div₀ (by linarith) (by linarith) hden hdenle
  have hele : eRho r nM nz nN nD x ≤ eRho r nM nz nN nD xp := by
    unfold eRho
    exact div_le_div₀ (by linarith [hM.2 xp, hN.2 xp, hD.2 xp]) (by linarith) hden hdenle
  have hg0 : 0 ≤ gRoot g r nM nz nN nD nsoft x := by
    unfold gRoot
    exact div_nonneg hnum0 (by linarith)
  have hgrle : gRoot g r nM nz nN nD nsoft x * r x ≤ gRoot g r nM nz nN nD nsoft xp * r xp :=
    mul_le_mul hgle r1 r0 (hg0.trans hgle)
  have hgrx : gRoot g r nM nz nN nD nsoft x * r x < 1 := lt_of_le_of_lt hgrle hgr
  have he0 : 0 ≤ eRho r nM nz nN nD x := by
    unfold eRho
    exact div_nonneg (by linarith) (by linarith)
  have hbt : bTop g r nM nz nN nD nsoft x ≤ bTop g r nM nz nN nD nsoft xp := by
    unfold bTop
    exact div_le_div₀ (sq_nonneg _) (pow_le_pow_left₀ he0 hele 2) (by linarith) (by linarith)
  exact ⟨hZle, hZx, hgle, hele, hgrx, hbt⟩

/-- **`N_ns/r = ∑_{k=2}^4 C_k r^{k-1}` is admissible** (`lem:record:direct-star-inputs`(iii) with
`Q = p₀` fixed, `lem:majorant`(i)): a polynomial in `r` with nonnegative coefficients. -/
theorem nns_admissible (r : Δ → ℝ) (hr : Admissible r) {C₂ C₃ C₄ : ℝ} (h₂ : 0 ≤ C₂)
    (h₃ : 0 ≤ C₃) (h₄ : 0 ≤ C₄) :
    Admissible (fun x => C₂ * r x + C₃ * r x ^ 2 + C₄ * r x ^ 3) := by
  refine ⟨fun x y hxy => ?_, fun x => ?_⟩
  · have r0 := hr.2 x
    have r1 := hr.1 hxy
    have a1 := mul_le_mul_of_nonneg_left r1 h₂
    have a2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ r0 r1 2) h₃
    have a3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ r0 r1 3) h₄
    linarith
  · have r0 := hr.2 x
    positivity

/-- **`ε_soft/r` is admissible** (`lem:record:monotone-endpoint`, proof): with
`ε_soft = 2(1 + ε_V)^{1/2}[r(∑_k ê_k²(𝐇_kk + ε_𝐁))^{1/2} + n r²(∑_k 4^{r_k})^{1/2}]`
(`thm:record:direct-star`), `ε_soft/r = 2(1 + ε_V)^{1/2}[(∑_k ê_k²(𝐇_kk + ε_𝐁))^{1/2} +
n r (∑_k 4^{r_k})^{1/2}]` is admissible when `ε_V`, the `ê_k`, `ε_𝐁` and `r` are and `𝐇_kk ≥ 0`. -/
theorem soft_admissible {K : Type*} [Fintype K] (r εV εB : Δ → ℝ) (e : K → Δ → ℝ)
    (Hkk : K → ℝ) (rk : K → ℕ) (nn : ℝ) (hr : Admissible r) (hεV : Admissible εV)
    (hεB : Admissible εB) (he : ∀ k, Admissible (e k)) (hH : ∀ k, 0 ≤ Hkk k) (hn : 0 ≤ nn) :
    Admissible (fun x => 2 * √(1 + εV x) * (√(∑ k, e k x ^ 2 * (Hkk k + εB x)) +
      nn * r x * √(∑ k, (4 : ℝ) ^ rk k))) := by
  refine ⟨fun x y hxy => ?_, fun x => ?_⟩
  · have hV := hεV.1 hxy
    have hsum : ∑ k, e k x ^ 2 * (Hkk k + εB x) ≤ ∑ k, e k y ^ 2 * (Hkk k + εB y) :=
      Finset.sum_le_sum fun k _ =>
        mul_le_mul (pow_le_pow_left₀ ((he k).2 x) ((he k).1 hxy) 2)
          (by linarith [hεB.1 hxy]) (by linarith [hεB.2 x, hH k]) (sq_nonneg _)
    have h1 : √(1 + εV x) ≤ √(1 + εV y) := Real.sqrt_le_sqrt (by linarith)
    have h2 : √(∑ k, e k x ^ 2 * (Hkk k + εB x)) ≤ √(∑ k, e k y ^ 2 * (Hkk k + εB y)) :=
      Real.sqrt_le_sqrt hsum
    have h3 : nn * r x * √(∑ k, (4 : ℝ) ^ rk k) ≤ nn * r y * √(∑ k, (4 : ℝ) ^ rk k) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hr.1 hxy) hn) (Real.sqrt_nonneg _)
    have h4 : 0 ≤ √(∑ k, e k x ^ 2 * (Hkk k + εB x)) + nn * r x * √(∑ k, (4 : ℝ) ^ rk k) :=
      add_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (mul_nonneg hn (hr.2 x)) (Real.sqrt_nonneg _))
    have h5 := mul_le_mul h1 (add_le_add h2 h3) h4 (Real.sqrt_nonneg _)
    nlinarith
  · have := hr.2 x
    positivity

end Numbers

/-! ## The conclusion at one prime -/

section Prime

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {Ξ : Type*} [Fintype Ξ]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- **`lem:record:monotone-endpoint` at one prime.** Let (H1) of `thm:record:direct-star` hold at
`p` (on every mode, with the frame numbers `ε_V, ε_×, ε_𝐁` of `lem:record:frame-inputs` at `p`),
with frame numbers at most those of the endpoint (`ε_V⁰, ε_×⁰, ε_𝐁⁰`, by admissibility), let the
Schur test `eq:record:schur` hold at the endpoint for both signs with `s_⋆, g_⋆`, let `𝐑 ⪰ 0` and
`ε_𝐁 > 0`, and let the decomposition (b) of `thm:record:direct-star` hold at `p` with the inputs
(H3). If the inputs give `ε_Z < 1`, `g_root(p) ≤ g₀` and `ε_ϱ(p)/r ≤ e₀` (their endpoint values,
`endpoint_numbers`), with `r ≤ r₀` and `g₀ r₀ < 1`, then (H2) holds at `p` with the same
`s_⋆, g_⋆`, and the cut operator satisfies `Op ⪰ -g₀ r`, `‖ϱ - 1‖ ≤ e₀ r` and
`Op ⪯ (1 + B₀ r²) = (1 + B₀/p)` with `B₀ = e₀²/(1 - g₀ r₀) = p₀ ε_ϱ(p₀)²/(1 - g₀ p₀^{-1/2})`
when `e₀ = ε_ϱ(p₀)/r₀`. With `e₀, g₀` taken at a point `X ≥ p₀` this is the general form. -/
theorem monotone_endpoint_prime [DecidableEq Ξ] (T K₀ L Soft Tns Tcoll : H →ₗ[𝕜] H)
    (one hs : H) (hone : ‖one‖ = 1) (E Bn : Ξ → (n → 𝕜) →ₗ[𝕜] H)
    (cE cB : H → Ξ → n → 𝕜) (hcE : ∀ f ξ z, ⟪E ξ z, f⟫ = star z ⬝ᵥ cE f ξ)
    (hcB : ∀ f ξ z, ⟪Bn ξ z, f⟫ = star z ⬝ᵥ cB f ξ)
    (horth : ∀ ξ ξ', ξ ≠ ξ' → ∀ u v u' v', ⟪E ξ u + Bn ξ v, E ξ' u' + Bn ξ' v'⟫ = 0)
    (D : Matrix n n 𝕜) (A : Ξ → Matrix n n 𝕜) (hA : ∀ ξ, A ξ = D ∨ A ξ = -D)
    (Hm R : Matrix n n 𝕜) (hRpsd : R.PosSemidef)
    {εV εx εB εV₀ εx₀ εB₀ Λ s g r : ℝ} (hεV : 0 ≤ εV) (hεx : 0 ≤ εx) (hεB : 0 < εB)
    (hΛ0 : 0 ≤ Λ) (hs0 : 0 < s) (hg : 0 < g) (hr : 0 < r)
    (hΛ : ∀ v, sqn (D *ᵥ v) ≤ Λ ^ 2 * sqn v)
    (hR : ∀ v, qform R v v = qform Hm v v - sqn (D *ᵥ v))
    (h1a : ∀ ξ u w, ‖⟪E ξ u, E ξ w⟫ - star u ⬝ᵥ w‖ ≤ εV * √(sqn u) * √(sqn w))
    (h1b : ∀ ξ u v, ‖⟪E ξ u, Bn ξ v⟫ - star u ⬝ᵥ (A ξ *ᵥ v)‖ ≤ εx * √(sqn u) * √(sqn v))
    (h1c : ∀ ξ v, ‖Bn ξ v‖ ^ 2 ≤ qform Hm v v + εB * sqn v)
    (hV : εV ≤ εV₀) (hx : εx ≤ εx₀) (hB : εB ≤ εB₀)
    (htestp₀ : (D + ((g / (1 + εV₀ + s) : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) - ((1 / g : ℝ) : 𝕜) •
      (R + ((εB₀ + 2 * Λ * εx₀ + Λ ^ 2 * εV₀ + (εx₀ + Λ * εV₀) ^ 2 / s : ℝ) : 𝕜) •
        (1 : Matrix n n 𝕜))).PosSemidef)
    (htestm₀ : (-D + ((g / (1 + εV₀ + s) : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) - ((1 / g : ℝ) : 𝕜) •
      (R + ((εB₀ + 2 * Λ * εx₀ + Λ ^ 2 * εV₀ + (εx₀ + Λ * εV₀) ^ 2 / s : ℝ) : 𝕜) •
        (1 : Matrix n n 𝕜))).PosSemidef)
    (hL : ∀ f, re ⟪f, L f⟫ = r * ∑ ξ, (qform (A ξ) (cE f ξ) (cE f ξ) +
      2 * re (star (cE f ξ) ⬝ᵥ (cB f ξ - (A ξ)ᴴ *ᵥ cE f ξ))))
    {Z₀ εsoft Mstar zstar Zstar Nns Dcol : ℝ}
    (hT : ∀ x, T x = ((Z₀⁻¹ : ℝ) : 𝕜) • K₀ x) (hZ₀ : ⟪one, K₀ one⟫ = (Z₀ : 𝕜))
    (hsym : T.IsSymmetric)
    (hb : ∀ x, K₀ x = ⟪one + hs, x⟫ • (one + hs) + L x +
      (Soft x - ⟪hs, x⟫ • hs + (Tns x - Tcoll x)))
    (hL1 : L one = 0) (hSoft1 : Soft one = 0) (hSoft : ∀ x, ‖Soft x‖ ≤ εsoft * ‖x‖)
    (hns : ∀ x, ‖Tns x‖ ≤ Nns * ‖x‖) (hcoll : ∀ x, ‖Tcoll x‖ ≤ Dcol * ‖x‖)
    (hM : ‖hs - ⟪one, hs⟫ • one‖ ≤ Mstar) (hz : ‖⟪one, hs⟫‖ ≤ zstar)
    (hZs : 2 * ‖⟪one, hs⟫‖ ≤ Zstar) (hεZ : Zstar + Nns + Dcol < 1)
    {g₀ e₀ r₀ : ℝ}
    (hgR : (g + (Nns + Dcol + Mstar ^ 2 + zstar ^ 2 + εsoft) / r) /
      (1 - (Zstar + Nns + Dcol)) ≤ g₀)
    (her : (Mstar + Nns + Dcol) / (1 - (Zstar + Nns + Dcol)) / r ≤ e₀)
    (hrr₀ : r ≤ r₀) (hgr₀ : g₀ * r₀ < 1) :
    ((D + ((g / (1 + εV + s) : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) - ((1 / g : ℝ) : 𝕜) •
        (R + ((εB + 2 * Λ * εx + Λ ^ 2 * εV + (εx + Λ * εV) ^ 2 / s : ℝ) : 𝕜) •
          (1 : Matrix n n 𝕜))).PosSemidef ∧
      (-D + ((g / (1 + εV + s) : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) - ((1 / g : ℝ) : 𝕜) •
        (R + ((εB + 2 * Λ * εx + Λ ^ 2 * εV + (εx + Λ * εV) ^ 2 / s : ℝ) : 𝕜) •
          (1 : Matrix n n 𝕜))).PosSemidef) ∧
    (∀ f, -(g₀ * r) * ‖f‖ ^ 2 ≤ re ⟪f, T f⟫) ∧
    ‖T one - one‖ ≤ e₀ * r ∧
    (∀ F, re ⟪F, T F⟫ ≤ (1 + e₀ ^ 2 / (1 - g₀ * r₀) * r ^ 2) * ‖F‖ ^ 2) := by
  -- (H2) at `p`
  have htp := schur_test_mono D R hg hs0 hΛ0 hεV hεx hV hx hB htestp₀
  have htm := schur_test_mono (-D) R hg hs0 hΛ0 hεV hεx hV hx hB htestm₀
  have hβ : 0 < εB + 2 * Λ * εx + Λ ^ 2 * εV + (εx + Λ * εV) ^ 2 / s := by
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hΛ0) hεx
    have := mul_nonneg (sq_nonneg Λ) hεV
    have := div_nonneg (sq_nonneg (εx + Λ * εV)) hs0.le
    linarith
  have hPd := posDef_R_add hRpsd hβ
  obtain ⟨-, -, hlow, hrho, -, hup⟩ := direct_star_explicit T K₀ L Soft Tns Tcoll one hs hone E Bn
    cE cB hcE hcB horth D A hA Hm R hεV hεx hΛ0 hs0 hg hr.le hΛ hR h1a h1b h1c hPd htp htm hL
    hT hZ₀ hsym hb hL1 hSoft1 hSoft hns hcoll hM hz hZs hεZ
  -- signs of the inputs (`H` contains the unit vector `1`)
  have hNns : 0 ≤ Nns := by
    have := hns one
    rw [hone, mul_one] at this
    exact (norm_nonneg _).trans this
  have hDcol : 0 ≤ Dcol := by
    have := hcoll one
    rw [hone, mul_one] at this
    exact (norm_nonneg _).trans this
  have hsoft0 : 0 ≤ εsoft := by
    have := hSoft one
    rw [hone, mul_one] at this
    exact (norm_nonneg _).trans this
  have hM0 : 0 ≤ Mstar := (norm_nonneg _).trans hM
  have hden : 0 < 1 - (Zstar + Nns + Dcol) := by linarith
  -- the lower bound `-g_root r ≥ -g₀ r`
  have hlowc : (g * r + (εsoft + Mstar ^ 2 + zstar ^ 2 + (Nns + Dcol))) /
      (1 - (Zstar + Nns + Dcol)) ≤ g₀ * r := by
    have e1 : (g * r + (εsoft + Mstar ^ 2 + zstar ^ 2 + (Nns + Dcol))) /
        (1 - (Zstar + Nns + Dcol)) =
        (g + (Nns + Dcol + Mstar ^ 2 + zstar ^ 2 + εsoft) / r) /
          (1 - (Zstar + Nns + Dcol)) * r := by
      field_simp
      ring
    rw [e1]
    exact mul_le_mul_of_nonneg_right hgR hr.le
  -- the compression bound `β ≤ g_root r ≤ g₀ r₀ < 1`
  have hβc : (g * r + (εsoft + (Nns + Dcol))) / (1 - (Zstar + Nns + Dcol)) ≤ g₀ * r := by
    refine le_trans ?_ hlowc
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg Mstar, sq_nonneg zstar]) hden.le
  have hg₀0 : 0 ≤ g₀ := by
    have h1 : 0 ≤ (g * r + (εsoft + (Nns + Dcol))) / (1 - (Zstar + Nns + Dcol)) :=
      div_nonneg (by nlinarith) hden.le
    have h2 := h1.trans hβc
    exact nonneg_of_mul_nonneg_left h2 hr
  have hgr : g₀ * r ≤ g₀ * r₀ := mul_le_mul_of_nonneg_left hrr₀ hg₀0
  have hβ1 : (g * r + (εsoft + (Nns + Dcol))) / (1 - (Zstar + Nns + Dcol)) < 1 :=
    lt_of_le_of_lt (hβc.trans hgr) hgr₀
  -- `ε_ϱ ≤ e₀ r`
  have hρ : (Mstar + (Nns + Dcol)) / (1 - (Zstar + Nns + Dcol)) ≤ e₀ * r := by
    have e1 : (Mstar + (Nns + Dcol)) / (1 - (Zstar + Nns + Dcol)) =
        (Mstar + Nns + Dcol) / (1 - (Zstar + Nns + Dcol)) / r * r := by
      field_simp
      ring
    rw [e1]
    exact mul_le_mul_of_nonneg_right her hr.le
  have hρ0 : 0 ≤ (Mstar + (Nns + Dcol)) / (1 - (Zstar + Nns + Dcol)) :=
    div_nonneg (by linarith) hden.le
  refine ⟨⟨htp, htm⟩, fun f => ?_, hrho.trans hρ, fun F => ?_⟩
  · exact le_trans (mul_le_mul_of_nonneg_right (neg_le_neg hlowc) (sq_nonneg ‖f‖)) (hlow f)
  · have h := hup hβ1 F
    have hF := sq_nonneg ‖F‖
    have hd1 : 0 < 1 - g₀ * r₀ := by linarith
    have hcmp : ((Mstar + (Nns + Dcol)) / (1 - (Zstar + Nns + Dcol))) ^ 2 /
        (1 - (g * r + (εsoft + (Nns + Dcol))) / (1 - (Zstar + Nns + Dcol))) ≤
        e₀ ^ 2 / (1 - g₀ * r₀) * r ^ 2 := by
      have hsq : ((Mstar + (Nns + Dcol)) / (1 - (Zstar + Nns + Dcol))) ^ 2 ≤ (e₀ * r) ^ 2 :=
        pow_le_pow_left₀ hρ0 hρ 2
      calc ((Mstar + (Nns + Dcol)) / (1 - (Zstar + Nns + Dcol))) ^ 2 /
            (1 - (g * r + (εsoft + (Nns + Dcol))) / (1 - (Zstar + Nns + Dcol))) ≤
            (e₀ * r) ^ 2 / (1 - g₀ * r₀) :=
            div_le_div₀ (sq_nonneg _) hsq hd1 (by linarith [hβc.trans hgr])
        _ = e₀ ^ 2 / (1 - g₀ * r₀) * r ^ 2 := by ring
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith [hcmp]) hF)

/-- **`lem:record:monotone-endpoint`** (one prime of the box, normalized inputs). On a box with
endpoint `xp` (in the application `r ∈ (0, r₀]`), let `r` and the normalized inputs `nM = M_⋆/r`,
`nz = z_⋆/r²`, `nN = N_ns/r`, `nD = D_col/r`, `nsoft = ε_soft/r` be admissible, with
`ε_Z(xp) < 1` and `g_root(xp) r(xp) < 1`. At a point `x` (the prime `p` with `r(x) = p^{-1/2}`)
let (H1) and (b) of `thm:record:direct-star` hold with frame numbers at most those of the
endpoint and inputs `M_⋆ = r nM`, `z_⋆ = r² nz`, `Z_⋆ = 2 z_⋆`, `N_ns = r nN`, `D_col = r nD`,
`ε_soft = r nsoft`, and let the endpoint Schur tests hold for both signs. Then (H2) and (H3)
hold at `p` with the same `s_⋆, g_⋆` and `Op ⪰ -g_root(p₀) r`, `‖ϱ - 1‖ ≤ ε_ϱ(p₀)/r₀ · r`,
`Op ⪯ 1 + B_top(p₀)/p`. -/
theorem monotone_endpoint {Δ : Type*} [Preorder Δ] [DecidableEq Ξ]
    (rr nM nz nN nD nsoft : Δ → ℝ) (hrA : Admissible rr) (hMA : Admissible nM)
    (hzA : Admissible nz) (hNA : Admissible nN) (hDA : Admissible nD)
    (hsoftA : Admissible nsoft) (xp : Δ) (hxp : ∀ x, x ≤ xp) (x : Δ) (hrx : 0 < rr x)
    (T K₀ L Soft Tns Tcoll : H →ₗ[𝕜] H)
    (one hs : H) (hone : ‖one‖ = 1) (E Bn : Ξ → (n → 𝕜) →ₗ[𝕜] H)
    (cE cB : H → Ξ → n → 𝕜) (hcE : ∀ f ξ z, ⟪E ξ z, f⟫ = star z ⬝ᵥ cE f ξ)
    (hcB : ∀ f ξ z, ⟪Bn ξ z, f⟫ = star z ⬝ᵥ cB f ξ)
    (horth : ∀ ξ ξ', ξ ≠ ξ' → ∀ u v u' v', ⟪E ξ u + Bn ξ v, E ξ' u' + Bn ξ' v'⟫ = 0)
    (D : Matrix n n 𝕜) (A : Ξ → Matrix n n 𝕜) (hA : ∀ ξ, A ξ = D ∨ A ξ = -D)
    (Hm R : Matrix n n 𝕜) (hRpsd : R.PosSemidef)
    {εV εx εB εV₀ εx₀ εB₀ Λ s g : ℝ} (hεV : 0 ≤ εV) (hεx : 0 ≤ εx) (hεB : 0 < εB)
    (hΛ0 : 0 ≤ Λ) (hs0 : 0 < s) (hg : 0 < g)
    (hΛ : ∀ v, sqn (D *ᵥ v) ≤ Λ ^ 2 * sqn v)
    (hR : ∀ v, qform R v v = qform Hm v v - sqn (D *ᵥ v))
    (h1a : ∀ ξ u w, ‖⟪E ξ u, E ξ w⟫ - star u ⬝ᵥ w‖ ≤ εV * √(sqn u) * √(sqn w))
    (h1b : ∀ ξ u v, ‖⟪E ξ u, Bn ξ v⟫ - star u ⬝ᵥ (A ξ *ᵥ v)‖ ≤ εx * √(sqn u) * √(sqn v))
    (h1c : ∀ ξ v, ‖Bn ξ v‖ ^ 2 ≤ qform Hm v v + εB * sqn v)
    (hV : εV ≤ εV₀) (hx : εx ≤ εx₀) (hB : εB ≤ εB₀)
    (htestp₀ : (D + ((g / (1 + εV₀ + s) : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) - ((1 / g : ℝ) : 𝕜) •
      (R + ((εB₀ + 2 * Λ * εx₀ + Λ ^ 2 * εV₀ + (εx₀ + Λ * εV₀) ^ 2 / s : ℝ) : 𝕜) •
        (1 : Matrix n n 𝕜))).PosSemidef)
    (htestm₀ : (-D + ((g / (1 + εV₀ + s) : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) - ((1 / g : ℝ) : 𝕜) •
      (R + ((εB₀ + 2 * Λ * εx₀ + Λ ^ 2 * εV₀ + (εx₀ + Λ * εV₀) ^ 2 / s : ℝ) : 𝕜) •
        (1 : Matrix n n 𝕜))).PosSemidef)
    (hL : ∀ f, re ⟪f, L f⟫ = rr x * ∑ ξ, (qform (A ξ) (cE f ξ) (cE f ξ) +
      2 * re (star (cE f ξ) ⬝ᵥ (cB f ξ - (A ξ)ᴴ *ᵥ cE f ξ))))
    {Z₀ : ℝ}
    (hT : ∀ y, T y = ((Z₀⁻¹ : ℝ) : 𝕜) • K₀ y) (hZ₀ : ⟪one, K₀ one⟫ = (Z₀ : 𝕜))
    (hsym : T.IsSymmetric)
    (hb : ∀ y, K₀ y = ⟪one + hs, y⟫ • (one + hs) + L y +
      (Soft y - ⟪hs, y⟫ • hs + (Tns y - Tcoll y)))
    (hL1 : L one = 0) (hSoft1 : Soft one = 0)
    (hSoft : ∀ y, ‖Soft y‖ ≤ rr x * nsoft x * ‖y‖)
    (hns : ∀ y, ‖Tns y‖ ≤ rr x * nN x * ‖y‖) (hcoll : ∀ y, ‖Tcoll y‖ ≤ rr x * nD x * ‖y‖)
    (hM : ‖hs - ⟪one, hs⟫ • one‖ ≤ rr x * nM x) (hz : ‖⟪one, hs⟫‖ ≤ rr x ^ 2 * nz x)
    (hZ1 : epsZ rr nz nN nD xp < 1)
    (hgr : gRoot g rr nM nz nN nD nsoft xp * rr xp < 1) :
    (∀ f, -(gRoot g rr nM nz nN nD nsoft xp * rr x) * ‖f‖ ^ 2 ≤ re ⟪f, T f⟫) ∧
    ‖T one - one‖ ≤ eRho rr nM nz nN nD xp * rr x ∧
    (∀ F, re ⟪F, T F⟫ ≤
      (1 + bTop g rr nM nz nN nD nsoft xp * rr x ^ 2) * ‖F‖ ^ 2) := by
  obtain ⟨-, hZx, hgle, hele, -, -⟩ :=
    endpoint_numbers g hg.le rr nM nz nN nD nsoft hrA hMA hzA hNA hDA hsoftA xp hxp hZ1 hgr x
  have hεZ : 2 * (rr x ^ 2 * nz x) + rr x * nN x + rr x * nD x < 1 := hZx
  have hgR := gRoot_eq g rr nM nz nN nD nsoft x hrx
  have heR := eRho_eq rr nM nz nN nD x hrx
  obtain ⟨-, hlow, hrho, hup⟩ := monotone_endpoint_prime T K₀ L Soft Tns Tcoll one hs hone E Bn
    cE cB hcE hcB horth D A hA Hm R hRpsd hεV hεx hεB hΛ0 hs0 hg hrx hΛ hR h1a h1b h1c hV hx hB
    htestp₀ htestm₀ hL (Zstar := 2 * (rr x ^ 2 * nz x)) hT hZ₀ hsym hb hL1 hSoft1 hSoft hns hcoll
    hM hz (by linarith [hz]) hεZ (g₀ := gRoot g rr nM nz nN nD nsoft xp)
    (e₀ := eRho rr nM nz nN nD xp) (r₀ := rr xp)
    (by rw [← hgR]; exact hgle) (by rw [← heR]; exact hele) (hrA.1 (hxp x)) hgr
  refine ⟨hlow, hrho, fun F => ?_⟩
  have h := hup F
  unfold bTop
  exact h

end Prime

/-! ## The block -/

/-- **`lem:record:monotone-endpoint`, the block.** For a root cut `D` (LL20 or LL22) and a block
of primes `p_i ≥ b ≥ X > 1` (`p_i ≡ 3 mod 4`, `b` the least prime) with `log q_𝔅 ≤ L`
(`L = L_u`, or `L'` in the general form), if at every `p_i` the cut operator satisfies
`-g₀ p_i^{-1/2} ⪯ Op ⪯ 1 + B₀/p_i` (the conclusion of `monotone_endpoint`, with
`g₀ = g_root(p₀)` and `B₀ = B_top(p₀)`) and `g₀ p₀^{-1/2} < 1` with `p₀ ≤ X`, then the normalized
block root operator is at least `-d b^{-1/2}`, `d = g₀ exp(B₀ L/(X log X))`. -/
theorem monotone_endpoint_block {U : Type*} [Fintype U] [DecidableEq U]
    (D : Sarkozy.Cuts.SpecData U) {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℕ)
    [∀ i, Fact (p i).Prime] (hne : ∀ i, (Labellings.injLabellings (ZMod (p i)) D.G).Nonempty)
    {g₀ B₀ p₀ X L b : ℝ} (hg : 0 ≤ g₀) (hB : 0 ≤ B₀) (hp₀ : 0 < p₀) (hp₀X : p₀ ≤ X) (hX : 1 < X)
    (hXb : X ≤ b) (hbp : ∀ i, b ≤ p i) (hL : ∑ i, Real.log (p i) ≤ L)
    (hgr₀ : g₀ * (√p₀)⁻¹ < 1)
    (hlow : ∀ i v, -(g₀ * (√(p i : ℝ))⁻¹) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp D (hne i) v⟫_ℝ)
    (hup : ∀ i v, ⟪v, Spectral.cutOp D (hne i) v⟫_ℝ ≤ (1 + B₀ / p i) * ‖v‖ ^ 2)
    (Fn : (∀ i, D.cut.Half → ZMod (p i)) → ℝ) :
    -(g₀ * Real.exp (B₀ * L / (X * Real.log X)) * (√b)⁻¹) *
        Recentering.nrm (FiniteLaw.pi fun i => D.halfLaw (hne i)) Fn ^ 2 ≤
      Sarkozy.Cuts.kernelForm (FiniteLaw.pi fun i => D.halfLaw (hne i))
        (FiniteLaw.pi fun i => D.halfLaw (hne i))
        (fun x y => ∏ i, D.cutK (x i) (y i) / D.cutZ (hne i)) Fn Fn := by
  refine cut_block_cap D p hne hg hB hX hXb hbp hL (fun i => ?_) hlow hup Fn
  have hpi : p₀ ≤ (p i : ℝ) := hp₀X.trans (hXb.trans (hbp i))
  have hs : (√(p i : ℝ))⁻¹ ≤ (√p₀)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.mpr hp₀) (Real.sqrt_le_sqrt hpi)
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hs hg) hgr₀

end Sarkozy.UpperReference
