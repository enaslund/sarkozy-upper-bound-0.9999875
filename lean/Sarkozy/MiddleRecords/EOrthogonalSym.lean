module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Sarkozy.MiddleRecords.MatchingCoefficients

/-!
# The symmetric part of the matching change (`lem:record:e-orthogonal`(c))

`paper/sections/21_middle_records.tex`, `lem:record:e-orthogonal`(c):
`‖Sym(K₁ - K^E₀)‖ ≤ s^E_p = 𝔰_p + 2e_E/(1 - 2q) + q²/((1 - q)(1 - 2q)) + 18q²/((1 - q)(1 - 9q))`.

**The operator step** (`proj_sym_step`, abstract, in any real inner product space): let `H` be an
orthogonal projection (`OrthProj`), `S = H S H` with `‖S‖ ≤ 𝔰`, and `X` symmetric with `‖X‖/z ≤ 𝔰`
and `‖X H‖ ≤ e`, `z > 0`. Then `‖S + X/z‖ ≤ 𝔰 + 2e/z`. The proof is the paper's:
`X = (I - H) X (I - H) + H X + (I - H) X H`, the operators `S` and `(I - H) X (I - H)/z` act on
orthogonal subspaces (so their sum has norm at most `𝔰`), `‖H X‖ = ‖X H‖ ≤ e` (as `X` is
symmetric) and `‖(I - H) X H‖ ≤ e`.

**The assembly** (`e_orthogonal_c`): with the decomposition of `lem:record:e-law`(c), (d) as
hypotheses — `Sym(K₁ - K^E₀) = S + (X + Y)/z₁ - Z/z₀` on `L²(ν_E)` (the compression by `Π_⊥` is
the identity on `Sym(K₁ - K^E₀)`, by (c)), `‖S‖ ≤ 𝔰_p`, `‖X‖/z₁ ≤ q/((1 - q)(1 - 2q))`,
`‖Y‖/z₁ ≤ q²/((1 - q)(1 - 2q))`, `‖Z‖ ≤ 18q²/(1 - q)`, `z₀ ≥ 1 - 9q`, `z₁ ≥ 1 - 2q` — and
`‖X H‖ ≤ e_E` (part (b), `Sarkozy.MiddleRecords.CD_V_bound`), together with
`q/((1 - q)(1 - 2q)) ≤ 𝔰_p` (`frak_s_ge`, the paper's `(1 + √2)/(1 - 9q) ≥ 1/(1 - 2q)`), the
bound `‖Sym(K₁ - K^E₀)‖ ≤ s^E_p` follows. The constants `𝔰_p`, `e_E`, `s^E_p` are the fork's
`frakS`, `eE`, `sEp` of `Sarkozy.MiddleRecords.MatchingCoefficients`. The operators are linear maps
on an abstract real inner
product space standing for `L²(ν_E)`; their identification with the kernels of
`lem:record:e-law` is not formalized.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Sarkozy.MiddleRecords

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An orthogonal projection, as an idempotent symmetric linear map. -/
structure OrthProj (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- The projection. -/
  H : E →ₗ[ℝ] E
  idem : ∀ x, H (H x) = H x
  symm : ∀ x y, ⟪H x, y⟫_ℝ = ⟪x, H y⟫_ℝ

namespace OrthProj

variable (P : OrthProj E)

theorem inner_H_sub (x y : E) : ⟪P.H x, y - P.H y⟫_ℝ = 0 := by
  rw [inner_sub_right, P.symm x y, P.symm x (P.H y), P.idem, sub_self]

theorem norm_sq_split (x : E) : ‖x‖ ^ 2 = ‖P.H x‖ ^ 2 + ‖x - P.H x‖ ^ 2 := by
  have h : x = P.H x + (x - P.H x) := by abel
  conv_lhs => rw [h]
  rw [norm_add_sq_real, P.inner_H_sub x x]
  ring

theorem norm_H_le (x : E) : ‖P.H x‖ ≤ ‖x‖ := by
  have h := P.norm_sq_split x
  have : ‖P.H x‖ ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x - P.H x‖]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this

theorem norm_sub_H_le (x : E) : ‖x - P.H x‖ ≤ ‖x‖ := by
  have h := P.norm_sq_split x
  have : ‖x - P.H x‖ ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖P.H x‖]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this

end OrthProj

/-- **The operator step of `lem:record:e-orthogonal`(c)**: `‖S + X/z‖ ≤ 𝔰 + 2e/z` for `S = H S H`,
`‖S‖ ≤ 𝔰`, `X` symmetric, `‖X‖ ≤ z 𝔰`, `‖X H‖ ≤ e`. -/
theorem proj_sym_step (P : OrthProj E) (S X : E →ₗ[ℝ] E) {s e z : ℝ} (hz : 0 < z)
    (hS : ∀ x, S x = P.H (S (P.H x))) (hX : ∀ x y, ⟪X x, y⟫_ℝ = ⟪x, X y⟫_ℝ)
    (hSn : ∀ x, ‖S x‖ ≤ s * ‖x‖) (hXn : ∀ x, ‖X x‖ ≤ z * s * ‖x‖)
    (hXH : ∀ x, ‖X (P.H x)‖ ≤ e * ‖x‖) (x : E) :
    ‖S x + z⁻¹ • X x‖ ≤ (s + 2 * e / z) * ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hs : 0 ≤ s := by
    have h1 := hSn x
    have h2 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    nlinarith [norm_nonneg (S x)]
  set x₁ := P.H x with hx₁
  set x₂ := x - P.H x with hx₂
  have hHx₂ : P.H x₂ = 0 := by rw [hx₂, map_sub, P.idem, sub_self]
  have hSx : S x = P.H (S x₁) := by
    rw [hS x, hx₁, hS (P.H x), P.idem, P.idem]
  have hSx₁ : ‖S x‖ ≤ s * ‖x₁‖ := by
    have h1 : S x = S x₁ := by rw [hS x₁, P.idem, ← hS x]
    rw [h1]; exact hSn x₁
  -- `X x = (I - H) X x₂ + H X x + (I - H) X x₁`
  have hdec : S x + z⁻¹ • X x = (S x + z⁻¹ • (X x₂ - P.H (X x₂))) + z⁻¹ • P.H (X x) +
      z⁻¹ • (X x₁ - P.H (X x₁)) := by
    have hx : x = x₁ + x₂ := by rw [hx₁, hx₂]; abel
    have : X x = X x₁ + X x₂ := by rw [← map_add, ← hx]
    rw [this, map_add]
    module
  -- the first part: orthogonal pieces
  have hA : ‖S x + z⁻¹ • (X x₂ - P.H (X x₂))‖ ≤ s * ‖x‖ := by
    have horth : ⟪S x, z⁻¹ • (X x₂ - P.H (X x₂))⟫_ℝ = 0 := by
      rw [hSx, inner_smul_right, P.inner_H_sub, mul_zero]
    have hsq : ‖S x + z⁻¹ • (X x₂ - P.H (X x₂))‖ ^ 2 =
        ‖S x‖ ^ 2 + ‖z⁻¹ • (X x₂ - P.H (X x₂))‖ ^ 2 := by
      rw [norm_add_sq_real, horth]; ring
    have hb : ‖z⁻¹ • (X x₂ - P.H (X x₂))‖ ≤ s * ‖x₂‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hz)]
      have h1 := P.norm_sub_H_le (X x₂)
      have h2 := hXn x₂
      calc z⁻¹ * ‖X x₂ - P.H (X x₂)‖ ≤ z⁻¹ * (z * s * ‖x₂‖) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) (inv_nonneg.mpr hz.le)
        _ = s * ‖x₂‖ := by field_simp
    have hsplit := P.norm_sq_split x
    rw [← hx₁, ← hx₂] at hsplit
    have h1 : ‖S x‖ ^ 2 ≤ (s * ‖x₁‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hSx₁ 2
    have h2 : ‖z⁻¹ • (X x₂ - P.H (X x₂))‖ ^ 2 ≤ (s * ‖x₂‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    have : ‖S x + z⁻¹ • (X x₂ - P.H (X x₂))‖ ^ 2 ≤ (s * ‖x‖) ^ 2 := by
      rw [hsq, mul_pow, hsplit]; nlinarith
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hs (norm_nonneg _))).mp this
  -- `‖H X x‖ ≤ e ‖x‖`, by the symmetry of `X`
  have hB : ‖P.H (X x)‖ ≤ e * ‖x‖ := by
    have hsq : ‖P.H (X x)‖ ^ 2 = ⟪x, X (P.H (P.H (X x)))⟫_ℝ := by
      rw [← real_inner_self_eq_norm_sq, P.symm (X x) (P.H (X x)), hX x (P.H (P.H (X x)))]
    have hcs := real_inner_le_norm x (X (P.H (P.H (X x))))
    have he := hXH (P.H (X x))
    rw [← hsq] at hcs
    have h0 : 0 ≤ ‖P.H (X x)‖ := norm_nonneg _
    by_cases hz0 : ‖P.H (X x)‖ = 0
    · rw [hz0]
      exact (norm_nonneg _).trans (hXH x)
    · have hpos : 0 < ‖P.H (X x)‖ := lt_of_le_of_ne h0 (Ne.symm hz0)
      have : ‖P.H (X x)‖ ^ 2 ≤ ‖x‖ * (e * ‖P.H (X x)‖) :=
        hcs.trans (mul_le_mul_of_nonneg_left he (norm_nonneg _))
      nlinarith
  -- `‖(I - H) X x₁‖ ≤ e ‖x‖`
  have hC : ‖X x₁ - P.H (X x₁)‖ ≤ e * ‖x‖ :=
    (P.norm_sub_H_le _).trans (hXH x)
  rw [hdec]
  calc ‖(S x + z⁻¹ • (X x₂ - P.H (X x₂))) + z⁻¹ • P.H (X x) + z⁻¹ • (X x₁ - P.H (X x₁))‖
      ≤ ‖S x + z⁻¹ • (X x₂ - P.H (X x₂))‖ + ‖z⁻¹ • P.H (X x)‖ +
          ‖z⁻¹ • (X x₁ - P.H (X x₁))‖ := norm_add₃_le
    _ ≤ s * ‖x‖ + z⁻¹ * (e * ‖x‖) + z⁻¹ * (e * ‖x‖) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hz)]
        have hzi : 0 ≤ z⁻¹ := inv_nonneg.mpr hz.le
        gcongr
    _ = (s + 2 * e / z) * ‖x‖ := by field_simp; ring

/-- `q/((1 - q)(1 - 2q)) ≤ 𝔰_p` for `0 ≤ q ≤ 1/100` (the paper's
`(1 + √2)/(1 - 9q) ≥ 1/(1 - 2q)`). -/
theorem frak_s_ge {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 100) :
    q / ((1 - q) * (1 - 2 * q)) ≤ frakS q := by
  unfold frakS Zq
  have h1 : 0 < 1 - q := by linarith
  have h2 : 0 < 1 - 2 * q := by linarith
  have h9 : 0 < 1 - 9 * q := by linarith
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hA : 1 / (1 - 2 * q) ≤ (1 + Real.sqrt 2) / (1 - 9 * q) := by
    rw [div_le_div_iff₀ h2 h9]
    nlinarith
  have hB : 0 ≤ 7 * q / ((1 - q) * (1 - 2 * q) * (1 - 9 * q) * (1 - 2 * q)) := by positivity
  have hq1 : 0 ≤ q / (1 - q) := by positivity
  calc q / ((1 - q) * (1 - 2 * q)) = q / (1 - q) * (1 / (1 - 2 * q)) := by
        field_simp
    _ ≤ q / (1 - q) * ((1 + Real.sqrt 2) / (1 - 9 * q)) := mul_le_mul_of_nonneg_left hA hq1
    _ ≤ q / (1 - q) * ((1 + Real.sqrt 2) / (1 - 9 * q) +
          7 * q / ((1 - q) * (1 - 2 * q) * (1 - 9 * q) * (1 - 2 * q))) := by
        apply mul_le_mul_of_nonneg_left _ hq1
        linarith

/-- **`lem:record:e-orthogonal`(c)**: given the decomposition and the bounds of
`lem:record:e-law`(c), (d) (hypotheses) and the bound `‖X H‖ ≤ e_E` of part (b), the symmetric
part `T = Sym(K₁ - K^E₀)` has `‖T‖ ≤ s^E_p`, for `0 < q ≤ 1/100`, `r ≥ 0`. -/
theorem e_orthogonal_c (P : OrthProj E) (T S X Y Z : E →ₗ[ℝ] E) {q r z₀ z₁ : ℝ}
    (hq : 0 < q) (hq' : q ≤ 1 / 100) (hr : 0 ≤ r) (hz₀ : 1 - 9 * q ≤ z₀) (hz₁ : 1 - 2 * q ≤ z₁)
    -- `lem:record:e-law`(c), (d): the decomposition and the norm bounds
    (hT : ∀ x, T x = S x + z₁⁻¹ • (X x + Y x) - z₀⁻¹ • Z x)
    (hS : ∀ x, S x = P.H (S (P.H x))) (hSn : ∀ x, ‖S x‖ ≤ frakS q * ‖x‖)
    (hXs : ∀ x y, ⟪X x, y⟫_ℝ = ⟪x, X y⟫_ℝ)
    (hXn : ∀ x, ‖X x‖ ≤ z₁ * (q / ((1 - q) * (1 - 2 * q))) * ‖x‖)
    (hYn : ∀ x, ‖Y x‖ ≤ z₁ * (q ^ 2 / ((1 - q) * (1 - 2 * q))) * ‖x‖)
    (hZn : ∀ x, ‖Z x‖ ≤ 18 * q ^ 2 / (1 - q) * ‖x‖)
    -- `lem:record:e-orthogonal`(b)
    (hXH : ∀ x, ‖X (P.H x)‖ ≤ eE q r * ‖x‖) (x : E) :
    ‖T x‖ ≤ sEp q r * ‖x‖ := by
  have h1 : 0 < 1 - q := by linarith
  have h2 : 0 < 1 - 2 * q := by linarith
  have h9 : 0 < 1 - 9 * q := by linarith
  have hz₁0 : 0 < z₁ := by linarith
  have hz₀0 : 0 < z₀ := by linarith
  have hfs := frak_s_ge hq.le hq'
  have hX' : ∀ x, ‖X x‖ ≤ z₁ * frakS q * ‖x‖ := by
    intro x
    refine (hXn x).trans ?_
    have := mul_le_mul_of_nonneg_left hfs hz₁0.le
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have hstep := proj_sym_step P S X hz₁0 hS hXs hSn hX' hXH x
  have heE : 0 ≤ eE q r := by unfold eE; positivity
  have hT' : T x = (S x + z₁⁻¹ • X x) + z₁⁻¹ • Y x - z₀⁻¹ • Z x := by
    rw [hT x, smul_add]; abel
  rw [hT']
  have hY : ‖z₁⁻¹ • Y x‖ ≤ q ^ 2 / ((1 - q) * (1 - 2 * q)) * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hz₁0)]
    calc z₁⁻¹ * ‖Y x‖ ≤ z₁⁻¹ * (z₁ * (q ^ 2 / ((1 - q) * (1 - 2 * q))) * ‖x‖) :=
          mul_le_mul_of_nonneg_left (hYn x) (inv_nonneg.mpr hz₁0.le)
      _ = q ^ 2 / ((1 - q) * (1 - 2 * q)) * ‖x‖ := by field_simp
  have hZ : ‖z₀⁻¹ • Z x‖ ≤ 18 * q ^ 2 / ((1 - q) * (1 - 9 * q)) * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hz₀0)]
    have hz0i : z₀⁻¹ ≤ (1 - 9 * q)⁻¹ := inv_anti₀ h9 hz₀
    calc z₀⁻¹ * ‖Z x‖ ≤ (1 - 9 * q)⁻¹ * (18 * q ^ 2 / (1 - q) * ‖x‖) :=
          mul_le_mul hz0i (hZn x) (norm_nonneg _) (inv_nonneg.mpr h9.le)
      _ = 18 * q ^ 2 / ((1 - q) * (1 - 9 * q)) * ‖x‖ := by field_simp
  have he : 2 * eE q r / z₁ ≤ 2 * eE q r / (1 - 2 * q) :=
    div_le_div_of_nonneg_left (by positivity) h2 hz₁
  calc ‖(S x + z₁⁻¹ • X x) + z₁⁻¹ • Y x - z₀⁻¹ • Z x‖
      ≤ ‖S x + z₁⁻¹ • X x‖ + ‖z₁⁻¹ • Y x‖ + ‖z₀⁻¹ • Z x‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ (frakS q + 2 * eE q r / z₁) * ‖x‖ + q ^ 2 / ((1 - q) * (1 - 2 * q)) * ‖x‖ +
          18 * q ^ 2 / ((1 - q) * (1 - 9 * q)) * ‖x‖ := by gcongr
    _ ≤ sEp q r * ‖x‖ := by
        unfold sEp
        have hx : 0 ≤ ‖x‖ := norm_nonneg _
        nlinarith [mul_le_mul_of_nonneg_right he hx]

end Sarkozy.MiddleRecords
