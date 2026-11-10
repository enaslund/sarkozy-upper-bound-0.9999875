module

public import Sarkozy.Spectral.RouteA

/-!
# `prop:spec2:mucentre` (c3), (c4): the perpendicular inputs from the expansion

`prop:spec2:mucentre` (`paper/sections/14_spectral.tex`), parts (c3) and (c4), in abstract form.
The cut operator is `Op = K₀/Z₀` with the character expansion of `lem:spec:expansion`,
`K₀ = 1 ⊗ 1 + T_star + T_ns - T_coll` (`eq:record:root-kernel`), where the star part `T_star`
vanishes between functions of `H_⊥ = (ℂ1 ⊕ V)^⊥` (`prop:spec2:mucentre` (a), from
`lem:spec:stars`), and `P₀ T_star 1 = h_⋆ - E_μ h_⋆` (`lem:spec:stars` (c)). With
`‖T_ns‖ ≤ N_ns`, `‖T_coll‖ ≤ D_col`, `‖h_⋆ - E_μ h_⋆‖ ≤ M_⋆` and `Z₀ ≥ 1 - ε_Z > 0`:
* (c3) `‖ϱ - 1‖ = ‖P₀ Op 1‖ ≤ ε_ϱ = R_Z (M_⋆ + N_ns + D_col)`;
* (c4) `|⟪h, Op h⟫| ≤ R_Z (N_ns + D_col) ‖h‖²` for `h ∈ H_⊥`.
These are the fields `rho_bound` and `perp_bound` of `RouteAInputs`.

Also (a) `mucentre_norm` and (b) `mucentre_form` (the norm and the form of `F = c 1 + F_V + F_⊥`),
(c1) `mucentre_Z` (`Z₀ - 1 = 2 E_μ h_⋆ + ⟪1, (T_ns - T_coll) 1⟫`, so `Z₀ ≥ 1 - ε_Z`), the
scalar step of (c5), `mucentre_cperp`, and `stars_c_inputs`, which turns the conclusion of
`lem:spec:stars` (c), `∑_S T_S 1 = h_⋆ + E_μ h_⋆`, into the star hypotheses of the two.
-/

@[expose] public section

open scoped InnerProductSpace
open RCLike

namespace Sarkozy.Spectral

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- **`prop:spec2:mucentre` (c3), (c4)**, abstract form. -/
theorem mucentre_inputs (T K₀ Tstar Tns Tcoll : H →ₗ[𝕜] H) (one : H) (hone : ‖one‖ = 1)
    (V : Submodule 𝕜 H) {Z₀ εZ Nns Dcol Mstar : ℝ} (hεZ : εZ < 1) (hZ : 1 - εZ ≤ Z₀)
    (hT : ∀ x, T x = ((Z₀⁻¹ : ℝ) : 𝕜) • K₀ x)
    (hK : ∀ x, K₀ x = ⟪one, x⟫ • one + Tstar x + Tns x - Tcoll x)
    (hmean : ⟪one, T one⟫ = 1)
    (hstar : ∀ h h', ⟪one, h⟫ = 0 → (∀ v ∈ V, ⟪v, h⟫ = 0) → ⟪one, h'⟫ = 0 →
      (∀ v ∈ V, ⟪v, h'⟫ = 0) → ⟪h', Tstar h⟫ = 0)
    (hstar1 : ‖Tstar one - ⟪one, Tstar one⟫ • one‖ ≤ Mstar)
    (hns : ∀ x, ‖Tns x‖ ≤ Nns * ‖x‖) (hcoll : ∀ x, ‖Tcoll x‖ ≤ Dcol * ‖x‖) :
    ‖T one - one‖ ≤ (Mstar + Nns + Dcol) / (1 - εZ) ∧
      ∀ h, ⟪one, h⟫ = 0 → (∀ v ∈ V, ⟪v, h⟫ = 0) →
        |re ⟪h, T h⟫| ≤ (Nns + Dcol) / (1 - εZ) * ‖h‖ ^ 2 := by
  have hd : 0 < 1 - εZ := by linarith
  have hZ0 : 0 < Z₀ := lt_of_lt_of_le hd hZ
  have hone' : ⟪one, one⟫ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hone]
    simp
  have hNns : 0 ≤ Nns := by
    have := hns 0
    simp only [map_zero, norm_zero, mul_zero] at this
    have h1 := hns one
    rw [hone, mul_one] at h1
    exact (norm_nonneg _).trans h1
  have hDcol : 0 ≤ Dcol := by
    have h1 := hcoll one
    rw [hone, mul_one] at h1
    exact (norm_nonneg _).trans h1
  constructor
  · -- `ϱ - 1 = P₀ Op 1 = Z₀⁻¹ P₀ K₀ 1`
    set P0 : H → H := fun x => x - ⟪one, x⟫ • one with hP0
    have hP0lin : ∀ x y : H, P0 (x + y) = P0 x + P0 y := fun x y => by
      simp only [hP0, inner_add_right, add_smul]
      abel
    have hP0sub : ∀ x y : H, P0 (x - y) = P0 x - P0 y := fun x y => by
      simp only [hP0, inner_sub_right, sub_smul]
      abel
    have hP0one : P0 one = 0 := by
      show one - ⟪one, one⟫ • one = 0
      rw [hone', one_smul, sub_self]
    have hP0norm : ∀ x, ‖P0 x‖ ≤ ‖x‖ := by
      intro x
      have hperp : ⟪one, P0 x⟫ = 0 := by
        simp only [hP0, inner_sub_right, inner_smul_right, hone', mul_one, sub_self]
      have hsplit : x = ⟪one, x⟫ • one + P0 x := by simp [hP0]
      have h0 : ⟪⟪one, x⟫ • one, P0 x⟫ = 0 := by rw [inner_smul_left, hperp, mul_zero]
      have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) _ _ h0
      rw [← hsplit] at hpy
      have := mul_self_nonneg ‖⟪one, x⟫ • one‖
      nlinarith [norm_nonneg x, norm_nonneg (P0 x)]
    have hrho : T one - one = ((Z₀⁻¹ : ℝ) : 𝕜) • P0 (K₀ one) := by
      have h1 : T one - one = P0 (T one) := by simp [hP0, hmean]
      rw [h1, hT one]
      simp only [hP0, inner_smul_right, smul_sub, mul_smul]
    have hK1 : P0 (K₀ one) = (Tstar one - ⟪one, Tstar one⟫ • one) + P0 (Tns one) -
        P0 (Tcoll one) := by
      rw [hK one, hP0sub, hP0lin, hP0lin, hone', one_smul, hP0one, zero_add]
    have hbound : ‖P0 (K₀ one)‖ ≤ Mstar + Nns + Dcol := by
      rw [hK1]
      have h1 := hP0norm (Tns one)
      have h2 := hP0norm (Tcoll one)
      have h3 := hns one
      have h4 := hcoll one
      rw [hone, mul_one] at h3 h4
      calc ‖(Tstar one - ⟪one, Tstar one⟫ • one) + P0 (Tns one) - P0 (Tcoll one)‖
          ≤ ‖(Tstar one - ⟪one, Tstar one⟫ • one) + P0 (Tns one)‖ + ‖P0 (Tcoll one)‖ :=
            norm_sub_le _ _
        _ ≤ ‖Tstar one - ⟪one, Tstar one⟫ • one‖ + ‖P0 (Tns one)‖ + ‖P0 (Tcoll one)‖ := by
            gcongr
            exact norm_add_le _ _
        _ ≤ Mstar + Nns + Dcol := by linarith
    rw [hrho, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hZ0)]
    rw [inv_mul_le_iff₀ hZ0]
    calc ‖P0 (K₀ one)‖ ≤ Mstar + Nns + Dcol := hbound
      _ = (Mstar + Nns + Dcol) / (1 - εZ) * (1 - εZ) := by field_simp
      _ ≤ (Mstar + Nns + Dcol) / (1 - εZ) * Z₀ := by
          refine mul_le_mul_of_nonneg_left hZ (div_nonneg ?_ hd.le)
          have := (norm_nonneg _).trans hstar1
          linarith
      _ = Z₀ * ((Mstar + Nns + Dcol) / (1 - εZ)) := by ring
  · intro h h1 hV
    -- only `T_ns - T_coll` contributes
    have hK' : ⟪h, K₀ h⟫ = ⟪h, Tns h⟫ - ⟪h, Tcoll h⟫ := by
      rw [hK h, h1, zero_smul, zero_add, inner_sub_right, inner_add_right,
        hstar h h h1 hV h1 hV, zero_add]
    have hQ : re ⟪h, T h⟫ = Z₀⁻¹ * (re ⟪h, Tns h⟫ - re ⟪h, Tcoll h⟫) := by
      rw [hT h, inner_smul_right, RCLike.re_ofReal_mul, hK', map_sub]
    have hn : |re ⟪h, Tns h⟫ - re ⟪h, Tcoll h⟫| ≤ (Nns + Dcol) * ‖h‖ ^ 2 := by
      have a1 : |re ⟪h, Tns h⟫| ≤ Nns * ‖h‖ ^ 2 :=
        (abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans (by
          have := hns h
          nlinarith [norm_nonneg h]))
      have a2 : |re ⟪h, Tcoll h⟫| ≤ Dcol * ‖h‖ ^ 2 :=
        (abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans (by
          have := hcoll h
          nlinarith [norm_nonneg h]))
      calc |re ⟪h, Tns h⟫ - re ⟪h, Tcoll h⟫| ≤ |re ⟪h, Tns h⟫| + |re ⟪h, Tcoll h⟫| :=
            abs_sub _ _
        _ ≤ Nns * ‖h‖ ^ 2 + Dcol * ‖h‖ ^ 2 := add_le_add a1 a2
        _ = (Nns + Dcol) * ‖h‖ ^ 2 := by ring
    rw [hQ, abs_mul, abs_of_pos (inv_pos.mpr hZ0)]
    have hh : 0 ≤ (Nns + Dcol) * ‖h‖ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    calc Z₀⁻¹ * |re ⟪h, Tns h⟫ - re ⟪h, Tcoll h⟫| ≤ Z₀⁻¹ * ((Nns + Dcol) * ‖h‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hZ0.le)
      _ ≤ (1 - εZ)⁻¹ * ((Nns + Dcol) * ‖h‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (inv_anti₀ hd hZ) hh
      _ = (Nns + Dcol) / (1 - εZ) * ‖h‖ ^ 2 := by ring

/-- **`prop:spec2:mucentre` (c1)**, abstract form: with the expansion
`K₀ = 1 ⊗ 1 + T_star + T_ns - T_coll` and `⟪1, T_star 1⟫ = 2 E_μ h_⋆` (`lem:spec:stars` (c)),
`Z₀ - 1 = 2 E_μ h_⋆ + ⟪1, (T_ns - T_coll) 1⟫`; hence `|Z₀ - 1| ≤ Z_⋆ + N_ns + D_col = ε_Z`
when `2|E_μ h_⋆| ≤ Z_⋆`, and in particular `Z₀ ≥ 1 - ε_Z` (the hypothesis `hZ` of
`mucentre_inputs`). -/
theorem mucentre_Z (K₀ Tstar Tns Tcoll : H →ₗ[𝕜] H) (one : H) (hone : ‖one‖ = 1)
    (hK : ∀ x, K₀ x = ⟪one, x⟫ • one + Tstar x + Tns x - Tcoll x)
    {hm Zstar Nns Dcol : ℝ} (hstar : ⟪one, Tstar one⟫ = ((2 * hm : ℝ) : 𝕜))
    (hZs : 2 * |hm| ≤ Zstar) (hns : ∀ x, ‖Tns x‖ ≤ Nns * ‖x‖)
    (hcoll : ∀ x, ‖Tcoll x‖ ≤ Dcol * ‖x‖) :
    ⟪one, K₀ one⟫ - 1 = ((2 * hm : ℝ) : 𝕜) + ⟪one, Tns one - Tcoll one⟫ ∧
      ‖⟪one, K₀ one⟫ - 1‖ ≤ Zstar + Nns + Dcol := by
  have hone' : ⟪one, one⟫ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hone]
    simp
  have e : ⟪one, K₀ one⟫ - 1 = ((2 * hm : ℝ) : 𝕜) + ⟪one, Tns one - Tcoll one⟫ := by
    rw [hK, inner_sub_right, inner_add_right, inner_add_right, inner_smul_right, hone', hstar,
      inner_sub_right]
    ring
  refine ⟨e, ?_⟩
  rw [e]
  have h1 : ‖⟪one, Tns one - Tcoll one⟫‖ ≤ Nns + Dcol := by
    calc ‖⟪one, Tns one - Tcoll one⟫‖ ≤ ‖one‖ * ‖Tns one - Tcoll one‖ := norm_inner_le_norm _ _
      _ = ‖Tns one - Tcoll one‖ := by rw [hone, one_mul]
      _ ≤ ‖Tns one‖ + ‖Tcoll one‖ := norm_sub_le _ _
      _ ≤ Nns * ‖one‖ + Dcol * ‖one‖ := add_le_add (hns one) (hcoll one)
      _ = Nns + Dcol := by rw [hone, mul_one, mul_one]
  calc ‖((2 * hm : ℝ) : 𝕜) + ⟪one, Tns one - Tcoll one⟫‖
      ≤ ‖((2 * hm : ℝ) : 𝕜)‖ + ‖⟪one, Tns one - Tcoll one⟫‖ := norm_add_le _ _
    _ ≤ Zstar + (Nns + Dcol) := by
        refine add_le_add ?_ h1
        rw [RCLike.norm_ofReal, abs_mul, abs_two]
        exact hZs
    _ = Zstar + Nns + Dcol := by ring

/-- **From `lem:spec:stars` (c) to the star inputs**: if the stars map `1` to `h_⋆ + E_μ h_⋆`
(`T_star 1 = h_⋆ + ⟪1, h_⋆⟫ 1`), then `⟪1, T_star 1⟫ = 2 ⟪1, h_⋆⟫` (the hypothesis `hstar` of
`mucentre_Z`) and `P₀ T_star 1 = h_⋆ - E_μ h_⋆`, so `‖h_⋆ - E_μ h_⋆‖ ≤ M_⋆` gives the
hypothesis `hstar1` of `mucentre_inputs`. -/
theorem stars_c_inputs (Tstar : H →ₗ[𝕜] H) (one hs : H) (hone : ‖one‖ = 1)
    (hT1 : Tstar one = hs + ⟪one, hs⟫ • one) {Mstar : ℝ}
    (hM : ‖hs - ⟪one, hs⟫ • one‖ ≤ Mstar) :
    ⟪one, Tstar one⟫ = 2 * ⟪one, hs⟫ ∧ ‖Tstar one - ⟪one, Tstar one⟫ • one‖ ≤ Mstar := by
  have hone' : ⟪one, one⟫ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hone]
    simp
  have h1 : ⟪one, Tstar one⟫ = 2 * ⟪one, hs⟫ := by
    rw [hT1, inner_add_right, inner_smul_right, hone']
    ring
  refine ⟨h1, ?_⟩
  have e : Tstar one - ⟪one, Tstar one⟫ • one = hs - ⟪one, hs⟫ • one := by
    rw [h1, hT1, two_mul, add_smul]
    abel
  rw [e]
  exact hM

/-- **`prop:spec2:mucentre` (b)**: for `F = c 1 + F_V + F_⊥` with `c` real,
`⟪1, F_V⟫ = ⟪1, F_⊥⟫ = 0` and `⟪ϱ - 1, F_V⟫ = 0` (`ϱ = Op 1`, `E_μ ϱ = 1`),
`Q(F) = c² + 2c re⟪ϱ - 1, F_⊥⟫ + Q(F_V) + 2 re⟪F_⊥, Op F_V⟫ + Q(F_⊥)`. -/
theorem mucentre_form (T : H →ₗ[𝕜] H) (hT : T.IsSymmetric) (one : H)
    (hmean : ⟪one, T one⟫ = 1) (c : ℝ) (FV Fp : H) (hV : ⟪one, FV⟫ = 0) (hp : ⟪one, Fp⟫ = 0)
    (hρV : ⟪T one - one, FV⟫ = 0) :
    re ⟪(c : 𝕜) • one + (FV + Fp), T ((c : 𝕜) • one + (FV + Fp))⟫ =
      c ^ 2 + 2 * c * re ⟪T one - one, Fp⟫ + re ⟪FV, T FV⟫ + 2 * re ⟪Fp, T FV⟫ +
        re ⟪Fp, T Fp⟫ := by
  rw [re_inner_map_add T hT, re_inner_map_add T hT FV Fp]
  have h1 : re ⟪(c : 𝕜) • one, T ((c : 𝕜) • one)⟫ = c ^ 2 := by
    rw [map_smul, inner_smul_left, inner_smul_right, hmean, RCLike.conj_ofReal, mul_one,
      ← RCLike.ofReal_mul, RCLike.ofReal_re]
    ring
  have h2 : re ⟪FV + Fp, T ((c : 𝕜) • one)⟫ = c * re ⟪T one - one, Fp⟫ := by
    rw [map_smul, inner_smul_right, RCLike.re_ofReal_mul]
    congr 1
    have e1 : ⟪FV + Fp, T one⟫ = ⟪FV + Fp, T one - one⟫ + ⟪FV + Fp, one⟫ := by
      rw [inner_sub_right]
      ring
    have e2 : ⟪FV + Fp, one⟫ = 0 := by
      rw [inner_add_left, ← inner_conj_symm FV one, ← inner_conj_symm Fp one, hV, hp,
        map_zero, add_zero]
    rw [e1, e2, add_zero, inner_add_left, map_add, inner_re_symm FV, inner_re_symm Fp, hρV,
      map_zero, zero_add]
  rw [h1, h2]
  ring

/-- **`prop:spec2:mucentre` (a)**, the norm: for pairwise orthogonal `c 1`, `F_V`, `F_⊥` with
`‖1‖ = 1`, `‖F‖² = c² + ‖F_V‖² + ‖F_⊥‖²`, and if `‖F_V‖² ≥ (1 - ε_V)‖g‖²` with `0 ≤ ε_V`
(`lem:spec:degone` (c)), then `‖F‖² ≥ (1 - ε_V)(c² + ‖g‖² + ‖F_⊥‖²)`. -/
theorem mucentre_norm (one : H) (hone : ‖one‖ = 1) (c : ℝ) (FV Fp : H) (hV : ⟪one, FV⟫ = 0)
    (hp : ⟪one, Fp⟫ = 0) (hVp : ⟪FV, Fp⟫ = 0) {g εV : ℝ} (hεV0 : 0 ≤ εV)
    (hg : (1 - εV) * g ≤ ‖FV‖ ^ 2) :
    ‖(c : 𝕜) • one + (FV + Fp)‖ ^ 2 = c ^ 2 + ‖FV‖ ^ 2 + ‖Fp‖ ^ 2 ∧
      (1 - εV) * (c ^ 2 + g + ‖Fp‖ ^ 2) ≤ ‖(c : 𝕜) • one + (FV + Fp)‖ ^ 2 := by
  have h1 : ⟪(c : 𝕜) • one, FV + Fp⟫ = 0 := by
    rw [inner_smul_left, inner_add_right, hV, hp, add_zero, mul_zero]
  have hnorm : ‖(c : 𝕜) • one + (FV + Fp)‖ ^ 2 = c ^ 2 + ‖FV‖ ^ 2 + ‖Fp‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := 𝕜), h1, map_zero, mul_zero, add_zero, norm_add_sq (𝕜 := 𝕜), hVp,
      map_zero, mul_zero, add_zero, norm_smul, hone, mul_one, RCLike.norm_ofReal, sq_abs]
    ring
  refine ⟨hnorm, ?_⟩
  rw [hnorm]
  have h2 : (1 - εV) * c ^ 2 ≤ c ^ 2 := by nlinarith [sq_nonneg c]
  have h3 : (1 - εV) * ‖Fp‖ ^ 2 ≤ ‖Fp‖ ^ 2 := by nlinarith [sq_nonneg ‖Fp‖]
  nlinarith [h2, h3, hg]

omit [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] in
/-- **`prop:spec2:mucentre` (c5)**, the scalar step: if `|⟪ϱ - 1, F_⊥⟫| ≤ ε_ϱ ‖F_⊥‖` and
`Q(F_⊥) ≥ -a_⊥ ‖F_⊥‖²`, then `c² + 2c⟪ϱ - 1, F_⊥⟫ + Q(F_⊥) ≥ -(a_⊥ + ε_ϱ²) ‖F_⊥‖²`; with
`a_⊥ = R_Z(N_ns + D_col)` this is `-c_⊥ r ‖F_⊥‖²`. -/
theorem mucentre_cperp {c t q aperp eρ x : ℝ} (ht : |t| ≤ eρ * x) (hq : -(aperp * x ^ 2) ≤ q) :
    -((aperp + eρ ^ 2) * x ^ 2) ≤ c ^ 2 + 2 * c * t + q := by
  have h1 : t ^ 2 ≤ (eρ * x) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg t) ht 2
  nlinarith [sq_nonneg (c + t)]

end Sarkozy.Spectral
