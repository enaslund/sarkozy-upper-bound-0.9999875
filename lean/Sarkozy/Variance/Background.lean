module

public import Sarkozy.Variance.Gain

/-!
# Positive backgrounds in a selected variance (`prop:background-variance`)

`paper/sections/22_variance.tex`, Section 22.6, `prop:background-variance`, with the margins
`eq:variance:margins` and the gains `eq:variance:background-gain`.

**What is formalized.**
* `class_cost_of_product_energy`: **the class-cost step** of the proof of (a) (and of
  `lem:var-gain`(b)): a lower bound `avg_s Y^{O'}[J_s] ≥ (C_m b̃ - z_b) Y` for the products of
  the actual half marginals, with any outside law `O'` (here `Ñ₀`), the two bounds of
  `lem:record:variance-interface`(ii) relative to `O'` and the bilinear bounds of the selected
  differences give `∑_s |I_{ω_s}| ≤ (B - [b̃ - R_*]_+ + z) ∑_s π_{ω_s} Y` for every
  `R_* ≥ R_err ≥ 0`. The comparison of `Ñ` with `Ñ₀` is made once, for all kept terms together.
* `background_selected`: **the selected term** of (a), measure level:
  `½ ∑_s Y[J_s] ≥ (C_m b_E(m) - z) Y` from (P3) (proved), (E1) for the selected diagonals and
  `lem:record:paired-e-joint`(b) (hypothesis `hb`, `paired_e_joint_b_aligned`).
* `background_term`: **a background term** of (a): `½ ∑_s Y[J_s ⊗ D_{Z,s}] ≥ (C_m p_E(m,r) - z) Y`
  from (P3′) in energy form (a hypothesis here; discharged at the measure level in
  `BackgroundTerm.lean` by `energy_le_product_interpolation`), (E1), (E2) and
  `lem:record:paired-e-joint`(b) for `X ∪ Z`.
* `background_assembly`: **the displayed bound** of (a): the kept terms of the exterior
  expansion (hypothesis `hext`, the expansion of `Ñ_{0,-X}` with the dropped terms
  nonnegative by (E2)), the term bounds and the choice weights
  `∑_{Z of pattern r} coeff_Z ≥ W(m,r;c_E)` (`lem:distinct-choice`(a), hypothesis) give
  `½ ∑_s Y^{Ñ₀}[J_s] ≥ (C_m [b_E(m) + ∑_r W(m,r;c_E) p_E(m,r)] - z) Y`.
* `background_gain_le_one`: `0 ≤ g_E(m)`, and `g_E(m) ≤ 1` when the bracket is at most `1 + R_*`
  (the gate of `cert:variance:fresh`).

(b) of the proposition is `cor:var-classes`(i) with `lem:var-gain`(c) (`Gain.lean`).
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

section ClassCost

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)] {ι : Type*}

/-- **The class-cost step** of `prop:background-variance`(a). Let `R` be the (nonempty) set of
selections of a class, with the selected record differences `ζ s`, bilinear bound `γ ≥ 0`
relative to the centred norm of the actual half marginal `m s` (`lem:record:variance-interface`(i)),
prices `π_s = γ C_X`, and suppose
* `avg_s Y^{O'}[J_s] ≥ (C_m b̃ - z_b) Y` with `1 ≤ C_X ≤ C_m` (the displayed bound, `O' = Ñ₀`);
* `Y^Ñ[Diag(m_s)] ≤ (B + z₃) C_X Y` and `Y^Ñ[J_s] ≥ Y^{O'}[J_s] - (R_err + z₄) C_X Y`
  (`lem:record:variance-interface`(ii), comparing `Ñ` with `O'`).

Then `∑_s |I_s| ≤ (B - [b̃ - R_*]_+ + z₃ + z₄ + z_b) ∑_s π_s Y` for `R_* ≥ R_err ≥ 0`. -/
theorem class_cost_of_product_energy (c : ReflectionCut V)
    (N lam O' : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J)
    (hN : ∀ j, j ≠ j₀ → c.Bracket (N j) (lam j) (N j)) (F : (∀ b, X b) → ℝ)
    (R : Finset ι) (hR : R.Nonempty) (m : ι → (c.Half → X j₀) → ℝ)
    (hm : ∀ s ∈ R, ∀ x, 0 ≤ m s x) (ζ : ι → ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ) {γ : ℝ} (hγ : 0 ≤ γ)
    (hζ : ∀ s ∈ R, ∀ G H : (c.Half → X j₀) → ℝ, |c.form (ζ s) G H| ≤
      γ * Real.sqrt (c.form (c.diagonalLaw (m s) - indepLaw c (m s)) G G) *
        Real.sqrt (c.form (c.diagonalLaw (m s) - indepLaw c (m s)) H H))
    {Yμ CX Cm bt zb z₃ z₄ Bf Rerr Rstar : ℝ} (hY : 0 ≤ Yμ) (hCX : 1 ≤ CX) (hCm : CX ≤ Cm)
    (hzb : 0 ≤ zb) (hz₄ : 0 ≤ z₄) (hR0 : 0 ≤ Rerr) (hRs : Rerr ≤ Rstar)
    (hbound : (Cm * bt - zb) * Yμ ≤ (∑ s ∈ R, energyAt O' j₀ (indepLaw c (m s)) F) / R.card)
    (hDiagN : ∀ s ∈ R, energyAt N j₀ (c.diagonalLaw (m s)) F ≤ (Bf + z₃) * CX * Yμ)
    (hJN : ∀ s ∈ R, energyAt O' j₀ (indepLaw c (m s)) F - (Rerr + z₄) * CX * Yμ ≤
      energyAt N j₀ (indepLaw c (m s)) F) :
    ∑ s ∈ R, |energyAt lam j₀ (ζ s) F| ≤
      (Bf - max 0 (bt - Rstar) + (z₃ + z₄ + zb)) * (∑ _s ∈ R, γ * CX) * Yμ := by
  have hn : (0 : ℝ) < R.card := by exact_mod_cast hR.card_pos
  have hNpos : ∀ j, j ≠ j₀ → c.Positive (N j) := fun j hj => (hN j hj).left_positive
  have hI : ∀ s ∈ R, |energyAt lam j₀ (ζ s) F| ≤
      γ * (energyAt N j₀ (c.diagonalLaw (m s)) F - energyAt N j₀ (indepLaw c (m s)) F) :=
    fun s hs => abs_energy_le_variance c N lam j₀ hN (hm s hs) hγ (ζ s) (hζ s hs) F
  have hsumγ : ∑ _s ∈ R, γ * CX = R.card * (γ * CX) := by rw [sum_const, nsmul_eq_mul]
  rw [hsumγ]
  have hCXY : 0 ≤ CX * Yμ := by nlinarith
  by_cases hg : 0 ≤ bt - Rstar
  · rw [max_eq_right hg]
    have hbt : 0 ≤ bt := by linarith
    -- `C_m b̃ ≥ C_X b̃` and `z_b Y ≤ z_b C_X Y`
    have hb' : R.card * ((bt - zb) * CX * Yμ) ≤
        ∑ s ∈ R, energyAt O' j₀ (indepLaw c (m s)) F := by
      have h1 := (le_div_iff₀ hn).mp hbound
      have h2 : (bt - zb) * CX * Yμ ≤ (Cm * bt - zb) * Yμ := by
        have e1 : CX * bt ≤ Cm * bt := mul_le_mul_of_nonneg_right hCm hbt
        have e2 : zb * Yμ ≤ zb * CX * Yμ := by
          have := mul_nonneg (mul_nonneg hzb hY) (sub_nonneg.mpr hCX)
          nlinarith
        nlinarith
      nlinarith
    have hle : ∀ s ∈ R, |energyAt lam j₀ (ζ s) F| ≤
        γ * ((Bf + z₃) * CX * Yμ + (Rerr + z₄) * CX * Yμ -
          energyAt O' j₀ (indepLaw c (m s)) F) := by
      intro s hs
      refine (hI s hs).trans ?_
      apply mul_le_mul_of_nonneg_left _ hγ
      linarith [hDiagN s hs, hJN s hs]
    have hsum := sum_le_sum hle
    rw [← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul] at hsum
    refine hsum.trans ?_
    have h3 : γ * (R.card * ((Bf + z₃) * CX * Yμ + (Rerr + z₄) * CX * Yμ) -
        ∑ s ∈ R, energyAt O' j₀ (indepLaw c (m s)) F) ≤
        γ * (R.card * ((Bf + z₃) * CX * Yμ + (Rerr + z₄) * CX * Yμ) -
          R.card * ((bt - zb) * CX * Yμ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hγ
    refine h3.trans ?_
    have h4 : 0 ≤ (R.card : ℝ) * (γ * CX) * Yμ := by
      have := mul_nonneg hn.le hγ
      nlinarith
    have h5 : γ * (R.card * ((Bf + z₃) * CX * Yμ + (Rerr + z₄) * CX * Yμ) -
          R.card * ((bt - zb) * CX * Yμ)) =
        (Bf - (bt - Rerr) + (z₃ + z₄ + zb)) * (R.card * (γ * CX) * Yμ) := by ring
    rw [h5]
    calc (Bf - (bt - Rerr) + (z₃ + z₄ + zb)) * (R.card * (γ * CX) * Yμ)
        ≤ (Bf - (bt - Rstar) + (z₃ + z₄ + zb)) * (R.card * (γ * CX) * Yμ) :=
          mul_le_mul_of_nonneg_right (by linarith) h4
      _ = (Bf - (bt - Rstar) + (z₃ + z₄ + zb)) * (R.card * (γ * CX)) * Yμ := by ring
  · push Not at hg
    rw [max_eq_left hg.le]
    have hle : ∀ s ∈ R, |energyAt lam j₀ (ζ s) F| ≤ γ * ((Bf + z₃) * CX * Yμ) := by
      intro s hs
      refine (hI s hs).trans ?_
      apply mul_le_mul_of_nonneg_left _ hγ
      have := energy_indepLaw_nonneg c N j₀ hNpos (hm s hs) F
      linarith [hDiagN s hs]
    have hsum := sum_le_sum hle
    rw [sum_const, nsmul_eq_mul] at hsum
    refine hsum.trans ?_
    have h4 : 0 ≤ (R.card : ℝ) * (γ * CX) * Yμ := by
      have := mul_nonneg hn.le hγ
      nlinarith
    calc (R.card : ℝ) * (γ * ((Bf + z₃) * CX * Yμ)) = (Bf + z₃) * (R.card * (γ * CX) * Yμ) := by
          ring
      _ ≤ (Bf - 0 + (z₃ + z₄ + zb)) * (R.card * (γ * CX) * Yμ) :=
          mul_le_mul_of_nonneg_right (by linarith) h4
      _ = (Bf - 0 + (z₃ + z₄ + zb)) * (R.card * (γ * CX)) * Yμ := by ring

end ClassCost

section Selected

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- **`prop:background-variance`(a), the selected term.** The aligned embeddings `E_s`
(`s = 0, 1`) are symmetric at `ι` with actual half marginals `m_s` and centred norm at most
`k = k_{E,m} < 1` (`lem:record:paired-e-bridge`(b), hypothesis `hcen`), so (P3) gives
`(1 - k) Y[J_s] ≥ Y[E_s] - k Y[Diag(m_s)]`; with (E1) for the diagonals
(`≤ (1 + z₂) C_X Y`, `C_X ≤ C_m`) and `lem:record:paired-e-joint`(b) with `l₀ = ℓ_m`,
`C = C_m`, `ε_X ≤ η_m` (hypothesis `hb`):
`½(Y[J_0] + Y[J_1]) ≥ (C_m b_E(m) - (e + k z₂ C_m)/(1 - k)) Y`, with
`b_E(m) = (ℓ_m/C_m - η_m - k)/(1 - k)` (`eq:variance:margins`). -/
theorem background_selected (ι : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J)
    (hO : ∀ j, j ≠ j₀ → ι.Positive (O j)) (F : (∀ b, X b) → ℝ)
    {E0 E1 : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ} {m0 m1 : (ι.Half → X j₀) → ℝ}
    (hm0 : ∀ x, 0 ≤ m0 x) (hm1 : ∀ x, 0 ≤ m1 x) (hm0p : 0 < ∑ x, m0 x) (hm1p : 0 < ∑ x, m1 x)
    (hs0 : ∀ G H : (ι.Half → X j₀) → ℝ, ι.form E0 G H = ι.form E0 H G)
    (hs1 : ∀ G H : (ι.Half → X j₀) → ℝ, ι.form E1 G H = ι.form E1 H G)
    (hp0 : ∀ G : (ι.Half → X j₀) → ℝ, ι.form E0 G 1 = ∑ x, m0 x * G x)
    (hp1 : ∀ G : (ι.Half → X j₀) → ℝ, ι.form E1 G 1 = ∑ x, m1 x * G x)
    {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hcen0 : CentredNormLe ι E0 m0 k) (hcen1 : CentredNormLe ι E1 m1 k)
    {Yμ CX Cm ℓ η e z₂ : ℝ} (hY : 0 ≤ Yμ) (hCX : CX ≤ Cm) (hCm : 0 < Cm) (hz₂ : 0 ≤ z₂)
    (hD0 : energyAt O j₀ (ι.diagonalLaw m0) F ≤ (1 + z₂) * CX * Yμ)
    (hD1 : energyAt O j₀ (ι.diagonalLaw m1) F ≤ (1 + z₂) * CX * Yμ)
    (hb : (ℓ - Cm * η - e) * Yμ ≤ (energyAt O j₀ E0 F + energyAt O j₀ E1 F) / 2) :
    (Cm * ((ℓ / Cm - η - k) / (1 - k)) - (e + k * z₂ * Cm) / (1 - k)) * Yμ ≤
      (energyAt O j₀ (indepLaw ι m0) F + energyAt O j₀ (indepLaw ι m1) F) / 2 := by
  have h1k : 0 < 1 - k := by linarith
  have hP0 := energy_le_centred_interpolation ι O j₀ hO hm0 hm0p hs0 hp0 hcen0 F
  have hP1 := energy_le_centred_interpolation ι O j₀ hO hm1 hm1p hs1 hp1 hcen1 F
  have hCXY : (1 + z₂) * CX * Yμ ≤ (1 + z₂) * Cm * Yμ := by
    have := mul_le_mul_of_nonneg_left hCX (by linarith : (0 : ℝ) ≤ 1 + z₂)
    nlinarith
  have e1 : (Cm * ((ℓ / Cm - η - k) / (1 - k)) - (e + k * z₂ * Cm) / (1 - k)) =
      ((ℓ - Cm * η - k * Cm) - (e + k * z₂ * Cm)) / (1 - k) := by
    field_simp
  rw [e1, div_mul_eq_mul_div, div_le_iff₀ h1k]
  nlinarith

end Selected

/-! ### The background terms and the displayed bound (scalar form) -/

/-- **`prop:background-variance`(a), a background term**, in energy form. For a set `Z` of
pattern `r` disjoint from `X`, with `T_s = Y[J_s ⊗ D_{Z,s}] ≥ 0` ((E2)), (P3′) gives
`Y[E^{X∪Z}_s] ≤ (1 - k) T_s + k Y[Diag(m^X_s ⊗ m^Z_s)]` (hypotheses `hP0`, `hP1`; at the
measure level they are (P3′), `energy_le_product_interpolation`, see
`background_term_measure`), (E1) bounds the diagonal by
`(1 + z₂) C_{X∪Z} Y ≤ (1 + z₂) C_m C_r Y`, and `lem:record:paired-e-joint`(b) for `X ∪ Z`
(pattern `m + r`) gives `½ ∑_s Y[E^{X∪Z}_s] ≥ (ℓ_{m+r} - C_m C_r η_{m+r} - e) Y`. Then
`½ ∑_s T_s ≥ (C_m p_E(m,r) - (e + k z₂ C_m C_r)/(1 - k)) Y`, with
`p_E(m,r) = [ℓ_{m+r}/C_m - C_r(η_{m+r} + k)]_+/(1 - k)`. -/
theorem background_term {YE0 YE1 T0 T1 D0 D1 Yμ ℓ Cm Cr CXZ η k e z₂ : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1) (hY : 0 ≤ Yμ) (hCm : 0 < Cm) (hCr : 0 ≤ Cr) (hz₂ : 0 ≤ z₂)
    (he : 0 ≤ e) (hCXZ : CXZ ≤ Cm * Cr) (hT0 : 0 ≤ T0) (hT1 : 0 ≤ T1)
    (hP0 : YE0 ≤ (1 - k) * T0 + k * D0) (hP1 : YE1 ≤ (1 - k) * T1 + k * D1)
    (hD0 : D0 ≤ (1 + z₂) * CXZ * Yμ) (hD1 : D1 ≤ (1 + z₂) * CXZ * Yμ)
    (hb : (ℓ - Cm * Cr * η - e) * Yμ ≤ (YE0 + YE1) / 2) :
    (Cm * (max 0 (ℓ / Cm - Cr * (η + k)) / (1 - k)) - (e + k * z₂ * Cm * Cr) / (1 - k)) * Yμ ≤
      (T0 + T1) / 2 := by
  have h1k : 0 < 1 - k := by linarith
  have hCC : (1 + z₂) * CXZ * Yμ ≤ (1 + z₂) * (Cm * Cr) * Yμ := by
    have := mul_le_mul_of_nonneg_left hCXZ (by linarith : (0 : ℝ) ≤ 1 + z₂)
    nlinarith
  have herr : 0 ≤ (e + k * z₂ * Cm * Cr) / (1 - k) := by
    apply div_nonneg _ h1k.le
    have := mul_nonneg (mul_nonneg (mul_nonneg hk0 hz₂) hCm.le) hCr
    linarith
  rcases le_or_gt 0 (ℓ / Cm - Cr * (η + k)) with hpos | hneg
  · rw [max_eq_right hpos]
    have e1 : (Cm * ((ℓ / Cm - Cr * (η + k)) / (1 - k)) - (e + k * z₂ * Cm * Cr) / (1 - k)) =
        ((ℓ - Cm * Cr * η - k * (Cm * Cr)) - (e + k * z₂ * Cm * Cr)) / (1 - k) := by
      field_simp
      ring
    rw [e1, div_mul_eq_mul_div, div_le_iff₀ h1k]
    nlinarith
  · rw [max_eq_left hneg.le, zero_div, mul_zero, zero_sub]
    have : -((e + k * z₂ * Cm * Cr) / (1 - k)) * Yμ ≤ 0 := by
      have := mul_nonneg herr hY
      linarith
    linarith

/-- **`prop:background-variance`(a), the displayed bound**, by summing the kept terms of the
exterior expansion. Data: the selected bound `S ≥ (C_m b - z_S) Y` (`background_selected`),
a finite set `𝒵` of kept background sets `Z` with coefficients `coeff Z ≥ 0` (the products
`∏_{𝔅∈Z} c_{E,i(𝔅)} b_𝔅^{-1}`), patterns `pat Z ∈ 𝒫`, and term bounds
`T Z ≥ (C_m p(pat Z) - z_Z) Y` with `p ≥ 0` (`background_term`); the exterior expansion
`Ŝ ≥ S + ∑_{Z∈𝒵} coeff_Z T_Z` (hypothesis `hext`: the expansion of `Ñ_{0,-X}` over the sets of
middle blocks outside `X`, the dropped terms being nonnegative by (E2)); and the choice weights
`∑_{Z ∈ 𝒵, pat Z = r} coeff_Z ≥ W_r ≥ 0` (`lem:distinct-choice`(a), hypothesis). Then
`Ŝ ≥ (C_m (b + ∑_r W_r p_r) - z_S - ∑_Z coeff_Z z_Z) Y`. Here `Ŝ` is
`½ ∑_s Y^{Ñ₀}[J_s]` and `S` is `½ ∑_s Y[J_s]`; the late-pool terms `P_E(m)` of
`lem:pool-coupons`(a) are further kept terms of the same form. -/
theorem background_assembly {ζ π : Type*} [DecidableEq π] (Zs : Finset ζ) (pats : Finset π)
    (pat : ζ → π) (hpat : ∀ Z ∈ Zs, pat Z ∈ pats) (coeff T zZ : ζ → ℝ) (p W : π → ℝ)
    {Shat S Yμ Cm b zS : ℝ} (hY : 0 ≤ Yμ) (hCm : 0 ≤ Cm)
    (hcoeff : ∀ Z ∈ Zs, 0 ≤ coeff Z) (hp : ∀ r ∈ pats, 0 ≤ p r)
    (hS : (Cm * b - zS) * Yμ ≤ S) (hT : ∀ Z ∈ Zs, (Cm * p (pat Z) - zZ Z) * Yμ ≤ T Z)
    (hext : S + ∑ Z ∈ Zs, coeff Z * T Z ≤ Shat)
    (hW : ∀ r ∈ pats, W r ≤ ∑ Z ∈ Zs.filter (fun Z => pat Z = r), coeff Z) :
    (Cm * (b + ∑ r ∈ pats, W r * p r) - zS - ∑ Z ∈ Zs, coeff Z * zZ Z) * Yμ ≤ Shat := by
  -- the kept terms
  have h1 : ∀ Z ∈ Zs, coeff Z * ((Cm * p (pat Z) - zZ Z) * Yμ) ≤ coeff Z * T Z :=
    fun Z hZ => mul_le_mul_of_nonneg_left (hT Z hZ) (hcoeff Z hZ)
  have h2 := sum_le_sum h1
  -- regroup the main parts by patterns
  have hgroup : ∑ Z ∈ Zs, coeff Z * p (pat Z) =
      ∑ r ∈ pats, (∑ Z ∈ Zs.filter (fun Z => pat Z = r), coeff Z) * p r := by
    rw [← sum_fiberwise_of_maps_to hpat]
    refine sum_congr rfl fun r _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun Z hZ => ?_
    rw [(mem_filter.mp hZ).2]
  have hWp : ∑ r ∈ pats, W r * p r ≤ ∑ Z ∈ Zs, coeff Z * p (pat Z) := by
    rw [hgroup]
    exact sum_le_sum fun r hr => mul_le_mul_of_nonneg_right (hW r hr) (hp r hr)
  have e2 : ∑ Z ∈ Zs, coeff Z * ((Cm * p (pat Z) - zZ Z) * Yμ) =
      Cm * Yμ * ∑ Z ∈ Zs, coeff Z * p (pat Z) - Yμ * ∑ Z ∈ Zs, coeff Z * zZ Z := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun Z _ => by ring
  rw [e2] at h2
  have hCY : 0 ≤ Cm * Yμ := mul_nonneg hCm hY
  have h3 := mul_le_mul_of_nonneg_left hWp hCY
  nlinarith

/-- `g_E(m) = [b̃ - R_*]_+` lies in `[0, 1]` when `b̃ ≤ 1 + R_*` (the gate "every gain in
`[0, 1)`" of `cert:variance:fresh` is the strict form). -/
theorem background_gain_le_one {bt Rstar : ℝ} (h : bt ≤ 1 + Rstar) :
    0 ≤ max 0 (bt - Rstar) ∧ max 0 (bt - Rstar) ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (by linarith)⟩

end Sarkozy.Variance
