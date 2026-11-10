module

public import Sarkozy.Variance.Background
public import Sarkozy.Variance.ProductInterpolation

/-!
# A background term at the measure level (`prop:background-variance`(a))

`paper/sections/22_variance.tex`, proof of `prop:background-variance`(a), "A background term":
the scalar `background_term` of `Background.lean` with its (P3′) hypothesis discharged by
`energy_le_product_interpolation` (`ProductInterpolation.lean`) and `T_s ≥ 0` by (E2).

**Setting.** The selected set `X` is the factor `j₀`, the background set `Z` (pattern `r`,
disjoint from `X`) the factor `j₁`; the outside laws `O` (`μ` outside `X ∪ Z`) are positive at
`ι`. For `s ∈ {0, 1}`: the aligned embedding `E^X_s` of `X` is symmetric at `ι` with actual half
marginal `m_s` and centred norm `≤ k = k_{E,m}` (`lem:record:paired-e-bridge`(b), hypothesis);
the aligned embedding `E^Z_s` of `Z` is a nonnegative weight `w_s`, symmetric at `ι`, with both
half marginals `m'_s` (so `D_{Z,s} = Diag_ι(m'_s)`). Then
`½ ∑_s Y[J(m_s) ⊗ D_{Z,s}] ≥ (C_m p_E(m,r) - (e + k z₂ C_m C_r)/(1 - k)) Y`
from `lem:record:paired-e-joint`(b) for `X ∪ Z` (hypothesis `hb`) and (E1) for
`Diag(m_s) ⊗ Diag(m'_s)` (hypotheses `hD0`, `hD1`).
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- (E2) for two positive factors: `Y[a ⊗ b] ≥ 0`. -/
theorem energyAt₂_nonneg (c : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    {j₀ j₁ : J} (hne : j₀ ≠ j₁) (hO : ∀ j, j ≠ j₀ → j ≠ j₁ → c.Positive (O j))
    {a : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ} {b : ((V → X j₁) → ℝ) →ₗ[ℝ] ℝ} (ha : c.Positive a)
    (hb : c.Positive b) (F : (∀ i, X i) → ℝ) : 0 ≤ energyAt₂ O j₀ j₁ a b F := by
  rw [energyAt₂_eq O hne]
  apply energyAt_nonneg c _ j₀ _ ha F
  intro j hj
  by_cases h1 : j = j₁
  · subst h1
    rw [Function.update_self]
    exact hb
  · rw [Function.update_of_ne h1]
    exact hO j hj h1

/-- **`prop:background-variance`(a), a background term, measure level.** -/
theorem background_term_measure (ι : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    {j₀ j₁ : J} (hne : j₀ ≠ j₁) (hO : ∀ j, j ≠ j₀ → j ≠ j₁ → ι.Positive (O j))
    (F : (∀ i, X i) → ℝ)
    {E0 E1 : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ} {m0 m1 : (ι.Half → X j₀) → ℝ}
    (hm0 : ∀ x, 0 ≤ m0 x) (hm1 : ∀ x, 0 ≤ m1 x) (hm0p : 0 < ∑ x, m0 x) (hm1p : 0 < ∑ x, m1 x)
    (hs0 : ∀ G H : (ι.Half → X j₀) → ℝ, ι.form E0 G H = ι.form E0 H G)
    (hs1 : ∀ G H : (ι.Half → X j₀) → ℝ, ι.form E1 G H = ι.form E1 H G)
    (hp0 : ∀ G : (ι.Half → X j₀) → ℝ, ι.form E0 G 1 = ∑ x, m0 x * G x)
    (hp1 : ∀ G : (ι.Half → X j₀) → ℝ, ι.form E1 G 1 = ∑ x, m1 x * G x)
    {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hcen0 : CentredNormLe ι E0 m0 k) (hcen1 : CentredNormLe ι E1 m1 k)
    {w0 w1 : (V → X j₁) → ℝ} (hw0 : ∀ z, 0 ≤ w0 z) (hw1 : ∀ z, 0 ≤ w1 z)
    {m0' m1' : (ι.Half → X j₁) → ℝ}
    (hq0 : plusMarginal ι w0 = m0') (hr0 : minusMarginal ι w0 = m0')
    (hq1 : plusMarginal ι w1 = m1') (hr1 : minusMarginal ι w1 = m1')
    (ht0 : ∀ G H : (ι.Half → X j₁) → ℝ,
      ι.form (signedIntegral w0) G H = ι.form (signedIntegral w0) H G)
    (ht1 : ∀ G H : (ι.Half → X j₁) → ℝ,
      ι.form (signedIntegral w1) G H = ι.form (signedIntegral w1) H G)
    {Yμ ℓ Cm Cr CXZ η e z₂ : ℝ} (hY : 0 ≤ Yμ) (hCm : 0 < Cm) (hCr : 0 ≤ Cr) (hz₂ : 0 ≤ z₂)
    (he : 0 ≤ e) (hCXZ : CXZ ≤ Cm * Cr)
    (hD0 : energyAt₂ O j₀ j₁ (ι.diagonalLaw m0) (ι.diagonalLaw m0') F ≤ (1 + z₂) * CXZ * Yμ)
    (hD1 : energyAt₂ O j₀ j₁ (ι.diagonalLaw m1) (ι.diagonalLaw m1') F ≤ (1 + z₂) * CXZ * Yμ)
    (hb : (ℓ - Cm * Cr * η - e) * Yμ ≤
      (energyAt₂ O j₀ j₁ E0 (signedIntegral w0) F + energyAt₂ O j₀ j₁ E1 (signedIntegral w1) F) /
        2) :
    (Cm * (max 0 (ℓ / Cm - Cr * (η + k)) / (1 - k)) - (e + k * z₂ * Cm * Cr) / (1 - k)) * Yμ ≤
      (energyAt₂ O j₀ j₁ (indepLaw ι m0) (ι.diagonalLaw m0') F +
        energyAt₂ O j₀ j₁ (indepLaw ι m1) (ι.diagonalLaw m1') F) / 2 := by
  have hm0' : ∀ x, 0 ≤ m0' x := fun x => hq0 ▸ plusMarginal_nonneg ι hw0 x
  have hm1' : ∀ x, 0 ≤ m1' x := fun x => hq1 ▸ plusMarginal_nonneg ι hw1 x
  have hP0 := energy_le_product_interpolation ι O hne hO F hm0 hm0p hs0 hp0 hcen0 hw0 hq0 hr0 ht0
  have hP1 := energy_le_product_interpolation ι O hne hO F hm1 hm1p hs1 hp1 hcen1 hw1 hq1 hr1 ht1
  have hT0 := energyAt₂_nonneg ι O hne hO (positive_indepLaw ι hm0)
    (ι.diagonalLaw_positive hm0') F
  have hT1 := energyAt₂_nonneg ι O hne hO (positive_indepLaw ι hm1)
    (ι.diagonalLaw_positive hm1') F
  exact background_term hk0 hk1 hY hCm hCr hz₂ he hCXZ hT0 hT1 hP0 hP1 hD0 hD1 hb

end Sarkozy.Variance
