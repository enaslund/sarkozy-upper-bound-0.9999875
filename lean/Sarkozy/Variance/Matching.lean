module

public import Sarkozy.Variance.Interpolation

/-!
# Matching selections (`lem:record:paired-e-joint`(b), (c))

`paper/sections/22_variance.tex`, Section 22.4. The matching records `E₀, E₁` are not folds;
their energies are reached from those of the fold records by polarization at the chamber cut
`ϑ₀`.

**Setting.** As in `Gain.lean`: the selected set `X` is the factor `j₀`, energies are
`Y[κ] = energyAt O j₀ κ F` with `μ` outside (`O j`, `j ≠ j₀`), which is positive at `ϑ₀` and
at `ι` (`(R2)`). Energies do not depend on the cut; the cut enters only through orders and
positivity.

**Hypotheses taken from elsewhere.**
* The orders of `lem:record:paired-e-joint`(a) are `lem:tr:polarization`(c), proved for
  five-type data in `FiveType/PolarizationTensor.lean` (`polarization_c_first`,
  `polarization_c_second`). Their identification with the block records of Section 22 needs
  the record laws, which are not yet defined in Lean; here the orders are hypotheses
  (`horder`).
* The merge products `𝓜_s` (the terms of `⊗(Π_{E_s,𝔅} + ε_𝔅 G_{s,𝔅})` with at least one merge
  law, of total mass `∏(1 + ε_𝔅) - 1 ≤ ε_X`) enter through (E1), `Y[𝓜_s] ≤ (1 + z) ε_X C_X Y`.
* The restoration bound `Y[⊗Π_{F_j}] ≥ (l₀ - z₁) Y` for `j = 1, 2` (`lem:record:restoration`,
  `Restoration.lean`).

**Main results.**
* `paired_e_joint_b_aligned`: **(b), first bound**:
  `½(Y[E^X_0] + Y[E^X_1]) ≥ (l₀ - C ε_X - z₁ - z ε_X C) Y`.
* `paired_e_joint_b_all`: **(b), second bound**, over the `2^k` matching embeddings:
  `2^{-k} ∑_s Y[E_s] ≥ (2^{1-k} l₀ - C ε_X - 2^{1-k} z₁ - z ε_X C) Y`.
* `paired_e_joint_c`: **(c)**: for the aligned embeddings, nonnegative weights coupling two
  copies of their actual half marginals `m^X_s` at `ι`,
  `Y[Diag_ι(m^X_0)] + Y[Diag_ι(m^X_1)] ≥ 2([l₀ - C ε_X]_+ - z₁ - z ε_X C) Y`, by the contraction
  (P1) (WP-R's `abs_energy_le_diagonal_marginals`).
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

section Matching

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- **`lem:record:paired-e-joint`(b), the aligned bound.** From the first order of (a),
`⊗Π_{F₁} + ⊗Π_{F₂} ⪯_{ϑ₀} (E^X_0 + 𝓜_0) + (E^X_1 + 𝓜_1)`, (E2) with `μ` outside, (E1) for the
merge products and the restoration bounds for the two fold products:
`½(Y[E^X_0] + Y[E^X_1]) ≥ (l₀ - C ε_X - z₁ - z ε_X C) Y`. -/
theorem paired_e_joint_b_aligned (ϑ₀ : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (j₀ : J) (hO : ∀ j, j ≠ j₀ → ϑ₀.Positive (O j)) (F : (∀ b, X b) → ℝ)
    {E0 E1 Mg0 Mg1 F1 F2 : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ}
    (horder : ϑ₀.Below (F1 + F2) ((E0 + Mg0) + (E1 + Mg1)))
    {Yμ CX C ε l₀ z₁ z : ℝ} (hY : 0 ≤ Yμ) (hCX : CX ≤ C) (hε : 0 ≤ ε) (hz : 0 ≤ z)
    (hF1 : (l₀ - z₁) * Yμ ≤ energyAt O j₀ F1 F) (hF2 : (l₀ - z₁) * Yμ ≤ energyAt O j₀ F2 F)
    (hMg0 : energyAt O j₀ Mg0 F ≤ (1 + z) * ε * CX * Yμ)
    (hMg1 : energyAt O j₀ Mg1 F ≤ (1 + z) * ε * CX * Yμ) :
    (l₀ - C * ε - z₁ - z * ε * C) * Yμ ≤ (energyAt O j₀ E0 F + energyAt O j₀ E1 F) / 2 := by
  have h := energy_le_of_below_factor ϑ₀ O j₀ hO horder F
  change energyAt O j₀ (F1 + F2) F ≤ energyAt O j₀ ((E0 + Mg0) + (E1 + Mg1)) F at h
  rw [energyAt_add, energyAt_add, energyAt_add, energyAt_add] at h
  have hc : (1 + z) * ε * CX * Yμ ≤ (1 + z) * ε * C * Yμ := by
    have h1 : 0 ≤ (1 + z) * ε := mul_nonneg (by linarith) hε
    have := mul_le_mul_of_nonneg_left hCX h1
    nlinarith
  nlinarith

/-- **`lem:record:paired-e-joint`(b), the bound over all `2^k` matching embeddings.** From the
second order of (a), `⊗Π_{F₁} + ⊗Π_{F₂} ⪯_{ϑ₀} ∑_s E_s + 𝓜` with the merge products `𝓜` of
total mass `∏(2 + 2ε_𝔅) - 2^k ≤ 2^k ε_X` ((E1): `Y[𝓜] ≤ (1 + z) 2^k ε_X C_X Y`):
`2^{-k} ∑_s Y[E_s] ≥ (2^{1-k} l₀ - C ε_X - 2^{1-k} z₁ - z ε_X C) Y`. (`S` is the set of the
`2^k` embeddings; its cardinality is not used, only the mass of the merge products.) -/
theorem paired_e_joint_b_all {σ : Type*} (ϑ₀ : ReflectionCut V)
    (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J) (hO : ∀ j, j ≠ j₀ → ϑ₀.Positive (O j))
    (F : (∀ b, X b) → ℝ) (S : Finset σ) (k : ℕ)
    (E : σ → ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ) {Mg F1 F2 : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ}
    (horder : ϑ₀.Below (F1 + F2) (∑ s ∈ S, E s + Mg))
    {Yμ CX C ε l₀ z₁ z : ℝ} (hY : 0 ≤ Yμ) (hCX : CX ≤ C) (hε : 0 ≤ ε) (hz : 0 ≤ z)
    (hF1 : (l₀ - z₁) * Yμ ≤ energyAt O j₀ F1 F) (hF2 : (l₀ - z₁) * Yμ ≤ energyAt O j₀ F2 F)
    (hMg : energyAt O j₀ Mg F ≤ (1 + z) * (2 ^ k * ε) * CX * Yμ) :
    (2 * (2 : ℝ)⁻¹ ^ k * l₀ - C * ε - 2 * (2 : ℝ)⁻¹ ^ k * z₁ - z * ε * C) * Yμ ≤
      (∑ s ∈ S, energyAt O j₀ (E s) F) / 2 ^ k := by
  have h := energy_le_of_below_factor ϑ₀ O j₀ hO horder F
  change energyAt O j₀ (F1 + F2) F ≤ energyAt O j₀ (∑ s ∈ S, E s + Mg) F at h
  rw [energyAt_add, energyAt_add] at h
  have hsum : energyAt O j₀ (∑ s ∈ S, E s) F = ∑ s ∈ S, energyAt O j₀ (E s) F := by
    have e : (∑ s ∈ S, E s) = ∑ s ∈ S, (1 : ℝ) • E s := by simp
    rw [e]
    rw [energyAt_sum]
    simp
  rw [hsum] at h
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  rw [le_div_iff₀ hk]
  have hinv : (2 : ℝ)⁻¹ ^ k * 2 ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  have hc : (1 + z) * (2 ^ k * ε) * CX * Yμ ≤ (1 + z) * (2 ^ k * ε) * C * Yμ := by
    have h1 : 0 ≤ (1 + z) * (2 ^ k * ε) := mul_nonneg (by linarith) (mul_nonneg hk.le hε)
    have := mul_le_mul_of_nonneg_left hCX h1
    nlinarith
  have e2 : (2 * (2 : ℝ)⁻¹ ^ k * l₀ - C * ε - 2 * (2 : ℝ)⁻¹ ^ k * z₁ - z * ε * C) * Yμ * 2 ^ k =
      2 * (l₀ - z₁) * Yμ - (1 + z) * (2 ^ k * ε) * C * Yμ := by
    have : (2 : ℝ)⁻¹ ^ k * 2 ^ k = 1 := hinv
    linear_combination (2 * l₀ * Yμ - 2 * z₁ * Yμ) * this
  rw [e2]
  linarith

/-- **`lem:record:paired-e-joint`(c)**: the aligned embeddings `E^X_s` are nonnegative weights
`w_s` coupling two copies of their actual half marginals `m^X_s` at `ι`
(`lem:record:paired-e-bridge`(b)), so the contraction (P1) gives `Y[E^X_s] ≤ Y[Diag_ι(m^X_s)]`;
with the first bound of (b) (hypothesis `hb`, the conclusion of `paired_e_joint_b_aligned`),
`Y[Diag_ι(m^X_0)] + Y[Diag_ι(m^X_1)] ≥ 2([l₀ - C ε_X]_+ - e) Y` for the error
`e = z₁ + z ε_X C ≥ 0`. -/
theorem paired_e_joint_c (ι : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J)
    (hO : ∀ j, j ≠ j₀ → ι.Positive (O j)) (F : (∀ b, X b) → ℝ)
    {w0 w1 : (V → X j₀) → ℝ} (hw0 : ∀ z, 0 ≤ w0 z) (hw1 : ∀ z, 0 ≤ w1 z)
    {m0 m1 : (ι.Half → X j₀) → ℝ} (hp0 : plusMarginal ι w0 = m0) (hn0 : minusMarginal ι w0 = m0)
    (hp1 : plusMarginal ι w1 = m1) (hn1 : minusMarginal ι w1 = m1)
    {Yμ C ε l₀ e : ℝ} (hY : 0 ≤ Yμ) (he : 0 ≤ e)
    (hb : (l₀ - C * ε - e) * Yμ ≤
      (energyAt O j₀ (signedIntegral w0) F + energyAt O j₀ (signedIntegral w1) F) / 2) :
    2 * (max 0 (l₀ - C * ε) - e) * Yμ ≤
      energyAt O j₀ (ι.diagonalLaw m0) F + energyAt O j₀ (ι.diagonalLaw m1) F := by
  have hcontr : ∀ {w : (V → X j₀) → ℝ} {m : (ι.Half → X j₀) → ℝ}, (∀ z, 0 ≤ w z) →
      plusMarginal ι w = m → minusMarginal ι w = m →
      energyAt O j₀ (signedIntegral w) F ≤ energyAt O j₀ (ι.diagonalLaw m) F := by
    intro w m hw hp hn
    have hm0 : ∀ x, 0 ≤ m x := fun x => hp ▸ plusMarginal_nonneg ι hw x
    have hD := energy_diagonalLaw_nonneg ι O j₀ hO hm0 F
    have h := abs_energy_le_diagonal_marginals ι O j₀ hO hw F
    rw [hp, hn, Real.mul_self_sqrt hD] at h
    exact (le_abs_self _).trans h
  have h0 := hcontr hw0 hp0 hn0
  have h1 := hcontr hw1 hp1 hn1
  have hD0 := energy_diagonalLaw_nonneg ι O j₀ hO (fun x => hp0 ▸ plusMarginal_nonneg ι hw0 x) F
  have hD1 := energy_diagonalLaw_nonneg ι O j₀ hO (fun x => hp1 ▸ plusMarginal_nonneg ι hw1 x) F
  rcases le_or_gt 0 (l₀ - C * ε) with hpos | hneg
  · rw [max_eq_right hpos]
    linarith
  · rw [max_eq_left hneg.le]
    have : 2 * (0 - e) * Yμ ≤ 0 := by nlinarith
    linarith

end Matching

end Sarkozy.Variance
