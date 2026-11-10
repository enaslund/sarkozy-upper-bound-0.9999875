module

public import Sarkozy.Variance.Gain
public import Sarkozy.Variance.ProductRecords

/-!
# `lem:var-gain`(a) with each selected block its own factor

`paper/sections/22_variance.tex`, `lem:var-gain`(a), for a selected set `X` of blocks that are
separate factors of the product law (`Xs : Finset J`), the records of an assignment `φ` being
products `⊗_{𝔅∈X} Π_{φ_𝔅,𝔅}` of nonnegative symmetric weights with centred norms
`κ_{φ,𝔅} ≤ κ` (the hypothesis (Cen) for the product, by (P4)). The proof is that of
`var_gain_a`, with (P3) for the product (`energy_le_product_records`) in place of (P3) for one
factor. Here `J_φ = ⊗_X J(m_{φ,𝔅})` and `Diag(m_φ) = ⊗_X Diag(m_{φ,𝔅})` (`recFam … ∅`,
`diagFam … Xs`).
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)] {ι : Type*}

/-- **`lem:var-gain`(a), blocks as factors.** -/
theorem var_gain_a_blocks (c : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (Xs : Finset J) (hO : ∀ j, j ∉ Xs → c.Positive (O j)) (F : (∀ b, X b) → ℝ)
    (R : Finset ι) (hR : R.Nonempty)
    (w : ι → ∀ j, (V → X j) → ℝ) (m : ι → ∀ j, (c.Half → X j) → ℝ)
    (hw : ∀ φ ∈ R, ∀ j ∈ Xs, ∀ z, 0 ≤ w φ j z)
    (hp : ∀ φ ∈ R, ∀ j ∈ Xs, plusMarginal c (w φ j) = m φ j)
    (hn : ∀ φ ∈ R, ∀ j ∈ Xs, minusMarginal c (w φ j) = m φ j)
    (ht : ∀ φ ∈ R, ∀ j ∈ Xs, ∀ G H : (c.Half → X j) → ℝ,
      c.form (signedIntegral (w φ j)) G H = c.form (signedIntegral (w φ j)) H G)
    (hmpos : ∀ φ ∈ R, ∀ j ∈ Xs, 0 < ∑ x, m φ j x) (κj : ι → J → ℝ)
    (hcen : ∀ φ ∈ R, ∀ j ∈ Xs, CentredNormLe c (signedIntegral (w φ j)) (m φ j) (κj φ j))
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hκ : ∀ φ ∈ R, ∀ j ∈ Xs, κj φ j ≤ κ)
    {Yμ CX C l₀ z₁ z₂ : ℝ} (hY : 0 ≤ Yμ) (hCX : 1 ≤ CX) (hC : CX ≤ C)
    (hz₁ : 0 ≤ z₁) (hz₂ : 0 ≤ z₂)
    (hRes : (l₀ - z₁) * Yμ ≤
      (∑ φ ∈ R, diagonalIntegral (tensorLaw (recFam c O Xs Xs (w φ) (m φ))) F) / R.card)
    (hE1 : ∀ φ ∈ R, diagonalIntegral (tensorLaw (diagFam c O Xs Xs (m φ))) F ≤
      (1 + z₂) * CX * Yμ) :
    (gainBar l₀ C κ - (z₁ + κ * z₂) / (1 - κ)) * CX * Yμ ≤
      (∑ φ ∈ R, diagonalIntegral (tensorLaw (recFam c O Xs ∅ (w φ) (m φ))) F) / R.card := by
  have hn' : (0 : ℝ) < R.card := by exact_mod_cast hR.card_pos
  have h1κ : 0 < 1 - κ := by linarith
  have hCpos : 0 < C := by linarith
  set SJ := ∑ φ ∈ R, diagonalIntegral (tensorLaw (recFam c O Xs ∅ (w φ) (m φ))) F with hSJ
  have hJnonneg : 0 ≤ SJ := by
    apply sum_nonneg
    intro φ hφ
    apply ReflectionCut.Positive.diagonal_nonneg
    apply ReflectionCut.Positive.tensor
    intro j
    simp only [recFam, notMem_empty, ↓reduceIte]
    by_cases hj : j ∈ Xs
    · simp only [hj, ↓reduceIte]
      exact positive_indepLaw c fun x => hp φ hφ j hj ▸ plusMarginal_nonneg c (hw φ hφ j hj) x
    · simp only [hj, ↓reduceIte]
      exact hO j hj
  have hsumP : ∑ φ ∈ R, diagonalIntegral (tensorLaw (recFam c O Xs Xs (w φ) (m φ))) F ≤
      (1 - κ) * SJ + R.card * (κ * ((1 + z₂) * CX * Yμ)) := by
    have hle : ∀ φ ∈ R, diagonalIntegral (tensorLaw (recFam c O Xs Xs (w φ) (m φ))) F ≤
        (1 - κ) * diagonalIntegral (tensorLaw (recFam c O Xs ∅ (w φ) (m φ))) F +
          κ * ((1 + z₂) * CX * Yμ) := by
      intro φ hφ
      have h3 := energy_le_product_records c O Xs hO F (w φ) (m φ) (hw φ hφ) (hp φ hφ)
        (hn φ hφ) (ht φ hφ) (hmpos φ hφ) (κj φ) (hcen φ hφ) (hκ φ hφ)
      have h4 := hE1 φ hφ
      nlinarith
    have := sum_le_sum hle
    rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul] at this
    exact this
  have hRes' : (l₀ - z₁) * Yμ * R.card ≤ (1 - κ) * SJ + R.card * (κ * ((1 + z₂) * CX * Yμ)) := by
    have := (le_div_iff₀ hn').mp hRes
    linarith
  rw [le_div_iff₀ hn']
  unfold gainBar
  rw [div_sub_div_same, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_le_iff₀ h1κ]
  by_cases hl : 0 ≤ l₀
  · have hA : l₀ / C * CX * Yμ ≤ l₀ * Yμ := by
      have : l₀ / C * CX ≤ l₀ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hCpos]
        nlinarith
      nlinarith
    have hB : z₁ * Yμ ≤ z₁ * CX * Yμ := by
      have := mul_nonneg (mul_nonneg hz₁ hY) (sub_nonneg.mpr hCX)
      nlinarith
    nlinarith
  · push Not at hl
    have hneg : (l₀ / C - κ - (z₁ + κ * z₂)) * CX * Yμ ≤ 0 := by
      have : l₀ / C < 0 := div_neg_of_neg_of_pos hl hCpos
      have h5 : l₀ / C - κ - (z₁ + κ * z₂) ≤ 0 := by nlinarith
      have h6 : 0 ≤ CX * Yμ := by nlinarith
      nlinarith
    nlinarith

end Sarkozy.Variance
