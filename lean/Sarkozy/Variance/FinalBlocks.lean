module

public import Sarkozy.Variance.Final
public import Sarkozy.Variance.GainBlocks

/-!
# The fold classes of the final construction with each block its own factor
(`cor:variance:final`(i))

`paper/sections/22_variance.tex`, `cor:variance:final`(i) for the fold selections, with the
selected set `X` as a set of factors: `var_gain_b_blocks` with the certified `R_* ≥ R_err`
(`gainOf_anti`). The aligned matching classes are `background_variance_class_cost_blocks`
(`ClassCostBlocks.lean`).
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)] {ι : Type*}

/-- **`cor:variance:final`(i), fold selections, blocks as factors**: the class cost
`B - g_F(m)` with `g_F(m) = [b_F(m) - R_*]_+`. -/
theorem variance_final_fold_class_blocks (c : ReflectionCut V)
    (O N lam : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (Xs : Finset J) (hXs : Xs.Nonempty)
    (hO : ∀ j, j ∉ Xs → c.Positive (O j)) (hN : ∀ j, j ∉ Xs → c.Bracket (N j) (lam j) (N j))
    (F : (∀ b, X b) → ℝ) (R : Finset ι) (hR : R.Nonempty)
    (w : ι → ∀ j, (V → X j) → ℝ) (m : ι → ∀ j, (c.Half → X j) → ℝ)
    (hw : ∀ φ ∈ R, ∀ j ∈ Xs, ∀ z, 0 ≤ w φ j z)
    (hp : ∀ φ ∈ R, ∀ j ∈ Xs, plusMarginal c (w φ j) = m φ j)
    (hn : ∀ φ ∈ R, ∀ j ∈ Xs, minusMarginal c (w φ j) = m φ j)
    (ht : ∀ φ ∈ R, ∀ j ∈ Xs, ∀ G H : (c.Half → X j) → ℝ,
      c.form (signedIntegral (w φ j)) G H = c.form (signedIntegral (w φ j)) H G)
    (hmpos : ∀ φ ∈ R, ∀ j ∈ Xs, 0 < ∑ x, m φ j x) (κj : ι → J → ℝ)
    (hcen : ∀ φ ∈ R, ∀ j ∈ Xs, CentredNormLe c (signedIntegral (w φ j)) (m φ j) (κj φ j))
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hκ : ∀ φ ∈ R, ∀ j ∈ Xs, κj φ j ≤ κ)
    {Yμ CX Cm ℓ z₁ z₂ z₃ z₄ Bf Rerr Rstar : ℝ} (hY : 0 ≤ Yμ) (hCX : 1 ≤ CX) (hC : CX ≤ Cm)
    (hz₁ : 0 ≤ z₁) (hz₂ : 0 ≤ z₂) (hz₄ : 0 ≤ z₄) (hRs : Rerr ≤ Rstar)
    (hRes : (ℓ - z₁) * Yμ ≤
      (∑ φ ∈ R, diagonalIntegral (tensorLaw (recFam c O Xs Xs (w φ) (m φ))) F) / R.card)
    (hE1 : ∀ φ ∈ R, diagonalIntegral (tensorLaw (diagFam c O Xs Xs (m φ))) F ≤
      (1 + z₂) * CX * Yμ)
    (γ : J → ℝ) (hγ : ∀ j ∈ Xs, 0 ≤ γ j) (ζ : ι → ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (hζ : ∀ φ ∈ R, ∀ j ∈ Xs, ∀ G H : (c.Half → X j) → ℝ, |c.form (ζ φ j) G H| ≤
      γ j * Real.sqrt (c.form (c.diagonalLaw (m φ j) - indepLaw c (m φ j)) G G) *
        Real.sqrt (c.form (c.diagonalLaw (m φ j) - indepLaw c (m φ j)) H H))
    (hDiagN : ∀ φ ∈ R, diagonalIntegral
      (tensorLaw fun j => if j ∈ Xs then c.diagonalLaw (m φ j) else N j) F ≤
        (Bf + z₃) * CX * Yμ)
    (hJN : ∀ φ ∈ R, diagonalIntegral (tensorLaw (recFam c O Xs ∅ (w φ) (m φ))) F -
        (Rerr + z₄) * CX * Yμ ≤
      diagonalIntegral (tensorLaw fun j => if j ∈ Xs then indepLaw c (m φ j) else N j) F) :
    ∑ φ ∈ R, |diagonalIntegral (tensorLaw fun j => if j ∈ Xs then ζ φ j else lam j) F| ≤
      (Bf - gainOf ℓ Cm κ Rstar + (z₃ + z₄ + (z₁ + κ * z₂) / (1 - κ))) *
        (∑ _φ ∈ R, (∏ j ∈ Xs, γ j) * CX) * Yμ := by
  have h := var_gain_b_blocks c O N lam Xs hXs hO hN F R hR w m hw hp hn ht hmpos κj hcen hκ0 hκ1
    hκ hY hCX hC hz₁ hz₂ hz₄ hRes hE1 γ hγ ζ hζ hDiagN hJN
  refine h.trans ?_
  have hsum : 0 ≤ (∑ _φ ∈ R, (∏ j ∈ Xs, γ j) * CX) * Yμ := by
    apply mul_nonneg _ hY
    exact sum_nonneg fun _ _ => mul_nonneg (prod_nonneg hγ) (by linarith)
  have hmono := gainOf_anti (l₀ := ℓ) (C := Cm) (κ := κ) hRs
  have := mul_le_mul_of_nonneg_right (show Bf - gainOf ℓ Cm κ Rerr +
      (z₃ + z₄ + (z₁ + κ * z₂) / (1 - κ)) ≤
      Bf - gainOf ℓ Cm κ Rstar + (z₃ + z₄ + (z₁ + κ * z₂) / (1 - κ)) by linarith) hsum
  calc (Bf - gainOf ℓ Cm κ Rerr + (z₃ + z₄ + (z₁ + κ * z₂) / (1 - κ))) *
        (∑ _φ ∈ R, (∏ j ∈ Xs, γ j) * CX) * Yμ
      = (Bf - gainOf ℓ Cm κ Rerr + (z₃ + z₄ + (z₁ + κ * z₂) / (1 - κ))) *
          ((∑ _φ ∈ R, (∏ j ∈ Xs, γ j) * CX) * Yμ) := by ring
    _ ≤ (Bf - gainOf ℓ Cm κ Rstar + (z₃ + z₄ + (z₁ + κ * z₂) / (1 - κ))) *
          ((∑ _φ ∈ R, (∏ j ∈ Xs, γ j) * CX) * Yμ) := this
    _ = _ := by ring

end Sarkozy.Variance
