module

public import Sarkozy.Variance.GainFlat
public import Sarkozy.Variance.VarianceInterface

/-!
# `lem:var-gain`(b) with each selected block its own factor

`paper/sections/22_variance.tex`, `lem:var-gain`(b), for a selected set `X` of blocks that are
separate factors (`Xs : Finset J`): the selection terms `I_φ = Y_{ζ_φ ⊗ λ_{-X}}` with
`ζ_φ = ⊗_X ζ_{φ,𝔅}` are bounded by `lem:record:variance-interface`(i) for the product
(`abs_energy_le_variance_blocks`), and `lem:var-gain`(a) for the blocks (`var_gain_a_blocks`) gives
the gain. The two bounds of `lem:record:variance-interface`(ii) are hypotheses, as in
`var_gain_b`. The price of `ω_φ` is `γ C_X` with `γ = ∏_𝔅 γ_𝔅`, common to the class.
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)] {ι : Type*}

/-- **`lem:var-gain`(b), blocks as factors**: the selections `ω_φ`, `φ ∈ 𝓡`, form a class of cost
`B - g`, `g = [l̄ - R_err]_+`: `∑_φ |I_φ| ≤ (B - g + z) ∑_φ π_φ Y` with `π_φ = (∏ γ_𝔅) C_X`. -/
theorem var_gain_b_blocks (c : ReflectionCut V) (O N lam : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (Xs : Finset J) (hXs : Xs.Nonempty) (hO : ∀ j, j ∉ Xs → c.Positive (O j))
    (hN : ∀ j, j ∉ Xs → c.Bracket (N j) (lam j) (N j)) (F : (∀ b, X b) → ℝ)
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
    {Yμ CX C l₀ z₁ z₂ z₃ z₄ Bf Rerr : ℝ} (hY : 0 ≤ Yμ) (hCX : 1 ≤ CX) (hC : CX ≤ C)
    (hz₁ : 0 ≤ z₁) (hz₂ : 0 ≤ z₂) (hz₄ : 0 ≤ z₄)
    (hRes : (l₀ - z₁) * Yμ ≤
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
      (Bf - gainOf l₀ C κ Rerr + (z₃ + z₄ + (z₁ + κ * z₂) / (1 - κ))) *
        (∑ _φ ∈ R, (∏ j ∈ Xs, γ j) * CX) * Yμ := by
  have hn' : (0 : ℝ) < R.card := by exact_mod_cast hR.card_pos
  have h1κ : 0 < 1 - κ := by linarith
  set ea := (z₁ + κ * z₂) / (1 - κ) with hea
  have hea0 : 0 ≤ ea := div_nonneg (by nlinarith) h1κ.le
  set g := ∏ j ∈ Xs, γ j with hg
  have hg0 : 0 ≤ g := prod_nonneg hγ
  have hm : ∀ φ ∈ R, ∀ j ∈ Xs, ∀ x, 0 ≤ m φ j x := fun φ hφ j hj x =>
    hp φ hφ j hj ▸ plusMarginal_nonneg c (hw φ hφ j hj) x
  have hI : ∀ φ ∈ R, |diagonalIntegral (tensorLaw fun j => if j ∈ Xs then ζ φ j else lam j) F| ≤
      g * (diagonalIntegral (tensorLaw fun j => if j ∈ Xs then c.diagonalLaw (m φ j) else N j) F -
        diagonalIntegral (tensorLaw fun j => if j ∈ Xs then indepLaw c (m φ j) else N j) F) :=
    fun φ hφ => abs_energy_le_variance_blocks c N lam Xs hXs hN (m φ) (hm φ hφ) γ hγ (ζ φ)
      (hζ φ hφ) F
  have hsumγ : ∑ _φ ∈ R, g * CX = R.card * (g * CX) := by rw [sum_const, nsmul_eq_mul]
  rw [hsumγ]
  have hNpos : ∀ j, j ∉ Xs → c.Positive (N j) := fun j hj => (hN j hj).left_positive
  by_cases hgain : 0 ≤ gainBar l₀ C κ - Rerr
  · have hgo : gainOf l₀ C κ Rerr = gainBar l₀ C κ - Rerr := max_eq_right hgain
    rw [hgo]
    have ha := var_gain_a_blocks c O Xs hO F R hR w m hw hp hn ht hmpos κj hcen hκ0 hκ1 hκ hY
      hCX hC hz₁ hz₂ hRes hE1
    rw [← hea] at ha
    have ha' : R.card * ((gainBar l₀ C κ - ea) * CX * Yμ) ≤
        ∑ φ ∈ R, diagonalIntegral (tensorLaw (recFam c O Xs ∅ (w φ) (m φ))) F := by
      have := (le_div_iff₀ hn').mp ha
      linarith
    have hle : ∀ φ ∈ R, |diagonalIntegral (tensorLaw fun j => if j ∈ Xs then ζ φ j else lam j) F|
        ≤ g * ((Bf + z₃) * CX * Yμ + (Rerr + z₄) * CX * Yμ -
          diagonalIntegral (tensorLaw (recFam c O Xs ∅ (w φ) (m φ))) F) := by
      intro φ hφ
      refine (hI φ hφ).trans ?_
      apply mul_le_mul_of_nonneg_left _ hg0
      linarith [hDiagN φ hφ, hJN φ hφ]
    have hsum := sum_le_sum hle
    rw [← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul] at hsum
    refine hsum.trans ?_
    have h3 : g * (R.card * ((Bf + z₃) * CX * Yμ + (Rerr + z₄) * CX * Yμ) -
        ∑ φ ∈ R, diagonalIntegral (tensorLaw (recFam c O Xs ∅ (w φ) (m φ))) F) ≤
        g * (R.card * ((Bf + z₃) * CX * Yμ + (Rerr + z₄) * CX * Yμ) -
          R.card * ((gainBar l₀ C κ - ea) * CX * Yμ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hg0
    refine h3.trans (le_of_eq ?_)
    ring
  · push Not at hgain
    have hgo : gainOf l₀ C κ Rerr = 0 := max_eq_left hgain.le
    rw [hgo]
    have hle : ∀ φ ∈ R, |diagonalIntegral (tensorLaw fun j => if j ∈ Xs then ζ φ j else lam j) F|
        ≤ g * ((Bf + z₃) * CX * Yμ) := by
      intro φ hφ
      refine (hI φ hφ).trans ?_
      apply mul_le_mul_of_nonneg_left _ hg0
      have hJ0 : 0 ≤ diagonalIntegral
          (tensorLaw fun j => if j ∈ Xs then indepLaw c (m φ j) else N j) F := by
        apply energy_nonneg_of_positive c
        intro j
        by_cases hj : j ∈ Xs
        · simp only [hj, ↓reduceIte]
          exact positive_indepLaw c (hm φ hφ j hj)
        · simp only [hj, ↓reduceIte]
          exact hNpos j hj
      linarith [hDiagN φ hφ]
    have hsum := sum_le_sum hle
    rw [sum_const, nsmul_eq_mul] at hsum
    refine hsum.trans ?_
    have h4 : 0 ≤ (R.card : ℝ) * (g * CX) * Yμ :=
      mul_nonneg (mul_nonneg hn'.le (mul_nonneg hg0 (by linarith))) hY
    calc (R.card : ℝ) * (g * ((Bf + z₃) * CX * Yμ)) = (Bf + z₃) * (R.card * (g * CX) * Yμ) := by
          ring
      _ ≤ (Bf - 0 + (z₃ + z₄ + ea)) * (R.card * (g * CX) * Yμ) :=
          mul_le_mul_of_nonneg_right (by linarith) h4
      _ = (Bf - 0 + (z₃ + z₄ + ea)) * (R.card * (g * CX)) * Yμ := by ring

end Sarkozy.Variance
