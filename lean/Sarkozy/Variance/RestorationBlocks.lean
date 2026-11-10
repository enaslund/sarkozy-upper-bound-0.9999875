module

public import Sarkozy.Variance.Exterior

/-!
# Restoration with each block its own factor: the pointwise branch

`paper/sections/22_variance.tex`, `lem:record:restoration`, steps (C), (B) and the pointwise
expression `l/M_X`, for a selected set `X` of blocks that are separate factors of the product law
(`Xs : Finset J`). The one-sided and bounded-variance branches are in `Restoration.lean`, for
`X` as one factor.

**Setting.** `c` is the fold chamber `ϑ_{2j}`. On a block `𝔅 ∈ X` the reference is
`μ_𝔅 = (1 + h_𝔅)⁻¹(Π^rt_𝔅 + 𝓜_𝔅)` (`hmix`); the root `Π^rt_𝔅` is a nonnegative weight `w_𝔅`
coupling two copies of its half law `ν_𝔅` (`hplus`, `hminus`); the record is `Diag_c(λ_𝔅)`; and
hypothesis (A) is `ν_𝔅 ≤ M_𝔅 λ_𝔅`. Off `X` the factors `O_b` are positive at `c`. (E1) for the
nonroot part of `⊗_X(Π^rt + 𝓜)` is the hypothesis `hE1M`, with mass `h = ∏(1 + h_𝔅) - 1`.

**Conclusion** (`restoration_pointwise_blocks`):
`(1 + h - (1 + z) h C_X) Y ≤ ∏_X M_𝔅 · Y[⊗_X Diag(λ) ⊗ O]`, that is
`Y[Π_X] ≥ (1 + h - (1 + z) h C_X)/M_X · Y` for `M_X = ∏ M_𝔅 > 0`; with `h ≤ h_X`, `C_X ≤ C` and
`1 ≤ C_X` the numerator is at least `l - z h_X C`, `l = 1 - (C - 1)h_X`, as in `restoration`.
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- The family equal to `A` on `Xs` and to `O` elsewhere. -/
def onBlocks (Xs : Finset J) (A O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) :
    ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ :=
  fun j => if j ∈ Xs then A j else O j

/-- **`lem:record:restoration`, steps (C), (B) and the pointwise branch, blocks as factors.** -/
theorem restoration_pointwise_blocks (c : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (Xs : Finset J) (hO : ∀ j, j ∉ Xs → c.Positive (O j)) (F : (∀ b, X b) → ℝ) {Yμ : ℝ}
    (hYdef : diagonalIntegral (tensorLaw O) F = Yμ)
    (w : ∀ j, (V → X j) → ℝ) (hw : ∀ j ∈ Xs, ∀ z, 0 ≤ w j z)
    (Mr : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (h : J → ℝ) (hh : ∀ j ∈ Xs, 0 ≤ h j)
    (hmix : ∀ j ∈ Xs, O j = (1 + h j)⁻¹ • (signedIntegral (w j) + Mr j))
    {CX z : ℝ}
    (hE1M : diagonalIntegral (tensorLaw (onBlocks Xs (fun j => signedIntegral (w j) + Mr j) O)) F
        - diagonalIntegral (tensorLaw (onBlocks Xs (fun j => signedIntegral (w j)) O)) F ≤
      (1 + z) * (∏ j ∈ Xs, (1 + h j) - 1) * CX * Yμ)
    (ν lam : ∀ j, (c.Half → X j) → ℝ) (hplus : ∀ j ∈ Xs, plusMarginal c (w j) = ν j)
    (hminus : ∀ j ∈ Xs, minusMarginal c (w j) = ν j)
    (M : J → ℝ) (hA : ∀ j ∈ Xs, ∀ x, ν j x ≤ M j * lam j x) :
    (1 + (∏ j ∈ Xs, (1 + h j) - 1) - (1 + z) * (∏ j ∈ Xs, (1 + h j) - 1) * CX) * Yμ ≤
      (∏ j ∈ Xs, M j) *
        diagonalIntegral (tensorLaw (onBlocks Xs (fun j => c.diagonalLaw (lam j)) O)) F := by
  set H := ∏ j ∈ Xs, (1 + h j) with hH
  have hHpos : 0 < H := prod_pos fun j hj => by linarith [hh j hj]
  have hν0 : ∀ j ∈ Xs, ∀ x, 0 ≤ ν j x := fun j hj x =>
    hplus j hj ▸ plusMarginal_nonneg c (hw j hj) x
  -- (C): `Y = H⁻¹ Y[⊗_X (Π^rt + 𝓜) ⊗ O]`
  have hO_eq : O = fun j => (if j ∈ Xs then (1 + h j)⁻¹ else 1) •
      onBlocks Xs (fun j => signedIntegral (w j) + Mr j) O j := by
    funext j
    by_cases hj : j ∈ Xs
    · simp only [onBlocks, hj, ↓reduceIte]
      exact hmix j hj
    · simp only [onBlocks, hj, ↓reduceIte, one_smul]
  have hY1 : Yμ = (∏ j ∈ Xs, (1 + h j))⁻¹ *
      diagonalIntegral (tensorLaw (onBlocks Xs (fun j => signedIntegral (w j) + Mr j) O)) F := by
    rw [← hYdef]
    conv_lhs => rw [hO_eq]
    rw [tensorLaw_smul]
    have hprod : ∏ j, (if j ∈ Xs then (1 + h j)⁻¹ else 1) = (∏ j ∈ Xs, (1 + h j))⁻¹ := by
      rw [prod_ite, prod_const_one, mul_one, ← prod_inv_distrib]
      congr 1
      ext j
      simp
    rw [hprod]
    rfl
  have hfull : diagonalIntegral (tensorLaw (onBlocks Xs (fun j => signedIntegral (w j) + Mr j) O))
      F = H * Yμ := by
    rw [hY1, ← hH]
    field_simp
  -- the root energy
  have hroot : (1 + (H - 1) - (1 + z) * (H - 1) * CX) * Yμ ≤
      diagonalIntegral (tensorLaw (onBlocks Xs (fun j => signedIntegral (w j)) O)) F := by
    have := hE1M
    rw [hfull] at this
    nlinarith
  -- (B): contraction, `Y[⊗_X Π^rt] ≤ Y[⊗_X Diag(ν)]`
  have hcontr : diagonalIntegral (tensorLaw (onBlocks Xs (fun j => signedIntegral (w j)) O)) F ≤
      diagonalIntegral (tensorLaw (onBlocks Xs (fun j => c.diagonalLaw (ν j)) O)) F := by
    have hpos : ∀ j, c.Positive (onBlocks Xs (fun j => c.diagonalLaw (ν j)) O j) := by
      intro j
      by_cases hj : j ∈ Xs
      · simp only [onBlocks, hj, ↓reduceIte]
        exact c.diagonalLaw_positive (hν0 j hj)
      · simp only [onBlocks, hj, ↓reduceIte]
        exact hO j hj
    have hbr := abs_energy_le_of_brackets (c := c)
      (κ := onBlocks Xs (fun j => c.diagonalLaw (ν j)) O)
      (ζ := onBlocks Xs (fun j => signedIntegral (w j)) O)
      (κ' := onBlocks Xs (fun j => c.diagonalLaw (ν j)) O) (fun j => by
        by_cases hj : j ∈ Xs
        · simp only [onBlocks, hj, ↓reduceIte]
          have hb := bracket_diagonal_marginals c (hw j hj)
          rw [hplus j hj, hminus j hj] at hb
          exact hb
        · simp only [onBlocks, hj, ↓reduceIte]
          exact (hO j hj).bracket_self) F
    have hnn := (ReflectionCut.Positive.tensor hpos).diagonal_nonneg F
    rw [Real.mul_self_sqrt hnn] at hbr
    exact (le_abs_self _).trans hbr
  -- (P2) for products: `Y[⊗_X Diag(ν)] ≤ ∏ M Y[⊗_X Diag(λ)]`
  have hP2 : diagonalIntegral (tensorLaw (onBlocks Xs (fun j => c.diagonalLaw (ν j)) O)) F ≤
      (∏ j ∈ Xs, M j) *
        diagonalIntegral (tensorLaw (onBlocks Xs (fun j => c.diagonalLaw (lam j)) O)) F := by
    have hle := energy_le_of_orders c
      (fun j => (if j ∈ Xs then M j else 1) • onBlocks Xs (fun j => c.diagonalLaw (lam j)) O j)
      (onBlocks Xs (fun j => c.diagonalLaw (ν j)) O)
      (fun j => by
        by_cases hj : j ∈ Xs
        · simp only [onBlocks, hj, ↓reduceIte]
          exact c.diagonalLaw_positive (hν0 j hj)
        · simp only [onBlocks, hj, ↓reduceIte]
          exact hO j hj)
      (fun j => by
        by_cases hj : j ∈ Xs
        · simp only [onBlocks, hj, ↓reduceIte]
          have e : M j • c.diagonalLaw (lam j) - c.diagonalLaw (ν j) =
              c.diagonalLaw (fun x => M j * lam j x - ν j x) := by
            apply LinearMap.ext
            intro f
            change M j * (∑ x, lam j x * f (c.join x x)) - ∑ x, ν j x * f (c.join x x) =
              ∑ x, (M j * lam j x - ν j x) * f (c.join x x)
            rw [mul_sum, ← sum_sub_distrib]
            exact sum_congr rfl fun x _ => by ring
          rw [e]
          exact c.diagonalLaw_positive fun x => by linarith [hA j hj x]
        · simp only [onBlocks, hj, ↓reduceIte, one_smul, sub_self]
          exact positive_zero c) F
    rw [tensorLaw_smul] at hle
    have hprod : ∏ j, (if j ∈ Xs then M j else 1) = ∏ j ∈ Xs, M j := by
      rw [prod_ite, prod_const_one, mul_one]
      congr 1
      ext j
      simp
    rw [hprod] at hle
    exact hle
  linarith

end Sarkozy.Variance
