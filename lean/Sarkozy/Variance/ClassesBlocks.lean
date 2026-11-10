module

public import Sarkozy.Variance.GainFlat
public import Sarkozy.Variance.RestorationBlocks
public import Sarkozy.Variance.RestorationVarianceBlocks

/-!
# The aligned fold class with each block its own factor (`cor:var-classes`(i))

`paper/sections/22_variance.tex`, `cor:var-classes`(i), as a composition in the blocks-as-factors
form: the pointwise restoration (`restoration_pointwise_blocks`, at the fold chamber `ϑ`) gives
(Res) for the fold product `⊗_X Π_{F_j,𝔅}`, and `lem:var-gain`(a) (`var_gain_a_blocks`, at the
reserved cut `ι`) gives the product of the actual half marginals.

The fold record of a block is one measure seen at two cuts. At `ϑ` it is the diagonal copy
`Diag_ϑ(λ_𝔅)` of the record law (`lem:record:fold-identification`), and at `ι` it is a
nonnegative weight `w_𝔅` with actual half marginal `m_𝔅` and centred norm `κ_𝔅`
(`lem:record:old-f-marginal`(d), hypothesis). This is the hypothesis `hrec`.
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- **`cor:var-classes`(i), blocks as factors, with the pointwise restoration**: with
`l₀ = (1 + h - (1 + z) h C_X)/∏ M_𝔅`, `Y[⊗_X J_ι(m) ⊗ O] ≥ (l̄_F - (z₁ + κ z₂)/(1 - κ)) C_X Y`
for `l̄_F = (l₀/C - κ)/(1 - κ)`, where `z₁ = 0`. -/
theorem var_classes_fold_blocks (ϑ ι : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (Xs : Finset J) (hOϑ : ∀ j, j ∉ Xs → ϑ.Positive (O j)) (hOι : ∀ j, j ∉ Xs → ι.Positive (O j))
    (F : (∀ b, X b) → ℝ) {Yμ : ℝ} (hYdef : diagonalIntegral (tensorLaw O) F = Yμ) (hY : 0 ≤ Yμ)
    -- the restoration data at `ϑ`
    (wr : ∀ j, (V → X j) → ℝ) (hwr : ∀ j ∈ Xs, ∀ z, 0 ≤ wr j z)
    (Mr : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (h : J → ℝ) (hh : ∀ j ∈ Xs, 0 ≤ h j)
    (hmix : ∀ j ∈ Xs, O j = (1 + h j)⁻¹ • (signedIntegral (wr j) + Mr j))
    {CX C z z₂ : ℝ} (hCX : 1 ≤ CX) (hC : CX ≤ C) (hz₂ : 0 ≤ z₂)
    (hE1M : diagonalIntegral (tensorLaw (onBlocks Xs (fun j => signedIntegral (wr j) + Mr j) O))
        F - diagonalIntegral (tensorLaw (onBlocks Xs (fun j => signedIntegral (wr j)) O)) F ≤
      (1 + z) * (∏ j ∈ Xs, (1 + h j) - 1) * CX * Yμ)
    (ν lam : ∀ j, (ϑ.Half → X j) → ℝ) (hplus : ∀ j ∈ Xs, plusMarginal ϑ (wr j) = ν j)
    (hminus : ∀ j ∈ Xs, minusMarginal ϑ (wr j) = ν j)
    (M : J → ℝ) (hMpos : 0 < ∏ j ∈ Xs, M j) (hA : ∀ j ∈ Xs, ∀ x, ν j x ≤ M j * lam j x)
    -- the fold records at `ι`
    (w : ∀ j, (V → X j) → ℝ) (m : ∀ j, (ι.Half → X j) → ℝ)
    (hrec : ∀ j ∈ Xs, signedIntegral (w j) = ϑ.diagonalLaw (lam j))
    (hw : ∀ j ∈ Xs, ∀ z, 0 ≤ w j z) (hp : ∀ j ∈ Xs, plusMarginal ι (w j) = m j)
    (hn : ∀ j ∈ Xs, minusMarginal ι (w j) = m j)
    (ht : ∀ j ∈ Xs, ∀ G H : (ι.Half → X j) → ℝ,
      ι.form (signedIntegral (w j)) G H = ι.form (signedIntegral (w j)) H G)
    (hmpos : ∀ j ∈ Xs, 0 < ∑ x, m j x) (κj : J → ℝ)
    (hcen : ∀ j ∈ Xs, CentredNormLe ι (signedIntegral (w j)) (m j) (κj j))
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hκ : ∀ j ∈ Xs, κj j ≤ κ)
    (hE1 : diagonalIntegral (tensorLaw (diagFam ι O Xs Xs m)) F ≤ (1 + z₂) * CX * Yμ) :
    (gainBar ((1 + (∏ j ∈ Xs, (1 + h j) - 1) - (1 + z) * (∏ j ∈ Xs, (1 + h j) - 1) * CX) /
        ∏ j ∈ Xs, M j) C κ - (0 + κ * z₂) / (1 - κ)) * CX * Yμ ≤
      diagonalIntegral (tensorLaw (recFam ι O Xs ∅ w m)) F := by
  have hres := restoration_pointwise_blocks ϑ O Xs hOϑ F hYdef wr hwr Mr h hh hmix hE1M ν lam
    hplus hminus M hA
  -- the fold product at `ι` is the record product at `ϑ`
  have hfam : recFam ι O Xs Xs w m = onBlocks Xs (fun j => ϑ.diagonalLaw (lam j)) O := by
    funext j
    by_cases hj : j ∈ Xs
    · simp only [recFam, onBlocks, hj, ↓reduceIte]
      exact hrec j hj
    · simp only [recFam, onBlocks, hj, ↓reduceIte]
  have hRes : ((1 + (∏ j ∈ Xs, (1 + h j) - 1) - (1 + z) * (∏ j ∈ Xs, (1 + h j) - 1) * CX) /
      ∏ j ∈ Xs, M j - 0) * Yμ ≤
      (∑ _φ ∈ (univ : Finset Unit), diagonalIntegral (tensorLaw (recFam ι O Xs Xs w m)) F) /
        (univ : Finset Unit).card := by
    simp only [sum_const, card_univ, Fintype.card_unit, one_smul, Nat.cast_one, div_one,
      sub_zero]
    rw [hfam, div_mul_eq_mul_div, div_le_iff₀ hMpos]
    linarith
  have ha := var_gain_a_blocks ι O Xs hOι F (univ : Finset Unit) univ_nonempty (fun _ => w)
    (fun _ => m) (fun _ _ => hw) (fun _ _ => hp) (fun _ _ => hn) (fun _ _ => ht)
    (fun _ _ => hmpos) (fun _ => κj) (fun _ _ => hcen) hκ0 hκ1 (fun _ _ => hκ) hY hCX hC le_rfl
    hz₂ hRes (fun _ _ => hE1)
  simpa using ha

/-- **`cor:var-classes`(i), blocks as factors, with the bounded-variance restoration**:
`restoration_variance_blocks` at the fold chamber `ϑ` gives (Res) with
`l₀ = branchVar l' C' χ_X`, `l' = 1 + h - (1 + z) h C_X`, and `var_gain_a_blocks` at `ι` gives
`Y[⊗_X J_ι(m) ⊗ O] ≥ (l̄_F - κ z₂/(1 - κ)) C_X Y` with `l̄_F = (l₀/C - κ)/(1 - κ)`. -/
theorem var_classes_fold_blocks_variance (ϑ ι : ReflectionCut V)
    (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (Xs : Finset J) (hOϑ : ∀ j, j ∉ Xs → ϑ.Positive (O j))
    (hOι : ∀ j, j ∉ Xs → ι.Positive (O j)) (F : (∀ b, X b) → ℝ) {Yμ : ℝ}
    (hYdef : diagonalIntegral (tensorLaw O) F = Yμ) (hY : 0 < Yμ)
    -- the restoration data at `ϑ`
    (wr : ∀ j, (V → X j) → ℝ) (hwr : ∀ j ∈ Xs, ∀ z, 0 ≤ wr j z)
    (Mr : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (h : J → ℝ) (hh : ∀ j ∈ Xs, 0 ≤ h j)
    (hmix : ∀ j ∈ Xs, O j = (1 + h j)⁻¹ • (signedIntegral (wr j) + Mr j)) {CX C z z₂ : ℝ}
    (hCX : 1 ≤ CX) (hC : CX ≤ C) (hz₂ : 0 ≤ z₂)
    (hE1M : diagonalIntegral (tensorLaw (onBlocks Xs (fun j => signedIntegral (wr j) + Mr j) O))
        F - diagonalIntegral (tensorLaw (onBlocks Xs (fun j => signedIntegral (wr j)) O)) F ≤
      (1 + z) * (∏ j ∈ Xs, (1 + h j) - 1) * CX * Yμ)
    (ν lam : ∀ j, (ϑ.Half → X j) → ℝ) (hplus : ∀ j ∈ Xs, plusMarginal ϑ (wr j) = ν j)
    (hminus : ∀ j ∈ Xs, minusMarginal ϑ (wr j) = ν j) (hlam0 : ∀ j ∈ Xs, ∀ x, 0 ≤ lam j x)
    (hν1 : ∀ j ∈ Xs, ∑ x, ν j x = 1) (hlam1 : ∀ j ∈ Xs, ∑ x, lam j x = 1)
    (hac : ∀ j ∈ Xs, ∀ x, lam j x = 0 → ν j x = 0) (χ : J → ℝ)
    (hχ : ∀ j ∈ Xs, ∑ x, (ν j x - lam j x) ^ 2 / lam j x ≤ χ j) {χX : ℝ}
    (hχX : ∏ j ∈ Xs, (1 + χ j) - 1 ≤ χX)
    (o : ∀ j, (ϑ.Half → X j) → (ϑ.Half → X j) → ℝ) (ho : ∀ j ∈ Xs, ∀ z y, 0 ≤ o j z y)
    (hνo : ∀ j ∈ Xs, ∀ y, ν j y = ∑ x, ν j x * o j x y)
    (hlamo : ∀ j ∈ Xs, ∀ y, lam j y = ∑ x, lam j x * o j x y) (i₀ : ∀ j, ϑ.Half → X j)
    {C' : ℝ}
    (hE1o : ∀ f : (∀ j, ϑ.Half → X j),
      diagonalIntegral (tensorLaw (onBlocks Xs (fun j => ϑ.diagonalLaw (o j (f j))) O)) F ≤
        C' * Yμ)
    (hl' : 0 < 1 + (∏ j ∈ Xs, (1 + h j) - 1) - (1 + z) * (∏ j ∈ Xs, (1 + h j) - 1) * CX)
    -- the fold records at `ι`
    (w : ∀ j, (V → X j) → ℝ) (m : ∀ j, (ι.Half → X j) → ℝ)
    (hrec : ∀ j ∈ Xs, signedIntegral (w j) = ϑ.diagonalLaw (lam j))
    (hw : ∀ j ∈ Xs, ∀ z, 0 ≤ w j z) (hp : ∀ j ∈ Xs, plusMarginal ι (w j) = m j)
    (hn : ∀ j ∈ Xs, minusMarginal ι (w j) = m j)
    (ht : ∀ j ∈ Xs, ∀ G H : (ι.Half → X j) → ℝ,
      ι.form (signedIntegral (w j)) G H = ι.form (signedIntegral (w j)) H G)
    (hmpos : ∀ j ∈ Xs, 0 < ∑ x, m j x) (κj : J → ℝ)
    (hcen : ∀ j ∈ Xs, CentredNormLe ι (signedIntegral (w j)) (m j) (κj j))
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hκ : ∀ j ∈ Xs, κj j ≤ κ)
    (hE1 : diagonalIntegral (tensorLaw (diagFam ι O Xs Xs m)) F ≤ (1 + z₂) * CX * Yμ) :
    (gainBar (branchVar (1 + (∏ j ∈ Xs, (1 + h j) - 1) -
        (1 + z) * (∏ j ∈ Xs, (1 + h j) - 1) * CX) C' χX) C κ - (0 + κ * z₂) / (1 - κ)) *
        CX * Yμ ≤
      diagonalIntegral (tensorLaw (recFam ι O Xs ∅ w m)) F := by
  have hres := restoration_variance_blocks ϑ O Xs hOϑ F hYdef hY wr hwr Mr h hh hmix hE1M ν lam
    hplus hminus hlam0 hν1 hlam1 hac χ hχ hχX o ho hνo hlamo i₀ hE1o hl'
  have hfam : recFam ι O Xs Xs w m = onBlocks Xs (fun j => ϑ.diagonalLaw (lam j)) O := by
    funext j
    by_cases hj : j ∈ Xs
    · simp only [recFam, onBlocks, hj, ↓reduceIte]
      exact hrec j hj
    · simp only [recFam, onBlocks, hj, ↓reduceIte]
  have hRes : (branchVar (1 + (∏ j ∈ Xs, (1 + h j) - 1) -
      (1 + z) * (∏ j ∈ Xs, (1 + h j) - 1) * CX) C' χX - 0) * Yμ ≤
      (∑ _φ ∈ (univ : Finset Unit), diagonalIntegral (tensorLaw (recFam ι O Xs Xs w m)) F) /
        (univ : Finset Unit).card := by
    simp only [sum_const, card_univ, Fintype.card_unit, one_smul, Nat.cast_one, div_one,
      sub_zero]
    rw [hfam]
    exact hres
  have ha := var_gain_a_blocks ι O Xs hOι F (univ : Finset Unit) univ_nonempty (fun _ => w)
    (fun _ => m) (fun _ _ => hw) (fun _ _ => hp) (fun _ _ => hn) (fun _ _ => ht)
    (fun _ _ => hmpos) (fun _ => κj) (fun _ _ => hcen) hκ0 hκ1 (fun _ _ => hκ) hY.le hCX hC
    le_rfl hz₂ hRes (fun _ _ => hE1)
  simpa using ha

end Sarkozy.Variance
