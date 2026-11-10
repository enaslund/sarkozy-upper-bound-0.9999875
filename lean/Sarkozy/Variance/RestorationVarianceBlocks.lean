module

public import Sarkozy.Variance.Restoration
public import Sarkozy.Variance.RestorationBlocks

/-!
# Restoration with each block its own factor: the bounded-variance branch

`paper/sections/22_variance.tex`, `lem:record:restoration`, the third (bounded-variance)
expression `branchVar l C χ_X` of `l₀`, for a selected set `X` of blocks that are separate
factors (`Xs : Finset J`). Steps (C), (B) are those of `restoration_pointwise_blocks`.

**The product orbit decomposition.** On each block the half laws decompose over the orbit laws,
`ρ_𝔅 = ∑_z ρ_𝔅(z) o_𝔅(z)` (`orbit_decomposition` for translation-invariant laws). Then
`Y[⊗_X Diag(ρ) ⊗ O] = ∑_f P_ρ(f) e(f)` over the product configurations `f`
(`energy_onBlocks_decomp`), with `P_ρ(f) = ∏_𝔅 ρ_𝔅(f_𝔅)` and
`e(f) = Y[⊗_X Diag(o_𝔅(f_𝔅)) ⊗ O]`. (E1) bounds `e(f) ≤ (1 + z₂) C_X Y`.

**The product chi-square.** `χ²(⊗ν ‖ ⊗λ) = ∏(1 + χ²(ν_𝔅 ‖ λ_𝔅)) - 1`, also when `λ_𝔅` vanishes
off its support (`ν_𝔅 ≪ λ_𝔅`), with the convention `x/0 = 0` (`prodLaw_chiSq_le`).

**Conclusion** (`restoration_variance_blocks`): for `l' = 1 + h - (1 + z) h C_X > 0`, `C' ≥
(1 + z₂) C_X` and `χ_X ≥ ∏(1 + χ_𝔅) - 1`, `Y[⊗_X Diag(λ) ⊗ O] ≥ branchVar l' C' χ_X · Y`.
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

/-! ### The scalar bounded-variance step on a finite set -/

section Scalar

variable {S : Type*} [Fintype S]

/-- `∑ (ν - λ)²/λ = ∑ ν²/λ - 1` for laws with `ν ≪ λ` (convention `x/0 = 0`). -/
theorem chiSq_eq_sum_sq_div {ν lam : S → ℝ} (hac : ∀ x, lam x = 0 → ν x = 0)
    (hν : ∑ x, ν x = 1) (hlam : ∑ x, lam x = 1) :
    ∑ x, (ν x - lam x) ^ 2 / lam x = ∑ x, ν x ^ 2 / lam x - 1 := by
  have hpt : ∀ x, (ν x - lam x) ^ 2 / lam x = ν x ^ 2 / lam x - 2 * ν x + lam x := by
    intro x
    by_cases h0 : lam x = 0
    · simp [h0, hac x h0]
    · field_simp
      ring
  simp_rw [hpt]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, hν, hlam]
  ring

/-- **The bounded-variance step**: for laws `ν ≪ λ` with `∑ (ν - λ)²/λ ≤ χ`, and energies
`0 ≤ e ≤ C' Y` with `l' Y ≤ ∑ ν e`, `l' > 0`, `Y > 0`: `branchVar l' C' χ · Y ≤ ∑ λ e`. -/
theorem variance_branch_scalar {ν lam e : S → ℝ} {χ Yμ l' C' : ℝ} (hlam0 : ∀ x, 0 ≤ lam x)
    (hlam : ∑ x, lam x = 1) (hν : ∑ x, ν x = 1) (hac : ∀ x, lam x = 0 → ν x = 0)
    (hχ : ∑ x, (ν x - lam x) ^ 2 / lam x ≤ χ) (he0 : ∀ x, 0 ≤ e x) (heC : ∀ x, e x ≤ C' * Yμ)
    (hY : 0 < Yμ) (hl' : 0 < l') (hmain : l' * Yμ ≤ ∑ x, ν x * e x) :
    branchVar l' C' χ * Yμ ≤ ∑ x, lam x * e x := by
  have hχ0 : 0 ≤ χ := le_trans (sum_nonneg fun x _ => div_nonneg (sq_nonneg _) (hlam0 x)) hχ
  set ebar := ∑ x, lam x * e x with hebar
  have hebar0 : 0 ≤ ebar := sum_nonneg fun x _ => mul_nonneg (hlam0 x) (he0 x)
  have hebarC : ebar ≤ C' * Yμ := by
    have : ebar ≤ ∑ x, lam x * (C' * Yμ) :=
      sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (heC x) (hlam0 x)
    rw [← sum_mul, hlam, one_mul] at this
    exact this
  have hzero : ∑ x, (ν x - lam x) = 0 := by rw [sum_sub_distrib, hν, hlam, sub_self]
  have hcen : ∑ x, (ν x - lam x) * e x = ∑ x, (ν x - lam x) * (e x - ebar) := by
    have : ∑ x, (ν x - lam x) * (e x - ebar) =
        ∑ x, (ν x - lam x) * e x - (∑ x, (ν x - lam x)) * ebar := by
      rw [sum_mul, ← sum_sub_distrib]
      exact sum_congr rfl fun x _ => by ring
    rw [this, hzero, zero_mul, sub_zero]
  have hcs := sum_sub_mul_le_sqrt (g := fun x => e x - ebar) hlam0 hac hχ
  have hvar : ∑ x, lam x * (e x - ebar) ^ 2 ≤ ebar * (C' * Yμ - ebar) := by
    have h1 : ∑ x, lam x * (e x - ebar) ^ 2 = ∑ x, lam x * e x ^ 2 - ebar ^ 2 := by
      have : ∀ x, lam x * (e x - ebar) ^ 2 =
          lam x * e x ^ 2 - 2 * ebar * (lam x * e x) + ebar ^ 2 * lam x := by
        intro x
        ring
      simp_rw [this]
      rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, hlam, ← hebar]
      ring
    have h2 : ∑ x, lam x * e x ^ 2 ≤ C' * Yμ * ebar := by
      rw [hebar, mul_sum]
      apply sum_le_sum
      intro x _
      have h5 : e x ^ 2 ≤ C' * Yμ * e x := by
        have := mul_le_mul_of_nonneg_left (heC x) (he0 x)
        rw [sq]
        linarith
      calc lam x * e x ^ 2 ≤ lam x * (C' * Yμ * e x) := mul_le_mul_of_nonneg_left h5 (hlam0 x)
        _ = C' * Yμ * (lam x * e x) := by ring
    rw [h1]
    have : ebar * (C' * Yμ - ebar) = C' * Yμ * ebar - ebar ^ 2 := by ring
    linarith
  have hbound : ∑ x, ν x * e x ≤ ebar + Real.sqrt (χ * (ebar * (C' * Yμ - ebar))) := by
    have h4 : ∑ x, ν x * e x - ebar ≤ Real.sqrt (χ * ∑ x, lam x * (e x - ebar) ^ 2) := by
      have : ∑ x, ν x * e x - ebar = ∑ x, (ν x - lam x) * e x := by
        rw [hebar, ← sum_sub_distrib]
        exact sum_congr rfl fun x _ => by ring
      rw [this, hcen]
      exact hcs
    have h3 : Real.sqrt (χ * ∑ x, lam x * (e x - ebar) ^ 2) ≤
        Real.sqrt (χ * (ebar * (C' * Yμ - ebar))) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hvar hχ0)
    linarith
  set x := ebar / Yμ with hx
  have hxY : ebar = x * Yμ := by rw [hx]; field_simp
  have hx0 : 0 ≤ x := div_nonneg hebar0 hY.le
  have hxC : x ≤ C' := by
    rw [hx, div_le_iff₀ hY]
    exact hebarC
  have hsqrt : Real.sqrt (χ * (ebar * (C' * Yμ - ebar))) =
      Real.sqrt (χ * x * (C' - x)) * Yμ := by
    rw [hxY]
    have : χ * (x * Yμ * (C' * Yμ - x * Yμ)) = (χ * x * (C' - x)) * Yμ ^ 2 := by ring
    rw [this, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hY.le]
  have hmain' : l' ≤ x + Real.sqrt (χ * x * (C' - x)) := by
    have := hmain.trans hbound
    rw [hsqrt, hxY] at this
    have h4 : l' * Yμ ≤ (x + Real.sqrt (χ * x * (C' - x))) * Yμ := by linarith
    exact le_of_mul_le_mul_right h4 hY
  have hbv := branchVar_le hl' hχ0 hx0 hxC hmain'
  rw [hxY]
  exact mul_le_mul_of_nonneg_right hbv hY.le

end Scalar

/-! ### Product laws -/

section ProductLaws

variable {J : Type*} [Fintype J] [DecidableEq J] {S : J → Type*} [∀ j, Fintype (S j)]
  [∀ j, DecidableEq (S j)]

/-- The product law: `ρ_j` on the blocks of `Xs`, the point mass at `i₀ j` elsewhere. -/
def prodLaw (Xs : Finset J) (ρ : ∀ j, S j → ℝ) (i₀ : ∀ j, S j) (f : ∀ j, S j) : ℝ :=
  ∏ j, (if j ∈ Xs then ρ j (f j) else if f j = i₀ j then 1 else 0)

omit [∀ j, Fintype (S j)] in
theorem prodLaw_nonneg (Xs : Finset J) {ρ : ∀ j, S j → ℝ} (hρ : ∀ j ∈ Xs, ∀ y, 0 ≤ ρ j y)
    (i₀ : ∀ j, S j) (f : ∀ j, S j) : 0 ≤ prodLaw Xs ρ i₀ f :=
  prod_nonneg fun j _ => by
    by_cases hj : j ∈ Xs
    · simp only [hj, ↓reduceIte]
      exact hρ j hj (f j)
    · simp only [hj, ↓reduceIte]
      split_ifs <;> norm_num

omit [∀ j, DecidableEq (S j)] in
/-- `∑_f ∏_j g_j(f_j) = ∏_j ∑_i g_j(i)`. -/
theorem sum_prod_eq (g : ∀ j, S j → ℝ) : ∑ f : (∀ j, S j), ∏ j, g j (f j) = ∏ j, ∑ i, g j i :=
  (Fintype.prod_sum g).symm

theorem prodLaw_sum (Xs : Finset J) {ρ : ∀ j, S j → ℝ} (hρ : ∀ j ∈ Xs, ∑ y, ρ j y = 1)
    (i₀ : ∀ j, S j) : ∑ f, prodLaw Xs ρ i₀ f = 1 := by
  unfold prodLaw
  rw [sum_prod_eq (fun j i => if j ∈ Xs then ρ j i else if i = i₀ j then 1 else 0)]
  apply prod_eq_one
  intro j _
  by_cases hj : j ∈ Xs
  · simp only [hj, ↓reduceIte]
    exact hρ j hj
  · simp [hj]

omit [∀ j, Fintype (S j)] in
theorem prodLaw_ac (Xs : Finset J) {ν lam : ∀ j, S j → ℝ}
    (hac : ∀ j ∈ Xs, ∀ y, lam j y = 0 → ν j y = 0) (i₀ : ∀ j, S j) (f : ∀ j, S j)
    (h0 : prodLaw Xs lam i₀ f = 0) : prodLaw Xs ν i₀ f = 0 := by
  unfold prodLaw at h0 ⊢
  obtain ⟨j, _, hj⟩ := prod_eq_zero_iff.mp h0
  apply prod_eq_zero (mem_univ j)
  by_cases hjX : j ∈ Xs
  · simp only [hjX, ↓reduceIte] at hj ⊢
    exact hac j hjX (f j) hj
  · simp only [hjX, ↓reduceIte] at hj ⊢
    split_ifs at hj ⊢ with h
    · norm_num at hj
    · rfl

/-- **The product chi-square**: `∑ (P_ν - P_λ)²/P_λ ≤ ∏_X (1 + χ_𝔅) - 1` when
`∑ (ν_𝔅 - λ_𝔅)²/λ_𝔅 ≤ χ_𝔅` and `ν_𝔅 ≪ λ_𝔅` are probabilities. -/
theorem prodLaw_chiSq_le (Xs : Finset J) {ν lam : ∀ j, S j → ℝ} (i₀ : ∀ j, S j)
    (hlam0 : ∀ j ∈ Xs, ∀ y, 0 ≤ lam j y) (hν1 : ∀ j ∈ Xs, ∑ y, ν j y = 1)
    (hlam1 : ∀ j ∈ Xs, ∑ y, lam j y = 1) (hac : ∀ j ∈ Xs, ∀ y, lam j y = 0 → ν j y = 0)
    (χ : J → ℝ) (hχ : ∀ j ∈ Xs, ∑ y, (ν j y - lam j y) ^ 2 / lam j y ≤ χ j) :
    ∑ f, (prodLaw Xs ν i₀ f - prodLaw Xs lam i₀ f) ^ 2 / prodLaw Xs lam i₀ f ≤
      ∏ j ∈ Xs, (1 + χ j) - 1 := by
  rw [chiSq_eq_sum_sq_div (prodLaw_ac Xs hac i₀) (prodLaw_sum Xs hν1 i₀) (prodLaw_sum Xs hlam1 i₀)]
  -- `P_ν²/P_λ = ∏ (ν²/λ)` (convention `x/0 = 0`)
  have hpt : ∀ f, prodLaw Xs ν i₀ f ^ 2 / prodLaw Xs lam i₀ f =
      ∏ j, (if j ∈ Xs then ν j (f j) ^ 2 / lam j (f j) else if f j = i₀ j then 1 else 0) := by
    intro f
    unfold prodLaw
    rw [← prod_pow, ← prod_div_distrib]
    refine prod_congr rfl fun j _ => ?_
    by_cases hj : j ∈ Xs
    · simp [hj]
    · by_cases h : f j = i₀ j <;> simp [hj, h]
  simp_rw [hpt]
  rw [sum_prod_eq (fun j i => if j ∈ Xs then ν j i ^ 2 / lam j i else if i = i₀ j then 1 else 0)]
  have hfac : ∀ j, ∑ i, (if j ∈ Xs then ν j i ^ 2 / lam j i else if i = i₀ j then 1 else 0) =
      if j ∈ Xs then ∑ i, ν j i ^ 2 / lam j i else 1 := by
    intro j
    by_cases hj : j ∈ Xs
    · simp [hj]
    · simp [hj]
  simp_rw [hfac]
  rw [prod_ite, prod_const_one, mul_one]
  have hfil : (univ.filter fun j => j ∈ Xs) = Xs := by ext j; simp
  rw [hfil]
  have hle : ∏ j ∈ Xs, ∑ i, ν j i ^ 2 / lam j i ≤ ∏ j ∈ Xs, (1 + χ j) := by
    apply prod_le_prod₀
    · intro j _
      exact sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hlam0 _ ‹_› i)
    · intro j hj
      have := chiSq_eq_sum_sq_div (hac j hj) (hν1 j hj) (hlam1 j hj)
      linarith [hχ j hj]
  linarith

end ProductLaws

/-! ### The energy decomposition and the restoration -/

section Energy

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- **The product orbit decomposition of the energy**: if on every block `ρ_𝔅 = ∑_z ρ_𝔅(z) o_𝔅(z)`,
then `Y[⊗_X Diag(ρ) ⊗ O] = ∑_f P_ρ(f) Y[⊗_X Diag(o(f)) ⊗ O]`. -/
theorem energy_onBlocks_decomp (c : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (Xs : Finset J) (F : (∀ b, X b) → ℝ) (ρ : ∀ j, (c.Half → X j) → ℝ)
    (o : ∀ j, (c.Half → X j) → (c.Half → X j) → ℝ)
    (hdec : ∀ j ∈ Xs, ∀ y, ρ j y = ∑ z, ρ j z * o j z y) (i₀ : ∀ j, c.Half → X j) :
    diagonalIntegral (tensorLaw (onBlocks Xs (fun j => c.diagonalLaw (ρ j)) O)) F =
      ∑ f : (∀ j, c.Half → X j), prodLaw Xs ρ i₀ f *
        diagonalIntegral (tensorLaw (onBlocks Xs (fun j => c.diagonalLaw (o j (f j))) O)) F := by
  have hfam : onBlocks Xs (fun j => c.diagonalLaw (ρ j)) O = fun j => ∑ i : c.Half → X j,
      (if j ∈ Xs then ρ j i else if i = i₀ j then 1 else 0) •
        (if j ∈ Xs then c.diagonalLaw (o j i) else O j) := by
    funext j
    by_cases hj : j ∈ Xs
    · simp only [onBlocks, hj, ↓reduceIte]
      exact diagonalLaw_decomp c (ρ j) (o j) (hdec j hj)
    · simp only [onBlocks, hj, ↓reduceIte, ite_smul, one_smul, zero_smul]
      rw [sum_ite_eq']
      simp
  rw [hfam, tensorLaw_sum, diagonalIntegral_sum]
  refine sum_congr rfl fun f _ => ?_
  rw [tensorLaw_smul]
  unfold prodLaw
  simp only [diagonalIntegral, multilinearIntegral, LinearMap.smul_apply, smul_eq_mul]
  rfl

/-- **`lem:record:restoration`, the bounded-variance branch, blocks as factors.** -/
theorem restoration_variance_blocks (c : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (Xs : Finset J) (hO : ∀ j, j ∉ Xs → c.Positive (O j)) (F : (∀ b, X b) → ℝ) {Yμ : ℝ}
    (hYdef : diagonalIntegral (tensorLaw O) F = Yμ) (hY : 0 < Yμ)
    (w : ∀ j, (V → X j) → ℝ) (hw : ∀ j ∈ Xs, ∀ z, 0 ≤ w j z)
    (Mr : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (h : J → ℝ) (hh : ∀ j ∈ Xs, 0 ≤ h j)
    (hmix : ∀ j ∈ Xs, O j = (1 + h j)⁻¹ • (signedIntegral (w j) + Mr j)) {CX z : ℝ}
    (hE1M : diagonalIntegral (tensorLaw (onBlocks Xs (fun j => signedIntegral (w j) + Mr j) O)) F
        - diagonalIntegral (tensorLaw (onBlocks Xs (fun j => signedIntegral (w j)) O)) F ≤
      (1 + z) * (∏ j ∈ Xs, (1 + h j) - 1) * CX * Yμ)
    (ν lam : ∀ j, (c.Half → X j) → ℝ) (hplus : ∀ j ∈ Xs, plusMarginal c (w j) = ν j)
    (hminus : ∀ j ∈ Xs, minusMarginal c (w j) = ν j) (hlam0 : ∀ j ∈ Xs, ∀ x, 0 ≤ lam j x)
    (hν1 : ∀ j ∈ Xs, ∑ x, ν j x = 1) (hlam1 : ∀ j ∈ Xs, ∑ x, lam j x = 1)
    (hac : ∀ j ∈ Xs, ∀ x, lam j x = 0 → ν j x = 0) (χ : J → ℝ)
    (hχ : ∀ j ∈ Xs, ∑ x, (ν j x - lam j x) ^ 2 / lam j x ≤ χ j) {χX : ℝ}
    (hχX : ∏ j ∈ Xs, (1 + χ j) - 1 ≤ χX)
    (o : ∀ j, (c.Half → X j) → (c.Half → X j) → ℝ) (ho : ∀ j ∈ Xs, ∀ z y, 0 ≤ o j z y)
    (hνo : ∀ j ∈ Xs, ∀ y, ν j y = ∑ x, ν j x * o j x y)
    (hlamo : ∀ j ∈ Xs, ∀ y, lam j y = ∑ x, lam j x * o j x y) (i₀ : ∀ j, c.Half → X j)
    {C' : ℝ}
    (hE1o : ∀ f : (∀ j, c.Half → X j),
      diagonalIntegral (tensorLaw (onBlocks Xs (fun j => c.diagonalLaw (o j (f j))) O)) F ≤
        C' * Yμ)
    (hl' : 0 < 1 + (∏ j ∈ Xs, (1 + h j) - 1) - (1 + z) * (∏ j ∈ Xs, (1 + h j) - 1) * CX) :
    branchVar (1 + (∏ j ∈ Xs, (1 + h j) - 1) - (1 + z) * (∏ j ∈ Xs, (1 + h j) - 1) * CX) C' χX *
        Yμ ≤
      diagonalIntegral (tensorLaw (onBlocks Xs (fun j => c.diagonalLaw (lam j)) O)) F := by
  set H := ∏ j ∈ Xs, (1 + h j) with hH
  have hν0 : ∀ j ∈ Xs, ∀ x, 0 ≤ ν j x := fun j hj x =>
    hplus j hj ▸ plusMarginal_nonneg c (hw j hj) x
  -- (C) and (B): `l' Y ≤ Y[⊗_X Diag(ν) ⊗ O]`
  have hO_eq : O = fun j => (if j ∈ Xs then (1 + h j)⁻¹ else 1) •
      onBlocks Xs (fun j => signedIntegral (w j) + Mr j) O j := by
    funext j
    by_cases hj : j ∈ Xs
    · simp only [onBlocks, hj, ↓reduceIte]
      exact hmix j hj
    · simp only [onBlocks, hj, ↓reduceIte, one_smul]
  have hHpos : 0 < H := prod_pos fun j hj => by linarith [hh j hj]
  have hfull : diagonalIntegral (tensorLaw (onBlocks Xs (fun j => signedIntegral (w j) + Mr j) O))
      F = H * Yμ := by
    have hY1 : Yμ = H⁻¹ *
        diagonalIntegral (tensorLaw (onBlocks Xs (fun j => signedIntegral (w j) + Mr j) O)) F := by
      rw [← hYdef]
      conv_lhs => rw [hO_eq]
      rw [tensorLaw_smul]
      have hprod : ∏ j, (if j ∈ Xs then (1 + h j)⁻¹ else 1) = H⁻¹ := by
        rw [prod_ite, prod_const_one, mul_one, hH, ← prod_inv_distrib]
        congr 1
        ext j
        simp
      rw [hprod]
      rfl
    rw [hY1]
    field_simp
  have hroot : (1 + (H - 1) - (1 + z) * (H - 1) * CX) * Yμ ≤
      diagonalIntegral (tensorLaw (onBlocks Xs (fun j => signedIntegral (w j)) O)) F := by
    have := hE1M
    rw [hfull] at this
    nlinarith
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
  -- the decompositions and the scalar step
  have hdnu := energy_onBlocks_decomp c O Xs F ν o hνo i₀
  have hdlam := energy_onBlocks_decomp c O Xs F lam o hlamo i₀
  have he0 : ∀ f : (∀ j, c.Half → X j), 0 ≤
      diagonalIntegral (tensorLaw (onBlocks Xs (fun j => c.diagonalLaw (o j (f j))) O)) F := by
    intro f
    have hpos : ∀ j, c.Positive (onBlocks Xs (fun j => c.diagonalLaw (o j (f j))) O j) := by
      intro j
      by_cases hj : j ∈ Xs
      · simp only [onBlocks, hj, ↓reduceIte]
        exact c.diagonalLaw_positive (ho j hj (f j))
      · simp only [onBlocks, hj, ↓reduceIte]
        exact hO j hj
    exact (ReflectionCut.Positive.tensor hpos).diagonal_nonneg F
  have hmain : (1 + (H - 1) - (1 + z) * (H - 1) * CX) * Yμ ≤
      ∑ f, prodLaw Xs ν i₀ f *
        diagonalIntegral (tensorLaw (onBlocks Xs (fun j => c.diagonalLaw (o j (f j))) O)) F := by
    rw [← hdnu]
    exact hroot.trans hcontr
  have hres := variance_branch_scalar (ν := prodLaw Xs ν i₀) (lam := prodLaw Xs lam i₀)
    (e := fun f => diagonalIntegral
      (tensorLaw (onBlocks Xs (fun j => c.diagonalLaw (o j (f j))) O)) F)
    (prodLaw_nonneg Xs hlam0 i₀) (prodLaw_sum Xs hlam1 i₀) (prodLaw_sum Xs hν1 i₀)
    (prodLaw_ac Xs hac i₀) ((prodLaw_chiSq_le Xs i₀ hlam0 hν1 hlam1 hac χ hχ).trans hχX) he0
    hE1o hY hl' hmain
  rw [hdlam]
  exact hres

end Energy

end Sarkozy.Variance
