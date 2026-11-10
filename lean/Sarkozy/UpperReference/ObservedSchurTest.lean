module

public import Sarkozy.UpperReference.ObservedSchurFull

/-!
# `prop:observed-caps`: the full Schur test `36I - B_⋆B_⋆ᵀ ± 6iD ⪰ 0`, assembled

The exact integer identities of `ObservedSchurFull.lean` (`gram_eq`, `gram_sos`, `Dfull_sq`,
`pMat_sos`) carried to complex matrices, and the sum-of-squares certificate of the test
(`full_schur_test`): `36I - B_⋆B_⋆ᵀ + 6σD = (15I - B_⋆B_⋆ᵀ) + 6(αI + σD) + (21 - 6α)I`
(`σ = ±i`, `α = 17321/5000`), each term positive semidefinite.
-/

@[expose] public section

open scoped Matrix ComplexOrder ComplexConjugate
open Matrix

namespace Sarkozy.UpperReference.Observed

/-- An integer matrix as a complex matrix. -/
noncomputable def toC {m n : Type*} (M : Matrix m n ℤ) : Matrix m n ℂ :=
  M.map (Int.castRingHom ℂ)

theorem toC_mul {l m n : Type*} [Fintype m] (M : Matrix l m ℤ) (N : Matrix m n ℤ) :
    toC (M * N) = toC M * toC N :=
  Matrix.map_mul

theorem toC_conjTranspose {m n : Type*} (M : Matrix m n ℤ) : (toC M)ᴴ = toC M.transpose := by
  ext a b
  simp [toC, conjTranspose_apply]

theorem toC_sub {m n : Type*} (M N : Matrix m n ℤ) : toC (M - N) = toC M - toC N := by
  ext a b
  simp [toC]

theorem toC_neg {m n : Type*} (M : Matrix m n ℤ) : toC (-M) = -toC M := by
  ext a b
  simp [toC]

theorem toC_nsmul {m n : Type*} (k : ℕ) (M : Matrix m n ℤ) :
    toC (k • M) = ((k : ℝ) : ℂ) • toC M := by
  ext a b
  simp [toC]

theorem toC_one : toC (1 : Matrix Half Half ℤ) = 1 := by
  ext a b
  simp only [toC, map_apply, one_apply]
  split_ifs <;> simp

theorem toC_add {m n : Type*} (M N : Matrix m n ℤ) : toC (M + N) = toC M + toC N := by
  ext a b
  simp [toC]

/-- `15 I - B_⋆B_⋆ᵀ ⪰ 0`. -/
theorem gram_le_15 : ((((15 : ℝ) : ℂ) • (1 : Matrix Half Half ℂ)) - toC gramMat).PosSemidef := by
  have h := congrArg toC gram_sos
  rw [toC_mul, ← toC_conjTranspose, toC_nsmul, toC_sub, toC_nsmul, toC_one] at h
  have hpsd := Matrix.posSemidef_conjTranspose_mul_self (toC nMat)
  rw [h] at hpsd
  have h2 := hpsd.smul ((RCLike.ofReal_nonneg (K := ℂ)).mpr (by norm_num : (0 : ℝ) ≤ 1 / 2))
  rw [smul_smul] at h2
  convert h2 using 2
  push_cast
  norm_num

/-- `12 I - P ⪰ 0` (`P = DᵀD`, `‖D‖² ≤ 12`). -/
theorem pMat_le_12 : ((((12 : ℝ) : ℂ) • (1 : Matrix Half Half ℂ)) - toC pMat).PosSemidef := by
  have h := congrArg toC pMat_sos
  rw [toC_add, toC_nsmul, toC_nsmul, toC_mul, toC_mul, toC_nsmul, toC_sub, toC_nsmul,
    toC_one] at h
  have hA : (toC aMat)ᴴ = toC aMat := by rw [toC_conjTranspose, aMat_symm]
  have hB : (toC bMat)ᴴ = toC bMat := by rw [toC_conjTranspose, bMat_symm]
  have hpA := Matrix.posSemidef_conjTranspose_mul_self (toC aMat)
  have hpB := Matrix.posSemidef_conjTranspose_mul_self (toC bMat)
  rw [hA] at hpA
  rw [hB] at hpB
  have hsum := (hpA.smul ((RCLike.ofReal_nonneg (K := ℂ)).mpr (by norm_num : (0 : ℝ) ≤ 3))).add
    (hpB.smul ((RCLike.ofReal_nonneg (K := ℂ)).mpr (by norm_num : (0 : ℝ) ≤ 4)))
  push_cast at h hsum
  rw [h] at hsum
  have h2 := hsum.smul ((RCLike.ofReal_nonneg (K := ℂ)).mpr (by norm_num : (0 : ℝ) ≤ 1 / 324))
  rw [smul_smul] at h2
  convert h2 using 2
  push_cast
  norm_num

/-- `D` as a complex matrix is antisymmetric: `Dᴴ = -D`. -/
theorem Dfull_conjTranspose : (toC Dfull)ᴴ = -toC Dfull := by
  rw [toC_conjTranspose, ← toC_neg]
  congr 1
  ext a b
  simp only [transpose_apply, neg_apply]
  exact Dfull_anti a b

/-- **`αI - σD ⪰ 0`** for `σ = ±i` and `α = 17321/5000 ≥ 2√3`. -/
theorem alpha_sub_Y (σ : ℂ) (hσ : σ = Complex.I ∨ σ = -Complex.I) :
    ((((17321 / 5000 : ℝ) : ℂ) • (1 : Matrix Half Half ℂ)) - σ • toC Dfull).PosSemidef := by
  have hσ2 : σ * σ = -1 := by
    rcases hσ with h | h <;> rw [h]
    · exact Complex.I_mul_I
    · rw [neg_mul_neg, Complex.I_mul_I]
  have hσc : -(star σ) = σ := by
    rcases hσ with h | h <;> rw [h]
    · rw [Complex.star_def, Complex.conj_I, neg_neg]
    · rw [Complex.star_def, map_neg, Complex.conj_I, neg_neg]
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix Half Half ℂ, Y = σ • toC Dfull := ⟨_, rfl⟩
  have hYH : Yᴴ = Y := by
    rw [hY, conjTranspose_smul, Dfull_conjTranspose, smul_neg, ← neg_smul, hσc]
  have hYY : Y * Y = toC pMat := by
    have h := congrArg toC Dfull_sq
    rw [toC_mul, toC_neg] at h
    rw [hY, smul_mul_smul_comm, hσ2, h, neg_one_smul, neg_neg]
  obtain ⟨A, hA⟩ : ∃ A : Matrix Half Half ℂ,
      A = Y - (((17321 / 5000 : ℝ)) : ℂ) • (1 : Matrix Half Half ℂ) := ⟨_, rfl⟩
  have hAH : Aᴴ = A := by
    rw [hA, conjTranspose_sub, hYH, conjTranspose_smul, conjTranspose_one, RCLike.star_def,
      Complex.conj_ofReal]
  have hAA : A * A = toC pMat - ((2 * (17321 / 5000) : ℝ) : ℂ) • Y +
      (((17321 / 5000) ^ 2 : ℝ) : ℂ) • (1 : Matrix Half Half ℂ) := by
    rw [hA]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    rw [hYY]
    push_cast
    module
  have hid : ((((17321 / 5000 : ℝ) : ℂ) • (1 : Matrix Half Half ℂ)) - Y) =
      ((1 / (2 * (17321 / 5000)) : ℝ) : ℂ) • (Aᴴ * A) +
        ((((17321 / 5000) ^ 2 - 12) / (2 * (17321 / 5000)) : ℝ) : ℂ) •
          (1 : Matrix Half Half ℂ) +
        ((1 / (2 * (17321 / 5000)) : ℝ) : ℂ) •
          ((((12 : ℝ) : ℂ) • (1 : Matrix Half Half ℂ)) - toC pMat) := by
    rw [hAH, hAA]
    push_cast
    module
  rw [← hY, hid]
  have hc₁ : (0 : ℝ) ≤ 1 / (2 * (17321 / 5000)) := by norm_num
  have hc₂ : (0 : ℝ) ≤ ((17321 / 5000) ^ 2 - 12) / (2 * (17321 / 5000)) := by norm_num
  exact (((Matrix.posSemidef_conjTranspose_mul_self A).smul (RCLike.ofReal_nonneg.mpr hc₁)).add
    (Matrix.PosSemidef.one.smul (RCLike.ofReal_nonneg.mpr hc₂))).add
    (pMat_le_12.smul (RCLike.ofReal_nonneg.mpr hc₁))

/-- **The full Schur test of EL22** (`prop:observed-caps`): `36 I - B_⋆B_⋆ᵀ + 6σD ⪰ 0` for
`σ = ±i`, with `B_⋆B_⋆ᵀ` from the paper's definition over the `162` supports (`gram`). -/
theorem full_schur_test (σ : ℂ) (hσ : σ = Complex.I ∨ σ = -Complex.I) :
    ((((36 : ℝ) : ℂ) • (1 : Matrix Half Half ℂ)) - Matrix.of (fun j j' => (gram j j' : ℂ)) +
      ((6 : ℂ) * σ) • toC Dfull).PosSemidef := by
  have hG : Matrix.of (fun j j' => (gram j j' : ℂ)) = toC gramMat := by
    ext j j'
    simp only [toC, map_apply, of_apply, gram_eq, gramMat, eq_intCast]
  rw [hG]
  have hσ' : -σ = Complex.I ∨ -σ = -Complex.I := by
    rcases hσ with h | h <;> rw [h]
    · exact Or.inr rfl
    · exact Or.inl (neg_neg _)
  have hα := alpha_sub_Y (-σ) hσ'
  have hid : ((((36 : ℝ) : ℂ) • (1 : Matrix Half Half ℂ)) - toC gramMat +
      ((6 : ℂ) * σ) • toC Dfull) =
      ((((15 : ℝ) : ℂ) • (1 : Matrix Half Half ℂ)) - toC gramMat) +
        ((6 : ℝ) : ℂ) • ((((17321 / 5000 : ℝ) : ℂ) • (1 : Matrix Half Half ℂ)) -
          (-σ) • toC Dfull) +
        ((21 - 6 * (17321 / 5000) : ℝ) : ℂ) • (1 : Matrix Half Half ℂ) := by
    push_cast
    module
  rw [hid]
  have h6 : (0 : ℝ) ≤ 6 := by norm_num
  have h21 : (0 : ℝ) ≤ 21 - 6 * (17321 / 5000) := by norm_num
  exact (gram_le_15.add (hα.smul (RCLike.ofReal_nonneg.mpr h6))).add
    (Matrix.PosSemidef.one.smul (RCLike.ofReal_nonneg.mpr h21))

end Sarkozy.UpperReference.Observed
