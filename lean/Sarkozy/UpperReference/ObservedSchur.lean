module

public import Sarkozy.UpperReference.ObservedCaps
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Complex.Basic

/-!
# `prop:observed-caps`: the Schur test of the merge's principal matrix

`paper/sections/25_upper_reference.tex`, `prop:observed-caps`, "Schur tests": the principal
matrix of the features of the merge's observed labels (twelve singletons and sixty supports)
satisfies `k²I - B_⋆B_⋆ᵀ ± i k D ⪰ 0` with `k = 2.188902`, which by `rem:realified-gates` gives
`‖M_vv(±i)‖ ≤ k`. On the singleton rows `B_⋆B_⋆ᵀ = I` (`merge_singleton_gram`), so the test is
`(k² - 1) I ± i k D_v ⪰ 0`, `D_v` the principal submatrix of `D` on the twelve labels of the
rows `0, 1` of the `E` coordinate.

* `Dmerge`, `Dmerge_anti`, `Dmerge_pow4`: `D_v` is antisymmetric and `D_v⁴ = -3 D_v²` (exact
  integer identities, by `decide`), so `Y = ±iD_v` is Hermitian with `Y⁴ = 3Y²`: its eigenvalues
  are `0` and `±√3`.
* `merge_schur_test`: **the test holds exactly**, for both signs. The certificate is the
  identity `(k² - 1) I + kY = c₁ A² + c₂ B² + c₃ I` with `A = Y + αI`, `B = 3I - Y²`,
  `α = 433/250`, `c₁ = k/(2α)`, `c₂ = k/(6α)` and
  `c₃ = k² - 1 - k(3 + α²)/(2α) ≈ 2.49·10⁻⁶ > 0` (the true margin is `k² - 1 - k√3`).

The step from the test to the norm bound (`rem:realified-gates`) is `ObservedGates.lean`
(`merge_gates`) and `ObservedNorm.lean` (`merge_normLe`).
-/

@[expose] public section

open scoped Matrix ComplexOrder ComplexConjugate
open Matrix

namespace Sarkozy.UpperReference.Observed

/-- The twelve labels of the rows `0, 1` of the `E` coordinate. -/
abbrev MHalf := Fin 2 × ZMod 6

/-- Their embedding into the eighteen labels of the plus half. -/
def mergeEmb (a : MHalf) : Half := (a.1.castSucc, a.2)

/-- The image of the embedding is the merge's set of observed labels. -/
theorem mergeEmb_image : Finset.univ.image mergeEmb = mergeObs := by
  decide +kernel

/-- **The principal submatrix `D_v` of `D` on the merge's observed labels.** -/
def Dmerge : Matrix MHalf MHalf ℤ := fun a b => crossD (mergeEmb a) (mergeEmb b)

/-- `D_v` is antisymmetric. -/
theorem Dmerge_anti : ∀ a b, Dmerge b a = -Dmerge a b := by
  decide +kernel

/-- **`D_v⁴ = -3 D_v²`**, an exact integer identity. -/
theorem Dmerge_pow4 :
    Dmerge * Dmerge * (Dmerge * Dmerge) =
      -(Dmerge * Dmerge + Dmerge * Dmerge + Dmerge * Dmerge) := by
  decide +kernel

/-- `D_v` as a complex matrix. -/
noncomputable def Dc : Matrix MHalf MHalf ℂ := Dmerge.map (Int.cast : ℤ → ℂ)

theorem Dc_eq : Dc = (Int.castRingHom ℂ).mapMatrix Dmerge := rfl

theorem Dc_conjTranspose : Dcᴴ = -Dc := by
  ext a b
  rw [conjTranspose_apply, neg_apply]
  simp only [Dc, map_apply, Dmerge_anti a b, Int.cast_neg, star_neg, star_intCast]

theorem Dc_pow4 : Dc * Dc * (Dc * Dc) = -(Dc * Dc + Dc * Dc + Dc * Dc) := by
  have h := congrArg (Int.castRingHom ℂ).mapMatrix Dmerge_pow4
  simp only [map_mul, map_neg, map_add] at h
  rw [Dc_eq]
  exact h

/-- **The merge Schur test** `(k² - 1) I + i σ k D_v ⪰ 0` for both signs `σ = ±1`, with
`k = 2188902/10⁶` (`prop:observed-caps`; `k² I - B_⋆B_⋆ᵀ ± ikD ⪰ 0` with `B_⋆B_⋆ᵀ = I` on the
singleton rows). -/
theorem merge_schur_test (σ : ℂ) (hσ : σ = Complex.I ∨ σ = -Complex.I) :
    ((((2188902 / 1000000 : ℝ) ^ 2 - 1 : ℝ) : ℂ) • (1 : Matrix MHalf MHalf ℂ) +
      (((2188902 / 1000000 : ℝ) : ℂ) * σ) • Dc).PosSemidef := by
  have hσ2 : σ * σ = -1 := by
    rcases hσ with h | h <;> rw [h]
    · exact Complex.I_mul_I
    · rw [neg_mul_neg, Complex.I_mul_I]
  have hσc : -(star σ) = σ := by
    rcases hσ with h | h <;> rw [h]
    · rw [Complex.star_def, Complex.conj_I, neg_neg]
    · rw [Complex.star_def, map_neg, Complex.conj_I, neg_neg]
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix MHalf MHalf ℂ, Y = σ • Dc := ⟨_, rfl⟩
  -- `Y` is Hermitian, `P = Y²` satisfies `P² = 3P`
  have hYH : Yᴴ = Y := by
    rw [hY, conjTranspose_smul, Dc_conjTranspose, smul_neg, ← neg_smul, hσc]
  obtain ⟨P, hP⟩ : ∃ P : Matrix MHalf MHalf ℂ, P = Y * Y := ⟨_, rfl⟩
  have hPD : P = -(Dc * Dc) := by
    rw [hP, hY, smul_mul_smul_comm, hσ2, neg_one_smul]
  have hPP : P * P = (3 : ℂ) • P := by
    rw [hPD, neg_mul_neg, Dc_pow4]
    module
  have hPH : Pᴴ = P := by rw [hP, conjTranspose_mul, hYH]
  -- the two squares
  obtain ⟨A, hA⟩ : ∃ A : Matrix MHalf MHalf ℂ,
      A = Y + (((433 / 250 : ℝ)) : ℂ) • (1 : Matrix MHalf MHalf ℂ) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix MHalf MHalf ℂ,
      B = (3 : ℂ) • (1 : Matrix MHalf MHalf ℂ) - P := ⟨_, rfl⟩
  have hAH : Aᴴ = A := by
    rw [hA, conjTranspose_add, hYH, conjTranspose_smul, conjTranspose_one, RCLike.star_def,
      Complex.conj_ofReal]
  have hBH : Bᴴ = B := by
    rw [hB, conjTranspose_sub, hPH, conjTranspose_smul, conjTranspose_one, star_ofNat]
  have hAA : A * A = P + ((2 * (433 / 250) : ℝ) : ℂ) • Y +
      (((433 / 250) ^ 2 : ℝ) : ℂ) • (1 : Matrix MHalf MHalf ℂ) := by
    rw [hA]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    rw [← hP]
    push_cast
    module
  have hBB : B * B = (9 : ℂ) • (1 : Matrix MHalf MHalf ℂ) - (3 : ℂ) • P := by
    rw [hB]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    rw [hPP]
    module
  -- the certificate
  have hid : ((((2188902 / 1000000 : ℝ) ^ 2 - 1 : ℝ) : ℂ) • (1 : Matrix MHalf MHalf ℂ) +
      (((2188902 / 1000000 : ℝ) : ℂ) * σ) • Dc) =
      (((2188902 / 1000000) / (2 * (433 / 250)) : ℝ) : ℂ) • (Aᴴ * A) +
        (((2188902 / 1000000) / (6 * (433 / 250)) : ℝ) : ℂ) • (Bᴴ * B) +
        (((2188902 / 1000000) ^ 2 - 1 - (2188902 / 1000000) * (3 + (433 / 250) ^ 2) /
          (2 * (433 / 250)) : ℝ) : ℂ) • (1 : Matrix MHalf MHalf ℂ) := by
    rw [hAH, hBH, hAA, hBB, mul_smul, ← hY]
    push_cast
    module
  rw [hid]
  have hc₁ : (0 : ℝ) ≤ (2188902 / 1000000) / (2 * (433 / 250)) := by norm_num
  have hc₂ : (0 : ℝ) ≤ (2188902 / 1000000) / (6 * (433 / 250)) := by norm_num
  have hc₃ : (0 : ℝ) ≤ (2188902 / 1000000) ^ 2 - 1 - (2188902 / 1000000) * (3 + (433 / 250) ^ 2) /
      (2 * (433 / 250)) := by norm_num
  exact (((Matrix.posSemidef_conjTranspose_mul_self A).smul (RCLike.ofReal_nonneg.mpr hc₁)).add
    ((Matrix.posSemidef_conjTranspose_mul_self B).smul (RCLike.ofReal_nonneg.mpr hc₂))).add
    (Matrix.PosSemidef.one.smul (RCLike.ofReal_nonneg.mpr hc₃))

end Sarkozy.UpperReference.Observed
