module

public import Sarkozy.Mixing.SectorLemma

/-!
# The spectrum of a tensor product of self-adjoint operators

`lem:sector`(g) (Tensor spectrum, no sector hypothesis) and the second assertion of
`lem:sector`(c), for real symmetric matrices (self-adjoint operators on `ℝ^n` with the
Euclidean, equivalently uniform, inner product). Spectral bounds are stated as quadratic-form
bounds, which for a symmetric matrix is the same as a bound on its spectrum.

* `tensor_spectrum`: if `-c_i ‖x‖² ≤ ⟨x, A_i x⟩ ≤ (1 + b_i) ‖x‖²` with `b_i ≥ 0` and
  `0 ≤ c_i ≤ 1 + b_i`, then the spectrum of `⊗_i A_i` lies in
  `[-M, ∏_i (1 + b_i)]` for every `M ≥ max_i c_i ∏_{k≠i} (1 + b_k)`.
* `tensor_spectrum_exp`: in particular `⊗_i A_i ⪰ -(max_i c_i) e^{∑_i b_i}`.
* `tensor_lower_markov`: with `b = 0` (spectra in `[-c_i, 1]`), `⊗_i A_i ⪰ -(max_i c_i)`, the
  second assertion of `lem:sector`(c).

Proof: diagonalize each factor by the spectral theorem (`Matrix.IsHermitian.spectral_theorem`);
the Kronecker product of the orthogonal matrices is orthogonal and diagonalizes `⊗_i A_i`, with
eigenvalues the products `∏_i λ_i`; a negative product has a negative factor `λ_i ≥ -c_i` and
the other factors of modulus at most `1 + b_k`.
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.Mixing

open Sarkozy.IndexSupport

/-- Orthogonal diagonalization of a real symmetric matrix. -/
theorem exists_orthogonal_diag {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : Aᵀ = A) :
    ∃ (U : Matrix n n ℝ) (μ : n → ℝ), Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧ A = U * Matrix.diagonal μ * Uᵀ := by
  have hH : A.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hA]
  refine ⟨(hH.eigenvectorUnitary : Matrix n n ℝ), hH.eigenvalues, ?_, ?_, ?_⟩
  · have h := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  · have h := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    rwa [Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] at h
  · have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] at h
    simpa only [RCLike.ofReal_real_eq_id, Function.id_comp] using h

/-- Eigenvalue bounds from quadratic-form bounds. -/
theorem diag_bounds {n : Type*} [Fintype n] [DecidableEq n] {A U : Matrix n n ℝ} {μ : n → ℝ}
    (hUU : Uᵀ * U = 1) (hA : A = U * Matrix.diagonal μ * Uᵀ) {lo hi : ℝ}
    (hlow : ∀ x, lo * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x)) (hup : ∀ x, x ⬝ᵥ (A *ᵥ x) ≤ hi * (x ⬝ᵥ x))
    (i : n) : lo ≤ μ i ∧ μ i ≤ hi := by
  have horth (x y : n → ℝ) : (U *ᵥ x) ⬝ᵥ (U *ᵥ y) = x ⬝ᵥ y := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hUU,
      Matrix.one_mulVec]
  have hAU : A * U = U * Matrix.diagonal μ := by
    rw [hA, Matrix.mul_assoc (U * Matrix.diagonal μ), hUU, Matrix.mul_one]
  set e : n → ℝ := Pi.single i 1 with he
  have hvv : (U *ᵥ e) ⬝ᵥ (U *ᵥ e) = 1 := by
    rw [horth, he]
    simp
  have hAv : (U *ᵥ e) ⬝ᵥ (A *ᵥ (U *ᵥ e)) = μ i := by
    rw [Matrix.mulVec_mulVec, hAU, ← Matrix.mulVec_mulVec, horth, he,
      Matrix.diagonal_mulVec_single]
    simp
  have h1 := hlow (U *ᵥ e)
  have h2 := hup (U *ᵥ e)
  rw [hvv, hAv, mul_one] at h1 h2
  exact ⟨h1, h2⟩

/-- The scalar heart of `lem:sector`(g): products of numbers in `[-c_i, 1 + b_i]`. -/
theorem prod_bounds {K : Type*} [Fintype K] [DecidableEq K] (lam b c : K → ℝ)
    (hcb : ∀ j, c j ≤ 1 + b j) (hlo : ∀ j, -c j ≤ lam j)
    (hhi : ∀ j, lam j ≤ 1 + b j) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i, c i * ∏ k : {k // k ≠ i}, (1 + b k) ≤ M) :
    -M ≤ ∏ j, lam j ∧ ∏ j, lam j ≤ ∏ j, (1 + b j) := by
  have habs (j : K) : |lam j| ≤ 1 + b j := abs_le.mpr ⟨by linarith [hlo j, hcb j], hhi j⟩
  have hprod_abs : |∏ j, lam j| ≤ ∏ j, (1 + b j) := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j _ => habs j)
  refine ⟨?_, (le_abs_self _).trans hprod_abs⟩
  by_cases hneg : ∏ j, lam j < 0
  · obtain ⟨i, hi⟩ : ∃ i, lam i < 0 := by
      by_contra h
      push Not at h
      exact absurd (Finset.prod_nonneg (fun j _ => h j)) (not_le.mpr hneg)
    have hsplit : |∏ j, lam j| = |lam i| * ∏ k : {k // k ≠ i}, |lam k| := by
      rw [Finset.abs_prod, Fintype.prod_eq_mul_prod_subtype_ne _ i]
    have hrest : ∏ k : {k // k ≠ i}, |lam k| ≤ ∏ k : {k // k ≠ i}, (1 + b k) :=
      Finset.prod_le_prod₀ (fun k _ => abs_nonneg _) (fun k _ => habs k)
    have hli : |lam i| ≤ c i := by
      rw [abs_of_neg hi]
      linarith [hlo i]
    have hrest0 : 0 ≤ ∏ k : {k // k ≠ i}, |lam k| := Finset.prod_nonneg (fun k _ => abs_nonneg _)
    have hc0 : 0 ≤ c i := le_trans (abs_nonneg _) hli
    have h1 : |∏ j, lam j| ≤ M := by
      rw [hsplit]
      calc |lam i| * ∏ k : {k // k ≠ i}, |lam k| ≤ c i * ∏ k : {k // k ≠ i}, (1 + b k) :=
            mul_le_mul hli hrest hrest0 hc0
        _ ≤ M := hM i
    have := neg_abs_le (∏ j, lam j)
    linarith
  · push Not at hneg
    linarith

variable {K : Type*} [Fintype K] [DecidableEq K] {Ω : K → Type*} [∀ j, Fintype (Ω j)]
  [∀ j, DecidableEq (Ω j)]

/-- **`lem:sector`(g), tensor spectrum.** For symmetric `A_i` with
`-c_i ‖x‖² ≤ ⟨x, A_i x⟩ ≤ (1 + b_i) ‖x‖²`, `b_i ≥ 0`, `0 ≤ c_i ≤ 1 + b_i`, and every
`M ≥ max_i c_i ∏_{k ≠ i} (1 + b_k)`:
`-M ‖x‖² ≤ ⟨x, (⊗_i A_i) x⟩ ≤ ∏_i (1 + b_i) ‖x‖²`. -/
theorem tensor_spectrum (A : ∀ j, Matrix (Ω j) (Ω j) ℝ) (hA : ∀ j, (A j)ᵀ = A j)
    (b c : K → ℝ) (hcb : ∀ j, c j ≤ 1 + b j)
    (hlow : ∀ j x, -c j * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A j *ᵥ x))
    (hup : ∀ j x, x ⬝ᵥ (A j *ᵥ x) ≤ (1 + b j) * (x ⬝ᵥ x))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i, c i * ∏ k : {k // k ≠ i}, (1 + b k) ≤ M)
    (x : (∀ j, Ω j) → ℝ) :
    -M * (x ⬝ᵥ x) ≤ x ⬝ᵥ (piKron A *ᵥ x) ∧
      x ⬝ᵥ (piKron A *ᵥ x) ≤ (∏ j, (1 + b j)) * (x ⬝ᵥ x) := by
  choose U μ hUU hUU' hdiag using fun j => exists_orthogonal_diag (hA j)
  have hbd (j : K) (i : Ω j) := diag_bounds (hUU j) (hdiag j) (hlow j) (hup j) i
  set W := piKron U with hW
  have hWW : Wᵀ * W = 1 := by
    rw [hW, piKron_transpose, piKron_mul]
    simp only [hUU, piKron_one]
  have hWW' : W * Wᵀ = 1 := by
    rw [hW, piKron_transpose, piKron_mul]
    simp only [hUU', piKron_one]
  have hAk : piKron A = W * Matrix.diagonal (prodW μ) * Wᵀ := by
    rw [hW, piKron_transpose, ← piKron_diagonal μ, piKron_mul, piKron_mul]
    congr 1
    funext j
    exact hdiag j
  set y := Wᵀ *ᵥ x with hy
  have hyy : y ⬝ᵥ y = x ⬝ᵥ x := by
    rw [hy, ← Matrix.dotProduct_transpose_mulVec, Matrix.transpose_transpose, Matrix.mulVec_mulVec,
      hWW', Matrix.one_mulVec]
  have hq : x ⬝ᵥ (piKron A *ᵥ x) = ∑ k, prodW μ k * y k ^ 2 := by
    rw [hAk, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.dotProduct_transpose_mulVec,
      ← hy]
    simp only [dotProduct, Matrix.mulVec_diagonal, sq]
    apply sum_congr rfl
    intro k _
    ring
  have hk (k : ∀ j, Ω j) : -M ≤ prodW μ k ∧ prodW μ k ≤ ∏ j, (1 + b j) :=
    prod_bounds (fun j => μ j (k j)) b c hcb (fun j => (hbd j (k j)).1)
      (fun j => (hbd j (k j)).2) hM0 hM
  have hyy' : y ⬝ᵥ y = ∑ k, y k ^ 2 := by simp only [dotProduct, sq]
  rw [hq, ← hyy, hyy']
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hk k).1 (sq_nonneg _))
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hk k).2 (sq_nonneg _))

/-- `lem:sector`(g), "in particular": `⊗_i A_i ⪰ -(max_i c_i) e^{∑_i b_i}` for every
`m ≥ max_i c_i`. -/
theorem tensor_spectrum_exp (A : ∀ j, Matrix (Ω j) (Ω j) ℝ) (hA : ∀ j, (A j)ᵀ = A j)
    (b c : K → ℝ) (hb : ∀ j, 0 ≤ b j) (hcb : ∀ j, c j ≤ 1 + b j)
    (hlow : ∀ j x, -c j * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A j *ᵥ x))
    (hup : ∀ j x, x ⬝ᵥ (A j *ᵥ x) ≤ (1 + b j) * (x ⬝ᵥ x))
    {m : ℝ} (hm0 : 0 ≤ m) (hm : ∀ i, c i ≤ m) (x : (∀ j, Ω j) → ℝ) :
    -(m * Real.exp (∑ j, b j)) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (piKron A *ᵥ x) := by
  have hprod : ∏ j, (1 + b j) ≤ Real.exp (∑ j, b j) := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun j _ => by linarith [hb j])
      (fun j _ => by linarith [Real.add_one_le_exp (b j)])
  have hM (i : K) : c i * ∏ k : {k // k ≠ i}, (1 + b k) ≤ m * Real.exp (∑ j, b j) := by
    have h1 : ∏ k : {k // k ≠ i}, (1 + b k) ≤ ∏ j, (1 + b j) := by
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
      have h0 : 0 ≤ ∏ k : {k // k ≠ i}, (1 + b k) :=
        Finset.prod_nonneg (fun k _ => by linarith [hb k])
      nlinarith [hb i]
    have h2 : 0 ≤ ∏ k : {k // k ≠ i}, (1 + b k) :=
      Finset.prod_nonneg (fun k _ => by linarith [hb k])
    calc c i * ∏ k : {k // k ≠ i}, (1 + b k) ≤ m * ∏ j, (1 + b j) :=
          mul_le_mul (hm i) h1 h2 hm0
      _ ≤ m * Real.exp (∑ j, b j) := mul_le_mul_of_nonneg_left hprod hm0
  exact (tensor_spectrum A hA b c hcb hlow hup
    (mul_nonneg hm0 (Real.exp_pos _).le) hM x).1

/-- The second assertion of `lem:sector`(c): self-adjoint factors with spectra in `[-c_j, 1]`,
`0 ≤ c_j ≤ 1`, give `⊗_j T_j ⪰ -(max_j c_j)`, for every `m ≥ max_j c_j`. -/
theorem tensor_lower_markov (A : ∀ j, Matrix (Ω j) (Ω j) ℝ) (hA : ∀ j, (A j)ᵀ = A j)
    (c : K → ℝ) (hc1 : ∀ j, c j ≤ 1)
    (hlow : ∀ j x, -c j * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A j *ᵥ x))
    (hup : ∀ j x, x ⬝ᵥ (A j *ᵥ x) ≤ 1 * (x ⬝ᵥ x))
    {m : ℝ} (hm0 : 0 ≤ m) (hm : ∀ i, c i ≤ m) (x : (∀ j, Ω j) → ℝ) :
    -m * (x ⬝ᵥ x) ≤ x ⬝ᵥ (piKron A *ᵥ x) := by
  have h := (tensor_spectrum A hA (fun _ => 0) c (fun j => by simp [hc1 j])
    hlow (fun j x => by simpa using hup j x) hm0
    (fun i => by simp only [add_zero, prod_const_one, mul_one]; exact hm i) x).1
  exact h

end Sarkozy.Mixing
