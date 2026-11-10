module

public import Sarkozy.Reflection.Tensor
public import Mathlib.Analysis.Matrix.Order

/-!
# Kronecker products over finite families of matrices

For a finite family of square real matrices `A j` indexed by coordinates `j`,
`piKron A` is the matrix on the product `∀ j, Ω j` with entries
`∏ j, A j (x j) (y j)`. This is the tensor product `⊗_j A_j` of the paper,
written in coordinates. We prove the mixed-product rule, transposes, the
identity and the averaging matrix, sums over product index sets, positivity,
and Loewner monotonicity (`0 ⪯ A_j ⪯ B_j` for all `j` implies
`⊗_j A_j ⪯ ⊗_j B_j`, the last assertion of `lem:record:block-gram`(d) for
entrywise-represented Kronecker products).

The positivity argument pulls each factor back to the product index set and
uses the Schur product theorem (`Matrix.PosSemidef.hadamard`), as in
`Sarkozy.matrix_prod_posSemidef` of `Sarkozy/Reflection/Matrix.lean`.
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.IndexSupport

/-- The averaging matrix of the uniform probability on a finite set: every entry is
`1 / |Ω|`. Applied to a function it returns the constant function equal to its mean. -/
noncomputable def meanMatrix (Ω : Type*) [Fintype Ω] : Matrix Ω Ω ℝ :=
  fun _ _ => (Fintype.card Ω : ℝ)⁻¹

theorem meanMatrix_apply (Ω : Type*) [Fintype Ω] (x y : Ω) :
    meanMatrix Ω x y = (Fintype.card Ω : ℝ)⁻¹ := rfl

theorem meanMatrix_transpose (Ω : Type*) [Fintype Ω] : (meanMatrix Ω)ᵀ = meanMatrix Ω := by
  ext x y
  rfl

theorem meanMatrix_mul_self (Ω : Type*) [Fintype Ω] [Nonempty Ω] :
    meanMatrix Ω * meanMatrix Ω = meanMatrix Ω := by
  ext x y
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Matrix.mul_apply, meanMatrix_apply, sum_const, card_univ, nsmul_eq_mul]
  field_simp

theorem meanMatrix_mulVec (Ω : Type*) [Fintype Ω] (f : Ω → ℝ) :
    meanMatrix Ω *ᵥ f = fun _ => (Fintype.card Ω : ℝ)⁻¹ * ∑ η, f η := by
  ext x
  simp only [Matrix.mulVec, dotProduct, meanMatrix_apply, Finset.mul_sum]

section Kron

variable {K : Type*} [Fintype K] {Ω : K → Type*}

/-- The Kronecker (tensor) product `⊗_j A_j` of a finite family of square matrices,
as a matrix on the product of the index sets. -/
def piKron (A : ∀ j, Matrix (Ω j) (Ω j) ℝ) : Matrix (∀ j, Ω j) (∀ j, Ω j) ℝ :=
  fun x y => ∏ j, A j (x j) (y j)

theorem piKron_apply (A : ∀ j, Matrix (Ω j) (Ω j) ℝ) (x y : ∀ j, Ω j) :
    piKron A x y = ∏ j, A j (x j) (y j) := rfl

/-- The mixed-product rule `(⊗_j A_j)(⊗_j B_j) = ⊗_j (A_j B_j)`. -/
theorem piKron_mul [DecidableEq K] [∀ j, Fintype (Ω j)] (A B : ∀ j, Matrix (Ω j) (Ω j) ℝ) :
    piKron A * piKron B = piKron (fun j => A j * B j) := by
  ext x z
  simp only [Matrix.mul_apply, piKron_apply]
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro y _
  rw [prod_mul_distrib]

theorem piKron_transpose (A : ∀ j, Matrix (Ω j) (Ω j) ℝ) :
    (piKron A)ᵀ = piKron (fun j => (A j)ᵀ) := by
  ext x y
  simp only [Matrix.transpose_apply, piKron_apply]

theorem piKron_one [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)] :
    piKron (fun j => (1 : Matrix (Ω j) (Ω j) ℝ)) = 1 := by
  ext x y
  simp only [piKron_apply, Matrix.one_apply]
  rw [prod_indicator_forall (fun j => x j = y j)]
  by_cases h : x = y
  · subst h
    simp
  · have h' : ¬ ∀ j, x j = y j := fun h'' => h (funext h'')
    rw [ite_eq_right h', ite_eq_right h]

theorem piKron_eq_zero {A : ∀ j, Matrix (Ω j) (Ω j) ℝ} (k : K) (hk : A k = 0) :
    piKron A = 0 := by
  ext x y
  simp only [piKron_apply, Matrix.zero_apply]
  exact prod_eq_zero (mem_univ k) (by rw [hk]; rfl)

theorem piKron_smul (c : K → ℝ) (A : ∀ j, Matrix (Ω j) (Ω j) ℝ) :
    piKron (fun j => c j • A j) = (∏ j, c j) • piKron A := by
  ext x y
  simp only [piKron_apply, Matrix.smul_apply, smul_eq_mul, prod_mul_distrib]

theorem piKron_meanMatrix [DecidableEq K] [∀ j, Fintype (Ω j)] :
    piKron (fun j => meanMatrix (Ω j)) = meanMatrix (∀ j, Ω j) := by
  ext x y
  simp only [piKron_apply, meanMatrix_apply, Fintype.card_pi, Nat.cast_prod, prod_inv_distrib]

/-- A sum of Kronecker products over a product index set factorizes. -/
theorem piKron_sum [DecidableEq K] {S : K → Type*} [∀ j, Fintype (S j)]
    (A : ∀ j, S j → Matrix (Ω j) (Ω j) ℝ) :
    ∑ s : ∀ j, S j, piKron (fun j => A j (s j)) = piKron (fun j => ∑ t, A j t) := by
  ext x y
  simp only [Matrix.sum_apply, piKron_apply]
  rw [Fintype.prod_sum]

/-- The same factorization over a box `∏_j t_j` of indices. -/
theorem piKron_sum_piFinset [DecidableEq K] {S : K → Type*} [∀ j, DecidableEq (S j)]
    (t : ∀ j, Finset (S j)) (A : ∀ j, S j → Matrix (Ω j) (Ω j) ℝ) :
    ∑ s ∈ Fintype.piFinset t, piKron (fun j => A j (s j)) =
      piKron (fun j => ∑ u ∈ t j, A j u) := by
  ext x y
  simp only [Matrix.sum_apply, piKron_apply]
  rw [prod_univ_sum]

/-- Partial Kronecker products over a finite set of coordinates (the other factors are
the all-ones matrix). Used for induction. -/
def piKronOn (s : Finset K) (A : ∀ j, Matrix (Ω j) (Ω j) ℝ) :
    Matrix (∀ j, Ω j) (∀ j, Ω j) ℝ :=
  fun x y => ∏ j ∈ s, A j (x j) (y j)

theorem piKronOn_univ (A : ∀ j, Matrix (Ω j) (Ω j) ℝ) : piKronOn univ A = piKron A := rfl

omit [Fintype K] in
theorem piKronOn_insert [DecidableEq K] {s : Finset K} {k : K} (hk : k ∉ s) (A : ∀ j, Matrix (Ω j) (Ω j) ℝ) :
    piKronOn (insert k s) A =
      ((A k).submatrix (fun x : ∀ j, Ω j => x k) (fun x => x k)) ⊙ piKronOn s A := by
  ext x y
  simp only [piKronOn, Matrix.hadamard_apply, Matrix.submatrix_apply, prod_insert hk]

theorem piKronOn_posSemidef [∀ j, Fintype (Ω j)] [DecidableEq K] (s : Finset K) {A : ∀ j, Matrix (Ω j) (Ω j) ℝ}
    (hA : ∀ j ∈ s, (A j).PosSemidef) : (piKronOn s A).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have he : piKronOn (∅ : Finset K) A =
        Matrix.vecMulVec (fun _ : (∀ j, Ω j) => (1 : ℝ)) (star (fun _ : (∀ j, Ω j) => (1 : ℝ))) := by
      ext x y
      simp [piKronOn, Matrix.vecMulVec]
    rw [he]
    exact Matrix.posSemidef_vecMulVec_self_star _
  | @insert k s hk ih =>
    rw [piKronOn_insert hk]
    exact ((hA k (mem_insert_self k s)).submatrix _).hadamard
      (ih (fun j hj => hA j (mem_insert_of_mem hj)))

/-- A Kronecker product of positive semidefinite matrices is positive semidefinite. -/
theorem piKron_posSemidef [∀ j, Fintype (Ω j)] [DecidableEq K] {A : ∀ j, Matrix (Ω j) (Ω j) ℝ} (hA : ∀ j, (A j).PosSemidef) :
    (piKron A).PosSemidef :=
  piKronOn_posSemidef univ (fun j _ => hA j)

theorem piKronOn_sub_posSemidef [∀ j, Fintype (Ω j)] [DecidableEq K] (s : Finset K) {A B : ∀ j, Matrix (Ω j) (Ω j) ℝ}
    (hA : ∀ j ∈ s, (A j).PosSemidef) (hAB : ∀ j ∈ s, (B j - A j).PosSemidef) :
    (piKronOn s B - piKronOn s A).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have he : piKronOn (∅ : Finset K) B - piKronOn (∅ : Finset K) A = 0 := by
      ext x y
      simp [piKronOn]
    rw [he]
    exact Matrix.PosSemidef.zero
  | @insert k s hk ih =>
    have hAs : ∀ j ∈ s, (A j).PosSemidef := fun j hj => hA j (mem_insert_of_mem hj)
    have hABs : ∀ j ∈ s, (B j - A j).PosSemidef := fun j hj => hAB j (mem_insert_of_mem hj)
    have hBk : (B k).PosSemidef := by
      have h := (hA k (mem_insert_self k s)).add (hAB k (mem_insert_self k s))
      rwa [add_sub_cancel] at h
    have he : piKronOn (insert k s) B - piKronOn (insert k s) A =
        ((B k).submatrix (fun x : ∀ j, Ω j => x k) (fun x => x k)) ⊙
            (piKronOn s B - piKronOn s A) +
          ((B k - A k).submatrix (fun x : ∀ j, Ω j => x k) (fun x => x k)) ⊙ piKronOn s A := by
      rw [piKronOn_insert hk, piKronOn_insert hk]
      ext x y
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.hadamard_apply,
        Matrix.submatrix_apply]
      ring
    rw [he]
    exact ((hBk.submatrix _).hadamard (ih hAs hABs)).add
      (((hAB k (mem_insert_self k s)).submatrix _).hadamard (piKronOn_posSemidef s hAs))

/-- Loewner monotonicity of Kronecker products: if `0 ⪯ A_j ⪯ B_j` for every `j`,
then `⊗_j A_j ⪯ ⊗_j B_j`. -/
theorem piKron_sub_posSemidef [∀ j, Fintype (Ω j)] [DecidableEq K] {A B : ∀ j, Matrix (Ω j) (Ω j) ℝ}
    (hA : ∀ j, (A j).PosSemidef) (hAB : ∀ j, (B j - A j).PosSemidef) :
    (piKron B - piKron A).PosSemidef :=
  piKronOn_sub_posSemidef univ (fun j _ => hA j) (fun j _ => hAB j)

end Kron

end Sarkozy.IndexSupport
