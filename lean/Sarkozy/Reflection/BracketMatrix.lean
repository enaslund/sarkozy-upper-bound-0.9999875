module

public import Sarkozy.Reflection.Bracket

/-!
# Matrix characterization and tensorization of brackets

The quadratic-form definition of a bracket is equivalent to positivity of
the literal two-by-two block cut matrix. Pulling back the factor block matrices
and taking their entrywise product proves tensorization, including singular
diagonal blocks and nonsymmetric off-diagonal blocks.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace Sarkozy.ReflectionCut

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]

theorem form_eq_dotProduct (c : ReflectionCut V) (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (F G : (c.Half → X) → ℝ) : c.form L F G = F ⬝ᵥ (c.matrix L *ᵥ G) := by
  rw [form, cut_form_eq_sum]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  change cutKernel L _ _ x y * F x * G y = F x * (cutKernel L _ _ x y * G y)
  ring

noncomputable def blockMatrix (c : ReflectionCut V)
    (L K R : ((V → X) → ℝ) →ₗ[ℝ] ℝ) :
    Matrix ((c.Half → X) ⊕ (c.Half → X)) ((c.Half → X) ⊕ (c.Half → X)) ℝ :=
  Matrix.fromBlocks (c.matrix L) (c.matrix K) (c.matrix K).transpose (c.matrix R)

theorem block_quadratic (c : ReflectionCut V) (L K R : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (F G : (c.Half → X) → ℝ) :
    Sum.elim F G ⬝ᵥ (c.blockMatrix L K R *ᵥ Sum.elim F G) =
      c.form L F F + 2 * c.form K F G + c.form R G G := by
  rw [blockMatrix, Matrix.fromBlocks_mulVec]
  change Sum.elim F G ⬝ᵥ Sum.elim
    (c.matrix L *ᵥ F + c.matrix K *ᵥ G)
    ((c.matrix K).transpose *ᵥ F + c.matrix R *ᵥ G) = _
  rw [sumElim_dotProduct_sumElim, dotProduct_add, dotProduct_add,
    Matrix.dotProduct_transpose_mulVec]
  rw [← c.form_eq_dotProduct, ← c.form_eq_dotProduct, ← c.form_eq_dotProduct]
  ring

theorem bracket_iff_blockMatrix_posSemidef (c : ReflectionCut V)
    (L K R : ((V → X) → ℝ) →ₗ[ℝ] ℝ) :
    c.Bracket L K R ↔ (c.blockMatrix L K R).PosSemidef := by
  constructor
  · intro h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · exact ((c.positive_iff_matrix_posSemidef L).mp h.left_positive).isHermitian.fromBlocks
        (by ext x y; rfl)
        ((c.positive_iff_matrix_posSemidef R).mp h.right_positive).isHermitian
    · intro x
      have he : x = Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) := by
        funext i
        cases i <;> rfl
      rw [star_trivial, he, c.block_quadratic]
      exact h.nonneg _ _
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · apply (c.positive_iff_matrix_posSemidef L).mpr
      exact h.submatrix Sum.inl
    · apply (c.positive_iff_matrix_posSemidef R).mpr
      exact h.submatrix Sum.inr
    · intro F G
      have hh := h.dotProduct_mulVec_nonneg (Sum.elim F G)
      rwa [star_trivial, c.block_quadratic] at hh

/-- Block positivity is preserved by any finite tensor product of laws at a
common cut. This is the block-Gram tensorization used in the comparison law. -/
theorem Bracket.tensor {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)] {c : ReflectionCut V}
    {L K R : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ} (h : ∀ j, c.Bracket (L j) (K j) (R j)) :
    c.Bracket (tensorLaw L) (tensorLaw K) (tensorLaw R) := by
  apply (c.bracket_iff_blockMatrix_posSemidef _ _ _).mpr
  let pull (j : J) : ((c.Half → ∀ j, X j) ⊕ (c.Half → ∀ j, X j)) →
      ((c.Half → X j) ⊕ (c.Half → X j)) :=
    Sum.map (fun x v => x v j) (fun x v => x v j)
  let B (j : J) := (c.blockMatrix (L j) (K j) (R j)).submatrix (pull j) (pull j)
  have hp (j : J) : (B j).PosSemidef :=
    ((c.bracket_iff_blockMatrix_posSemidef _ _ _).mp (h j)).submatrix (pull j)
  have he : c.blockMatrix (tensorLaw L) (tensorLaw K) (tensorLaw R) =
      fun x y => ∏ j, B j x y := by
    ext (x | x) (y | y)
    · exact tensorLaw_cutKernel L (fun v : c.Half => v.1) (fun v => c.flip v.1) x y
    · exact tensorLaw_cutKernel K (fun v : c.Half => v.1) (fun v => c.flip v.1) x y
    · exact tensorLaw_cutKernel K (fun v : c.Half => v.1) (fun v => c.flip v.1) y x
    · exact tensorLaw_cutKernel R (fun v : c.Half => v.1) (fun v => c.flip v.1) x y
  rw [he]
  exact matrix_prod_posSemidef B hp

end Sarkozy.ReflectionCut
