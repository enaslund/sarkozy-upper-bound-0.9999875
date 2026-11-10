module

public import Sarkozy.Angles.AllPinNorm

/-!
# `lem:mid:allpin`, second statement: principal submatrices

`lem:mid:allpin` (`paper/sections/13_cuts_correlations.tex`), "in particular" part, for an
abstract family of subspaces indexed by a subset `S ⊆ P` (an injective `f : S → P`): with
`ℰ_{SS} = ℰ.submatrix f f`,
`cos∠(V[S ∖ {j}], V[S ∖ {i}]) ≤ [(I - ℰ_{SS})⁻¹]_{ij} ≤ [(I - ℰ)⁻¹]_{f i, f j}`
(`allpin_submatrix`). The matrix facts:
* `norm_submatrix_le`: `‖ℰ_{SS}‖ ≤ ‖ℰ‖` for the `ℓ²` operator norm (`ℰ_{SS} = Rᵀ ℰ R` with the
  inclusion `R`, `RᵀR = 1`);
* `inv_submatrix_le`: `[(I - ℰ_{SS})⁻¹]_{ij} ≤ [(I - ℰ)⁻¹]_{f i, f j}` for `ℰ ≥ 0`, `‖ℰ‖ < 1`
  (termwise comparison of the Neumann series, `(ℰ_{SS}ᵏ)_{ij} ≤ (ℰᵏ)_{f i, f j}`).
-/

@[expose] public section

open scoped InnerProductSpace Matrix.Norms.L2Operator
open Matrix

namespace Sarkozy.Angles

variable {P : Type*} [Fintype P] [DecidableEq P]
variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The inclusion matrix `R_{p s} = [p = f s]` of a map `f : S → P`. -/
def inclMatrix (f : S → P) : Matrix P S ℝ := Matrix.of fun p s => if p = f s then 1 else 0

omit [Fintype S] in
theorem inclMatrix_transpose_mul (f : S → P) (hf : Function.Injective f) :
    (inclMatrix f)ᵀ * inclMatrix f = 1 := by
  ext s t
  simp only [inclMatrix, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true, hf.eq_iff]
  by_cases h : s = t
  · subst h; simp
  · simp [h, Ne.symm h]

omit [Fintype S] [DecidableEq S] in
theorem submatrix_eq_incl (E : Matrix P P ℝ) (f : S → P) :
    E.submatrix f f = (inclMatrix f)ᵀ * E * inclMatrix f := by
  ext s t
  simp only [inclMatrix, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.of_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq']

theorem norm_one_matrix_le : ‖(1 : Matrix S S ℝ)‖ ≤ 1 := by
  rw [cstar_norm_def, map_one]
  exact ContinuousLinearMap.norm_id_le

theorem norm_inclMatrix_le (f : S → P) (hf : Function.Injective f) : ‖inclMatrix f‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self (inclMatrix f)
  rw [conjTranspose_eq_transpose_of_trivial, inclMatrix_transpose_mul f hf] at h
  have h1 := norm_one_matrix_le (S := S)
  rw [h] at h1
  nlinarith [norm_nonneg (inclMatrix f)]

/-- `‖ℰ_{SS}‖ ≤ ‖ℰ‖` for the `ℓ²` operator norm. -/
theorem norm_submatrix_le (E : Matrix P P ℝ) (f : S → P) (hf : Function.Injective f) :
    ‖E.submatrix f f‖ ≤ ‖E‖ := by
  rw [submatrix_eq_incl]
  have hR := norm_inclMatrix_le f hf
  have hRt : ‖(inclMatrix f)ᵀ‖ ≤ 1 := by
    rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose]
    exact hR
  calc ‖(inclMatrix f)ᵀ * E * inclMatrix f‖
      ≤ ‖(inclMatrix f)ᵀ * E‖ * ‖inclMatrix f‖ := l2_opNorm_mul _ _
    _ ≤ (‖(inclMatrix f)ᵀ‖ * ‖E‖) * 1 := by
        gcongr
        exact l2_opNorm_mul _ _
    _ ≤ (1 * ‖E‖) * 1 := by gcongr
    _ = ‖E‖ := by ring

/-- Termwise comparison: `(ℰ_{SS}ᵏ)_{st} ≤ (ℰᵏ)_{f s, f t}` for `ℰ ≥ 0`. -/
theorem pow_submatrix_apply_le (E : Matrix P P ℝ) (hnn : ∀ x y, 0 ≤ E x y) (f : S → P)
    (hf : Function.Injective f) (k : ℕ) (s t : S) :
    ((E.submatrix f f) ^ k) s t ≤ (E ^ k) (f s) (f t) := by
  induction k generalizing s t with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, hf.eq_iff]
    exact le_rfl
  | succ k ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    calc ∑ u, ((E.submatrix f f) ^ k) s u * (E.submatrix f f) u t
        ≤ ∑ u, (E ^ k) (f s) (f u) * E (f u) (f t) := by
          refine Finset.sum_le_sum fun u _ => ?_
          rw [Matrix.submatrix_apply]
          exact mul_le_mul_of_nonneg_right (ih s u) (hnn _ _)
      _ = ∑ p ∈ Finset.univ.map ⟨f, hf⟩, (E ^ k) (f s) p * E p (f t) := by
          rw [Finset.sum_map]
          rfl
      _ ≤ ∑ p, (E ^ k) (f s) p * E p (f t) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun p _ _ =>
            mul_nonneg (pow_apply_nonneg E hnn k _ _) (hnn _ _)

/-- `[(I - ℰ_{SS})⁻¹]_{st} ≤ [(I - ℰ)⁻¹]_{f s, f t}` for `ℰ ≥ 0` with `‖ℰ‖ < 1`. -/
theorem inv_submatrix_le (E : Matrix P P ℝ) (hnn : ∀ x y, 0 ≤ E x y) (hnorm : ‖E‖ < 1)
    (f : S → P) (hf : Function.Injective f) (s t : S) :
    (1 - E.submatrix f f)⁻¹ s t ≤ (1 - E)⁻¹ (f s) (f t) := by
  have hnorm' : ‖E.submatrix f f‖ < 1 := (norm_submatrix_le E f hf).trans_lt hnorm
  rw [Matrix.inv_eq_left_inv (neumann_mul _ hnorm'), Matrix.inv_eq_left_inv (neumann_mul _ hnorm),
    neumann_apply _ hnorm', neumann_apply _ hnorm]
  exact (summable_pow_apply _ hnorm' s t).tsum_le_tsum
    (fun k => pow_submatrix_apply_le E hnn f hf k s t) (summable_pow_apply _ hnorm _ _)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **`lem:mid:allpin`, second statement**, for an abstract family of subspaces indexed by the
subsets of `S`, where `f : S → P` is injective (the paper's `F' ⊆ F`): if `ℰ` is symmetric with
nonnegative entries, zero diagonal and `‖ℰ‖ < 1`, and `cos∠(V[{i}], V[{j}]) ≤ ℰ_{f i, f j}`,
then `cos∠(V[S ∖ {j}], V[S ∖ {i}]) ≤ [(I - ℰ_{SS})⁻¹]_{ij} ≤ [(I - ℰ)⁻¹]_{f i, f j}`. -/
theorem allpin_submatrix (V : Finset S → Submodule ℝ E)
    (hV : ∀ 𝒴 𝒴' : Finset S, V 𝒴 ⊓ V 𝒴' = V (𝒴 ∪ 𝒴'))
    (Ebar : Matrix P P ℝ) (hsymm : Ebar.IsSymm) (hdiag : ∀ x, Ebar x x = 0)
    (hnn : ∀ x y, 0 ≤ Ebar x y) (hnorm : ‖Ebar‖ < 1) (f : S → P) (hf : Function.Injective f)
    (hcos : ∀ i j, i ≠ j → friedrichsCos (V {i}) (V {j}) ≤ Ebar (f i) (f j))
    {i j : S} (hne : i ≠ j) :
    friedrichsCos (V (Finset.univ \ {j})) (V (Finset.univ \ {i})) ≤
        (1 - Ebar.submatrix f f)⁻¹ i j ∧
      (1 - Ebar.submatrix f f)⁻¹ i j ≤ (1 - Ebar)⁻¹ (f i) (f j) := by
  refine ⟨allpin V hV (Ebar.submatrix f f) (hsymm.submatrix f) (fun x => hdiag (f x))
    (fun x y => hnn (f x) (f y)) ((norm_submatrix_le Ebar f hf).trans_lt hnorm) hcos hne, ?_⟩
  exact inv_submatrix_le Ebar hnn hnorm f hf i j

end Sarkozy.Angles
