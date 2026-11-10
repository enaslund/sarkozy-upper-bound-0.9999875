module

public import Sarkozy.Cuts.Frames
public import Sarkozy.Cuts.Swapped
public import Mathlib.Analysis.Matrix.Order

/-!
# Cuts, XII: positive semidefinite majorants and Schur products

`13_cuts_correlations.tex`.

* `weighted_frame_psd`: `lem:weighted-frame` (a), the eigenvalue form. If
  `λ I - D^{1/2} G D^{1/2} ⪰ 0`, the synthesis map has squared norm at most `λ`. Since
  `λ_max(D^{1/2} G D^{1/2})` is the least such `λ`, this is the bound by `λ_max`; with `d ≡ 1` it is
  `‖∑_i V_i V_i^*‖ ≤ λ_max(G)`.
* `schur_operator_nonneg`, `schur_operator_le`: `lem:swapped-rectangle` (b), the general
  statement. Let `Γ` be a positive semidefinite kernel with `Γ(z, z) ≤ c`, and `W` an operator
  on `L²(γ)` with `0 ⪯ W ⪯ aI`. Then `0 ⪯ Γ ∘ W ⪯ caI`. The proof uses the Schur product theorem
  (`Matrix.PosSemidef.hadamard`). Here `γ` has full support, as in the paper.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Recentering Matrix

/-- The quadratic form of a real positive semidefinite matrix is nonnegative. -/
theorem quad_nonneg_of_posSemidef {ι : Type*} [Fintype ι] {M : Matrix ι ι ℝ}
    (hM : M.PosSemidef) (x : ι → ℝ) : 0 ≤ ∑ i, ∑ j, x i * M i j * x j := by
  have h := (posSemidef_iff_dotProduct_mulVec.mp hM).2 x
  simp only [star_trivial, dotProduct, mulVec, Finset.mul_sum] at h
  exact le_of_le_of_eq h
    (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring)))

/-- A real symmetric matrix with nonnegative quadratic form is positive semidefinite. -/
theorem posSemidef_of_quad {ι : Type*} [Fintype ι] {M : Matrix ι ι ℝ}
    (hsym : ∀ i j, M i j = M j i) (hq : ∀ x : ι → ℝ, 0 ≤ ∑ i, ∑ j, x i * M i j * x j) :
    M.PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    simp only [conjTranspose_apply, star_trivial]
    exact hsym j i
  · have h := hq x
    simp only [star_trivial, dotProduct, mulVec, Finset.mul_sum]
    exact le_of_le_of_eq h
      (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring)))

/-- **`lem:weighted-frame` (a), eigenvalue form.** If `λ I - D^{1/2} G D^{1/2} ⪰ 0`, then
`‖∑_i √d_i V_i z_i‖² ≤ λ ∑_i ‖z_i‖²`. -/
theorem weighted_frame_psd {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (V : ∀ i, E i →ₗ[ℝ] F) (G : ι → ι → ℝ)
    (hV : ∀ i j (z : E i) (z' : E j), |inner ℝ (V i z) (V j z')| ≤ G i j * ‖z‖ * ‖z'‖)
    (d : ι → ℝ) {lam : ℝ}
    (hpsd : (Matrix.of fun i j => (if i = j then lam else 0) - √(d i) * G i j * √(d j)).PosSemidef)
    (z : ∀ i, E i) :
    ‖∑ i, √(d i) • V i (z i)‖ ^ 2 ≤ lam * ∑ i, ‖z i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp only [inner_sum, real_inner_smul_left, real_inner_smul_right]
  have hq := quad_nonneg_of_posSemidef hpsd (fun i => ‖z i‖)
  simp only [Matrix.of_apply] at hq
  have hdiag : ∑ i, ∑ j, ‖z i‖ * (if i = j then lam else 0) * ‖z j‖ = lam * ∑ i, ‖z i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [mul_ite, ite_mul, mul_zero, zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
    ring
  have hsplit : ∑ i, ∑ j, ‖z i‖ * ((if i = j then lam else 0) - √(d i) * G i j * √(d j)) * ‖z j‖ =
      ∑ i, ∑ j, ‖z i‖ * (if i = j then lam else 0) * ‖z j‖ -
        ∑ i, ∑ j, √(d i) * √(d j) * (G i j * ‖z i‖ * ‖z j‖) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hsplit, hdiag] at hq
  refine le_trans ?_ (sub_nonneg.mp hq)
  refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
  have h := hV i j (z i) (z j)
  have hs : 0 ≤ √(d i) * √(d j) := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have e : √(d j) * (√(d i) * inner ℝ (V i (z i)) (V j (z j))) =
      (√(d i) * √(d j)) * inner ℝ (V i (z i)) (V j (z j)) := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans h) hs

section Schur

variable {Z : Type*} [Fintype Z] [DecidableEq Z]

omit [DecidableEq Z] in
/-- The quadratic form of a kernel operator: `⟨f, W f⟩_γ = ∑_{z,z'} (γf)(z) W(z,z') (γf)(z')`. -/
theorem kernelForm_quad (γ : FiniteLaw Z) (W : Z → Z → ℝ) (f : Z → ℝ) :
    kernelForm γ γ W f f = ∑ z, ∑ z', (γ.weight z * f z) * W z z' * (γ.weight z' * f z') := by
  simp only [kernelForm, LinearMap.mk₂_apply]
  exact Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun z' _ => by ring))

omit [DecidableEq Z] in
/-- **`lem:swapped-rectangle` (b), general statement, lower bound.** If `Γ ⪰ 0` (as a matrix) and
`W ⪰ 0` on `L²(γ)` with symmetric kernel, then `Γ ∘ W ⪰ 0`. -/
theorem schur_operator_nonneg (γ : FiniteLaw Z) (hγ : ∀ z, 0 < γ.weight z) (Γ W : Z → Z → ℝ)
    (hΓ : (Matrix.of Γ).PosSemidef) (hWs : ∀ z z', W z z' = W z' z)
    (hW : ∀ f, 0 ≤ kernelForm γ γ W f f) (f : Z → ℝ) :
    0 ≤ kernelForm γ γ (fun z z' => Γ z z' * W z z') f f := by
  have hWm : (Matrix.of W).PosSemidef := by
    refine posSemidef_of_quad (fun i j => by simp only [Matrix.of_apply]; exact hWs i j)
      (fun x => ?_)
    have h := hW (fun z => x z / γ.weight z)
    rw [kernelForm_quad] at h
    have e : ∑ i, ∑ j, x i * Matrix.of W i j * x j = ∑ z, ∑ z', γ.weight z * (x z / γ.weight z) *
        W z z' * (γ.weight z' * (x z' / γ.weight z')) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      have h1 : γ.weight i * (x i / γ.weight i) = x i := by field_simp [(hγ i).ne']
      have h2 : γ.weight j * (x j / γ.weight j) = x j := by field_simp [(hγ j).ne']
      rw [h1, h2, Matrix.of_apply]
    rw [e]
    exact h
  have hprod := (hΓ.hadamard hWm)
  have h := quad_nonneg_of_posSemidef hprod (fun z => γ.weight z * f z)
  rw [kernelForm_quad]
  have e : ∑ i, ∑ j, (γ.weight i * f i) * (Matrix.of Γ ⊙ Matrix.of W) i j * (γ.weight j * f j) =
      ∑ z, ∑ z', (γ.weight z * f z) * (Γ z z' * W z z') * (γ.weight z' * f z') := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hadamard_apply, Matrix.of_apply, Matrix.of_apply]
  rw [e] at h
  exact h

/-- **`lem:swapped-rectangle` (b), general statement, upper bound.** If moreover `Γ(z, z) ≤ c`
and `W ⪯ aI`, then `Γ ∘ W ⪯ caI`. -/
theorem schur_operator_le (γ : FiniteLaw Z) (hγ : ∀ z, 0 < γ.weight z) (Γ W : Z → Z → ℝ)
    (hΓ : (Matrix.of Γ).PosSemidef) (hWs : ∀ z z', W z z' = W z' z) {a c : ℝ}
    (hc : ∀ z, Γ z z ≤ c) (ha : 0 ≤ a)
    (hW : ∀ f, kernelForm γ γ W f f ≤ a * nrm γ f ^ 2) (f : Z → ℝ) :
    kernelForm γ γ (fun z z' => Γ z z' * W z z') f f ≤ c * a * nrm γ f ^ 2 := by
  -- the matrix `a D - W` with `D = diag(1/γ)` is positive semidefinite
  set M : Z → Z → ℝ := fun z z' => (if z = z' then a / γ.weight z else 0) - W z z' with hM
  have hnrm : ∀ g : Z → ℝ, nrm γ g ^ 2 = ∑ z, γ.weight z * g z ^ 2 := by
    intro g
    rw [nrm_sq_expect]
    rfl
  have hMm : (Matrix.of M).PosSemidef := by
    refine posSemidef_of_quad (fun i j => ?_) (fun x => ?_)
    · simp only [Matrix.of_apply, hM]
      by_cases hij : i = j
      · subst hij; rfl
      · rw [ite_eq_right hij, ite_eq_right (Ne.symm hij), hWs]
    · have h := hW (fun z => x z / γ.weight z)
      rw [kernelForm_quad, hnrm] at h
      have e1 : ∑ i, ∑ j, x i * Matrix.of M i j * x j =
          ∑ i, x i * (a / γ.weight i) * x i - ∑ i, ∑ j, x i * W i j * x j := by
        simp only [Matrix.of_apply, hM, mul_sub, sub_mul, Finset.sum_sub_distrib]
        congr 1
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [mul_ite, ite_mul, mul_zero, zero_mul]
        rw [Finset.sum_ite_eq]
        simp only [Finset.mem_univ, ite_true]
      have e2 : ∑ i, ∑ j, γ.weight i * (x i / γ.weight i) * W i j *
          (γ.weight j * (x j / γ.weight j)) = ∑ i, ∑ j, x i * W i j * x j := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        field_simp [(hγ i).ne', (hγ j).ne']
      have e3 : a * ∑ z, γ.weight z * (x z / γ.weight z) ^ 2 =
          ∑ i, x i * (a / γ.weight i) * x i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        field_simp [(hγ i).ne']
      rw [e2, e3] at h
      rw [e1]
      linarith
  have hprod := hΓ.hadamard hMm
  have h := quad_nonneg_of_posSemidef hprod (fun z => γ.weight z * f z)
  have e4 : ∑ i, ∑ j, (γ.weight i * f i) * (Matrix.of Γ ⊙ Matrix.of M) i j * (γ.weight j * f j) =
      ∑ i, (γ.weight i * f i) * (Γ i i * (a / γ.weight i)) * (γ.weight i * f i) -
        kernelForm γ γ (fun z z' => Γ z z' * W z z') f f := by
    rw [kernelForm_quad]
    simp only [hadamard_apply, Matrix.of_apply, hM, mul_sub, sub_mul, Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [mul_ite, ite_mul, mul_zero, zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
  rw [e4] at h
  have e5 : ∑ i, (γ.weight i * f i) * (Γ i i * (a / γ.weight i)) * (γ.weight i * f i) =
      a * ∑ i, Γ i i * (γ.weight i * f i ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    field_simp [(hγ i).ne']
  rw [e5] at h
  have h6 : a * ∑ i, Γ i i * (γ.weight i * f i ^ 2) ≤ c * a * nrm γ f ^ 2 := by
    rw [hnrm]
    have hle : ∑ i, Γ i i * (γ.weight i * f i ^ 2) ≤ c * ∑ z, γ.weight z * f z ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hc i)
        (mul_nonneg (hγ i).le (sq_nonneg _)))
    calc a * ∑ i, Γ i i * (γ.weight i * f i ^ 2) ≤ a * (c * ∑ z, γ.weight z * f z ^ 2) :=
          mul_le_mul_of_nonneg_left hle ha
      _ = c * a * ∑ z, γ.weight z * f z ^ 2 := by ring
  linarith

end Schur

end Sarkozy.Cuts
