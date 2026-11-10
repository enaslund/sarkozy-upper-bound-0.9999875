module

public import Sarkozy.Angles.AllPinSub

/-!
# `lem:mid:allpin` with elementary matrix hypotheses

`allpin_elementary` restates the second statement of `lem:mid:allpin` (`allpin_submatrix`)
with the matrix data in elementary form, for use without Mathlib's matrix norms:
* the influence matrix is a function `E : U → U → ℝ` on a free set `F : Finset U`;
* the operator-norm bound `‖E_{FF}‖ ≤ e < 1` is the inequality
  `∑ i ∈ F, (∑ j ∈ F, E i j * x j) ^ 2 ≤ e ^ 2 * ∑ j ∈ F, x j ^ 2` for all `x`;
* `(I - E_{FF})⁻¹` is any `Q` with `Q i j = [i = j] + ∑ l ∈ F, E i l * Q l j` on `F × F`.

These are the conventions of `Sarkozy.Influence` (`OpBound F F E e` unfolds to the second
item). The subspaces are indexed by the subsets of a smaller free set `F' ⊆ F`.
-/

@[expose] public section

open scoped InnerProductSpace Matrix.Norms.L2Operator
open Matrix

namespace Sarkozy.Angles

variable {U : Type*} [DecidableEq U]

/-- The `ℓ²` operator norm of `E_{FF}` (as a matrix indexed by the subtype `F`) is at most `e`
when `∑ i ∈ F, (∑ j ∈ F, E i j * x j) ^ 2 ≤ e ^ 2 * ∑ j ∈ F, x j ^ 2` for all `x`. -/
theorem norm_restrict_le (F : Finset U) (E : U → U → ℝ) {e : ℝ} (he0 : 0 ≤ e)
    (hE : ∀ x : U → ℝ, ∑ i ∈ F, (∑ j ∈ F, E i j * x j) ^ 2 ≤ e ^ 2 * ∑ j ∈ F, x j ^ 2) :
    ‖(Matrix.of fun a b : F => E a b)‖ ≤ e := by
  rw [cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ he0 fun X => ?_
  set x : U → ℝ := fun u => if h : u ∈ F then X.ofLp ⟨u, h⟩ else 0 with hx
  have hxF : ∀ b : F, x b = X.ofLp b := fun b => by simp [hx, b.2]
  have h := hE x
  -- rewrite both sides of `h` as sums over the subtype `F`
  have hl : ∀ i, ∑ j ∈ F, E i j * x j = ∑ b : F, E i b * X.ofLp b := fun i => by
    rw [← Finset.sum_coe_sort F]
    exact Finset.sum_congr rfl fun b _ => by rw [hxF]
  rw [← Finset.sum_coe_sort F (fun i => (∑ j ∈ F, E i j * x j) ^ 2),
    ← Finset.sum_coe_sort F (fun j => x j ^ 2)] at h
  simp only [hl, hxF] at h
  have hY : ‖toEuclideanCLM (n := F) (𝕜 := ℝ) (Matrix.of fun a b : F => E a b) X‖ ^ 2 =
      ∑ a : F, (∑ b : F, E a b * X.ofLp b) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ofLp_toEuclideanCLM, Real.norm_eq_abs, sq_abs]
    simp [Matrix.mulVec, dotProduct]
  have hX : ‖X‖ ^ 2 = ∑ b : F, X.ofLp b ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun b _ => by rw [Real.norm_eq_abs, sq_abs]
  have hsq : ‖toEuclideanCLM (n := F) (𝕜 := ℝ) (Matrix.of fun a b : F => E a b) X‖ ^ 2 ≤
      (e * ‖X‖) ^ 2 := by
    rw [hY, mul_pow, hX]
    exact h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg he0 (norm_nonneg _))
    two_ne_zero).mp hsq

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **`lem:mid:allpin`, second statement, elementary form.** Let `F' ⊆ F` be finite sets of
vertices, `𝓔 : U → U → ℝ` symmetric with nonnegative entries and zero diagonal, with
`∑ i ∈ F, (∑ j ∈ F, 𝓔 i j * x j) ^ 2 ≤ e ^ 2 * ∑ j ∈ F, x j ^ 2` for some `0 ≤ e < 1`, and let
`Q` satisfy `Q = I + 𝓔 Q` on `F × F`. Let `V[𝒴]`, for `𝒴 ⊆ F'`, satisfy
`V[𝒴] ⊓ V[𝒴'] = V[𝒴 ∪ 𝒴']` and `cos∠(V[{i}], V[{j}]) ≤ 𝓔 i j`. Then for distinct
`i, j ∈ F'`, `cos∠(V[F' ∖ {j}], V[F' ∖ {i}]) ≤ Q i j`. -/
theorem allpin_elementary (F F' : Finset U) (hF' : F' ⊆ F) (𝓔 : U → U → ℝ)
    (hsymm : ∀ i j, 𝓔 i j = 𝓔 j i) (hdiag : ∀ i, 𝓔 i i = 0) (hnn : ∀ i j, 0 ≤ 𝓔 i j)
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1)
    (hE : ∀ x : U → ℝ, ∑ i ∈ F, (∑ j ∈ F, 𝓔 i j * x j) ^ 2 ≤ e ^ 2 * ∑ j ∈ F, x j ^ 2)
    (Q : U → U → ℝ)
    (hQ : ∀ i ∈ F, ∀ j ∈ F, Q i j = (if i = j then 1 else 0) + ∑ l ∈ F, 𝓔 i l * Q l j)
    (V : Finset F' → Submodule ℝ E)
    (hV : ∀ 𝒴 𝒴' : Finset F', V 𝒴 ⊓ V 𝒴' = V (𝒴 ∪ 𝒴'))
    (hcos : ∀ i j : F', i ≠ j → friedrichsCos (V {i}) (V {j}) ≤ 𝓔 i j)
    {i j : F'} (hne : i ≠ j) :
    friedrichsCos (V (Finset.univ \ {j})) (V (Finset.univ \ {i})) ≤ Q i j := by
  set Ebar : Matrix F F ℝ := Matrix.of fun a b : F => 𝓔 a b with hEbar
  set Qm : Matrix F F ℝ := Matrix.of fun a b : F => Q a b with hQm
  have hnorm : ‖Ebar‖ < 1 := (norm_restrict_le F 𝓔 he0 hE).trans_lt he1
  have hsymm' : Ebar.IsSymm := by
    ext a b
    simp [hEbar, hsymm]
  -- `Qm` is the inverse of `1 - Ebar`
  have hinv : (1 - Ebar)⁻¹ = Qm := by
    refine Matrix.inv_eq_right_inv ?_
    ext a b
    have hs : ∑ c : F, Ebar a c * Qm c b = ∑ l ∈ F, 𝓔 a l * Q l b := by
      rw [← Finset.sum_coe_sort F (fun l => 𝓔 a l * Q l b)]
      rfl
    have hq := hQ a a.2 b b.2
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.one_apply]
    rw [Matrix.mul_apply, hs]
    simp only [hQm, Matrix.of_apply, Subtype.ext_iff]
    linarith
  -- the inclusion `F' → F`
  let f : F' → F := fun a => ⟨a.1, hF' a.2⟩
  have hf : Function.Injective f := fun a b h => by
    have h' : (f a).1 = (f b).1 := congrArg Subtype.val h
    exact Subtype.ext h'
  have h := allpin_submatrix V hV Ebar hsymm' (fun a => hdiag a) (fun a b => hnn a b) hnorm f hf
    (fun a b hab => hcos a b hab) hne
  have h2 := h.1.trans h.2
  rwa [hinv] at h2

end Sarkozy.Angles
