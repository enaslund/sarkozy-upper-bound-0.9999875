module

public import Sarkozy.OpsFeature.StarKernel

@[expose] public section

/-!
# The unit tables label by label (`lem:oct24:mask-schur`(a))

`paper/sections/23_envelopes.tex`, `lem:oct24:mask-schur`(a): `Lift(D)` replaces, in every factor,
the unit `e_aa` of a singleton label by `V_a V_a^*` and the scalar units `e_33`, `e_44` by `Q₁₂`,
`Q₀₁`; the singleton sectors carry `Ξ_p = (V_0, V_1, V_2, A_3°/r_p, 0)` (`eq:signed-star`).

The hypothesis `hUY` of `hdom_of_table_paley(_blocks)` asks, at every block, that the diagonal
blocks of the unit table dominate those of the Gram table of the sector maps. **`hUY_of_labels`**
reduces it to one inequality per label `a`:
`U(a, a) ⪰ ∑_p Ξ_{p,a} Ξ_{p,a}^*` (as kernels), that is `V_a V_a^* ⪰ ∑_p V_a P_{{p}} V_a^*` for
`a = 0, 1, 2` and `Q₁₂ ⪰ ∑_p (A_3°/r_p)(A_3°/r_p)^*` for `a = 3`.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.OpsFeature

section UnitTable

variable {X : Type*} {L O : X → Type*} [∀ b, Fintype (L b)] [∀ b, DecidableEq (L b)]
  [∀ b, Fintype (O b)]

/-- **`hUY` label by label**: the diagonal blocks of `CU − G` dominate `0` if each label block
`(CU − G)(a, a)` does. -/
theorem hUY_of_labels (CU G : ∀ b, Matrix (L b × O b) (L b × O b) ℝ) (b : X)
    (h : ∀ a : L b,
      (Matrix.of fun x y : O b => CU b (a, x) (a, y) - G b (a, x) (a, y)).PosSemidef) :
    (maskT (fun b => (id : L b → L b)) CU b -
      maskT (fun b => (id : L b → L b)) G b).PosSemidef := by
  have e : maskT (fun b => (id : L b → L b)) CU b - maskT (fun b => (id : L b → L b)) G b =
      Matrix.of fun P Q => if P.1 = Q.1 then CU b P Q - G b P Q else 0 := by
    ext P Q
    simp only [maskT, id, Matrix.sub_apply, Matrix.of_apply]
    split_ifs <;> ring
  rw [e]
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun ξ => ?_
  · ext P Q
    simp only [conjTranspose_apply, star_trivial, Matrix.of_apply]
    obtain ⟨a, x⟩ := P
    obtain ⟨a', y⟩ := Q
    by_cases hq : a = a'
    · subst hq
      have hs := congrFun (congrFun (h a).1 x) y
      simp only [conjTranspose_apply, star_trivial, Matrix.of_apply] at hs
      simp only [↓reduceIte, hs]
    · simp only [hq, Ne.symm hq, ↓reduceIte]
  · have e2 : star ξ ⬝ᵥ ((Matrix.of fun P Q : L b × O b =>
          if P.1 = Q.1 then CU b P Q - G b P Q else 0) *ᵥ ξ)
        = ∑ a : L b, star (fun x => ξ (a, x)) ⬝ᵥ
          ((Matrix.of fun x y : O b => CU b (a, x) (a, y) - G b (a, x) (a, y)) *ᵥ
            fun x => ξ (a, x)) := by
      simp only [dotProduct, mulVec, star_trivial, Matrix.of_apply]
      rw [Fintype.sum_prod_type]
      refine sum_congr rfl fun a _ => sum_congr rfl fun x _ => ?_
      congr 1
      rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
      · simp only [↓reduceIte]
      · intro a' _ ha'
        simp only [Ne.symm ha', ↓reduceIte, zero_mul, sum_const_zero]
      · simp
    rw [e2]
    exact sum_nonneg fun a _ => (h a).dotProduct_mulVec_nonneg _

/-- **A singleton label `a = 0, 1, 2`** (Bessel): if `U(a, a) = V Vᵀ` (the kernel of `V_a V_a^*`,
`V` in an orthonormal basis of the label space) and the sector maps are `Ξ_{p,a} = V S_p` with
`∑_p S_p S_pᵀ ⪯ I` (the singleton sectors are orthogonal), then `U(a, a) ⪰ ∑_p Ξ_{p,a} Ξ_{p,a}ᵀ`,
the label inequality of `hUY_of_labels`. -/
theorem gram_le_of_bessel {O W S : Type*} [Fintype O] [Fintype W] [DecidableEq W] [Fintype S]
    {Z : S → Type*} [∀ p, Fintype (Z p)] (V : Matrix O W ℝ) (Sp : ∀ p, Matrix W (Z p) ℝ)
    (hB : (1 - ∑ p, Sp p * (Sp p)ᴴ).PosSemidef) :
    (V * Vᴴ - ∑ p, (V * Sp p) * (V * Sp p)ᴴ).PosSemidef := by
  have e : V * Vᴴ - ∑ p, (V * Sp p) * (V * Sp p)ᴴ = V * (1 - ∑ p, Sp p * (Sp p)ᴴ) * Vᴴ := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_sum, Matrix.sum_mul,
      conjTranspose_mul, Matrix.mul_assoc]
  rw [e]
  exact hB.mul_mul_conjTranspose_same V

end UnitTable

end Sarkozy.OpsFeature
