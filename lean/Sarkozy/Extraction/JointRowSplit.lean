module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Data.Matrix.Block
public import Mathlib.Algebra.Order.Star.Real

@[expose] public section

/-!
# The joint fluctuation in a positive row (`cor:joint-row-split`, first assertion)

`paper/sections/16_extraction.tex`, `cor:joint-row-split`. In `lem:joint-rows`(b) let
`h ≥ 0` and `𝗄 ≥ h` satisfy `E ⪰ −hI` and `(E C; C* E) ⪰ −𝗄 I`. If `0 ≤ m ≤ H` and
`a_S ≥ H a_D ≥ 0`, then

  `(a_S E   m a_D C; m a_D C*   a_S E) ⪰ −(h a_S + H a_D (𝗄 − h)) I`.

The proof is the paper's: the matrix is `m a_D` copies of the joint block plus
`a_S − m a_D` copies of `diag(E, E)`, both coefficients being nonnegative; its lower bound is
`−(m a_D 𝗄 + (a_S − m a_D) h) = −(h a_S + m a_D (𝗄 − h))`, and `m ≤ H` is used only after
`𝗄 − h ≥ 0`.

The statement is for real matrices (`Cᵀ = C*`), with `X ⪰ −c I` written
`(X + c • 1).PosSemidef`. The corollary's second assertion (the replacement of `C` by
`T_F − U_L ⊗ U_R`) is `lem:joint-rows`(c) multiplied by `m a_D ≤ H a_D`; it is not
formalized here.
-/

open Matrix

namespace Sarkozy.Extraction

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- A block-diagonal matrix with a positive semidefinite block twice is positive
semidefinite. -/
theorem posSemidef_fromBlocks_diag {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    (fromBlocks A 0 0 A).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact IsHermitian.fromBlocks hA.isHermitian (by simp) hA.isHermitian
  · intro x
    have h1 := hA.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
    have h2 := hA.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
    have hx : x = Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) := by
      funext i; cases i <;> rfl
    rw [hx, fromBlocks_mulVec]
    simp only [Matrix.zero_mulVec, add_zero, zero_add, star_trivial, Sum.elim_comp_inl,
      Sum.elim_comp_inr]
    rw [sumElim_dotProduct_sumElim]
    simp only [star_trivial] at h1 h2
    exact add_nonneg h1 h2

/-- **`cor:joint-row-split`** (first assertion). -/
theorem joint_row_split {E C : Matrix n n ℝ} {h k m H aS aD : ℝ}
    (hk : h ≤ k) (hE : (E + h • (1 : Matrix n n ℝ)).PosSemidef)
    (hJ : (fromBlocks E C Cᵀ E + k • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)).PosSemidef)
    (hm0 : 0 ≤ m) (hmH : m ≤ H) (haD : 0 ≤ aD) (haS : H * aD ≤ aS) :
    (fromBlocks (aS • E) ((m * aD) • C) ((m * aD) • Cᵀ) (aS • E) +
        (h * aS + H * aD * (k - h)) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)).PosSemidef := by
  have hmaD : 0 ≤ m * aD := mul_nonneg hm0 haD
  have hrest : 0 ≤ aS - m * aD := by nlinarith
  have hD := posSemidef_fromBlocks_diag hE
  have hextra : 0 ≤ (H - m) * aD * (k - h) :=
    mul_nonneg (mul_nonneg (by linarith) haD) (by linarith)
  have hsum := ((hJ.smul hmaD).add (hD.smul hrest)).add
    ((Matrix.PosSemidef.one (R := ℝ) (n := n ⊕ n)).smul hextra)
  convert hsum using 1
  ext (i | i) (j | j) <;>
    simp only [Matrix.add_apply, Matrix.smul_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.one_apply, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq, ite_false, Matrix.zero_apply, smul_eq_mul, mul_zero, add_zero] <;>
    split_ifs <;> ring

end Sarkozy.Extraction
