module

public import Sarkozy.FiveType.JointBlocks
public import Sarkozy.FiveType.Rows
public import Sarkozy.Reflection.Matrix
public import Sarkozy.Extraction.JointRowSplit

/-!
# Weighted kernel matrices and block tensorization

Tools for `lem:joint-rows` (b), (c) (`paper/sections/16_extraction.tex`).

A kernel `A` relative to `μ ⊗ μ` is the matrix `wk μ A = (μ(x) μ(y) A(x, y))`, the identity of
`L²(μ)` is `wI μ = diag(μ)`, `J` is `wJ μ` and `I - J` is `wQ μ`. Then quadratic forms are those of
`L²(μ)` (`dot_wk`, `dot_wI`, `dot_wQ`), with no full-support assumption.

* Per-prime positive semidefinite `2 × 2` blocks:
  - `psd_blockJ`: `(J J; J J) ⪰ 0`;
  - `psd_blockNorm`: `(eQ C; Cᵀ eQ) ⪰ 0` when `C` annihilates the constants and `‖C‖ ≤ e`;
  - `psd_blockJoint`: `(E + KQ C; Cᵀ E + KQ) ⪰ 0` when the joint block of `(E, C)` is
    `⪰ -k I`, `k ≤ K`, and `E`, `C` annihilate the constants.
* `psd_tprod_blocks`: **block tensorization** (the block-Gram lemma, `lem:record:block-gram`):
  entrywise products over the primes of positive semidefinite `2 × 2` blocks are positive
  semidefinite (Schur's product theorem, `matrix_prod_posSemidef`).
-/

@[expose] public section

open scoped BigOperators
open Matrix

namespace Sarkozy.JointRows

open Sarkozy.FiveType

section Weighted

variable {X : Type*} [Fintype X]

/-- The weighted matrix `μ(x) μ(y) A(x, y)` of a kernel relative to `μ ⊗ μ`. -/
def wk (μ : FiniteLaw X) (A : X → X → ℝ) : Matrix X X ℝ :=
  fun x y => μ.weight x * μ.weight y * A x y

/-- The identity of `L²(μ)`: `diag(μ)`. -/
def wI [DecidableEq X] (μ : FiniteLaw X) : Matrix X X ℝ :=
  fun x y => if x = y then μ.weight x else 0

/-- `J`, the projection onto the constants. -/
def wJ (μ : FiniteLaw X) : Matrix X X ℝ := wk μ (fun _ _ => 1)

/-- `Q = I - J`. -/
def wQ [DecidableEq X] (μ : FiniteLaw X) : Matrix X X ℝ := wI μ - wJ μ

theorem dot_wk (μ : FiniteLaw X) (A : X → X → ℝ) (v w : X → ℝ) :
    v ⬝ᵥ (wk μ A *ᵥ w) = kf μ A v w := by
  simp only [dotProduct, mulVec, wk, kf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem dot_wI [DecidableEq X] (μ : FiniteLaw X) (v w : X → ℝ) :
    v ⬝ᵥ (wI μ *ᵥ w) = ip μ v w := by
  simp only [dotProduct, mulVec, wI, ip, FiniteLaw.expect]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x (fun y _ hy => by simp only [Ne.symm hy, ↓reduceIte, zero_mul])
    (fun h => absurd (Finset.mem_univ x) h)]
  simp only [↓reduceIte]
  ring

theorem kf_const_one (μ : FiniteLaw X) (v w : X → ℝ) :
    kf μ (fun _ _ => 1) v w = μ.expect v * μ.expect w := by
  simp only [kf, FiniteLaw.expect, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem dot_wJ (μ : FiniteLaw X) (v w : X → ℝ) :
    v ⬝ᵥ (wJ μ *ᵥ w) = μ.expect v * μ.expect w := by
  rw [wJ, dot_wk, kf_const_one]

/-- `⟨v, Qv⟩ = ‖v - E v‖²`. -/
theorem dot_wQ [DecidableEq X] (μ : FiniteLaw X) (v : X → ℝ) :
    v ⬝ᵥ (wQ μ *ᵥ v) = nrm μ (cen μ v) ^ 2 := by
  rw [wQ, sub_mulVec, dotProduct_sub, dot_wI, dot_wJ, ← ip_self_eq, ip_self_split]
  ring

theorem wk_transpose (μ : FiniteLaw X) (A : X → X → ℝ) :
    (wk μ A)ᵀ = wk μ (fun x y => A y x) := by
  ext x y
  simp only [transpose_apply, wk]
  ring

theorem wk_symm {μ : FiniteLaw X} {A : X → X → ℝ} (h : ∀ x y, A x y = A y x) :
    (wk μ A)ᵀ = wk μ A := by
  rw [wk_transpose]
  congr 1
  funext x y
  exact h y x

theorem wI_transpose [DecidableEq X] (μ : FiniteLaw X) : (wI μ)ᵀ = wI μ := by
  ext x y
  simp only [transpose_apply, wI]
  by_cases h : y = x
  · subst h; rfl
  · simp only [h, Ne.symm h, ↓reduceIte]

theorem wQ_transpose [DecidableEq X] (μ : FiniteLaw X) : (wQ μ)ᵀ = wQ μ := by
  rw [wQ, transpose_sub, wI_transpose, wJ, wk_symm (fun _ _ => rfl)]

theorem psd_wQ [DecidableEq X] (μ : FiniteLaw X) : (wQ μ).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
  · exact wQ_transpose μ
  · simp only [star_trivial]
    rw [dot_wQ]
    exact sq_nonneg _

theorem psd_wJ (μ : FiniteLaw X) : (wJ μ).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
  · exact wk_symm (fun _ _ => rfl)
  · simp only [star_trivial]
    rw [dot_wJ]
    exact mul_self_nonneg _

/-- The quadratic form of a `2 × 2` block matrix. -/
theorem dot_fromBlocks (A B C D : Matrix X X ℝ) (v w : X → ℝ) :
    Sum.elim v w ⬝ᵥ (fromBlocks A B C D *ᵥ Sum.elim v w) =
      v ⬝ᵥ (A *ᵥ v) + v ⬝ᵥ (B *ᵥ w) + (w ⬝ᵥ (C *ᵥ v) + w ⬝ᵥ (D *ᵥ w)) := by
  rw [fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, dotProduct_add]

omit [Fintype X] in
/-- A block matrix `(A B; Bᵀ D)` with symmetric diagonal blocks is symmetric. -/
theorem isHermitian_fromBlocks {A B D : Matrix X X ℝ} (hA : Aᵀ = A) (hD : Dᵀ = D) :
    (fromBlocks A B Bᵀ D).IsHermitian := by
  refine IsHermitian.fromBlocks ?_ ?_ ?_
  · exact hA
  · simp
  · exact hD

/-- Positive semidefiniteness of a block matrix from its quadratic form. -/
theorem psd_of_form {A B D : Matrix X X ℝ} (hA : Aᵀ = A) (hD : Dᵀ = D)
    (h : ∀ v w : X → ℝ, 0 ≤ v ⬝ᵥ (A *ᵥ v) + 2 * (v ⬝ᵥ (B *ᵥ w)) + w ⬝ᵥ (D *ᵥ w)) :
    (fromBlocks A B Bᵀ D).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_fromBlocks hA hD) fun z => ?_
  simp only [star_trivial]
  have hz : z = Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) := by funext i; cases i <;> rfl
  rw [hz, dot_fromBlocks]
  have ht : (z ∘ Sum.inr) ⬝ᵥ (Bᵀ *ᵥ (z ∘ Sum.inl)) = (z ∘ Sum.inl) ⬝ᵥ (B *ᵥ (z ∘ Sum.inr)) := by
    rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  rw [ht]
  have := h (z ∘ Sum.inl) (z ∘ Sum.inr)
  linarith

/-- A form bound is nonnegative. -/
theorem formBound_nonneg {μ : FiniteLaw X} {A : X → X → ℝ} {e : ℝ} (h : FormBound μ A e) :
    0 ≤ e := by
  have h1 := h (fun _ => 1) (fun _ => 1)
  have hn : nrm μ (fun _ => (1 : ℝ)) = 1 := by
    unfold nrm ip
    simp only [mul_one, FiniteLaw.expect_const, Real.sqrt_one]
  rw [hn, mul_one, mul_one] at h1
  exact le_trans (abs_nonneg _) h1

/-- `(J J; J J) ⪰ 0`. -/
theorem psd_blockJ (μ : FiniteLaw X) : (fromBlocks (wJ μ) (wJ μ) (wJ μ)ᵀ (wJ μ)).PosSemidef := by
  have hJ : (wJ μ)ᵀ = wJ μ := wk_symm (fun _ _ => rfl)
  refine psd_of_form hJ hJ fun v w => ?_
  rw [dot_wJ, dot_wJ, dot_wJ]
  nlinarith [sq_nonneg (μ.expect v + μ.expect w)]

/-- `(eQ C; Cᵀ eQ) ⪰ 0` when `C` annihilates the constants and `‖C‖ ≤ e`. -/
theorem psd_blockNorm [DecidableEq X] {μ : FiniteLaw X} {C : X → X → ℝ} {e : ℝ}
    (hC : Annihilates μ C)
    (hb : FormBound μ C e) :
    (fromBlocks (e • wQ μ) (wk μ C) (wk μ C)ᵀ (e • wQ μ)).PosSemidef := by
  have hQ : (e • wQ μ)ᵀ = e • wQ μ := by rw [transpose_smul, wQ_transpose]
  refine psd_of_form hQ hQ fun v w => ?_
  have he := formBound_nonneg hb
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul, dot_wQ, smul_mulVec, dotProduct_smul,
    smul_eq_mul, dot_wQ, dot_wk, kf_annihilates hC]
  have h1 := hb (cen μ v) (cen μ w)
  have h2 := neg_abs_le (kf μ C (cen μ v) (cen μ w))
  have h3 : 2 * (nrm μ (cen μ v) * nrm μ (cen μ w)) ≤
      nrm μ (cen μ v) ^ 2 + nrm μ (cen μ w) ^ 2 := by
    nlinarith [sq_nonneg (nrm μ (cen μ v) - nrm μ (cen μ w))]
  nlinarith [mul_le_mul_of_nonneg_left h3 he]

/-- `(E + KQ C; Cᵀ E + KQ) ⪰ 0` from the joint block of `(E, C)`. -/
theorem psd_blockJoint [DecidableEq X] {μ : FiniteLaw X} {E C : X → X → ℝ} {k K : ℝ}
    (hE : Annihilates μ E)
    (hC : Annihilates μ C) (hsym : ∀ x y, E x y = E y x) (hJ : Blocks.JointBlockLower μ E C k)
    (hk : k ≤ K) :
    (fromBlocks (wk μ E + K • wQ μ) (wk μ C) (wk μ C)ᵀ (wk μ E + K • wQ μ)).PosSemidef := by
  have hT : (wk μ E + K • wQ μ)ᵀ = wk μ E + K • wQ μ := by
    rw [transpose_add, wk_symm hsym, transpose_smul, wQ_transpose]
  refine psd_of_form hT hT fun v w => ?_
  simp only [add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [dot_wk, dot_wk, dot_wk, dot_wQ, dot_wQ, kf_annihilates hE v v, kf_annihilates hE w w,
    kf_annihilates hC v w]
  have h1 := hJ (cen μ v) (cen μ w)
  have hn : 0 ≤ nrm μ (cen μ v) ^ 2 + nrm μ (cen μ w) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hk hn]

end Weighted

/-! ## Block tensorization -/

section Tensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Xp : ι → Type*} [∀ i, Fintype (Xp i)]

/-- The entrywise product over the primes, `(⊗_i M_i)(x, y) = ∏_i M_i(x_i, y_i)`. -/
def tprod (M : ∀ i, Matrix (Xp i) (Xp i) ℝ) : Matrix ((i : ι) → Xp i) ((i : ι) → Xp i) ℝ :=
  fun x y => ∏ i, M i (x i) (y i)

/-- **Block tensorization**: entrywise products of positive semidefinite `2 × 2` blocks. -/
theorem psd_tprod_blocks (L B R : ∀ i, Matrix (Xp i) (Xp i) ℝ)
    (h : ∀ i, (fromBlocks (L i) (B i) (B i)ᵀ (R i)).PosSemidef) :
    (fromBlocks (tprod L) (tprod B) (tprod B)ᵀ (tprod R)).PosSemidef := by
  let pull (i : ι) : ((∀ i, Xp i) ⊕ (∀ i, Xp i)) → (Xp i ⊕ Xp i) :=
    Sum.map (fun x => x i) (fun x => x i)
  have hp : ∀ i, ((fromBlocks (L i) (B i) (B i)ᵀ (R i)).submatrix (pull i) (pull i)).PosSemidef :=
    fun i => (h i).submatrix _
  have := matrix_prod_posSemidef _ hp
  have heq : fromBlocks (tprod L) (tprod B) (tprod B)ᵀ (tprod R) =
      fun a b => ∏ j, (fromBlocks (L j) (B j) (B j)ᵀ (R j)).submatrix (pull j) (pull j) a b := by
    ext (x | x) (y | y) <;>
      simp [tprod, pull, Matrix.submatrix, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
        fromBlocks_apply₂₁, fromBlocks_apply₂₂, transpose_apply]
  rw [heq]
  exact this

/-- Entrywise products of positive semidefinite matrices. -/
theorem psd_tprod (M : ∀ i, Matrix (Xp i) (Xp i) ℝ) (h : ∀ i, (M i).PosSemidef) :
    (tprod M).PosSemidef := by
  have hp : ∀ i, ((M i).submatrix (fun x : (∀ i, Xp i) => x i) (fun x => x i)).PosSemidef :=
    fun i => (h i).submatrix _
  exact matrix_prod_posSemidef _ hp

theorem tprod_wk (νp : ∀ i, FiniteLaw (Xp i)) (A : ∀ i, Xp i → Xp i → ℝ) :
    tprod (fun i => wk (νp i) (A i)) = wk (Blocks.blockLaw νp) (Blocks.prodKernel A) := by
  ext x y
  simp only [tprod, wk, Blocks.blockLaw, Blocks.prodKernel, Finset.prod_mul_distrib]

theorem tprod_wI [∀ i, DecidableEq (Xp i)] (νp : ∀ i, FiniteLaw (Xp i)) :
    tprod (fun i => wI (νp i)) = wI (Blocks.blockLaw νp) := by
  ext x y
  simp only [tprod, wI, Blocks.blockLaw]
  by_cases h : x = y
  · subst h; simp
  · simp only [h, ↓reduceIte]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [hi, ↓reduceIte])

end Tensor

end Sarkozy.JointRows
