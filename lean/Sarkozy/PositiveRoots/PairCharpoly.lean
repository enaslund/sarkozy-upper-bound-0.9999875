module

public import Sarkozy.PositiveRoots.RootCubic

@[expose] public section

/-!
# The characteristic polynomial of `M_λ` (`lem:root-pair-matrix`)

`paper/sections/20b_positive_roots.tex`, `lem:root-pair-matrix`: on the eighteen coordinates (the
six singletons and the twelve supports of `lem:l20-star-matrix`(a), W3's `Idx18`),
`det(xI − M_λ) = x^{12}(x + λ/3)(x² − (λ/3)x − 4)(x³ − (λ/3)x² − 30x + 26λ/3)`
(`charpoly_Mlam18`), and the consequences for the negative eigenvalues (`neg_root_cases`).

The proof is the factorization of steps (1)–(4) in matrix form, as in W3's `charpoly_M18`:
`M_λ = P Q` with the six columns `P = [A, Z, e₀₁, e₄₅ | W, E]` and the rows
`Q = [Z^*; A^*; c e₄₅^*; c e₀₁^*| E^*; W^* + c E^*]`, `c = λ/3` (`Mlam18_eq`); the `6 × 6` matrix
`Q P` is block diagonal with the blocks
`B₄ = [[0, 15, 1, 1], [2, 0, 0, 0], [0, c, 0, c], [0, c, c, 0]]` and `B₂ = [[0, 1], [4, c]]`
(`Q_mul_P`), computed from the Gram table of `A, Z, W, E, e₀₁, e₄₅` (`gram_table`); then
`charpoly(PQ) = x^{12} charpoly(QP)` (`Matrix.charpoly_mul_comm_of_le`),
`charpoly B₄ = (x + c)(x³ − cx² − 30x + 26c)` (`charpoly_B4`) and `charpoly B₂ = x² − cx − 4`.
(The paper's unitary equivalence to `(3×3) ⊕ (2×2) ⊕ (−λ/3) ⊕ 0₁₂` is this factorization in an
orthonormal basis; `B₄` carries the `3 × 3` block and the eigenvalue `−λ/3`.)

`neg_root_cases`: a real negative root of the characteristic polynomial is `−g(λ)`, or a root
`≥ −2` of the quadratic, or `−λ/3`; so the least eigenvalue is `−g(λ)` and every other negative
eigenvalue is at least `−max(2, λ/3)` (`lem:root-pair-matrix`, "every other negative eigenvalue").
-/

namespace Sarkozy.PositiveRoots

open Finset Complex Sarkozy.SpectralC Sarkozy.SpectralD.StarMatrix Sarkozy.L20Cap
open scoped BigOperators ComplexConjugate

/-! ## The factorization -/

/-- **`M_λ` on the eighteen coordinates.** -/
noncomputable def Mlam18 (lam : ℝ) : Matrix Idx18 Idx18 ℂ :=
  Matrix.of fun a b => Mlam lam (emb18 a) (emb18 b)

/-- The six vectors `A, Z, W, E, e₀₁, e₄₅`. -/
noncomputable def vecs6c : Fin 6 → Idx → ℂ := ![vA, vZ, vW, vE, eS {0, 1}, eS {4, 5}]

def vR6c : Fin 6 → Fin 6 → ℤ := ![aZ, 0, wZ, 0, 0, 0]

def vI6c : Fin 6 → Fin 6 → ℤ := ![0, sZ, 0, 0, 0, 0]

def vS6c : Fin 6 → Finset (Fin 6) → ℤ :=
  ![0, fun S => ∏ k ∈ S, sZ k, 0, eSZ {2, 3}, eSZ {0, 1}, eSZ {4, 5}]

theorem vecs6c_eq (a : Fin 6) : vecs6c a = mkVec (vR6c a) (vI6c a) (vS6c a) := by
  fin_cases a <;> rfl

/-- The Gram table of `A, Z, W, E, e₀₁, e₄₅` on the eighteen coordinates. -/
def gramZ : Fin 6 → Fin 6 → ℤ :=
  ![![2, 0, 0, 0, 0, 0], ![0, 15, 0, 0, 1, 1], ![0, 0, 4, 0, 0, 0], ![0, 0, 0, 1, 0, 0],
    ![0, 1, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1]]

theorem gram_int : ∀ a b : Fin 6,
    (∑ i, (vR6c a i * vR6c b i + vI6c a i * vI6c b i) + ∑ S ∈ twelve, vS6c a S * vS6c b S =
      gramZ a b) ∧ ∑ i, (vR6c a i * vI6c b i - vI6c a i * vR6c b i) = 0 := by
  decide

/-- **The Gram table** `⟨X_a, X_b⟩` over the eighteen coordinates. -/
theorem gram_table (a b : Fin 6) : cip18 (vecs6c a) (vecs6c b) = (gramZ a b : ℂ) := by
  rw [vecs6c_eq, vecs6c_eq, cip18_mkVec, (gram_int a b).1, (gram_int a b).2]
  simp

/-- The coefficient of the row `i` of `Q` along the six vectors (conjugated). -/
noncomputable def rowCoef (c : ℂ) : Fin 4 ⊕ Fin 2 → Fin 6 → ℂ :=
  Sum.elim ![![0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, c], ![0, 0, 0, 0, c, 0]]
    ![![0, 0, 0, 1, 0, 0], ![0, 0, 1, c, 0, 0]]

/-- The vector of the column `j` of `P`. -/
def colIdx : Fin 4 ⊕ Fin 2 → Fin 6 := Sum.elim ![0, 1, 4, 5] ![2, 3]

/-- `P = [A, Z, e₀₁, e₄₅ | W, E]`. -/
noncomputable def Pm : Matrix Idx18 (Fin 4 ⊕ Fin 2) ℂ :=
  Matrix.of fun k j => vecs6c (colIdx j) (emb18 k)

/-- `Q = [Z^*; A^*; c e₄₅^*; c e₀₁^* | E^*; W^* + cE^*]`. -/
noncomputable def Qm (c : ℂ) : Matrix (Fin 4 ⊕ Fin 2) Idx18 ℂ :=
  Matrix.of fun i l => ∑ a, rowCoef c i a * conj (vecs6c a (emb18 l))

/-- **`M_λ = P Q`** on the eighteen coordinates (`c = λ/3`). -/
theorem Mlam18_eq (lam : ℝ) : Mlam18 lam = Pm * Qm ((lam / 3 : ℝ) : ℂ) := by
  ext a b
  simp [Mlam18, Pm, Qm, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_four,
    Fin.sum_univ_two, Fin.sum_univ_six, rowCoef, colIdx, vecs6c, Mlam, softM_D20_eq, pairC]
  ring

/-- The entries of `Q P` from the Gram table. -/
theorem QP_apply (c : ℂ) (i j : Fin 4 ⊕ Fin 2) :
    (Qm c * Pm) i j = ∑ a, rowCoef c i a * (gramZ a (colIdx j) : ℂ) := by
  simp only [Qm, Pm, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← gram_table, cip18, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The block `B₄` (carrying the `3 × 3` block of the paper and the eigenvalue `−c`). -/
noncomputable def B4 (c : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 15, 1, 1; 2, 0, 0, 0; 0, c, 0, c; 0, c, c, 0]

/-- The block `B₂` (the `2 × 2` block of the paper). -/
noncomputable def B2 (c : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 4, c]

/-- **`Q P = B₄ ⊕ B₂`**. -/
theorem Q_mul_P (c : ℂ) : Qm c * Pm = Matrix.fromBlocks (B4 c) 0 0 (B2 c) := by
  ext i j
  rw [QP_apply]
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rowCoef, colIdx, gramZ, Fin.sum_univ_six, B4, B2]

open Polynomial in
/-- **`charpoly B₄ = (x + c)(x³ − cx² − 30x + 26c)`.** -/
theorem charpoly_B4 (c : ℂ) :
    (B4 c).charpoly = (X + C c) * (X ^ 3 - C c * X ^ 2 - 30 * X + 26 * C c) := by
  have s10 : Fin.succAbove (1 : Fin 4) (0 : Fin 3) = 0 := rfl
  have s11 : Fin.succAbove (1 : Fin 4) (1 : Fin 3) = 2 := rfl
  have s12 : Fin.succAbove (1 : Fin 4) (2 : Fin 3) = 3 := rfl
  have s20 : Fin.succAbove (2 : Fin 4) (0 : Fin 3) = 0 := rfl
  have s21 : Fin.succAbove (2 : Fin 4) (1 : Fin 3) = 1 := rfl
  have s22 : Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 := rfl
  have s31 : Fin.succAbove (Fin.succ (2 : Fin 3)) (1 : Fin 3) = 1 := rfl
  have s32 : Fin.succAbove (Fin.succ (2 : Fin 3)) (2 : Fin 3) = 2 := rfl
  have e15 : (C (15 : ℂ) : ℂ[X]) = 15 := map_ofNat C 15
  have e2 : (C (2 : ℂ) : ℂ[X]) = 2 := map_ofNat C 2
  unfold B4
  rw [Matrix.charpoly, Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.det_fin_three, Matrix.charmatrix_apply,
    Matrix.submatrix_apply, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Matrix.diagonal_apply,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.zero_succAbove, s10, s11, s12, s20, s21, s22,
    s31, s32]
  simp
  rw [e15, e2]
  ring

open Polynomial in
/-- **`charpoly B₂ = x² − cx − 4`.** -/
theorem charpoly_B2 (c : ℂ) : (B2 c).charpoly = X ^ 2 - C c * X - 4 := by
  unfold B2
  rw [Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, zero_add, zero_mul, one_mul, zero_sub]
  rw [map_neg, show (C (4 : ℂ) : ℂ[X]) = 4 from map_ofNat C 4]
  ring

open Polynomial in
/-- **`lem:root-pair-matrix`, the characteristic polynomial**: on the eighteen coordinates,
`det(xI − M_λ) = x^{12}(x + λ/3)(x² − (λ/3)x − 4)(x³ − (λ/3)x² − 30x + 26λ/3)`. -/
theorem charpoly_Mlam18 (lam : ℝ) :
    (Mlam18 lam).charpoly = X ^ 12 * (X + C ((lam / 3 : ℝ) : ℂ)) *
      (X ^ 2 - C ((lam / 3 : ℝ) : ℂ) * X - 4) *
      (X ^ 3 - C ((lam / 3 : ℝ) : ℂ) * X ^ 2 - 30 * X + 26 * C ((lam / 3 : ℝ) : ℂ)) := by
  have hle : Fintype.card (Fin 4 ⊕ Fin 2) ≤ Fintype.card Idx18 := by
    rw [card_Idx18]
    simp
  rw [Mlam18_eq, Matrix.charpoly_mul_comm_of_le Pm (Qm _) hle, Q_mul_P,
    Matrix.charpoly_fromBlocks_zero₁₂, charpoly_B4, charpoly_B2, card_Idx18]
  have h6 : Fintype.card (Fin 4 ⊕ Fin 2) = 6 := by simp
  rw [h6]
  norm_num
  ring

/-! ## The negative eigenvalues -/

/-- **The negative roots of the characteristic polynomial** (`lem:root-pair-matrix`): for
`λ ≥ 0`, a real `x < 0` with `det(xI − M_λ) = 0` is `−g(λ)` (the cubic), or a root of
`x² − (λ/3)x − 4` and then `x ≥ −2`, or `x = −λ/3`. Hence the least eigenvalue is `−g(λ)` (for
`λ ≤ 3√26`, `−max(2, λ/3) > −g(λ)`) and every other negative eigenvalue is `≥ −max(2, λ/3)`. -/
theorem neg_root_cases {lam x : ℝ} (hlam : 0 ≤ lam) (hx : x < 0)
    (hroot : (Mlam18 lam).charpoly.eval (x : ℂ) = 0) :
    x = -gRoot lam ∨ -2 ≤ x ∨ x = -(lam / 3) := by
  rw [charpoly_Mlam18] at hroot
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_ofNat] at hroot
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne
  rcases mul_eq_zero.mp hroot with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) hx0
      · -- `x + λ/3 = 0`
        right; right
        have : ((x + lam / 3 : ℝ) : ℂ) = 0 := by push_cast at h ⊢; exact h
        have := Complex.ofReal_eq_zero.mp this
        linarith
    · -- the quadratic: `x² − (λ/3)x − 4 = 0` with `x < 0` gives `x ≥ −2`
      right; left
      have hr : ((x ^ 2 - lam / 3 * x - 4 : ℝ) : ℂ) = 0 := by push_cast at h ⊢; exact h
      have hq := Complex.ofReal_eq_zero.mp hr
      by_contra hlt
      push Not at hlt
      have : 4 < x ^ 2 := by nlinarith
      have : 0 ≤ -(lam / 3 * x) := by nlinarith
      linarith
  · -- the cubic: `x = −g` with `3g³ + λg² − 90g − 26λ = 0`
    left
    have hr : ((x ^ 3 - lam / 3 * x ^ 2 - 30 * x + 26 * (lam / 3) : ℝ) : ℂ) = 0 := by
      push_cast at h ⊢; exact h
    have hc := Complex.ofReal_eq_zero.mp hr
    have hg : rootCubic lam (-x) = 0 := by
      unfold rootCubic
      nlinarith
    have := gRoot_unique hlam (by linarith) hg
    linarith

end Sarkozy.PositiveRoots
