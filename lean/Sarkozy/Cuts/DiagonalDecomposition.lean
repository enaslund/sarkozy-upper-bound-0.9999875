module

public import Sarkozy.Cuts.ProjectedDiagonal

/-! Orthogonal constant, variable-diagonal, and off-diagonal pieces in the auxiliary pair space. -/

@[expose] public section

namespace Sarkozy.Cuts

open Finset Sarkozy.Recentering

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ]

noncomputable def diagonalMean (F : Λ × Λ → ℝ) : ℝ :=
  (FiniteLaw.uniform Λ).expect fun a => F (a, a)

noncomputable def diagonalFluctuation (F : Λ × Λ → ℝ) (a : Λ) : ℝ := F (a, a) - diagonalMean F

noncomputable def constantDiagonalPart (F : Λ × Λ → ℝ) (z : Λ × Λ) : ℝ :=
  diagonalMean F / ((Fintype.card Λ : ℝ) - 1) * projectedDiagonal (fun _ : Λ => 1) z.1 z.2

noncomputable def variableDiagonalPart (F : Λ × Λ → ℝ) (z : Λ × Λ) : ℝ :=
  ((Fintype.card Λ : ℝ) - 2)⁻¹ * projectedDiagonal (diagonalFluctuation F) z.1 z.2

noncomputable def offDiagonalPart (F : Λ × Λ → ℝ) (z : Λ × Λ) : ℝ :=
  F z - constantDiagonalPart F z - variableDiagonalPart F z

omit [DecidableEq Λ] in
theorem diagonalFluctuation_mean (F : Λ × Λ → ℝ) :
    (FiniteLaw.uniform Λ).expect (diagonalFluctuation F) = 0 := by
  change (FiniteLaw.uniform Λ).expect (fun a => F (a, a) - diagonalMean F) = 0
  rw [FiniteLaw.expect_sub, FiniteLaw.expect_const]
  exact sub_self _

theorem constantDiagonalPart_rows (F : Λ × Λ → ℝ) (a : Λ) :
    (FiniteLaw.uniform Λ).expect (fun b => constantDiagonalPart F (a, b)) = 0 := by
  simp only [constantDiagonalPart, FiniteLaw.expect_const_mul, projectedDiagonal_rows, mul_zero]

theorem constantDiagonalPart_cols (F : Λ × Λ → ℝ) (b : Λ) :
    (FiniteLaw.uniform Λ).expect (fun a => constantDiagonalPart F (a, b)) = 0 := by
  simp only [constantDiagonalPart, FiniteLaw.expect_const_mul, projectedDiagonal_cols, mul_zero]

theorem variableDiagonalPart_rows (F : Λ × Λ → ℝ) (a : Λ) :
    (FiniteLaw.uniform Λ).expect (fun b => variableDiagonalPart F (a, b)) = 0 := by
  simp only [variableDiagonalPart, FiniteLaw.expect_const_mul, projectedDiagonal_rows, mul_zero]

theorem variableDiagonalPart_cols (F : Λ × Λ → ℝ) (b : Λ) :
    (FiniteLaw.uniform Λ).expect (fun a => variableDiagonalPart F (a, b)) = 0 := by
  simp only [variableDiagonalPart, FiniteLaw.expect_const_mul, projectedDiagonal_cols, mul_zero]

theorem offDiagonalPart_rows (F : Λ × Λ → ℝ)
    (hrow : ∀ a, (FiniteLaw.uniform Λ).expect (fun b => F (a, b)) = 0) (a : Λ) :
    (FiniteLaw.uniform Λ).expect (fun b => offDiagonalPart F (a, b)) = 0 := by
  simp only [offDiagonalPart, FiniteLaw.expect_sub, hrow, constantDiagonalPart_rows,
    variableDiagonalPart_rows, sub_zero]

theorem offDiagonalPart_cols (F : Λ × Λ → ℝ)
    (hcol : ∀ b, (FiniteLaw.uniform Λ).expect (fun a => F (a, b)) = 0) (b : Λ) :
    (FiniteLaw.uniform Λ).expect (fun a => offDiagonalPart F (a, b)) = 0 := by
  simp only [offDiagonalPart, FiniteLaw.expect_sub, hcol, constantDiagonalPart_cols,
    variableDiagonalPart_cols, sub_zero]

theorem offDiagonalPart_diagonal (hp : 3 ≤ Fintype.card Λ) (F : Λ × Λ → ℝ) (a : Λ) :
    offDiagonalPart F (a, a) = 0 := by
  have hp' : (3 : ℝ) ≤ Fintype.card Λ := by exact_mod_cast hp
  have h1 : (Fintype.card Λ : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (Fintype.card Λ : ℝ) - 2 ≠ 0 := by linarith
  unfold offDiagonalPart constantDiagonalPart variableDiagonalPart
  rw [projectedDiagonal_one]
  simp only [ite_true, mul_one, projectedDiagonal, diagonalFluctuation_mean]
  unfold diagonalFluctuation
  field_simp
  ring

theorem diagonal_parts_sum (F : Λ × Λ → ℝ) (z : Λ × Λ) :
    F z = constantDiagonalPart F z + variableDiagonalPart F z + offDiagonalPart F z := by
  unfold offDiagonalPart
  ring

theorem diagonal_parts_orthogonal (hp : 3 ≤ Fintype.card Λ) (F : Λ × Λ → ℝ)
    (hrow : ∀ a, (FiniteLaw.uniform Λ).expect (fun b => F (a, b)) = 0)
    (hcol : ∀ b, (FiniteLaw.uniform Λ).expect (fun a => F (a, b)) = 0) :
    ip ((FiniteLaw.uniform Λ).product (FiniteLaw.uniform Λ))
      (constantDiagonalPart F) (variableDiagonalPart F) = 0 ∧
    ip ((FiniteLaw.uniform Λ).product (FiniteLaw.uniform Λ))
      (constantDiagonalPart F) (offDiagonalPart F) = 0 ∧
    ip ((FiniteLaw.uniform Λ).product (FiniteLaw.uniform Λ))
      (variableDiagonalPart F) (offDiagonalPart F) = 0 := by
  have ho (h : Λ → ℝ) :
      ip ((FiniteLaw.uniform Λ).product (FiniteLaw.uniform Λ))
        (fun z => projectedDiagonal h z.1 z.2) (offDiagonalPart F) = 0 := by
    rw [projectedDiagonal_contraction h _ (offDiagonalPart_rows F hrow) (offDiagonalPart_cols F hcol)]
    simp only [offDiagonalPart_diagonal hp, mul_zero, FiniteLaw.expect_const]
  refine ⟨?_, ?_, ?_⟩
  · unfold constantDiagonalPart variableDiagonalPart
    rw [ip_smul_left, ip_comm, ip_smul_left,
      projectedDiagonal_mean_zero_gram _ _ (diagonalFluctuation_mean F)]
    have hz : ip (FiniteLaw.uniform Λ) (diagonalFluctuation F) (fun _ => 1) = 0 := by
      simpa only [ip, mul_one] using diagonalFluctuation_mean F
    rw [hz, mul_zero, mul_zero, mul_zero]
  · unfold constantDiagonalPart
    rw [ip_smul_left, ho, mul_zero]
  · unfold variableDiagonalPart
    rw [ip_smul_left, ho, mul_zero]

theorem diagonal_parts_energy (hp : 3 ≤ Fintype.card Λ) (F : Λ × Λ → ℝ)
    (hrow : ∀ a, (FiniteLaw.uniform Λ).expect (fun b => F (a, b)) = 0)
    (hcol : ∀ b, (FiniteLaw.uniform Λ).expect (fun a => F (a, b)) = 0) :
    nrm ((FiniteLaw.uniform Λ).product (FiniteLaw.uniform Λ)) F ^ 2 =
      nrm ((FiniteLaw.uniform Λ).product (FiniteLaw.uniform Λ)) (constantDiagonalPart F) ^ 2 +
      nrm ((FiniteLaw.uniform Λ).product (FiniteLaw.uniform Λ)) (variableDiagonalPart F) ^ 2 +
      nrm ((FiniteLaw.uniform Λ).product (FiniteLaw.uniform Λ)) (offDiagonalPart F) ^ 2 := by
  obtain ⟨hcv, hco, hvo⟩ := diagonal_parts_orthogonal hp F hrow hcol
  have he : (fun z => F z ^ 2) = fun z =>
      constantDiagonalPart F z ^ 2 + variableDiagonalPart F z ^ 2 + offDiagonalPart F z ^ 2 +
      2 * (constantDiagonalPart F z * variableDiagonalPart F z) +
      2 * (constantDiagonalPart F z * offDiagonalPart F z) +
      2 * (variableDiagonalPart F z * offDiagonalPart F z) := by
    funext z
    conv_lhs => rw [diagonal_parts_sum F z]
    ring
  simp only [ip] at hcv hco hvo
  simp only [nrm_sq_expect, he, FiniteLaw.expect_add, FiniteLaw.expect_const_mul,
    hcv, hco, hvo, mul_zero, add_zero]

end Sarkozy.Cuts
