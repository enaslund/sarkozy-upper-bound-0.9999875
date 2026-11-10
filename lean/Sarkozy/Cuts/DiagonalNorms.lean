module

public import Sarkozy.Cuts.DiagonalDecomposition

/-! Exact norm prices for the two projected-diagonal components. -/

@[expose] public section

namespace Sarkozy.Cuts

open Finset Sarkozy.Recentering

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ]

theorem constantDiagonalPart_norm_sq (hp : 2 ≤ Fintype.card Λ) (F : Λ × Λ → ℝ) :
    nrm ((FiniteLaw.uniform Λ).product (FiniteLaw.uniform Λ)) (constantDiagonalPart F) ^ 2 =
      diagonalMean F ^ 2 / ((Fintype.card Λ : ℝ) - 1) := by
  have hp' : (2 : ℝ) ≤ Fintype.card Λ := by exact_mod_cast hp
  have h1 : (Fintype.card Λ : ℝ) - 1 ≠ 0 := by linarith
  rw [nrm_sq_eq]
  unfold constantDiagonalPart
  rw [ip_smul_left, ip_comm, ip_smul_left, projectedDiagonal_gram]
  simp only [ip, mul_one, FiniteLaw.expect_const]
  field_simp
  ring

theorem variableDiagonalPart_norm_sq (hp : 3 ≤ Fintype.card Λ) (F : Λ × Λ → ℝ) :
    nrm ((FiniteLaw.uniform Λ).product (FiniteLaw.uniform Λ)) (variableDiagonalPart F) ^ 2 =
      nrm (FiniteLaw.uniform Λ) (diagonalFluctuation F) ^ 2 / ((Fintype.card Λ : ℝ) - 2) := by
  have hp' : (3 : ℝ) ≤ Fintype.card Λ := by exact_mod_cast hp
  have h2 : (Fintype.card Λ : ℝ) - 2 ≠ 0 := by linarith
  rw [nrm_sq_eq]
  unfold variableDiagonalPart
  rw [ip_smul_left, ip_comm, ip_smul_left,
    projectedDiagonal_mean_zero_gram _ _ (diagonalFluctuation_mean F), ← nrm_sq_eq]
  field_simp

theorem diagonal_parts_energy_exact (hp : 3 ≤ Fintype.card Λ) (F : Λ × Λ → ℝ)
    (hrow : ∀ a, (FiniteLaw.uniform Λ).expect (fun b => F (a, b)) = 0)
    (hcol : ∀ b, (FiniteLaw.uniform Λ).expect (fun a => F (a, b)) = 0) :
    nrm ((FiniteLaw.uniform Λ).product (FiniteLaw.uniform Λ)) F ^ 2 =
      diagonalMean F ^ 2 / ((Fintype.card Λ : ℝ) - 1) +
      nrm (FiniteLaw.uniform Λ) (diagonalFluctuation F) ^ 2 / ((Fintype.card Λ : ℝ) - 2) +
      nrm ((FiniteLaw.uniform Λ).product (FiniteLaw.uniform Λ)) (offDiagonalPart F) ^ 2 := by
  rw [diagonal_parts_energy hp F hrow hcol, constantDiagonalPart_norm_sq (by omega),
    variableDiagonalPart_norm_sq hp]

end Sarkozy.Cuts
