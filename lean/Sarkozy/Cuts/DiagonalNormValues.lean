module

public import Sarkozy.Cuts.DiagonalNorms

/-! Norms and unit-vector coordinates of the projected auxiliary diagonal parts. -/

@[expose] public section

namespace Sarkozy.Cuts

open Sarkozy.Recentering

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ]

theorem constantDiagonalPart_norm (hp : 2 ≤ Fintype.card Λ) (F : Λ × Λ → ℝ) :
    nrm ((FiniteLaw.uniform Λ).product (FiniteLaw.uniform Λ)) (constantDiagonalPart F) =
      |diagonalMean F| / Real.sqrt ((Fintype.card Λ : ℝ) - 1) := by
  have hp' : (2 : ℝ) ≤ Fintype.card Λ := by exact_mod_cast hp
  apply (sq_eq_sq₀ (nrm_nonneg _ _) (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [constantDiagonalPart_norm_sq hp, div_pow, sq_abs, Real.sq_sqrt (by linarith)]

theorem variableDiagonalPart_norm (hp : 3 ≤ Fintype.card Λ) (F : Λ × Λ → ℝ) :
    nrm ((FiniteLaw.uniform Λ).product (FiniteLaw.uniform Λ)) (variableDiagonalPart F) =
      nrm (FiniteLaw.uniform Λ) (diagonalFluctuation F) /
        Real.sqrt ((Fintype.card Λ : ℝ) - 2) := by
  have hp' : (3 : ℝ) ≤ Fintype.card Λ := by exact_mod_cast hp
  apply (sq_eq_sq₀ (nrm_nonneg _ _) (div_nonneg (nrm_nonneg _ _) (Real.sqrt_nonneg _))).mp
  rw [variableDiagonalPart_norm_sq hp, div_pow, Real.sq_sqrt (by linarith)]

theorem constantDiagonalPart_entangled (hp : 2 ≤ Fintype.card Λ) (F : Λ × Λ → ℝ)
    (z : Λ × Λ) :
    constantDiagonalPart F z = diagonalMean F / Real.sqrt ((Fintype.card Λ : ℝ) - 1) *
      entangled z.1 z.2 := by
  have hp' : (2 : ℝ) ≤ Fintype.card Λ := by exact_mod_cast hp
  have he := Real.sq_sqrt (show 0 ≤ (Fintype.card Λ : ℝ) - 1 by linarith)
  unfold constantDiagonalPart
  rw [projectedDiagonal_one]
  unfold entangled
  rw [div_mul_div_comm, ← pow_two, he]
  ring

end Sarkozy.Cuts
