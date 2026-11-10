module

public import Sarkozy.Cuts.ProjectedDiagonal

/-! Exact contractions of a tensor product against the auxiliary diagonal components. -/

@[expose] public section

namespace Sarkozy.Cuts

open Finset Sarkozy.Recentering

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ]

theorem projectedDiagonal_tensor (h a b : Λ → ℝ) :
    ip ((FiniteLaw.uniform Λ).product (FiniteLaw.uniform Λ))
      (fun z => projectedDiagonal h z.1 z.2) (fun z => a z.1 * b z.2) =
      (FiniteLaw.uniform Λ).expect (fun u => h u * a u * b u) -
      (FiniteLaw.uniform Λ).expect b * (FiniteLaw.uniform Λ).expect (fun u => h u * a u) -
      (FiniteLaw.uniform Λ).expect a * (FiniteLaw.uniform Λ).expect (fun u => h u * b u) +
      (FiniteLaw.uniform Λ).expect h * (FiniteLaw.uniform Λ).expect a *
        (FiniteLaw.uniform Λ).expect b := by
  have hp : (Fintype.card Λ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he (u v : Λ) : projectedDiagonal h u v * (a u * b v) =
      (if u = v then (Fintype.card Λ : ℝ) * h u * a u * b v else 0) -
        (h u * a u) * b v - a u * (h v * b v) +
        (FiniteLaw.uniform Λ).expect h * a u * b v := by
    unfold projectedDiagonal
    split_ifs <;> ring
  unfold ip
  rw [FiniteLaw.expect_product]
  simp_rw [he]
  simp only [FiniteLaw.expect_add, FiniteLaw.expect_sub, FiniteLaw.expect_const_mul,
    FiniteLaw.expect_mul_const, uniform_diagonal_expect]
  have he' (u : Λ) : ((Fintype.card Λ : ℝ) * h u * a u * b u) / Fintype.card Λ =
      h u * a u * b u := by field_simp
  simp_rw [he']
  ring

theorem entangled_tensor (a b : Λ → ℝ) :
    ((FiniteLaw.uniform Λ).product (FiniteLaw.uniform Λ)).expect
      (fun z => a z.1 * b z.2 * entangled z.1 z.2) =
      ((FiniteLaw.uniform Λ).expect (fun u => a u * b u) -
        (FiniteLaw.uniform Λ).expect a * (FiniteLaw.uniform Λ).expect b) /
          Real.sqrt ((Fintype.card Λ : ℝ) - 1) := by
  have he (u v : Λ) : a u * b v * entangled u v =
      ((if u = v then (Fintype.card Λ : ℝ) * a u * b v else 0) - a u * b v) /
        Real.sqrt ((Fintype.card Λ : ℝ) - 1) := by
    unfold entangled
    split_ifs <;> ring
  rw [FiniteLaw.expect_product]
  simp_rw [he, div_eq_mul_inv]
  simp only [FiniteLaw.expect_mul_const, FiniteLaw.expect_sub, FiniteLaw.expect_const_mul,
    uniform_diagonal_expect]
  have hp : (Fintype.card Λ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he' (u : Λ) : ((Fintype.card Λ : ℝ) * a u * b u) / Fintype.card Λ = a u * b u := by
    field_simp
  simp_rw [he']

end Sarkozy.Cuts
