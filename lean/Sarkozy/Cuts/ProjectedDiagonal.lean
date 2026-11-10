module

public import Sarkozy.Cuts.Swapped

/-! The exact Gram of the auxiliary diagonal projected to the two mean-zero input spaces. -/

@[expose] public section

namespace Sarkozy.Cuts

open Finset Sarkozy.Recentering

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ]

noncomputable def projectedDiagonal (h : Λ → ℝ) (a b : Λ) : ℝ :=
  (if a = b then (Fintype.card Λ : ℝ) * h a else 0) - h a - h b +
    (FiniteLaw.uniform Λ).expect h

theorem uniform_diagonal_expect (a : Λ) (f : Λ → ℝ) :
    (FiniteLaw.uniform Λ).expect (fun b => if a = b then f b else 0) =
      f a / (Fintype.card Λ : ℝ) := by
  rw [FiniteLaw.expect_uniform, sum_ite_eq]
  simp only [mem_univ, ite_true]

theorem uniform_diagonal_const (a : Λ) (c : ℝ) :
    (FiniteLaw.uniform Λ).expect (fun b => if a = b then c else 0) =
      c / (Fintype.card Λ : ℝ) := uniform_diagonal_expect a (fun _ => c)

theorem projectedDiagonal_rows (h : Λ → ℝ) (a : Λ) :
    (FiniteLaw.uniform Λ).expect (projectedDiagonal h a) = 0 := by
  have hp : (Fintype.card Λ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  change (FiniteLaw.uniform Λ).expect (fun b => projectedDiagonal h a b) = 0
  simp only [projectedDiagonal, FiniteLaw.expect_add, FiniteLaw.expect_sub,
    FiniteLaw.expect_const, uniform_diagonal_const, mul_div_cancel_left₀ _ hp]
  ring

theorem projectedDiagonal_symm (h : Λ → ℝ) (a b : Λ) :
    projectedDiagonal h a b = projectedDiagonal h b a := by
  unfold projectedDiagonal
  by_cases hab : a = b
  · subst b; rfl
  · rw [ite_eq_right hab, ite_eq_right (Ne.symm hab)]
    ring

theorem projectedDiagonal_cols (h : Λ → ℝ) (b : Λ) :
    (FiniteLaw.uniform Λ).expect (fun a => projectedDiagonal h a b) = 0 := by
  simp_rw [projectedDiagonal_symm h _ b]
  exact projectedDiagonal_rows h b

theorem projectedDiagonal_contraction (h : Λ → ℝ) (F : Λ × Λ → ℝ)
    (hrow : ∀ a, (FiniteLaw.uniform Λ).expect (fun b => F (a, b)) = 0)
    (hcol : ∀ b, (FiniteLaw.uniform Λ).expect (fun a => F (a, b)) = 0) :
    ip ((FiniteLaw.uniform Λ).product (FiniteLaw.uniform Λ))
      (fun z => projectedDiagonal h z.1 z.2) F =
        (FiniteLaw.uniform Λ).expect (fun a => h a * F (a, a)) := by
  have hp : (Fintype.card Λ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold ip
  rw [FiniteLaw.expect_product]
  simp only [projectedDiagonal, add_mul, sub_mul, ite_mul, zero_mul,
    FiniteLaw.expect_add, FiniteLaw.expect_sub, FiniteLaw.expect_const_mul, hrow,
    mul_zero, sub_zero, add_zero]
  have hd (a : Λ) : (FiniteLaw.uniform Λ).expect
      (fun b => if a = b then (Fintype.card Λ : ℝ) * h a * F (a, b) else 0) =
        h a * F (a, a) := by
    rw [uniform_diagonal_expect]
    field_simp
  simp_rw [hd]
  have hz : (FiniteLaw.uniform Λ).expect (fun a =>
      (FiniteLaw.uniform Λ).expect (fun b => h b * F (a, b))) = 0 := by
    rw [expect_comm]
    simp only [FiniteLaw.expect_const_mul, hcol, mul_zero, FiniteLaw.expect_const]
  rw [hz, sub_zero]

theorem projectedDiagonal_gram (h k : Λ → ℝ) :
    ip ((FiniteLaw.uniform Λ).product (FiniteLaw.uniform Λ))
      (fun z => projectedDiagonal h z.1 z.2) (fun z => projectedDiagonal k z.1 z.2) =
      ((Fintype.card Λ : ℝ) - 2) * ip (FiniteLaw.uniform Λ) h k +
        (FiniteLaw.uniform Λ).expect h * (FiniteLaw.uniform Λ).expect k := by
  rw [projectedDiagonal_contraction h _ (projectedDiagonal_rows k) (projectedDiagonal_cols k)]
  have he (a : Λ) : h a * projectedDiagonal k a a =
      ((Fintype.card Λ : ℝ) - 2) * (h a * k a) + h a * (FiniteLaw.uniform Λ).expect k := by
    simp only [projectedDiagonal, ite_true]
    ring
  simp_rw [he]
  rw [FiniteLaw.expect_add, FiniteLaw.expect_const_mul, FiniteLaw.expect_mul_const]
  rfl

theorem projectedDiagonal_one (a b : Λ) :
    projectedDiagonal (fun _ : Λ => (1 : ℝ)) a b =
      (Fintype.card Λ : ℝ) * (if a = b then 1 else 0) - 1 := by
  simp only [projectedDiagonal, FiniteLaw.expect_const]
  split_ifs <;> ring

theorem projectedDiagonal_mean_zero_gram (h k : Λ → ℝ)
    (hh : (FiniteLaw.uniform Λ).expect h = 0) :
    ip ((FiniteLaw.uniform Λ).product (FiniteLaw.uniform Λ))
      (fun z => projectedDiagonal h z.1 z.2) (fun z => projectedDiagonal k z.1 z.2) =
      ((Fintype.card Λ : ℝ) - 2) * ip (FiniteLaw.uniform Λ) h k := by
  rw [projectedDiagonal_gram, hh, zero_mul, add_zero]

theorem projectedDiagonal_entangled_orthogonal (h : Λ → ℝ)
    (hh : (FiniteLaw.uniform Λ).expect h = 0) :
    ip ((FiniteLaw.uniform Λ).product (FiniteLaw.uniform Λ))
      (fun z => projectedDiagonal h z.1 z.2) (fun z => entangled z.1 z.2) = 0 := by
  have he : (fun z : Λ × Λ => entangled z.1 z.2) =
      fun z => (Real.sqrt ((Fintype.card Λ : ℝ) - 1))⁻¹ *
        projectedDiagonal (fun _ : Λ => 1) z.1 z.2 := by
    funext z
    rw [projectedDiagonal_one]
    unfold entangled
    ring
  rw [he, ip_comm, ip_smul_left, ip_comm, projectedDiagonal_mean_zero_gram h _ hh]
  have hz : ip (FiniteLaw.uniform Λ) h (fun _ => 1) = 0 := by
    simpa only [ip, mul_one] using hh
  rw [hz, mul_zero, mul_zero]

end Sarkozy.Cuts
