module

public import Sarkozy.JointRows.CubeCoordinates
public import Sarkozy.L20Cap.Mass

/-! Uniform label integration for the finite character-graph moment certificate. -/

@[expose] public section

namespace Sarkozy.Variance.CharacterGraph

open Finset Sarkozy.FiveType.Blocks Sarkozy.JointRows.Star

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X] [Nonempty X]

noncomputable def labelLaw (ι X : Type*) [Fintype ι] [DecidableEq ι] [Fintype X] [Nonempty X] :
    FiniteLaw (ι → X) := FiniteLaw.uniform (ι → X)

omit [DecidableEq X] in
theorem label_expect_block (f : (ι → X) → ℝ) :
    (labelLaw ι X).expect f = (blockLaw (fun _ : ι => FiniteLaw.uniform X)).expect f := by
  unfold FiniteLaw.expect labelLaw
  apply sum_congr rfl
  intro x _
  congr 1
  simp only [FiniteLaw.uniform, blockLaw, Fintype.card_fun, Nat.cast_pow, prod_const,
    card_univ, inv_pow]

theorem label_expect_update (i : ι) (f : (ι → X) → ℝ) :
    (labelLaw ι X).expect f = (labelLaw ι X).expect (fun x =>
      (FiniteLaw.uniform X).expect (fun t => f (Function.update x i t))) := by
  rw [label_expect_block, label_expect_block]
  exact (expect_condMean (fun _ : ι => FiniteLaw.uniform X) i f).symm

omit [DecidableEq X] in
theorem label_expect_equiv (e : (ι → X) ≃ (ι → X)) (f : (ι → X) → ℝ) :
    (labelLaw ι X).expect (fun x => f (e x)) = (labelLaw ι X).expect f := by
  unfold labelLaw
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform]
  congr 1
  exact Equiv.sum_comp e f

omit [DecidableEq X] in
theorem label_expect_permute (e : Equiv.Perm ι) (f : (ι → X) → ℝ) :
    (labelLaw ι X).expect (fun x => f (x ∘ e)) = (labelLaw ι X).expect f := by
  exact label_expect_equiv (Equiv.arrowCongr e.symm (Equiv.refl X)) f

theorem label_expect_identify (a b : ι) (hab : a ≠ b) (f : (ι → X) → ℝ) :
    (labelLaw ι X).expect (fun x => if x a = x b then f x else 0) =
      (Fintype.card X : ℝ)⁻¹ *
        (labelLaw ι X).expect (fun x => f (Function.update x b (x a))) := by
  rw [label_expect_update b (fun x => if x a = x b then f x else 0)]
  simp only [Function.update_of_ne hab, Function.update_self]
  have hinner (x : ι → X) : (FiniteLaw.uniform X).expect
      (fun t => if x a = t then f (Function.update x b t) else 0) =
        (Fintype.card X : ℝ)⁻¹ * f (Function.update x b (x a)) := by
    rw [FiniteLaw.expect_uniform]
    simp only [sum_ite_eq, mem_univ, ite_true, div_eq_mul_inv]
    ring
  simp_rw [hinner]
  rw [FiniteLaw.expect_const_mul]

omit [Fintype ι] [DecidableEq ι] [DecidableEq X] in
theorem label_expect_fin_succ {n : ℕ} (f : (Fin (n + 1) → X) → ℝ) :
    (labelLaw (Fin (n + 1)) X).expect f =
      (FiniteLaw.uniform X).expect (fun a =>
        (labelLaw (Fin n) X).expect (fun x => f (Fin.cons a x))) := by
  simp only [labelLaw, FiniteLaw.expect_uniform, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow]
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => X)) f,
    Fintype.sum_prod_type]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, ← sum_div]
  rw [div_div, pow_succ]

end Sarkozy.Variance.CharacterGraph
