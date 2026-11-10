module

public import Sarkozy.JointRows.CollLambda

/-! Exact uniform weights after restricting independent allowed coordinates to injectivity. -/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.Coll

open Finset

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]

def strictSet (A : I → Finset X) : Finset (I → X) :=
  univ.filter fun x => Function.Injective x ∧ ∀ i, x i ∈ A i

theorem product_allowed_weight (A : I → Finset X) (hA : ∀ i, (A i).Nonempty)
    (x : I → X) :
    (FiniteLaw.pi fun i => unifOn (A i) (hA i)).weight x =
      if ∀ i, x i ∈ A i then ∏ i, ((A i).card : ℝ)⁻¹ else 0 := by
  change (∏ i, if x i ∈ A i then ((A i).card : ℝ)⁻¹ else 0) = _
  by_cases hx : ∀ i, x i ∈ A i
  · simp [hx]
  · rw [ite_eq_right hx]
    push Not at hx
    obtain ⟨i, hi⟩ := hx
    exact prod_eq_zero (mem_univ i) (ite_eq_right hi)

theorem strict_product_weight (A : I → Finset X) (hA : ∀ i, (A i).Nonempty)
    (hP : 0 < Peyre.prob (FiniteLaw.pi fun i => unifOn (A i) (hA i))
      (fun x => Function.Injective x)) (x : I → X) :
    (Peyre.condLaw (FiniteLaw.pi fun i => unifOn (A i) (hA i))
      (fun x => Function.Injective x) hP).weight x =
      if x ∈ strictSet A then (((strictSet A).card : ℝ))⁻¹ else 0 := by
  let lam := FiniteLaw.pi fun i => unifOn (A i) (hA i)
  let C : ℝ := ∏ i, ((A i).card : ℝ)⁻¹
  have hC : C ≠ 0 := ne_of_gt (prod_pos fun i _ =>
    inv_pos.mpr (by exact_mod_cast card_pos.mpr (hA i)))
  have hi (y : I → X) : Peyre.ind (fun z => Function.Injective z) y * lam.weight y =
      if y ∈ strictSet A then C else 0 := by
    rw [show lam.weight y = _ from product_allowed_weight A hA y]
    simp only [strictSet, mem_filter, mem_univ, true_and]
    by_cases hy : Function.Injective y <;> by_cases hya : ∀ i, y i ∈ A i
    all_goals simp [hy, hya, Peyre.ind, C]
  have hp : Peyre.prob lam (fun z => Function.Injective z) =
      (strictSet A).card * C := by
    unfold Peyre.prob FiniteLaw.expect
    simp_rw [mul_comm (lam.weight _) _, hi]
    rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
  change (Peyre.condLaw lam _ hP).weight x = _
  rw [Peyre.cond_weight, hi, hp]
  split_ifs <;> simp [hC, mul_comm, div_eq_mul_inv]

end Sarkozy.JointRows.Coll
