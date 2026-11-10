module

public import Sarkozy.JointRows.RawIndicator

/-! Expectations of indicators under a finite uniform law. -/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.Coll

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem uniform_indicator_sum (μ : FiniteLaw X) (S : Finset X)
    (hμ : ∀ x, μ.weight x = if x ∈ S then (S.card : ℝ)⁻¹ else 0)
    (P : X → Prop) [DecidablePred P] (C : ℝ) :
    μ.expect (fun x => if P x then C else 0) = C * (S.card : ℝ)⁻¹ * (S.filter P).card := by
  have hterm (x : X) : μ.weight x * (if P x then C else 0) =
      if x ∈ S.filter P then C * (S.card : ℝ)⁻¹ else 0 := by
    rw [hμ]
    by_cases hx : x ∈ S <;> by_cases hp : P x <;> simp [hx, hp, mul_comm]
  unfold FiniteLaw.expect
  rw [sum_congr rfl fun x _ => hterm x, sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
  ring

end Sarkozy.JointRows.Coll
