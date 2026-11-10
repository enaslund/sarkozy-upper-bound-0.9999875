module

public import Sarkozy.JointRows.StarOpsBounds
public import Sarkozy.SecondOrder.WeightedStars

/-!
# Paley contraction at every odd prime

The tail row estimates use no prime-class restriction. The two-root
identity gives the exact squared norm directly, so the feature bounds
also apply when the Paley operator is symmetric.
-/

@[expose] public section

namespace Sarkozy.JointRows.StarOps

open Finset Sarkozy.JointRows.PaleyGauss

variable {p : ℕ} [Fact p.Prime]

theorem sum_paley_sq_eq_odd (hp : p ≠ 2) (h : ZMod p → ℝ) :
    ∑ t, paley p h t * paley p h t = ∑ t, h t * h t - (∑ t, h t) ^ 2 / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hquad : ∑ t, (∑ a, chiR p (a - t) * h a) ^ 2 =
      ∑ a, ∑ b, h a * h b * ((p : ℝ) * (if a = b then 1 else 0) - 1) := by
    have hexp (t : ZMod p) : (∑ a, chiR p (a - t) * h a) ^ 2 =
        ∑ a, ∑ b, h a * h b * (chiR p (a - t) * chiR p (b - t)) := by
      rw [sq, sum_mul_sum]
      exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
    simp_rw [hexp]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    rw [sum_comm]
    apply sum_congr rfl
    intro b _
    rw [← mul_sum]
    exact congrArg (h a * h b * ·) (SecondOrder.sum_chi_mul_chi hp a b)
  have hs : ∑ a, ∑ b, h a * h b * ((p : ℝ) * (if a = b then 1 else 0) - 1) =
      (p : ℝ) * ∑ a, h a * h a - (∑ a, h a) ^ 2 := by
    simp only [mul_sub, mul_one, mul_ite, mul_zero, sum_sub_distrib, sum_ite_eq,
      mem_univ, ite_true]
    rw [sq, sum_mul_sum, mul_sum]
    congr 1
    exact sum_congr rfl fun a _ => by ring
  simp only [paley]
  have hnorm : ∀ t : ZMod p,
      (Real.sqrt p / p * ∑ a, chiR p (a - t) * h a) *
        (Real.sqrt p / p * ∑ a, chiR p (a - t) * h a) =
      (Real.sqrt p / p) ^ 2 * (∑ a, chiR p (a - t) * h a) ^ 2 := fun _ => by ring
  simp_rw [hnorm]
  rw [← mul_sum, hquad, hs, div_pow, Real.sq_sqrt hp0.le]
  field_simp

theorem sum_paley_sq_le_odd (hp : p ≠ 2) (h : ZMod p → ℝ) :
    ∑ t, paley p h t * paley p h t ≤ ∑ t, h t * h t := by
  rw [sum_paley_sq_eq_odd hp]
  exact sub_le_self _ (by positivity)

end Sarkozy.JointRows.StarOps
