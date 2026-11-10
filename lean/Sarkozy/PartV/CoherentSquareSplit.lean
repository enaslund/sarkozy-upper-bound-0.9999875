module

public import Sarkozy.PartV.CoherentDiagonalProduct

/-! Exact split of the physical coherent square by its shared auxiliary labels. -/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

noncomputable def offdiagTraceProduct (S T : Support) (x : Vertex → ZMod p) : ℝ :=
  (∑ u, ∑ v, if u = v then 0 else evaluation S x u * evaluation T x v) / p

theorem score_square_split (D : Dictionary) (x : Vertex → ZMod p) :
    coherentScore p D x ^ 2 =
      (∑ z, (dictionaryEval D (fun S => evaluation S x z)) ^ 2) / p +
        ((D.product D).map fun st =>
          ((st.1.2 * st.2.2 : ℚ) : ℝ) * offdiagTraceProduct st.1.1 st.2.1 x).sum := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hs : coherentScore p D x =
      (Real.sqrt p / p) * ∑ z, dictionaryEval D (fun S => evaluation S x z) := by
    change Real.sqrt p * (D.map fun sc => (sc.2 : ℝ) *
      ((∑ z, evaluation sc.1 x z) / p)).sum = _
    unfold dictionaryEval
    rw [sum_list_map_comm]
    simp only [← mul_sum, div_eq_mul_inv, ← mul_assoc, List.sum_map_mul_right]
    ring
  let a := fun z => dictionaryEval D (fun S => evaluation S x z)
  have hdiag : (∑ u, ∑ v, a u * a v) =
      (∑ z, a z ^ 2) + ∑ u, ∑ v, if u = v then 0 else a u * a v := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro u _
    have he (v : ZMod p) : a u * a v =
        (if u = v then a u ^ 2 else 0) + (if u = v then 0 else a u * a v) := by
      split_ifs with h
      · rw [h]; ring
      · ring
    rw [sum_congr rfl (fun v _ => he v), sum_add_distrib, sum_ite_eq]
    simp only [mem_univ, ite_true]
  have hcross (u v : ZMod p) : a u * a v =
      ((D.product D).map fun st => ((st.1.2 * st.2.2 : ℚ) : ℝ) *
        (evaluation st.1.1 x u * evaluation st.2.1 x v)).sum := by
    have h := sum_product_mul D D
      (fun sc => (sc.2 : ℝ) * evaluation sc.1 x u)
      (fun sc => (sc.2 : ℝ) * evaluation sc.1 x v)
    unfold a dictionaryEval
    rw [← h]
    apply congrArg List.sum
    apply List.map_congr_left
    intro st _
    push_cast
    ring
  have hoff : (∑ u, ∑ v, if u = v then 0 else a u * a v) / p =
      ((D.product D).map fun st =>
        ((st.1.2 * st.2.2 : ℚ) : ℝ) * offdiagTraceProduct st.1.1 st.2.1 x).sum := by
    have he (u v : ZMod p) : (if u = v then 0 else a u * a v) =
        ((D.product D).map fun st => ((st.1.2 * st.2.2 : ℚ) : ℝ) *
          (if u = v then 0 else evaluation st.1.1 x u * evaluation st.2.1 x v)).sum := by
      by_cases huv : u = v
      · simp only [ite_eq_left huv, mul_zero, List.map_const', List.sum_replicate, nsmul_zero]
      · simp only [ite_eq_right huv, hcross]
    simp_rw [he, sum_list_map_comm]
    simp only [← mul_sum, offdiagTraceProduct, div_eq_mul_inv, ← mul_assoc,
      List.sum_map_mul_right]

  rw [hs, mul_pow, div_pow, Real.sq_sqrt hp.le]
  change (p : ℝ) / p ^ 2 * (∑ z, a z) ^ 2 = _
  rw [sq (∑ z, a z), sum_mul_sum, hdiag]
  rw [mul_add]
  have he (b : ℝ) : (p : ℝ) / p ^ 2 * b = b / p := by field_simp
  rw [he, he, hoff]

end Sarkozy.PartV.CoherentDictionary
