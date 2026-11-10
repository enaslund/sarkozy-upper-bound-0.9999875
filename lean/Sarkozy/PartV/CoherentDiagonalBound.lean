module

public import Sarkozy.PartV.CoherentDiagonalProduct
public import Sarkozy.PartV.CoherentDiagonalTrace
public import Sarkozy.PartV.CoherentPinBounds

/-! A quantitative auxiliary-diagonal identity for the physical 39-trace score. -/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset
open scoped symmDiff

theorem diagonal_hole_budget :
    ((dictionary39.product dictionary39).map fun st =>
      |st.1.2 * st.2.2| * ((st.1.1 ∩ st.2.1).card : ℚ)).sum = 1936 / 75 := by
  decide +kernel

theorem abs_list_sum (l : List ℝ) : |l.sum| ≤ (l.map abs).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simpa only [List.sum_cons, List.map_cons] using
      (abs_add_le a l.sum).trans (add_le_add le_rfl ih)

theorem abs_map_sum {α : Type*} (l : List α) (f : α → ℝ) :
    |(l.map f).sum| ≤ (l.map fun a => |f a|).sum := by
  simpa only [List.map_map, Function.comp_def] using abs_list_sum (l.map f)

variable {p : ℕ} [Fact p.Prime]

theorem auxiliary_diagonal_error (x : Vertex → ZMod p) :
    |(∑ z, (dictionaryEval dictionary39 (fun S => evaluation S x z)) ^ 2) / p -
      dictionaryEval diagonalRaw (fun S => trace S x / p)| ≤ (1936 / 75 : ℝ) / p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [auxiliary_diagonal]
  simp only [dictionaryEval, diagonalRaw, List.map_map, Function.comp_def]
  rw [← sum_map_sub]
  calc
    _ ≤ ((dictionary39.product dictionary39).map fun st =>
        |((st.1.2 * st.2.2 : ℚ) : ℝ) * traceProduct st.1.1 st.2.1 x -
          ((st.1.2 * st.2.2 : ℚ) : ℝ) * (trace (st.1.1 ∆ st.2.1) x / p)|).sum := by
      exact abs_map_sum _ _
    _ ≤ ((dictionary39.product dictionary39).map fun st =>
        |((st.1.2 * st.2.2 : ℚ) : ℝ)| * ((st.1.1 ∩ st.2.1).card : ℝ) / p).sum := by
      apply List.sum_le_sum
      intro st _
      rw [← mul_sub, abs_mul, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (traceProduct_error _ _ x) (abs_nonneg _)
    _ = _ := by
      simp_rw [div_eq_mul_inv]
      rw [List.sum_map_mul_right]
      have h := congrArg (fun q : ℚ => (q : ℝ)) diagonal_hole_budget
      simp only [Rat.cast_list_sum, List.map_map, Function.comp_def, Rat.cast_mul,
        Rat.cast_abs, Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat] at h
      simp only [Rat.cast_mul]
      rw [h, div_eq_mul_inv]

end Sarkozy.PartV.CoherentDictionary
