module

public import Sarkozy.PartV.CoherentPinBounds

/-!
# Coherent score and weight bounds on arbitrary collision strata

The unrestricted bound `|H| ≤ (13/5) sqrt(p)` is the price used on
the exceptional matching events in the finite chamber and layer estimates.
It requires neither distinctness nor a character-sum hypothesis.
-/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset

variable {p : ℕ} [Fact p.Prime]

theorem trace_unrestricted (S : Support) (x : Vertex → ZMod p) : |trace S x| ≤ p := by
  change |∑ z, evaluation S x z| ≤ p
  calc
    _ ≤ ∑ z, |evaluation S x z| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z : ZMod p, (1 : ℝ) := sum_le_sum (fun z _ => abs_evaluation_le S x z)
    _ = p := by simp

theorem dictionary39_unrestricted (x : Vertex → ZMod p) :
    |coherentScore p dictionary39 x| ≤ (13 / 5 : ℝ) * Real.sqrt p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have ht : |dictionaryEval dictionary39 (fun S => trace S x)| ≤ (13 / 5 : ℝ) * p := by
    refine (abs_dictionaryEval_le dictionary39 _).trans ?_
    calc
      _ ≤ (dictionary39.map fun sc => |(sc.2 : ℝ)| * p).sum := by
        apply List.sum_le_sum
        intro sc _
        exact mul_le_mul_of_nonneg_left (trace_unrestricted sc.1 x) (abs_nonneg _)
      _ = _ := by
        rw [List.sum_map_mul_right]
        have h := congrArg (fun q : ℚ => (q : ℝ)) dictionary39_abs_sum
        simp only [Rat.cast_list_sum, List.map_map, Function.comp_def, Rat.cast_abs,
          Rat.cast_div, Rat.cast_ofNat] at h
        rw [h]
  rw [coherentScore_eq_dictionaryEval, abs_div, abs_of_pos hs]
  refine (div_le_div_of_nonneg_right ht hs.le).trans_eq ?_
  rw [div_eq_iff hs.ne']
  have he := Real.sq_sqrt hp.le
  nlinarith

theorem dictionary39_unrestricted_weight (u η : ℚ) (x : Vertex → ZMod p) :
    (η : ℝ) ≤ coherentWeight p dictionary39 u η x ∧
      coherentWeight p dictionary39 u η x ≤
        (η : ℝ) + (1 + |(u : ℝ)| * ((13 / 5 : ℝ) * Real.sqrt p)) ^ 2 := by
  have ha : |1 + (u : ℝ) * coherentScore p dictionary39 x| ≤
      1 + |(u : ℝ)| * ((13 / 5 : ℝ) * Real.sqrt p) := by
    refine (abs_add_le _ _).trans ?_
    simpa only [abs_one, abs_mul] using add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (dictionary39_unrestricted x) (abs_nonneg (u : ℝ)))
  constructor
  · exact le_add_of_nonneg_right (sq_nonneg _)
  · unfold coherentWeight
    apply add_le_add le_rfl
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ha 2

end Sarkozy.PartV.CoherentDictionary
