module

public import Sarkozy.PartV.CoherentDictionary

/-!
# The coherent score bound `14 + r`

Equation `eq:merge-local-I-30`: Weil's bound with the even-degree improvement,
summed over the exact dictionary. The configuration need only be injective.
-/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset Sarkozy.Labellings

theorem subsetBound_eq (s : ℝ) (k : ℕ) :
    subsetBound s k = (leadingCoeff k : ℝ) * s + (evenCoeff k : ℝ) := by
  simp only [subsetBound, leadingCoeff, evenCoeff]
  push_cast
  rfl

theorem dictionary39_subsetBound_sum (s : ℝ) :
    (dictionary39.map fun sc => |(sc.2 : ℝ)| * subsetBound s sc.1.card).sum = 14 * s + 1 := by
  have h1 : (dictionary39.map fun sc => |(sc.2 : ℝ)| * (leadingCoeff sc.1.card : ℝ)).sum = 14 := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) dictionary39_graded_sums.1
    simpa only [Rat.cast_list_sum, List.map_map, Function.comp_def, Rat.cast_mul,
      Rat.cast_abs, Rat.cast_ofNat] using h
  have h2 : (dictionary39.map fun sc => |(sc.2 : ℝ)| * (evenCoeff sc.1.card : ℝ)).sum = 1 := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) dictionary39_graded_sums.2
    simpa only [Rat.cast_list_sum, List.map_map, Function.comp_def, Rat.cast_mul,
      Rat.cast_abs, Rat.cast_one] using h
  simp_rw [subsetBound_eq, mul_add, ← mul_assoc]
  rw [List.sum_map_add, List.sum_map_mul_right, h1, h2]

variable {p : ℕ} [Fact p.Prime]

def trace (S : Support) (x : Vertex → ZMod p) : ℝ :=
  ∑ s : ZMod p, ∏ v ∈ S, (quadraticChar (ZMod p) (s - x v) : ℝ)

theorem trace_eq_rootSum (S : Support) (x : Vertex → ZMod p) (hx : Function.Injective x) :
    trace S x = (rootSum (S.image x) : ℝ) := by
  simp only [trace, rootSum, Int.cast_sum, map_prod, Int.cast_prod]
  apply sum_congr rfl
  intro s _
  rw [prod_image hx.injOn]

theorem trace_bound (hW : WeilBound (ZMod p)) (S : Support) (hS : S.Nonempty)
    (x : Vertex → ZMod p) (hx : Function.Injective x) :
    |trace S x| ≤ subsetBound (Real.sqrt p) S.card := by
  rw [trace_eq_rootSum S x hx]
  have h := abs_rootSum_le hW (hS.image x)
  simpa only [card_image_of_injective S hx, ZMod.card] using h

theorem dictionary39_score_bound (hW : WeilBound (ZMod p))
    (x : Vertex → ZMod p) (hx : Function.Injective x) :
    |coherentScore p dictionary39 x| ≤ 14 + 1 / Real.sqrt p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have htriangle (l : List ℝ) : |l.sum| ≤ (l.map abs).sum := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simpa only [List.sum_cons, List.map_cons] using
        (abs_add_le a l.sum).trans (add_le_add le_rfl ih)
  have hsum : |(dictionary39.map fun sc => (sc.2 : ℝ) * (trace sc.1 x / p)).sum| ≤
      (dictionary39.map fun sc => |(sc.2 : ℝ)| * subsetBound (Real.sqrt p) sc.1.card / p).sum := by
    calc
      _ ≤ (dictionary39.map fun sc => |(sc.2 : ℝ) * (trace sc.1 x / p)|).sum := by
        simpa only [List.map_map, Function.comp_def] using
          htriangle (dictionary39.map fun sc => (sc.2 : ℝ) * (trace sc.1 x / p))
      _ ≤ _ := by
        apply List.sum_le_sum
        intro sc hsc
        have hc := (dictionary39_supports sc hsc).1
        have hne : sc.1.Nonempty := card_pos.mp (by omega)
        rw [abs_mul, abs_div, abs_of_pos hp, ← mul_div_assoc]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (trace_bound hW sc.1 hne x hx) (abs_nonneg _)) hp.le
  change |Real.sqrt p * _| ≤ _
  rw [abs_mul, abs_of_pos hs]
  have hsum' := mul_le_mul_of_nonneg_left hsum hs.le
  change Real.sqrt p * |(dictionary39.map fun sc => (sc.2 : ℝ) * (trace sc.1 x / p)).sum| ≤ _
  refine hsum'.trans_eq ?_
  simp_rw [div_eq_mul_inv]
  rw [List.sum_map_mul_right, dictionary39_subsetBound_sum]
  have he : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt hp.le
  field_simp [hp.ne', hs.ne']
  nlinarith

theorem dictionary39_weight_bounds (hW : WeilBound (ZMod p)) (u η : ℚ)
    (x : Vertex → ZMod p) (hx : Function.Injective x) :
    (η : ℝ) ≤ coherentWeight p dictionary39 u η x ∧
      coherentWeight p dictionary39 u η x ≤
        (η : ℝ) + (1 + |(u : ℝ)| * (14 + 1 / Real.sqrt p)) ^ 2 := by
  have hh := dictionary39_score_bound hW x hx
  have ha : |1 + (u : ℝ) * coherentScore p dictionary39 x| ≤
      1 + |(u : ℝ)| * (14 + 1 / Real.sqrt p) := by
    calc
      _ ≤ |(1 : ℝ)| + |(u : ℝ) * coherentScore p dictionary39 x| := abs_add_le _ _
      _ = 1 + |(u : ℝ)| * |coherentScore p dictionary39 x| := by rw [abs_one, abs_mul]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hh (abs_nonneg _))
  constructor
  · exact le_add_of_nonneg_right (sq_nonneg _)
  · unfold coherentWeight
    apply add_le_add le_rfl
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ha 2

end Sarkozy.PartV.CoherentDictionary
