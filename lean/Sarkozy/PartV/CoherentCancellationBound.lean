module

public import Sarkozy.PartV.CoherentCancellation
public import Sarkozy.PartV.CoherentPinBounds

/-! The original Weil price survives every partial repeated-root cancellation. -/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset Sarkozy.Labellings

theorem subsetBound_add_pairs (s : ℝ) (m n : ℕ) :
    subsetBound s (m + 2 * n) = subsetBound s m + 2 * (n : ℝ) * s := by
  have he : evenCoeff (m + 2 * n) = evenCoeff m := by
    norm_num [evenCoeff, pow_add, pow_mul]
  rw [subsetBound_eq, subsetBound_eq]
  unfold leadingCoeff
  rw [he]
  push_cast
  ring

variable {p : ℕ} [Fact p.Prime]

theorem trace_partial_cancellation_bound (hW : WeilBound (ZMod p))
    (S : Support) (x : Vertex → ZMod p) (hne : ¬Cancellation x S ∅) :
    |trace S x| ≤ subsetBound (Real.sqrt p) S.card := by
  obtain ⟨T, hT, hinj⟩ := exists_injective_cancellation S x
  have hTne : T.Nonempty := nonempty_iff_ne_empty.mpr (fun h => hne (h ▸ hT))
  obtain ⟨n, hn, he⟩ := hT.trace_error
  have hs : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hmul := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  calc
    _ ≤ |trace S x - trace T x| + |trace T x| := by
      simpa only [sub_add_cancel] using abs_add_le (trace S x - trace T x) (trace T x)
    _ ≤ (n : ℝ) + subsetBound (Real.sqrt p) T.card :=
      add_le_add he (trace_bound_injOn hW T hTne x hinj)
    _ ≤ _ := by
      rw [hn, subsetBound_add_pairs]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem dictionary39_partial_cancellation_bound (hW : WeilBound (ZMod p))
    (x : Vertex → ZMod p)
    (hne : ∀ sc ∈ dictionary39, ¬Cancellation x sc.1 ∅) :
    |coherentScore p dictionary39 x| ≤ 14 + 1 / Real.sqrt p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have ht : |dictionaryEval dictionary39 (fun S => trace S x)| ≤ 14 * Real.sqrt p + 1 := by
    refine (abs_dictionaryEval_le dictionary39 _).trans ?_
    rw [← dictionary39_subsetBound_sum]
    apply List.sum_le_sum
    intro sc hsc
    exact mul_le_mul_of_nonneg_left
      (trace_partial_cancellation_bound hW sc.1 x (hne sc hsc)) (abs_nonneg _)
  rw [coherentScore_eq_dictionaryEval, abs_div, abs_of_pos hs]
  refine (div_le_div_of_nonneg_right ht hs.le).trans_eq ?_
  rw [add_div, mul_div_cancel_right₀ _ hs.ne']

theorem no_cancellation_of_odd (S : Support) (hS : S.card % 2 = 1)
    (x : Vertex → ZMod p) : ¬Cancellation x S ∅ := by
  intro hc
  obtain ⟨n, hn, _⟩ := hc.trace_error
  simp only [card_empty] at hn
  omega

/-- Only the degree-six and degree-eight terms can cancel completely. -/
theorem dictionary39_partial_bound_of_even (hW : WeilBound (ZMod p))
    (x : Vertex → ZMod p)
    (hne : ∀ sc ∈ dictionary39, sc.1.card = 6 ∨ sc.1.card = 8 → ¬Cancellation x sc.1 ∅) :
    |coherentScore p dictionary39 x| ≤ 14 + 1 / Real.sqrt p := by
  apply dictionary39_partial_cancellation_bound hW x
  intro sc hsc
  rcases (dictionary39_supports sc hsc).1 with h6 | h7 | h8
  · exact hne sc hsc (Or.inl h6)
  · exact no_cancellation_of_odd sc.1 (by omega) x
  · exact hne sc hsc (Or.inr h8)

end Sarkozy.PartV.CoherentDictionary
