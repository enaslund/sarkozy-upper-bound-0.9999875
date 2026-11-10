module

public import Sarkozy.PartV.CoherentDictionaryBounds

/-! Exact collection of a rational dictionary preserves every real evaluation. -/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset Sarkozy.Labellings

def supports (D : Dictionary) : Finset Support := (D.map Prod.fst).toFinset

def coefficientAt (D : Dictionary) (s : Support) : ℚ :=
  (D.map fun sc => if sc.1 = s then sc.2 else 0).sum

def leadingMass (D : Dictionary) : ℚ :=
  ∑ s ∈ supports D, |coefficientAt D s| * leadingCoeff s.card

def evenMass (D : Dictionary) : ℚ :=
  ∑ s ∈ supports D, |coefficientAt D s| * evenCoeff s.card

noncomputable def dictionaryEval (D : Dictionary) (f : Support → ℝ) : ℝ :=
  (D.map fun sc => (sc.2 : ℝ) * f sc.1).sum

theorem sum_list_map_comm {α β : Type*} (s : Finset α) (l : List β) (f : α → β → ℝ) :
    (∑ a ∈ s, (l.map (f a)).sum) = (l.map fun b => ∑ a ∈ s, f a b).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [Finset.sum_add_distrib, ih]

theorem coefficientAt_eval (D : Dictionary) (s : Support) (f : Support → ℝ) :
    (coefficientAt D s : ℝ) * f s =
      (D.map fun sc => if sc.1 = s then (sc.2 : ℝ) * f sc.1 else 0).sum := by
  unfold coefficientAt
  rw [Rat.cast_list_sum, List.map_map, ← List.sum_map_mul_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro sc _
  dsimp only [Function.comp_def]
  by_cases h : sc.1 = s <;> simp [h]

theorem collect_eval (D : Dictionary) (f : Support → ℝ) :
    (∑ s ∈ supports D, (coefficientAt D s : ℝ) * f s) = dictionaryEval D f := by
  simp_rw [coefficientAt_eval]
  rw [sum_list_map_comm]
  apply congrArg List.sum
  apply List.map_congr_left
  intro sc hsc
  have hs : sc.1 ∈ supports D := by
    simp only [supports, List.mem_toFinset, List.mem_map]
    exact ⟨sc, hsc, rfl⟩
  simp [hs]

theorem collected_subsetBound (D : Dictionary) (s : ℝ) :
    (∑ S ∈ supports D, |(coefficientAt D S : ℝ)| * subsetBound s S.card) =
      (leadingMass D : ℝ) * s + (evenMass D : ℝ) := by
  simp only [subsetBound_eq, mul_add, ← mul_assoc, sum_add_distrib, sum_mul,
    leadingMass, evenMass, Rat.cast_sum, Rat.cast_mul, Rat.cast_abs]

theorem abs_dictionaryEval_le (D : Dictionary) (f : Support → ℝ) :
    |dictionaryEval D f| ≤ (D.map fun sc => |(sc.2 : ℝ)| * |f sc.1|).sum := by
  induction D with
  | nil => simp [dictionaryEval]
  | cons sc D ih =>
    simp only [dictionaryEval, List.map_cons, List.sum_cons] at ih ⊢
    exact (abs_add_le _ _).trans (by simpa only [abs_mul] using add_le_add le_rfl ih)

end Sarkozy.PartV.CoherentDictionary
