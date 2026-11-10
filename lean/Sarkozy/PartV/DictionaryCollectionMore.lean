module

public import Sarkozy.PartV.DictionaryCollection

/-! Collection over any finite support cover, and coefficients of a support filter. -/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset

theorem sum_product_map {α β M : Type*} [AddCommMonoid M]
    (A : List α) (B : List β) (f : α → β → M) :
    ((A.product B).map fun ab => f ab.1 ab.2).sum =
      (A.map fun a => (B.map (f a)).sum).sum := by
  induction A with
  | nil => simp [List.product]
  | cons a A ih =>
    simp only [List.product] at ih ⊢
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_map,
      Function.comp_def, List.map_cons, List.sum_cons, ih]

theorem coefficientAt_filter (D : Dictionary) (P : Support → Prop) [DecidablePred P]
    (S : Support) : coefficientAt (D.filter fun sc => decide (P sc.1)) S =
      if P S then coefficientAt D S else 0 := by
  induction D with
  | nil => simp [coefficientAt]
  | cons sc D ih =>
    by_cases h : P sc.1 <;> by_cases he : sc.1 = S <;> by_cases hs : P S <;>
      simp_all [coefficientAt]

theorem collect_cover_eval (D : Dictionary) (C : Finset Support)
    (hC : ∀ sc ∈ D, sc.1 ∈ C) (f : Support → ℝ) :
    (∑ S ∈ C, (coefficientAt D S : ℝ) * f S) = dictionaryEval D f := by
  simp_rw [coefficientAt_eval]
  rw [sum_list_map_comm]
  apply congrArg List.sum
  apply List.map_congr_left
  intro sc hsc
  simp [hC sc hsc]

theorem collect_nonzero_cover_eval (D : Dictionary) (C : Finset Support)
    (hC : ∀ sc ∈ D, sc.1 ∈ C) (f : Support → ℝ) :
    (∑ S ∈ C.filter (fun S => coefficientAt D S ≠ 0), (coefficientAt D S : ℝ) * f S) =
      dictionaryEval D f := by
  rw [← collect_cover_eval D C hC f]
  apply sum_subset (filter_subset _ _)
  intro S hS hn
  have hc : coefficientAt D S = 0 := by
    simpa only [mem_filter, hS, true_and, not_not] using hn
  simp only [hc, Rat.cast_zero, zero_mul]

theorem sum_list_map_list_comm {α β M : Type*} [AddCommMonoid M]
    (A : List α) (B : List β) (f : α → β → M) :
    (A.map fun a => (B.map (f a)).sum).sum =
      (B.map fun b => (A.map fun a => f a b).sum).sum := by
  induction A with
  | nil => simp
  | cons a A ih => simp [List.sum_map_add, ih]

theorem sum_flatMap_map {α β M : Type*} [AddCommMonoid M]
    (A : List α) (B : α → List β) (f : β → M) :
    ((A.flatMap B).map f).sum = (A.map fun a => ((B a).map f).sum).sum := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, ih]

theorem collect_list_eval (D E : Dictionary)
    (hcoeff : ∀ sc ∈ E, sc.2 = coefficientAt D sc.1)
    (hmult : ∀ sc ∈ D, (E.map fun tc => if tc.1 = sc.1 then (1 : ℚ) else 0).sum = 1)
    (f : Support → ℝ) : dictionaryEval E f = dictionaryEval D f := by
  calc
    _ = (E.map fun sc => (D.map fun tc =>
        if tc.1 = sc.1 then (tc.2 : ℝ) * f tc.1 else 0).sum).sum := by
      unfold dictionaryEval
      apply congrArg List.sum
      apply List.map_congr_left
      intro sc hsc
      rw [hcoeff sc hsc, coefficientAt_eval]
    _ = (D.map fun tc => (E.map fun sc =>
        if tc.1 = sc.1 then (tc.2 : ℝ) * f tc.1 else 0).sum).sum :=
      sum_list_map_list_comm E D _
    _ = _ := by
      unfold dictionaryEval
      apply congrArg List.sum
      apply List.map_congr_left
      intro tc htc
      have hm := congrArg (fun q : ℚ => (q : ℝ)) (hmult tc htc)
      simp only [Rat.cast_list_sum, List.map_map, Function.comp_def, apply_ite,
        Rat.cast_one, Rat.cast_zero] at hm
      have he (sc : Support × ℚ) :
          (if tc.1 = sc.1 then (tc.2 : ℝ) * f tc.1 else 0) =
            (if sc.1 = tc.1 then (1 : ℝ) else 0) * ((tc.2 : ℝ) * f tc.1) := by
        by_cases h : sc.1 = tc.1 <;> simp [h, Ne.symm]
      simp_rw [he]
      rw [List.sum_map_mul_right, hm, one_mul]

theorem dictionaryEval_filter (D : Dictionary) (P : Support → Prop) [DecidablePred P]
    (f : Support → ℝ) :
    dictionaryEval (D.filter fun sc => decide (P sc.1)) f =
      dictionaryEval D (fun S => if P S then f S else 0) := by
  induction D with
  | nil => rfl
  | cons sc D ih =>
    by_cases h : P sc.1 <;> simp [dictionaryEval, h] at ih ⊢ <;> exact ih

end Sarkozy.PartV.CoherentDictionary
