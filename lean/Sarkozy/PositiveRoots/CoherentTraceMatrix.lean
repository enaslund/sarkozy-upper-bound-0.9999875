module

public import Sarkozy.PositiveRoots.CoherentTraceChart
public import Sarkozy.PositiveRoots.CoherentFrameOrder

/-! Collect the physical trace-pair dictionary into its certified coefficient matrix. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.PartV Sarkozy.PartV.CoherentDictionary
open Sarkozy.SpectralC Sarkozy.SpectralD
open scoped BigOperators

def supportFeature (S : Finset (Fin 6)) : Feature :=
  if h : 2 ≤ S.card then Sum.inr ⟨S, mem_filter.mpr ⟨mem_univ _, h⟩⟩ else Sum.inl 0

def chamberFeature (side : Bool) (S : Support) : Feature :=
  supportFeature (chamberSupport side S)

theorem supportFeature_star (S : Finset (Fin 6)) (h : 2 ≤ S.card) :
    supportFeature S = Sum.inr ⟨S, mem_filter.mpr ⟨mem_univ _, h⟩⟩ := by
  simp only [supportFeature, h, ↓reduceDIte]

theorem chamber_feature_indices : ∀ sc ∈ dictionary39,
    (CoherentOldChamber.index (chamberFeature true sc.1)).val = CoherentMatrix.leftCode sc.1 ∧
      (CoherentOldChamber.index (chamberFeature false sc.1)).val =
        CoherentMatrix.rightCode sc.1 := by
  decide +kernel

theorem chamber_feature_iff (sc : Support × ℚ) (hsc : sc ∈ dictionary39) (a b : Feature) :
    (chamberFeature true sc.1 = a ∧ chamberFeature false sc.1 = b) ↔
      (CoherentMatrix.leftCode sc.1 = (CoherentOldChamber.index a).val ∧
        CoherentMatrix.rightCode sc.1 = (CoherentOldChamber.index b).val) := by
  rw [← (chamber_feature_indices sc hsc).1, ← (chamber_feature_indices sc hsc).2]
  constructor
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨ha, hb⟩
    exact ⟨CoherentOldChamber.index_injective (Fin.ext ha),
      CoherentOldChamber.index_injective (Fin.ext hb)⟩

def chamberCoeff (a b : Feature) : ℚ :=
  (dictionary39.map fun sc =>
    if chamberFeature true sc.1 = a ∧ chamberFeature false sc.1 = b then sc.2 else 0).sum

theorem chamberCoeff_eq (a b : Feature) :
    chamberCoeff a b = CoherentMatrix.coefficient
      (CoherentOldChamber.index a) (CoherentOldChamber.index b) := by
  unfold chamberCoeff CoherentMatrix.coefficient
  apply congrArg List.sum
  apply List.map_congr_left
  intro sc hsc
  simp only [chamber_feature_iff sc hsc]

theorem sum_list_map_complex {α β : Type*} (s : Finset α) (l : List β)
    (f : α → β → ℂ) :
    (∑ a ∈ s, (l.map (f a)).sum) = (l.map fun b => ∑ a ∈ s, f a b).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [sum_add_distrib, ih]

theorem chamberCoeff_eval (F : Feature → Feature → ℂ) :
    (∑ a, ∑ b, (chamberCoeff a b : ℂ) * F a b) =
      (dictionary39.map fun sc => (sc.2 : ℂ) *
        F (chamberFeature true sc.1) (chamberFeature false sc.1)).sum := by
  have he (a b : Feature) : (chamberCoeff a b : ℂ) * F a b =
      (dictionary39.map fun sc =>
        if chamberFeature true sc.1 = a ∧ chamberFeature false sc.1 = b
        then (sc.2 : ℂ) * F a b else 0).sum := by
    unfold chamberCoeff
    rw [Rat.cast_list_sum, List.map_map, ← List.sum_map_mul_right]
    apply congrArg List.sum
    apply List.map_congr_left
    intro sc _
    dsimp only [Function.comp_def]
    split_ifs <;> simp
  simp_rw [he, sum_list_map_complex]
  apply congrArg List.sum
  apply List.map_congr_left
  intro sc _
  have inner (a : Feature) :
      (∑ b : Feature, if chamberFeature true sc.1 = a ∧ chamberFeature false sc.1 = b
        then (sc.2 : ℂ) * F a b else 0) =
      if chamberFeature true sc.1 = a then (sc.2 : ℂ) * F a (chamberFeature false sc.1)
        else 0 := by
    by_cases ha : chamberFeature true sc.1 = a
    · simp only [ha, true_and, sum_ite_eq, mem_univ, ite_true]
    · simp only [ha, false_and, ite_false, sum_const_zero]
  simp_rw [inner]
  simp only [sum_ite_eq, mem_univ, ite_true]

end Sarkozy.PositiveRoots.CoherentFrame
