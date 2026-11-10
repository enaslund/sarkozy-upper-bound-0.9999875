module

public import Sarkozy.PartV.CoherentDiagonalCollectionData
public import Sarkozy.PartV.CoherentDiagonalSplit
public import Sarkozy.PartV.DictionaryCollectionMore

/-! The checked diagonal blocks evaluate to the physical symmetric-difference sum. -/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open scoped symmDiff

theorem diagonalCoefficient_eq (S : Support) :
    diagonalCoefficient S = coefficientAt diagonalRaw S := by
  unfold diagonalCoefficient coefficientAt diagonalRaw
  simp only [List.map_map, Function.comp_def]
  exact (sum_product_map dictionary39 dictionary39 _).symm

theorem diagonal_blocks_eval (f : Support → ℝ) :
    dictionaryEval diagonalBlocks.flatten f = dictionaryEval diagonalRaw f := by
  apply collect_list_eval
  · intro sc hsc
    obtain ⟨D, hD, hs⟩ := List.mem_flatten.mp hsc
    exact (diagonal_block_coefficients D hD sc hs).trans (diagonalCoefficient_eq _)
  · intro sc hsc
    change sc ∈ (dictionary39.product dictionary39).map
      (fun st => (st.1.1 ∆ st.2.1, st.1.2 * st.2.2)) at hsc
    obtain ⟨st, hst, rfl⟩ := List.mem_map.mp hsc
    obtain ⟨ha, hb⟩ := List.mem_product.mp hst
    have h := diagonal_block_coverage st.1 ha st.2 hb
    simpa only [diagonalMultiplicity, List.flatten_eq_flatMap, sum_flatMap_map, id_eq] using h

def diagonalTwoSided (sc : Support × ℚ) : Prop :=
  sc.1.Nonempty ∧ ¬OneSided false sc.1 ∧ sc.2 ≠ 0

instance (sc : Support × ℚ) : Decidable (diagonalTwoSided sc) := by
  unfold diagonalTwoSided
  infer_instance

def twoSidedBlocks : List Dictionary :=
  diagonalBlocks.map fun D => D.filter fun sc => decide (diagonalTwoSided sc)

def collectedTwoSided : Dictionary := twoSidedBlocks.flatten

theorem dictionaryEval_nonzero_filter (D : Dictionary) (P : Support → Prop) [DecidablePred P]
    (f : Support → ℝ) :
    dictionaryEval (D.filter fun sc => decide (P sc.1 ∧ sc.2 ≠ 0)) f =
      dictionaryEval (D.filter fun sc => decide (P sc.1)) f := by
  induction D with
  | nil => rfl
  | cons sc D ih =>
    by_cases hP : P sc.1 <;> by_cases hc : sc.2 = 0 <;>
      simp [dictionaryEval, hP, hc] at ih ⊢ <;> exact ih

theorem twoSided_collect_eval (f : Support → ℝ) :
    dictionaryEval (twoSidedRaw false) f = dictionaryEval collectedTwoSided f := by
  have h := diagonal_blocks_eval (fun S => if S.Nonempty ∧ ¬OneSided false S then f S else 0)
  rw [← dictionaryEval_filter, ← dictionaryEval_filter] at h
  change _ = dictionaryEval (diagonalBlocks.map
    (fun D => D.filter fun sc => decide (diagonalTwoSided sc))).flatten f
  rw [← List.filter_flatten]
  unfold diagonalTwoSided
  simp only [← and_assoc]
  rw [dictionaryEval_nonzero_filter diagonalBlocks.flatten
    (fun S => S.Nonempty ∧ ¬OneSided false S) f]
  exact h.symm

end Sarkozy.PartV.CoherentDictionary
