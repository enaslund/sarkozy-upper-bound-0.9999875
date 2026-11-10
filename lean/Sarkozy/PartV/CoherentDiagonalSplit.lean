module

public import Sarkozy.PartV.CoherentDiagonalBound

/-! Isolate the constant, one-sided, and two-sided auxiliary-diagonal contributions. -/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset

def twoSidedRaw (isLayer : Bool) : Dictionary :=
  diagonalRaw.filter fun sc => decide (sc.1.Nonempty ∧ ¬OneSided isLayer sc.1)

theorem diagonal_partition_eval (D : Dictionary) (isLayer : Bool) (f : Support → ℝ) :
    dictionaryEval D f = (coefficientAt D ∅ : ℝ) * f ∅ +
      dictionaryEval (D.filter fun sc => decide (OneSided isLayer sc.1)) f +
      dictionaryEval (D.filter fun sc => decide (sc.1.Nonempty ∧ ¬OneSided isLayer sc.1)) f := by
  induction D with
  | nil => simp [dictionaryEval, coefficientAt]
  | cons sc D ih =>
    by_cases he : sc.1 = ∅
    · simp [dictionaryEval, coefficientAt, he, OneSided] at ih ⊢
      linarith
    · have hn : sc.1.Nonempty := nonempty_iff_ne_empty.mpr he
      by_cases ho : OneSided isLayer sc.1
      · simp [dictionaryEval, coefficientAt, he, hn, ho] at ih ⊢
        linarith
      · simp [dictionaryEval, coefficientAt, he, hn, ho] at ih ⊢
        linarith

variable {p : ℕ} [Fact p.Prime]

theorem diagonal_trace_split (hp : p ≠ 2) (isLayer : Bool) (x : Vertex → ZMod p)
    (hleft : Set.InjOn x {v | cutSide isLayer v = true})
    (hright : Set.InjOn x {v | cutSide isLayer v = false}) :
    dictionaryEval diagonalRaw (fun S => trace S x / p) =
      13 / 75 + (if isLayer then (8 / 75 : ℝ) / p else -(8 / 45 : ℝ) / p) +
      dictionaryEval (twoSidedRaw isLayer) (fun S => trace S x / p) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have he : trace ∅ x / p = 1 := by simp [trace, hp0]
  rw [diagonal_partition_eval diagonalRaw isLayer, diagonal_constant, he]
  change ((13 / 75 : ℚ) : ℝ) * 1 +
    dictionaryEval (oneSidedRaw isLayer) (fun S => trace S x / p) + _ = _
  rw [oneSided_trace hp isLayer x hleft hright]
  norm_num [twoSidedRaw]

theorem auxiliary_diagonal_split_error (hp : p ≠ 2) (isLayer : Bool) (x : Vertex → ZMod p)
    (hleft : Set.InjOn x {v | cutSide isLayer v = true})
    (hright : Set.InjOn x {v | cutSide isLayer v = false}) :
    |(∑ z, (dictionaryEval dictionary39 (fun S => evaluation S x z)) ^ 2) / p -
      (13 / 75 + (if isLayer then (8 / 75 : ℝ) / p else -(8 / 45 : ℝ) / p) +
        dictionaryEval (twoSidedRaw isLayer) (fun S => trace S x / p))| ≤
      (1936 / 75 : ℝ) / p := by
  rw [← diagonal_trace_split hp isLayer x hleft hright]
  exact auxiliary_diagonal_error x

end Sarkozy.PartV.CoherentDictionary
