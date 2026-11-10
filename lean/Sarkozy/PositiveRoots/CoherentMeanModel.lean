module

public import Sarkozy.PositiveRoots.CoherentMatrixAlgebra

/-!
# The three invariant-mean coefficient matrices of the coherent root

These are the physical dictionary's chamber core, chamber mixed, and layer
blocks in `imp:local:coherent-39`. The caps are `7/100`, `21/100`, and `21/100`.
-/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentMean

open Finset Sarkozy.PartV Sarkozy.PartV.CoherentDictionary

inductive Kind where
  | core | mixed | layer
  deriving DecidableEq

def size : Kind → ℕ
  | .core => 5
  | .mixed => 10
  | .layer => 15

def active : Kind → List ℕ
  | .core => [19, 35, 49, 50, 51]
  | .mixed => [7, 11, 13, 14, 15, 28, 44, 52, 56, 60]
  | .layer => [11, 13, 19, 22, 25, 26, 27, 37, 38, 41, 44, 45, 50, 52, 54]

def index (k : Kind) (i : Fin (size k)) : Fin 64 :=
  ⟨(active k).getD i.val 0 % 64, Nat.mod_lt _ (by decide)⟩

def layerCode (s : Support) (l : Fin 2) : ℕ :=
  ∑ v ∈ s, if v.2 = l then 2 ^ v.1.val else 0

def layerCoefficient (i j : Fin 64) : ℚ :=
  (dictionary39.map fun sc =>
    if layerCode sc.1 0 = i.val ∧ layerCode sc.1 1 = j.val then sc.2 else 0).sum

def layerNumerator (i j : Fin 64) : ℤ :=
  (dictionary39.map fun sc =>
    if layerCode sc.1 0 = i.val ∧ layerCode sc.1 1 = j.val then
      (if 0 < sc.2 then 1 else -1) else 0).sum

theorem layerCoefficient_eq (i j : Fin 64) :
    layerCoefficient i j = (layerNumerator i j : ℚ) / 15 := by
  have hc : ∀ sc ∈ dictionary39,
      sc.2 = (if 0 < sc.2 then (1 : ℤ) else -1) / (15 : ℚ) := by decide +kernel
  unfold layerCoefficient layerNumerator
  rw [Int.cast_list_sum, div_eq_mul_inv, List.map_map, ← List.sum_map_mul_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro sc hsc
  dsimp only [Function.comp_def]
  split_ifs with h hpos
  · simpa only [hpos, ite_true, Int.cast_one, one_mul, one_div] using hc sc hsc
  · simpa only [hpos, ite_false, Int.cast_neg, Int.cast_one, div_eq_mul_inv] using hc sc hsc
  · simp

def numerator (k : Kind) (i j : Fin (size k)) : ℤ :=
  if k = .layer then layerNumerator (index k i) (index k j)
  else CoherentMatrix.coefficientNumerator (index k i) (index k j)

noncomputable def leading (k : Kind) (i j : Fin (size k)) : ℂ :=
  (numerator k i j : ℂ) / 15

def capNumerator : Kind → ℤ
  | .core => 21
  | .mixed | .layer => 63

def cap (k : Kind) : ℚ := (capNumerator k : ℚ) / 300

def modelReal (k : Kind) (i j : Fin (size k)) : ℤ :=
  20 * numerator k i j + if i = j then capNumerator k else 0

theorem index_injective (k : Kind) : Function.Injective (index k) := by
  cases k <;> decide +kernel

theorem chamber_support_coverage : ∀ sc ∈ dictionary39,
    (∃ i j : Fin (size .core), CoherentMatrix.leftCode sc.1 = (index .core i).val ∧
      CoherentMatrix.rightCode sc.1 = (index .core j).val) ∨
    (∃ i j : Fin (size .mixed), CoherentMatrix.leftCode sc.1 = (index .mixed i).val ∧
      CoherentMatrix.rightCode sc.1 = (index .mixed j).val) := by
  decide +kernel

theorem chamber_separation : ∀ (i : Fin (size .core)) (j : Fin (size .mixed)),
    CoherentMatrix.coefficient (index .core i) (index .mixed j) = 0 ∧
      CoherentMatrix.coefficient (index .mixed j) (index .core i) = 0 := by
  decide +kernel

theorem layer_support_coverage : ∀ sc ∈ dictionary39,
    ∃ i j : Fin (size .layer), layerCode sc.1 0 = (index .layer i).val ∧
      layerCode sc.1 1 = (index .layer j).val := by
  decide +kernel

end Sarkozy.PositiveRoots.CoherentMean
