module

public import Sarkozy.PositiveRoots.CoherentProductGeometry
public import Sarkozy.PartV.CoherentDiagonalCollection

/-! Collected auxiliary-diagonal supports and the exact three operator budgets. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.PartV.CoherentDictionary

def PrivateDiagonal (S : Support) : Prop :=
  (privateSupport true S).Nonempty ∧ (privateSupport false S).Nonempty

instance (S : Support) : Decidable (PrivateDiagonal S) := by unfold PrivateDiagonal; infer_instance

def CoreDiagonal (S : Support) : Prop :=
  (coreSupport true S).Nonempty ∧ (coreSupport false S).Nonempty

instance (S : Support) : Decidable (CoreDiagonal S) := by unfold CoreDiagonal; infer_instance

def CrossDiagonal (S : Support) : Prop := ∃ i : Fin 4, ∃ j : Fin 2,
  (chamberSupport true S = {coreVertex i} ∧ chamberSupport false S = {privateVertex j}) ∨
    (chamberSupport true S = {privateVertex j} ∧ chamberSupport false S = {coreVertex i})

instance (S : Support) : Decidable (CrossDiagonal S) := by unfold CrossDiagonal; infer_instance

def diagonalCoreFactor (S : Finset (Fin 4)) : ℚ := if S.card = 1 then 1 else 4

def diagonalPrivateCost (sc : Support × ℚ) : ℚ :=
  if PrivateDiagonal sc.1 then |sc.2| else 0

def diagonalCoreCost (sc : Support × ℚ) : ℚ :=
  if ¬PrivateDiagonal sc.1 ∧ CoreDiagonal sc.1 then
    |sc.2| * diagonalCoreFactor (coreSupport true sc.1) *
      diagonalCoreFactor (coreSupport false sc.1) else 0

def diagonalCrossCost (sc : Support × ℚ) : ℚ :=
  if ¬PrivateDiagonal sc.1 ∧ ¬CoreDiagonal sc.1 then |sc.2| else 0

def diagonalPrivateBudget : ℚ :=
  (twoSidedBlocks.map fun D => (D.map diagonalPrivateCost).sum).sum

def diagonalCoreBudget : ℚ :=
  (twoSidedBlocks.map fun D => (D.map diagonalCoreCost).sum).sum

def diagonalCrossBudget : ℚ :=
  (twoSidedBlocks.map fun D => (D.map diagonalCrossCost).sum).sum

theorem diagonal_private_budget : diagonalPrivateBudget = 44 / 15 := by decide +kernel

theorem diagonal_core_budget : diagonalCoreBudget = 3712 / 225 := by decide +kernel

theorem diagonal_cross_budget : diagonalCrossBudget = 32 / 225 := by decide +kernel

theorem diagonal_cross_geometry_blocks : ∀ D ∈ twoSidedBlocks, ∀ sc ∈ D,
    ¬PrivateDiagonal sc.1 → ¬CoreDiagonal sc.1 → CrossDiagonal sc.1 := by decide +kernel

theorem diagonal_cross_geometry (sc : Support × ℚ) (hsc : sc ∈ collectedTwoSided)
    (hp : ¬PrivateDiagonal sc.1) (hc : ¬CoreDiagonal sc.1) : CrossDiagonal sc.1 := by
  obtain ⟨D, hD, hs⟩ := List.mem_flatten.mp hsc
  exact diagonal_cross_geometry_blocks D hD sc hs hp hc

theorem diagonal_private_sum : (collectedTwoSided.map diagonalPrivateCost).sum = 44 / 15 := by
  rw [collectedTwoSided, List.flatten_eq_flatMap, sum_flatMap_map]
  exact diagonal_private_budget

theorem diagonal_core_sum : (collectedTwoSided.map diagonalCoreCost).sum = 3712 / 225 := by
  rw [collectedTwoSided, List.flatten_eq_flatMap, sum_flatMap_map]
  exact diagonal_core_budget

theorem diagonal_cross_sum : (collectedTwoSided.map diagonalCrossCost).sum = 32 / 225 := by
  rw [collectedTwoSided, List.flatten_eq_flatMap, sum_flatMap_map]
  exact diagonal_cross_budget

end Sarkozy.PositiveRoots.CoherentFrame
