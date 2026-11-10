module

public import Sarkozy.PartV.CoherentChamberDensity
public import Sarkozy.L20Cap.BalancedCollision

/-! Transport the actual chamber cross kernel and collision event to L20. -/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset Sarkozy.Labellings Sarkozy.Extraction

def chamberCrossEdge (e : Fin 6 × Fin 6) : Vertex × Vertex :=
  if L20Cap.D20Z e.1 e.2 = 1 then
    (chamberVertices true e.1, chamberVertices false e.2)
  else (chamberVertices false e.2, chamberVertices true e.1)

theorem chamberCross_image :
    (collisionCross L20Cap.D20Z).image chamberCrossEdge = rawCrossEdges false := by
  decide +kernel

theorem chamberCross_inj : Set.InjOn chamberCrossEdge (collisionCross L20Cap.D20Z) := by
  decide +kernel

theorem chamberVertices_cover : ∀ v : Vertex,
    (∃ i, chamberVertices true i = v) ∨ (∃ i, chamberVertices false i = v) := by
  decide +kernel

variable {p : ℕ}

theorem join_chamber_left (x y : Fin 6 → ZMod p) (i : Fin 6) :
    joinHalves false (chamberLabelsEquiv true x) (chamberLabelsEquiv false y)
      (chamberVertices true i) = x i := by
  change joinHalves false (chamberLabelsEquiv true x) (chamberLabelsEquiv false y)
    (chamberEquiv true i).val = x i
  rw [joinHalves_left]
  change x ((chamberEquiv true).symm (chamberEquiv true i)) = x i
  rw [Equiv.symm_apply_apply]

theorem join_chamber_right (x y : Fin 6 → ZMod p) (i : Fin 6) :
    joinHalves false (chamberLabelsEquiv true x) (chamberLabelsEquiv false y)
      (chamberVertices false i) = y i := by
  change joinHalves false (chamberLabelsEquiv true x) (chamberLabelsEquiv false y)
    (chamberEquiv false i).val = y i
  rw [joinHalves_right]
  change y ((chamberEquiv false).symm (chamberEquiv false i)) = y i
  rw [Equiv.symm_apply_apply]

theorem chamberCross_difference (x y : Fin 6 → ZMod p) (e : Fin 6 × Fin 6)
    (he : e ∈ collisionCross L20Cap.D20Z) :
    let z := joinHalves false (chamberLabelsEquiv true x) (chamberLabelsEquiv false y)
    z (chamberCrossEdge e).2 - z (chamberCrossEdge e).1 =
      (L20Cap.D20Z e.1 e.2 : ZMod p) * (y e.2 - x e.1) := by
  have hs := (L20Cap.balanced_signs e.1 e.2).resolve_left (mem_filter.mp he).2
  rcases hs with hs | hs
  · simp [chamberCrossEdge, hs, join_chamber_left, join_chamber_right]
  · simp [chamberCrossEdge, hs, join_chamber_left, join_chamber_right]

/-- Exact identification of the sixteen-factor positive kernel. -/
theorem chamber_raw_kernel [Fact p.Prime] (x y : Fin 6 → ZMod p) :
    rawCrossKernel false
      (joinHalves false (chamberLabelsEquiv true x) (chamberLabelsEquiv false y)) =
        collisionKernel L20Cap.D20Z x y := by
  unfold rawCrossKernel collisionKernel
  rw [← chamberCross_image, prod_image chamberCross_inj]
  refine prod_congr rfl fun e he => ?_
  rw [chamberCross_difference x y e he]

theorem chamber_common_zero (x y : Fin 6 → ZMod p) :
    collisionCommon x y = 0 ↔ ∀ i j, x i ≠ y j := by
  unfold collisionCommon
  rw [card_eq_zero, ← disjoint_iff_inter_eq_empty, disjoint_left]
  constructor
  · intro h i j hij
    exact h (mem_image_of_mem _ (mem_univ i)) (hij ▸ mem_image_of_mem _ (mem_univ j))
  · intro h a ha hb
    obtain ⟨i, -, hi⟩ := mem_image.mp ha
    obtain ⟨j, -, hj⟩ := mem_image.mp hb
    exact h i j (hi.trans hj.symm)

theorem chamber_join_injective (x y : Fin 6 → ZMod p)
    (hx : Function.Injective x) (hy : Function.Injective y) :
    Function.Injective
      (joinHalves false (chamberLabelsEquiv true x) (chamberLabelsEquiv false y)) ↔
        ∀ i j, x i ≠ y j := by
  constructor
  · intro h i j hij
    have hv := @h (chamberVertices true i) (chamberVertices false j)
      (by simpa only [join_chamber_left, join_chamber_right] using hij)
    have hs := congrArg (cutSide false) hv
    simp [chamberVertices_side] at hs
  · intro h v w hvw
    rcases chamberVertices_cover v with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
      rcases chamberVertices_cover w with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [join_chamber_left, join_chamber_left] at hvw
      exact congrArg (chamberVertices true) (hx hvw)
    · rw [join_chamber_left, join_chamber_right] at hvw
      exact (h i j hvw).elim
    · rw [join_chamber_right, join_chamber_left] at hvw
      exact (h j i hvw.symm).elim
    · rw [join_chamber_right, join_chamber_right] at hvw
      exact congrArg (chamberVertices false) (hy hvw)

theorem chamber_collision_iff (x y : Fin 6 → ZMod p)
    (hx : Function.Injective x) (hy : Function.Injective y) :
    Collision false (chamberLabelsEquiv true x) (chamberLabelsEquiv false y) ↔
      1 ≤ collisionCommon x y := by
  have hb : Function.Injective (chamberLabelsEquiv false y) := by
    intro u v h
    exact (chamberEquiv false).symm.injective (hy h)
  simp only [Collision, hb, true_and, chamber_join_injective x y hx hy,
    ← chamber_common_zero]
  omega

end Sarkozy.PartV.CoherentDictionary
