module

public import Sarkozy.Reflection.Holder
public import Mathlib.Data.ZMod.Basic

/-!
# The actual 72 slots and their sorting sequence

The slots are `(ℤ/6ℤ) × (ℤ/6ℤ) × (ℤ/2ℤ)`. The chamber half at a is
`{a,a+1,a+2}` and the chamber reflection is `j ↦ 2a-1-j`.
Finite checks below use kernel reduction (`decide`), never native evaluation.
-/

@[expose] public section

namespace Sarkozy

namespace ReflectionCut

variable {V : Type*} [Fintype V] [DecidableEq V]

def prodLeft (c : ReflectionCut V) (W : Type*) [Fintype W] [DecidableEq W] :
    ReflectionCut (V × W) where
  half := c.half.product Finset.univ
  flip := Equiv.prodCongr c.flip (Equiv.refl W)
  flip_flip := by intro v; exact Prod.ext (c.flip_flip v.1) rfl
  crosses := by
    intro v
    change (c.flip v.1, v.2) ∈ c.half.product Finset.univ ↔
      (v.1, v.2) ∉ c.half.product Finset.univ
    constructor
    · intro h hin
      exact (c.crosses v.1).mp (Finset.mem_product.mp h).1 (Finset.mem_product.mp hin).1
    · intro h
      apply Finset.mem_product.mpr
      refine ⟨(c.crosses v.1).mpr ?_, Finset.mem_univ _⟩
      intro hv
      exact h (Finset.mem_product.mpr ⟨hv, Finset.mem_univ _⟩)

def prodRight (c : ReflectionCut V) (W : Type*) [Fintype W] [DecidableEq W] :
    ReflectionCut (W × V) where
  half := Finset.univ.product c.half
  flip := Equiv.prodCongr (Equiv.refl W) c.flip
  flip_flip := by intro v; exact Prod.ext rfl (c.flip_flip v.2)
  crosses := by
    intro v
    change (v.1, c.flip v.2) ∈ Finset.univ.product c.half ↔
      (v.1, v.2) ∉ Finset.univ.product c.half
    constructor
    · intro h hin
      exact (c.crosses v.2).mp (Finset.mem_product.mp h).2 (Finset.mem_product.mp hin).2
    · intro h
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_univ _, (c.crosses v.2).mpr ?_⟩
      intro hv
      exact h (Finset.mem_product.mpr ⟨Finset.mem_univ _, hv⟩)

end ReflectionCut

abbrev Chamber := ZMod 6
abbrev Layer := ZMod 2
abbrev Slot := Chamber × Chamber × Layer

def chamberReflection (a : Chamber) : Chamber ≃ Chamber where
  toFun j := 2 * a - 1 - j
  invFun j := 2 * a - 1 - j
  left_inv := by intro j; ring
  right_inv := by intro j; ring

def chamberCut (a : Chamber) : ReflectionCut Chamber where
  half := {a, a + 1, a + 2}
  flip := chamberReflection a
  flip_flip := by intro j; change 2 * a - 1 - (2 * a - 1 - j) = j; ring
  crosses := by
    have h : ∀ a j : Chamber,
        2 * a - 1 - j ∈ ({a, a + 1, a + 2} : Finset Chamber) ↔
          j ∉ ({a, a + 1, a + 2} : Finset Chamber) := by decide
    exact h a

def layerCut : ReflectionCut Layer where
  half := {0}
  flip := {
    toFun := fun j => 1 - j
    invFun := fun j => 1 - j
    left_inv := by intro j; ring
    right_inv := by intro j; ring }
  flip_flip := by intro j; change 1 - (1 - j) = j; ring
  crosses := by decide

def firstChamberCut (a : Chamber) : ReflectionCut Slot :=
  (chamberCut a).prodLeft (Chamber × Layer)

def secondChamberCut (a : Chamber) : ReflectionCut Slot :=
  ((chamberCut a).prodLeft Layer).prodRight Chamber

def reservedCut : ReflectionCut Slot :=
  (layerCut.prodRight Chamber).prodRight Chamber

def slotSortingCuts : List (ReflectionCut Slot) :=
  [firstChamberCut 0, firstChamberCut 4, firstChamberCut 0,
    secondChamberCut 0, secondChamberCut 4, secondChamberCut 0, reservedCut]

theorem card_slot : Fintype.card Slot = 72 := by decide

theorem chamber_sorting : ∀ j : Chamber,
    (chamberCut 0).foldPlus ((chamberCut 4).foldPlus ((chamberCut 0).foldPlus j)) = 0 := by
  decide

set_option maxHeartbeats 2000000 in
/-- The seven explicit folds collapse every slot to the origin. -/
theorem slot_sorting : IsSorting slotSortingCuts (0, 0, 0) := by
  unfold IsSorting
  decide

def chamberRotation (j : Chamber) : Chamber := if j.val % 2 = 0 then j + 2 else j - 2

theorem chamber_rotation_injective : Function.Injective chamberRotation := by
  decide

theorem chamber_rotation_commutes_reflection : ∀ a j : Chamber,
    chamberRotation (chamberReflection a j) = chamberReflection a (chamberRotation j) := by
  decide

def querySource (j : Chamber) : Slot := (0, j, 0)
def queryTarget (j : Chamber) : Slot := (2, chamberRotation j, 1)

/-- The six queries have twelve distinct endpoints. -/
theorem query_endpoints_injective : Function.Injective
    (fun p : Chamber × Bool => if p.2 then queryTarget p.1 else querySource p.1) := by
  decide

theorem queries_cross_reserved : ∀ j : Chamber,
    querySource j ∈ reservedCut.half ∧ queryTarget j ∉ reservedCut.half := by
  decide

/-- Source and reflected-target labels are distinct within the same half. -/
theorem reflected_query_endpoints_injective : Function.Injective
    (fun p : Chamber × Bool =>
      if p.2 then reservedCut.flip (queryTarget p.1) else querySource p.1) := by
  decide

/-- Only positivity at the cuts actually used by sorting is needed here. -/
def SlotReflectionPositive {X : Type*}
    (L : ((Slot → X) → ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∀ c ∈ slotSortingCuts, c.Positive L

theorem slot_diagonal_nonneg {X : Type*}
    {L : ((Slot → X) → ℝ) →ₗ[ℝ] ℝ} (hp : SlotReflectionPositive L) (f : X → ℝ) :
    0 ≤ diagonalIntegral L f := by
  exact (hp (firstChamberCut 0) (by simp [slotSortingCuts])).diagonal_nonneg f

theorem slot_signed_holder {X : Type*}
    {L : ((Slot → X) → ℝ) →ₗ[ℝ] ℝ} (hp : SlotReflectionPositive L) (a : Slot → X → ℝ) :
    |multilinearIntegral L a| ≤ ∏ v, diagonalIntegral L (a v) ^ ((1 : ℝ) / 72) := by
  simpa only [card_slot, Nat.cast_ofNat] using
    signed_holder_of_sorting L (slot_diagonal_nonneg hp) slotSortingCuts hp slot_sorting a

end Sarkozy
