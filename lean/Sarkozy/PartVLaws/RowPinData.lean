module

public import Sarkozy.PartVLaws.RowRestriction
public import Sarkozy.JointRows.AllowedProduct
public import Sarkozy.JointRows.LawEquiv

/-! The ten rows' actual pins, encoded in the coordinates of pinned extraction. -/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.PartVLaws.FieldGraphs.RowCase

open Finset Sarkozy.Labellings Sarkozy.JointRows Sarkozy.ExtractionK

noncomputable def indexEquiv (c : RowCase) : c.Index ≃ Fin (Fintype.card c.Index) :=
  Fintype.equivFin c.Index

variable {p : ℕ}

noncomputable def labelEquiv (c : RowCase) :
    (c.Index → ZMod p) ≃ (Fin (Fintype.card c.Index) → ZMod p) :=
  Equiv.arrowCongr c.indexEquiv (Equiv.refl _)

noncomputable def pinData (c : RowCase) (b : c.Index → ZMod p)
    (i : Fin (Fintype.card c.Index)) (t : ZMod p) : ℤ :=
  ∑ j, if b j = t then c.pinSign (c.indexEquiv.symm i) j else 0

theorem pinData_at (c : RowCase) (b : c.Index → ZMod p) (hb : Function.Injective b)
    (i : Fin (Fintype.card c.Index)) (j : c.Index) :
    c.pinData b i (b j) = c.pinSign (c.indexEquiv.symm i) j := by
  simp [pinData, hb.eq_iff]

theorem pinData_zero (c : RowCase) (b : c.Index → ZMod p)
    (i : Fin (Fintype.card c.Index)) {t : ZMod p} (ht : t ∉ c.fixedLabels b) :
    c.pinData b i t = 0 := by
  unfold pinData
  apply sum_eq_zero
  intro j _
  have hj : b j ≠ t := fun h => ht (h ▸ mem_image_of_mem b (mem_univ j))
  exact ite_eq_right hj

theorem pinData_cases (c : RowCase) (b : c.Index → ZMod p) (hb : Function.Injective b)
    (i : Fin (Fintype.card c.Index)) (t : ZMod p) :
    c.pinData b i t = 0 ∨ c.pinData b i t = 1 ∨ c.pinData b i t = -1 := by
  by_cases ht : t ∈ c.fixedLabels b
  · obtain ⟨j, _, rfl⟩ := mem_image.mp ht
    rw [c.pinData_at b hb]
    exact c.pinSign_cases _ _
  · exact Or.inl (c.pinData_zero b i ht)

theorem pinData_mem (c : RowCase) (b : c.Index → ZMod p)
    (i : Fin (Fintype.card c.Index)) (t : ZMod p) (ht : c.pinData b i t ≠ 0) :
    t ∈ c.fixedLabels b := by
  by_contra h
  exact ht (c.pinData_zero b i h)

variable [Fact p.Prime]

theorem pinData_roots (c : RowCase) (b : c.Index → ZMod p) (hb : Function.Injective b)
    (i : Fin (Fintype.card c.Index)) :
    pinRoots (c.pinData b) i = (c.pinNeighbours (c.indexEquiv.symm i)).image b := by
  ext t
  constructor
  · intro ht
    have ht' := (mem_filter.mp ht).2
    obtain ⟨j, _, rfl⟩ := mem_image.mp (c.pinData_mem b i t ht')
    apply mem_image_of_mem
    exact mem_filter.mpr ⟨mem_univ _, by rwa [c.pinData_at b hb] at ht'⟩
  · intro ht
    obtain ⟨j, hj, rfl⟩ := mem_image.mp ht
    exact mem_filter.mpr ⟨mem_univ _, by
      rw [c.pinData_at b hb]
      exact (mem_filter.mp hj).2⟩

theorem pinData_count (c : RowCase) (b : c.Index → ZMod p) (hb : Function.Injective b)
    (i : Fin (Fintype.card c.Index)) : pinCount (c.pinData b) i ≤ 4 := by
  unfold pinCount
  rw [c.pinData_roots b hb]
  exact card_image_le.trans ((c.pin_degree _).trans c.pins_le)

theorem pinData_allowed (c : RowCase) (b : c.Index → ZMod p) (hb : Function.Injective b)
    (i : Fin (Fintype.card c.Index)) :
    pinAllowed (c.fixedLabels b) (c.pinData b) i = c.allowed b (c.indexEquiv.symm i) := by
  ext t
  simp only [pinAllowed, allowed, admissible, mem_filter, mem_univ, true_and]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h j
    have hj := (mem_filter.mp j.2).2
    have hpm : c.pinSign (c.indexEquiv.symm i) j.1 = 1 ∨
        c.pinSign (c.indexEquiv.symm i) j.1 = -1 := by
      rcases c.pinSign_cases _ _ with h0 | h1 | h1
      · exact False.elim (hj h0)
      · exact Or.inl h1
      · exact Or.inr h1
    have hh := h (b j.1) (by rwa [c.pinData_at b hb])
    rw [c.pinData_at b hb] at hh
    exact (pin_cond_iff hpm _).mp hh
  · intro h u hu
    obtain ⟨j, _, rfl⟩ := mem_image.mp (c.pinData_mem b i u hu)
    rw [c.pinData_at b hb] at hu ⊢
    have hj : j ∈ c.pinNeighbours (c.indexEquiv.symm i) :=
      mem_filter.mpr ⟨mem_univ _, hu⟩
    have hpm : c.pinSign (c.indexEquiv.symm i) j = 1 ∨
        c.pinSign (c.indexEquiv.symm i) j = -1 := by
      rcases c.pinSign_cases _ _ with h0 | h1 | h1
      · exact False.elim (hu h0)
      · exact Or.inl h1
      · exact Or.inr h1
    exact (pin_cond_iff hpm _).mpr (h ⟨j, hj⟩)

end Sarkozy.PartVLaws.FieldGraphs.RowCase
