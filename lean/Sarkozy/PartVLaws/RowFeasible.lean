module

public import Sarkozy.PartVLaws.RowLabellings

/-! Every strict reference row gives a feasible pinned graph restriction. -/

@[expose] public section

namespace Sarkozy.PartVLaws.FieldGraphs.RowCase

open Finset Sarkozy.Labellings Sarkozy.JointRows

def pinnedDomain (c : RowCase) (a : Fin 3) : Finset (Fin 3 × c.Index) :=
  univ.filter fun v => v.1 = 1 ∨ v.1 = a

variable {p : ℕ} [Fact p.Prime]

theorem pinned_feasible (c : RowCase) (b x : c.Index → ZMod p)
    (hb : Function.Injective b) (hx : x ∈ Coll.strictSet (c.allowed b))
    (a : Fin 3) (ha : a = 0 ∨ a = 2) :
    Feasible (ZMod p) c.rowGraph (c.pinnedDomain a) (c.pack b x x) := by
  classical
  have hpa (i : c.Index) : c.pack b x x (a, i) = x i := by
    rcases ha with rfl | rfl <;> rfl
  have hp1 (i : c.Index) : c.pack b x x (1, i) = b i := rfl
  obtain ⟨hxi, hxa⟩ := (mem_filter.mp hx).2
  have hallow i := (c.allowed_graph_iff b i (x i)).mp (hxa i)
  have hxb (i j : c.Index) : x i ≠ b j := fun hij =>
    (hallow i).1 (hij ▸ mem_image_of_mem b (mem_univ j))
  have he1 (i j : c.Index) (h : c.edge (a, i) (1, j) = true) :
      quadraticChar (ZMod p) (b j - x i) = 1 := by
    apply (hallow i).2.2 j
    rcases ha with rfl | rfl
    · exact h
    · rwa [(c.pins_agree i j).1]
  have he2 (i j : c.Index) (h : c.edge (1, j) (a, i) = true) :
      quadraticChar (ZMod p) (x i - b j) = 1 := by
    apply (hallow i).2.1 j
    rcases ha with rfl | rfl
    · exact h
    · rwa [(c.pins_agree i j).2]
  constructor
  · rintro ⟨d, i⟩ hd ⟨e, j⟩ he hij
    have hd' : d = 1 ∨ d = a := (mem_filter.mp hd).2
    have he' : e = 1 ∨ e = a := (mem_filter.mp he).2
    rcases hd' with hd' | hd' <;> subst d <;>
      rcases he' with he' | he' <;> subst e
    · exact congrArg (Prod.mk 1) (hb hij)
    · exact False.elim (hxb j i (by simpa only [hpa, hp1] using hij.symm))
    · exact False.elim (hxb i j (by simpa only [hpa, hp1] using hij))
    · exact congrArg (Prod.mk a) (hxi (by simpa only [hpa] using hij))
  · rintro ⟨⟨d, i⟩, ⟨e, j⟩⟩ hedge hd he
    have hed := (c.mem_rowGraph (d, i) (e, j)).mp hedge
    have hd' : d = 1 ∨ d = a := (mem_filter.mp hd).2
    have he' : e = 1 ∨ e = a := (mem_filter.mp he).2
    rcases hd' with hd' | hd' <;> subst d <;>
      rcases he' with he' | he' <;> subst e
    · simp [c.no_internal_edges] at hed
    · simpa only [hpa, hp1] using he2 j i hed
    · simpa only [hpa, hp1] using he1 i j hed
    · simp [c.no_internal_edges] at hed

theorem pinned_count_ratio (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b x x' : c.Index → ZMod p) (hb : Function.Injective b)
    (hx : x ∈ Coll.strictSet (c.allowed b)) (hx' : x' ∈ Coll.strictSet (c.allowed b))
    (a : Fin 3) (ha : a = 0 ∨ a = 2) :
    (extCount c.rowGraph (c.pinnedDomain a) (c.pack b x x) : ℝ) ≤
      countRho p ^ 72 * extCount c.rowGraph (c.pinnedDomain a) (c.pack b x' x') := by
  have h := tail_count_ratio p hW hp c.rowGraph_card c.rowGraph c.rowGraph_degree
    (c.pinned_feasible b x hb hx a ha) (c.pinned_feasible b x' hb hx' a ha)
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  apply pow_le_pow_right₀ (one_le_countRho p)
  exact (card_le_univ _).trans c.rowGraph_card

end Sarkozy.PartVLaws.FieldGraphs.RowCase
