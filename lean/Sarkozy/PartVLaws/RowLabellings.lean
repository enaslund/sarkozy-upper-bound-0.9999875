module

public import Sarkozy.PartVLaws.RowCompatibility

/-! The pinned-kernel support is exactly the set of actual three-row labellings. -/

@[expose] public section

namespace Sarkozy.PartVLaws.FieldGraphs.RowCase

open Finset Sarkozy.Labellings Sarkozy.JointRows

variable {p : ℕ} [Fact p.Prime]

theorem row_allowed (c : RowCase) (z : Fin 3 × c.Index → ZMod p)
    (hi : Function.Injective z)
    (he : ∀ a d, c.edge a d = true → quadraticChar (ZMod p) (z d - z a) = 1)
    (a : Fin 3) (ha : a = 0 ∨ a = 2) (i : c.Index) :
    z (a, i) ∈ c.allowed (fun j => z (1, j)) i := by
  rw [c.allowed_graph_iff]
  have ha1 : a ≠ 1 := by rcases ha with rfl | rfl <;> decide
  refine ⟨?_, ?_, ?_⟩
  · intro h
    obtain ⟨j, _, hj⟩ := mem_image.mp h
    exact ha1 (congrArg Prod.fst (hi hj.symm))
  · intro j hj
    apply he (1, j) (a, i)
    rcases ha with rfl | rfl
    · exact hj
    · rwa [← (c.pins_agree i j).2]
  · intro j hj
    apply he (a, i) (1, j)
    rcases ha with rfl | rfl
    · exact hj
    · rwa [← (c.pins_agree i j).1]

theorem pack_mem_iff (c : RowCase) (b x y : c.Index → ZMod p)
    (hb : Function.Injective b) :
    c.pack b x y ∈ injLabellings (ZMod p) c.rowGraph ↔
      x ∈ Coll.strictSet (c.allowed b) ∧ y ∈ Coll.strictSet (c.allowed b) ∧
        Coll.Compatible c.finSigns (c.labelEquiv x) (c.labelEquiv y) := by
  classical
  simp only [injLabellings, Coll.strictSet, mem_filter, mem_univ, true_and]
  rw [c.compatible_iff]
  constructor
  · intro h
    have hi : Function.Injective (c.pack b x y) := fun a d had =>
      h.1 a (mem_univ _) d (mem_univ _) had
    have he : ∀ a d, c.edge a d = true →
        quadraticChar (ZMod p) (c.pack b x y d - c.pack b x y a) = 1 :=
      fun a d had => h.2 (a, d) ((c.mem_rowGraph a d).mpr had) (mem_univ _) (mem_univ _)
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · intro i j hij
      exact congrArg Prod.snd (hi (show c.pack b x y (0, i) = c.pack b x y (0, j) from hij))
    · exact fun i => c.row_allowed _ hi he 0 (Or.inl rfl) i
    · intro i j hij
      exact congrArg Prod.snd (hi (show c.pack b x y (2, i) = c.pack b x y (2, j) from hij))
    · exact fun i => c.row_allowed _ hi he 2 (Or.inr rfl) i
    · intro i j hij
      have hh := congrArg Prod.fst
        (hi (show c.pack b x y (0, i) = c.pack b x y (2, j) from hij))
      exact (by decide : (0 : Fin 3) ≠ 2) hh
    · exact fun i j hij => he (0, i) (2, j) hij
    · exact fun i j hij => he (2, j) (0, i) hij
  · rintro ⟨⟨hxi, hxa⟩, ⟨hyi, hya⟩, hxy, h02, h20⟩
    have hx i := (c.allowed_graph_iff b i (x i)).mp (hxa i)
    have hy i := (c.allowed_graph_iff b i (y i)).mp (hya i)
    have hi := c.pack_injective b x y hb hxi hyi
      (fun i j hij => (hx i).1 (hij ▸ mem_image_of_mem b (mem_univ j)))
      (fun i j hij => (hy i).1 (hij ▸ mem_image_of_mem b (mem_univ j))) hxy
    refine ⟨fun a _ d _ had => hi had, ?_⟩
    rintro ⟨⟨a, i⟩, ⟨d, j⟩⟩ hed _ _
    have he := (c.mem_rowGraph (a, i) (d, j)).mp hed
    fin_cases a <;> fin_cases d <;> dsimp [pack]
    · simp [c.no_internal_edges] at he
    · exact (hx i).2.2 j he
    · exact h02 i j he
    · exact (hx j).2.1 i he
    · simp [c.no_internal_edges] at he
    · exact (hy j).2.1 i (by rwa [(c.pins_agree j i).2])
    · exact h20 j i he
    · exact (hy i).2.2 j (by rwa [(c.pins_agree i j).1])
    · simp [c.no_internal_edges] at he

end Sarkozy.PartVLaws.FieldGraphs.RowCase
