module

public import Sarkozy.PartVLaws.RowNormalized

/-! The actual three-row graphs behind the ten pinned kernel estimates. -/

@[expose] public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Sarkozy.PartVLaws.FieldGraphs.RowCase

open Finset Sarkozy.Labellings Sarkozy.PartV

def rowGraph : (c : RowCase) → OrientedGraph (Fin 3 × c.Index)
  | .FL1 => fieldGraph .F .L (Fin 1)
  | .FL2 => fieldGraph .F .L (Fin 2)
  | .FF1 => fieldGraph .F .F (Fin 1)
  | .FF2 => fieldGraph .F .F (Fin 2)
  | .FE1 => fieldGraph .F .E (Fin 1)
  | .FE2 => fieldGraph .F .E (Fin 2)
  | .EL1 => fieldGraph .E .L (Fin 1)
  | .EL2 => fieldGraph .E .L (Fin 2)
  | .EF1 => fieldGraph .E .F (Fin 1)
  | .EF2 => fieldGraph .E .F (Fin 2)

theorem mem_rowGraph (c : RowCase) (a b : Fin 3 × c.Index) :
    (a, b) ∈ c.rowGraph.E ↔ c.edge a b = true := by
  cases c
  · exact mem_twoLayerGraph typeF typeL typeF_proper typeL_proper (a, b)
  · exact mem_twoLayerGraph typeF typeL typeF_proper typeL_proper (a, b)
  · exact mem_twoLayerGraph typeF typeF typeF_proper typeF_proper (a, b)
  · exact mem_twoLayerGraph typeF typeF typeF_proper typeF_proper (a, b)
  · exact mem_twoLayerGraph typeF typeE typeF_proper typeE_proper (a, b)
  · exact mem_twoLayerGraph typeF typeE typeF_proper typeE_proper (a, b)
  · exact mem_twoLayerGraph typeE typeL typeE_proper typeL_proper (a, b)
  · exact mem_twoLayerGraph typeE typeL typeE_proper typeL_proper (a, b)
  · exact mem_twoLayerGraph typeE typeF typeE_proper typeF_proper (a, b)
  · exact mem_twoLayerGraph typeE typeF typeE_proper typeF_proper (a, b)

theorem edge_asymm (c : RowCase) (a b : Fin 3 × c.Index) (h : c.edge a b = true) :
    c.edge b a = false := by
  apply Bool.eq_false_iff.mpr
  intro hb
  exact c.rowGraph.oriented a b ((c.mem_rowGraph a b).mpr h) ((c.mem_rowGraph b a).mpr hb)

theorem rowGraph_card (c : RowCase) : Fintype.card (Fin 3 × c.Index) ≤ 72 := by
  rw [Fintype.card_prod, Fintype.card_fin]
  have h := c.card_index
  omega

theorem rowGraph_degree (c : RowCase) (v : Fin 3 × c.Index) :
    nbrCount c.rowGraph univ v ≤ 20 := by
  cases c
  · exact fieldGraph_degree_one .F .L v
  · exact fieldGraph_degree_two .F .L v
  · exact fieldGraph_degree_one .F .F v
  · exact fieldGraph_degree_two .F .F v
  · exact fieldGraph_degree_one .F .E v
  · exact fieldGraph_degree_two .F .E v
  · exact fieldGraph_degree_one .E .L v
  · exact fieldGraph_degree_two .E .L v
  · exact fieldGraph_degree_one .E .F v
  · exact fieldGraph_degree_two .E .F v

variable {p : ℕ} [Fact p.Prime]

theorem allowed_sign_iff (c : RowCase) (b : c.Index → ZMod p) (i : c.Index) (t : ZMod p) :
    t ∈ c.allowed b i ↔ t ∉ c.fixedLabels b ∧ ∀ j, c.pinSign i j ≠ 0 →
      quadraticChar (ZMod p) ((c.pinSign i j : ZMod p) * (t - b j)) = 1 := by
  simp only [allowed, admissible, mem_filter, mem_univ, true_and]
  refine and_congr_right fun _ => ?_
  have hpm (j : c.Index) (hj : c.pinSign i j ≠ 0) :
      c.pinSign i j = 1 ∨ c.pinSign i j = -1 := by
    rcases c.pinSign_cases i j with h | h | h
    · exact False.elim (hj h)
    · exact Or.inl h
    · exact Or.inr h
  constructor
  · intro h j hj
    exact (ExtractionK.pin_cond_iff (hpm j hj) _).mpr
      (h ⟨j, mem_filter.mpr ⟨mem_univ _, hj⟩⟩)
  · intro h j
    exact (ExtractionK.pin_cond_iff (hpm j.1 (mem_filter.mp j.2).2) _).mp
      (h j.1 (mem_filter.mp j.2).2)

theorem allowed_graph_iff (c : RowCase) (b : c.Index → ZMod p) (i : c.Index) (t : ZMod p) :
    t ∈ c.allowed b i ↔ t ∉ c.fixedLabels b ∧
      (∀ j, c.edge (1, j) (0, i) = true → quadraticChar (ZMod p) (t - b j) = 1) ∧
      (∀ j, c.edge (0, i) (1, j) = true → quadraticChar (ZMod p) (b j - t) = 1) := by
  rw [c.allowed_sign_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    constructor
    · intro j hj
      have hs : c.pinSign i j = 1 := by simp [pinSign, hj]
      have hh := h j (by rw [hs]; norm_num)
      simpa only [hs, Int.cast_one, one_mul] using hh
    · intro j hj
      have ha := c.edge_asymm (0, i) (1, j) hj
      have hs : c.pinSign i j = -1 := by simp [pinSign, hj, ha]
      have hh := h j (by rw [hs]; norm_num)
      simpa only [hs, Int.cast_neg, Int.cast_one, neg_one_mul, neg_sub] using hh
  · rintro ⟨h1, h2⟩ j hj
    unfold pinSign at hj ⊢
    split_ifs with h10 h01
    · simpa only [Int.cast_one, one_mul] using h1 j h10
    · simpa only [Int.cast_neg, Int.cast_one, neg_one_mul, neg_sub] using h2 j h01
    · exact False.elim (hj (by simp [h10, h01]))

end Sarkozy.PartVLaws.FieldGraphs.RowCase
