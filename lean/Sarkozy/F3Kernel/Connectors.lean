module

public import Sarkozy.F3Kernel.RootLayouts

/-!
# Soundness of a connector decision

An accepted connector adds its edge to one of the two masks, or keeps a previously absent
edge unchanged. The update preserves coherence and, for an edge not already present,
class validity. Its finite-set bounds allow the two connector decisions to be composed.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction

inductive ConnectorChange (G : Consts) (c : Cyl) (e : Fin 36 × Fin 36) : Cyl → Prop
  | present (he : e ∈ decT G.ET) (hA : e ∉ decT c.qt) : ConnectorChange G c e (c.present e)
  | absent (he : e ∈ decT G.ET) (hA : e ∉ decT c.qt) : ConnectorChange G c e (c.absent e)
  | unchanged (h : e ∉ decT G.ET ∨ e ∈ decT c.qt) : ConnectorChange G c e c

theorem connector_change {G : Consts} {c d : Cyl} (e : Fin 36 × Fin 36) {q : ℕ}
    (h : connector G c e.1.val e.2.val q = some d) : ConnectorChange G c e d := by
  unfold connector at h
  dsimp only at h
  simp only [Bool.cond_eq_ite] at h
  split at h
  next hg =>
    have hfree : e ∈ decT G.ET ∧ e ∉ decT c.qt := by
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
      change bit G.ET (64 * e.2.val + e.1.val) = true ∧
        bit c.qt (64 * e.2.val + e.1.val) = false at hg
      simpa only [mem_decT, Bool.not_eq_true] using hg
    split at h
    · have hd : c.present e = d := Option.some.inj h
      rw [← hd]
      exact .present hfree.1 hfree.2
    · have hd : c.absent e = d := Option.some.inj h
      rw [← hd]
      exact .absent hfree.1 hfree.2
  next hg =>
    split at h
    · have hd : c = d := Option.some.inj h
      rw [← hd]
      apply ConnectorChange.unchanged
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
      change ¬(bit G.ET (64 * e.2.val + e.1.val) = true ∧
        bit c.qt (64 * e.2.val + e.1.val) = false) at hg
      simp only [mem_decT]
      rw [← Bool.not_eq_true] at hg
      tauto
    · cases h

structure ConnectorBounds (G : Consts) (c d : Cyl) (e : Fin 36 × Fin 36) : Prop where
  monoP : decT c.pt ⊆ decT d.pt
  monoA : decT c.qt ⊆ decT d.qt
  addedP : ∀ v ∈ decT d.pt, v ∈ decT c.pt ∨ v = e ∧ e ∈ decT G.ET
  addedA : ∀ v ∈ decT d.qt, v ∈ decT c.qt ∨ v = e ∧ e ∈ decT G.ET
  decided : e ∈ decT G.ET → e ∈ decT d.pt ∨ e ∈ decT d.qt

namespace ConnectorChange

variable {G : Consts} {c d : Cyl} {e : Fin 36 × Fin 36} (h : ConnectorChange G c e d)

include h

theorem coherent (hc : c.Coherent) : d.Coherent := by
  cases h with
  | present => exact hc.present e
  | absent => exact hc.absent e
  | unchanged => exact hc

theorem valid (hc : IsClassDatum (decT G.ET) (decT c.pt, decT c.qt))
    (hP : e ∉ decT c.pt) : IsClassDatum (decT G.ET) (decT d.pt, decT d.qt) := by
  cases h with
  | present he hA =>
    change IsClassDatum _ (decT (Nat.lor c.pt (Nat.shiftLeft 1 (edgeRank e))), decT c.qt)
    rw [show edgeRank e = 64 * e.2.val + e.1.val from rfl, decT_insert]
    exact (hc.children (mem_sdiff.mpr ⟨he,
      by simpa only [mem_union, not_or] using And.intro hP hA⟩)).1
  | absent he hA =>
    change IsClassDatum _ (decT c.pt, decT (Nat.lor c.qt (Nat.shiftLeft 1 (edgeRank e))))
    rw [show edgeRank e = 64 * e.2.val + e.1.val from rfl, decT_insert]
    exact (hc.children (mem_sdiff.mpr ⟨he,
      by simpa only [mem_union, not_or] using And.intro hP hA⟩)).2
  | unchanged => exact hc

theorem bounds : ConnectorBounds G c d e := by
  cases h with
  | present he hA =>
    have hp : decT (c.present e).pt = insert e (decT c.pt) := decT_insert c.pt e
    refine ⟨?_, subset_rfl, ?_, fun v hv => Or.inl hv, ?_⟩
    · rw [hp]
      exact subset_insert _ _
    · intro v hv
      rw [hp, mem_insert] at hv
      rcases hv with rfl | hv
      · exact Or.inr ⟨rfl, he⟩
      · exact Or.inl hv
    · intro _
      exact Or.inl (hp ▸ mem_insert_self e (decT c.pt))
  | absent he hA =>
    have ha : decT (c.absent e).qt = insert e (decT c.qt) := decT_insert c.qt e
    refine ⟨subset_rfl, ?_, fun v hv => Or.inl hv, ?_, ?_⟩
    · rw [ha]
      exact subset_insert _ _
    · intro v hv
      rw [ha, mem_insert] at hv
      rcases hv with rfl | hv
      · exact Or.inr ⟨rfl, he⟩
      · exact Or.inl hv
    · intro _
      exact Or.inr (ha ▸ mem_insert_self e (decT c.qt))
  | unchanged hskip =>
    refine ⟨subset_rfl, subset_rfl, fun v hv => Or.inl hv, fun v hv => Or.inl hv, ?_⟩
    intro he
    exact Or.inr (hskip.resolve_left (not_not.mpr he))

end ConnectorChange

end Sarkozy.F3Kernel
