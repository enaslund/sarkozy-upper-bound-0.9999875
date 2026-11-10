module

public import Sarkozy.F3Kernel.ClassRootsA
public import Sarkozy.F3Kernel.Connectors

/-!
# The two connector decisions complete compressed case (A)

Combining their local soundness statements identifies the finished class with `datumA`.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction

theorem classA_connectors_valid {G : Consts} {e f : Fin 36 × Fin 36}
    (he : e ∈ decT G.ET) (hf : f ∈ decT G.ET) (hef : edgeRank e < edgeRank f)
    (hdis : PairDisj e f) {c₁ c₂ : Cyl}
    (h₁ : ConnectorChange G (classAStart G e f) (e.1, f.2) c₁)
    (h₂ : ConnectorChange G c₁ (f.1, e.2) c₂) :
    IsClassDatum (decT G.ET) (decT c₂.pt, decT c₂.qt) ∧
    IsCompressedDatum edgeRank (decT G.ET) (decT c₂.pt) (decT c₂.pt, decT c₂.qt) := by
  have hnot₁ : (e.1, f.2) ∉ decT (classAStart G e f).pt := by
    rw [classAStart_present]
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨fun h => hdis.2 (congrArg Prod.snd h).symm,
      fun h => by have hh := congrArg Prod.fst h; exact hdis.1 hh⟩
  have hnot₂ : (f.1, e.2) ∉ decT (classAStart G e f).pt := by
    rw [classAStart_present]
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨fun h => hdis.1 (congrArg Prod.fst h).symm,
      fun h => by have hh := congrArg Prod.snd h; exact hdis.2 hh⟩
  have hne : (f.1, e.2) ≠ (e.1, f.2) := fun h => hdis.1 (congrArg Prod.fst h).symm
  have hnot₂' : (f.1, e.2) ∉ decT c₁.pt := by
    intro hmem
    rcases h₁.bounds.addedP _ hmem with hold | hnew
    · exact hnot₂ hold
    · exact hne hnew.1
  have hv₁ := h₁.valid (classAStart_valid G e f he hf hef) hnot₁
  have hv₂ := h₂.valid hv₁ hnot₂'
  refine ⟨hv₂, compressedA_of_invariants hv₂ ?_ ?_ hef hdis ?_ ?_ ?_ ?_⟩
  · apply h₂.bounds.monoP
    apply h₁.bounds.monoP
    rw [classAStart_present]
    exact mem_insert_self _ _
  · apply h₂.bounds.monoP
    apply h₁.bounds.monoP
    rw [classAStart_present]
    exact mem_insert_of_mem (mem_singleton_self _)
  · intro q hq
    rcases h₂.bounds.addedP q hq with hq₁ | ⟨rfl, hE⟩
    · rcases h₁.bounds.addedP q hq₁ with hq₀ | ⟨rfl, hE⟩
      · exact mem_union_left _ ((classAStart_present G e f) ▸ hq₀)
      · exact mem_union_right _ (mem_filter.mpr ⟨hE, Or.inl rfl⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hE, Or.inr rfl⟩)
  · intro q hq
    apply h₂.bounds.monoA
    apply h₁.bounds.monoA
    rwa [classAStart_absent G e f hef]
  · intro q hq
    rcases h₂.bounds.addedA q hq with hq₁ | ⟨rfl, hE⟩
    · rcases h₁.bounds.addedA q hq₁ with hq₀ | ⟨rfl, hE⟩
      · exact mem_union_left _ ((classAStart_absent G e f hef) ▸ hq₀)
      · exact mem_union_right _ (mem_filter.mpr ⟨hE, Or.inl rfl⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hE, Or.inr rfl⟩)
  · intro q hq
    obtain ⟨hE, hq⟩ := mem_filter.mp hq
    rw [mem_union]
    rcases hq with rfl | rfl
    · exact (h₁.bounds.decided hE).imp (fun h => h₂.bounds.monoP h)
        (fun h => h₂.bounds.monoA h)
    · exact h₂.bounds.decided hE

theorem classA_connectors_coherent {G : Consts} (hG : G.Coherent)
    {e f : Fin 36 × Fin 36} {c₁ c₂ : Cyl}
    (h₁ : ConnectorChange G (classAStart G e f) (e.1, f.2) c₁)
    (h₂ : ConnectorChange G c₁ (f.1, e.2) c₂) : c₂.Coherent :=
  h₂.coherent (h₁.coherent (classAStart_coherent hG e f))

end Sarkozy.F3Kernel
