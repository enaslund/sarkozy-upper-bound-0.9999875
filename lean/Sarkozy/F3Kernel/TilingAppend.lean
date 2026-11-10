module

public import Sarkozy.F3Kernel.ChunkIntervals

/-!
# Combining disjoint certificate tilings
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction

theorem Tiling.cls_subset {Ex : Finset (Fin 36 × Fin 36)}
    {l : List (Finset (Fin 36 × Fin 36) × Finset (Fin 36 × Fin 36))}
    {U : Finset (Finset (Fin 36 × Fin 36))} (t : Tiling Ex l U)
    {d : Finset (Fin 36 × Fin 36) × Finset (Fin 36 × Fin 36)} (hd : d ∈ l) :
    cls Ex d.1 d.2 ⊆ U := fun _ hS => (t.union _).mpr ⟨d, hd, hS⟩

theorem Tiling.nil (Ex : Finset (Fin 36 × Fin 36)) : Tiling Ex [] ∅ where
  datum _ h := by cases h
  disj := .nil
  union _ := by simp

theorem Tiling.append {Ex : Finset (Fin 36 × Fin 36)}
    {l r : List (Finset (Fin 36 × Fin 36) × Finset (Fin 36 × Fin 36))}
    {U V : Finset (Finset (Fin 36 × Fin 36))}
    (t : Tiling Ex l U) (s : Tiling Ex r V) (hd : Disjoint U V) :
    Tiling Ex (l ++ r) (U ∪ V) where
  datum d hd := (List.mem_append.mp hd).elim (t.datum d) (s.datum d)
  disj := List.pairwise_append.mpr ⟨t.disj, s.disj,
    fun a ha b hb => hd.mono (t.cls_subset ha) (s.cls_subset hb)⟩
  union S := by
    rw [mem_union, t.union, s.union]
    constructor
    · rintro (⟨d, hd, hS⟩ | ⟨d, hd, hS⟩)
      · exact ⟨d, List.mem_append_left _ hd, hS⟩
      · exact ⟨d, List.mem_append_right _ hd, hS⟩
    · rintro ⟨d, hd, hS⟩
      exact (List.mem_append.mp hd).elim (fun hl => Or.inl ⟨d, hl, hS⟩)
        (fun hr => Or.inr ⟨d, hr, hS⟩)

theorem rootFamily_member_key {G : Consts} {toks : List ℕ}
    {S : Finset (Fin 36 × Fin 36)} (hS : S ∈ rootFamily G toks) :
    ∃ key ∈ rootKeys toks, ∃ c, classRoot G key = some c ∧
      S ∈ cls (decT G.ET) (dec c).1 (dec c).2 := by
  obtain ⟨d, hd, hS⟩ := mem_biUnion.mp hS
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
  obtain ⟨key, hk, hkey⟩ := List.mem_filterMap.mp hc
  exact ⟨key, hk, c, hkey, hS⟩

end Sarkozy.F3Kernel
