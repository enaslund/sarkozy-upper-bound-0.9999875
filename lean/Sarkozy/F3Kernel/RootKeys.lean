module

public import Sarkozy.F3Kernel.RootKeysA
public import Sarkozy.F3Kernel.RootSoundness

/-!
# Accepted root keys encode distinct compressed classes

Kind-zero roots have no edge disjoint from their first edge; kind-one roots do. Together
with recovery of each kind's fields, this proves injectivity across all accepted keys.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction

theorem root_kinds_incompatible {a b : ℕ} {P : Finset (Fin 36 × Fin 36)}
    (s : RootBKeyParts a P) (t : RootAKeyParts b P) : False := by
  have he : s.e = t.e := IsFirst.unique edgeRank edgeRank_injective.injOn
    (subset_univ P) s.first t.first
  have hf := mem_filter.mp t.next.1
  exact s.noDisjoint t.f hf.1 (he ▸ hf.2)

theorem classRoot_key_injective {G : Consts} (hG : G.WellFormedT)
    {key key' : ℕ} {c c' : Cyl}
    (h : classRoot G key = some c) (h' : classRoot G key' = some c')
    (hP : decT c.pt = decT c'.pt) : key = key' := by
  by_cases hk : Nat.land (Nat.shiftRight key 24) 1 = 0 <;>
    by_cases hk' : Nat.land (Nat.shiftRight key' 24) 1 = 0
  · exact classRoot_B_key_injective hG hk hk' h h' hP
  · obtain ⟨s⟩ := classRoot_B_key_parts hG hk h
    obtain ⟨t⟩ := classRoot_A_key_parts hG hk' h'
    rw [← hP] at t
    exact False.elim (root_kinds_incompatible s t)
  · obtain ⟨s⟩ := classRoot_B_key_parts hG hk' h'
    obtain ⟨t⟩ := classRoot_A_key_parts hG hk h
    rw [hP] at t
    exact False.elim (root_kinds_incompatible s t)
  · exact classRoot_A_key_injective hG hk hk' h h' hP

theorem classRoot_classes_disjoint {G : Consts} (hG : G.WellFormedT)
    {key key' : ℕ} {c c' : Cyl}
    (h : classRoot G key = some c) (h' : classRoot G key' = some c') (hne : key ≠ key') :
    Disjoint (cls (decT G.ET) (dec c).1 (dec c).2)
      (cls (decT G.ET) (dec c').1 (dec c').2) := by
  have hp := isExactPartition_compressedPartition edgeRank
    (Ex := decT G.ET) edgeRank_injective.injOn
  apply hp.2.1 (classRoot_mem_compressedPartition hG h)
    (classRoot_mem_compressedPartition hG h')
  intro heq
  apply hne
  exact classRoot_key_injective hG h h' (congrArg Prod.fst heq)

end Sarkozy.F3Kernel
