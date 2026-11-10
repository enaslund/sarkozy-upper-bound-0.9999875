module

public import Sarkozy.F3Kernel.ChunkPartition

/-!
# The remaining global coverage check is an exact mass identity

An accepted chunk partitions a subset of the nonstars. Since its root classes are disjoint,
equality of their total mass with the explicit nonstar count proves full coverage.
The mass here uses mathematical free-edge cardinalities; its equality to the SWAR summary
is a separate numerical soundness obligation.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction Sarkozy.ExtractionK

def nonstarMass (Ex : Finset (Fin 36 × Fin 36)) : ℕ :=
  2 ^ #Ex - (1 + #Ex + ∑ j : Fin 36, (2 ^ rowDeg Ex j - 1 - rowDeg Ex j) +
    ∑ j : Fin 36, (2 ^ colDeg Ex j - 1 - colDeg Ex j))

theorem card_nonstars_eq_mass (Ex : Finset (Fin 36 × Fin 36)) :
    #(nonstars Ex) = nonstarMass Ex := by
  have h := card_nonstars_add Ex
  unfold nonstarMass
  omega

def rootMass (G : Consts) (toks : List ℕ) : ℕ :=
  ∑ c ∈ ((rootCyls G toks).map dec).toFinset, 2 ^ #(decT G.ET \ (c.1 ∪ c.2))

noncomputable def leafFamily (G : Consts) (last : ℕ) (toks : List ℕ) :
    Finset (Finset (Fin 36 × Fin 36) × Finset (Fin 36 × Fin 36)) :=
  ((trace G toks (startState last)).map dec).toFinset

theorem partition_mass_card {Ex : Finset (Fin 36 × Fin 36)}
    {𝓟 : Finset (Finset (Fin 36 × Fin 36) × Finset (Fin 36 × Fin 36))}
    {U : Finset (Finset (Fin 36 × Fin 36))} (h : IsExactPartition Ex 𝓟 U) :
    ∑ c ∈ 𝓟, 2 ^ #(Ex \ (c.1 ∪ c.2)) = #U := by
  rw [← h.2.2, card_biUnion h.2.1]
  exact sum_congr rfl fun c hc => (card_cls (h.1 c hc).1 (h.1 c hc).2.2).symm

theorem rootMass_eq_card {G : Consts} (hG : G.WellFormedT)
    {toks : List ℕ} {st st' : St} (h : run G toks st = some st') :
    rootMass G toks = #(rootFamily G toks) :=
  partition_mass_card (rootCyls_tiling hG h).isExactPartition

theorem rootFamily_eq_nonstars_of_mass {G : Consts} (hG : G.WellFormedT)
    {toks : List ℕ} {st st' : St} (h : run G toks st = some st')
    (hmass : rootMass G toks = nonstarMass (decT G.ET)) :
    rootFamily G toks = nonstars (decT G.ET) := by
  have hc : #(rootFamily G toks) = #(nonstars (decT G.ET)) := by
    rw [← rootMass_eq_card hG h, card_nonstars_eq_mass, hmass]
  exact eq_of_subset_of_card_le (rootFamily_subset_nonstars G hG toks) hc.ge

theorem chunk_nonstar_partition {G : Consts} (hG : G.WellFormedT)
    {last : ℕ} {toks : List ℕ} {summary : Summary}
    (h : chunk G last toks = some summary)
    (hmass : rootMass G toks = nonstarMass (decT G.ET)) :
    IsExactPartition (decT G.ET) (leafFamily G last toks) (nonstars (decT G.ET)) := by
  obtain ⟨st, hr, _, _⟩ := chunk_run h
  have hp := chunk_isExactPartition hG h
  rw [rootFamily_eq_nonstars_of_mass hG hr hmass] at hp
  exact hp

theorem LL20_chunk_record_family {last : ℕ} {toks : List ℕ} {summary : Summary}
    (h : chunk LL20 last toks = some summary) :
    ∀ d ∈ leafFamily LL20 last toks,
      ∃ R : LeafRecordData (Fin 36), R.Valid (decT LL20.ET) d := by
  intro d hd
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
  exact LL20_chunk_validRecords h c hc

theorem LL22_chunk_record_family {last : ℕ} {toks : List ℕ} {summary : Summary}
    (h : chunk LL22 last toks = some summary) :
    ∀ d ∈ leafFamily LL22 last toks,
      ∃ R : LeafRecordData (Fin 36), R.Valid (decT LL22.ET) d := by
  intro d hd
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
  exact LL22_chunk_validRecords h c hc

end Sarkozy.F3Kernel
