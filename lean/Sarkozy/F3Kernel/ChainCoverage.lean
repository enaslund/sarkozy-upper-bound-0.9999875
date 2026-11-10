module

public import Sarkozy.F3Kernel.ChunkChain
public import Sarkozy.F3Kernel.NonstarCounts

/-!
# Full nonstar coverage from checked chunk summaries

A sequence of accepted chunks with the correct total mass partitions every nonstar edge
set exactly once. The certificate may be split into arbitrarily many separately checked files.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction

theorem chunks_tiling {G : Consts} (hG : G.WellFormedT) {cs : List CertificateChunk}
    {last : ℕ} (h : ChunksAccepted G last cs) :
    Tiling (decT G.ET) ((chunksLeaves G last cs).map dec) (chunksFamily G cs) := by
  induction cs generalizing last with
  | nil => exact Tiling.nil _
  | cons c cs ih =>
      have ht := (chunk_tiling hG h.1).append (ih h.2) (chunksFamily_head_disjoint hG h)
      simpa only [chunksLeaves, chunksFamily, List.map_append] using ht

theorem chunks_mass_card {G : Consts} (hM : MatrixWord G.EM) (hT : G.WellFormedT)
    (hG : G.Coherent) {cs : List CertificateChunk} {last : ℕ} (h : ChunksAccepted G last cs) :
    chunksMass cs = #(chunksFamily G cs) := by
  induction cs generalizing last with
  | nil => rfl
  | cons c cs ih =>
      obtain ⟨st, hr, _, _⟩ := chunk_run h.1
      change c.summary.mass + chunksMass cs = #(rootFamily G c.tokens ∪ chunksFamily G cs)
      rw [card_union_of_disjoint (chunksFamily_head_disjoint hT h), ih h.2,
        chunk_mass_eq_rootMass hM hT hG h.1, rootMass_eq_card hT hr]

theorem chunks_partition_of_mass {G : Consts} (hM : MatrixWord G.EM) (hT : G.WellFormedT)
    (hG : G.Coherent) {cs : List CertificateChunk} {last : ℕ} (h : ChunksAccepted G last cs)
    (hm : chunksMass cs = nonstarMass (decT G.ET)) :
    IsExactPartition (decT G.ET) ((chunksLeaves G last cs).map dec).toFinset
      (nonstars (decT G.ET)) := by
  have hcard : #(chunksFamily G cs) = #(nonstars (decT G.ET)) := by
    rw [← chunks_mass_card hM hT hG h, card_nonstars_eq_mass, hm]
  have he := eq_of_subset_of_card_le (chunksFamily_subset_nonstars G hT cs) hcard.ge
  exact he ▸ (chunks_tiling hT h).isExactPartition

theorem LL20_chunks_full_partition {cs : List CertificateChunk} {last : ℕ}
    (h : ChunksAccepted LL20 last cs) (hm : chunksMass cs = 2 ^ 384 - 147001) :
    IsExactPartition (decT LL20.ET) ((chunksLeaves LL20 last cs).map dec).toFinset
      (nonstars (decT LL20.ET)) :=
  chunks_partition_of_mass LL20_matrixWordM LL20_wellFormedT LL20_coherent h
    (hm.trans LL20_nonstarMass.symm)

theorem LL22_chunks_full_partition {cs : List CertificateChunk} {last : ℕ}
    (h : ChunksAccepted LL22 last cs) (hm : chunksMass cs = 2 ^ 360 - 73297) :
    IsExactPartition (decT LL22.ET) ((chunksLeaves LL22 last cs).map dec).toFinset
      (nonstars (decT LL22.ET)) :=
  chunks_partition_of_mass LL22_matrixWordM LL22_wellFormedT LL22_coherent h
    (hm.trans LL22_nonstarMass.symm)

end Sarkozy.F3Kernel
