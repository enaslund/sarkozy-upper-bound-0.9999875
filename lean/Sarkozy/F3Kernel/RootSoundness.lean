module

public import Sarkozy.F3Kernel.ClassRootChecksA
public import Sarkozy.F3Kernel.ClassBodies

/-!
# From an accepted root key to valid extraction records for its leaves

Both kinds of root key belong to the paper's compressed partition. Their mask coherence
and class validity discharge the root hypotheses of the class-body soundness theorem.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction Sarkozy.ExtractionK

theorem classRoot_mem_compressedPartition {G : Consts} (hG : G.WellFormedT)
    {key : ℕ} {c : Cyl} (h : classRoot G key = some c) :
    dec c ∈ compressedPartition edgeRank (decT G.ET) := by
  obtain ⟨hv, hc⟩ := classRoot_compressed hG h
  have hself := IsCompressedDatum.self_mem_cls edgeRank hv.1 hc
  have hns := (IsCompressedDatum.of_mem_cls edgeRank hc hself).1
  apply mem_image.mpr
  refine ⟨decT c.pt, mem_nonstars.mpr ⟨hv.1, hns⟩, ?_⟩
  exact IsCompressedDatum.unique edgeRank edgeRank_injective.injOn hv.1
    (compressedDatum_spec edgeRank _ hns) hc

theorem classRoot_nonstars {G : Consts} (hG : G.WellFormedT)
    {key : ℕ} {c : Cyl} (h : classRoot G key = some c) :
    cls (decT G.ET) (dec c).1 (dec c).2 ⊆ nonstars (decT G.ET) := by
  intro S hS
  have hc := (classRoot_compressed hG h).2
  exact mem_nonstars.mpr ⟨((mem_cls.mp hS).2).trans sdiff_subset,
    (IsCompressedDatum.of_mem_cls edgeRank hc hS).1⟩

theorem LL20_checkedRoot_validRecords {st st' : St} {root : Cyl} {key : ℕ} {toks : List ℕ}
    (hkey : classRoot LL20 key = some root)
    (hroot : st.cur = some root) (hstack : st.stack = [])
    (htoks : ∀ tok ∈ toks, Nat.land tok 3 = 1 ∨ Nat.land tok 3 = 2)
    (h : run LL20 toks st = some st') (hend : pend st' = []) :
    IsExactPartition (decT LL20.ET) ((trace LL20 toks st).map dec).toFinset
      (cls (decT LL20.ET) (dec root).1 (dec root).2) ∧
    ∀ d ∈ ((trace LL20 toks st).map dec).toFinset,
      ∃ R : LeafRecordData (Fin 36), R.Valid (decT LL20.ET) d :=
  LL20_body_validRecords hroot hstack
    (classRoot_coherent LL20_wellFormedT LL20_coherent hkey)
    (classRoot_compressed LL20_wellFormedT hkey).1 htoks h hend

theorem LL22_checkedRoot_validRecords {st st' : St} {root : Cyl} {key : ℕ} {toks : List ℕ}
    (hkey : classRoot LL22 key = some root)
    (hroot : st.cur = some root) (hstack : st.stack = [])
    (htoks : ∀ tok ∈ toks, Nat.land tok 3 = 1 ∨ Nat.land tok 3 = 2)
    (h : run LL22 toks st = some st') (hend : pend st' = []) :
    IsExactPartition (decT LL22.ET) ((trace LL22 toks st).map dec).toFinset
      (cls (decT LL22.ET) (dec root).1 (dec root).2) ∧
    ∀ d ∈ ((trace LL22 toks st).map dec).toFinset,
      ∃ R : LeafRecordData (Fin 36), R.Valid (decT LL22.ET) d :=
  LL22_body_validRecords hroot hstack
    (classRoot_coherent LL22_wellFormedT LL22_coherent hkey)
    (classRoot_compressed LL22_wellFormedT hkey).1 htoks h hend

end Sarkozy.F3Kernel
