module

public import Sarkozy.F3Kernel.MaskRuns

/-!
# An accepted class tree partitions its root into classes with valid records

This combines the earlier refinement-partition proof with the semantic leaf-check proof.
The hypotheses concern only the root cylinder, accepted token run, and final empty stack.
Identification and coverage of the compressed class roots remain separate global obligations.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction Sarkozy.ExtractionK

theorem body_validRecords {G : Consts} (hG : G.WellFormedT)
    (hleaf : ∀ {c : Cyl} {rec k value free : ℕ}, c.Coherent →
      IsClassDatum (decT G.ET) (dec c) → leafCheck G c rec = some (k, value, free) →
      ∃ R : LeafRecordData (Fin 36), R.k = k ∧ R.Valid (decT G.ET) (dec c))
    {st st' : St} {root : Cyl} {toks : List ℕ}
    (hroot : st.cur = some root) (hstack : st.stack = []) (hcoh : root.Coherent)
    (hdat : IsClassDatum (decT G.ET) (dec root))
    (htoks : ∀ tok ∈ toks, Nat.land tok 3 = 1 ∨ Nat.land tok 3 = 2)
    (h : run G toks st = some st') (hend : pend st' = []) :
    IsExactPartition (decT G.ET) ((trace G toks st).map dec).toFinset
      (cls (decT G.ET) (dec root).1 (dec root).2) ∧
    ∀ d ∈ ((trace G toks st).map dec).toFinset,
      ∃ R : LeafRecordData (Fin 36), R.Valid (decT G.ET) d := by
  have hp := body_isExactPartition hG hroot hstack hdat htoks h hend
  have hc : ∀ c ∈ pend st, c.Coherent := by
    intro c hc
    have he : c = root := by simpa only [pend, hroot, hstack, Option.toList_some,
      List.append_nil, List.mem_singleton] using hc
    exact he ▸ hcoh
  have hcohs := (run_coherent hG toks st st' htoks h hc).2
  refine ⟨hp, ?_⟩
  intro d hd
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
  obtain ⟨rec, k, value, free, hcheck⟩ := run_leafChecks toks st st' h c hc
  obtain ⟨R, _, hR⟩ := hleaf (hcohs c hc) (hp.1 (dec c) hd) hcheck
  exact ⟨R, hR⟩

theorem LL20_body_validRecords {st st' : St} {root : Cyl} {toks : List ℕ}
    (hroot : st.cur = some root) (hstack : st.stack = []) (hcoh : root.Coherent)
    (hdat : IsClassDatum (decT LL20.ET) (dec root))
    (htoks : ∀ tok ∈ toks, Nat.land tok 3 = 1 ∨ Nat.land tok 3 = 2)
    (h : run LL20 toks st = some st') (hend : pend st' = []) :
    IsExactPartition (decT LL20.ET) ((trace LL20 toks st).map dec).toFinset
      (cls (decT LL20.ET) (dec root).1 (dec root).2) ∧
    ∀ d ∈ ((trace LL20 toks st).map dec).toFinset,
      ∃ R : LeafRecordData (Fin 36), R.Valid (decT LL20.ET) d :=
  body_validRecords LL20_wellFormedT leafCheck_LL20_valid_T
    hroot hstack hcoh hdat htoks h hend

theorem LL22_body_validRecords {st st' : St} {root : Cyl} {toks : List ℕ}
    (hroot : st.cur = some root) (hstack : st.stack = []) (hcoh : root.Coherent)
    (hdat : IsClassDatum (decT LL22.ET) (dec root))
    (htoks : ∀ tok ∈ toks, Nat.land tok 3 = 1 ∨ Nat.land tok 3 = 2)
    (h : run LL22 toks st = some st') (hend : pend st' = []) :
    IsExactPartition (decT LL22.ET) ((trace LL22 toks st).map dec).toFinset
      (cls (decT LL22.ET) (dec root).1 (dec root).2) ∧
    ∀ d ∈ ((trace LL22 toks st).map dec).toFinset,
      ∃ R : LeafRecordData (Fin 36), R.Valid (decT LL22.ET) d :=
  body_validRecords LL22_wellFormedT leafCheck_LL22_valid_T
    hroot hstack hcoh hdat htoks h hend

end Sarkozy.F3Kernel
