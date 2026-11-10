module

public import Sarkozy.F3Kernel.MassSteps
public import Sarkozy.F3Kernel.ChunkCoverage

/-!
# The reported chunk mass is the mathematical root mass

Strict root ordering excludes duplicate classes. The integer accumulator therefore equals
the sum of the cardinalities of the disjoint mathematical root classes.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction

theorem run_cmass {G : Consts} (hM : MatrixWord G.EM) (hT : G.WellFormedT)
    (hG : G.Coherent) :
    ∀ (toks : List ℕ) (st st' : St), run G toks st = some st' →
      st'.cmass = st.cmass + ((rootCyls G toks).map (fun c => 2 ^ #(freePairs G c))).sum
  | [], st, st', h => by
      rw [run_nil, Option.some.injEq] at h
      subst st'
      simp [rootCyls, rootKeys]
  | tok :: ts, st, st', h => by
      rw [run_cons] at h
      cases hs : step G st tok with
      | none => rw [hs] at h; cases h
      | some mid =>
        rw [hs, Option.bind_some] at h
        have ih := run_cmass hM hT hG ts mid st' h
        by_cases ht : Nat.land tok 3 = 0
        · obtain ⟨c, hc, hm⟩ := step_root_cmass hM hT hG ht hs
          rw [ih, hm]
          simp only [rootCyls, rootKeys, ht, ite_true, List.filterMap_cons, hc,
            List.map_cons, List.sum_cons, Nat.add_assoc]
        · rw [step_nonroot_cmass hT ht hs] at ih
          simpa only [rootCyls, rootKeys, ht, ite_false] using ih

theorem Tiling.nodup {Ex : Finset (Fin 36 × Fin 36)}
    {l : List (Finset (Fin 36 × Fin 36) × Finset (Fin 36 × Fin 36))}
    {U : Finset (Finset (Fin 36 × Fin 36))} (t : Tiling Ex l U) : l.Nodup := by
  apply t.disj.imp_of_mem
  intro a b ha _ hd he
  subst b
  have hc := t.datum a ha
  have hm : a.1 ∈ cls Ex a.1 a.2 := mem_cls.mpr ⟨Subset.rfl,
    subset_sdiff.mpr ⟨hc.1, hc.2.2⟩⟩
  exact disjoint_left.mp hd hm hm

theorem rootMass_eq_list {G : Consts} (hT : G.WellFormedT) (hG : G.Coherent)
    {toks : List ℕ} {st st' : St} (h : run G toks st = some st') :
    rootMass G toks = ((rootCyls G toks).map (fun c => 2 ^ #(freePairs G c))).sum := by
  unfold rootMass
  rw [List.sum_toFinset _ (rootCyls_tiling hT h).nodup, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro c hc
  obtain ⟨key, _, hkey⟩ := List.mem_filterMap.mp hc
  have hcoh := classRoot_coherent hT hG hkey
  exact congrArg (fun s : Finset (Fin 36 × Fin 36) => 2 ^ #s) (freePairs_eq_T hG hcoh).symm

theorem chunk_summary_mass {G : Consts} {last : ℕ} {toks : List ℕ} {summary : Summary}
    (h : chunk G last toks = some summary) {st : St}
    (hr : run G toks (startState last) = some st) : summary.mass = st.cmass := by
  unfold chunk at h
  dsimp only [startState] at hr
  rw [hr] at h
  simp only [Bool.cond_eq_ite] at h
  split at h
  · split at h
    · cases h
      rfl
    · cases h
  · cases h

theorem chunk_mass_eq_rootMass {G : Consts} (hM : MatrixWord G.EM) (hT : G.WellFormedT)
    (hG : G.Coherent) {last : ℕ} {toks : List ℕ} {summary : Summary}
    (h : chunk G last toks = some summary) : summary.mass = rootMass G toks := by
  obtain ⟨st, hr, _, _⟩ := chunk_run h
  rw [chunk_summary_mass h hr, rootMass_eq_list hT hG hr, run_cmass hM hT hG toks _ _ hr]
  simp only [startState, Nat.zero_add]

theorem chunk_nonstar_partition_of_summary {G : Consts} (hM : MatrixWord G.EM)
    (hT : G.WellFormedT) (hG : G.Coherent) {last : ℕ} {toks : List ℕ} {summary : Summary}
    (h : chunk G last toks = some summary) (hm : summary.mass = nonstarMass (decT G.ET)) :
    IsExactPartition (decT G.ET) (leafFamily G last toks) (nonstars (decT G.ET)) :=
  chunk_nonstar_partition hT h ((chunk_mass_eq_rootMass hM hT hG h).symm.trans hm)

end Sarkozy.F3Kernel
