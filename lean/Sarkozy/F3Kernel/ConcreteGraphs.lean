module

public import Sarkozy.F3Kernel.GraphExponents
public import Sarkozy.F3Kernel.GraphData

/-!
# The paper's half graphs in certificate coordinates

These are genuine oriented graphs obtained by pulling back the paper's half-edge sets
along the verified vertex permutations. Their adjacency vectors are the checker constants.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings

namespace GraphData

def pullbackGraph {U : Type*} [Fintype U] [DecidableEq U]
    (H : OrientedGraph U) (e : Fin 36 ≃ U) : OrientedGraph (Fin 36) where
  E := univ.filter (fun p => (e p.1, e p.2) ∈ H.E)
  loopless u hu := H.loopless (e u) (mem_filter.mp hu).2
  oriented u v huv hvu := H.oriented (e u) (e v) (mem_filter.mp huv).2 (mem_filter.mp hvu).2

@[simp] theorem mem_pullbackGraph {U : Type*} [Fintype U] [DecidableEq U]
    (H : OrientedGraph U) (e : Fin 36 ≃ U) (u v : Fin 36) :
    (u, v) ∈ (pullbackGraph H e).E ↔ (e u, e v) ∈ H.E := by
  simp [pullbackGraph]

noncomputable def graph20 : OrientedGraph (Fin 36) :=
  pullbackGraph SpectralD.Root.LL20.halfGraph equiv20

noncomputable def graph22 : OrientedGraph (Fin 36) :=
  pullbackGraph SpectralD.Root.LL22.halfGraph equiv22

noncomputable def sign20 (u v : Fin 36) : ℤ :=
  SpectralD.Root.LL20.sgn (equiv20 u) (equiv20 v)

noncomputable def sign22 (u v : Fin 36) : ℤ :=
  SpectralD.Root.LL22.sgn (equiv22 u) (equiv22 v)

theorem graph20_adj (u v : Fin 36) : graphAdj graph20 u v ↔
    SpectralD.Root.LL20.Adj (equiv20 u).val (equiv20 v).val := by
  simp only [graphAdj, graph20, mem_pullbackGraph, Cuts.SpecData.mem_halfGraph,
    Cuts.SpecData.Adj]

theorem graph22_adj (u v : Fin 36) : graphAdj graph22 u v ↔
    SpectralD.Root.LL22.Adj (equiv22 u).val (equiv22 v).val := by
  simp only [graphAdj, graph22, mem_pullbackGraph, Cuts.SpecData.mem_halfGraph,
    Cuts.SpecData.Adj]

theorem graph20_adjacencyCounts : AdjacencyCounts LL20 (graphAdj graph20) := by
  intro u
  rw [LL20_adjacencyCounts u]
  apply congrArg packCounts
  funext v
  simp only [neighbourCount_fin, graph20_adj]

theorem graph22_adjacencyCounts : AdjacencyCounts LL22 (graphAdj graph22) := by
  intro u
  rw [LL22_adjacencyCounts u]
  apply congrArg packCounts
  funext v
  simp only [neighbourCount_fin, graph22_adj]

end GraphData

end Sarkozy.F3Kernel
