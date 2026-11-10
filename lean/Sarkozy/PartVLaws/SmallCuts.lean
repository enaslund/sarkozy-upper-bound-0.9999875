module

public import Sarkozy.PartVLaws.ChamberSpectral
public import Sarkozy.PartVLaws.LayerSpectral
public import Sarkozy.SpectralD.FiniteGeometry
public import Sarkozy.SecondOrder.GraphPinned

/-!
# Geometry of the nine smaller tail cuts

These are the five chamber cuts and four layer cuts other than LL20 and
LL22. All sizes and degree bounds are checked on their actual Boolean
edge relations by Lean's kernel.
-/

@[expose] public section

namespace Sarkozy.PartVLaws.FieldGraphs

open Finset Sarkozy.Labellings Sarkozy.SpectralD Sarkozy.SecondOrder

inductive SmallCut
  | chLL1 | chLF1 | chLF2 | chLE1 | chLE2 | lyLF | lyLE | lyFF | lyFE
  deriving DecidableEq

namespace SmallCut

def Vertex : SmallCut → Type
  | .chLL1 => ZMod 6 × ZMod 6 × Unit
  | .chLF1 | .chLE1 => ZMod 6 × Fin 3 × Unit
  | .chLF2 | .chLE2 | .lyLF | .lyLE => ZMod 6 × Fin 3 × ZMod 2
  | .lyFF | .lyFE => Fin 3 × Fin 3 × ZMod 2

instance (c : SmallCut) : Fintype c.Vertex := by cases c <;> unfold Vertex <;> infer_instance
instance (c : SmallCut) : DecidableEq c.Vertex := by
  cases c <;> unfold Vertex <;> infer_instance

noncomputable def data : (c : SmallCut) → Cuts.SpecData c.Vertex
  | .chLL1 => chamberData .L Unit
  | .chLF1 => chamberData .F Unit
  | .chLF2 => chamberData .F (ZMod 2)
  | .chLE1 => chamberData .E Unit
  | .chLE2 => chamberData .E (ZMod 2)
  | .lyLF => layerData .L .F
  | .lyLE => layerData .L .E
  | .lyFF => layerData .F .F
  | .lyFE => layerData .F .E

def edge : (c : SmallCut) → c.Vertex → c.Vertex → Bool
  | .chLL1 => twoLayerEdge typeL typeL
  | .chLF1 | .chLF2 | .lyLF => twoLayerEdge typeL typeF
  | .chLE1 | .chLE2 | .lyLE => twoLayerEdge typeL typeE
  | .lyFF => twoLayerEdge typeF typeF
  | .lyFE => twoLayerEdge typeF typeE

theorem mem_edge (c : SmallCut) (i j : c.Vertex) :
    (i, j) ∈ c.data.G.E ↔ c.edge i j = true := by
  cases c
  · exact mem_chamberGraph .L Unit i j
  · exact mem_chamberGraph .F Unit i j
  · exact mem_chamberGraph .F (ZMod 2) i j
  · exact mem_chamberGraph .E Unit i j
  · exact mem_chamberGraph .E (ZMod 2) i j
  · exact mem_graph .L .F i j
  · exact mem_graph .L .E i j
  · exact mem_graph .F .F i j
  · exact mem_graph .F .E i j

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem card_vertex (c : SmallCut) : Fintype.card c.Vertex ≤ 36 := by
  cases c <;> decide +kernel

theorem card_half (c : SmallCut) : Fintype.card c.data.cut.Half ≤ 18 := by
  cases c <;> decide +kernel

theorem cross_pairs (c : SmallCut) : c.data.crossPairs.card ≤ 96 := by
  rw [crossPairs_eq_edgeCrossPairs c.data c.edge (mem_edge c)]
  cases c <;> decide +kernel

theorem cross_degree (c : SmallCut) (k : c.data.cut.Half) : (c.data.Nset k).card ≤ 8 := by
  rw [Nset_eq_edgeNeighbours c.data c.edge (mem_edge c)]
  revert k
  cases c <;> decide +kernel

theorem degree (c : SmallCut) (v : c.Vertex) :
    (univ.filter (fun w => (v, w) ∈ c.data.G.E ∨ (w, v) ∈ c.data.G.E)).card ≤ 20 := by
  simp only [mem_edge]
  revert v
  cases c <;> decide +kernel

theorem half_degree (c : SmallCut) (v : c.data.cut.Half) :
    nbrCount c.data.halfGraph (univ.erase v) v ≤ 6 := by
  have h : ∀ v : c.data.cut.Half,
      (univ.filter (fun w : c.data.cut.Half =>
        c.edge v.1 w.1 = true ∨ c.edge w.1 v.1 = true)).card ≤ 6 := by
    cases c <;> decide +kernel
  rw [nbrCount_erase_self]
  simpa only [graphNbrs, Cuts.SpecData.mem_halfGraph, mem_edge, or_comm] using h v

end SmallCut

end Sarkozy.PartVLaws.FieldGraphs
