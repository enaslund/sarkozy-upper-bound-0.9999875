module

public import Sarkozy.F3Kernel.NonstarTransport
public import Sarkozy.F3Kernel.ProductionTables

/-!
# Production certificates in the paper's original coordinates
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

namespace GraphData

theorem pullbackGraph_nonempty {U : Type*} [Fintype U] [DecidableEq U]
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (H : OrientedGraph U) (e : Fin 36 ≃ U) (h : (injLabellings F H).Nonempty) :
    (injLabellings F (pullbackGraph H e)).Nonempty := by
  obtain ⟨x, hx⟩ := h
  refine ⟨fun u => x (e u), (Cuts.inj_iso _ _ e (mem_pullbackGraph H e) _).mpr ?_⟩
  simpa only [Equiv.apply_symm_apply] using hx

theorem cross20_map : (decT LL20.ET).map (equiv20.prodCongr equiv20).toEmbedding =
    SpectralD.Root.LL20.crossPairs := by
  ext ⟨u, v⟩
  rw [mem_map_equiv]
  change (equiv20.symm u, equiv20.symm v) ∈ decT LL20.ET ↔ _
  rw [mem_cross20, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem cross22_map : (decT LL22.ET).map (equiv22.prodCongr equiv22).toEmbedding =
    SpectralD.Root.LL22.crossPairs := by
  ext ⟨u, v⟩
  rw [mem_map_equiv]
  change (equiv22.symm u, equiv22.symm v) ∈ decT LL22.ET ↔ _
  rw [mem_cross22, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end GraphData

theorem LL20_paper_nonstar_bound {cs : List CertificateChunk} {last : ℕ}
    (hc : ChunksAccepted LL20 last cs) (hm : chunksMass cs = 2 ^ 384 - 147001)
    {p : ℕ} [Fact p.Prime] (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2)
    (h4 : FourCycleBound p) (hp : productionAnchor ≤ p)
    (hne : (injLabellings (ZMod p) SpectralD.Root.LL20.G).Nonempty)
    (f h : (SpectralD.Root.LL20.cut.Half → ZMod p) → ℝ) :
    |(SpectralD.Root.LL20.halfLaw hne).expect (fun x => f x *
      (SpectralD.Root.LL20.halfLaw hne).expect (fun y =>
        (∑ S ∈ nonstars SpectralD.Root.LL20.crossPairs,
          ∏ e ∈ S, chiPair SpectralD.Root.LL20.sgn e x y) * h y))| ≤
      certificatePolynomial GraphData.graph20 productionAnchor 36 cs (Real.sqrt p)⁻¹ *
        Real.sqrt ((SpectralD.Root.LL20.halfLaw hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((SpectralD.Root.LL20.halfLaw hne).expect (fun x => h x ^ 2)) := by
  have hhalf := SpectralD.Root.LL20.half_nonempty hne
  have hcoord := GraphData.pullbackGraph_nonempty _ GraphData.equiv20 hhalf
  have hb := nonstar_bound_equiv GraphData.graph20 SpectralD.Root.LL20.halfGraph
    GraphData.equiv20 (GraphData.mem_pullbackGraph _ _) hcoord hhalf
    (decT LL20.ET) GraphData.sign20 SpectralD.Root.LL20.sgn (fun _ _ => rfl)
    (LL20_chunks_nonstar_bound (by decide) LL20_gradedTableBounds hc hm hW hp2 h4
      (by exact_mod_cast hp) hcoord) f h
  rw [GraphData.cross20_map] at hb
  exact hb

theorem LL22_paper_nonstar_bound {cs : List CertificateChunk} {last : ℕ}
    (hc : ChunksAccepted LL22 last cs) (hm : chunksMass cs = 2 ^ 360 - 73297)
    {p : ℕ} [Fact p.Prime] (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2)
    (h4 : FourCycleBound p) (hp : productionAnchor ≤ p)
    (hne : (injLabellings (ZMod p) SpectralD.Root.LL22.G).Nonempty)
    (f h : (SpectralD.Root.LL22.cut.Half → ZMod p) → ℝ) :
    |(SpectralD.Root.LL22.halfLaw hne).expect (fun x => f x *
      (SpectralD.Root.LL22.halfLaw hne).expect (fun y =>
        (∑ S ∈ nonstars SpectralD.Root.LL22.crossPairs,
          ∏ e ∈ S, chiPair SpectralD.Root.LL22.sgn e x y) * h y))| ≤
      certificatePolynomial GraphData.graph22 productionAnchor 36 cs (Real.sqrt p)⁻¹ *
        Real.sqrt ((SpectralD.Root.LL22.halfLaw hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((SpectralD.Root.LL22.halfLaw hne).expect (fun x => h x ^ 2)) := by
  have hhalf := SpectralD.Root.LL22.half_nonempty hne
  have hcoord := GraphData.pullbackGraph_nonempty _ GraphData.equiv22 hhalf
  have hb := nonstar_bound_equiv GraphData.graph22 SpectralD.Root.LL22.halfGraph
    GraphData.equiv22 (GraphData.mem_pullbackGraph _ _) hcoord hhalf
    (decT LL22.ET) GraphData.sign22 SpectralD.Root.LL22.sgn (fun _ _ => rfl)
    (LL22_chunks_nonstar_bound (by decide) LL22_gradedTableBounds hc hm hW hp2 h4
      (by exact_mod_cast hp) hcoord) f h
  rw [GraphData.cross22_map] at hb
  exact hb

end Sarkozy.F3Kernel
