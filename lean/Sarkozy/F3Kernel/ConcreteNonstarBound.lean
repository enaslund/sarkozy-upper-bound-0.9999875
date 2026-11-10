module

public import Sarkozy.F3Kernel.NonstarBound

/-!
# LL20 and LL22 certificate bounds
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

namespace GraphData

theorem sign20_values (u v : Fin 36) : sign20 u v = 0 ∨ sign20 u v = 1 ∨ sign20 u v = -1 := by
  unfold sign20 Cuts.SpecData.sgn
  split_ifs <;> simp

theorem sign22_values (u v : Fin 36) : sign22 u v = 0 ∨ sign22 u v = 1 ∨ sign22 u v = -1 := by
  unfold sign22 Cuts.SpecData.sgn
  split_ifs <;> simp

theorem sign20_antisymm (u v : Fin 36) : sign20 v u = -sign20 u v :=
  SpectralD.Root.LL20.sgn_antisymm _ _

theorem sign22_antisymm (u v : Fin 36) : sign22 v u = -sign22 u v :=
  SpectralD.Root.LL22.sgn_antisymm _ _

theorem sign20_cross {e : Fin 36 × Fin 36} (he : e ∈ decT LL20.ET) : sign20 e.1 e.2 ≠ 0 :=
  (mem_filter.mp ((mem_cross20 _ _).mp he)).2

theorem sign22_cross {e : Fin 36 × Fin 36} (he : e ∈ decT LL22.ET) : sign22 e.1 e.2 ≠ 0 :=
  (mem_filter.mp ((mem_cross22 _ _).mp he)).2

end GraphData

theorem LL20_chunks_nonstar_bound {q : ℝ} {n : ℕ} (hn : 36 ≤ n)
    (hb : GradedTableBounds LL20 GraphData.graph20 GraphData.sign20 q n)
    {cs : List CertificateChunk} {last : ℕ} (hc : ChunksAccepted LL20 last cs)
    (hm : chunksMass cs = 2 ^ 384 - 147001)
    {p : ℕ} [Fact p.Prime] (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2)
    (h4 : FourCycleBound p) (hqp : q ≤ p)
    (hne : (injLabellings (ZMod p) GraphData.graph20).Nonempty)
    (f h : (Fin 36 → ZMod p) → ℝ) :
    |(graphLaw GraphData.graph20 hne).expect (fun x => f x *
      (graphLaw GraphData.graph20 hne).expect (fun x' =>
        (∑ S ∈ nonstars (decT LL20.ET), ∏ e ∈ S, chiPair GraphData.sign20 e x x') * h x'))| ≤
      certificatePolynomial GraphData.graph20 q n cs (Real.sqrt p)⁻¹ *
        Real.sqrt ((graphLaw GraphData.graph20 hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw GraphData.graph20 hne).expect (fun x => h x ^ 2)) :=
  chunks_nonstar_bound LL20_matrixWordM LL20_wellFormedT LL20_coherent
    LL20_validComponentTables GraphData.graph20 GraphData.graph20_adjacencyCounts
    GraphData.sign20 GraphData.sign20_values GraphData.sign20_antisymm
    (fun _ he => GraphData.sign20_cross he) hn hb LL20_sqrtTwo hc
    (hm.trans LL20_nonstarMass.symm) hW hp2 h4 hqp hne f h

theorem LL22_chunks_nonstar_bound {q : ℝ} {n : ℕ} (hn : 36 ≤ n)
    (hb : GradedTableBounds LL22 GraphData.graph22 GraphData.sign22 q n)
    {cs : List CertificateChunk} {last : ℕ} (hc : ChunksAccepted LL22 last cs)
    (hm : chunksMass cs = 2 ^ 360 - 73297)
    {p : ℕ} [Fact p.Prime] (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2)
    (h4 : FourCycleBound p) (hqp : q ≤ p)
    (hne : (injLabellings (ZMod p) GraphData.graph22).Nonempty)
    (f h : (Fin 36 → ZMod p) → ℝ) :
    |(graphLaw GraphData.graph22 hne).expect (fun x => f x *
      (graphLaw GraphData.graph22 hne).expect (fun x' =>
        (∑ S ∈ nonstars (decT LL22.ET), ∏ e ∈ S, chiPair GraphData.sign22 e x x') * h x'))| ≤
      certificatePolynomial GraphData.graph22 q n cs (Real.sqrt p)⁻¹ *
        Real.sqrt ((graphLaw GraphData.graph22 hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw GraphData.graph22 hne).expect (fun x => h x ^ 2)) :=
  chunks_nonstar_bound LL22_matrixWordM LL22_wellFormedT LL22_coherent
    LL22_validComponentTables GraphData.graph22 GraphData.graph22_adjacencyCounts
    GraphData.sign22 GraphData.sign22_values GraphData.sign22_antisymm
    (fun _ he => GraphData.sign22_cross he) hn hb LL22_sqrtTwo hc
    (hm.trans LL22_nonstarMass.symm) hW hp2 h4 hqp hne f h

end Sarkozy.F3Kernel
