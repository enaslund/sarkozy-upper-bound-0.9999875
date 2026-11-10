module

public import Sarkozy.Cuts.SpecData

/-!
# Boolean geometry for finite spectral checks

Replacing graph membership by its defining Boolean edge test avoids
repeated searches through the complete edge set in kernel computations.
The equalities below relate those computations to the actual spectral data.
-/

@[expose] public section

namespace Sarkozy.SpectralD

open Finset

variable {W : Type*} [Fintype W] [DecidableEq W]

def edgeSign (E : W → W → Bool) (flip : W → W) (j k : W) : ℤ :=
  if E j (flip k) then 1 else if E (flip k) j then -1 else 0

def edgeNeighbours (E : W → W → Bool) (c : ReflectionCut W) (k : c.Half) :
    Finset c.Half := univ.filter (fun j => edgeSign E c.flip j.1 k.1 ≠ 0)

def edgeCrossPairs (E : W → W → Bool) (c : ReflectionCut W) :
    Finset (c.Half × c.Half) :=
  univ.filter (fun jk => edgeSign E c.flip jk.1.1 jk.2.1 ≠ 0)

variable (D : Cuts.SpecData W) (E : W → W → Bool)
  (hE : ∀ i j, (i, j) ∈ D.G.E ↔ E i j = true)

include hE

theorem sgn_eq_edgeSign (j k : D.cut.Half) :
    D.sgn j k = edgeSign E D.cut.flip j.1 k.1 := by
  simp only [Cuts.SpecData.sgn, edgeSign, hE]

theorem Nset_eq_edgeNeighbours : D.Nset = edgeNeighbours E D.cut := by
  funext k
  simp only [Cuts.SpecData.Nset, edgeNeighbours, sgn_eq_edgeSign D E hE]

theorem crossPairs_eq_edgeCrossPairs : D.crossPairs = edgeCrossPairs E D.cut := by
  simp only [Cuts.SpecData.crossPairs, edgeCrossPairs, sgn_eq_edgeSign D E hE]

end Sarkozy.SpectralD
