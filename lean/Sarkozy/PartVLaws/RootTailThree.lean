module

public import Sarkozy.PartVLaws.RootSpectral
public import Sarkozy.PartV.TailCoefficients
public import Sarkozy.SpectralD.RootTailThree

/-!
# The LL root envelope and layer cap at class-three tail primes

The proved spectral bounds give the actual reflection-order statements
for the paper's field laws, with its constants 113 and 45.
-/

@[expose] public section

namespace Sarkozy.PartVLaws.FieldGraphs

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.FiveType.TwoCoord

variable {p : ℕ} [Fact p.Prime]

theorem tail_rootEnv_LL20_three (hW : Target.Weil) (hMR : Target.MovingRoot)
    (h4 : Extraction.FourCycleBound p) (hp : 2 ^ 512 ≤ p) (hp3 : p % 4 = 3)
    (hne : TailNonempty p) (hRow : RowHyp0 (lam2 (tailFieldLaws p hne)) .L) :
    RootEnv (rowD0 (lam2 (tailFieldLaws p hne)) .L hRow) 113 (tailR p) := by
  apply tail_rootEnv_of_LL20 p hne hRow 113 (tailR p)
  intro v
  simpa only [tailR_eq, one_div, SpectralC.rp] using
    SpectralD.Root.LL20_tail_three hW hMR h4 hp hp3 (hne.two .L .L) v

theorem tail_layerCap_LL22_three (hW : Target.Weil) (hMR : Target.MovingRoot)
    (h4 : Extraction.FourCycleBound p) (hp : 2 ^ 512 ≤ p) (hp3 : p % 4 = 3)
    (hne : TailNonempty p) :
    (Reserved.fieldCut FieldTy.L.Obj FieldTy.L.Obj).Below
      (-(45 * tailR p) • pushFunctional (lawL (lam1 (tailFieldLaws p hne) .L .L)) Reserved.diagF)
      (lawL (lam2 (tailFieldLaws p hne) .L .L)) := by
  apply tail_layerCap_of_LL22 p hne (45 * tailR p)
  intro v
  simpa only [tailR_eq, one_div, SpectralC.rp] using
    SpectralD.Root.LL22_tail_three hW hMR h4 hp hp3 (hne.two .L .L) v

end Sarkozy.PartVLaws.FieldGraphs
