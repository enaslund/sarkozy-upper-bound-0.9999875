module

public import Sarkozy.PartVLaws.ChamberSpectral
public import Sarkozy.PartVLaws.LayerSpectral
public import Sarkozy.SpectralD.RootCuts

/-!
# The existing LL20 and LL22 criteria supply the upper-reference inequalities

The root spectral data already used by the class-three and class-one criteria
have the same graphs and cuts as `chamberData .L` and `layerData .L .L`. Their
deletion orders differ, but a cut operator is independent of the deletion order.
The identifications below are definitional equalities, checked by the kernel.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Sarkozy.PartVLaws.FieldGraphs

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.FiveType.TwoCoord

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The chamber operator is the existing LL20 operator, including its normalization. -/
theorem chamber_cutOp_eq_LL20 (hne : (injLabellings F rootGraph).Nonempty) :
    Spectral.cutOp (chamberData .L (ZMod 2)) hne =
      Spectral.cutOp SpectralD.Root.LL20 hne := rfl

/-- The layer operator is the existing LL22 operator, including its normalization. -/
theorem layer_cutOp_eq_LL22 (hne : (injLabellings F rootGraph).Nonempty) :
    Spectral.cutOp (layerData .L .L) hne =
      Spectral.cutOp SpectralD.Root.LL22 hne := rfl

/-- The conclusion of either prime-class LL20 criterion gives the actual root
envelope (V1) at field type `L`. -/
theorem tail_rootEnv_of_LL20 (p : ℕ) [Fact p.Prime] (hne : TailNonempty p)
    (hRow : RowHyp0 (lam2 (tailFieldLaws p hne)) .L) (d r : ℝ)
    (h : ∀ v : EuclideanSpace ℝ (SpectralD.Root.LL20.cut.Half → ZMod p),
      -(d * r) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp SpectralD.Root.LL20 (hne.two .L .L) v⟫_ℝ) :
    RootEnv (rowD0 (lam2 (tailFieldLaws p hne)) .L hRow) d r :=
  tail_rootEnv_two .L p hne hRow d r h

/-- The conclusion of either prime-class LL22 criterion gives the actual layer
cap (V3) of field pair `LL`. -/
theorem tail_layerCap_of_LL22 (p : ℕ) [Fact p.Prime] (hne : TailNonempty p) (a : ℝ)
    (h : ∀ v : EuclideanSpace ℝ (SpectralD.Root.LL22.cut.Half → ZMod p),
      -a * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp SpectralD.Root.LL22 (hne.two .L .L) v⟫_ℝ) :
    (Reserved.fieldCut FieldTy.L.Obj FieldTy.L.Obj).Below
      (-a • pushFunctional (lawL (lam1 (tailFieldLaws p hne) .L .L)) Reserved.diagF)
      (lawL (lam2 (tailFieldLaws p hne) .L .L)) :=
  tail_layerCap p hne .L .L a h

end Sarkozy.PartVLaws.FieldGraphs
