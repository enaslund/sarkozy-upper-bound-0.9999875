module

public import Sarkozy.TailCorrCore.CapsSwap
public import Sarkozy.PartVLaws.RootSpectral




@[expose] public section

open scoped InnerProductSpace

namespace Sarkozy.TailCorrCore

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.FiveType.TwoCoord
  Sarkozy.PartVLaws Sarkozy.PartVLaws.FieldGraphs Sarkozy.TailCorr

/-- The eleven operator lower bounds needed by the tail construction, after the
proved coordinate symmetries. All operators are on the actual field graphs. -/
structure TailCutBounds (q : ℕ) [Fact q.Prime] (hne : TailNonempty q) : Prop where
  root20 : ∀ (f' : FieldTy)
    (v : EuclideanSpace ℝ ((chamberData f' (ZMod 2)).cut.Half → ZMod q)),
    -((tailOrd f').d * tailR q) * ‖v‖ ^ 2 ≤
      ⟪v, Spectral.cutOp (chamberData f' (ZMod 2))
        (FieldGraphs.nonempty .L f' twoLayers (hne.two _ _)) v⟫_ℝ
  root10 : ∀ (f' : FieldTy)
    (v : EuclideanSpace ℝ ((chamberData f' Unit).cut.Half → ZMod q)),
    -((tailRes f').d * tailR q) * ‖v‖ ^ 2 ≤
      ⟪v, Spectral.cutOp (chamberData f' Unit)
        (FieldGraphs.nonempty .L f' oneLayer (hne.one _ _)) v⟫_ℝ
  caps : ∀ f0 f1 : FieldTy, (f0, f1) ∈ ({(.L, .L), (.F, .F), (.L, .F), (.L, .E), (.F, .E)} :
      Finset (FieldTy × FieldTy)) →
    ∀ v : EuclideanSpace ℝ ((layerData f0 f1).cut.Half → ZMod q),
      -(tailKappa f0 f1 * tailR q) * ‖v‖ ^ 2 ≤
        ⟪v, Spectral.cutOp (layerData f0 f1)
          (FieldGraphs.nonempty f0 f1 twoLayers (hne.two _ _)) v⟫_ℝ

/-- The remaining ten row-correlation estimates. The matching rows at `E` have
already been proved and are supplied by `tailSpectral_of_core`. -/
structure TailRowBounds (q : ℕ) [Fact q.Prime] (hne : TailNonempty q)
    (hW : WeilBound (ZMod q)) (hp : (2 : ℝ) ^ 20 ≤ q) : Prop where
  fold20 : ∀ f', FoldCorr (rowD0 (lam2 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).two0 f')) (tailCF (tailOrd f') * tailR q)
  fold10 : ∀ f', FoldCorr (rowD0 (lam1 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).one0 f')) (tailCF (tailRes f') * tailR q)
  match20 : ∀ f', f' ≠ .E → MatchNorm (rowD0 (lam2 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).two0 f')) ((tailOrd f').h * tailR q)
  match10 : ∀ f', f' ≠ .E → MatchNorm (rowD0 (lam1 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).one0 f')) ((tailRes f').h * tailR q)

/-- **The tail's reflection inequalities follow from its graph operators.**
The half-law identifications, law reindexings and row grouping are all proved. -/
theorem tailSpectralCore1_of_operatorBounds (q : ℕ) [Fact q.Prime] (hne : TailNonempty q)
    (hW : WeilBound (ZMod q)) (hp : (2 : ℝ) ^ 20 ≤ q)
    (hcut : TailCutBounds q hne) (hrow : TailRowBounds q hne hW hp) :
    TailSpectralCore1 q hne hW hp where
  root20 f' := tail_rootEnv_two f' q hne
    ((tail_upperDatumHyp q hW hp hne).two0 f') _ _ (hcut.root20 f')
  root10 f' := tail_rootEnv_one f' q hne
    ((tail_upperDatumHyp q hW hp hne).one0 f') _ _ (hcut.root10 f')
  fold20 := hrow.fold20
  fold10 := hrow.fold10
  match20 := hrow.match20
  match10 := hrow.match10
  caps f0 f1 hf := tail_layerCap q hne f0 f1 _ (hcut.caps f0 f1 hf)

/-- A plug-in for the main theorem's `hC`, now phrased in graph spectral bounds
and the outstanding row estimates. No reflection-order identification is assumed. -/
theorem tailInputsCorr_of_operatorBounds {P : ℕ} (hP : P4 ≤ P)
    (hcut : ∀ (q : ℕ) [Fact q.Prime], P ≤ q → ∀ hne, TailCutBounds q hne)
    (hrow : ∀ (q : ℕ) [Fact q.Prime], P ≤ q → ∀ (hne : TailNonempty q)
      (hW : WeilBound (ZMod q)) (hp : (2 : ℝ) ^ 20 ≤ q), TailRowBounds q hne hW hp) :
    TailInputsCorr P :=
  tailInputsCorr_of_core1 hP fun q _ hq hne hW hp =>
    tailSpectralCore1_of_operatorBounds q hne hW hp (hcut q hq hne) (hrow q hq hne hW hp)

/-- Validity of the tail inputs from the eleven graph-cut bounds and ten row
estimates. This uses the existing count and Schur estimates without changing them. -/
theorem tailInputsValid_of_operatorBounds
    (hcut : ∀ (q : ℕ) [Fact q.Prime], P4 ≤ q → ∀ hne, TailCutBounds q hne)
    (hrow : ∀ (q : ℕ) [Fact q.Prime], P4 ≤ q → ∀ (hne : TailNonempty q)
      (hW : WeilBound (ZMod q)) (hp : (2 : ℝ) ^ 20 ≤ q), TailRowBounds q hne hW hp) :
    TailInputsValid P4 :=
  tailInputsValid_of_corr le_rfl (tailInputsCorr_of_operatorBounds le_rfl hcut hrow)

end Sarkozy.TailCorrCore
