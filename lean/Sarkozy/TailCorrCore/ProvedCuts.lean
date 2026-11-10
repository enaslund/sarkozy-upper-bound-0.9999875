module

public import Sarkozy.TailCorrCore.SmallOperatorInputs
public import Sarkozy.SpectralD.SmallTail

/-!
# All eleven tail cut bounds

The two root bounds and nine smaller bounds supply every operator input
of the tail construction. Only the ten row-correlation estimates remain
in the reduction to `TailInputsCorr`.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Sarkozy.TailCorrCore

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.FiveType.TwoCoord
  Sarkozy.PartVLaws Sarkozy.PartVLaws.FieldGraphs Sarkozy.TailCorr
  Sarkozy.SpectralD.SmallMatrices

theorem tailSmallCutBounds {q : ℕ} [Fact q.Prime]
    (hW : Target.Weil) (hMR : Target.MovingRoot) (h4 : Extraction.FourCycleBound q)
    (hq : 2 ^ 512 ≤ q) (hne : TailNonempty q) : TailSmallCutBounds q hne where
  root20 f' hf v := by
    cases f' with
    | L => exact (hf rfl).elim
    | F =>
      convert tail_bound .chLF2 hW hMR h4 hq
        (FieldGraphs.nonempty .L .F twoLayers (hne.two _ _)) v using 1 <;>
        norm_num [cap, tailOrd, toFType, tailOrdinary, tailR_eq, SpectralC.rp]
      all_goals first | (left; congr!) | congr!
    | E =>
      convert tail_bound .chLE2 hW hMR h4 hq
        (FieldGraphs.nonempty .L .E twoLayers (hne.two _ _)) v using 1 <;>
        norm_num [cap, tailOrd, toFType, tailOrdinary, tailR_eq, SpectralC.rp]
      all_goals first | (left; congr!) | congr!
  root10 f' v := by
    cases f' with
    | L =>
      convert tail_bound .chLL1 hW hMR h4 hq
        (FieldGraphs.nonempty .L .L oneLayer (hne.one _ _)) v using 1 <;>
        norm_num [cap, tailRes, toFType, tailReserved, tailR_eq, SpectralC.rp]
      all_goals first | (left; congr!) | congr!
    | F =>
      convert tail_bound .chLF1 hW hMR h4 hq
        (FieldGraphs.nonempty .L .F oneLayer (hne.one _ _)) v using 1 <;>
        norm_num [cap, tailRes, toFType, tailReserved, tailR_eq, SpectralC.rp]
      all_goals first | (left; congr!) | congr!
    | E =>
      convert tail_bound .chLE1 hW hMR h4 hq
        (FieldGraphs.nonempty .L .E oneLayer (hne.one _ _)) v using 1 <;>
        norm_num [cap, tailRes, toFType, tailReserved, tailR_eq, SpectralC.rp]
      all_goals first | (left; congr!) | congr!
  caps f0 f1 hf := by
    cases f0 <;> cases f1 <;> norm_num at hf
    · intro v
      convert tail_bound .lyLF hW hMR h4 hq
        (FieldGraphs.nonempty .L .F twoLayers (hne.two _ _)) v using 1 <;>
        norm_num [cap, tailKappa, toFType, tailFieldCap, tailR_eq, SpectralC.rp]
      all_goals first | (left; congr!) | congr!
    · intro v
      convert tail_bound .lyLE hW hMR h4 hq
        (FieldGraphs.nonempty .L .E twoLayers (hne.two _ _)) v using 1 <;>
        norm_num [cap, tailKappa, toFType, tailFieldCap, tailR_eq, SpectralC.rp]
      all_goals first | (left; congr!) | congr!
    · intro v
      convert tail_bound .lyFF hW hMR h4 hq
        (FieldGraphs.nonempty .F .F twoLayers (hne.two _ _)) v using 1 <;>
        norm_num [cap, tailKappa, toFType, tailFieldCap, tailR_eq, SpectralC.rp]
      all_goals first | (left; congr!) | congr!
    · intro v
      convert tail_bound .lyFE hW hMR h4 hq
        (FieldGraphs.nonempty .F .E twoLayers (hne.two _ _)) v using 1 <;>
        norm_num [cap, tailKappa, toFType, tailFieldCap, tailR_eq, SpectralC.rp]
      all_goals first | (left; congr!) | congr!

theorem tailCutBounds {q : ℕ} [Fact q.Prime]
    (hW : Target.Weil) (hMR : Target.MovingRoot) (h4 : Extraction.FourCycleBound q)
    (hq : 2 ^ 512 ≤ q) (hne : TailNonempty q) : TailCutBounds q hne :=
  tailCutBounds_of_small hW hMR h4 hq hne (tailSmallCutBounds hW hMR h4 hq hne)

theorem tailInputsCorr_of_rowBounds (hW : Target.Weil) (hMR : Target.MovingRoot)
    (h4 : ∀ (q : ℕ) [Fact q.Prime], P4 ≤ q → Extraction.FourCycleBound q)
    (hrow : ∀ (q : ℕ) [Fact q.Prime], P4 ≤ q → ∀ (hne : TailNonempty q)
      (hw : WeilBound (ZMod q)) (hp : (2 : ℝ) ^ 20 ≤ q), TailRowBounds q hne hw hp) :
    TailInputsCorr P4 :=
  tailInputsCorr_of_operatorBounds le_rfl
    (fun q _ hq hne => tailCutBounds hW hMR (h4 q hq) hq hne) hrow

end Sarkozy.TailCorrCore
