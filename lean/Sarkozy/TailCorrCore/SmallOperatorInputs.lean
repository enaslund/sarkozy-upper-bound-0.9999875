module

public import Sarkozy.TailCorrCore.OperatorInputs
public import Sarkozy.PartVLaws.RootTail

/-!
# The tail construction after discharging its two LL root cuts

The proved LL20 and LL22 bounds leave only five smaller chamber cuts and
four smaller layer cuts in the spectral input. The row-correlation
estimates remain separate obligations.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Sarkozy.TailCorrCore

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.FiveType.TwoCoord
  Sarkozy.PartVLaws Sarkozy.PartVLaws.FieldGraphs Sarkozy.TailCorr

structure TailSmallCutBounds (q : ℕ) [Fact q.Prime] (hne : TailNonempty q) : Prop where
  root20 : ∀ (f' : FieldTy), f' ≠ .L →
    ∀ v : EuclideanSpace ℝ ((chamberData f' (ZMod 2)).cut.Half → ZMod q),
    -((tailOrd f').d * tailR q) * ‖v‖ ^ 2 ≤
      ⟪v, Spectral.cutOp (chamberData f' (ZMod 2))
        (FieldGraphs.nonempty .L f' twoLayers (hne.two _ _)) v⟫_ℝ
  root10 : ∀ (f' : FieldTy)
    (v : EuclideanSpace ℝ ((chamberData f' Unit).cut.Half → ZMod q)),
    -((tailRes f').d * tailR q) * ‖v‖ ^ 2 ≤
      ⟪v, Spectral.cutOp (chamberData f' Unit)
        (FieldGraphs.nonempty .L f' oneLayer (hne.one _ _)) v⟫_ℝ
  caps : ∀ f0 f1 : FieldTy,
    (f0, f1) ∈ ({(.F, .F), (.L, .F), (.L, .E), (.F, .E)} : Finset (FieldTy × FieldTy)) →
    ∀ v : EuclideanSpace ℝ ((layerData f0 f1).cut.Half → ZMod q),
      -(tailKappa f0 f1 * tailR q) * ‖v‖ ^ 2 ≤
        ⟪v, Spectral.cutOp (layerData f0 f1)
          (FieldGraphs.nonempty f0 f1 twoLayers (hne.two _ _)) v⟫_ℝ

theorem tailCutBounds_of_small {q : ℕ} [Fact q.Prime]
    (hW : Target.Weil) (hMR : Target.MovingRoot) (h4 : Extraction.FourCycleBound q)
    (hq : 2 ^ 512 ≤ q) (hne : TailNonempty q) (hsmall : TailSmallCutBounds q hne) :
    TailCutBounds q hne where
  root20 f' := by
    by_cases hf : f' = .L
    · subst f'
      intro v
      change -((tailOrd .L).d * tailR q) * ‖v‖ ^ 2 ≤
        ⟪v, Spectral.cutOp SpectralD.Root.LL20 (hne.two .L .L) v⟫_ℝ
      convert SpectralD.Root.LL20_tail hW hMR h4 hq (hne.two .L .L) v using 1 <;>
        norm_num [tailOrd, toFType, tailOrdinary, tailR_eq, SpectralC.rp]
      all_goals first
      | (left; congr!)
      | congr!
    · exact hsmall.root20 f' hf
  root10 := hsmall.root10
  caps f0 f1 hf := by
    rcases Finset.mem_insert.mp hf with hLL | hrest
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hLL
      intro v
      change -(tailKappa .L .L * tailR q) * ‖v‖ ^ 2 ≤
        ⟪v, Spectral.cutOp SpectralD.Root.LL22 (hne.two .L .L) v⟫_ℝ
      convert SpectralD.Root.LL22_tail hW hMR h4 hq (hne.two .L .L) v using 1 <;>
        norm_num [tailKappa, toFType, tailFieldCap, tailR_eq, SpectralC.rp]
      all_goals first
      | (left; congr!)
      | congr!
    · exact hsmall.caps f0 f1 hrest

end Sarkozy.TailCorrCore
