module

public import Sarkozy.SpectralD.TailParity

/-! The tail allowance applied to the actual non-coverable character averages. -/

@[expose] public section

namespace Sarkozy.SpectralD

open Finset Sarkozy.SpectralC Sarkozy.SpectralOne Sarkozy.Labellings

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W]

theorem noncoverable_tail (D : Cuts.SpecData W) (hW : WeilBound (ZMod p))
    (hp : 2 ^ 512 ≤ p) (hnW : Fintype.card W ≤ 72)
    (hn : Fintype.card D.cut.Half = 36) (ht : ∀ i, D.tdeg i ≤ 24)
    (hd : ∀ j, nbrCount D.halfGraph (univ.erase j) j ≤ 24)
    (hne : (injLabellings (ZMod p) D.G).Nonempty)
    (Adj : D.cut.Half → D.cut.Half → Prop)
    (hAdj : ∀ i j, (i, j) ∈ D.halfGraph.E ∨ (j, i) ∈ D.halfGraph.E → Adj i j)
    (J : Finset D.cut.Half) (hJ : 2 ≤ J.card) (hnc : ¬ PaleyB.Coverable Adj J) :
    ‖PaleyB.tJ (Cx.nuA D hne) J‖ ≤ 2⁻¹ ^ 80 * rp p := by
  have he1 : ∀ i, TraceMixing.coarseErr (Fintype.card (ZMod p)) (D.tdeg i) 72 < 1 := by
    intro i
    rw [ZMod.card]
    exact (coarseErr_tail hp (ht i) le_rfl).trans_lt (by norm_num)
  have he : ∀ i, TraceMixing.coarseErr p (deg0 D i) (Fintype.card D.cut.Half) < 1 := by
    intro i
    exact (coarseErr_tail hp (hd i) (by omega)).trans_lt (by norm_num)
  have h := hzeta_cut_paper D hW (by omega) hnW hne he1 le_rfl (by omega)
    he Adj hAdj J hJ hnc
  exact h.trans (mul_le_mul_of_nonneg_right (zeta_tail D hp hn ht hd) (by unfold rp; positivity))

end Sarkozy.SpectralD
