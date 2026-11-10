module

public import Sarkozy.SpectralD.SmallNonstar
public import Sarkozy.SpectralD.CxNonstar

/-!
# The nonstar operator for every smaller tail cut

The singleton extraction estimate applies directly to the actual cut
operator whenever its half has at most eighteen vertices and at most
ninety-six cross pairs. Both odd prime classes are included.
-/

@[expose] public section

namespace Sarkozy.SpectralD

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W]

theorem small_nsOp_bound (D : Cuts.SpecData W) (hW : WeilBound (ZMod p))
    (h4 : FourCycleBound p) (hp : 2 ^ 512 ≤ p)
    (hn : Fintype.card D.cut.Half ≤ 18) (hm : D.crossPairs.card ≤ 96)
    (hne : (injLabellings (ZMod p) D.G).Nonempty)
    (v : EuclideanSpace ℝ (D.cut.Half → ZMod p)) :
    ‖Cx.nsOp D hne v‖ ≤ 2 ^ 196 * (Real.sqrt p)⁻¹ ^ 2 * ‖v‖ := by
  have hk : Cx.nsKer (p := p) D = fun x y =>
      ∑ S ∈ nonstars D.crossPairs, ∏ e ∈ S, chiPair D.sgn e x y := by
    funext x y
    exact Cx.nsKer_eq D x y
  unfold Cx.nsOp
  rw [hk]
  apply Cx.kernelOp_norm_le_of_bilinear _ _ (by positivity) _ v
  apply small_nonstar_bound hW h4 hp D.halfGraph D.sgn _ D.sgn_antisymm
    hn (D.half_nonempty hne) D.crossPairs hm
  · intro e he
    exact (mem_filter.mp he).2
  · intro j k
    unfold Cuts.SpecData.sgn
    split_ifs <;> simp

theorem small_nsOp_tail (D : Cuts.SpecData W) (hW : WeilBound (ZMod p))
    (h4 : FourCycleBound p) (hp : 2 ^ 512 ≤ p)
    (hn : Fintype.card D.cut.Half ≤ 18) (hm : D.crossPairs.card ≤ 96)
    (hne : (injLabellings (ZMod p) D.G).Nonempty)
    (v : EuclideanSpace ℝ (D.cut.Half → ZMod p)) :
    ‖Cx.nsOp D hne v‖ ≤ 2⁻¹ ^ 50 * (Real.sqrt p)⁻¹ * ‖v‖ :=
  (small_nsOp_bound D hW h4 hp hn hm hne v).trans
    (mul_le_mul_of_nonneg_right (small_nonstar_tail_scalar hp) (norm_nonneg _))

end Sarkozy.SpectralD
