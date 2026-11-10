module

public import Sarkozy.F3Kernel.FullCertificateBound
public import Sarkozy.F3Kernel.ProductionDecay
public import Sarkozy.SpectralD.CxNonstar

/-!
# The certified nonstar input for the actual spectral operators

These bounds have no certificate hypotheses. They apply to both odd prime classes.
The tail estimate is much smaller than the error allowance in the spectral criterion;
the other spectral inputs still need separate proofs.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK Sarkozy.SpectralD

variable {p : ℕ} [Fact p.Prime]

theorem LL20_nsOp_bound (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (hp : productionAnchor ≤ p)
    (hne : (injLabellings (ZMod p) Root.LL20.G).Nonempty)
    (v : EuclideanSpace ℝ (Root.LL20.cut.Half → ZMod p)) :
    ‖Cx.nsOp Root.LL20 hne v‖ ≤ productionPolynomial coefficientCap20 p * ‖v‖ := by
  have hp2 : p ≠ 2 := by unfold productionAnchor at hp; omega
  have hk : Cx.nsKer (p := p) Root.LL20 = fun x y =>
      ∑ S ∈ Sarkozy.Extraction.nonstars Root.LL20.crossPairs,
        ∏ e ∈ S, chiPair Root.LL20.sgn e x y := by
    funext x y
    exact Cx.nsKer_eq Root.LL20 x y
  unfold Cx.nsOp
  rw [hk]
  exact Cx.kernelOp_norm_le_of_bilinear _ _ (productionPolynomial_nonneg _ _)
    (LL20_full_nonstar_bound hW hp2 h4 hp hne) v

theorem LL22_nsOp_bound (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (hp : productionAnchor ≤ p)
    (hne : (injLabellings (ZMod p) Root.LL22.G).Nonempty)
    (v : EuclideanSpace ℝ (Root.LL22.cut.Half → ZMod p)) :
    ‖Cx.nsOp Root.LL22 hne v‖ ≤ productionPolynomial coefficientCap22 p * ‖v‖ := by
  have hp2 : p ≠ 2 := by unfold productionAnchor at hp; omega
  have hk : Cx.nsKer (p := p) Root.LL22 = fun x y =>
      ∑ S ∈ Sarkozy.Extraction.nonstars Root.LL22.crossPairs,
        ∏ e ∈ S, chiPair Root.LL22.sgn e x y := by
    funext x y
    exact Cx.nsKer_eq Root.LL22 x y
  unfold Cx.nsOp
  rw [hk]
  exact Cx.kernelOp_norm_le_of_bilinear _ _ (productionPolynomial_nonneg _ _)
    (LL22_full_nonstar_bound hW hp2 h4 hp hne) v

theorem LL20_nsOp_bound64 (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (hp : 2 ^ 64 ≤ p) (hne : (injLabellings (ZMod p) Root.LL20.G).Nonempty)
    (v : EuclideanSpace ℝ (Root.LL20.cut.Half → ZMod p)) :
    ‖Cx.nsOp Root.LL20 hne v‖ ≤ 19 * (Real.sqrt p)⁻¹ * ‖v‖ := by
  have h60 : productionAnchor ≤ p := by unfold productionAnchor; omega
  exact (LL20_nsOp_bound hW h4 h60 hne v).trans
    (mul_le_mul_of_nonneg_right (LL20_production_decay64 hp) (norm_nonneg _))

theorem LL22_nsOp_bound64 (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (hp : 2 ^ 64 ≤ p) (hne : (injLabellings (ZMod p) Root.LL22.G).Nonempty)
    (v : EuclideanSpace ℝ (Root.LL22.cut.Half → ZMod p)) :
    ‖Cx.nsOp Root.LL22 hne v‖ ≤ 16 * (Real.sqrt p)⁻¹ * ‖v‖ := by
  have h60 : productionAnchor ≤ p := by unfold productionAnchor; omega
  exact (LL22_nsOp_bound hW h4 h60 hne v).trans
    (mul_le_mul_of_nonneg_right (LL22_production_decay64 hp) (norm_nonneg _))

theorem LL20_nsOp_tail (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (hp : 2 ^ 512 ≤ p) (hne : (injLabellings (ZMod p) Root.LL20.G).Nonempty)
    (v : EuclideanSpace ℝ (Root.LL20.cut.Half → ZMod p)) :
    ‖Cx.nsOp Root.LL20 hne v‖ ≤ 2⁻¹ ^ 200 * (Real.sqrt p)⁻¹ * ‖v‖ := by
  have h60 : productionAnchor ≤ p := by unfold productionAnchor; omega
  exact (LL20_nsOp_bound hW h4 h60 hne v).trans
    (mul_le_mul_of_nonneg_right (LL20_production_decay512 hp) (norm_nonneg _))

theorem LL22_nsOp_tail (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (hp : 2 ^ 512 ≤ p) (hne : (injLabellings (ZMod p) Root.LL22.G).Nonempty)
    (v : EuclideanSpace ℝ (Root.LL22.cut.Half → ZMod p)) :
    ‖Cx.nsOp Root.LL22 hne v‖ ≤ 2⁻¹ ^ 200 * (Real.sqrt p)⁻¹ * ‖v‖ := by
  have h60 : productionAnchor ≤ p := by unfold productionAnchor; omega
  exact (LL22_nsOp_bound hW h4 h60 hne v).trans
    (mul_le_mul_of_nonneg_right (LL22_production_decay512 hp) (norm_nonneg _))

end Sarkozy.F3Kernel
