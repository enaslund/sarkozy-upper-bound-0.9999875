module

public import Sarkozy.PositiveRoots.CoherentProductNumerics

/-! Concrete core-product residual bounds from Weil and the four-cycle input. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.L20Cap Sarkozy.SpectralC Sarkozy.SpectralC.TwoLabel Sarkozy.SpectralD
open Sarkozy.Cuts Sarkozy.Recentering
open scoped symmDiff

variable {p : ℕ} [Fact p.Prime] [Nonempty (CoreT (ZMod p))]

omit [Nonempty (CoreT (ZMod p))] in
theorem core_starMean_le_cap (hW : Labellings.WeilBound (ZMod p)) (hp40 : 2 ^ 40 ≤ p)
    {S : Finset (Fin 4)} (hS : S.Nonempty) (c : CoreT (ZMod p)) :
    |starMean S c.val| ≤ coreMeanCap p :=
  (abs_starMean_graded hW hS c.val c.property.1.injOn).trans (gradedStarPrice_core_le hp40 hS)

theorem core_reducedStarProduct_norm_9_5 (hW : Labellings.WeilBound (ZMod p))
    (hDLK : Target.FourCycle) (hp3 : p % 4 = 3) (hp40 : 2 ^ 40 ≤ p)
    (S T : Finset (Fin 4)) (hS : S.Nonempty) (hT : T.Nonempty) (hST : 2 ≤ (S ∪ T).card)
    (F : ZMod p × ZMod p → ℝ)
    (hrow : ∀ u, (fieldLaw p).expect (fun v => F (u, v)) = 0)
    (hcol : ∀ v, (fieldLaw p).expect (fun u => F (u, v)) = 0) :
    nrm coreLaw (fun c : CoreT (ZMod p) => reducedStarProduct S T F c.val) ≤
      (if S = T then 9 else 5) * nrm ((fieldLaw p).product (fieldLaw p)) F := by
  have h := core_reducedStarProduct_norm hDLK hp3 (by omega : 7 < p) S T hS hT hST
    (coreMeanCap_nonneg (p := p)) (coreMeanCap_nonneg (p := p)) (coreMeanCap_nonneg (p := p))
    (core_starMean_le_cap hW hp40 hS) (core_starMean_le_cap hW hp40 hT)
    (fun he => core_starMean_le_cap hW hp40 (symmDiff_nonempty.mpr he)) F hrow hcol
  exact h.trans (mul_le_mul_of_nonneg_right (residualProductPrice_small hp40 S T) (nrm_nonneg _ _))

end Sarkozy.PositiveRoots.CoherentFrame
