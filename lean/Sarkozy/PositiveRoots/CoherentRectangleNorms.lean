module

public import Sarkozy.PositiveRoots.CoherentRectangleMeans
public import Sarkozy.Cuts.FeatureComposition

/-! The star rectangle and its centered remainder have explicit operator bounds. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Sarkozy.L20Cap Sarkozy.SpectralC Sarkozy.SpectralC.TwoLabel Sarkozy.SpectralD
open Sarkozy.Cuts Sarkozy.Recentering

variable {p : ℕ} [Fact p.Prime] [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]

omit [Nonempty (CoreT (ZMod p))] in
theorem rectangleStar_action (f : PairT (ZMod p) → ℝ) :
    recOp pairLaw rectangleStar f = fun C =>
      (rp p * Real.sqrt 30) *
        recOp (fieldLaw p) (fun C : CoreT (ZMod p) => coreZKernel C.val)
          (recAdj pairLaw pairVKernel f) C +
      (2 * rp p) * recOp (fieldLaw p) coreWKernel (recAdj pairLaw pairEKernel f) C := by
  unfold rectangleStar
  rw [recOp_kernel_add, recOp_kernel_smul, recOp_kernel_smul,
    recOp_featureComposition, recOp_featureComposition]

theorem rectangleStar_norm (hW : Labellings.WeilBound (ZMod p))
    (hp3 : p % 4 = 3) (hp40 : 2 ^ 40 ≤ p) (f : PairT (ZMod p) → ℝ) :
    nrm coreLaw (recOp pairLaw rectangleStar f) ≤
      ((15 / 2 : ℝ) * rp p) * nrm pairLaw f := by
  have hr0 := rp_nonneg (p := p)
  have hf0 := nrm_nonneg pairLaw f
  have hV : nrm (fieldLaw p) (recAdj pairLaw pairVKernel f) ≤ nrm pairLaw f := by
    simpa only [one_mul] using nrm_recAdj_le pairLaw (fieldLaw p) pairVKernel
      (by norm_num : (0 : ℝ) ≤ 1) (fun g => by simpa only [one_mul] using pairV_norm g) f
  have hE : nrm (fieldLaw p) (recAdj pairLaw pairEKernel f) ≤ nrm pairLaw f := by
    simpa only [one_mul] using nrm_recAdj_le pairLaw (fieldLaw p) pairEKernel
      (by norm_num : (0 : ℝ) ≤ 1)
      (fun g => by simpa only [one_mul] using pairE_norm (by omega : p ≠ 2) g) f
  have hZ := (coreZKernel_norm_full hW hp3 hp40 (recAdj pairLaw pairVKernel f)).trans
    (mul_le_mul_of_nonneg_left hV (by norm_num : (0 : ℝ) ≤ 1001 / 1000))
  have hWn := (coreW_norm hp3 (recAdj pairLaw pairEKernel f)).trans hE
  have hs : Real.sqrt 30 ≤ (548 / 100 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    norm_num
  have hc : Real.sqrt 30 * (1001 / 1000 : ℝ) + 2 ≤ (15 / 2 : ℝ) := by
    nlinarith
  rw [rectangleStar_action]
  refine (nrm_add_le _ _ _).trans ?_
  rw [nrm_smul, nrm_smul, abs_of_nonneg (by positivity : 0 ≤ rp p * Real.sqrt 30),
    abs_of_nonneg (by positivity : 0 ≤ 2 * rp p)]
  calc
    _ ≤ (rp p * Real.sqrt 30) * ((1001 / 1000 : ℝ) * nrm pairLaw f) +
        (2 * rp p) * nrm pairLaw f := by gcongr
    _ = (Real.sqrt 30 * (1001 / 1000 : ℝ) + 2) * rp p * nrm pairLaw f := by ring
    _ ≤ _ := by gcongr

theorem rectangle_centered_norm (hW : Labellings.WeilBound (ZMod p))
    (hDLK : Target.FourCycle) (hp3 : p % 4 = 3) (hp40 : 2 ^ 40 ≤ p)
    (f : PairT (ZMod p) → ℝ) :
    nrm coreLaw (recOp pairLaw Rc f) ≤
      ((15 / 2 : ℝ) * rp p + 282 * (p : ℝ)⁻¹) * nrm pairLaw f := by
  have he : (Rc : CoreT (ZMod p) → PairT (ZMod p) → ℝ) =
      fun C b => rectangleStar C b + rectangleRemainder C b := by
    funext C b
    rw [Rc, rectangle_rank_star_remainder (by omega : p ≠ 2)]
    ring
  rw [he, recOp_kernel_add]
  exact (nrm_add_le _ _ _).trans ((add_le_add
    (rectangleStar_norm hW hp3 hp40 f) (rectangleRemainder_norm hW hDLK hp3 hp40 f)).trans_eq
      (by ring))

end Sarkozy.PositiveRoots.CoherentFrame
