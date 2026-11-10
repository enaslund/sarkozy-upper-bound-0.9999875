module

public import Sarkozy.PositiveRoots.CoherentCoreLaw
public import Sarkozy.PositiveRoots.CoherentRawStarReal

/-! Every nonempty raw core star has norm at most r on mean-zero auxiliary inputs. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Sarkozy.L20Cap Sarkozy.SpectralC.TwoLabel Sarkozy.SpectralC Sarkozy.Cuts Sarkozy.Recentering
open Sarkozy.SpectralD

variable {p : ℕ} [Fact p.Prime] [Nonempty (CoreT (ZMod p))]

theorem core_rawStar_mean_zero_sq (hp3 : p % 4 = 3)
    (S : Finset (Fin 4)) (hS : S.Nonempty) (F : ZMod p → ℝ) (hF : (fieldLaw p).expect F = 0) :
    coreLaw.expect (fun c : CoreT (ZMod p) => rawStarMap S F c.val ^ 2) ≤
      (p : ℝ)⁻¹ * (fieldLaw p).expect (fun z => F z ^ 2) := by
  rw [← coreAmbient_expect (fun x => rawStarMap S F x ^ 2)]
  exact rawStarMap_mean_zero_sq hp3 coreAmbientLaw coreAmbient_affine coreAmbient_injective S hS F hF

theorem core_rawStar_mean_zero_norm (hp3 : p % 4 = 3)
    (S : Finset (Fin 4)) (hS : S.Nonempty) (F : ZMod p → ℝ) (hF : (fieldLaw p).expect F = 0) :
    nrm coreLaw (fun c : CoreT (ZMod p) => rawStarMap S F c.val) ≤
      rp p * nrm (fieldLaw p) F := by
  have h : nrm coreLaw (fun c : CoreT (ZMod p) => rawStarMap S F c.val) ^ 2 ≤
      (rp p * nrm (fieldLaw p) F) ^ 2 := by
    rw [nrm_sq_expect, mul_pow, rp_sq, nrm_sq_expect]
    exact core_rawStar_mean_zero_sq hp3 S hS F hF
  exact (abs_le_of_sq_le_sq' h (mul_nonneg rp_nonneg (nrm_nonneg _ _))).2

theorem core_coordinate_norm (hp3 : p % 4 = 3) (i : Fin 4) (F : ZMod p → ℝ) :
    nrm coreLaw (fun c : CoreT (ZMod p) => F (c.val i)) = nrm (fieldLaw p) F := by
  apply (sq_eq_sq₀ (nrm_nonneg _ _) (nrm_nonneg _ _)).mp
  rw [nrm_sq_expect, nrm_sq_expect, core_coordinate_square hp3]

end Sarkozy.PositiveRoots.CoherentFrame
