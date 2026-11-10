module

public import Sarkozy.PositiveRoots.CoherentPairMeans
public import Sarkozy.PositiveRoots.CoherentElementaryNorms

/-! Exact rank, star and nonstar decomposition of the physical accepting rectangle. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.L20Cap Sarkozy.SpectralC Sarkozy.SpectralC.TwoLabel Sarkozy.SpectralD
open Sarkozy.Cuts Sarkozy.Recentering
open Sarkozy.JointRows.StarOps (expect_finset_sum)

variable {p : ℕ} [Fact p.Prime]

noncomputable def rectangleStar (C : CoreT (ZMod p)) (b : PairT (ZMod p)) : ℝ :=
  (rp p * Real.sqrt 30) * (fieldLaw p).expect (fun z => coreZKernel C.val z * pairVKernel b z) +
    (2 * rp p) * (fieldLaw p).expect (fun z => coreWKernel C z * pairEKernel b z)

theorem rectangle_ZV_exact (C : CoreT (ZMod p)) (b : PairT (ZMod p)) :
    (rp p * Real.sqrt 30) * (fieldLaw p).expect (fun z => coreZKernel C.val z * pairVKernel b z) =
      Kz b.val.1 C.val + Kz b.val.2 C.val - 2 * Kbar C.val := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hr : rp p ≠ 0 := by unfold rp; positivity
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have h15 : Real.sqrt 15 ≠ 0 := by positivity
  have hs : Real.sqrt 30 = Real.sqrt 15 * Real.sqrt 2 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 15)]
    norm_num
  have he : (fieldLaw p).expect (fun z => coreZKernel C.val z * pairVKernel b z) =
      recOp (fieldLaw p) pairVKernel (coreZKernel C.val) b := by
    unfold recOp
    exact (fieldLaw p).expect_congr fun z => mul_comm _ _
  rw [he, pairV_action, coreZKernel_mean_zero, mul_zero, sub_zero, hs]
  unfold coreZKernel
  field_simp
  ring

theorem rectangle_WE_exact (hp2 : p ≠ 2) (C : CoreT (ZMod p)) (b : PairT (ZMod p)) :
    (2 * rp p) * (fieldLaw p).expect (fun z => coreWKernel C z * pairEKernel b z) =
      (∑ i : Fin 4, chi (b.val.1 - C.val i) * chi (b.val.2 - C.val i)) + 4 * (p : ℝ)⁻¹ := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hr : rp p ≠ 0 := by unfold rp; positivity
  change (2 * rp p) * recOp (fieldLaw p) coreWKernel (pairEKernel b) C = _
  rw [coreW_action, pairE_mean_zero hp2, mul_zero, sub_zero]
  simp only [pairEKernel, Fin.sum_univ_four]
  field_simp
  ring

theorem rectangleStar_exact (hp2 : p ≠ 2) (C : CoreT (ZMod p)) (b : PairT (ZMod p)) :
    rectangleStar C b = Kz b.val.1 C.val + Kz b.val.2 C.val - 2 * Kbar C.val +
      (∑ i : Fin 4, chi (b.val.1 - C.val i) * chi (b.val.2 - C.val i)) + 4 * (p : ℝ)⁻¹ := by
  rw [rectangleStar, rectangle_ZV_exact, rectangle_WE_exact hp2]
  ring

variable [Nonempty (PairT (ZMod p))]

noncomputable def rectangleRemainder (C : CoreT (ZMod p)) (b : PairT (ZMod p)) : ℝ :=
  Nrect C b - pairLaw.expect (Nrect C)

theorem rectangleStar_row_mean (hp2 : p ≠ 2) (C : CoreT (ZMod p)) :
    pairLaw.expect (rectangleStar C) = 0 := by
  unfold rectangleStar
  simp only [FiniteLaw.expect_add, FiniteLaw.expect_const_mul]
  rw [Cuts.expect_comm pairLaw (fieldLaw p), Cuts.expect_comm pairLaw (fieldLaw p)]
  simp only [FiniteLaw.expect_const_mul, pairV_column_mean, pairE_column_mean hp2,
    mul_zero, FiniteLaw.expect_const, add_zero]

omit [Nonempty (PairT (ZMod p))] in
theorem rectangle_before_centering (hp2 : p ≠ 2) (C : CoreT (ZMod p)) (b : PairT (ZMod p)) :
    Rk C b = rectangleStar C b + Nrect C b + (2 * Kbar C.val - 1 - 4 * (p : ℝ)⁻¹) := by
  rw [rectangleStar_exact hp2]
  unfold Rk Nrect
  ring

theorem rectangle_nonstar_row_mean (hp2 : p ≠ 2) (C : CoreT (ZMod p)) :
    pairLaw.expect (Nrect C) = rmass C - (2 * Kbar C.val - 1 - 4 * (p : ℝ)⁻¹) := by
  have he : rmass C = pairLaw.expect (rectangleStar C) + pairLaw.expect (Nrect C) +
      (2 * Kbar C.val - 1 - 4 * (p : ℝ)⁻¹) := by
    unfold rmass
    simp_rw [rectangle_before_centering hp2 C]
    rw [FiniteLaw.expect_add, FiniteLaw.expect_add, FiniteLaw.expect_const]
  rw [rectangleStar_row_mean hp2, zero_add] at he
  linarith

theorem rectangle_rank_star_remainder (hp2 : p ≠ 2) (C : CoreT (ZMod p))
    (b : PairT (ZMod p)) : Rk C b = rmass C + rectangleStar C b + rectangleRemainder C b := by
  rw [rectangleRemainder, rectangle_nonstar_row_mean hp2, rectangle_before_centering hp2]
  ring

theorem rectangleRemainder_row_mean (C : CoreT (ZMod p)) :
    pairLaw.expect (rectangleRemainder C) = 0 := by
  unfold rectangleRemainder
  simp only [FiniteLaw.expect_sub, FiniteLaw.expect_const, sub_self]

theorem rectangleRemainder_action (f : PairT (ZMod p) → ℝ) :
    recOp pairLaw rectangleRemainder f = recOp pairLaw Nrect (center pairLaw f) := by
  funext C
  unfold recOp rectangleRemainder center
  simp only [sub_mul, mul_sub, FiniteLaw.expect_sub, FiniteLaw.expect_const_mul,
    FiniteLaw.expect_mul_const]

variable [Nonempty (CoreT (ZMod p))]

theorem rectangleRemainder_norm (hW : Labellings.WeilBound (ZMod p)) (hDLK : Target.FourCycle)
    (hp3 : p % 4 = 3) (hp40 : 2 ^ 40 ≤ p) (f : PairT (ZMod p) → ℝ) :
    nrm coreLaw (recOp pairLaw rectangleRemainder f) ≤ (282 * (p : ℝ)⁻¹) * nrm pairLaw f := by
  rw [rectangleRemainder_action]
  exact (rectangle_nonstar_norm_282_target hW hDLK hp3 hp40 (center pairLaw f)).trans
    (mul_le_mul_of_nonneg_left (nrm_center_le pairLaw f) (by positivity))

end Sarkozy.PositiveRoots.CoherentFrame
