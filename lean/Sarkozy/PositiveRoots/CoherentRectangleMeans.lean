module

public import Sarkozy.PositiveRoots.CoherentRectangleExpansion
public import Sarkozy.L20Cap.AffineMeans

/-! Both feature factors and the centered rectangle remainder have zero column means. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.L20Cap Sarkozy.SpectralC Sarkozy.SpectralC.TwoLabel Sarkozy.SpectralD
open Sarkozy.Cuts Sarkozy.Recentering

variable {p : ℕ} [Fact p.Prime]

theorem centeredPoint_affine (α β a z : ZMod p) (hα : α ≠ 0) :
    centeredPointKernel (α * a + β) (α * z + β) = centeredPointKernel a z := by
  have he : α * a + β = α * z + β ↔ a = z := by
    constructor
    · intro h
      exact mul_left_cancel₀ hα (add_right_cancel h)
    · intro h
      rw [h]
  simp only [centeredPointKernel, he]

theorem coreWKernel_affine (α β : ZMod p) (hα : quadraticChar (ZMod p) α = 1)
    (C : CoreT (ZMod p)) (z : ZMod p) :
    coreWKernel (affCoreEquiv hα β C) (α * z + β) = coreWKernel C z := by
  unfold coreWKernel
  congr 1
  exact sum_congr rfl fun i _ => centeredPoint_affine α β (C.val i) z (ne_zero_of_chi hα)

variable [Nonempty (CoreT (ZMod p))]

theorem coreZKernel_column_mean (z : ZMod p) :
    coreLaw.expect (fun C : CoreT (ZMod p) => coreZKernel C.val z) = 0 := by
  apply coreKernel_column_mean_zero
    (fun C : CoreT (ZMod p) => coreZKernel C.val) _ (fun C => coreZKernel_mean_zero C.val)
  intro β C y
  simpa only [one_mul] using coreZKernel_affine 1 β (map_one _) C y

theorem coreWKernel_column_mean (z : ZMod p) :
    coreLaw.expect (fun C : CoreT (ZMod p) => coreWKernel C z) = 0 := by
  apply coreKernel_column_mean_zero coreWKernel _ coreW_mean_zero
  intro β C y
  simpa only [one_mul] using coreWKernel_affine 1 β (map_one _) C y

theorem rectangleStar_column_mean (b : PairT (ZMod p)) :
    coreLaw.expect (fun C : CoreT (ZMod p) => rectangleStar C b) = 0 := by
  unfold rectangleStar
  simp only [FiniteLaw.expect_add, FiniteLaw.expect_const_mul]
  rw [Cuts.expect_comm coreLaw (fieldLaw p), Cuts.expect_comm coreLaw (fieldLaw p)]
  simp only [FiniteLaw.expect_mul_const, coreZKernel_column_mean, coreWKernel_column_mean,
    zero_mul, FiniteLaw.expect_const, mul_zero, add_zero]

variable [Nonempty (PairT (ZMod p))]

theorem rectangleRemainder_column_mean (hp3 : p % 4 = 3) (b : PairT (ZMod p)) :
    coreLaw.expect (fun C : CoreT (ZMod p) => rectangleRemainder C b) = 0 := by
  have he := adj_one (JointRows.PaleyGauss.chi_neg_one hp3) b
  simp only [recAdj, mul_one] at he
  simp_rw [rectangle_rank_star_remainder (by omega : p ≠ 2)] at he
  rw [FiniteLaw.expect_add, FiniteLaw.expect_add, rectangleStar_column_mean, add_zero] at he
  linarith

end Sarkozy.PositiveRoots.CoherentFrame
