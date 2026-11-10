module

public import Sarkozy.PositiveRoots.CoherentOffdiagActual
public import Sarkozy.PartV.CoherentDiagonalOperator

/-! An unconditional soft-kernel bound from the actual accepting rectangle's row masses. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.L20Cap Sarkozy.Cuts Sarkozy.Recentering Sarkozy.Labellings

variable {p : ℕ} [Fact p.Prime]

theorem Rk_nonneg_actual (hp3 : p % 4 = 3) (c : CoreT (ZMod p)) (b : PairT (ZMod p)) :
    0 ≤ Rk c b := by
  have hm1 := JointRows.PaleyGauss.chi_neg_one hp3
  exact mul_nonneg (Kz_nonneg hm1 c.property b.val.1) (Kz_nonneg hm1 c.property b.val.2)

theorem Ksoft_nonneg_actual (hp3 : p % 4 = 3)
    (x y : CoreT (ZMod p) × PairT (ZMod p)) : 0 ≤ Ksoft x y :=
  mul_nonneg (Rk_nonneg_actual hp3 _ _) (Rk_nonneg_actual hp3 _ _)

theorem Ksoft_rowmass (hp3 : p % 4 = 3)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]
    (x : CoreT (ZMod p) × PairT (ZMod p)) :
    (coreLaw.product pairLaw).expect (fun y => Ksoft x y) =
      rmass x.1 * coreLaw.expect (rmass (F := ZMod p)) := by
  rw [FiniteLaw.expect_product]
  simp only [Ksoft, FiniteLaw.expect_mul_const, FiniteLaw.expect_const_mul]
  change rmass x.1 * coreLaw.expect (fun c => Rk c x.2) = _
  congr 1
  simpa only [recAdj, mul_one] using adj_one (JointRows.PaleyGauss.chi_neg_one hp3) x.2

theorem Ksoft_rectangle_bound (hW : WeilBound (ZMod p)) (hp3 : p % 4 = 3)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]
    (f : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    |kernelForm (coreLaw.product pairLaw) (coreLaw.product pairLaw) Ksoft f f| ≤
      rectangleMassUpper p ^ 2 * nrm (coreLaw.product pairLaw) f ^ 2 := by
  have hm1 := JointRows.PaleyGauss.chi_neg_one hp3
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have ha (c : CoreT (ZMod p)) : rmass c ≤ rectangleMassUpper p := by
    simpa only [rectangleMassUpper, ZMod.card] using rmass_le hm1 hF hW c
  apply schur_test _ _ (Ksoft_nonneg_actual hp3) (fun x y => mul_comm _ _)
  intro x _
  rw [Ksoft_rowmass hp3, pow_two]
  exact mul_le_mul (ha x.1) (FiniteLaw.expect_le_const _ ha)
    (FiniteLaw.expect_nonneg _ fun c =>
      FiniteLaw.expect_nonneg _ fun b => Rk_nonneg_actual hp3 c b) rectangleMassUpper_nonneg

theorem Ksoft_actual_bound (hW : WeilBound (ZMod p)) (hp3 : p % 4 = 3) (hp6 : 6 ≤ p)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]
    (f : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    |kernelForm (halfLaw (by rwa [ZMod.card])) (halfLaw (by rwa [ZMod.card])) Ksoft f f| ≤
      (rectangleMassUpper p ^ 2 * privateCompression p) *
        nrm (halfLaw (by rwa [ZMod.card])) f ^ 2 := by
  have h6 : 6 ≤ Fintype.card (ZMod p) := by rwa [ZMod.card]
  have h := condLaw_abs (coreLaw.product pairLaw) Avoid (hP_pos h6) Ksoft
    (Ksoft_rectangle_bound hW hp3) f
  change _ ≤ rectangleMassUpper p ^ 2 / prob (coreLaw.product pairLaw) Avoid *
    nrm (halfLaw h6) f ^ 2 at h
  refine h.trans ?_
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hP_inv_le_privateCompression hp6) (sq_nonneg _)) (sq_nonneg _)

end Sarkozy.PositiveRoots.CoherentFrame
