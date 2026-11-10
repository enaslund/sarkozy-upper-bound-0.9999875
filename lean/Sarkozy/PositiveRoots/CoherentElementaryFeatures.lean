module

public import Sarkozy.PositiveRoots.CoherentZGram
public import Sarkozy.L20Cap.RectangleActual

/-! The centered singleton and private pair features of the accepting rectangle. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.L20Cap Sarkozy.SpectralC Sarkozy.SpectralC.TwoLabel Sarkozy.SpectralD
open Sarkozy.Cuts Sarkozy.Recentering
open Sarkozy.JointRows.StarOps (expect_finset_sum)

variable {p : ℕ} [Fact p.Prime]

noncomputable def centeredPointKernel (a z : ZMod p) : ℝ :=
  (if a = z then (p : ℝ) else 0) - 1

theorem centeredPoint_action (a : ZMod p) (f : ZMod p → ℝ) :
    (fieldLaw p).expect (fun z => centeredPointKernel a z * f z) =
      f a - (fieldLaw p).expect f := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have he (z : ZMod p) : centeredPointKernel a z * f z =
      (p : ℝ) * (if a = z then f z else 0) - f z := by
    unfold centeredPointKernel
    split_ifs <;> ring
  simp_rw [he]
  rw [FiniteLaw.expect_sub, FiniteLaw.expect_const_mul]
  change (p : ℝ) * (FiniteLaw.uniform (ZMod p)).expect (fun z => if a = z then f z else 0) - _ = _
  rw [uniform_diagonal_expect, ZMod.card, mul_div_cancel₀ _ hp]

theorem centeredPoint_mean_zero (a : ZMod p) :
    (fieldLaw p).expect (centeredPointKernel a) = 0 := by
  simpa only [mul_one, FiniteLaw.expect_const, sub_self] using centeredPoint_action a (fun _ => 1)

noncomputable def pairVKernel (b : PairT (ZMod p)) (z : ZMod p) : ℝ :=
  (centeredPointKernel b.val.1 z + centeredPointKernel b.val.2 z) / Real.sqrt 2

noncomputable def coreWKernel (C : CoreT (ZMod p)) (z : ZMod p) : ℝ :=
  (∑ i : Fin 4, centeredPointKernel (C.val i) z) / 2

noncomputable def pairEKernel (b : PairT (ZMod p)) (z : ZMod p) : ℝ :=
  (chi (b.val.1 - z) * chi (b.val.2 - z) + (p : ℝ)⁻¹) / rp p

theorem pairV_action (b : PairT (ZMod p)) (f : ZMod p → ℝ) :
    recOp (fieldLaw p) pairVKernel f b =
      (f b.val.1 + f b.val.2 - 2 * (fieldLaw p).expect f) / Real.sqrt 2 := by
  unfold recOp pairVKernel
  simp only [div_eq_mul_inv, add_mul, mul_right_comm _ (Real.sqrt 2)⁻¹,
    FiniteLaw.expect_mul_const, FiniteLaw.expect_add, centeredPoint_action]
  ring

theorem coreW_action (C : CoreT (ZMod p)) (f : ZMod p → ℝ) :
    recOp (fieldLaw p) coreWKernel f C =
      ((∑ i : Fin 4, f (C.val i)) - 4 * (fieldLaw p).expect f) / 2 := by
  unfold recOp coreWKernel
  simp only [div_eq_mul_inv, mul_right_comm _ (2 : ℝ)⁻¹, FiniteLaw.expect_mul_const,
    sum_mul, expect_finset_sum, centeredPoint_action]
  rw [← sum_mul, sum_sub_distrib]
  simp

theorem pairV_mean_zero (b : PairT (ZMod p)) : (fieldLaw p).expect (pairVKernel b) = 0 := by
  unfold pairVKernel
  simp only [div_eq_mul_inv, FiniteLaw.expect_mul_const, FiniteLaw.expect_add,
    centeredPoint_mean_zero, zero_add, zero_mul]

theorem coreW_mean_zero (C : CoreT (ZMod p)) : (fieldLaw p).expect (coreWKernel C) = 0 := by
  unfold coreWKernel
  simp only [div_eq_mul_inv, FiniteLaw.expect_mul_const, expect_finset_sum,
    centeredPoint_mean_zero, sum_const_zero, zero_mul]

theorem pairE_mean_zero (hp2 : p ≠ 2) (b : PairT (ZMod p)) :
    (fieldLaw p).expect (pairEKernel b) = 0 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have hs := sum_chi_rev hF b.val.1 b.val.2
  rw [ite_eq_right b.property] at hs
  have he : (fieldLaw p).expect (fun z => chi (b.val.1 - z) * chi (b.val.2 - z)) =
      -(p : ℝ)⁻¹ := by
    rw [fieldLaw, FiniteLaw.expect_uniform, ZMod.card, hs]
    ring
  unfold pairEKernel
  simp only [div_eq_mul_inv, FiniteLaw.expect_mul_const, FiniteLaw.expect_add,
    FiniteLaw.expect_const, he, neg_add_cancel, zero_mul]

theorem pairE_action (b : PairT (ZMod p)) (f : ZMod p → ℝ)
    (hf : (fieldLaw p).expect f = 0) :
    recOp (fieldLaw p) pairEKernel f b = Wop f b / rp p := by
  unfold recOp pairEKernel
  have he (z : ZMod p) :
      (chi (b.val.1 - z) * chi (b.val.2 - z) + (p : ℝ)⁻¹) / rp p * f z =
      (chi (b.val.1 - z) * chi (b.val.2 - z) * f z) * (rp p)⁻¹ +
        ((p : ℝ)⁻¹ * (rp p)⁻¹) * f z := by ring
  simp_rw [he]
  rw [FiniteLaw.expect_add, FiniteLaw.expect_mul_const, FiniteLaw.expect_const_mul, hf,
    mul_zero, add_zero, fieldLaw, FiniteLaw.expect_uniform, ZMod.card]
  unfold Wop
  rw [ZMod.card]
  ring

end Sarkozy.PositiveRoots.CoherentFrame
