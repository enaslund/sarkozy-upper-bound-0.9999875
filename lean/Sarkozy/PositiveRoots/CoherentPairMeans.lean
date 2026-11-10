module

public import Sarkozy.PositiveRoots.CoherentElementaryFeatures

/-! Both pair features are centered in the physical pair variable as well. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.L20Cap Sarkozy.SpectralC Sarkozy.SpectralC.TwoLabel Sarkozy.SpectralD
open Sarkozy.Cuts Sarkozy.Recentering

variable {p : ℕ} [Fact p.Prime] [Nonempty (PairT (ZMod p))]

theorem pair_fst_expect (f : ZMod p → ℝ) :
    pairLaw.expect (fun b : PairT (ZMod p) => f b.val.1) = (fieldLaw p).expect f := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    linarith
  rw [pairLaw_expect (fun b : ZMod p × ZMod p => f b.1), fieldLaw, FiniteLaw.expect_uniform,
    ZMod.card]
  simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul, ← mul_sum]
  field_simp

theorem pair_snd_expect (f : ZMod p → ℝ) :
    pairLaw.expect (fun b : PairT (ZMod p) => f b.val.2) = (fieldLaw p).expect f := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    linarith
  rw [pairLaw_expect (fun b : ZMod p × ZMod p => f b.2), fieldLaw, FiniteLaw.expect_uniform,
    ZMod.card]
  simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  field_simp

theorem pair_chi_product_expect (hp2 : p ≠ 2) (z : ZMod p) :
    pairLaw.expect (fun b : PairT (ZMod p) => chi (b.val.1 - z) * chi (b.val.2 - z)) =
      -(p : ℝ)⁻¹ := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    linarith
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  rw [pairLaw_expect (fun b : ZMod p × ZMod p => chi (b.1 - z) * chi (b.2 - z))]
  dsimp only
  rw [← sum_mul_sum, L20Cap.sum_chi_shift hF z, zero_mul, sum_chi_mul_chi hF z z]
  simp only [ite_true, ZMod.card]
  field_simp
  ring

theorem pairV_column_mean (z : ZMod p) :
    pairLaw.expect (fun b : PairT (ZMod p) => pairVKernel b z) = 0 := by
  have he : (fieldLaw p).expect (fun a => centeredPointKernel a z) = 0 := by
    convert centeredPoint_mean_zero z using 1
    congr 1
    funext a
    simp only [centeredPointKernel, eq_comm]
  unfold pairVKernel
  simp only [div_eq_mul_inv, FiniteLaw.expect_mul_const, FiniteLaw.expect_add]
  rw [pair_fst_expect (fun a => centeredPointKernel a z),
    pair_snd_expect (fun a => centeredPointKernel a z), he]
  simp

theorem pairE_column_mean (hp2 : p ≠ 2) (z : ZMod p) :
    pairLaw.expect (fun b : PairT (ZMod p) => pairEKernel b z) = 0 := by
  unfold pairEKernel
  simp only [div_eq_mul_inv, FiniteLaw.expect_mul_const, FiniteLaw.expect_add,
    FiniteLaw.expect_const, pair_chi_product_expect hp2 z, neg_add_cancel, zero_mul]

end Sarkozy.PositiveRoots.CoherentFrame
