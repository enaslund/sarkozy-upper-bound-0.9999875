module

public import Sarkozy.PositiveRoots.CoherentElementaryFeatures

/-! Exact Grams and unit norm bounds for the rectangle's v, w and e features. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.L20Cap Sarkozy.SpectralC Sarkozy.SpectralC.TwoLabel Sarkozy.SpectralD
open Sarkozy.Cuts Sarkozy.Recentering

variable {p : ℕ} [Fact p.Prime]

theorem field_sum_zero (f : ZMod p → ℝ) (hf : (fieldLaw p).expect f = 0) : ∑ z, f z = 0 := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [fieldLaw, FiniteLaw.expect_uniform, ZMod.card] at hf
  exact (div_eq_zero_iff.mp hf).resolve_right hp

theorem field_norm_sq_sum (f : ZMod p → ℝ) :
    nrm (fieldLaw p) f ^ 2 = (∑ z, f z ^ 2) / (p : ℝ) := by
  rw [nrm_sq_expect, fieldLaw, FiniteLaw.expect_uniform, ZMod.card]

theorem prime_q_lt_one : (p : ℝ)⁻¹ < 1 := by
  apply inv_lt_one_of_one_lt₀
  exact_mod_cast (Fact.out : p.Prime).one_lt

section Pair

variable [Nonempty (PairT (ZMod p))]

theorem pairV_norm_sq (f : ZMod p → ℝ) (hf : (fieldLaw p).expect f = 0) :
    nrm pairLaw (recOp (fieldLaw p) pairVKernel f) ^ 2 =
      ((1 - 2 * (p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹)) * nrm (fieldLaw p) f ^ 2 := by
  have h := vfeat_sq f (field_sum_zero f hf)
  simp only [ZMod.card] at h
  rw [nrm_sq_expect]
  simp_rw [pairV_action, hf, mul_zero, sub_zero, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp_rw [div_eq_mul_inv]
  rw [FiniteLaw.expect_mul_const, h, field_norm_sq_sum]
  ring

theorem pairV_norm_zero (f : ZMod p → ℝ) (hf : (fieldLaw p).expect f = 0) :
    nrm pairLaw (recOp (fieldLaw p) pairVKernel f) ≤ nrm (fieldLaw p) f := by
  have hprice : (1 - 2 * (p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ≤ 1 := by
    rw [div_le_one (by linarith [prime_q_lt_one (p := p)])]
    have : 0 ≤ (p : ℝ)⁻¹ := by positivity
    linarith
  have h := mul_le_mul_of_nonneg_right hprice (sq_nonneg (nrm (fieldLaw p) f))
  rw [← pairV_norm_sq f hf, one_mul] at h
  exact (abs_le_of_sq_le_sq' h (nrm_nonneg _ _)).2

theorem pairV_norm (f : ZMod p → ℝ) :
    nrm pairLaw (recOp (fieldLaw p) pairVKernel f) ≤ nrm (fieldLaw p) f := by
  have h := pairV_norm_zero (center (fieldLaw p) f) (expect_center _ _)
  rw [recOp_center_of_row_mean_zero (fieldLaw p) pairVKernel pairV_mean_zero f] at h
  exact h.trans (nrm_center_le _ _)

theorem pairE_norm_sq (hp2 : p ≠ 2) (f : ZMod p → ℝ) (hf : (fieldLaw p).expect f = 0) :
    nrm pairLaw (recOp (fieldLaw p) pairEKernel f) ^ 2 =
      ((1 - 2 * (p : ℝ)⁻¹ - (p : ℝ)⁻¹ ^ 2) / (1 - (p : ℝ)⁻¹)) *
        nrm (fieldLaw p) f ^ 2 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have h := Wop_sq hF f (field_sum_zero f hf)
  simp only [ZMod.card] at h
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [nrm_sq_expect]
  simp_rw [pairE_action _ f hf, div_pow, rp_sq, div_eq_mul_inv, inv_inv]
  rw [FiniteLaw.expect_mul_const, h, field_norm_sq_sum]
  field_simp

theorem pairE_norm_zero (hp2 : p ≠ 2) (f : ZMod p → ℝ) (hf : (fieldLaw p).expect f = 0) :
    nrm pairLaw (recOp (fieldLaw p) pairEKernel f) ≤ nrm (fieldLaw p) f := by
  have hprice : (1 - 2 * (p : ℝ)⁻¹ - (p : ℝ)⁻¹ ^ 2) / (1 - (p : ℝ)⁻¹) ≤ 1 := by
    rw [div_le_one (by linarith [prime_q_lt_one (p := p)])]
    have : 0 ≤ (p : ℝ)⁻¹ := by positivity
    nlinarith [sq_nonneg ((p : ℝ)⁻¹)]
  have h := mul_le_mul_of_nonneg_right hprice (sq_nonneg (nrm (fieldLaw p) f))
  rw [← pairE_norm_sq hp2 f hf, one_mul] at h
  exact (abs_le_of_sq_le_sq' h (nrm_nonneg _ _)).2

theorem pairE_norm (hp2 : p ≠ 2) (f : ZMod p → ℝ) :
    nrm pairLaw (recOp (fieldLaw p) pairEKernel f) ≤ nrm (fieldLaw p) f := by
  have h := pairE_norm_zero hp2 (center (fieldLaw p) f) (expect_center _ _)
  rw [recOp_center_of_row_mean_zero (fieldLaw p) pairEKernel (pairE_mean_zero hp2) f] at h
  exact h.trans (nrm_center_le _ _)

end Pair

section Core

variable [Nonempty (CoreT (ZMod p))]

theorem coreW_norm_sq (hp3 : p % 4 = 3) (f : ZMod p → ℝ) (hf : (fieldLaw p).expect f = 0) :
    nrm coreLaw (recOp (fieldLaw p) coreWKernel f) ^ 2 =
      ((1 - 4 * (p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹)) * nrm (fieldLaw p) f ^ 2 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have h := wvec_sq (JointRows.PaleyGauss.chi_neg_one hp3) hF f (field_sum_zero f hf)
  simp only [ZMod.card] at h
  rw [nrm_sq_expect]
  simp_rw [coreW_action, hf, mul_zero, sub_zero, Fin.sum_univ_four]
  rw [h, field_norm_sq_sum]

theorem coreW_norm_zero (hp3 : p % 4 = 3) (f : ZMod p → ℝ) (hf : (fieldLaw p).expect f = 0) :
    nrm coreLaw (recOp (fieldLaw p) coreWKernel f) ≤ nrm (fieldLaw p) f := by
  have hprice : (1 - 4 * (p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ≤ 1 := by
    rw [div_le_one (by linarith [prime_q_lt_one (p := p)])]
    have : 0 ≤ (p : ℝ)⁻¹ := by positivity
    linarith
  have h := mul_le_mul_of_nonneg_right hprice (sq_nonneg (nrm (fieldLaw p) f))
  rw [← coreW_norm_sq hp3 f hf, one_mul] at h
  exact (abs_le_of_sq_le_sq' h (nrm_nonneg _ _)).2

theorem coreW_norm (hp3 : p % 4 = 3) (f : ZMod p → ℝ) :
    nrm coreLaw (recOp (fieldLaw p) coreWKernel f) ≤ nrm (fieldLaw p) f := by
  have h := coreW_norm_zero hp3 (center (fieldLaw p) f) (expect_center _ _)
  rw [recOp_center_of_row_mean_zero (fieldLaw p) coreWKernel coreW_mean_zero f] at h
  exact h.trans (nrm_center_le _ _)

end Core

end Sarkozy.PositiveRoots.CoherentFrame
