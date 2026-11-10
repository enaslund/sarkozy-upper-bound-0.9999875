module

public import Sarkozy.PositiveRoots.CoherentZPhysical
public import Sarkozy.L20Cap.AffineGram

/-! The actual centered Z feature has operator norm at most 1.001 for p ≥ 2^40. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Sarkozy.L20Cap Sarkozy.SpectralC Sarkozy.SpectralC.TwoLabel Sarkozy.SpectralD
open Sarkozy.Cuts Sarkozy.Recentering

variable {p : ℕ} [Fact p.Prime]

theorem coreZKernel_affine (α β : ZMod p) (hα : quadraticChar (ZMod p) α = 1)
    (C : CoreT (ZMod p)) (z : ZMod p) :
    coreZKernel (affCoreEquiv hα β C).val (α * z + β) = coreZKernel C.val z := by
  change (Kz (α * z + β) (affCore α β C.val) - Kbar (affCore α β C.val)) /
    (Real.sqrt 15 * rp p) = _
  rw [Kz_affine hα, Kbar_affine hα]
  rfl

theorem field_Kz_expect (x : Fin 4 → ZMod p) : (fieldLaw p).expect (fun z => Kz z x) = Kbar x := by
  rw [fieldLaw, FiniteLaw.expect_uniform]
  rfl

theorem coreZKernel_second_moment (hp3 : p % 4 = 3) (C : CoreT (ZMod p)) :
    (fieldLaw p).expect (fun z => coreZKernel C.val z ^ 2) =
      ((p : ℝ) / 15) * (16 * Kbar C.val - Kbar C.val ^ 2) := by
  have hm1 := JointRows.PaleyGauss.chi_neg_one hp3
  have hs : (fieldLaw p).expect (fun z => Kz z C.val ^ 2) = 16 * Kbar C.val := by
    simp_rw [Kz_sq hm1 C.property]
    rw [FiniteLaw.expect_const_mul, field_Kz_expect]
  have hv := (fieldLaw p).expect_sq_sub_mean (fun z => Kz z C.val)
  rw [field_Kz_expect, hs] at hv
  change (fieldLaw p).expect (fun z => ((Kz z C.val - Kbar C.val) /
    (Real.sqrt 15 * rp p)) ^ 2) = _
  simp only [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15), rp_sq]
  simp only [div_eq_mul_inv, FiniteLaw.expect_mul_const, hv, mul_inv_rev, inv_inv]
  ring

theorem coreZKernel_second_moment_le (hW : Labellings.WeilBound (ZMod p))
    (hp3 : p % 4 = 3) (C : CoreT (ZMod p)) :
    (fieldLaw p).expect (fun z => coreZKernel C.val z ^ 2) ≤
      (p : ℝ) * (1 + (14 / 15 : ℝ) * etaL (ZMod p)) := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hdev := Kbar_dev hF hW C.property.1
  change |Kbar C.val - 1| ≤ etaL (ZMod p) at hdev
  have hu : Kbar C.val - 1 ≤ etaL (ZMod p) := (le_abs_self _).trans hdev
  rw [coreZKernel_second_moment hp3 C]
  have hpoly : 16 * Kbar C.val - Kbar C.val ^ 2 ≤ 15 + 14 * etaL (ZMod p) := by
    nlinarith [sq_nonneg (Kbar C.val - 1)]
  exact (mul_le_mul_of_nonneg_left hpoly (by positivity : 0 ≤ (p : ℝ) / 15)).trans_eq (by ring)

variable [Nonempty (CoreT (ZMod p))]

theorem coreZKernel_norm (hW : Labellings.WeilBound (ZMod p))
    (hp3 : p % 4 = 3) (hp40 : 2 ^ 40 ≤ p) (f : ZMod p → ℝ)
    (hf : (fieldLaw p).expect f = 0) :
    nrm coreLaw (recOp (fieldLaw p) (fun C : CoreT (ZMod p) => coreZKernel C.val) f) ≤
      (1001 / 1000 : ℝ) * nrm (fieldLaw p) f := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast (by omega : 2 ≤ p)
  have he := coreKernel_mean_zero_norm_sq (JointRows.PaleyGauss.chi_neg_one hp3)
    (fun C : CoreT (ZMod p) => coreZKernel C.val) coreZKernel_affine
    (fun C => coreZKernel_mean_zero C.val) f hf
  simp only [ZMod.card] at he
  have hm : coreLaw.expect (fun C : CoreT (ZMod p) =>
      (fieldLaw p).expect (fun z => coreZKernel C.val z ^ 2)) ≤
        (p : ℝ) * (1 + (14 / 15 : ℝ) * etaL (ZMod p)) :=
    coreLaw.expect_le_const (coreZKernel_second_moment_le hW hp3)
  have hη := etaL_small_40 hp40
  have hη0 : 0 ≤ etaL (ZMod p) := by unfold etaL; positivity
  have hden := private_density_small_40 hp40
  have hprice : (p : ℝ) * (1 + (14 / 15 : ℝ) * etaL (ZMod p)) / (p - 1) ≤
      (1001 / 1000 : ℝ) ^ 2 := by
    calc
      _ = ((p : ℝ) / (p - 1)) * (1 + (14 / 15 : ℝ) * etaL (ZMod p)) := by ring
      _ ≤ (10001 / 10000 : ℝ) * (1 + (14 / 15 : ℝ) * (1 / 50000)) := by gcongr
      _ ≤ _ := by norm_num
  apply nrm_le_of_sq_le coreLaw (fieldLaw p) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
  change nrm coreLaw (recOp (FiniteLaw.uniform (ZMod p))
    (fun C : CoreT (ZMod p) => coreZKernel C.val) f) ^ 2 ≤ _
  rw [he]
  change _ * nrm (fieldLaw p) f ^ 2 ≤ _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact (div_le_div_of_nonneg_right hm (by linarith : (0 : ℝ) ≤ p - 1)).trans hprice

theorem coreZKernel_norm_full (hW : Labellings.WeilBound (ZMod p))
    (hp3 : p % 4 = 3) (hp40 : 2 ^ 40 ≤ p) (f : ZMod p → ℝ) :
    nrm coreLaw (recOp (fieldLaw p) (fun C : CoreT (ZMod p) => coreZKernel C.val) f) ≤
      (1001 / 1000 : ℝ) * nrm (fieldLaw p) f := by
  have h := coreZKernel_norm hW hp3 hp40 (center (fieldLaw p) f)
    (expect_center (fieldLaw p) f)
  have he := recOp_center_of_row_mean_zero (fieldLaw p)
    (fun C : CoreT (ZMod p) => coreZKernel C.val)
    (fun C : CoreT (ZMod p) => coreZKernel_mean_zero C.val) f
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left (nrm_center_le (fieldLaw p) f) (by norm_num))

end Sarkozy.PositiveRoots.CoherentFrame
