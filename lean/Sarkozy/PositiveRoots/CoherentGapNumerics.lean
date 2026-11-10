module

public import Sarkozy.L20Cap.GapSumSquares
public import Sarkozy.L20Cap.GapRange
public import Sarkozy.L20Cap.GapComplement
public import Sarkozy.L20Cap.RectangleActual
public import Sarkozy.PositiveRoots.CoherentCovarianceNumerics

/-! The centered rectangle has norm at most 5.9 / √p for p ≥ 2^40. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Sarkozy.L20Cap Sarkozy.SpectralC Sarkozy.SpectralD
open Sarkozy.Cuts Sarkozy.Recentering

variable {p : ℕ} [Fact p.Prime]

theorem rectangle_range_price_small_40 (hp40 : 2 ^ 40 ≤ p) :
    Real.sqrt (2 * (p : ℝ)⁻¹ *
      (15 + 44 * etaL (ZMod p) + (42 + 12 * etaL (ZMod p)) * etaL (ZMod p) ^ 2) /
      ((1 - (p : ℝ)⁻¹) ^ 2 * (1 - 2 * (p : ℝ)⁻¹))) ≤ (11 / 2 : ℝ) * rp p := by
  have hq0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hr0 := rp_nonneg (p := p)
  have hq := q_small_40 hp40
  have hη := etaL_small_40 hp40
  have hη0 : 0 ≤ etaL (ZMod p) := by unfold etaL; positivity
  have htail : (42 + 12 * etaL (ZMod p)) * etaL (ZMod p) ^ 2 ≤
      (42 + 12 * (1 / 50000 : ℝ)) * (1 / 50000 : ℝ) ^ 2 := by gcongr
  have hM : 15 + 44 * etaL (ZMod p) +
      (42 + 12 * etaL (ZMod p)) * etaL (ZMod p) ^ 2 ≤ (1501 / 100 : ℝ) := by
    linarith
  have hD : (999 / 1000 : ℝ) ≤ (1 - (p : ℝ)⁻¹) ^ 2 * (1 - 2 * (p : ℝ)⁻¹) := by
    calc
      _ ≤ (9999 / 10000 : ℝ) ^ 2 * (9999 / 10000) := by norm_num
      _ ≤ _ := by gcongr <;> linarith
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by linarith : 0 <
    (1 - (p : ℝ)⁻¹) ^ 2 * (1 - 2 * (p : ℝ)⁻¹)), mul_pow, rp_sq]
  calc
    _ ≤ 2 * (p : ℝ)⁻¹ * (1501 / 100) := by gcongr
    _ ≤ (11 / 2 : ℝ) ^ 2 * (p : ℝ)⁻¹ * (999 / 1000) := by nlinarith
    _ ≤ _ := by gcongr

omit [Fact p.Prime] in
theorem rectangle_complement_price_small_40 (hp40 : 2 ^ 40 ≤ p) :
    2 * rp p + 282 * (p : ℝ)⁻¹ ≤ (2001 / 1000 : ℝ) * rp p := by
  have hr := rp_small_40 hp40
  have hr0 := rp_nonneg (p := p)
  rw [← rp_sq]
  nlinarith [mul_nonneg hr0 (show 0 ≤ 1 / 1000000 - rp p by linarith)]

variable [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]

theorem rectangle_centered_norm_small_40 (hW : Labellings.WeilBound (ZMod p))
    (hDLK : Target.FourCycle) (hp3 : p % 4 = 3) (hp40 : 2 ^ 40 ≤ p)
    (f : PairT (ZMod p) → ℝ) :
    nrm coreLaw (recOp pairLaw Rc f) ≤ ((59 / 10 : ℝ) * rp p) * nrm pairLaw f := by
  have hr0 := rp_nonneg (p := p)
  have h5 : 5 ≤ Fintype.card (ZMod p) := by rw [ZMod.card]; omega
  have hm1 := JointRows.PaleyGauss.chi_neg_one hp3
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hη : ∀ C : CoreT (ZMod p), |Kbar C.val - 1| ≤ etaL (ZMod p) :=
    fun C => Kbar_dev hF hW C.property.1
  have hm : (coreLaw (F := ZMod p)).expect (fun C => Kbar C.val - 1) ≤ etaL (ZMod p) :=
    coreLaw.expect_le_const (fun C => (le_abs_self _).trans (hη C))
  apply pair_ranges_sum_squares h5 (τ := (11 / 2 : ℝ) * rp p)
    (l := (2001 / 1000 : ℝ) * rp p) (c := (59 / 10 : ℝ) * rp p)
    (by positivity) ?_ ?_ ?_ f
  · nlinarith [sq_nonneg (rp p)]
  · intro h hh
    have hb := hA_proved hm1 h5 hη hm h hh
    rw [ZMod.card] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (rectangle_range_price_small_40 hp40)
      (nrm_nonneg _ _))
  · intro g hg horth
    have hb := hB_of_nonstar hm1 hF h5
      (fun g _ _ => rectangle_nonstar_norm_282_target hW hDLK hp3 hp40 g) g hg horth
    rw [ZMod.card] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (rectangle_complement_price_small_40 hp40)
      (nrm_nonneg _ _))

end Sarkozy.PositiveRoots.CoherentFrame
