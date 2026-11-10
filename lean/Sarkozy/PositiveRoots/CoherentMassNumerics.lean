module

public import Sarkozy.PositiveRoots.CoherentMassMoment
public import Sarkozy.PositiveRoots.CoherentCovarianceNumerics

/-! Explicit mass-variation prices at the endpoint p = 2^40 and above. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Sarkozy.L20Cap Sarkozy.SpectralC Sarkozy.SpectralD Sarkozy.Variance
open Sarkozy.Cuts Sarkozy.Recentering

variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem weightedMoment_price_small_40 (hp40 : 2 ^ 40 ≤ p) :
    (5 * (p : ℝ)⁻¹ + 34 * (p : ℝ)⁻¹ * rp p + 11 * (p : ℝ)⁻¹ ^ 3) /
      RootMarginal.Z4 ((p : ℝ)⁻¹) ≤ ((2239 / 1000 : ℝ) * rp p) ^ 2 := by
  have hq0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hr0 := rp_nonneg (p := p)
  have hq := q_small_40 hp40
  have hr := rp_small_40 hp40
  have hqsq : (p : ℝ)⁻¹ ^ 2 ≤ (p : ℝ)⁻¹ := by
    nlinarith [mul_nonneg hq0 (show 0 ≤ 1 - (p : ℝ)⁻¹ by linarith)]
  have hZ : 0 < RootMarginal.Z4 ((p : ℝ)⁻¹) := by
    unfold RootMarginal.Z4
    have h1 : 0 < 1 - (p : ℝ)⁻¹ := by linarith
    have h3 : 0 < 1 - 3 * (p : ℝ)⁻¹ := by linarith
    have h7 : 0 < 1 - 7 * (p : ℝ)⁻¹ := by linarith
    positivity
  have hd : 1 / RootMarginal.Z4 ((p : ℝ)⁻¹) ≤ (10001 / 10000 : ℝ) := by
    have he : coreCubeDensity p / 16 = 1 / RootMarginal.Z4 ((p : ℝ)⁻¹) := by
      unfold coreCubeDensity RootMarginal.Z4
      ring
    rw [← he]
    exact core_density_small_40 hp40
  have hn : 5 + 34 * rp p + 11 * (p : ℝ)⁻¹ ^ 2 ≤ (50001 / 10000 : ℝ) := by
    nlinarith
  calc
    _ = (p : ℝ)⁻¹ * ((5 + 34 * rp p + 11 * (p : ℝ)⁻¹ ^ 2) *
        (1 / RootMarginal.Z4 ((p : ℝ)⁻¹))) := by ring
    _ ≤ (p : ℝ)⁻¹ * ((50001 / 10000 : ℝ) * (10001 / 10000)) := by gcongr
    _ ≤ _ := by rw [mul_pow, rp_sq]; nlinarith

variable [Nonempty (CoreT (ZMod p))]

theorem core_softW_norm_small_40 (hAO : Target.AhlgrenOno) (hp3 : p % 4 = 3)
    (hp40 : 2 ^ 40 ≤ p) :
    nrm coreLaw (fun C : CoreT (ZMod p) =>
      (RootMarginal.softW (C.val 0) (C.val 1) (C.val 2) (C.val 3) : ℝ) / p) ≤
        (2239 / 1000 : ℝ) * rp p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hr : rp p * Real.sqrt p = 1 := by unfold rp; exact inv_mul_cancel₀ (by positivity)
  have hm := core_softW_second_moment hp3 (by omega : 7 < p) hAO hr
  simp only [one_div] at hm
  have hs := hm.trans (weightedMoment_price_small_40 hp40)
  rw [← nrm_sq_expect] at hs
  exact (abs_le_of_sq_le_sq' hs (mul_nonneg (by norm_num) (rp_nonneg (p := p)))).2

theorem core_Kbar_norm_small_40 (hAO : Target.AhlgrenOno) (hp3 : p % 4 = 3)
    (hp40 : 2 ^ 40 ≤ p) :
    nrm coreLaw (fun C : CoreT (ZMod p) => Kbar C.val - 1) ≤
      (224 / 100 : ℝ) * rp p := by
  have hsoft := core_softW_norm_small_40 hAO hp3 hp40
  have he : (fun C : CoreT (ZMod p) => Kbar C.val - 1) = fun C =>
      2 / (p : ℝ) + (RootMarginal.softW (C.val 0) (C.val 1) (C.val 2) (C.val 3) : ℝ) / p :=
    funext (Kbar_softW (by omega : p ≠ 2))
  have hn : nrm (coreLaw (F := ZMod p)) (fun _ => 2 / (p : ℝ)) = 2 / (p : ℝ) := by
    simpa only [mul_one, nrm_one, abs_of_nonneg (by positivity : 0 ≤ 2 / (p : ℝ))] using
      nrm_smul (coreLaw (F := ZMod p)) (2 / (p : ℝ)) (fun _ => 1)
  have hr := rp_small_40 hp40
  have hr0 := rp_nonneg (p := p)
  have hq : 2 / (p : ℝ) + (2239 / 1000 : ℝ) * rp p ≤ (224 / 100 : ℝ) * rp p := by
    rw [div_eq_mul_inv, ← rp_sq]
    nlinarith [mul_nonneg hr0 (show 0 ≤ 1 / 1000000 - rp p by linarith)]
  rw [he]
  exact (nrm_add_le _ _ _).trans (by rw [hn]; linarith)

variable [Nonempty (PairT (ZMod p))]

theorem rectangle_mass_variation_small_40 (hW : Labellings.WeilBound (ZMod p))
    (hAO : Target.AhlgrenOno) (hp3 : p % 4 = 3) (hp40 : 2 ^ 40 ≤ p) :
    nrm coreLaw (fun C : CoreT (ZMod p) => rmass C - 1) ≤ (9 / 2 : ℝ) * rp p := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hη : ∀ C : CoreT (ZMod p), |Kbar C.val - 1| ≤ etaL (ZMod p) :=
    fun C => Kbar_dev hF hW C.property.1
  have hm := nrm_rmass_sub_one_le (JointRows.PaleyGauss.chi_neg_one hp3) hη
    (core_Kbar_norm_small_40 hAO hp3 hp40)
  rw [ZMod.card] at hm
  have hq := q_small_40 hp40
  have hr := rp_small_40 hp40
  have he := etaL_small_40 hp40
  have hr0 := rp_nonneg (p := p)
  have hη0 : 0 ≤ etaL (ZMod p) := by unfold etaL; positivity
  apply hm.trans
  rw [div_le_iff₀ (by linarith : 0 < 1 - (p : ℝ)⁻¹)]
  have hmul : (2 + etaL (ZMod p) + 16 * (p : ℝ)⁻¹) * (224 / 100 : ℝ) ≤
      (2 + 1 / 50000 + 16 / 100000000) * (224 / 100 : ℝ) := by linarith
  have hmulr := mul_le_mul_of_nonneg_right hmul hr0
  have hqsmall : (p : ℝ)⁻¹ ≤ rp p / 1000000 := by
    rw [← rp_sq]
    nlinarith [mul_nonneg hr0 (show 0 ≤ 1 / 1000000 - rp p by linarith)]
  have hqr := mul_le_mul_of_nonneg_right hq hr0
  nlinarith

end Sarkozy.PositiveRoots.CoherentFrame
