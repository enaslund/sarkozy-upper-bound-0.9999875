module

public import Sarkozy.PositiveRoots.CoherentProductResidual
public import Sarkozy.PositiveRoots.CoherentGradedMeans
public import Sarkozy.PositiveRoots.CoherentCovarianceNumerics

/-! Uniform positive majorants for the coherent core products at p ≥ 2^40. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.L20Cap Sarkozy.SpectralC Sarkozy.SpectralD

noncomputable def coreMeanCap (p : ℕ) : ℝ := (201 / 100 : ℝ) * rp p

variable {p : ℕ}

theorem coreMeanCap_nonneg : 0 ≤ coreMeanCap p :=
  mul_nonneg (by norm_num) rp_nonneg

theorem gradedStarPrice_core_le (hp40 : 2 ^ 40 ≤ p) {S : Finset (Fin 4)} (hS : S.Nonempty) :
    gradedStarPrice p S.card ≤ coreMeanCap p := by
  have h1 := hS.card_pos
  have h4 : S.card ≤ 4 := card_le_univ S
  have hr := rp_nonneg (p := p)
  have hr1 := rp_small_40 hp40
  have hq := rp_sq (p := p)
  unfold coreMeanCap
  interval_cases hc : S.card <;>
    simp only [gradedStarPrice_one, gradedStarPrice_two, gradedStarPrice_three,
      gradedStarPrice_four] <;> nlinarith

theorem entangled_factor_times_r_le (hp40 : 2 ^ 40 ≤ p) :
    ((p : ℝ) / Real.sqrt (p - 1)) * rp p ≤ 1001 / 1000 := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast (by omega : 2 ≤ p)
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have he : (((p : ℝ) / Real.sqrt (p - 1)) * rp p) ^ 2 = (p : ℝ) / (p - 1) := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by linarith), rp_sq]
    field_simp
  have hb := private_density_small_40 hp40
  nlinarith

theorem variableProductPrice_small (hp40 : 2 ^ 40 ≤ p) (S T : Finset (Fin 4)) :
    variableProductPrice p S T (coreMeanCap p) (coreMeanCap p) ≤ 101 / 100 := by
  have hr := rp_nonneg (p := p)
  have hr1 := rp_small_40 hp40
  have hq := q_small_40 hp40
  have hq0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hc : ((S ∩ T).card : ℝ) ≤ 4 := by exact_mod_cast card_le_univ (S ∩ T)
  have hs : (999 / 1000 : ℝ) ≤ Real.sqrt (1 - 2 * (p : ℝ)⁻¹) := by
    apply (Real.le_sqrt (by norm_num) (by linarith)).mpr
    norm_num
    linarith
  unfold variableProductPrice coreMeanCap
  apply (div_le_iff₀ (by linarith : 0 < Real.sqrt (1 - 2 * (p : ℝ)⁻¹))).mpr
  nlinarith

theorem constantProductPrice_small (hp40 : 2 ^ 40 ≤ p) (S T : Finset (Fin 4)) :
    constantProductPrice p S T (coreMeanCap p) (coreMeanCap p) (coreMeanCap p) ≤
      if S = T then 1 / 100 else 21 / 10 := by
  have hr := rp_nonneg (p := p)
  have hr1 := rp_small_40 hp40
  have hfac := entangled_factor_times_r_le hp40
  have hfac0 : 0 ≤ (p : ℝ) / Real.sqrt (p - 1) := by positivity
  have hmul : 0 ≤ ((p : ℝ) / Real.sqrt (p - 1)) * rp p := mul_nonneg hfac0 hr
  have hc : (S.card : ℝ) ≤ 4 := by exact_mod_cast card_le_univ S
  have hi : ((S ∩ T).card : ℝ) ≤ 4 := by exact_mod_cast card_le_univ (S ∩ T)
  unfold constantProductPrice coreMeanCap
  rw [← rp_sq]
  split_ifs with he
  · calc
      _ ≤ ((p : ℝ) / Real.sqrt (p - 1)) * (9 * rp p ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hfac0
        nlinarith [mul_nonneg (show 0 ≤ 4 - (S.card : ℝ) by linarith) (sq_nonneg (rp p))]
      _ = 9 * (((p : ℝ) / Real.sqrt (p - 1)) * rp p) * rp p := by ring
      _ ≤ 9 * (1001 / 1000 : ℝ) * (1 / 1000000) := by gcongr
      _ ≤ _ := by norm_num
  · calc
      _ ≤ ((p : ℝ) / Real.sqrt (p - 1)) * ((201 / 100 : ℝ) * rp p + 9 * rp p ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hfac0
        nlinarith [mul_nonneg (show 0 ≤ 4 - ((S ∩ T).card : ℝ) by linarith) (sq_nonneg (rp p))]
      _ = (((p : ℝ) / Real.sqrt (p - 1)) * rp p) * ((201 / 100 : ℝ) + 9 * rp p) := by ring
      _ ≤ (1001 / 1000 : ℝ) * ((201 / 100 : ℝ) + 9 * (1 / 1000000)) := by gcongr
      _ ≤ _ := by norm_num

theorem core_sqrt_density_small (hp40 : 2 ^ 40 ≤ p) :
    Real.sqrt (coreCubeDensity p) ≤ 401 / 100 := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have h := core_density_small_40 hp40
  nlinarith

theorem residualProductPrice_small (hp40 : 2 ^ 40 ≤ p) (S T : Finset (Fin 4)) :
    residualProductPrice p S T (coreMeanCap p) (coreMeanCap p) (coreMeanCap p) ≤
      if S = T then 9 else 5 := by
  have hc := constantProductPrice_small hp40 S T
  have hc0 := constantProductPrice_nonneg (p := p) S T
    (coreMeanCap_nonneg (p := p)) (coreMeanCap_nonneg (p := p)) (coreMeanCap_nonneg (p := p))
  have hv := variableProductPrice_small hp40 S T
  have hv0 := variableProductPrice_nonneg (p := p) S T
    (coreMeanCap_nonneg (p := p)) (coreMeanCap_nonneg (p := p))
  have hd := core_sqrt_density_small hp40
  have hd0 := Real.sqrt_nonneg (coreCubeDensity p)
  have hvs := pow_le_pow_left₀ hv0 hv 2
  have hds := pow_le_pow_left₀ hd0 hd 2
  unfold residualProductPrice productFactor
  by_cases he : S = T
  · simp only [ite_eq_left he] at hc ⊢
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have hcs := pow_le_pow_left₀ hc0 hc 2
    nlinarith
  · simp only [ite_eq_right he] at hc ⊢
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have hcs := pow_le_pow_left₀ hc0 hc 2
    nlinarith

end Sarkozy.PositiveRoots.CoherentFrame
