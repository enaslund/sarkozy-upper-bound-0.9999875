module

public import Sarkozy.SpectralD.Features

/-! Uniform arithmetic bounds for the sixty-three actual coherent features. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Sarkozy.SpectralC Sarkozy.SpectralD

theorem sqrt_entry_le {r N : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 64)
    (hN : N ≤ 43 * r ^ 2) :
    Real.sqrt (N / (1 - r ^ 2) ^ 2) ≤ 7 * r := by
  have hq : r ^ 2 ≤ 1 / 4096 := by nlinarith
  have hd : (63 / 64 : ℝ) ≤ 1 - r ^ 2 := by linarith
  have hd0 : 0 < 1 - r ^ 2 := by linarith
  have hd2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 63 / 64) hd 2
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hd0)]
  calc
    N ≤ 43 * r ^ 2 := hN
    _ ≤ (7 * r) ^ 2 * (63 / 64) ^ 2 := by nlinarith [sq_nonneg r]
    _ ≤ (7 * r) ^ 2 * (1 - r ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hd2 (sq_nonneg _)

variable {p : ℕ}

theorem rp_le (hp : 4096 ≤ p) : rp p ≤ 1 / 64 := by
  have hp' : (4096 : ℝ) ≤ p := by exact_mod_cast hp
  have hs : (64 : ℝ) ≤ Real.sqrt p := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 64)]
    exact Real.sqrt_le_sqrt (by norm_num at hp' ⊢; exact hp')
  simpa [rp, one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 64) hs

theorem q_le_r (hp : 4096 ≤ p) : (p : ℝ)⁻¹ ≤ rp p := by
  rw [← rp_sq]
  have h0 := rp_nonneg (p := p)
  have hr := rp_le hp
  nlinarith

theorem aConst_nonneg (d : ℕ) : 0 ≤ aConst p d := by
  unfold aConst
  split_ifs with h1 h2
  · exact le_rfl
  · positivity
  · have hd : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    exact mul_nonneg (sub_nonneg.mpr hd) rp_nonneg

theorem aConst_le (hp : 4096 ≤ p) {d : ℕ} (hd : d ≤ 6) : aConst p d ≤ 5 * rp p := by
  unfold aConst
  split_ifs with h1 h2
  · exact mul_nonneg (by norm_num) rp_nonneg
  · exact (q_le_r hp).trans (by nlinarith [rp_nonneg (p := p)])
  · have hd' : (d : ℝ) ≤ 6 := by exact_mod_cast hd
    exact mul_le_mul_of_nonneg_right (by linarith) rp_nonneg

theorem star_price (hp : 4096 ≤ p) {k l c d : ℕ}
    (hk : 1 ≤ k) (hk6 : k ≤ 6) (hl : 1 ≤ l) (hl6 : l ≤ 6)
    (hc : c ≤ 6) (hd : d ≤ 6) :
    Real.sqrt (((aConst p d + ((c : ℝ) + ((k : ℝ) - 1) * ((l : ℝ) - 1)) *
      (p : ℝ)⁻¹) ^ 2 + (p : ℝ)⁻¹ * (8 - 1)) / (1 - (p : ℝ)⁻¹) ^ 2) ≤ 7 * rp p := by
  have hr0 := rp_nonneg (p := p)
  have hr := rp_le hp
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk6' : (k : ℝ) ≤ 6 := by exact_mod_cast hk6
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hl6' : (l : ℝ) ≤ 6 := by exact_mod_cast hl6
  have hc' : (c : ℝ) ≤ 6 := by exact_mod_cast hc
  have hcoef0 : 0 ≤ (c : ℝ) + ((k : ℝ) - 1) * ((l : ℝ) - 1) := by positivity
  have hprod : ((k : ℝ) - 1) * ((l : ℝ) - 1) ≤ 25 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 6 - (k : ℝ))
      (by linarith : 0 ≤ (l : ℝ) - 1)]
  have hcoef : (c : ℝ) + ((k : ℝ) - 1) * ((l : ℝ) - 1) ≤ 31 := by linarith
  have hA0 : 0 ≤ aConst p d + ((c : ℝ) + ((k : ℝ) - 1) * ((l : ℝ) - 1)) *
      (p : ℝ)⁻¹ := add_nonneg (aConst_nonneg d) (mul_nonneg hcoef0 (by positivity))
  have hA : aConst p d + ((c : ℝ) + ((k : ℝ) - 1) * ((l : ℝ) - 1)) *
      (p : ℝ)⁻¹ ≤ 6 * rp p := by
    have h1 := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ (p : ℝ)⁻¹)
    rw [← rp_sq] at h1
    rw [← rp_sq]
    nlinarith [aConst_le hp hd, mul_le_mul_of_nonneg_left hr hr0]
  have hsq := pow_le_pow_left₀ hA0 hA 2
  rw [← rp_sq]
  apply sqrt_entry_le hr0 hr
  rw [← rp_sq] at hsq
  nlinarith

theorem vertex_price (hp : 4096 ≤ p) :
    Real.sqrt ((p : ℝ)⁻¹ * (1 + (p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ^ 2) ≤ 7 * rp p := by
  have hr0 := rp_nonneg (p := p)
  have hr := rp_le hp
  rw [← rp_sq]
  apply sqrt_entry_le hr0 hr
  have hq : rp p ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hq (sq_nonneg (rp p))]

theorem vertex_star_out_price (hp : 4096 ≤ p) {k : ℕ} (hk : 1 ≤ k) (hk6 : k ≤ 6) :
    Real.sqrt ((rp p ^ 2 * (1 + ((k : ℝ) - 1) * rp p) ^ 2 +
      (k : ℝ) ^ 2 * (p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ^ 2) ≤ 7 * rp p := by
  have hr0 := rp_nonneg (p := p)
  have hr := rp_le hp
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk6' : (k : ℝ) ≤ 6 := by exact_mod_cast hk6
  have ha0 : 0 ≤ 1 + ((k : ℝ) - 1) * rp p := by positivity
  have ha : 1 + ((k : ℝ) - 1) * rp p ≤ 2 := by
    have := mul_le_mul_of_nonneg_right (by linarith : (k : ℝ) - 1 ≤ 5) hr0
    linarith
  have ha2 := pow_le_pow_left₀ ha0 ha 2
  have hk2 : (k : ℝ) ^ 2 ≤ 36 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left ha2 (sq_nonneg (rp p))
  have h2 := mul_le_mul_of_nonneg_right hk2 (sq_nonneg (rp p))
  rw [← rp_sq]
  apply sqrt_entry_le hr0 hr
  nlinarith

theorem vertex_star_mem_price (hp : 4096 ≤ p) {k : ℕ} (hk : 2 ≤ k) (hk6 : k ≤ 6) :
    Real.sqrt (((p : ℝ)⁻¹ * (((k : ℝ) - 1) * rp p) ^ 2 +
      (aConst p (k - 1) + (p : ℝ)⁻¹) ^ 2) / (1 - (p : ℝ)⁻¹) ^ 2) ≤ 7 * rp p := by
  have hr0 := rp_nonneg (p := p)
  have hr := rp_le hp
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hk6' : (k : ℝ) ≤ 6 := by exact_mod_cast hk6
  have ha0 : 0 ≤ ((k : ℝ) - 1) * rp p := by positivity
  have ha : ((k : ℝ) - 1) * rp p ≤ 1 := by
    have := mul_le_mul_of_nonneg_right (by linarith : (k : ℝ) - 1 ≤ 5) hr0
    linarith
  have ha2 := pow_le_pow_left₀ ha0 ha 2
  have hb0 : 0 ≤ aConst p (k - 1) + (p : ℝ)⁻¹ := by
    exact add_nonneg (aConst_nonneg _) (by positivity)
  have hb : aConst p (k - 1) + (p : ℝ)⁻¹ ≤ 6 * rp p := by
    linarith [aConst_le hp (by omega : k - 1 ≤ 6), q_le_r hp]
  have hb2 := pow_le_pow_left₀ hb0 hb 2
  have h1 := mul_le_mul_of_nonneg_left ha2 (by positivity : 0 ≤ (p : ℝ)⁻¹)
  rw [← rp_sq] at h1 hb2 ⊢
  apply sqrt_entry_le hr0 hr
  nlinarith

end Sarkozy.PositiveRoots.CoherentFrame
