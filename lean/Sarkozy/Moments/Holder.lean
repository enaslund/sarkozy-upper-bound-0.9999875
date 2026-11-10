module

public import Sarkozy.Moments.Basic

/-!
# Finite weighted Hölder inequality

The exponent may vary between factors. The proof uses weighted AM–GM on
normalized functions and explicitly handles a zero norm using the support of
the probability law.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiniteLaw

variable {Ω I : Type*} [Fintype Ω] [Fintype I] (μ : FiniteLaw Ω)

theorem eq_zero_on_support_of_lpNorm_eq_zero {p : ℝ} (hp : 0 < p)
    {f : Ω → ℝ} (h : μ.lpNorm p f = 0) {x : Ω} (hx : μ.weight x ≠ 0) : f x = 0 := by
  have hm := μ.lpNorm_rpow hp.ne' f
  rw [h, Real.zero_rpow hp.ne'] at hm
  have hsum : ∑ y, μ.weight y * |f y| ^ p = 0 := hm.symm
  have hterm : μ.weight x * |f x| ^ p = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ => mul_nonneg (μ.nonneg y) (Real.rpow_nonneg (abs_nonneg _) _))).mp
        hsum x (Finset.mem_univ _)
  have hr : |f x| ^ p = 0 := (mul_eq_zero.mp hterm).resolve_left hx
  exact abs_eq_zero.mp ((Real.rpow_eq_zero_iff_of_nonneg (abs_nonneg _)).mp hr).1

theorem expect_prod_eq_zero_of_lpNorm_eq_zero {p : ℝ} (hp : 0 < p)
    (f : I → Ω → ℝ) (i : I) (hi : μ.lpNorm p (f i) = 0) :
    μ.expect (fun x => ∏ j, f j x) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro x _
  change μ.weight x * (∏ j, f j x) = 0
  by_cases hx : μ.weight x = 0
  · simp only [hx, zero_mul]
  · have hz := μ.eq_zero_on_support_of_lpNorm_eq_zero hp hi hx
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hz, mul_zero]

theorem expect_prod_le_one_of_moments (p : I → ℝ) (hp : ∀ i, 0 < p i)
    (hsum : ∑ i, 1 / p i = 1) (f : I → Ω → ℝ)
    (hf : ∀ i x, 0 ≤ f i x) (hm : ∀ i, μ.expect (fun x => f i x ^ p i) ≤ 1) :
    μ.expect (fun x => ∏ i, f i x) ≤ 1 := by
  have hpoint (x : Ω) : ∏ i, f i x ≤ ∑ i, (1 / p i) * f i x ^ p i := by
    have h := Real.geom_mean_le_arith_mean_weighted Finset.univ
      (fun i => 1 / p i) (fun i => f i x ^ p i)
      (fun i _ => one_div_nonneg.mpr (hp i).le) hsum
      (fun i _ => Real.rpow_nonneg (hf i x) _)
    have he (i : I) : (f i x ^ p i) ^ (1 / p i) = f i x := by
      rw [← Real.rpow_mul (hf i x), mul_one_div_cancel (hp i).ne', Real.rpow_one]
    simpa only [he] using h
  apply (μ.expect_mono hpoint).trans
  rw [μ.expect_sum]
  simp only [μ.expect_const_mul]
  calc
    ∑ i, (1 / p i) * μ.expect (fun x => f i x ^ p i) ≤ ∑ i, 1 / p i := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hm i)
        (one_div_nonneg.mpr (hp i).le)
    _ = 1 := hsum

/-- Hölder for a finite probability law and any positive conjugate family of
exponents. Zero weights and zero norms are allowed. -/
theorem abs_expect_prod_le_lpNorm (p : I → ℝ) (hp : ∀ i, 0 < p i)
    (hsum : ∑ i, 1 / p i = 1) (f : I → Ω → ℝ) :
    |μ.expect (fun x => ∏ i, f i x)| ≤ ∏ i, μ.lpNorm (p i) (f i) := by
  classical
  by_cases hz : ∃ i, μ.lpNorm (p i) (f i) = 0
  · obtain ⟨i, hi⟩ := hz
    rw [μ.expect_prod_eq_zero_of_lpNorm_eq_zero (hp i) f i hi, abs_zero,
      Finset.prod_eq_zero (Finset.mem_univ i) hi]
  have hpos (i : I) : 0 < μ.lpNorm (p i) (f i) :=
    lt_of_le_of_ne (μ.lpNorm_nonneg _ _) (fun h => hz ⟨i, h.symm⟩)
  let g : I → Ω → ℝ := fun i x => |f i x| / μ.lpNorm (p i) (f i)
  have hg (i : I) (x : Ω) : 0 ≤ g i x := div_nonneg (abs_nonneg _) (hpos i).le
  have hgm (i : I) : μ.expect (fun x => g i x ^ p i) ≤ 1 := by
    have hden := μ.lpNorm_rpow (hp i).ne' (f i)
    have he : μ.expect (fun x => g i x ^ p i) =
        μ.moment (p i) (f i) / μ.lpNorm (p i) (f i) ^ p i := by
      calc
        _ = μ.expect (fun x => |f i x| ^ p i / μ.lpNorm (p i) (f i) ^ p i) :=
          μ.expect_congr (fun x => Real.div_rpow (abs_nonneg (f i x)) (hpos i).le (p i))
        _ = _ := by
          simp only [div_eq_mul_inv]
          exact μ.expect_mul_const _ _
    rw [he, ← hden, div_self (Real.rpow_pos_of_pos (hpos i) _).ne']
  have hn := μ.expect_prod_le_one_of_moments p hp hsum g hg hgm
  have he (x : Ω) : ∏ i, |f i x| = (∏ i, μ.lpNorm (p i) (f i)) * ∏ i, g i x := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    dsimp only [g]
    field_simp [(hpos i).ne']
  calc
    |μ.expect (fun x => ∏ i, f i x)| ≤ μ.expect (fun x => ∏ i, |f i x|) := by
      simpa only [Finset.abs_prod] using μ.abs_expect_le (fun x => ∏ i, f i x)
    _ = (∏ i, μ.lpNorm (p i) (f i)) * μ.expect (fun x => ∏ i, g i x) := by
      simp only [he, μ.expect_const_mul]
    _ ≤ ∏ i, μ.lpNorm (p i) (f i) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hn
        (Finset.prod_nonneg (fun i _ => μ.lpNorm_nonneg _ _))

end Sarkozy.FiniteLaw
