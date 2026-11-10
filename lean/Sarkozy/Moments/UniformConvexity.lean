module

public import Sarkozy.Moments.NormDerivatives

/-!
# Uniform convexity on a finite probability space

For nonnegative f and 1 < p ≤ 2, the square of its Lp norm controls the
square of its mean plus (p - 1) times the squared Lp norm of its centered
part. Zero values of f are included by continuity at the endpoint.
-/

@[expose] public section

open scoped BigOperators
open Set

namespace Sarkozy

theorem second_derivative_endpoint_bound (F F' F'' : ℝ → ℝ) (c : ℝ)
    (hcont : ContinuousOn F (Icc 0 1))
    (hfirst : ∀ t ∈ Ioo 0 1, HasDerivAt F (F' t) t)
    (hsecond : ∀ t ∈ Ioo 0 1, HasDerivAt F' (F'' t) t)
    (hlower : ∀ t ∈ Ioo 0 1, 2 * c ≤ F'' t)
    (hzero : HasDerivAt F 0 0) : F 0 + c ≤ F 1 := by
  let G : ℝ → ℝ := fun t => F t - c * t ^ 2
  let G' : ℝ → ℝ := fun t => F' t - 2 * c * t
  let G'' : ℝ → ℝ := fun t => F'' t - 2 * c
  have hGcont : ContinuousOn G (Icc 0 1) :=
    hcont.sub (continuous_const.mul (continuous_id.pow 2)).continuousOn
  have hGfirst (t : ℝ) (ht : t ∈ Ioo 0 1) : HasDerivAt G (G' t) t := by
    have hh := (hfirst t ht).fun_sub (((hasDerivAt_id t).fun_pow 2).const_mul c)
    dsimp only [id_eq] at hh
    dsimp only [G, G']
    convert hh using 1
    ring
  have hGsecond (t : ℝ) (ht : t ∈ Ioo 0 1) : HasDerivAt G' (G'' t) t := by
    have hh := (hsecond t ht).fun_sub ((hasDerivAt_id t).const_mul (2 * c))
    convert hh using 1
    dsimp [G'']
    ring
  have hconv : ConvexOn ℝ (Icc 0 1) G := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1) hGcont
      (f' := G') (f'' := G'')
    · intro t ht
      exact (hGfirst t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
    · intro t ht
      exact (hGsecond t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
    · intro t ht
      exact sub_nonneg.mpr (hlower t (by simpa only [interior_Icc] using ht))
  have hGzero : HasDerivAt G 0 0 := by
    have hh := hzero.fun_sub (((hasDerivAt_id (0 : ℝ)).fun_pow 2).const_mul c)
    simpa only [G, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_zero,
      sub_zero, zero_mul] using hh
  have hs := hconv.le_slope_of_hasDerivAt (x := 0) (y := 1)
    (by norm_num) (by norm_num) (by norm_num) hGzero
  norm_num [slope_def_field, G] at hs
  linarith

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)

theorem continuous_affineNormSq {p : ℝ} (hp : 0 ≤ p) (g h : Ω → ℝ) :
    Continuous (μ.affineNormSq p g h) := by
  have hA : Continuous (μ.affineMoment p g h) := by
    unfold affineMoment expect
    apply continuous_finsetSum
    intro x _
    exact continuous_const.mul
      ((continuous_const.add (continuous_id.mul continuous_const)).rpow_const (fun _ => Or.inr hp))
  exact hA.rpow_const (fun _ => Or.inr (div_nonneg (by norm_num) hp))

/-- The exact finite-probability uniform-convexity inequality used in the paper. -/
theorem lpNorm_uniform_convexity {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) :
    μ.expect f ^ 2 + (p - 1) * μ.lpNorm p (fun x => f x - μ.expect f) ^ 2 ≤
      μ.lpNorm p f ^ 2 := by
  have hp0 : 0 < p := by linarith
  by_cases hz : μ.expect f = 0
  · simp only [hz, sub_zero, zero_pow (by omega : (2 : ℕ) ≠ 0), zero_add]
    have hh := mul_le_mul_of_nonneg_right (by linarith : p - 1 ≤ 1)
      (sq_nonneg (μ.lpNorm p f))
    simpa only [one_mul] using hh
  have hm : 0 < μ.expect f := lt_of_le_of_ne (μ.expect_nonneg hf) (Ne.symm hz)
  let m := μ.expect f
  let h : Ω → ℝ := fun x => f x - m
  let F := μ.affineNormSq p (fun _ => m) h
  let F' := μ.affineNormSqDeriv p (fun _ => m) h
  let F'' := μ.affineNormSqDeriv2 p (fun _ => m) h
  have hpos (t : ℝ) (ht : t ∈ Ioo 0 1) (x : Ω) : 0 < m + t * h x := by
    have hleft := mul_pos (sub_pos.mpr ht.2) hm
    have hright := mul_nonneg ht.1.le (hf x)
    dsimp only [h]
    nlinarith
  have hdir : μ.affineMomentDirection p (fun _ => m) h 0 = 0 := by
    simp only [affineMomentDirection, zero_mul, add_zero]
    rw [μ.expect_const_mul]
    dsimp only [h]
    rw [μ.expect_sub, μ.expect_const]
    simp only [m, sub_self, mul_zero]
  have hFzero : HasDerivAt F 0 0 := by
    have hh := μ.hasDerivAt_affineNormSq hp0.ne' (fun _ => m) h
      (t := 0) (fun _ => by simpa only [zero_mul, add_zero] using hm)
    simpa only [affineNormSqDeriv, hdir, mul_zero] using hh
  have hF0 : F 0 = m ^ 2 := by
    dsimp only [F, affineNormSq, affineMoment]
    simp only [zero_mul, add_zero, μ.expect_const]
    rw [← Real.rpow_mul hm.le, show p * (2 / p) = 2 by field_simp]
    exact Real.rpow_two m
  have hF1 : F 1 = μ.lpNorm p f ^ 2 := by
    rw [μ.lpNorm_sq_eq_moment_rpow]
    dsimp only [F, affineNormSq, affineMoment, h, moment]
    simp only [one_mul, add_sub_cancel, abs_of_nonneg (hf _)]
  have hend := second_derivative_endpoint_bound F F' F'' ((p - 1) * μ.lpNorm p h ^ 2)
    (μ.continuous_affineNormSq hp0.le _ _).continuousOn
    (fun t ht => μ.hasDerivAt_affineNormSq hp0.ne' _ _ (hpos t ht))
    (fun t ht => μ.hasDerivAt_affineNormSqDeriv hp0.ne' _ _ (hpos t ht))
    (fun t ht => by
      have hh := μ.affineNormSqDeriv2_lower hp hp2 _ _ (hpos t ht)
      simpa only [mul_assoc] using hh)
    hFzero
  simpa only [hF0, hF1] using hend

end FiniteLaw
end Sarkozy
