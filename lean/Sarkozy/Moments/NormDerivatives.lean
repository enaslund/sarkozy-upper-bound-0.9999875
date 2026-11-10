module

public import Sarkozy.Moments.Interpolation
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Convex.Deriv

/-!
# Derivatives of the square of a finite Lp norm

The computations are made on positive affine lines. Endpoint continuity will
allow zero values in the final uniform-convexity inequality.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiniteLaw

variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)

theorem hasDerivAt_expect {f : Ω → ℝ → ℝ} {f' : Ω → ℝ} {t : ℝ}
    (hf : ∀ x, HasDerivAt (f x) (f' x) t) :
    HasDerivAt (fun s => μ.expect (fun x => f x s)) (μ.expect f') t := by
  have hh := HasDerivAt.sum (u := Finset.univ) (fun x _ => (hf x).const_mul (μ.weight x))
  convert hh using 1
  · funext s
    exact (Finset.sum_apply s Finset.univ (fun x y => μ.weight x * f x y)).symm
  · rfl

noncomputable def affineMoment (p : ℝ) (g h : Ω → ℝ) (t : ℝ) : ℝ :=
  μ.expect (fun x => (g x + t * h x) ^ p)

noncomputable def affineMomentDirection (p : ℝ) (g h : Ω → ℝ) (t : ℝ) : ℝ :=
  μ.expect (fun x => (g x + t * h x) ^ (p - 1) * h x)

noncomputable def affineMomentHessian (p : ℝ) (g h : Ω → ℝ) (t : ℝ) : ℝ :=
  μ.expect (fun x => (g x + t * h x) ^ (p - 2) * h x ^ 2)

noncomputable def affineNormSq (p : ℝ) (g h : Ω → ℝ) (t : ℝ) : ℝ :=
  μ.affineMoment p g h t ^ (2 / p)

noncomputable def affineNormSqDeriv (p : ℝ) (g h : Ω → ℝ) (t : ℝ) : ℝ :=
  2 * μ.affineMoment p g h t ^ (2 / p - 1) * μ.affineMomentDirection p g h t

noncomputable def affineNormSqDeriv2 (p : ℝ) (g h : Ω → ℝ) (t : ℝ) : ℝ :=
  2 * (2 - p) * μ.affineMoment p g h t ^ (2 / p - 2) *
      μ.affineMomentDirection p g h t ^ 2 +
    2 * (p - 1) * μ.affineMoment p g h t ^ (2 / p - 1) * μ.affineMomentHessian p g h t

omit [Fintype Ω] in
theorem hasDerivAt_affine (g h : Ω → ℝ) (t : ℝ) (x : Ω) :
    HasDerivAt (fun s => g x + s * h x) (h x) t := by
  simpa only [zero_add, one_mul, id_eq, Pi.add_def] using
    (hasDerivAt_const t (g x)).add ((hasDerivAt_id t).mul_const (h x))

theorem affineMoment_pos (p : ℝ) (g h : Ω → ℝ) {t : ℝ}
    (hpos : ∀ x, 0 < g x + t * h x) : 0 < μ.affineMoment p g h t :=
  μ.expect_pos_of_pos (fun x => Real.rpow_pos_of_pos (hpos x) p)

theorem hasDerivAt_affineMoment (p : ℝ) (g h : Ω → ℝ) {t : ℝ}
    (hpos : ∀ x, 0 < g x + t * h x) :
    HasDerivAt (μ.affineMoment p g h) (p * μ.affineMomentDirection p g h t) t := by
  unfold affineMoment
  have hh := μ.hasDerivAt_expect (fun x =>
    (hasDerivAt_affine g h t x).rpow_const (p := p) (Or.inl (hpos x).ne'))
  convert hh using 1
  rw [affineMomentDirection, ← μ.expect_const_mul]
  apply μ.expect_congr
  intro x
  ring

theorem hasDerivAt_affineMomentDirection (p : ℝ) (g h : Ω → ℝ) {t : ℝ}
    (hpos : ∀ x, 0 < g x + t * h x) :
    HasDerivAt (μ.affineMomentDirection p g h)
      ((p - 1) * μ.affineMomentHessian p g h t) t := by
  unfold affineMomentDirection
  have hh := μ.hasDerivAt_expect (fun x =>
    ((hasDerivAt_affine g h t x).rpow_const (p := p - 1) (Or.inl (hpos x).ne')).mul_const (h x))
  convert hh using 1
  rw [affineMomentHessian, ← μ.expect_const_mul]
  apply μ.expect_congr
  intro x
  rw [show p - 1 - 1 = p - 2 by ring]
  ring

theorem hasDerivAt_affineNormSq {p : ℝ} (hp : p ≠ 0) (g h : Ω → ℝ) {t : ℝ}
    (hpos : ∀ x, 0 < g x + t * h x) :
    HasDerivAt (μ.affineNormSq p g h) (μ.affineNormSqDeriv p g h t) t := by
  unfold affineNormSq
  have hh := (μ.hasDerivAt_affineMoment p g h hpos).rpow_const
    (p := 2 / p) (Or.inl (μ.affineMoment_pos p g h hpos).ne')
  convert hh using 1
  unfold affineNormSqDeriv
  field_simp

theorem hasDerivAt_affineNormSqDeriv {p : ℝ} (hp : p ≠ 0) (g h : Ω → ℝ) {t : ℝ}
    (hpos : ∀ x, 0 < g x + t * h x) :
    HasDerivAt (μ.affineNormSqDeriv p g h) (μ.affineNormSqDeriv2 p g h t) t := by
  unfold affineNormSqDeriv
  have hh := (((μ.hasDerivAt_affineMoment p g h hpos).rpow_const
      (p := 2 / p - 1) (Or.inl (μ.affineMoment_pos p g h hpos).ne')).const_mul 2).mul
    (μ.hasDerivAt_affineMomentDirection p g h hpos)
  convert hh using 1
  unfold affineNormSqDeriv2
  rw [show 2 / p - 1 - 1 = 2 / p - 2 by ring]
  field_simp

/-- The exact dimension-free Hessian lower bound. -/
theorem affineNormSqDeriv2_lower {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (g h : Ω → ℝ) {t : ℝ} (hpos : ∀ x, 0 < g x + t * h x) :
    2 * (p - 1) * μ.lpNorm p h ^ 2 ≤ μ.affineNormSqDeriv2 p g h t := by
  have hr := μ.reverse_holder_hessian (by linarith : 0 < p) hp2
    (fun x => g x + t * h x) h hpos
  have hh := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2 * (p - 1))
  have hfirst : 0 ≤ 2 * (2 - p) * μ.affineMoment p g h t ^ (2 / p - 2) *
      μ.affineMomentDirection p g h t ^ 2 := by
    apply mul_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hp2))
        (Real.rpow_nonneg (μ.affineMoment_pos p g h hpos).le _)
    · exact sq_nonneg _
  unfold affineNormSqDeriv2
  change 2 * (p - 1) * μ.lpNorm p h ^ 2 ≤
    2 * (p - 1) * (μ.affineMoment p g h t ^ (2 / p - 1) * μ.affineMomentHessian p g h t) at hh
  linarith

end Sarkozy.FiniteLaw
