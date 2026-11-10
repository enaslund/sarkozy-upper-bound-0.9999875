module

public import Sarkozy.Restoration
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite probability laws and the restoration argument

A law is an ordinary nonnegative, normalized weight on a finite set. All
expectations below are literal finite sums. In particular, the comparison and
variance inequalities are proved from those sums, not included as fields in
the definition of a law.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)

noncomputable def expect (f : Ω → ℝ) : ℝ := ∑ ω, μ.weight ω * f ω

theorem expect_congr {f g : Ω → ℝ} (h : ∀ ω, f ω = g ω) : μ.expect f = μ.expect g := by
  exact Finset.sum_congr rfl (fun ω _ => congrArg (μ.weight ω * ·) (h ω))

@[simp] theorem expect_const (c : ℝ) : μ.expect (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, μ.total]

theorem expect_add (f g : Ω → ℝ) :
    μ.expect (fun ω => f ω + g ω) = μ.expect f + μ.expect g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (f g : Ω → ℝ) :
    μ.expect (fun ω => f ω - g ω) = μ.expect f - μ.expect g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_const_mul (c : ℝ) (f : Ω → ℝ) :
    μ.expect (fun ω => c * f ω) = c * μ.expect f := by
  simp [expect, Finset.mul_sum, mul_left_comm]

theorem expect_mul_const (f : Ω → ℝ) (c : ℝ) :
    μ.expect (fun ω => f ω * c) = μ.expect f * c := by
  simp only [expect, ← mul_assoc, Finset.sum_mul]

theorem expect_nonneg {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ μ.expect f :=
  Finset.sum_nonneg (fun ω _ => mul_nonneg (μ.nonneg ω) (hf ω))

theorem expect_mono {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) : μ.expect f ≤ μ.expect g :=
  Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (μ.nonneg ω))

theorem expect_le_const {f : Ω → ℝ} {C : ℝ} (h : ∀ ω, f ω ≤ C) : μ.expect f ≤ C := by
  simpa only [expect_const] using μ.expect_mono h

theorem const_le_expect {f : Ω → ℝ} {c : ℝ} (h : ∀ ω, c ≤ f ω) : c ≤ μ.expect f := by
  simpa only [expect_const] using μ.expect_mono h

theorem abs_expect_le (f : Ω → ℝ) : |μ.expect f| ≤ μ.expect (fun ω => |f ω|) := by
  calc
    _ ≤ ∑ ω, |μ.weight ω * f ω| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul, abs_of_nonneg (μ.nonneg _), expect]

theorem abs_expect_le_const {f : Ω → ℝ} {C : ℝ} (h : ∀ ω, |f ω| ≤ C) :
    |μ.expect f| ≤ C := (μ.abs_expect_le f).trans (μ.expect_le_const h)

theorem second_moment_nonneg (f : Ω → ℝ) : 0 ≤ μ.expect (fun ω => f ω ^ 2) :=
  μ.expect_nonneg (fun ω => sq_nonneg (f ω))

/-- Cauchy--Schwarz for the finite weighted expectation, including zero weights. -/
theorem cauchy_schwarz_sq (f g : Ω → ℝ) :
    μ.expect (fun ω => f ω * g ω) ^ 2 ≤
      μ.expect (fun ω => f ω ^ 2) * μ.expect (fun ω => g ω ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun ω => Real.sqrt (μ.weight ω) * f ω)
    (fun ω => Real.sqrt (μ.weight ω) * g ω)
  have hc (ω : Ω) :
      (Real.sqrt (μ.weight ω) * f ω) * (Real.sqrt (μ.weight ω) * g ω) =
        μ.weight ω * (f ω * g ω) := by
    calc
      _ = Real.sqrt (μ.weight ω) ^ 2 * (f ω * g ω) := by ring
      _ = _ := by rw [Real.sq_sqrt (μ.nonneg ω)]
  simpa only [hc, mul_pow, Real.sq_sqrt (μ.nonneg _), expect] using h

theorem abs_expect_mul_le (f g : Ω → ℝ) :
    |μ.expect (fun ω => f ω * g ω)| ≤
      Real.sqrt (μ.expect (fun ω => f ω ^ 2)) *
        Real.sqrt (μ.expect (fun ω => g ω ^ 2)) := by
  have h := Real.abs_le_sqrt (μ.cauchy_schwarz_sq f g)
  rwa [Real.sqrt_mul (μ.second_moment_nonneg f)] at h

theorem expect_sq_sub_mean (f : Ω → ℝ) :
    μ.expect (fun ω => (f ω - μ.expect f) ^ 2) =
      μ.expect (fun ω => f ω ^ 2) - μ.expect f ^ 2 := by
  calc
    _ = μ.expect (fun ω => (f ω ^ 2 - (2 * μ.expect f) * f ω) + μ.expect f ^ 2) :=
      μ.expect_congr (fun ω => by ring)
    _ = _ := by rw [expect_add, expect_sub, expect_const_mul, expect_const]; ring

theorem mean_sq_le_second_moment (f : Ω → ℝ) :
    μ.expect f ^ 2 ≤ μ.expect (fun ω => f ω ^ 2) := by
  have h := μ.second_moment_nonneg (fun ω => f ω - μ.expect f)
  rw [expect_sq_sub_mean] at h
  linarith

/-- Squared L² distance of a density w from the constant density one. -/
noncomputable def chiSquare (w : Ω → ℝ) : ℝ := μ.expect (fun ω => (w ω - 1) ^ 2)

theorem chiSquare_nonneg (w : Ω → ℝ) : 0 ≤ μ.chiSquare w :=
  μ.second_moment_nonneg _

/-- Centering removes the constant part of a normalized density. -/
theorem reweighted_mean_identity (w f : Ω → ℝ) (hw : μ.expect w = 1) :
    μ.expect (fun ω => w ω * f ω) = μ.expect f +
      μ.expect (fun ω => (w ω - 1) * (f ω - μ.expect f)) := by
  have hcenter : μ.expect (fun ω => w ω - 1) = 0 := by
    rw [expect_sub, expect_const, hw]; ring
  calc
    _ = μ.expect (fun ω => (f ω + (w ω - 1) * (f ω - μ.expect f)) +
        μ.expect f * (w ω - 1)) := μ.expect_congr (fun ω => by ring)
    _ = _ := by rw [expect_add, expect_add, expect_const_mul, hcenter]; ring

/-- The centered chi-square comparison, derived from Cauchy--Schwarz. -/
theorem reweighted_mean_le (w f : Ω → ℝ) (hw : μ.expect w = 1) :
    μ.expect (fun ω => w ω * f ω) ≤ μ.expect f +
      Real.sqrt (μ.chiSquare w) *
        Real.sqrt (μ.expect (fun ω => f ω ^ 2) - μ.expect f ^ 2) := by
  rw [μ.reweighted_mean_identity w f hw]
  apply add_le_add le_rfl
  have h := μ.abs_expect_mul_le (fun ω => w ω - 1) (fun ω => f ω - μ.expect f)
  rw [expect_sq_sub_mean] at h
  exact (le_abs_self _).trans h

theorem reweighted_mean_le_of_moment_bounds (w f : Ω → ℝ) (hw : μ.expect w = 1)
    {C χ : ℝ} (hχ : μ.chiSquare w ≤ χ)
    (hsecond : μ.expect (fun ω => f ω ^ 2) ≤ C ^ 2) :
    μ.expect (fun ω => w ω * f ω) ≤
      μ.expect f + Real.sqrt χ * Real.sqrt (C ^ 2 - μ.expect f ^ 2) := by
  apply (μ.reweighted_mean_le w f hw).trans
  apply add_le_add le_rfl
  exact mul_le_mul (Real.sqrt_le_sqrt hχ)
    (Real.sqrt_le_sqrt (sub_le_sub_right hsecond _))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- Pointwise domination of a density controls every nonnegative test function. -/
theorem dominated_mean {w f : Ω → ℝ} {M : ℝ}
    (hf : ∀ ω, 0 ≤ f ω) (hw : ∀ ω, w ω ≤ M) :
    μ.expect (fun ω => w ω * f ω) ≤ M * μ.expect f := by
  simpa only [expect_const_mul] using
    μ.expect_mono (fun ω => mul_le_mul_of_nonneg_right (hw ω) (hf ω))

/-- The paper's F₂ restoration bound from finite probability data.

The caller supplies a root-mean lower bound, a second-moment upper bound,
and density domination. Positivity, variance control, and the centered
comparison are proved here rather than postulated.
-/
theorem restoration_from_moments (w f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (hw : μ.expect w = 1)
    {C h M χ : ℝ} (hM : 0 < M) (hdom : ∀ ω, w ω ≤ M)
    (hχ : μ.chiSquare w ≤ χ) (hsecond : μ.expect (fun ω => f ω ^ 2) ≤ C ^ 2)
    (hroot : max 0 (1 - (C - 1) * h) ≤ μ.expect (fun ω => w ω * f ω)) :
    restoration C h M χ ≤ μ.expect f := by
  apply restoration_le_mean (μ.expect_nonneg hf) hM ((μ.chiSquare_nonneg w).trans hχ)
  · exact sub_nonneg.mpr ((μ.mean_sq_le_second_moment f).trans hsecond)
  · simpa only [mul_comm] using hroot.trans (μ.dominated_mean hf hdom)
  · exact hroot.trans (μ.reweighted_mean_le_of_moment_bounds w f hw hχ hsecond)

end FiniteLaw
end Sarkozy
