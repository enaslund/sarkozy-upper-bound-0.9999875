module

public import Sarkozy.ProbabilityConstructions
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.MeanInequalities

/-!
# Finite probability moments

The norms in the moment argument are normalized finite expectations. These
lemmas include zero weights and zero functions; no positivity of a function
or full support of the law is built into the definitions.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiniteLaw

variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)

noncomputable def moment (p : ℝ) (f : Ω → ℝ) : ℝ :=
  μ.expect (fun x => |f x| ^ p)

noncomputable def lpNorm (p : ℝ) (f : Ω → ℝ) : ℝ :=
  μ.moment p f ^ (1 / p)

theorem moment_nonneg (p : ℝ) (f : Ω → ℝ) : 0 ≤ μ.moment p f :=
  μ.expect_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _)

theorem lpNorm_nonneg (p : ℝ) (f : Ω → ℝ) : 0 ≤ μ.lpNorm p f :=
  Real.rpow_nonneg (μ.moment_nonneg p f) _

theorem lpNorm_rpow {p : ℝ} (hp : p ≠ 0) (f : Ω → ℝ) :
    μ.lpNorm p f ^ p = μ.moment p f := by
  rw [lpNorm, ← Real.rpow_mul (μ.moment_nonneg p f), one_div_mul_cancel hp,
    Real.rpow_one]

theorem moment_nat (p : ℕ) (f : Ω → ℝ) :
    μ.moment p f = μ.expect (fun x => |f x| ^ p) := by
  simp only [moment, Real.rpow_natCast]

theorem lpNorm_nat_pow {p : ℕ} (hp : p ≠ 0) (f : Ω → ℝ) :
    μ.lpNorm p f ^ p = μ.expect (fun x => |f x| ^ p) := by
  simpa only [Real.rpow_natCast, moment_nat] using
    μ.lpNorm_rpow (by exact_mod_cast hp : (p : ℝ) ≠ 0) f

theorem expect_sum {I : Type*} (s : Finset I) (f : I → Ω → ℝ) :
    μ.expect (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, μ.expect (f i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem moment_const_mul {p : ℝ} (c : ℝ) (f : Ω → ℝ) :
    μ.moment p (fun x => c * f x) = |c| ^ p * μ.moment p f := by
  simp only [moment, abs_mul, Real.mul_rpow (abs_nonneg c) (abs_nonneg (f _))]
  exact μ.expect_const_mul _ _

theorem lpNorm_const_mul {p : ℝ} (hp : p ≠ 0) (c : ℝ) (f : Ω → ℝ) :
    μ.lpNorm p (fun x => c * f x) = |c| * μ.lpNorm p f := by
  rw [lpNorm, moment_const_mul,
    Real.mul_rpow (Real.rpow_nonneg (abs_nonneg _) _) (μ.moment_nonneg _ _),
    ← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel hp, Real.rpow_one]
  rfl

theorem expect_rpow_le {p : ℝ} (hp : 1 ≤ p) {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) :
    μ.expect f ^ p ≤ μ.expect (fun x => f x ^ p) :=
  Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ μ.weight f
    (fun x _ => μ.nonneg x) μ.total (fun x _ => hf x) hp

theorem lpNorm_mono {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (f : Ω → ℝ) :
    μ.lpNorm p f ≤ μ.lpNorm q f := by
  have hq : 0 < q := hp.trans_le hpq
  have hratio : 1 ≤ q / p := (le_div_iff₀ hp).2 (by simpa using hpq)
  have h := μ.expect_rpow_le hratio (fun x => Real.rpow_nonneg (abs_nonneg (f x)) p)
  have he (x : Ω) : (|f x| ^ p) ^ (q / p) = |f x| ^ q := by
    rw [← Real.rpow_mul (abs_nonneg _)]
    congr 1
    field_simp
  simp only [he] at h
  apply (Real.rpow_le_rpow_iff (μ.lpNorm_nonneg p f) (μ.lpNorm_nonneg q f) hq).mp
  rw [μ.lpNorm_rpow hq.ne' f]
  change (μ.moment p f ^ (1 / p)) ^ q ≤ μ.moment q f
  rw [← Real.rpow_mul (μ.moment_nonneg p f)]
  rw [show 1 / p * q = q / p by ring]
  exact h

theorem abs_expect_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (f : Ω → ℝ) :
    |μ.expect f| ≤ μ.lpNorm p f := by
  have h := μ.lpNorm_mono (by norm_num : (0 : ℝ) < 1) hp f
  simpa only [lpNorm, moment, one_div_one, Real.rpow_one] using
    (μ.abs_expect_le f).trans (by simpa only [lpNorm, moment, one_div_one,
      Real.rpow_one] using h)

end Sarkozy.FiniteLaw
