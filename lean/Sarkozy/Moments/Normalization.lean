module

public import Sarkozy.Moments.Mixed

/-!
# Reducing mixed bounds to nonnegative unit-norm inputs

The uniform measure has full support. A zero uniform Lp norm therefore makes
the whole corresponding factor zero. All remaining factors can be normalized
without a limiting argument.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy
namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)

theorem lpNorm_abs (p : ℝ) (f : Ω → ℝ) : μ.lpNorm p (fun x => |f x|) = μ.lpNorm p f := by
  simp only [lpNorm, moment, abs_abs]

theorem lpNorm_le_one_of_moment_le_one {p : ℝ} (hp : 0 < p) {f : Ω → ℝ}
    (h : μ.moment p f ≤ 1) : μ.lpNorm p f ≤ 1 :=
  Real.rpow_le_one (μ.moment_nonneg _ _) h (one_div_nonneg.mpr hp.le)

theorem moment_eq_one_of_lpNorm_eq_one {p : ℝ} (hp : p ≠ 0) {f : Ω → ℝ}
    (h : μ.lpNorm p f = 1) : μ.moment p f = 1 := by
  rw [← μ.lpNorm_rpow hp f, h, Real.one_rpow]

theorem lpNorm_normalize {p : ℝ} (hp : p ≠ 0) {f : Ω → ℝ}
    (hn : 0 < μ.lpNorm p f) :
    μ.lpNorm p (fun x => |f x| / μ.lpNorm p f) = 1 := by
  have he : (fun x => |f x| / μ.lpNorm p f) =
      (fun x => (μ.lpNorm p f)⁻¹ * |f x|) := by ext x; ring
  rw [he, μ.lpNorm_const_mul hp, μ.lpNorm_abs, abs_of_nonneg (inv_nonneg.mpr hn.le),
    inv_mul_cancel₀ hn.ne']

theorem uniform_function_eq_zero_of_lpNorm_eq_zero [Nonempty Ω] {p : ℝ} (hp : 0 < p)
    {f : Ω → ℝ} (h : (uniform Ω).lpNorm p f = 0) (x : Ω) : f x = 0 := by
  apply (uniform Ω).eq_zero_on_support_of_lpNorm_eq_zero hp h
  change (Fintype.card Ω : ℝ)⁻¹ ≠ 0
  exact inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)

end FiniteLaw

theorem mixedLpBound_of_normalized {V X : Type*} [Fintype V] [DecidableEq V]
    [Fintype X] [Nonempty X] (μ : FiniteLaw (V → X)) {p C : ℝ} (hp : 0 < p)
    (h : ∀ f : V → X → ℝ, (∀ v x, 0 ≤ f v x) →
      (∀ v, (FiniteLaw.uniform X).lpNorm p (f v) = 1) →
      μ.expect (fun z => ∏ v, f v (z v)) ≤ C) : MixedLpBound μ p C := by
  classical
  intro f
  by_cases hz : ∃ v, (FiniteLaw.uniform X).lpNorm p (f v) = 0
  · obtain ⟨v, hv⟩ := hz
    have hzero (z : V → X) : ∏ i, f i (z i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ v)
        (FiniteLaw.uniform_function_eq_zero_of_lpNorm_eq_zero hp hv (z v))
    have hnzero : (∏ i, (FiniteLaw.uniform X).lpNorm p (f i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ v) hv
    simp only [hzero, FiniteLaw.expect_const, abs_zero, hnzero, mul_zero, le_refl]
  have hpos (v : V) : 0 < (FiniteLaw.uniform X).lpNorm p (f v) :=
    lt_of_le_of_ne ((FiniteLaw.uniform X).lpNorm_nonneg _ _) (fun h => hz ⟨v, h.symm⟩)
  let g : V → X → ℝ := fun v x => |f v x| / (FiniteLaw.uniform X).lpNorm p (f v)
  have hg := h g (fun v x => div_nonneg (abs_nonneg _) (hpos v).le)
    (fun v => (FiniteLaw.uniform X).lpNorm_normalize hp.ne' (hpos v))
  have he (z : V → X) : ∏ v, |f v (z v)| =
      (∏ v, (FiniteLaw.uniform X).lpNorm p (f v)) * ∏ v, g v (z v) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v _
    dsimp only [g]
    field_simp [(hpos v).ne']
  calc
    |μ.expect (fun z => ∏ v, f v (z v))| ≤ μ.expect (fun z => ∏ v, |f v (z v)|) := by
      simpa only [Finset.abs_prod] using μ.abs_expect_le (fun z => ∏ v, f v (z v))
    _ = (∏ v, (FiniteLaw.uniform X).lpNorm p (f v)) * μ.expect (fun z => ∏ v, g v (z v)) := by
      simp only [he, μ.expect_const_mul]
    _ ≤ (∏ v, (FiniteLaw.uniform X).lpNorm p (f v)) * C :=
      mul_le_mul_of_nonneg_left hg
        (Finset.prod_nonneg (fun _ _ => (FiniteLaw.uniform X).lpNorm_nonneg _ _))
    _ = C * ∏ v, (FiniteLaw.uniform X).lpNorm p (f v) := mul_comm _ _

end Sarkozy
