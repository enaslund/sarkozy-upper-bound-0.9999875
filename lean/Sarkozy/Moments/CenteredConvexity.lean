module

public import Sarkozy.Moments.Centered
public import Sarkozy.Moments.UniformConvexity

/-!
# Centered estimates imply unit mixed Lp bounds

Uniform convexity supplies the radius inequality in the centered expansion.
Only the actual centered correlation estimates remain as inputs.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [Nonempty X]

noncomputable def centeredRadius (p : ℝ) (f : X → ℝ) : ℝ :=
  Real.sqrt (p - 1) * (FiniteLaw.uniform X).lpNorm p (centeredInput f)

theorem centeredRadius_nonneg (p : ℝ) (f : X → ℝ) : 0 ≤ centeredRadius p f :=
  mul_nonneg (Real.sqrt_nonneg _) ((FiniteLaw.uniform X).lpNorm_nonneg _ _)

theorem mean_sq_add_centeredRadius_sq {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ((FiniteLaw.uniform X).expect f) ^ 2 + centeredRadius p f ^ 2 ≤
      (FiniteLaw.uniform X).lpNorm p f ^ 2 := by
  unfold centeredRadius centeredInput
  rw [mul_pow, Real.sq_sqrt (sub_nonneg.mpr hp.le)]
  exact (FiniteLaw.uniform X).lpNorm_uniform_convexity hp hp2 f hf

theorem mixedLpBound_of_centeredLp (μ : FiniteLaw (V → X)) (hm : HasUniformMarginals μ)
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (c : Finset V → ℝ)
    (hc : ∀ S ∈ centeredSets V, 0 ≤ c S)
    (hsum : ∑ S ∈ centeredSets V, c S / Real.sqrt (p - 1) ^ S.card ≤ 1)
    (hcenter : ∀ f : V → X → ℝ, ∀ S ∈ centeredSets V,
      |centeredForm μ f S| ≤ c S * ∏ v ∈ S, (FiniteLaw.uniform X).lpNorm p (centeredInput (f v))) :
    MixedLpBound μ p 1 := by
  have hsqrt : 0 < Real.sqrt (p - 1) := Real.sqrt_pos.mpr (sub_pos.mpr hp)
  refine mixedLpBound_of_centered_small μ hm (by linarith) (centeredRadius p)
    (centeredRadius_nonneg p) ?_ (fun S => c S / Real.sqrt (p - 1) ^ S.card) ?_ hsum ?_
  · intro f hf hn
    simpa only [hn, one_pow] using mean_sq_add_centeredRadius_sq hp hp2 f hf
  · intro S hS
    exact div_nonneg (hc S hS) (pow_nonneg hsqrt.le _)
  · intro f S hS
    have he : c S / Real.sqrt (p - 1) ^ S.card * (∏ v ∈ S, centeredRadius p (f v)) =
        c S * ∏ v ∈ S, (FiniteLaw.uniform X).lpNorm p (centeredInput (f v)) := by
      simp only [centeredRadius, Finset.prod_mul_distrib, Finset.prod_const]
      field_simp
    rw [he]
    exact hcenter f S hS

noncomputable def centeredTolerance (V : Type*) [Fintype V] [DecidableEq V] (p : ℝ) : ℝ :=
  Real.sqrt (p - 1) ^ Fintype.card V / ((centeredSets V).card + 1)

theorem centeredTolerance_pos {p : ℝ} (hp : 1 < p) : 0 < centeredTolerance V p := by
  unfold centeredTolerance
  exact div_pos (pow_pos (Real.sqrt_pos.mpr (sub_pos.mpr hp)) _) (by positivity)

/-- A positive tolerance depending only on p and the number of slots,
independent of the alphabet size. -/
theorem mixedLpBound_of_centered_tolerance (μ : FiniteLaw (V → X))
    (hm : HasUniformMarginals μ) {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hcenter : ∀ f : V → X → ℝ, ∀ S ∈ centeredSets V,
      |centeredForm μ f S| ≤ centeredTolerance V p *
        ∏ v ∈ S, (FiniteLaw.uniform X).lpNorm p (centeredInput (f v))) :
    MixedLpBound μ p 1 := by
  have hb : 0 < Real.sqrt (p - 1) := Real.sqrt_pos.mpr (sub_pos.mpr hp)
  have hb1 : Real.sqrt (p - 1) ≤ 1 := by
    nlinarith [Real.sq_sqrt (sub_nonneg.mpr hp.le)]
  have hn : (0 : ℝ) < (centeredSets V).card + 1 := by positivity
  apply mixedLpBound_of_centeredLp μ hm hp hp2 (fun _ => centeredTolerance V p)
    (fun _ _ => (centeredTolerance_pos hp).le) _ hcenter
  have hterm (S : Finset V) : centeredTolerance V p / Real.sqrt (p - 1) ^ S.card ≤
      1 / ((centeredSets V).card + 1 : ℝ) := by
    have hpow := pow_le_pow_of_le_one hb.le hb1 (Finset.card_le_univ S)
    calc
      _ ≤ (Real.sqrt (p - 1) ^ S.card / ((centeredSets V).card + 1)) /
          Real.sqrt (p - 1) ^ S.card :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hpow hn.le) (pow_nonneg hb.le _)
      _ = _ := by field_simp
  apply (Finset.sum_le_sum (fun S _ => hterm S)).trans
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  exact (div_le_one hn).2 (by linarith)

end Sarkozy
