module

public import Sarkozy.Moments.Energy
public import Sarkozy.Moments.Holder
public import Sarkozy.ProbabilityProducts

/-!
# Mixed moment bounds for finite laws

Uniform marginal laws always satisfy the ordinary L^d Hölder bound. Independent
coordinates satisfy the stronger L1 bound. Mixtures preserve a common exponent,
with the average of the component constants, and the exponent may be increased.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [Nonempty X]

theorem lpNorm_coordinate {μ : FiniteLaw (V → X)} (hm : HasUniformMarginals μ)
    (p : ℝ) (v : V) (f : X → ℝ) :
    μ.lpNorm p (fun z => f (z v)) = (FiniteLaw.uniform X).lpNorm p f := by
  unfold FiniteLaw.lpNorm FiniteLaw.moment
  rw [hm v (fun x => |f x| ^ p)]

theorem MixedLpBound.mono_exponent {μ : FiniteLaw (V → X)} {p q C : ℝ}
    (h : MixedLpBound μ p C) (hC : 0 ≤ C) (hp : 0 < p) (hpq : p ≤ q) :
    MixedLpBound μ q C := by
  intro f
  apply (h f).trans
  apply mul_le_mul_of_nonneg_left _ hC
  exact Finset.prod_le_prod₀ (fun _ _ => (FiniteLaw.uniform X).lpNorm_nonneg _ _)
    (fun v _ => (FiniteLaw.uniform X).lpNorm_mono hp hpq (f v))

theorem MixedLpBound.mono_constant {μ : FiniteLaw (V → X)} {p C D : ℝ}
    (h : MixedLpBound μ p C) (hCD : C ≤ D) : MixedLpBound μ p D := by
  intro f
  exact (h f).trans (mul_le_mul_of_nonneg_right hCD
    (Finset.prod_nonneg (fun _ _ => (FiniteLaw.uniform X).lpNorm_nonneg _ _)))

theorem mixedLpBound_of_uniform_marginals [Nonempty V]
    (μ : FiniteLaw (V → X)) (hm : HasUniformMarginals μ) :
    MixedLpBound μ (Fintype.card V) 1 := by
  have hc : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  intro f
  have hh := μ.abs_expect_prod_le_lpNorm (fun _ : V => Fintype.card V)
    (fun _ => hc) (by simp [hc.ne']) (fun v z => f v (z v))
  simpa only [lpNorm_coordinate hm, one_mul] using hh

theorem mixedLpBound_independent :
    MixedLpBound (FiniteLaw.pi (fun _ : V => FiniteLaw.uniform X)) 1 1 := by
  intro f
  rw [FiniteLaw.expect_pi_product, Finset.abs_prod, one_mul]
  apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
  intro v _
  exact (FiniteLaw.uniform X).abs_expect_le_lpNorm le_rfl (f v)

theorem mixedLpBound_mixture {I : Type*} [Fintype I]
    (weights : FiniteLaw I) (laws : I → FiniteLaw (V → X)) (p : ℝ) (C : I → ℝ)
    (h : ∀ i, MixedLpBound (laws i) p (C i)) :
    MixedLpBound (FiniteLaw.mixture weights laws) p (weights.expect C) := by
  intro f
  rw [FiniteLaw.expect_mixture]
  calc
    |weights.expect (fun i => (laws i).expect (fun z => ∏ v, f v (z v)))| ≤
        weights.expect (fun i => |(laws i).expect (fun z => ∏ v, f v (z v))|) :=
      weights.abs_expect_le _
    _ ≤ weights.expect (fun i => C i * ∏ v, (FiniteLaw.uniform X).lpNorm p (f v)) :=
      weights.expect_mono (fun i => h i f)
    _ = _ := weights.expect_mul_const _ _

end Sarkozy
