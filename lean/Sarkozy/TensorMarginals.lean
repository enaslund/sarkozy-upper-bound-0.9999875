module

public import Sarkozy.ProbabilityProducts
public import Sarkozy.Reflection.Coordinates
public import Sarkozy.Energy

/-!
# Tensoring uniform one-slot marginals

The point masses of a slot marginal factor over independent label coordinates.
Consequently, tensoring laws with uniform one-slot marginals preserves that
property. Together with tensor reflection positivity, this supplies both
structural hypotheses for a reference law assembled prime by prime.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy

theorem uniform_expect_of_pointMass {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ x, lawDensity L x = (Fintype.card Ω : ℝ)⁻¹) (f : Ω → ℝ) :
    L f = (FiniteLaw.uniform Ω).expect f := by
  rw [linearFunctional_density L f, FiniteLaw.expect_uniform]
  change (∑ x, lawDensity L x * f x) = _
  simp_rw [h]
  rw [← Finset.mul_sum]
  ring

theorem tensorLaw_uniform_marginal {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)] [∀ j, Nonempty (X j)]
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (hm : ∀ j v f, L j (fun z => f (z v)) = (FiniteLaw.uniform (X j)).expect f)
    (v : V) (f : (∀ j, X j) → ℝ) :
    tensorLaw L (fun z => f (z v)) = (FiniteLaw.uniform (∀ j, X j)).expect f := by
  classical
  let mean := pushFunctional (tensorLaw L) (fun z : V → ∀ j, X j => z v)
  change mean f = _
  apply uniform_expect_of_pointMass mean
  intro x
  change tensorLaw L (fun z => if z v = x then 1 else 0) = _
  have he : (fun z : V → ∀ j, X j => if z v = x then (1 : ℝ) else 0) =
      (fun z => ∏ j, if z v j = x j then 1 else 0) := by
    funext z
    rw [prod_indicator_forall]
    congr 1
    exact propext ⟨fun h j => congrFun h j, fun h => funext h⟩
  rw [he, tensorLaw_fubini L (fun j z => if z v = x j then 1 else 0)]
  have hcoord (j : J) : L j (fun z => if z v = x j then 1 else 0) = (Fintype.card (X j) : ℝ)⁻¹ := by
    rw [hm j v (fun y => if y = x j then 1 else 0), FiniteLaw.expect_uniform]
    simp
  simp only [hcoord, Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]

theorem tensor_uniform_marginals {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)] [∀ j, Nonempty (X j)]
    (μ : ∀ j, FiniteLaw (V → X j)) (hm : ∀ j, HasUniformMarginals (μ j)) :
    HasUniformMarginals (FiniteLaw.tensor μ) := by
  intro v f
  rw [FiniteLaw.expect_eq_signedIntegral, FiniteLaw.signedIntegral_tensor]
  exact tensorLaw_uniform_marginal _ hm v f

theorem tensor_slot_reflection_positive {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (μ : ∀ j, FiniteLaw (Slot → X j))
    (hp : ∀ j, SlotReflectionPositive (signedIntegral (μ j).weight)) :
    SlotReflectionPositive (signedIntegral (FiniteLaw.tensor μ).weight) := by
  intro c hc
  exact FiniteLaw.tensor_positive μ c (fun j => hp j c hc)

end Sarkozy
