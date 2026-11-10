module

public import Sarkozy.ProbabilityConstructions
public import Sarkozy.Reflection.Tensor

/-!
# Atomic laws and finite products

Finite probability functionals are converted to their explicit nonnegative
weights. Independent coordinate products and tensor products of slot laws
are then probability laws with proved expectation identities.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiniteLaw

noncomputable def point {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (x : Ω) : FiniteLaw Ω where
  weight y := if y = x then 1 else 0
  nonneg y := by split <;> norm_num
  total := by simp

@[simp] theorem expect_point {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (x : Ω) (f : Ω → ℝ) : (point x).expect f = f x := by
  simp [point, expect, ite_mul]

noncomputable def ofFunctional {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (hL : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ L f)
    (hunit : L (fun _ => 1) = 1) : FiniteLaw Ω where
  weight := lawDensity L
  nonneg x := hL _ (fun y => by split <;> norm_num)
  total := by
    have h := linearFunctional_density L (fun _ => 1)
    simpa only [hunit, mul_one, lawDensity] using h.symm

theorem expect_ofFunctional {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (hL : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ L f)
    (hunit : L (fun _ => 1) = 1) (f : Ω → ℝ) : (ofFunctional L hL hunit).expect f = L f :=
  (linearFunctional_density L f).symm

theorem signedIntegral_ofFunctional {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (hL : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ L f)
    (hunit : L (fun _ => 1) = 1) : signedIntegral (ofFunctional L hL hunit).weight = L := by
  apply LinearMap.ext
  exact expect_ofFunctional L hL hunit

noncomputable def pi {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (μ : ∀ i, FiniteLaw (Ω i)) : FiniteLaw (∀ i, Ω i) where
  weight x := ∏ i, (μ i).weight (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (μ i).nonneg (x i))
  total := by
    rw [← Fintype.prod_sum]
    simp only [(μ _).total, Finset.prod_const_one]

theorem expect_pi_product {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (μ : ∀ i, FiniteLaw (Ω i))
    (f : ∀ i, Ω i → ℝ) :
    (pi μ).expect (fun x => ∏ i, f i (x i)) = ∏ i, (μ i).expect (f i) := by
  change (∑ x : ∀ i, Ω i, (∏ i, (μ i).weight (x i)) * ∏ i, f i (x i)) = _
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => (μ i).weight x * f i x)).symm

theorem expect_pi_coordinate {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    (μ : I → FiniteLaw Ω) (i : I) (f : Ω → ℝ) :
    (pi μ).expect (fun x => f (x i)) = (μ i).expect f := by
  have h := expect_pi_product μ (fun j => if j = i then f else fun _ => 1)
  simpa only [ite_apply, Finset.prod_ite_eq', Finset.mem_univ, ite_eq_left,
    apply_ite, expect_const] using h

noncomputable def tensor {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)] (μ : ∀ j, FiniteLaw (V → X j)) : FiniteLaw (V → ∀ j, X j) :=
  ofFunctional (tensorLaw (fun j => signedIntegral (μ j).weight))
    (fun f hf => tensorLaw_nonneg _ (fun j _ hg => (μ j).expect_nonneg hg) f hf)
    (tensorLaw_probability _ (fun j => (μ j).expect_const 1))

theorem signedIntegral_tensor {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)] (μ : ∀ j, FiniteLaw (V → X j)) :
    signedIntegral (tensor μ).weight = tensorLaw (fun j => signedIntegral (μ j).weight) :=
  signedIntegral_ofFunctional _ _ _

theorem tensor_positive {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)] (μ : ∀ j, FiniteLaw (V → X j)) (c : ReflectionCut V)
    (h : ∀ j, c.Positive (signedIntegral (μ j).weight)) :
    c.Positive (signedIntegral (tensor μ).weight) := by
  rw [signedIntegral_tensor]
  exact ReflectionCut.Positive.tensor h

end Sarkozy.FiniteLaw
