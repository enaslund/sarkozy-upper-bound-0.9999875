module

public import Sarkozy.DensityMoments.ChoiceClasses
public import Sarkozy.Moments.Product

/-!
# Identities of finite laws used to identify the replacement prefix

Bookkeeping for `thm:density:iid-prefix`(b) (`paper/sections/30_density_moment_upgrade.tex`):

* `law_eq_of_expect`: a finite law is determined by its expectations;
* `map_map_law`: pushforwards compose;
* `pi_uniform`: independent uniform coordinates are uniform on the product;
* `expect_uniform_equiv`: uniform expectations are invariant under a bijection;
* `expect_tensor_eq`, `expect_tensor_map`: the tensor law (`FiniteLaw.tensor`) as an explicit
  sum, and the tensor of pushforwards as the pushforward of the independent product.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.DensityMoments

/-- A finite law is determined by its expectations. -/
theorem law_eq_of_expect {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {μ ν : FiniteLaw Ω}
    (h : ∀ F : Ω → ℝ, μ.expect F = ν.expect F) : μ = ν := by
  apply FiniteLaw.ext
  intro x
  have hx := h (fun y => if y = x then 1 else 0)
  simpa [FiniteLaw.expect] using hx

/-- Pushforwards compose. -/
theorem map_map_law {Ω Ξ Ψ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ] [Fintype Ψ]
    [DecidableEq Ψ] (μ : FiniteLaw Ω) (f : Ω → Ξ) (g : Ξ → Ψ) :
    (μ.map f).map g = μ.map (g ∘ f) := by
  apply law_eq_of_expect
  intro F
  rw [FiniteLaw.expect_map, FiniteLaw.expect_map, FiniteLaw.expect_map]
  rfl

/-- Independent uniform coordinates form the uniform law on the product. -/
theorem pi_uniform {I : Type*} [Fintype I] [DecidableEq I] {Ω : I → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] :
    FiniteLaw.pi (fun i => FiniteLaw.uniform (Ω i)) = FiniteLaw.uniform (∀ i, Ω i) := by
  apply FiniteLaw.ext
  intro x
  simp [FiniteLaw.pi, FiniteLaw.uniform, Fintype.card_pi, Finset.prod_inv_distrib]

/-- Uniform expectations are invariant under a bijection. -/
theorem expect_uniform_equiv {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (e : α ≃ β) (F : β → ℝ) :
    (FiniteLaw.uniform α).expect (fun a => F (e a)) = (FiniteLaw.uniform β).expect F := by
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform, Fintype.card_congr e, e.sum_comp F]

/-- The tensor law as an explicit sum. -/
theorem expect_tensor_eq {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (μ : ∀ j, FiniteLaw (V → X j)) (F : (V → ∀ j, X j) → ℝ) :
    (FiniteLaw.tensor μ).expect F =
      ∑ z : ∀ j, V → X j, (∏ j, (μ j).weight (z j)) * F (fun v j => z j v) := by
  rw [FiniteLaw.expect_eq_signedIntegral, FiniteLaw.signedIntegral_tensor]
  unfold tensorLaw
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_congr rfl fun z _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [lawDensity, signedIntegral]

/-- **The tensor of pushforwards is the pushforward of the independent product.** -/
theorem expect_tensor_map {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] (lam : ∀ j, FiniteLaw (Ω j))
    (φ : ∀ j, Ω j → V → X j) (F : (V → ∀ j, X j) → ℝ) :
    (FiniteLaw.tensor (fun j => (lam j).map (φ j))).expect F =
      (FiniteLaw.pi lam).expect (fun u => F (fun v j => φ j (u j) v)) := by
  classical
  rw [expect_tensor_eq]
  have hw : ∀ z : ∀ j, V → X j, (∏ j, ((lam j).map (φ j)).weight (z j)) =
      ∑ u : ∀ j, Ω j, if (fun j => φ j (u j)) = z then ∏ j, (lam j).weight (u j) else 0 := by
    intro z
    simp only [FiniteLaw.map]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Fintype.prod_ite_zero]
    congr 1
    exact propext ⟨fun h => funext h, fun h j => congrFun h j⟩
  simp_rw [hw, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold FiniteLaw.expect
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [mem_univ, ↓reduceIte]
  rfl

end Sarkozy.DensityMoments
