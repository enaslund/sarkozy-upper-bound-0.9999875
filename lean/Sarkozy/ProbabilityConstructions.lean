module

public import Sarkozy.FiniteProbability

/-!
# Explicit constructions of finite probability laws

Uniform laws, deterministic pushforwards, independent products, and mixtures
are defined by their weights. Their normalization and expectation identities
are proved by rearranging finite sums.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiniteLaw

noncomputable def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  weight _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [hc]

theorem expect_uniform {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    (uniform Ω).expect f = (∑ ω, f ω) / (Fintype.card Ω : ℝ) := by
  change (∑ ω, (Fintype.card Ω : ℝ)⁻¹ * f ω) = _
  rw [← Finset.mul_sum]
  ring

noncomputable def map {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ]
    (μ : FiniteLaw Ω) (φ : Ω → Ξ) : FiniteLaw Ξ where
  weight ξ := ∑ ω, if φ ω = ξ then μ.weight ω else 0
  nonneg ξ := Finset.sum_nonneg (fun ω _ => by split <;> simp_all [μ.nonneg])
  total := by
    rw [Finset.sum_comm]
    simpa using μ.total

theorem expect_map {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ]
    (μ : FiniteLaw Ω) (φ : Ω → Ξ) (f : Ξ → ℝ) :
    (μ.map φ).expect f = μ.expect (f ∘ φ) := by
  unfold expect map
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [ite_mul]

noncomputable def product {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ) : FiniteLaw (Ω × Ξ) where
  weight p := μ.weight p.1 * ν.weight p.2
  nonneg p := mul_nonneg (μ.nonneg _) (ν.nonneg _)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ν.total, mul_one, μ.total]

theorem expect_product {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ) (f : Ω × Ξ → ℝ) :
    (μ.product ν).expect f = μ.expect (fun ω => ν.expect (fun ξ => f (ω, ξ))) := by
  simp only [expect, product, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem expect_product_mul {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ) (f : Ω → ℝ) (g : Ξ → ℝ) :
    (μ.product ν).expect (fun p => f p.1 * g p.2) = μ.expect f * ν.expect g := by
  rw [expect_product]
  simp_rw [expect_const_mul]
  exact μ.expect_mul_const f (ν.expect g)

noncomputable def mixture {I Ω : Type*} [Fintype I] [Fintype Ω]
    (weights : FiniteLaw I) (laws : I → FiniteLaw Ω) : FiniteLaw Ω where
  weight ω := ∑ i, weights.weight i * (laws i).weight ω
  nonneg ω := Finset.sum_nonneg (fun i _ => mul_nonneg (weights.nonneg i) ((laws i).nonneg ω))
  total := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, (laws _).total, mul_one, weights.total]

theorem expect_mixture {I Ω : Type*} [Fintype I] [Fintype Ω]
    (weights : FiniteLaw I) (laws : I → FiniteLaw Ω) (f : Ω → ℝ) :
    (mixture weights laws).expect f = weights.expect (fun i => (laws i).expect f) := by
  simp only [expect, mixture, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_assoc]

end Sarkozy.FiniteLaw
