module

public import Sarkozy.EnvelopeSteps.Regroup

@[expose] public section

/-!
# The placement is multiplicative over the blocks

`paper/sections/23_envelopes.tex`, `subsec:reflection-averaging`, "Record assignments and placed
measures": "the map `K ↦ [K]_ω` is linear and multiplicative over the blocks".

For a record assignment on a block set `S`, the objects are the tuples `x = (x_j)_{j ∈ S}`, the half
marginal is the product `m_ω(x) = ∏_j m_j(x_j)` (`prodWeight`) and the placement is the product of
the placements of the blocks (`prodPlace`). An operator whose kernel relative to `m_ω` is the
product of the kernels of operators `K_j` (the tensor `⊗_j K_j`) is placed as the tensor of the
placements:

* `join_prodPlace`: joining two product placements is joining blockwise;
* **`place_tensor`**: `[⊗_j K_j]_ω = ⊗_j [K_j]_{ω(j)}`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeSteps

variable {V : Type*} [Fintype V] [DecidableEq V] (c : ReflectionCut V)
  {S : Type*} [Fintype S] [DecidableEq S] {O : S → Type*} [∀ j, Fintype (O j)]
  [∀ j, DecidableEq (O j)] {X : S → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]

/-- The product placement `x ↦ (φ_j(x_j))_j`. -/
def prodPlace (φ : ∀ j, O j → (c.Half → X j)) (x : ∀ j, O j) : c.Half → ∀ j, X j :=
  fun v j => φ j (x j) v

/-- The product half marginal `m_ω(x) = ∏_j m_j(x_j)`. -/
def prodWeight (m : ∀ j, O j → ℝ) (x : ∀ j, O j) : ℝ := ∏ j, m j (x j)

omit [Fintype S] [DecidableEq S] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
  [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] in
theorem join_prodPlace (φ : ∀ j, O j → (c.Half → X j)) (x y : ∀ j, O j) :
    c.join (prodPlace c φ x) (prodPlace c φ y) = fun v j => c.join (φ j (x j)) (φ j (y j)) v := by
  funext v j
  unfold ReflectionCut.join prodPlace
  split_ifs <;> rfl

/-- **`[⊗_j K_j]_ω = ⊗_j [K_j]_{ω(j)}`**: if the kernel of `Kp` relative to the product marginal is
the product of the kernels of the `K_j`, its placement by the product placement is the tensor of
the placements. -/
theorem place_tensor (m : ∀ j, O j → ℝ) (φ : ∀ j, O j → (c.Half → X j))
    (K : ∀ j, (O j → ℝ) →ₗ[ℝ] (O j → ℝ)) (Kp : ((∀ j, O j) → ℝ) →ₗ[ℝ] ((∀ j, O j) → ℝ))
    (hK : ∀ x y, kern (prodWeight m) Kp x y = ∏ j, kern (m j) (K j) (x j) (y j)) :
    place c (prodWeight m) (prodPlace c φ) Kp = tensorLaw (fun j => place c (m j) (φ j) (K j)) := by
  refine LinearMap.ext fun Φ => ?_
  -- the joined labellings of a pair of objects at each block
  set Jn : ∀ j, O j × O j → (V → X j) := fun j q => c.join (φ j q.1) (φ j q.2) with hJn
  change (∑ q : (∀ j, O j) × (∀ j, O j), kern (prodWeight m) Kp q.1 q.2 *
      Φ (c.join (prodPlace c φ q.1) (prodPlace c φ q.2))) =
    ∑ z : ∀ j, V → X j, (∏ j, lawDensity (place c (m j) (φ j) (K j)) (z j)) *
      Φ (fun v j => z j v)
  have hdens : ∀ j (w : V → X j), lawDensity (place c (m j) (φ j) (K j)) w =
      ∑ q : O j × O j, kern (m j) (K j) q.1 q.2 * (if Jn j q = w then 1 else 0) := by
    intro j w
    rfl
  simp only [hdens]
  -- expand the product of sums
  have hexp : ∀ z : ∀ j, V → X j,
      (∏ j, ∑ q : O j × O j, kern (m j) (K j) q.1 q.2 * (if Jn j q = z j then (1 : ℝ) else 0)) =
      ∑ Q : ∀ j, O j × O j, (∏ j, kern (m j) (K j) (Q j).1 (Q j).2) *
        (if (fun j => Jn j (Q j)) = z then 1 else 0) := by
    intro z
    rw [Fintype.prod_sum]
    refine sum_congr rfl fun Q _ => ?_
    rw [prod_mul_distrib, prod_indicator_forall]
    congr 2
    apply propext
    constructor
    · intro h
      exact funext h
    · intro h j
      exact congrFun h j
  simp only [hexp, sum_mul]
  rw [sum_comm]
  have hcol : ∀ Q : ∀ j, O j × O j, ∑ z : ∀ j, V → X j,
      (∏ j, kern (m j) (K j) (Q j).1 (Q j).2) * (if (fun j => Jn j (Q j)) = z then 1 else 0) *
        Φ (fun v j => z j v) =
      (∏ j, kern (m j) (K j) (Q j).1 (Q j).2) * Φ (fun v j => Jn j (Q j) v) := by
    intro Q
    rw [Fintype.sum_eq_single (fun j => Jn j (Q j))]
    · simp
    · intro z hz
      rw [ite_eq_right (fun h => hz h.symm)]
      ring
  simp only [hcol]
  refine Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow S O O).symm _ _ fun q => ?_
  rw [hK, join_prodPlace]
  rfl

end Sarkozy.EnvelopeSteps
