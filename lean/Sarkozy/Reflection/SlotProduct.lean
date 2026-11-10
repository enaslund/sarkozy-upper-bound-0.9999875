module

public import Sarkozy.Moments.Product
public import Sarkozy.Reflection.Coordinates
public import Sarkozy.Energy

/-!
# Independent products of slot laws

The reference law is a product over atoms (`def:record:functional`(d)); in
particular it is the product of its fixed low part and its tail. For two laws on
labellings of the same slots, the independent product (`FiniteLaw.slotProduct`) is
reflection positive at every cut at which both factors are, and has uniform one-slot
marginals when both factors do. The cut matrix of the product is the entrywise
(Schur) product of the two cut matrices pulled back along the coordinate
projections; this is `eq:cc:kron` for two factors.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy

variable {V X Y : Type*} [Fintype V] [DecidableEq V] [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]

/-- The weight of an independent slot product. -/
theorem FiniteLaw.slotProduct_weight (μ : FiniteLaw (V → X)) (ν : FiniteLaw (V → Y))
    (u : V → X × Y) :
    (μ.slotProduct ν).weight u = μ.weight (fun v => (u v).1) * ν.weight (fun v => (u v).2) := by
  unfold FiniteLaw.slotProduct FiniteLaw.map FiniteLaw.product
  simp only
  rw [Finset.sum_eq_single ((fun v => (u v).1), (fun v => (u v).2))]
  · simp
  · intro b _ hb
    split_ifs with h
    · exfalso
      apply hb
      have h1 : (fun v => (b.1 v, b.2 v)) = u := h
      ext v
      · exact congrArg Prod.fst (congrFun h1 v)
      · exact congrArg Prod.snd (congrFun h1 v)
    · rfl
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
theorem ReflectionCut.join_fst (c : ReflectionCut V) (x y : c.Half → X × Y) (v : V) :
    (c.join x y v).1 = c.join (fun w => (x w).1) (fun w => (y w).1) v := by
  unfold ReflectionCut.join
  split_ifs <;> rfl

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
theorem ReflectionCut.join_snd (c : ReflectionCut V) (x y : c.Half → X × Y) (v : V) :
    (c.join x y v).2 = c.join (fun w => (x w).2) (fun w => (y w).2) v := by
  unfold ReflectionCut.join
  split_ifs <;> rfl

/-- Positivity at a cut is preserved by independent slot products. -/
theorem ReflectionCut.Positive.slotProduct {c : ReflectionCut V} {μ : FiniteLaw (V → X)}
    {ν : FiniteLaw (V → Y)} (hμ : c.Positive (signedIntegral μ.weight))
    (hν : c.Positive (signedIntegral ν.weight)) :
    c.Positive (signedIntegral (μ.slotProduct ν).weight) := by
  rw [ReflectionCut.positive_iff_matrix_posSemidef] at hμ hν ⊢
  have hA := hμ.submatrix (fun x : c.Half → X × Y => fun v => (x v).1)
  have hB := hν.submatrix (fun x : c.Half → X × Y => fun v => (x v).2)
  have heq : c.matrix (signedIntegral (μ.slotProduct ν).weight) =
      ((c.matrix (signedIntegral μ.weight)).submatrix
          (fun x : c.Half → X × Y => fun v => (x v).1) (fun x => fun v => (x v).1)).hadamard
        ((c.matrix (signedIntegral ν.weight)).submatrix
          (fun x : c.Half → X × Y => fun v => (x v).2) (fun x => fun v => (x v).2)) := by
    ext x y
    rw [c.matrix_signedIntegral, FiniteLaw.slotProduct_weight, Matrix.hadamard_apply,
      Matrix.submatrix_apply, Matrix.submatrix_apply, c.matrix_signedIntegral,
      c.matrix_signedIntegral]
    congr 1
    · congr 1
      funext v
      exact c.join_fst x y v
    · congr 1
      funext v
      exact c.join_snd x y v
  rw [heq]
  exact hA.hadamard hB

/-- Reflection positivity at the sorting cuts of the 72 slots is preserved by
independent slot products. -/
theorem slotReflectionPositive_slotProduct {μ : FiniteLaw (Slot → X)} {ν : FiniteLaw (Slot → Y)}
    (hμ : SlotReflectionPositive (signedIntegral μ.weight))
    (hν : SlotReflectionPositive (signedIntegral ν.weight)) :
    SlotReflectionPositive (signedIntegral (μ.slotProduct ν).weight) :=
  fun c hc => (hμ c hc).slotProduct (hν c hc)

/-- Uniform one-slot marginals are preserved by independent slot products. -/
theorem HasUniformMarginals.slotProduct [Nonempty X] [Nonempty Y] {μ : FiniteLaw (V → X)}
    {ν : FiniteLaw (V → Y)} (hμ : HasUniformMarginals μ) (hν : HasUniformMarginals ν) :
    HasUniformMarginals (μ.slotProduct ν) := by
  intro v f
  rw [FiniteLaw.expect_slotProduct]
  have h1 : (fun z : V → X => ν.expect (fun w => f (z v, w v))) =
      fun z => (FiniteLaw.uniform Y).expect (fun y => f (z v, y)) := by
    funext z
    exact hν v (fun y => f (z v, y))
  rw [h1, hμ v (fun x => (FiniteLaw.uniform Y).expect (fun y => f (x, y))),
    ← FiniteLaw.uniform_product, FiniteLaw.expect_product]

end Sarkozy
