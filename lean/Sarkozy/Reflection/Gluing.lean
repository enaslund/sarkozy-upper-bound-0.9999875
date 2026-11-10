module

public import Sarkozy.Reflection.HalfLocal

/-!
# Reflection-positive laws from conditional independent halves

Draw a latent state, draw two half-configurations independently from the same
conditional law, and join them along a cut. The cut form is an average of
products of conditional means and is therefore positive. This construction
also records the exact half-marginals.
-/

@[expose] public section

namespace Sarkozy.ReflectionCut

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]

noncomputable def independentHalves (c : ReflectionCut V)
    (μ ν : FiniteLaw (c.Half → X)) : FiniteLaw (V → X) :=
  (μ.product ν).map (fun p => c.join p.1 p.2)

theorem expect_independentHalves (c : ReflectionCut V)
    (μ ν : FiniteLaw (c.Half → X)) (f : (V → X) → ℝ) :
    (c.independentHalves μ ν).expect f =
      μ.expect (fun x => ν.expect (fun y => f (c.join x y))) := by
  rw [independentHalves, FiniteLaw.expect_map, FiniteLaw.expect_product]
  rfl

theorem form_independentHalves (c : ReflectionCut V)
    (μ ν : FiniteLaw (c.Half → X)) (F G : (c.Half → X) → ℝ) :
    c.form (signedIntegral (c.independentHalves μ ν).weight) F G = μ.expect F * ν.expect G := by
  change (c.independentHalves μ ν).expect _ = _
  rw [independentHalves, FiniteLaw.expect_map]
  change (μ.product ν).expect
    (fun p => F (fun v => c.join p.1 p.2 v.1) * G (fun v => c.join p.1 p.2 (c.flip v.1))) = _
  simp only [join_plus, join_minus]
  exact FiniteLaw.expect_product_mul μ ν F G

theorem independentHalves_positive (c : ReflectionCut V) (μ : FiniteLaw (c.Half → X)) :
    c.Positive (signedIntegral (c.independentHalves μ μ).weight) := by
  constructor
  · intro F G
    rw [c.form_independentHalves, c.form_independentHalves, mul_comm]
  · intro F
    rw [c.form_independentHalves]
    exact mul_self_nonneg _

theorem expect_independentHalves_plus (c : ReflectionCut V)
    (μ ν : FiniteLaw (c.Half → X)) (F : (c.Half → X) → ℝ) :
    (c.independentHalves μ ν).expect (fun z => F (fun v => z v.1)) = μ.expect F := by
  rw [c.expect_independentHalves]
  simp only [join_plus, FiniteLaw.expect_const]

theorem expect_independentHalves_minus (c : ReflectionCut V)
    (μ ν : FiniteLaw (c.Half → X)) (F : (c.Half → X) → ℝ) :
    (c.independentHalves μ ν).expect (fun z => F (fun v => z (c.flip v.1))) = ν.expect F := by
  rw [c.expect_independentHalves]
  simp only [join_minus, FiniteLaw.expect_const]

omit [DecidableEq X] in
theorem form_mixture {I : Type*} [Fintype I] (c : ReflectionCut V)
    (α : FiniteLaw I) (μ : I → FiniteLaw (V → X)) (F G : (c.Half → X) → ℝ) :
    c.form (signedIntegral (FiniteLaw.mixture α μ).weight) F G =
      α.expect (fun i => c.form (signedIntegral (μ i).weight) F G) :=
  FiniteLaw.expect_mixture α μ _

omit [DecidableEq X] in
theorem mixture_positive {I : Type*} [Fintype I] (c : ReflectionCut V)
    (α : FiniteLaw I) (μ : I → FiniteLaw (V → X))
    (hμ : ∀ i, c.Positive (signedIntegral (μ i).weight)) :
    c.Positive (signedIntegral (FiniteLaw.mixture α μ).weight) := by
  constructor
  · intro F G
    rw [c.form_mixture, c.form_mixture]
    exact α.expect_congr (fun i => (hμ i).symmetric F G)
  · intro F
    rw [c.form_mixture]
    exact α.expect_nonneg (fun i => (hμ i).nonneg F)

noncomputable def glued {I : Type*} [Fintype I] (c : ReflectionCut V)
    (α : FiniteLaw I) (μ : I → FiniteLaw (c.Half → X)) : FiniteLaw (V → X) :=
  FiniteLaw.mixture α (fun i => c.independentHalves (μ i) (μ i))

theorem glued_positive {I : Type*} [Fintype I] (c : ReflectionCut V)
    (α : FiniteLaw I) (μ : I → FiniteLaw (c.Half → X)) :
    c.Positive (signedIntegral (c.glued α μ).weight) :=
  c.mixture_positive α _ (fun i => c.independentHalves_positive (μ i))

theorem expect_glued_plus {I : Type*} [Fintype I] (c : ReflectionCut V)
    (α : FiniteLaw I) (μ : I → FiniteLaw (c.Half → X)) (F : (c.Half → X) → ℝ) :
    (c.glued α μ).expect (fun z => F (fun v => z v.1)) = α.expect (fun i => (μ i).expect F) := by
  rw [glued, FiniteLaw.expect_mixture]
  simp only [c.expect_independentHalves_plus]

theorem expect_glued_minus {I : Type*} [Fintype I] (c : ReflectionCut V)
    (α : FiniteLaw I) (μ : I → FiniteLaw (c.Half → X)) (F : (c.Half → X) → ℝ) :
    (c.glued α μ).expect (fun z => F (fun v => z (c.flip v.1))) = α.expect (fun i => (μ i).expect F) := by
  rw [glued, FiniteLaw.expect_mixture]
  simp only [c.expect_independentHalves_minus]

end Sarkozy.ReflectionCut
