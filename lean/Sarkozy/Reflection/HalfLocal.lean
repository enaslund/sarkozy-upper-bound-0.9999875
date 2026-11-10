module

public import Sarkozy.Reflection.Transport
public import Sarkozy.ProbabilityProducts

/-!
# Half-local maps

A deterministic map applied separately to the two halves intertwines their
reflections. It is the deterministic case of the Markov transport theorem and
preserves both cut inequalities and samplewise fixed support.
-/

@[expose] public section

namespace Sarkozy.ReflectionCut

variable {V W X Y : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

def halfLocalMap (c : ReflectionCut V) (d : ReflectionCut W)
    (φ : (c.Half → X) → (d.Half → Y)) (z : V → X) : W → Y :=
  d.join (φ (fun v => z v.1)) (φ (fun v => z (c.flip v.1)))

theorem halfLocalMap_reflection (c : ReflectionCut V) (d : ReflectionCut W)
    (φ : (c.Half → X) → (d.Half → Y)) (z : V → X) :
    c.halfLocalMap d φ (z ∘ c.flip) = c.halfLocalMap d φ z ∘ d.flip := by
  unfold halfLocalMap
  rw [d.join_reflection]
  simp only [Function.comp_apply, c.flip_flip]

theorem SamplewiseFixed.halfLocalMap {Ω : Type*} {c : ReflectionCut V}
    (d : ReflectionCut W) {w : Ω → ℝ} {Z : Ω → V → X}
    (h : c.SamplewiseFixed w Z) (φ : (c.Half → X) → (d.Half → Y)) :
    d.SamplewiseFixed w (fun ω => c.halfLocalMap d φ (Z ω)) := by
  intro ω hω v
  have hfix : Z ω ∘ c.flip = Z ω := funext (fun i => h ω hω i)
  have he := c.halfLocalMap_reflection d φ (Z ω)
  rw [hfix] at he
  exact (congrFun he v).symm

theorem form_halfLocalMap (c : ReflectionCut V) (d : ReflectionCut W)
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (φ : (c.Half → X) → (d.Half → Y))
    (F G : (d.Half → Y) → ℝ) :
    d.form (pushFunctional L (c.halfLocalMap d φ)) F G = c.form L (F ∘ φ) (G ∘ φ) := by
  apply congrArg L
  funext z
  simp only [Function.comp_apply, halfLocalMap, join_plus, join_minus]

theorem Positive.halfLocalMap {c : ReflectionCut V} (d : ReflectionCut W)
    {L : ((V → X) → ℝ) →ₗ[ℝ] ℝ} (h : c.Positive L)
    (φ : (c.Half → X) → (d.Half → Y)) : d.Positive (pushFunctional L (c.halfLocalMap d φ)) := by
  constructor
  · intro F G
    rw [c.form_halfLocalMap, c.form_halfLocalMap]
    exact h.symmetric _ _
  · intro F
    rw [c.form_halfLocalMap]
    exact h.nonneg _

theorem Below.halfLocalMap {c : ReflectionCut V} (d : ReflectionCut W)
    {L M : ((V → X) → ℝ) →ₗ[ℝ] ℝ} (h : c.Below L M)
    (φ : (c.Half → X) → (d.Half → Y)) :
    d.Below (pushFunctional L (c.halfLocalMap d φ)) (pushFunctional M (c.halfLocalMap d φ)) :=
  Positive.halfLocalMap d h φ

theorem transport_point_eq_halfLocalMap [Fintype Y] [DecidableEq Y]
    (c : ReflectionCut V) (d : ReflectionCut W)
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (φ : (c.Half → X) → (d.Half → Y)) :
    c.transport d L (fun x => FiniteLaw.point (φ x)) = pushFunctional L (c.halfLocalMap d φ) := by
  apply LinearMap.ext
  intro f
  apply congrArg L
  funext z
  change (c.kernelLaw d (fun x => FiniteLaw.point (φ x)) z).expect f = f (c.halfLocalMap d φ z)
  rw [kernelLaw, FiniteLaw.expect_map, FiniteLaw.expect_product]
  simp only [FiniteLaw.expect_point, Function.comp_apply, halfLocalMap]

end Sarkozy.ReflectionCut
