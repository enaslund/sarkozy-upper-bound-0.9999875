module

public import Sarkozy.Reflection.BracketMatrix

/-!
# Coordinates at a cut

Splitting into the plus half and the reflected minus half is an actual
bijection of configuration spaces. Its inverse joins any two half-labelings.
Consequently, the cut matrix determines every finite signed functional, and
symmetry of the cut form gives invariance under the reflection.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy

noncomputable def pushFunctional {Ω Ξ : Type*} (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (φ : Ω → Ξ) :
    (Ξ → ℝ) →ₗ[ℝ] ℝ where
  toFun f := L (f ∘ φ)
  map_add' f g := by exact L.map_add (f ∘ φ) (g ∘ φ)
  map_smul' a f := by exact L.map_smul a (f ∘ φ)

namespace ReflectionCut

variable {V X : Type*} [Fintype V] [DecidableEq V] (c : ReflectionCut V)

def join (x y : c.Half → X) (v : V) : X :=
  if hv : v ∈ c.half then x ⟨v, hv⟩ else y ⟨c.flip v, (c.crosses v).mpr hv⟩

@[simp] theorem join_plus (x y : c.Half → X) (v : c.Half) : c.join x y v.1 = x v := by
  simp only [join, dite_eq_left v.2]

@[simp] theorem join_minus (x y : c.Half → X) (v : c.Half) :
    c.join x y (c.flip v.1) = y v := by
  simp only [join, dite_eq_right (c.flip_not_mem v.2), c.flip_flip]

def configurationEquiv : (V → X) ≃ (c.Half → X) × (c.Half → X) where
  toFun z := (fun v => z v.1, fun v => z (c.flip v.1))
  invFun p := c.join p.1 p.2
  left_inv z := by
    funext v
    by_cases hv : v ∈ c.half
    · simp only [join, dite_eq_left hv]
    · simp only [join, dite_eq_right hv, c.flip_flip]
  right_inv p := by
    apply Prod.ext <;> funext v
    · exact c.join_plus _ _ v
    · exact c.join_minus _ _ v

theorem halves_eq_iff (z : V → X) (x y : c.Half → X) :
    ((fun v : c.Half => z v.1) = x ∧ (fun v : c.Half => z (c.flip v.1)) = y) ↔
      z = c.join x y := by
  change (c.configurationEquiv z).1 = x ∧ (c.configurationEquiv z).2 = y ↔ _
  have hp : ((c.configurationEquiv z).1 = x ∧ (c.configurationEquiv z).2 = y) ↔
      c.configurationEquiv z = (x, y) :=
    ⟨fun h => Prod.ext h.1 h.2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩
  exact hp.trans c.configurationEquiv.eq_symm_apply.symm

theorem reflection_swaps_halves (z : V → X) :
    c.configurationEquiv (z ∘ c.flip) = Prod.swap (c.configurationEquiv z) := by
  apply Prod.ext <;> funext v
  · rfl
  · exact congrArg z (c.flip_flip v.1)

theorem join_reflection (x y : c.Half → X) : c.join x y ∘ c.flip = c.join y x := by
  apply c.configurationEquiv.injective
  rw [c.reflection_swaps_halves]
  change Prod.swap (c.configurationEquiv (c.configurationEquiv.symm (x, y))) =
    c.configurationEquiv (c.configurationEquiv.symm (y, x))
  simp only [Equiv.apply_symm_apply, Prod.swap_prod_mk]

theorem matrix_eq_density_join [Fintype X] [DecidableEq X]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (x y : c.Half → X) :
    c.matrix L x y = lawDensity L (c.join x y) := by
  unfold matrix cutKernel lawDensity
  apply congrArg L
  funext z
  change (if (fun v : c.Half => z v.1) = x ∧ (fun v : c.Half => z (c.flip v.1)) = y
    then (1 : ℝ) else 0) = if z = c.join x y then 1 else 0
  simp only [c.halves_eq_iff]

theorem matrix_signedIntegral [Fintype X] [DecidableEq X]
    (w : (V → X) → ℝ) (x y : c.Half → X) :
    c.matrix (signedIntegral w) x y = w (c.join x y) := by
  rw [c.matrix_eq_density_join]
  simp [lawDensity, signedIntegral, mul_ite]

/-- A cut matrix loses no information about a finite signed law. -/
theorem matrix_injective [Fintype X] [DecidableEq X] :
    Function.Injective (c.matrix (X := X)) := by
  intro L M h
  apply LinearMap.ext
  intro f
  rw [linearFunctional_density L f, linearFunctional_density M f]
  apply Finset.sum_congr rfl
  intro z _
  have he := congrFun (congrFun h (fun v : c.Half => z v.1))
    (fun v : c.Half => z (c.flip v.1))
  rw [c.matrix_eq_density_join, c.matrix_eq_density_join] at he
  have hj : c.join (fun v : c.Half => z v.1) (fun v : c.Half => z (c.flip v.1)) = z :=
    c.configurationEquiv.symm_apply_apply z
  rw [hj] at he
  exact congrArg (· * f z) he

theorem matrix_reflection [Fintype X] [DecidableEq X]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) :
    c.matrix (pushFunctional L (fun z : V → X => z ∘ c.flip)) = (c.matrix L).transpose := by
  ext x y
  unfold matrix cutKernel pushFunctional
  change L (fun z : V → X => if
    (fun v : c.Half => z (c.flip v.1)) = x ∧
      (fun v : c.Half => z (c.flip (c.flip v.1))) = y then 1 else 0) = _
  simp only [c.flip_flip]
  apply congrArg L
  funext z
  simp only [and_comm]

theorem Positive.reflection_invariant {c : ReflectionCut V} [Fintype X] [DecidableEq X]
    {L : ((V → X) → ℝ) →ₗ[ℝ] ℝ} (h : c.Positive L) :
    pushFunctional L (fun z : V → X => z ∘ c.flip) = L := by
  apply c.matrix_injective
  rw [c.matrix_reflection]
  have hs := ((c.positive_iff_matrix_posSemidef L).mp h).isHermitian
  ext x y
  have hxy := congrFun (congrFun hs x) y
  simpa only [Matrix.conjTranspose_apply, star_trivial, Matrix.transpose_apply] using hxy

end ReflectionCut
end Sarkozy
