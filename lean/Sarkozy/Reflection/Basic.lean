module

public import Sarkozy.FiniteProbability
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.LinearAlgebra.Pi

/-!
# Reflection cuts and finite signed integrals

The definitions follow Section 5 of the paper. A cut exchanges its two halves;
its positive quadratic form is the ordinary reflection-positivity condition.
The integral is a linear functional and can, in particular, be the explicitly
weighted finite sum `signedIntegral` below. No positivity of the weights is
required for the one-cut arguments.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy

noncomputable def signedIntegral {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) :
    (Ω → ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∑ ω, w ω * f ω
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by simp [mul_left_comm, Finset.mul_sum]

theorem signedIntegral_nonneg {Ω : Type*} [Fintype Ω] {w f : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ signedIntegral w f :=
  Finset.sum_nonneg (fun ω _ => mul_nonneg (hw ω) (hf ω))

theorem FiniteLaw.expect_eq_signedIntegral {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (f : Ω → ℝ) : μ.expect f = signedIntegral μ.weight f := rfl

noncomputable def multilinearIntegral {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (a : V → X → ℝ) : ℝ :=
  L (fun z => ∏ v, a v (z v))

noncomputable def diagonalIntegral {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (g : X → ℝ) : ℝ :=
  multilinearIntegral L (fun _ => g)

structure ReflectionCut (V : Type*) [Fintype V] [DecidableEq V] where
  half : Finset V
  flip : V ≃ V
  flip_flip : ∀ v, flip (flip v) = v
  crosses : ∀ v, flip v ∈ half ↔ v ∉ half

namespace ReflectionCut

variable {V : Type*} [Fintype V] [DecidableEq V] (c : ReflectionCut V)

abbrev Half := {v : V // v ∈ c.half}

theorem flip_not_mem {v : V} (hv : v ∈ c.half) : c.flip v ∉ c.half := by
  rw [c.crosses]
  exact not_not.mpr hv

theorem flip_ne (v : V) : c.flip v ≠ v := by
  intro h
  have hc := c.crosses v
  rw [h] at hc
  by_cases hv : v ∈ c.half
  · exact (hc.mp hv) hv
  · exact hv (hc.mpr hv)

def halfSumEquiv : (c.Half ⊕ c.Half) ≃ V where
  toFun := Sum.elim (fun v => v.1) (fun v => c.flip v.1)
  invFun v := if hv : v ∈ c.half then Sum.inl ⟨v, hv⟩
    else Sum.inr ⟨c.flip v, (c.crosses v).2 hv⟩
  left_inv := by
    rintro (v | v)
    · exact dite_eq_left v.2
    · simp only [Sum.elim_inr, dite_eq_right (c.flip_not_mem v.2), c.flip_flip]
  right_inv := by
    intro v
    by_cases hv : v ∈ c.half
    · simp only [dite_eq_left hv, Sum.elim_inl]
    · simp only [dite_eq_right hv, Sum.elim_inr, c.flip_flip]

def foldPlus (v : V) : V := if v ∈ c.half then v else c.flip v
def foldMinus (v : V) : V := if v ∈ c.half then c.flip v else v

@[simp] theorem foldPlus_half (v : c.Half) : c.foldPlus v = v := by
  simp only [foldPlus, ite_eq_left v.2]

@[simp] theorem foldPlus_flip_half (v : c.Half) : c.foldPlus (c.flip v) = v := by
  simp only [foldPlus, ite_eq_right (c.flip_not_mem v.2), c.flip_flip]

@[simp] theorem foldMinus_half (v : c.Half) : c.foldMinus v = c.flip v := by
  simp only [foldMinus, ite_eq_left v.2]

@[simp] theorem foldMinus_flip_half (v : c.Half) : c.foldMinus (c.flip v) = c.flip v := by
  simp only [foldMinus, ite_eq_right (c.flip_not_mem v.2)]

theorem prod_split {M : Type*} [CommMonoid M] (f : V → M) :
    (∏ v, f v) = (∏ v : c.Half, f v.1) * (∏ v : c.Half, f (c.flip v.1)) := by
  rw [← Fintype.prod_equiv c.halfSumEquiv (fun v => f (c.halfSumEquiv v)) f (fun _ => rfl)]
  exact Fintype.prod_sum_type _

noncomputable def halfProduct {X : Type*} (a : V → X → ℝ) (x : c.Half → X) : ℝ :=
  ∏ v : c.Half, a v.1 (x v)

noncomputable def form {X : Type*} (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (F G : (c.Half → X) → ℝ) : ℝ :=
  L (fun z => F (fun v => z v.1) * G (fun v => z (c.flip v.1)))

structure Positive {X : Type*} (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) : Prop where
  symmetric : ∀ F G : (c.Half → X) → ℝ, c.form L F G = c.form L G F
  nonneg : ∀ F : (c.Half → X) → ℝ, 0 ≤ c.form L F F

theorem multilinear_eq_form {X : Type*} (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (a : V → X → ℝ) :
    multilinearIntegral L a = c.form L (c.halfProduct a) (c.halfProduct (a ∘ c.flip)) := by
  apply congrArg L
  funext z
  exact c.prod_split (fun v => a v (z v))

theorem folded_plus_eq_form {X : Type*} (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (a : V → X → ℝ) :
    multilinearIntegral L (a ∘ c.foldPlus) = c.form L (c.halfProduct a) (c.halfProduct a) := by
  unfold multilinearIntegral form
  apply congrArg L
  funext z
  rw [c.prod_split]
  simp only [Function.comp_apply, foldPlus_half, foldPlus_flip_half, halfProduct]

theorem folded_minus_eq_form {X : Type*} (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (a : V → X → ℝ) :
    multilinearIntegral L (a ∘ c.foldMinus) =
      c.form L (c.halfProduct (a ∘ c.flip)) (c.halfProduct (a ∘ c.flip)) := by
  unfold multilinearIntegral form
  apply congrArg L
  funext z
  rw [c.prod_split]
  simp only [Function.comp_apply, foldMinus_half, foldMinus_flip_half, halfProduct]

/-- Cauchy--Schwarz follows from positivity of the quadratic polynomial in t.
The proof follows the general cut argument in OpenAI's `MarkedTuples.lean`.
-/
theorem Positive.cauchy_schwarz_sq {c : ReflectionCut V} {X : Type*} {L : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    (h : c.Positive L) (F G : (c.Half → X) → ℝ) :
    |c.form L F G| ^ 2 ≤ c.form L F F * c.form L G G := by
  have hquad (t : ℝ) := h.nonneg (fun x => t * F x + G x)
  have heq (t : ℝ) : c.form L (fun x => t * F x + G x) (fun x => t * F x + G x) =
      t * t * c.form L F F + t * c.form L F G + t * c.form L G F + c.form L G G := by
    unfold form
    have he : (fun z : V → X =>
        (t * F (fun v => z v.1) + G (fun v => z v.1)) *
        (t * F (fun v => z (c.flip v.1)) + G (fun v => z (c.flip v.1)))) =
        (t * t) • (fun z => F (fun v => z v.1) * F (fun v => z (c.flip v.1))) +
        t • (fun z => F (fun v => z v.1) * G (fun v => z (c.flip v.1))) +
        t • (fun z => G (fun v => z v.1) * F (fun v => z (c.flip v.1))) +
        (fun z => G (fun v => z v.1) * G (fun v => z (c.flip v.1))) := by
      funext z
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he]
    simp only [map_add, map_smul, smul_eq_mul]
  simp only [heq, ← h.symmetric F G] at hquad
  have hdisc := discrim_le_zero (fun t => show 0 ≤
    c.form L F F * (t * t) + (2 * c.form L F G) * t + c.form L G G by
      nlinarith [hquad t])
  rw [discrim] at hdisc
  rw [sq_abs]
  nlinarith

theorem Positive.folding {c : ReflectionCut V} {X : Type*} {L : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    (h : c.Positive L) (a : V → X → ℝ) :
    |multilinearIntegral L a| ^ 2 ≤
      multilinearIntegral L (a ∘ c.foldPlus) * multilinearIntegral L (a ∘ c.foldMinus) := by
  rw [c.multilinear_eq_form, c.folded_plus_eq_form, c.folded_minus_eq_form]
  exact h.cauchy_schwarz_sq _ _

theorem Positive.foldPlus_nonneg {c : ReflectionCut V} {X : Type*} {L : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    (h : c.Positive L) (a : V → X → ℝ) : 0 ≤ multilinearIntegral L (a ∘ c.foldPlus) := by
  rw [c.folded_plus_eq_form]
  exact h.nonneg _

theorem Positive.foldMinus_nonneg {c : ReflectionCut V} {X : Type*} {L : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    (h : c.Positive L) (a : V → X → ℝ) : 0 ≤ multilinearIntegral L (a ∘ c.foldMinus) := by
  rw [c.folded_minus_eq_form]
  exact h.nonneg _

theorem Positive.diagonal_nonneg {c : ReflectionCut V} {X : Type*} {L : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    (h : c.Positive L) (f : X → ℝ) : 0 ≤ diagonalIntegral L f :=
  h.foldPlus_nonneg (fun _ => f)

end ReflectionCut
end Sarkozy
