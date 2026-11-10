module

public import Sarkozy.Reflection.Basic
public import Mathlib.Analysis.Matrix.Order

/-!
# Cut matrices

The matrix entry is the mass of the corresponding pair of half-configurations.
Its quadratic form is exactly the cut form. The equivalence with positive
semidefiniteness and preservation under products are proved here.

The finite matrix arguments adapt OpenAI's `WordReflection.lean`; see NOTICES.md.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy

noncomputable def cutKernel {Ω I : Type*} [DecidableEq I]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (left right : Ω → I) : Matrix I I ℝ :=
  fun x y => L (fun z => if left z = x ∧ right z = y then 1 else 0)

theorem cut_form_eq_sum {Ω I : Type*} [Fintype I] [DecidableEq I]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (left right : Ω → I) (F G : I → ℝ) :
    L (fun z => F (left z) * G (right z)) =
      ∑ x, ∑ y, cutKernel L left right x y * F x * G y := by
  classical
  have he : (fun z => F (left z) * G (right z)) =
      ∑ x, ∑ y, (F x * G y) • (fun z => if left z = x ∧ right z = y then (1 : ℝ) else 0) := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ite_and]
    simp
  rw [he, map_sum]
  apply sum_congr rfl
  intro x _
  rw [map_sum]
  apply sum_congr rfl
  intro y _
  rw [map_smul, smul_eq_mul]
  change (F x * G y) * cutKernel L left right x y = _
  ring

theorem cutKernel_posSemidef {Ω I : Type*} [Fintype I] [DecidableEq I]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (left right : Ω → I)
    (hsym : ∀ F G : I → ℝ,
      L (fun z => F (left z) * G (right z)) =
      L (fun z => G (left z) * F (right z)))
    (hpos : ∀ F : I → ℝ, 0 ≤ L (fun z => F (left z) * F (right z))) :
    (cutKernel L left right).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext x y
    have hs := hsym (fun z => if z=x then 1 else 0) (fun z => if z=y then 1 else 0)
    have he (x y : I) (z : Ω) :
        (if left z=x then (1 : ℝ) else 0) * (if right z=y then 1 else 0) =
          if left z=x ∧ right z=y then 1 else 0 := by split_ifs <;> simp_all
    simp_rw [he] at hs
    exact hs.symm
  · intro F
    have hh := hpos F
    rw [cut_form_eq_sum] at hh
    simpa only [dotProduct, Matrix.mulVec, star_trivial, sum_mul, mul_sum,
      mul_left_comm, mul_comm, mul_assoc] using hh

theorem matrix_prod_posSemidef {J I : Type*} [Fintype J] [Fintype I]
    (K : J → Matrix I I ℝ) (hK : ∀ j, (K j).PosSemidef) :
    Matrix.PosSemidef (fun x y => ∏ j, K j x y) := by
  classical
  have hs (s : Finset J) : Matrix.PosSemidef (fun x y => ∏ j ∈ s, K j x y) := by
    induction s using Finset.induction_on with
    | empty =>
      have he : (fun x y => ∏ j ∈ (∅ : Finset J), K j x y) =
          Matrix.vecMulVec (fun _ : I => (1 : ℝ)) (star (fun _ : I => (1 : ℝ))) := by
        ext x y
        simp [Matrix.vecMulVec]
      rw [he]
      exact Matrix.posSemidef_vecMulVec_self_star (fun _ : I => (1 : ℝ))
    | @insert j s hj ih =>
      have he : (fun x y => ∏ k ∈ insert j s, K k x y) =
          (K j).hadamard (fun x y => ∏ k ∈ s, K k x y) := by
        ext x y
        change (∏ k ∈ insert j s, K k x y) = K j x y * ∏ k ∈ s, K k x y
        exact prod_insert hj
      rw [he]
      exact (hK j).hadamard ih
  exact hs univ

theorem cut_positive_of_kernel {Ω I : Type*} [Fintype I] [DecidableEq I]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (left right : Ω → I)
    (hK : (cutKernel L left right).PosSemidef) (F : I → ℝ) :
    0 ≤ L (fun z => F (left z) * F (right z)) := by
  rw [cut_form_eq_sum]
  have hh := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hK).2 F
  simpa only [dotProduct, Matrix.mulVec, star_trivial, sum_mul, mul_sum,
    mul_left_comm, mul_comm, mul_assoc] using hh

theorem cut_symmetric_of_kernel {Ω I : Type*} [Fintype I] [DecidableEq I]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (left right : Ω → I)
    (hK : (cutKernel L left right).PosSemidef) (F G : I → ℝ) :
    L (fun z => F (left z) * G (right z)) =
      L (fun z => G (left z) * F (right z)) := by
  rw [cut_form_eq_sum, cut_form_eq_sum, sum_comm]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  have hs : cutKernel L left right x y = cutKernel L left right y x := by
    have h := congrFun (congrFun hK.isHermitian x) y
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h.symm
  rw [hs]
  ring

namespace ReflectionCut

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]

noncomputable def matrix (c : ReflectionCut V) (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) :
    Matrix (c.Half → X) (c.Half → X) ℝ :=
  cutKernel L (fun z v => z v.1) (fun z v => z (c.flip v.1))

theorem positive_iff_matrix_posSemidef (c : ReflectionCut V)
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) : c.Positive L ↔ (c.matrix L).PosSemidef := by
  constructor
  · intro h
    exact cutKernel_posSemidef L _ _ h.symmetric h.nonneg
  · intro h
    exact ⟨cut_symmetric_of_kernel L _ _ h, cut_positive_of_kernel L _ _ h⟩

end ReflectionCut
end Sarkozy
