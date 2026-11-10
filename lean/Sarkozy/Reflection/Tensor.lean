module

public import Sarkozy.Reflection.Matrix

/-!
# Tensor products of finite signed laws

Finite signed functionals are represented by their point masses. Tensoring
those masses gives an explicit functional on product labels. Its cut matrix
is the entrywise product of the pulled-back factor cut matrices, so reflection
positivity tensorizes. The arguments adapt OpenAI's `MarkedTuples.lean` and
`WordReflection.lean`; see NOTICES.md.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy

theorem linearFunctional_density {X : Type*} [Fintype X] [DecidableEq X]
    (L : (X → ℝ) →ₗ[ℝ] ℝ) (f : X → ℝ) :
    L f = ∑ x, L (fun y => if y = x then 1 else 0) * f x := by
  classical
  have hf : f = ∑ x, f x • (fun y => if y = x then (1 : ℝ) else 0) := by
    ext y
    simp
  conv_lhs => rw [hf, map_sum]
  apply sum_congr rfl
  intro x _
  simp [mul_comm]

noncomputable def lawDensity {Ω : Type*} [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (x : Ω) : ℝ :=
  L (fun y => if y=x then 1 else 0)

noncomputable def tensorLaw {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) : ((V → ∀ j, X j) → ℝ) →ₗ[ℝ] ℝ where
  toFun F := ∑ z : ∀ j, V → X j, (∏ j, lawDensity (L j) (z j)) * F (fun v j => z j v)
  map_add' F G := by simp only [Pi.add_apply, mul_add, sum_add_distrib]
  map_smul' c F := by simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm, ← mul_sum, RingHom.id_apply]

theorem tensorLaw_fubini {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (F : ∀ j, (V → X j) → ℝ) :
    tensorLaw L (fun z => ∏ j, F j (fun v => z v j)) = ∏ j, L j (F j) := by
  change (∑ z : ∀ j, V → X j, (∏ j, lawDensity (L j) (z j)) * ∏ j, F j (z j)) = _
  simp_rw [← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j z => lawDensity (L j) z * F j z)]
  apply prod_congr rfl
  intro j _
  exact (linearFunctional_density (L j) (F j)).symm

theorem tensorLaw_probability {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (hL : ∀ j, L j (fun _ => 1)=1) :
    tensorLaw L (fun _ => 1) = 1 := by
  have hh := tensorLaw_fubini L (fun _ _ => 1)
  simpa only [prod_const_one, hL] using hh

theorem tensorLaw_nonneg {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ j F, (∀ z, 0 ≤ F z) → 0 ≤ L j F)
    (F : (V → ∀ j, X j) → ℝ) (hF : ∀ z, 0 ≤ F z) :
    0 ≤ tensorLaw L F := by
  apply sum_nonneg
  intro z _
  apply mul_nonneg (prod_nonneg fun j _ => ?_) (hF _)
  exact hL j _ (fun _ => by split_ifs <;> norm_num)

theorem prod_indicator_forall {J : Type*} [Fintype J] (P : J → Prop) [DecidablePred P]
    [Decidable (∀ j, P j)] :
    (∏ j, if P j then (1 : ℝ) else 0) = if ∀ j, P j then 1 else 0 := by
  classical
  by_cases h : ∀ j, P j
  · simp [h]
  · obtain ⟨j, hj⟩ := not_forall.mp h
    rw [ite_eq_right h]
    exact prod_eq_zero (mem_univ j) (ite_eq_right hj)

theorem tensorLaw_cutKernel {J V W : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (l r : W → V)
    (x y : W → ∀ j, X j) :
    cutKernel (tensorLaw L) (fun z w => z (l w)) (fun z w => z (r w)) x y =
      ∏ j, cutKernel (L j) (fun z w => z (l w)) (fun z w => z (r w))
        (fun w => x w j) (fun w => y w j) := by
  classical
  unfold cutKernel
  have he (z : V → ∀ j, X j) :
      (if (fun w => z (l w))=x ∧ (fun w => z (r w))=y then (1 : ℝ) else 0) =
      ∏ j, if (fun w => z (l w) j)=(fun w => x w j) ∧
        (fun w => z (r w) j)=(fun w => y w j) then 1 else 0 := by
    rw [prod_indicator_forall]
    congr 1
    apply propext
    constructor
    · rintro ⟨hl, hr⟩ j
      exact ⟨funext fun w => congrFun (congrFun hl w) j,
        funext fun w => congrFun (congrFun hr w) j⟩
    · intro h
      exact ⟨funext fun w => funext fun j => congrFun (h j).1 w,
        funext fun w => funext fun j => congrFun (h j).2 w⟩
  simp_rw [he]
  exact tensorLaw_fubini L (fun j z => if (fun w => z (l w))=(fun w => x w j) ∧
    (fun w => z (r w))=(fun w => y w j) then 1 else 0)

theorem tensorLaw_cut_positive {J V W : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (l r : W → V)
    (hsym : ∀ j, ∀ F G : (W → X j) → ℝ,
      L j (fun z => F (fun w => z (l w)) * G (fun w => z (r w))) =
      L j (fun z => G (fun w => z (l w)) * F (fun w => z (r w))))
    (hpos : ∀ j, ∀ F : (W → X j) → ℝ,
      0 ≤ L j (fun z => F (fun w => z (l w)) * F (fun w => z (r w)))) :
    (cutKernel (tensorLaw L) (fun z w => z (l w)) (fun z w => z (r w))).PosSemidef := by
  classical
  have he : cutKernel (tensorLaw L) (fun z w => z (l w)) (fun z w => z (r w)) =
      fun x y => ∏ j, cutKernel (L j) (fun z w => z (l w)) (fun z w => z (r w))
        (fun w => x w j) (fun w => y w j) := by
    funext x y
    exact tensorLaw_cutKernel L l r x y
  rw [he]
  let K (j : J) : Matrix (W → ∀ j, X j) (W → ∀ j, X j) ℝ :=
    (cutKernel (L j) (fun z w => z (l w)) (fun z w => z (r w))).submatrix
      (fun x w => x w j) (fun x w => x w j)
  have hK (j : J) : (K j).PosSemidef :=
    (cutKernel_posSemidef (L j) _ _ (hsym j) (hpos j)).submatrix _
  exact matrix_prod_posSemidef K hK

namespace ReflectionCut

/-- Tensoring laws that are positive at the same cut preserves positivity. -/
theorem Positive.tensor {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)] {c : ReflectionCut V}
    {L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ} (h : ∀ j, c.Positive (L j)) :
    c.Positive (tensorLaw L) := by
  apply (c.positive_iff_matrix_posSemidef _).mpr
  exact tensorLaw_cut_positive L (fun v : c.Half => v.1)
    (fun v : c.Half => c.flip v.1) (fun j => (h j).symmetric) (fun j => (h j).nonneg)

end ReflectionCut
end Sarkozy
