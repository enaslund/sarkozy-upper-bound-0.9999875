module

public import Sarkozy.Misc.TripleBlock

@[expose] public section

/-!
# `‖T - J‖ = 3/(p-3)` on ordered triples (`it:triple:bound`, the norm equality)

`paper/sections/12_labellings.tex`, `sec:frontier:empty-triple-negative`(b) (`it:triple:bound`):
"Hence `-3/(p-3) I ⪯ T ⪯ I`, the lower constant is attained, and `‖T - J‖ = 3/(p-3)`."

WP-S proved `T ⪯ I`, `T ⪰ -3/(n-3) I` and `‖T - J‖ ≤ 3/(n-3)` on ordered triples, and that the
lower constant is attained by the unordered-triple operator `T̄` (`disjOp_eigen`,
`disjOp_attained`: `g(S) = [x₀ ∈ S] - 3/n` has `T̄ g = -3/(n-3) g`). This file transfers the
eigenfunction to the ordered triples and concludes the equality:

* `card_orderings`: a `3`-set has exactly six orderings;
* `liftTriple_setFun`: the sum over the orderings of a function of the set is six times it;
* `tripleMatrix_eigen`: `f(x) = [x₀ ∈ x] - 3/n` satisfies `T f = -3/(n-3) f` on `𝒯`;
* **`tripleMatrix_norm_eq`**: `‖(T - J) g‖₂ ≤ 3/(n-3) ‖g‖₂` for every `g`, with equality for the
  nonzero mean-zero `f` above, i.e. `‖T - J‖ = 3/(n-3)` (`n ≥ 7`).
-/

namespace Sarkozy.Misc

open Finset Matrix Sarkozy.TraceMixing Sarkozy.IndexSupport
open scoped BigOperators Matrix

variable {F : Type*} [Fintype F] [DecidableEq F]

omit [Fintype F] in
theorem mem_tripleSet {x : Fin 3 → F} {a : F} : a ∈ tripleSet x ↔ ∃ i, x i = a := by
  simp [tripleSet]

/-- **A `3`-set has exactly six orderings.** -/
theorem card_orderings (S : Finset F) (hS : S.card = 3) :
    (univ.filter fun x : Fin 3 → F => Function.Injective x ∧ tripleSet x = S).card = 6 := by
  rw [← Fintype.card_subtype]
  have hmem (x : {x : Fin 3 → F // Function.Injective x ∧ tripleSet x = S}) (i : Fin 3) :
      x.1 i ∈ S := by
    have h : x.1 i ∈ tripleSet x.1 := mem_tripleSet.mpr ⟨i, rfl⟩
    rwa [x.2.2] at h
  let e : {x : Fin 3 → F // Function.Injective x ∧ tripleSet x = S} ≃ (Fin 3 ↪ S) :=
    { toFun := fun x => ⟨fun i => ⟨x.1 i, hmem x i⟩, fun i j h => x.2.1 (congrArg Subtype.val h)⟩
      invFun := fun f => ⟨fun i => (f i).1, fun i j h => f.injective (Subtype.ext h), by
        apply Finset.eq_of_subset_of_card_le
        · intro y hy
          obtain ⟨i, rfl⟩ := mem_tripleSet.mp hy
          exact (f i).2
        · rw [hS, tripleSet, card_image_of_injective _
            (fun i j h => f.injective (Subtype.ext h))]
          simp⟩
      left_inv := fun x => rfl
      right_inv := fun f => by
        ext i
        rfl }
  rw [Fintype.card_congr e, Fintype.card_embedding_eq, Fintype.card_coe, hS, Fintype.card_fin]
  rfl

/-- The sum over the orderings of a function of the underlying set is six times the function. -/
theorem liftTriple_setFun (G : Finset F → ℝ) (S : Finset F) (hS : S.card = 3) :
    liftTriple (extTrip fun t : Trip F => G (tripleSet t.1)) S = 6 * G S := by
  unfold liftTriple
  have h : ∀ y : Fin 3 → F, (if Function.Injective y ∧ tripleSet y = S then
      extTrip (fun t : Trip F => G (tripleSet t.1)) y else 0) =
      (if Function.Injective y ∧ tripleSet y = S then G S else 0) := fun y => by
    by_cases hy : Function.Injective y ∧ tripleSet y = S
    · rw [ite_eq_left hy, ite_eq_left hy]
      simp [extTrip, hy.1, hy.2]
    · rw [ite_eq_right hy, ite_eq_right hy]
  rw [sum_congr rfl fun y _ => h y, ← sum_filter, sum_const, card_orderings S hS, nsmul_eq_mul]
  push_cast
  ring

/-- The eigenfunction `f(x) = [x₀ ∈ x] - 3/n` on `𝒯`. -/
noncomputable def tripleEigenFun (x₀ : F) : Trip F → ℝ :=
  fun t => (if x₀ ∈ tripleSet t.1 then 1 else 0) - 3 / (Fintype.card F : ℝ)

omit [Fintype F] in
theorem card_tripleSet (t : Trip F) : (tripleSet t.1).card = 3 := by
  simp [tripleSet, card_image_of_injective _ t.2]

/-- **`T f = -3/(n-3) f`** for `f(x) = [x₀ ∈ x] - 3/n` on the ordered triples (`n ≥ 6`), from
WP-S's eigenfunction of `T̄` (`disjOp_eigen`). -/
theorem tripleMatrix_eigen (hn : 6 ≤ Fintype.card F) (x₀ : F) (x : Trip F) :
    (tripleMatrix F *ᵥ tripleEigenFun x₀) x =
      -(3 / ((Fintype.card F : ℝ) - 3)) * tripleEigenFun x₀ x := by
  set g : Finset F → ℝ := fun S => (if x₀ ∈ S then 1 else 0) - 3 / (Fintype.card F : ℝ)
  have hf : tripleEigenFun x₀ = fun t : Trip F => g (tripleSet t.1) := rfl
  rw [tripleMatrix_mulVec, tripleOp_eq_disjOp, hf]
  have hdisj : disjOp (liftTriple (extTrip fun t : Trip F => g (tripleSet t.1))) (tripleSet x.1) =
      6 * disjOp g (tripleSet x.1) := by
    unfold disjOp
    have hs : ∑ S' ∈ univ.filter (fun S : Finset F => S.card = 3),
        (if Disjoint (tripleSet x.1) S' then
          liftTriple (extTrip fun t : Trip F => g (tripleSet t.1)) S' else 0) =
        6 * ∑ S' ∈ univ.filter (fun S : Finset F => S.card = 3),
          (if Disjoint (tripleSet x.1) S' then g S' else 0) := by
      rw [mul_sum]
      refine sum_congr rfl fun S hS => ?_
      have hS3 : S.card = 3 := (mem_filter.mp hS).2
      split_ifs
      · exact liftTriple_setFun g S hS3
      · ring
    rw [hs]
    ring
  rw [hdisj, disjOp_eigen hn x₀ (card_tripleSet x)]
  ring

/-- The eigenfunction has mean zero and is nonzero (`n ≥ 6`). -/
theorem tripleEigenFun_sum_sq (hn : 6 ≤ Fintype.card F) (x₀ : F) :
    ∑ t, tripleEigenFun x₀ t = 0 ∧ 0 < tripleEigenFun x₀ ⬝ᵥ tripleEigenFun x₀ := by
  set g : Finset F → ℝ := fun S => (if x₀ ∈ S then 1 else 0) - 3 / (Fintype.card F : ℝ)
  obtain ⟨h0, hpos, -⟩ := disjOp_attained hn x₀
  have hlift (G : Finset F → ℝ) : ∑ t : Trip F, G (tripleSet t.1) =
      6 * ∑ S ∈ univ.filter (fun S : Finset F => S.card = 3), G S := by
    rw [trip_sum, ← liftTriple_sum, mul_sum]
    exact sum_congr rfl fun S hS => liftTriple_setFun G S (mem_filter.mp hS).2
  constructor
  · have := hlift g
    rw [h0, mul_zero] at this
    exact this
  · have := hlift (fun S => g S ^ 2)
    simp only [dotProduct]
    have e : ∑ t : Trip F, tripleEigenFun x₀ t * tripleEigenFun x₀ t =
        ∑ t : Trip F, g (tripleSet t.1) ^ 2 := sum_congr rfl fun t _ => by
      rw [sq]
      rfl
    rw [e, this]
    positivity

/-- **`‖T - J‖ = 3/(n-3)` on `L²(𝒯)`** (`it:triple:bound`, `n ≥ 7`): `‖(T - J) g‖₂ ≤ 3/(n-3) ‖g‖₂`
for every `g` (squared), and equality holds for the nonzero `f(x) = [x₀ ∈ x] - 3/n`. -/
theorem tripleMatrix_norm_eq (hn : 7 ≤ Fintype.card F) :
    (∀ g : Trip F → ℝ, ((tripleMatrix F - meanMatrix (Trip F)) *ᵥ g) ⬝ᵥ
        ((tripleMatrix F - meanMatrix (Trip F)) *ᵥ g) ≤
          (3 / ((Fintype.card F : ℝ) - 3)) ^ 2 * (g ⬝ᵥ g)) ∧
      ∀ x₀ : F, tripleEigenFun x₀ ≠ 0 ∧
        ((tripleMatrix F - meanMatrix (Trip F)) *ᵥ tripleEigenFun x₀) ⬝ᵥ
            ((tripleMatrix F - meanMatrix (Trip F)) *ᵥ tripleEigenFun x₀) =
          (3 / ((Fintype.card F : ℝ) - 3)) ^ 2 * (tripleEigenFun x₀ ⬝ᵥ tripleEigenFun x₀) := by
  set c : ℝ := 3 / ((Fintype.card F : ℝ) - 3)
  have hc0 : 0 ≤ c := div_nonneg (by norm_num) (by
    have : (7 : ℝ) ≤ Fintype.card F := by exact_mod_cast hn
    linarith)
  obtain ⟨h1, h2⟩ := tripleMatrix_centred (F := F) hn
  have hJ : (meanMatrix (Trip F)).PosSemidef := by
    have he : meanMatrix (Trip F) = (Fintype.card (Trip F) : ℝ)⁻¹ •
        Matrix.vecMulVec (fun _ : Trip F => (1 : ℝ)) (star (fun _ : Trip F => (1 : ℝ))) := by
      ext x y
      simp [meanMatrix_apply, Matrix.vecMulVec]
    rw [he]
    exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by positivity)
  have hlo : ((tripleMatrix F - meanMatrix (Trip F)) + c • 1).PosSemidef := by
    have h := h1.add (hJ.smul hc0)
    have he : (tripleMatrix F - meanMatrix (Trip F)) + c • (1 - meanMatrix (Trip F)) +
        c • meanMatrix (Trip F) = (tripleMatrix F - meanMatrix (Trip F)) + c • 1 := by
      ext x y
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      ring
    rwa [he] at h
  have hup : (c • 1 - (tripleMatrix F - meanMatrix (Trip F))).PosSemidef := by
    have h := h2.add (hJ.smul hc0)
    have he : c • (1 - meanMatrix (Trip F)) - (tripleMatrix F - meanMatrix (Trip F)) +
        c • meanMatrix (Trip F) = c • 1 - (tripleMatrix F - meanMatrix (Trip F)) := by
      ext x y
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      ring
    rwa [he] at h
  have hT : (tripleMatrix F - meanMatrix (Trip F))ᵀ = tripleMatrix F - meanMatrix (Trip F) := by
    rw [transpose_sub, meanMatrix_transpose, tripleMatrix_transpose]
  refine ⟨mulVec_sq_le_of_two_sided _ hT hc0 hlo hup, fun x₀ => ?_⟩
  obtain ⟨hsum, hpos⟩ := tripleEigenFun_sum_sq (by omega) x₀
  have hTf : (tripleMatrix F - meanMatrix (Trip F)) *ᵥ tripleEigenFun x₀ =
      (-c) • tripleEigenFun x₀ := by
    rw [sub_mulVec]
    funext x
    rw [Pi.sub_apply, tripleMatrix_eigen (by omega) x₀ x, meanMatrix_mulVec]
    simp only [hsum, mul_zero, sub_zero, Pi.smul_apply, smul_eq_mul]
    rfl
  refine ⟨fun h => by rw [h] at hpos; simp at hpos, ?_⟩
  rw [hTf, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

end Sarkozy.Misc
