module

public import Mathlib

/-!
# The disjoint-triple operator (`sec:frontier:empty-triple-negative`, first assertions)

`paper/sections/12_labellings.tex`, lemma `sec:frontier:empty-triple-negative`, on any finite
type `F` with `n` elements. `𝒯` is the set of ordered triples of distinct elements
(`Function.Injective x` for `x : Fin 3 → F`), with its uniform law, and
`T f(x) = ((n - 3)(n - 4)(n - 5))⁻¹ ∑_{y ∈ 𝒯, y ∩ x = ∅} f(y)` (`tripleOp`; the constant is
`(n - 3).descFactorial 3`).

* `card_disjTriple`: a triple `x ∈ 𝒯` has exactly `(n - 3)(n - 4)(n - 5)` disjoint triples in `𝒯`.
* `tripleOp_one`: `T 1 = 1` on `𝒯` (`n ≥ 6`).
* `tripleOp_selfAdjoint`: `T` is self-adjoint for the uniform law on `𝒯`.
* `tripleOp_eq_zero_of_symm`: `T f = 0` when the average of `f` over the orderings of each
  triple vanishes.
* `tripleOp_le`: `T ⪯ I`, i.e. `⟨T f, f⟩ ≤ ⟨f, f⟩`.

The lower bound `-3/(n - 3) I ⪯ T`, `‖T - J‖ = 3/(n - 3)`, the eigenvalues `λ₀ = 1` (constants),
`λ₁`, `λ₂`, `λ₃` with explicit eigenfunctions, and the factorization of `T` through the unordered
triple are in `Sarkozy.TraceMixing.DisjointTripleBound` and
`Sarkozy.TraceMixing.DisjointTripleOrdered`. Not formalized: that these eigenvalues exhaust the
spectrum (part (a)), and the tensor products over a block (part (c)).
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.TraceMixing

variable {F : Type*} [Fintype F] [DecidableEq F]

/-- `y` is an ordered triple of distinct elements, disjoint from `x`. -/
def DisjTriple (x y : Fin 3 → F) : Prop := Function.Injective y ∧ ∀ i j, x i ≠ y j

instance (x y : Fin 3 → F) : Decidable (DisjTriple x y) := by
  unfold DisjTriple
  infer_instance

/-- The disjoint-triple operator. -/
noncomputable def tripleOp (f : (Fin 3 → F) → ℝ) (x : Fin 3 → F) : ℝ :=
  ((Fintype.card F - 3).descFactorial 3 : ℝ)⁻¹ * ∑ y, if DisjTriple x y then f y else 0

/-- The disjoint triples of `x` are the embeddings of `Fin 3` into the complement of `x`. -/
def disjTripleEquiv (x : Fin 3 → F) :
    {y : Fin 3 → F // DisjTriple x y} ≃ (Fin 3 ↪ {z : F // ∀ i, x i ≠ z}) where
  toFun y := ⟨fun i => ⟨y.1 i, fun k => y.2.2 k i⟩, fun _ _ h => y.2.1 (congrArg Subtype.val h)⟩
  invFun e := ⟨fun i => (e i).1, fun _ _ h => e.injective (Subtype.ext h),
    fun k i => (e i).2 k⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **A triple of distinct elements has `(n - 3)(n - 4)(n - 5)` disjoint triples.** -/
theorem card_disjTriple {x : Fin 3 → F} (hx : Function.Injective x) :
    (univ.filter fun y => DisjTriple x y).card = (Fintype.card F - 3).descFactorial 3 := by
  rw [← Fintype.card_subtype, Fintype.card_congr (disjTripleEquiv x),
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_subtype]
  have e : (univ.filter fun z : F => ∀ i, x i ≠ z) = univ \ univ.image x := by
    ext z
    simp
  rw [e, card_sdiff_of_subset (subset_univ _), card_image_of_injective _ hx, card_univ,
    card_univ, Fintype.card_fin]

/-- **`T 1 = 1` on `𝒯`** (for `n ≥ 6`). -/
theorem tripleOp_one (hn : 6 ≤ Fintype.card F) {x : Fin 3 → F} (hx : Function.Injective x) :
    tripleOp (fun _ => (1 : ℝ)) x = 1 := by
  unfold tripleOp
  rw [Finset.sum_boole, card_disjTriple hx]
  have h0 : ((Fintype.card F - 3).descFactorial 3 : ℝ) ≠ 0 := by
    have : (Fintype.card F - 3).descFactorial 3 ≠ 0 := by
      rw [Ne, Nat.descFactorial_eq_zero_iff_lt]
      omega
    exact_mod_cast this
  exact inv_mul_cancel₀ h0

omit [Fintype F] [DecidableEq F] in
theorem disj_comm (x y : Fin 3 → F) : (∀ i j, x i ≠ y j) ↔ ∀ i j, y i ≠ x j :=
  ⟨fun h i j e => h j i e.symm, fun h i j e => h j i e.symm⟩

/-- **`T` is self-adjoint** for the uniform law on `𝒯`. -/
theorem tripleOp_selfAdjoint (f g : (Fin 3 → F) → ℝ) :
    ∑ x, (if Function.Injective x then g x * tripleOp f x else 0) =
      ∑ y, (if Function.Injective y then tripleOp g y * f y else 0) := by
  unfold tripleOp
  set c : ℝ := ((Fintype.card F - 3).descFactorial 3 : ℝ) with hc
  have hL (x : Fin 3 → F) : (if Function.Injective x then
      g x * (c⁻¹ * ∑ y, if DisjTriple x y then f y else 0) else 0) =
      c⁻¹ * ∑ y, (if Function.Injective x ∧ DisjTriple x y then g x * f y else 0) := by
    by_cases hx : Function.Injective x
    · rw [ite_eq_left hx, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine sum_congr rfl fun y _ => ?_
      by_cases hy : DisjTriple x y
      · rw [ite_eq_left hy, ite_eq_left (⟨hx, hy⟩ : Function.Injective x ∧ DisjTriple x y)]
        ring
      · rw [ite_eq_right hy,
          ite_eq_right (fun h : Function.Injective x ∧ DisjTriple x y => hy h.2)]
        ring
    · rw [ite_eq_right hx]
      have : ∑ y, (if Function.Injective x ∧ DisjTriple x y then g x * f y else 0) = 0 :=
        Finset.sum_eq_zero fun y _ => ite_eq_right (fun h => hx h.1)
      rw [this, mul_zero]
  have hR (y : Fin 3 → F) : (if Function.Injective y then
      (c⁻¹ * ∑ x, if DisjTriple y x then g x else 0) * f y else 0) =
      c⁻¹ * ∑ x, (if Function.Injective y ∧ DisjTriple y x then g x * f y else 0) := by
    by_cases hy : Function.Injective y
    · rw [ite_eq_left hy, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
      refine sum_congr rfl fun x _ => ?_
      by_cases hxy : DisjTriple y x
      · rw [ite_eq_left hxy, ite_eq_left (⟨hy, hxy⟩ : Function.Injective y ∧ DisjTriple y x)]
        ring
      · rw [ite_eq_right hxy,
          ite_eq_right (fun h : Function.Injective y ∧ DisjTriple y x => hxy h.2)]
        ring
    · rw [ite_eq_right hy]
      have : ∑ x, (if Function.Injective y ∧ DisjTriple y x then g x * f y else 0) = 0 :=
        Finset.sum_eq_zero fun x _ => ite_eq_right (fun h => hy h.1)
      rw [this, mul_zero]
  simp only [hL, hR]
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine sum_congr rfl fun y _ => sum_congr rfl fun x _ => ?_
  have hiff : (Function.Injective x ∧ DisjTriple x y) ↔
      (Function.Injective y ∧ DisjTriple y x) := by
    unfold DisjTriple
    rw [disj_comm x y]
    tauto
  by_cases h : Function.Injective x ∧ DisjTriple x y
  · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.mpr h'))]

/-- Reindexing a triple by a permutation of its coordinates. -/
def permTriple (σ : Equiv.Perm (Fin 3)) : (Fin 3 → F) ≃ (Fin 3 → F) where
  toFun y := y ∘ σ
  invFun y := y ∘ σ.symm
  left_inv y := by
    funext i
    simp
  right_inv y := by
    funext i
    simp

omit [Fintype F] [DecidableEq F] in
theorem disjTriple_perm (σ : Equiv.Perm (Fin 3)) (x y : Fin 3 → F) :
    DisjTriple x (y ∘ σ) ↔ DisjTriple x y := by
  unfold DisjTriple
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j h => ?_, fun i j h => ?_⟩
    · have := h1 (show (y ∘ σ) (σ.symm i) = (y ∘ σ) (σ.symm j) by simp [h])
      simpa using this
    · exact h2 i (σ.symm j) (by simp [h])
  · rintro ⟨h1, h2⟩
    exact ⟨h1.comp σ.injective, fun i j => h2 i (σ j)⟩

/-- **`T f = 0` when the average of `f` over the orderings of each triple vanishes.** -/
theorem tripleOp_eq_zero_of_symm (f : (Fin 3 → F) → ℝ)
    (hf : ∀ y : Fin 3 → F, Function.Injective y → ∑ σ : Equiv.Perm (Fin 3), f (y ∘ σ) = 0)
    (x : Fin 3 → F) : tripleOp f x = 0 := by
  unfold tripleOp
  have hσ (σ : Equiv.Perm (Fin 3)) : ∑ y, (if DisjTriple x y then f y else 0) =
      ∑ y, (if DisjTriple x y then f (y ∘ σ) else 0) := by
    refine (Fintype.sum_equiv (permTriple σ) _ _ fun y => ?_).symm
    change (if DisjTriple x y then f (y ∘ σ) else 0) =
      (if DisjTriple x (y ∘ σ) then f (y ∘ σ) else 0)
    by_cases hy : DisjTriple x y
    · rw [ite_eq_left hy, ite_eq_left ((disjTriple_perm σ x y).mpr hy)]
    · rw [ite_eq_right hy, ite_eq_right (fun h => hy ((disjTriple_perm σ x y).mp h))]
  have hsum : ∑ σ : Equiv.Perm (Fin 3), ∑ y, (if DisjTriple x y then f (y ∘ σ) else 0) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun y _ => ?_
    by_cases hy : DisjTriple x y
    · simp only [hy, ite_true]
      exact hf y hy.1
    · simp only [hy, ite_false, Finset.sum_const_zero]
  have hconst : ∑ σ : Equiv.Perm (Fin 3), ∑ y, (if DisjTriple x y then f (y ∘ σ) else 0) =
      (Fintype.card (Equiv.Perm (Fin 3)) : ℝ) * ∑ y, (if DisjTriple x y then f y else 0) := by
    rw [← Finset.card_univ, ← nsmul_eq_mul, ← Finset.sum_const]
    exact sum_congr rfl fun σ _ => (hσ σ).symm
  rw [hconst] at hsum
  have hcard : (Fintype.card (Equiv.Perm (Fin 3)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h0 : ∑ y, (if DisjTriple x y then f y else 0) = 0 := by
    rcases mul_eq_zero.mp hsum with h | h
    · exact absurd h hcard
    · exact h
  rw [h0, mul_zero]

/-- **`T ⪯ I`**: `⟨T f, f⟩ ≤ ⟨f, f⟩` for the uniform law on `𝒯` (`n ≥ 6`). -/
theorem tripleOp_le (hn : 6 ≤ Fintype.card F) (f : (Fin 3 → F) → ℝ) :
    ∑ x, (if Function.Injective x then f x * tripleOp f x else 0) ≤
      ∑ x, (if Function.Injective x then f x ^ 2 else 0) := by
  unfold tripleOp
  set c : ℝ := ((Fintype.card F - 3).descFactorial 3 : ℝ) with hc
  have hc0 : 0 < c := by
    have : (Fintype.card F - 3).descFactorial 3 ≠ 0 := by
      rw [Ne, Nat.descFactorial_eq_zero_iff_lt]
      omega
    rw [hc]
    exact_mod_cast Nat.pos_of_ne_zero this
  have hdeg (x : Fin 3 → F) (hx : Function.Injective x) :
      ∑ y, (if DisjTriple x y then (1 : ℝ) else 0) = c := by
    rw [Finset.sum_boole, card_disjTriple hx]
  have hiff (x y : Fin 3 → F) : (Function.Injective x ∧ DisjTriple x y) ↔
      (Function.Injective y ∧ DisjTriple y x) := by
    unfold DisjTriple
    rw [disj_comm x y]
    tauto
  set K : (Fin 3 → F) → (Fin 3 → F) → ℝ :=
    fun x y => if Function.Injective x ∧ DisjTriple x y then 1 else 0 with hK
  have hKsymm (x y : Fin 3 → F) : K x y = K y x := by
    simp only [hK]
    by_cases h : Function.Injective x ∧ DisjTriple x y
    · rw [ite_eq_left h, ite_eq_left ((hiff x y).mp h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ((hiff x y).mpr h'))]
  have hK0 (x y : Fin 3 → F) : 0 ≤ K x y := by
    simp only [hK]
    split_ifs <;> norm_num
  have hrow (x : Fin 3 → F) : ∑ y, K x y = if Function.Injective x then c else 0 := by
    simp only [hK]
    by_cases hx : Function.Injective x
    · rw [ite_eq_left hx, ← hdeg x hx]
      refine sum_congr rfl fun y _ => ?_
      by_cases hy : DisjTriple x y
      · rw [ite_eq_left (⟨hx, hy⟩ : Function.Injective x ∧ DisjTriple x y), ite_eq_left hy]
      · rw [ite_eq_right (fun h : Function.Injective x ∧ DisjTriple x y => hy h.2),
          ite_eq_right hy]
    · rw [ite_eq_right hx]
      exact Finset.sum_eq_zero fun y _ => ite_eq_right (fun h => hx h.1)
  have hcol (y : Fin 3 → F) : ∑ x, K x y = if Function.Injective y then c else 0 := by
    rw [← hrow y]
    exact sum_congr rfl fun x _ => hKsymm x y
  have hL (x : Fin 3 → F) : (if Function.Injective x then
      f x * (c⁻¹ * ∑ y, if DisjTriple x y then f y else 0) else 0) =
      c⁻¹ * ∑ y, K x y * (f x * f y) := by
    by_cases hx : Function.Injective x
    · rw [ite_eq_left hx, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine sum_congr rfl fun y _ => ?_
      simp only [hK]
      by_cases hy : DisjTriple x y
      · rw [ite_eq_left hy, ite_eq_left (⟨hx, hy⟩ : Function.Injective x ∧ DisjTriple x y)]
        ring
      · rw [ite_eq_right hy,
          ite_eq_right (fun h : Function.Injective x ∧ DisjTriple x y => hy h.2)]
        ring
    · rw [ite_eq_right hx]
      have : ∑ y, K x y * (f x * f y) = 0 := Finset.sum_eq_zero fun y _ => by
        simp only [hK]
        rw [ite_eq_right (fun h : Function.Injective x ∧ DisjTriple x y => hx h.1)]
        ring
      rw [this, mul_zero]
  simp only [hL]
  rw [← Finset.mul_sum]
  have hpt (x y : Fin 3 → F) : 2 * (K x y * (f x * f y)) ≤ K x y * f x ^ 2 + K x y * f y ^ 2 := by
    have := mul_le_mul_of_nonneg_left (two_mul_le_add_sq (f x) (f y)) (hK0 x y)
    linarith
  have hsum : 2 * ∑ x, ∑ y, K x y * (f x * f y) ≤
      ∑ x, ∑ y, K x y * f x ^ 2 + ∑ x, ∑ y, K x y * f y ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun y _ => hpt x y
  have h1 : ∑ x, ∑ y, K x y * f x ^ 2 =
      c * ∑ x, (if Function.Injective x then f x ^ 2 else 0) := by
    rw [Finset.mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_mul, hrow x]
    split_ifs <;> ring
  have h2 : ∑ x, ∑ y, K x y * f y ^ 2 =
      c * ∑ x, (if Function.Injective x then f x ^ 2 else 0) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_mul, hcol y]
    split_ifs <;> ring
  rw [h1, h2] at hsum
  have hS : ∑ x, ∑ y, K x y * (f x * f y) ≤
      c * ∑ x, (if Function.Injective x then f x ^ 2 else 0) := by linarith
  calc c⁻¹ * ∑ x, ∑ y, K x y * (f x * f y)
      ≤ c⁻¹ * (c * ∑ x, (if Function.Injective x then f x ^ 2 else 0)) :=
        mul_le_mul_of_nonneg_left hS (inv_nonneg.mpr hc0.le)
    _ = ∑ x, (if Function.Injective x then f x ^ 2 else 0) := by
        rw [← mul_assoc, inv_mul_cancel₀ hc0.ne', one_mul]

end Sarkozy.TraceMixing
